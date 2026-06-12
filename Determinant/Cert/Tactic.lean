module

public import Determinant.Cert.Bird
public import Mathlib.Tactic.Ring
public import Qq
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Meta.Transform
public meta import Lean.Elab.Tactic.Basic

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring

public meta section

/--
A `Cert` represents an equality:

```
subject = norm
```
where the `subject` is the lhs of the `proof`'s type.
-/
structure Cert {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- The `Ring` tactic normal form that the subject is equal to -/
  norm : Q($α)
  val : Common.ExSum RatCoeff sα norm
  /-- Proof that the `subject` is equal to the `norm` -/
  proof : Expr
  /-- `true` when `norm` is zero -/
  isZero : Bool

namespace Cert

section Helpers

structure BinaryOpApp where
  partialApp : Expr
  x : Expr
  y : Expr

structure UnaryOpApp where
  partialApp : Expr
  x : Expr

/-- Destructure `@HAdd.hAdd α α α inst x y` into `⟨partialApp, x, y⟩`. -/
def destructAdd? (e : Expr) : Option BinaryOpApp := Id.run do
  let_expr HAdd.hAdd α β γ inst x y := e | return none
  return some ⟨mkApp4 e.getAppFn α β γ inst, x, y⟩

/-- Destructure `@HMul.hMul α α α inst x y` into `⟨partialApp, x, y⟩`. -/
def destructMul? (e : Expr) : Option BinaryOpApp := Id.run do
  let_expr HMul.hMul α β γ inst x y := e | return none
  return some ⟨mkApp4 e.getAppFn α β γ inst, x, y⟩ 

/-- Destructure `@Neg.neg α inst x` into `⟨partialApp, x⟩`. -/
def destructNeg? (e : Expr) : Option UnaryOpApp := Id.run do
  let_expr Neg.neg α inst x := e | return none
  return some ⟨mkApp2 e.getAppFn α inst, x⟩

/-- A proof of `lo < n` by `decide` -/
def mkLtProof (lo n : Nat) : MetaM Expr := do
  unless lo < n do
    throwError m!"failed to prove {lo} < {n}"
  let p ← mkAppOptM ``LT.lt #[
    mkConst ``Nat,
    mkConst ``instLTNat,
    mkNatLit lo,
    mkNatLit n
  ]
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  return mkApp3 (mkConst ``of_decide_eq_true) p inst (← mkEqRefl (mkConst ``Bool.true))

/-- A proof of `¬ lo < n` by `decide` -/
def mkNotLtProof (lo n : Nat) : MetaM Expr := do
  unless ¬ lo < n do
    throwError m!"failed to prove ¬ {lo} < {n}"
  let p ← mkAppOptM ``LT.lt #[
    mkConst ``Nat,
    mkConst ``instLTNat,
    mkNatLit lo,
    mkNatLit n
  ]
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  return mkApp3 (mkConst ``of_decide_eq_false) p inst (← mkEqRefl (mkConst ``Bool.false))

structure EqProof where
  proof : Expr
  lhs : Expr
  rhs : Expr

/-- Instantiate the lemma `name` and return `{proof, lhs, rhs}` -/
def applyEqLemma (name : Name) (u : Level) (args : Array Expr) : MetaM EqProof := do
  let proof := mkAppN (mkConst name [u]) args
  let some (_, lhs, rhs) := (← inferType proof).eq?
    | throwError "applyEqLemms: {name} did not produce an equality"
  return {proof, lhs, rhs}

/-- Parse an array literal into an array of element exrpessions -/
def arrayLiteral? (e : Expr) : MetaM (Option (Array Expr)) := do
  getArrayLit? e

structure BirdDetInfo where
  level : Level
  ringType : Expr
  commRingInst : Expr
  dimension : Nat
  dimensionExpr : Expr
  arrayExpr : Expr
  arrayEntries : Array Expr

def reifyBirdDet (e : Expr) : MetaM BirdDetInfo := do
  let e ← instantiateMVars e
  let_expr birdDet ringType commRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let .const _ [level] := e.getAppFn
    | throwError "expected `birdDet` to have exactly one universe level"
  let dimensionExpr ← whnf dimensionExpr
  let some dimension := dimensionExpr.rawNatLit?
    | throwError "expected the dimension to be a `Nat` literal, got {dimensionExpr}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, expected {dimension * dimension}"
  return {level, ringType, commRingInst, dimension, dimensionExpr, arrayExpr, arrayEntries}

end Helpers

variable
  {u : Level}
  {α : Q(Type u)}
  {sα : Q(CommSemiring $α)}

def isZeroVal {e : Q($α)} (val : Common.ExSum RatCoeff sα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/-- Repackage a `Ring` evaluation result as a certificate. -/
def toCert {e : Q($α)} (res : Common.Result (Common.ExSum RatCoeff sα) e) : Cert sα :=
  { norm := res.expr, val := res.val, proof := res.proof, isZero := isZeroVal res.val }

/-- Cast an existing `proof : subject = 0` as a certificate for the cannonical zero -/
def zeroCertOf (subject proof : Expr) : MetaM (Cert sα) := do
  let zero : Q($α) := q(0)
  let proof ← mkExpectedTypeHint proof (← mkEq subject zero)
  return {norm := zero, val := .zero, proof, isZero := true}

/-- Given `cz.proof : cz.subject! = 0`, certify the product `x * cz.subject = 0` without evaluating `x`.

`mulP` is HMul.hmul, partially applied with types and instances (see `destructMul?`).
-/
def zeroProdCert (mulP x : Expr) (cz : Cert sα) : MetaM (Cert sα) := do
  -- x * (cz.subject) = x * 0
  let h1 ← mkCongrArg (mkApp mulP x) cz.proof
  -- x * 0 = 0
  let h2 ← mkAppM ``mul_zero #[x]
  -- x * (cz.subject) = 0
  let h ← mkEqTrans h1 h2
  let some (_, lhs, _) := (← inferType h1).eq? | unreachable!
  zeroCertOf lhs h

/-- Extract the certificate's subject

Used for tests and debugging-/
def subject! (c : Cert sα) : MetaM Expr := do
  let some (_, lhs, _) := (← inferType c.proof).eq?
    | throwError "Cert.subject!: proof is not an equality: {c.proof}"
  return lhs

end Cert

end
