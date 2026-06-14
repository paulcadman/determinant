module

public import Determinant.CertChain.Bird
public import Mathlib.Tactic.Ring
public import Qq
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Meta.Transform
public meta import Lean.Elab.Tactic.Basic

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring
open BirdDet

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

/-- Given `cz.proof : cz.subject! = 0`, certify the product `x * cz.subject =
  0` without evaluating `x`.

`mulP` is HMul.hmul, partially applied with types and instances (see
`destructMul?`).
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

structure Ctx {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  rα : Q(CommRing $α)
  /-- `Ring` evaluation cache for the scalar ring. -/
  cα : Common.Cache sα
  /-- Proof-producing ring arithmetic. -/
  rc : Common.RingCompute RatCoeff sα
  /-- `CommRing` expression, using the same spelilng as the
    `birdDet goal.-/
  commRingInst : Expr
  dimension : Nat
  dimensionExpr : Expr
  array : Expr
  arrayEntries : Array Expr
  /-- Canonical `@get R inst n A` — both the matrix reader and the initial
  entry function of the recurrence. -/
  getP : Expr

structure AppResult {u : Level} (α : Q(Type u)) where
  /-- The application expression -/
  app : Q($α)
  /-- The result of the application -/
  result : Q($α)
  /-- A proof that app and result are equal -/
  proof : Q($app = $result)

namespace Ctx

def iterP (ctx : Ctx sα) (t : Nat) : Expr :=
  mkAppN
    (mkConst ``iter [u])
    #[α, ctx.commRingInst, ctx.dimensionExpr, ctx.array, mkNatLit t, ctx.getP]

/-- Constructs an equality between `get i j` and arrayEntries[i * dimenstion + j]

app: `get ctx.dimension ctx.array i j`
result: `ctx.arrayEntries[i * ctx.dimension + j]`
proof: app = result
-/
def get (ctx : Ctx sα) (i j : Nat) : MetaM (AppResult α) := do
  let app := mkApp2 ctx.getP (mkNatLit i) (mkNatLit j)
  let result := ctx.arrayEntries[i * ctx.dimension + j]!
  let app : Q($α) := app
  let result : Q($α) := result
  -- let proof ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq app result)
  let proof ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq app result)
  return {app, result, proof}

/-- Certify the evaluation of `e` using the Ring tactic -/
def eval (ctx : Ctx sα) (e : Q($α)) : AtomM (Cert sα) := do
  let res ← Common.eval rcℕ ctx.rc ctx.cα e
  return {norm := res.expr, val := res.val, proof := res.proof, isZero := isZeroVal res.val}

end Ctx

abbrev CertM {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) :=
  ReaderT (Ctx sα) AtomM

/-- Returns a certificate whose subject is `get n A i j`.

```
get n A i j = elem  -- By rfl
            = norm  -- Ring.eval on the entry
```
-/
def certEntry (i j : Nat) : CertM sα (Cert sα) := do
  let ctx ← read
  let elemApp ← ctx.get i j
  let ce ← ctx.eval elemApp.result
  let proof ← mkExpectedTypeHint (← mkEqTrans elemApp.proof ce.proof) (← mkEq elemApp.app ce.norm)
  return {ce with proof}

end Cert

end
