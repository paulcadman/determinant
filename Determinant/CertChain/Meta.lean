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

namespace Meta

structure BinaryOpApp where
  partialApp : Expr
  x : Expr
  y : Expr

structure UnaryOpApp where
  partialApp : Expr
  x : Expr

/-- A convenience type representing an equality roof `proof : lhs = rhs`. -/
structure EqProof {u : Level} (α : Q(Type u)) where
  lhs : Q($α)
  rhs : Q($α)
  proof : Q($lhs = $rhs)

/-- Parse an `EqProof` or throw -/
def expectProof {u : Level} {α : Q(Type u)} (proof : Expr) : MetaM (EqProof α) := do
  let some (_, lhs, rhs) := (← inferType proof).eq?
    | throwError "expectProof: proof is not an equality: {proof}"
  let some lhs ← checkTypeQ lhs α
    | throwError "expectProof: lhs does not have expected type{indentExpr α}"
  let some rhs ← checkTypeQ rhs α
    | throwError "expectProof: rhs does not have expected type{indentExpr α}"
  let proof ← mkExpectedTypeHint proof (← mkEq lhs rhs)
  return {lhs, rhs, proof}

/-- Parse an addition expression or throw. -/
def expectAdd (context : String) (e : Expr) : MetaM BinaryOpApp := do
  match_expr e with
  | HAdd.hAdd α β γ inst x y =>
      return ⟨mkApp4 e.getAppFn α β γ inst, x, y⟩
  | _ => throwError "{context}: expected add, got {e}"

/-- Parse a multiplication expression or throw. -/
def expectMul (context : String) (e : Expr) : MetaM BinaryOpApp := do
  match_expr e with
  | HMul.hMul α β γ inst x y =>
      return ⟨mkApp4 e.getAppFn α β γ inst, x, y⟩
  | _ => throwError "{context}: expected mul, got {e}"

/-- Parse a negation expression or throw. -/
def expectNeg (context : String) (e : Expr) : MetaM UnaryOpApp := do
  match_expr e with
  | Neg.neg α inst x =>
      return ⟨mkApp2 e.getAppFn α inst, x⟩
  | _ => throwError "{context}: expected neg, got {e}"

/-- Extract the function argument from a `sumFrom` expression. -/
def expectSumFromFun (context : String) (e : Expr) : MetaM Expr := do
  let_expr sumFrom _ _ _ _ f := e
    | throwError "{context}: expected sumFrom, got {e}"
  return f

/-- Given h₁ : x = x' and h₂ : y = y', construct `opP x y = opP x' y'` -/
def mkCongrBinop (opP h₁ h₂ : Expr) : MetaM Expr := do
  mkCongr (← mkCongrArg opP h₁) h₂

/-- Chain three equalities `h₁ : a = b`, `h₂ : b = c`, `h₃ : c = d` into `a = d` -/
def trans3 (h₁ h₂ h₃ : Expr) : MetaM Expr := do
  mkEqTrans h₁ (← mkEqTrans h₂ h₃)

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

/-- Parse an array literal into an array of element exrpessions -/
def arrayLiteral? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← zetaReduce (← whnf e)
  match_expr e with
  | Array.mk _ xs =>
      let some elems ← getListLit? xs | return none
      return some elems
  | List.toArray _ xs =>
      let some elems ← getListLit? xs | return none
      return some elems
  | _ => return none

/-- Information parsed by `reifyBirdDet` -/
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

end Meta

end
