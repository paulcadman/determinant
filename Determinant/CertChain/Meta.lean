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

/-- A convenience type representing an equality proof `proof : lhs = rhs`. -/
structure EqProof {u : Level} (α : Q(Type u)) where
  lhs : Q($α)
  rhs : Q($α)
  proof : Q($lhs = $rhs)

/-- Parse an `EqProof` or throw -/
def expectProof {u : Level} {α : Q(Type u)} (context : String) (proof : Expr) :
    MetaM (EqProof α) := do
  let some (_, lhs, rhs) := (← inferType proof).eq?
    | throwError "{context}: expected equality proof, got {proof}"
  let some lhs ← checkTypeQ lhs α
    | throwError "{context}: lhs does not have expected type{indentExpr α}"
  let some rhs ← checkTypeQ rhs α
    | throwError "{context}: rhs does not have expected type{indentExpr α}"
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

/-- Given h₁ : x = x' and h₂ : y = y', construct `opP x y = opP x' y'` -/
def mkCongrBinop (opP h₁ h₂ : Expr) : MetaM Expr := do
  mkCongr (← mkCongrArg opP h₁) h₂

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

/-- Parse an array literal into an array of element expressions. -/
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

/-- Recognize both raw kernel Nat literals and ordinary elaborated Nat numerals. -/
def natLiteral? (e : Expr) : Option Nat :=
  e.rawNatLit? <|>
    match_expr e with
    | OfNat.ofNat ty n _ =>
        if ty.isConstOf ``Nat then n.rawNatLit? else none
    | _ => none

/-- Information parsed by `reifyBirdDet` -/
structure BirdDetInfo where
  level : Level
  ringType : Q(Type level)
  birdRingInst : Q(CommRing $ringType)
  dimension : Nat
  dimensionExpr : Q(Nat)
  arrayExpr : Q(Array $ringType)
  arrayEntries : Array Q($ringType)

def reifyBirdDet (e : Expr) : MetaM BirdDetInfo := do
  let e ← instantiateMVars e
  let ⟨level, α, _⟩ ← inferTypeQ' e
  let_expr birdDet _ birdRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let some birdRingInst ← checkTypeQ birdRingInst q(CommRing $α)
    | throwError "expected `birdDet` ring instance to have type{indentExpr q(CommRing $α)}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionExpr ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected the dimension to have type `Nat`, got {dimensionExpr}"
  let some dimension := natLiteral? dimensionExpr
    | throwError "expected the dimension to be a `Nat` literal, got {dimensionExpr}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected the array to have type{indentExpr q(Array $α)}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, expected {dimension * dimension}"
  let arrayEntries ← arrayEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry α
      | throwError "expected array entry to have type{indentExpr α}"
    return entry
  return {level, ringType := α, birdRingInst, dimension, dimensionExpr, arrayExpr, arrayEntries}

end Meta

end
