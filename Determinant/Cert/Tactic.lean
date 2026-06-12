module

public import Determinant.Cert.Bird
public import Mathlib.Tactic.Ring
public import Qq
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Meta.Transform
public meta import Lean.Elab.Tactic.Basic

public meta section

namespace Cert

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring

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

end Cert

end
