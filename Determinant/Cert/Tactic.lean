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


end Cert

end
