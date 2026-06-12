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

end Cert

end
