module

import Determinant.Bird
import Determinant.CbvOpaqueDefs
public import Mathlib.Lean.Expr.Basic
public meta import Lean.Meta.Tactic.Cbv.Main
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Init.CbvSimproc
meta import Mathlib.Tactic
public import Mathlib.Algebra.Ring.Defs


public meta section

namespace Bird

open Lean Meta Sym.Simp
open CbvOpaqueDefs

/-- Construct an equality proof from `eqThm` and `args and use the RHS as a `cbv` step -/
def stepFromEqProof (eqThm : Name) (args : Array (Option Expr)) : Sym.Simp.SimpM Result := do
  let proof ← mkAppOptM eqThm args
  let some (_, _, rhs) := (← Meta.inferType proof).eq? | return .rfl
  return .step rhs proof

/-- Pre-cbv simplification for symbolic addition with zero

```
  rzero + y = y
  x + rzero = x
  0 + y = y
  x + 0 = x
```
-/
cbv_simproc ↓ evalRaddZero (radd _ _) := fun e => do
  let_expr radd R _ x y := e | return .rfl
  if x.isAppOf' ``rzero then stepFromEqProof ``rzero_radd #[R, none, y]
  else if y.isAppOf' ``rzero then stepFromEqProof ``radd_rzero #[R, none, x]
  else if let some 0 := x.numeral? then stepFromEqProof ``zero_radd #[R, none, y]
  else if let some 0 := y.numeral? then stepFromEqProof ``radd_zero #[R, none, x]
  else return .rfl

/-- Pre-cbv simplification for symbolic multiplications with zero or one

```
  rzero * y = rzero
  x * rzero = rzero
  0 * y = 0
  x * 0 = 0
  rone * y = y
  x * rone = x
  1 * y = y
  x * 1 = x
```
-/
cbv_simproc ↓ evalRMulZeroOne (rmul _ _) := fun e => do
  let_expr rmul R _ x y := e | return .rfl
  if x.isAppOf' ``rzero then stepFromEqProof ``rzero_rmul #[R, none, y]
  else if y.isAppOf' ``rzero then stepFromEqProof ``rmul_rzero #[R, none, x]
  else if let some 0 := x.numeral? then stepFromEqProof ``zero_rmul #[R, none, y]
  else if let some 0 := y.numeral? then stepFromEqProof ``rmul_zero #[R, none, x]
  else if x.isAppOf' ``rone then stepFromEqProof ``rone_rmul #[R, none, y]
  else if y.isAppOf' ``rone then stepFromEqProof ``rmul_one #[R, none, x]
  else if let some 1 := x.numeral? then stepFromEqProof ``one_rmul #[R, none, y]
  else if let some 1 := y.numeral? then stepFromEqProof ``rmul_one #[R, none, x]
  else return .rfl

/-- Pre-cbv simplification for symbolic negation of zero

```
  rneg rzero = rzero
  rneg 0 = 0
```

-/
cbv_simproc ↓ evalRNegZero (rneg _) := fun e => do
  let_expr rneg R _ x := e | return .rfl
  if x.isAppOf' ``rzero then stepFromEqProof ``rneg_rzero #[R, none]
  else if let some 0 := x.numeral? then stepFromEqProof ``rneg_zero #[R, none]
  else return .rfl

namespace Test

variable
  {R : Type*}
  [CommRing R]

example (x : R) : radd (0 : R) x = x := by
  cbv

example (x : R) : radd x (0 : R) = x := by
  cbv

example (x : R) : radd rzero x = x := by
  cbv

example (x : R) : radd x rzero = x := by
  cbv

example (x : R) : (radd rzero <| radd (0 : R) x) = x := by
  cbv

example (x : R) : rmul x rone = x := by
  cbv

example (x : R) : rmul rone x = x := by
  cbv

example (x : R) : rmul 1 x = x := by
  cbv

example (x : R) : rmul x 1 = x := by
  cbv

example (x : R) : rmul x rzero = rzero := by
  cbv

example (x : R) : rmul rzero x = rzero := by
  cbv

example (x : R) : rmul 0 x = 0 := by
  cbv

example (x : R) : rmul x 0 = 0 := by
  cbv

example : rneg (rzero : R) = rzero := by
  cbv

example : rneg (0 : R) = 0 := by
  cbv

end Test

end Bird

end
