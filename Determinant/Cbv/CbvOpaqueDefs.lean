module

public meta import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Ring.Defs

/-!
`cbv` opaque definitions to avoid `cbv` unfolding generic ring operations
through typeclass projections.

Each definition uses minimal typeclass constraints (instead of CommRing)
because this reduces the size of the terms prduced by the cbv reduction.
-/

@[expose] public section

namespace CbvOpaqueDefs

variable {R : Type*}

@[cbv_opaque] def rzero [Zero R] : R := 0

@[cbv_opaque] def rone [One R] : R := 1

@[cbv_opaque] def rint [IntCast R] (n : Int) : R := n

@[cbv_opaque] def radd [Add R] (x y : R) : R := x + y

@[cbv_opaque] def rmul [Mul R] (x y : R) : R := x * y

@[cbv_opaque] def rneg [Neg R] (x : R) : R := -x

@[cbv_opaque] def rsub [Sub R] (x y : R) : R := x - y

@[cbv_opaque] def rdiv [Div R] (x y : R) : R := x / y

@[cbv_opaque] def rpow [Pow R Nat] (x : R) (n : Nat) : R := x ^ n

@[cbv_opaque] def ratom (x : R) : R := x

theorem rzero_radd [AddZeroClass R] (x : R) : radd rzero x = x := by
  simp [radd, rzero]

theorem radd_rzero [AddZeroClass R] (x : R) : radd x rzero = x := by
  simp [radd, rzero]

theorem zero_radd [AddZeroClass R] (x : R) : radd 0 x = x := by
  simp [radd]

theorem radd_zero [AddZeroClass R] (x : R) : radd x 0 = x := by
  simp [radd]

theorem rzero_rmul [MulZeroClass R] (x : R) : rmul rzero x = rzero := by
  simp [rmul, rzero]

theorem rmul_rzero [MulZeroClass R] (x : R) : rmul x rzero = rzero := by
  simp [rmul, rzero]

theorem zero_rmul [MulZeroClass R] (x : R) : rmul 0 x = 0 := by
  simp [rmul]

theorem rmul_zero [MulZeroClass R] (x : R) : rmul x 0 = 0 := by
  simp [rmul]

theorem rone_rmul [MulOneClass R] (x : R) : rmul rone x = x := by
  simp [rmul, rone]

theorem rmul_rone [MulOneClass R] (x : R) : rmul x rone = x := by
  simp [rmul, rone]

theorem one_rmul [MulOneClass R] (x : R) : rmul 1 x = x := by
  simp [rmul]

theorem rmul_one [MulOneClass R] (x : R) : rmul x 1 = x := by
  simp [rmul]

theorem rneg_rzero [NegZeroClass R] : rneg (R := R) rzero = rzero := by
  simp [rneg, rzero]

theorem rneg_zero [NegZeroClass R] : rneg (R := R) 0 = 0 := by
  simp [rneg]

theorem ratom_eq (x : R) : ratom x = x := by
  simp [ratom]

private meta partial def expandSymTerm : Lean.TSyntax `term → Lean.MacroM (Lean.TSyntax `term)
  | `(term| 0) => `(term| rzero)
  | `(term| 1) => `(term| rone)
  | `(term| $n:num) => `(term| rint ($n : Int))
  | `(term| ($x:term)) => expandSymTerm x
  | `(term| - $x:term) => do
    let x ← expandSymTerm x
    `(term| rneg $x)
  | `(term| $x:term + $y:term) => do
    let x ← expandSymTerm x
    let y ← expandSymTerm y
    `(term| radd $x $y)
  | `(term| $x:term - $y:term) => do
    let x ← expandSymTerm x
    let y ← expandSymTerm y
    `(term| rsub $x $y)
  | `(term| $x:term / $y:term) => do
    let x ← expandSymTerm x
    let y ← expandSymTerm y
    `(term| rdiv $x $y)
  | `(term| $x:term * $y:term) => do
    let x ← expandSymTerm x
    let y ← expandSymTerm y
    `(term| rmul $x $y)
  | `(term| $x:term ^ $n:term) => do
    let x ← expandSymTerm x
    `(term| rpow $x ($n : Nat))
  | x => `(term| ratom $x)


/-- Convert a ring expression into a cbv_opaque ring expression

Examples:

* `sym% 0` -> `rzero`
* `sym% 1` -> `rone`
* `sym% 2 * a` -> `rmul (rint 2) a`
* `sym% `1 - 3` -> `rsub rone (rint 3)`
* `sym% `2 + a` -> `radd (rint 2) a`
* `sym% `1 / x` -> `rdiv rone (ratom x)`
* `sym% -(2 + a) -> `rneg (radd (rint2) a)`
* `sym% X` -> `ratom X`
-/
macro "sym% " x:term : term => expandSymTerm x

/-- Convert each element in an array of ring expressions to cbv_opaque ring
  expressions using `sym%` -/
macro "symflat% " "#[" xs:term,* "]" : term => `(#[$[sym% $xs],*])

end CbvOpaqueDefs

end
