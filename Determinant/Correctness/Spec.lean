module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

@[expose] public section

namespace Correctness

variable {R : Type*} [CommRing R]

/--
One scalar-entry step of Bird's determinant recurrence.

This is the `(i, j)` entry of `mu(F) * A` from the paper. The proof works with
this scalar form instead of constructing the whole matrix `mu(F)`.
-/
def stepEntry {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (F : Fin n → Fin n → R)
    (i j : Fin n) : R :=
  let diag : R := -∑ k : Fin n, if i < k then F k k else 0
  diag * A i j
    + ∑ k : Fin n, if i < k then F i k * A k j else 0

/--
Scalar-entry iteration of Bird's determinant recurrence.

The expression

```lean
iterEntry A p (fun i j => A i j) i j
```

is Bird's `x^(p)_ij`, the `(i, j)` entry of `F_A^p(A)`.
-/
def iterEntry {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) :
    Nat → (Fin n → Fin n → R) → Fin n → Fin n → R
  | 0, F => F
  | p + 1, F =>
      fun i j => stepEntry A (iterEntry A p F) i j

/-- Proof-friendly scalar Bird determinant specification. -/
def birdDetSpec {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) : R :=
  match n with
  | 0 => 1
  | k + 1 =>
      (-1 : R)^k *
        iterEntry A k (fun i j => A i j) 0 0

theorem stepEntry_eq {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (F : Fin n → Fin n → R)
    (i j : Fin n) :
    stepEntry A F i j =
      (-∑ k : Fin n, if i < k then F k k else 0) * A i j
        + ∑ k : Fin n, if i < k then F i k * A k j else 0 := by
  rfl

theorem iterEntry_zero {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (F : Fin n → Fin n → R) :
    iterEntry A 0 F = F := by
  rfl

theorem iterEntry_succ {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (F : Fin n → Fin n → R) :
    iterEntry A (p + 1) F =
      fun i j => stepEntry A (iterEntry A p F) i j := by
  rfl

theorem birdDetSpec_zero
    (A : Matrix (Fin 0) (Fin 0) R) :
    birdDetSpec A = 1 := by
  rfl

theorem birdDetSpec_succ {k : Nat}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    birdDetSpec A =
      (-1 : R)^k * iterEntry A k (fun i j => A i j) 0 0 := by
  rfl

end Correctness
