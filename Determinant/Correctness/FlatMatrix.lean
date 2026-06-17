module

public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

namespace BirdDet

/-- Row-major index for an `n × n` flat matrix. -/
def flatIdx (n i j : Nat) : Nat :=
  i * n + j

theorem flatIdx_lt_mul
    {n i j : Nat} (hi : i < n) (hj : j < n) :
    flatIdx n i j < n * n := by
  unfold flatIdx
  have h1 : i * n + j < i * n + n := Nat.add_lt_add_left hj _
  have h2 : i * n + n = (i + 1) * n := by
    rw [Nat.succ_mul]
  have h3 : i + 1 ≤ n := Nat.succ_le_of_lt hi
  have h4 : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n h3
  exact lt_of_lt_of_le (by simpa [h2] using h1) h4

/--
Interpret a flat row-major array as a square matrix, checking that the array has
exactly `n * n` entries.

The dimension `n` is implicit for direct use, but frontend code should usually
pass `(n := ...)` explicitly because Lean cannot infer it from the size proof
under `Matrix.det`.
-/
def ofFlatArray
    {R : Type*}
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    Matrix (Fin n) (Fin n) R :=
  fun i j =>
    A[flatIdx n i.val j.val]'(by
      rw [hA]
      exact flatIdx_lt_mul i.isLt j.isLt)

theorem ofFlatArray_apply
    {R : Type*}
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n)
    (i j : Fin n) :
    ofFlatArray A hA i j =
      A[flatIdx n i.val j.val]'(by
        rw [hA]
        exact flatIdx_lt_mul i.isLt j.isLt) := rfl

theorem getD_eq_get_of_lt
    {α : Type*}
    (A : Array α) (idx : Nat) (fallback : α) (h : idx < A.size) :
    A.getD idx fallback = A[idx]'h := by
  simp [Array.getD, h]

end BirdDet

end
