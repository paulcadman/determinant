module

public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

namespace BirdDet

/-- Row-major index for an `n × m` flat matrix, using `m` as the row stride. -/
def flatIdx (m i j : Nat) : Nat :=
  i * m + j

theorem flatIdx_lt_mul
  {n m i j : Nat} (hi : i < n) (hj : j < m) :
    flatIdx m i j < n * m := by
      unfold flatIdx
      calc
        i * m + j < i * m + m := Nat.add_lt_add_left hj (i * m)
        _ = (i + 1) * m := Eq.symm (Nat.succ_mul i m)
        _ ≤ n * m := Nat.mul_le_mul_right m hi

/--
Interpret a flat row-major array as an `n × m` matrix, checking that the array
has exactly `n * m` entries.

The dimensions `n` and `m` are implicit for direct use, but frontend code should
usually pass `(n := rows)` and `(m := cols)` explicitly because Lean cannot infer
them from the size proof alone.
-/
def ofFlatArray
    {R : Type*}
    {n m : Nat}
    (A : Array R)
    (hA : A.size = n * m) :
    Matrix (Fin n) (Fin m) R :=
  fun i j =>
    A[flatIdx m i.val j.val]'(by
      rw [hA]
      exact flatIdx_lt_mul i.isLt j.isLt)

theorem ofFlatArray_apply
    {R : Type*}
    {n m : Nat}
    (A : Array R)
    (hA : A.size = n * m)
    (i : Fin n) (j : Fin m) :
    ofFlatArray A hA i j =
      A[flatIdx m i.val j.val]'(by
        rw [hA]
        exact flatIdx_lt_mul i.isLt j.isLt) := rfl

theorem getD_eq_get_of_lt
    {α : Type*}
    (A : Array α) (idx : Nat) (fallback : α) (h : idx < A.size) :
    A.getD idx fallback = A[idx]'h := by
  simp [Array.getD, h]

end BirdDet

end
