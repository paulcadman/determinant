module

public import Determinant.Correctness.FlatAdapter
public import Determinant.Correctness.Invariant

@[expose] public section

namespace Correctness

/-!
This file proves the final bridge from the proof-friendly Bird determinant
specification to Mathlib's determinant:

```
Correctness.birdDetSpec A = A.det
```

The theorem `birdDetSpec_eq_det` is proved below from Bird's invariant
`iterEntry_formula`. At the final step, this file uses `iterEntry_formula` at
`p = n - 1`, then uses `TailWords_final_singleton` and `wordDet_full_eq_det` to
derive `birdDetSpec_eq_det`.

The final theorems in `BirdDet` combine this with
`BirdDet.birdDet_eq_birdDetSpec_ofFlatArray` to connect the flat-array
implementation used by the tactic to `Matrix.det`.
-/

/-- `0 :: [1, ..., k] = [0, ..., k]`. -/
theorem vcons_zero_finalTailWord_eq_fullWord (k : Nat) :
    vcons (0 : Fin (k + 1)) (finalTailWord k) = fullWord (k + 1) := by
  apply List.Vector.ext
  intro q
  cases q using Fin.cases with
  | zero =>
      simp [fullWord, vcons_head]
  | succ q =>
      simp [fullWord, finalTailWord, vcons_get_succ]

/--
Specializes Bird equation (1) to `p = k`, `i = 0`, and `j = 0`.

This is the determinant-value part of the paper's conclusion: at
`p = n - 1`, the top-left entry carries the determinant up to the final sign.
-/
theorem iterEntry_top_left_eq_det
    {R : Type*} [CommRing R]
    {k : Nat}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    Correctness.iterEntry A k (fun i j => A i j) 0 0 =
      (-1 : R)^k * A.det := by
  rw [iterEntry_formula A k 0 0]
  rw [TailWords_final_singleton]
  simp [vcons_zero_finalTailWord_eq_fullWord, wordDet_full_eq_det]

/--
Applies the final sign correction.

The paper observes that only the top-left entry survives at `p = n - 1`; the
proof-friendly determinant specification extracts that entry and cancels the
two factors of `(-1)^k`.
-/
theorem birdDetSpec_eq_det_pos
    {R : Type*} [CommRing R]
    {k : Nat}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    Correctness.birdDetSpec A = A.det := by
  calc
    Correctness.birdDetSpec A
        = (-1 : R)^k *
            Correctness.iterEntry A k (fun i j => A i j) 0 0 := by
              rw [Correctness.birdDetSpec_succ]
    _ = (-1 : R)^k * ((-1 : R)^k * A.det) := by
              rw [iterEntry_top_left_eq_det]
    _ = A.det := by
              rw [← mul_assoc, neg_one_pow_mul_self, one_mul]

theorem det_fin_zero_local
    {R : Type*} [CommRing R]
    (A : Matrix (Fin 0) (Fin 0) R) :
    A.det = 1 := by
  classical
  simp [Matrix.det_apply]

/-
The final proof is:
1. Use `iterEntry_formula` with `p = k`, `i = 0`, and `j = 0`.
2. `TailWords_final_singleton` reduces the sum to `[1, ..., k]`.
3. `vcons 0 finalTailWord = fullWord`.
4. `wordDet_full_eq_det` turns the word determinant into `A.det`.
5. The two factors `(-1)^k` cancel.
-/
/--
Final correctness theorem for all `n`.

This is the formal determinant-value statement corresponding to Bird's Theorem
1: the Bird recurrence computes Mathlib's determinant.
-/
theorem birdDetSpec_eq_det
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) :
    Correctness.birdDetSpec A = A.det := by
  cases n with
  | zero =>
      rw [Correctness.birdDetSpec_zero]
      exact (det_fin_zero_local A).symm
  | succ k =>
      exact birdDetSpec_eq_det_pos A

end Correctness

namespace BirdDet

/--
Mathlib's determinant of the checked flat-array matrix agrees with the
flat-array Bird implementation.
-/
theorem det_ofFlatArray_eq_birdDet
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    Matrix.det (ofFlatArray (n := n) (m := n) A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec_ofFlatArray A hA]
  exact (Correctness.birdDetSpec_eq_det (ofFlatArray (n := n) (m := n) A hA)).symm

/-- Symmetric orientation of `det_ofFlatArray_eq_birdDet`. -/
theorem birdDet_eq_det_ofFlatArray
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    birdDet n A = Matrix.det (ofFlatArray (n := n) (m := n) A hA) :=
  (det_ofFlatArray_eq_birdDet A hA).symm

end BirdDet
