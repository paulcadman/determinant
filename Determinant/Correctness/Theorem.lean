module

public import Determinant.Correctness.Invariant

@[expose] public section

namespace Correctness

/-!
This file proves the final bridge from the proof-friendly Bird determinant specification to
Mathlib's determinant:

```
Correctness.birdDetSpec A = A.det
```

The theorem `birdDetSpec_eq_det` is proved below from Bird's invariant
`iterEntry_formula`.

Future adapter TODOs, intentionally not part of this proof milestone:

```
theorem flatBird_eq_birdDetSpec ...
theorem numericBird_eq_birdDetSpec ...
theorem exbaseBird_eq_birdDetSpec ...
```
-/

theorem vcons_zero_finalTailWord_eq_fullWord (k : Nat) :
    vcons (0 : Fin (k + 1)) (finalTailWord k) = fullWord (k + 1) := by
  apply List.Vector.ext
  intro q
  cases q using Fin.cases with
  | zero =>
      simp [fullWord, vcons_head]
  | succ q =>
      simp [fullWord, finalTailWord, vcons_get_succ]

theorem iterEntry_top_left_eq_det
    {R : Type*} [CommRing R]
    {k : Nat}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    Correctness.iterEntry A k (fun i j => A i j) 0 0 =
      (-1 : R)^k * A.det := by
  rw [iterEntry_formula A k 0 0]
  rw [TailWords_final_singleton]
  simp [vcons_zero_finalTailWord_eq_fullWord, wordDet_full_eq_det]

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

example {R : Type*} [CommRing R]
    (A : Matrix (Fin 0) (Fin 0) R) :
    Correctness.birdDetSpec A = A.det := by
  exact birdDetSpec_eq_det A

example {R : Type*} [CommRing R]
    (A : Matrix (Fin 1) (Fin 1) R) :
    Correctness.birdDetSpec A = A.det := by
  exact birdDetSpec_eq_det A

example {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) :
    Correctness.birdDetSpec A = A.det := by
  exact birdDetSpec_eq_det A

example :
    Correctness.birdDetSpec (R := ℤ)
      !![1, 2;
         3, 4]
      =
    Matrix.det
      !![1, 2;
         3, 4] := by
  exact birdDetSpec_eq_det
    (A := (Matrix.of ![![1, 2], ![3, 4]] :
      Matrix (Fin 2) (Fin 2) ℤ))

end Correctness
