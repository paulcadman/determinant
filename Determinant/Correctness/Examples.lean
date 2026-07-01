module

import Determinant.Correctness.FlatMatrix
import Determinant.Correctness.Theorem

open scoped BigOperators

namespace Correctness

section FlatMatrixExamples

example :
    (Matrix.ofFlatArray (m := 2) (n := 3)
      #[(1 : ℤ), 2, 3, 4, 5, 6] rfl)
        (1 : Fin 2) (2 : Fin 3) = 6 := by
  rfl

example :
    (Matrix.ofFlatArray (m := 3) (n := 2)
      #[(1 : ℤ), 2, 3, 4, 5, 6] rfl)
        (2 : Fin 3) (1 : Fin 2) = 6 := by
  rfl

/--
Application type mismatch
-/
#guard_msgs (substring := true) in
#check (Matrix.ofFlatArray (m := 2) (n := 3) #[(1 : ℤ), 2, 3, 4, 5] rfl)

end FlatMatrixExamples

section FlatAdapterExamples

example {R : Type*} [CommRing R]
    (A : Array R) (hA : A.size = 2 * 2)
    (i j : Fin 2) :
    BirdDet.get 2 A i.val j.val =
      Matrix.ofFlatArray (m := 2) (n := 2) A hA i j := by
  exact BirdDet.get_eq_ofFlatArray_square A hA i j

example {R : Type*} [CommRing R]
    (f : Nat → R) (i : Fin 4) :
    BirdDet.sumFrom 4 (i.val + 1) f =
      ∑ k : Fin 4, if i < k then f k.val else 0 := by
  exact BirdDet.sumFrom_fin_tail 4 i f

example {R : Type*} [CommRing R]
    (A : Array R) (hA : A.size = 3 * 3)
    (F : Nat → Nat → R)
    (i j : Fin 3) :
    (-(BirdDet.sumFrom 3 (i.val + 1) fun k => F k k) *
        BirdDet.get 3 A i.val j.val
      +
      BirdDet.sumFrom 3 (i.val + 1) fun k =>
        F i.val k * BirdDet.get 3 A k j.val)
      =
    Correctness.stepEntry
      (Matrix.ofFlatArray (m := 3) (n := 3) A hA)
      (BirdDet.finView F)
      i j := by
  exact BirdDet.step_formula_bridge_ofFlatArray A hA F i j

example {R : Type*} [CommRing R]
    (A : Array R) (hA : A.size = 3 * 3) :
    BirdDet.birdDet 3 A =
      Correctness.birdDetSpec
        (Matrix.ofFlatArray (m := 3) (n := 3) A hA) := by
  exact BirdDet.birdDet_eq_birdDetSpec_ofFlatArray A hA

end FlatAdapterExamples

section InvariantExamples

example {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    Correctness.iterEntry A 0 (fun i j => A i j) i j =
      (-1 : R)^0 *
        (∑ α ∈ TailWords i 0,
          wordDet A (vcons i α) (vcons j α)) := by
  simpa using iterEntry_formula A 0 i j

example {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    Correctness.iterEntry A 1 (fun i j => A i j) i j =
      (-1 : R)^1 *
        (∑ α ∈ TailWords i 1,
          wordDet A (vcons i α) (vcons j α)) := by
  simpa using iterEntry_formula A 1 i j

end InvariantExamples

section TheoremExamples

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

end TheoremExamples

end Correctness
