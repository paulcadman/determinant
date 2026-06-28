module

import Determinant.Correctness.FlatMatrix
import Determinant.Correctness.Theorem

open scoped BigOperators

namespace Correctness

section FlatMatrixExamples

example :
    (BirdDet.ofFlatArray (m := 2) (n := 3)
      #[(1 : ℤ), 2, 3, 4, 5, 6] rfl)
        (1 : Fin 2) (2 : Fin 3) = 6 := by
  rfl

example :
    (BirdDet.ofFlatArray (m := 3) (n := 2)
      #[(1 : ℤ), 2, 3, 4, 5, 6] rfl)
        (2 : Fin 3) (1 : Fin 2) = 6 := by
  rfl

/--
Application type mismatch
-/
#guard_msgs (substring := true) in
#check (BirdDet.ofFlatArray (m := 2) (n := 3) #[(1 : ℤ), 2, 3, 4, 5] rfl)

end FlatMatrixExamples

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
