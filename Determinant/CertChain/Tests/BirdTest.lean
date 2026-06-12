module

import Determinant.CertChain.Bird
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace CertChain

variable
  {R : Type*}
  [CommRing R]

example : birdDet 0 #[] = (Matrix.det !![] : ℤ) := by
  cbv

example : birdDet 1 #[2] = (Matrix.det !![2] : ℤ) := by
  cbv

example : birdDet 2 #[1, 0, 0, 1] = (Matrix.det !![1, 0; 0, 1] : ℤ) := by
  cbv

/-- Test that the birdDet equality can be proved just using the Bird recurrence
  lemmas, rfl, decide, and a final ring -/
example (a b c d : R) : birdDet 2 #[a, b, c, d] = a * d - b * c := by
  let A := #[a, b, c, d]
  calc birdDet 2 A
      = (-1 : R)^1 * iter 2 A 1 (get 2 A) 0 0 := birdDet_eq 2 1 _ rfl
    _ = (-1 : R)^1 * 
          (-(sumFrom 2 1 fun k => iter 2 A 0 (get 2 A) k k) * a
            + sumFrom 2 1 fun k => iter 2 A 0 (get 2 A) 0 k * get 2 A k 0) := rfl
    _ = (-1 : R)^1 * (-(d + 0) * a + (b * c + 0)) := by
        rw [sumFrom_step 2 1 _ (by decide), sumFrom_stop 2 2 _ (by decide),
            sumFrom_step 2 1 _ (by decide), sumFrom_stop 2 2 _ (by decide)]
        exact rfl
    _ = a * d - b * c := by
      ring

end CertChain
