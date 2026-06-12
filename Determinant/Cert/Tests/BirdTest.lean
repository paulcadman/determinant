module

import Determinant.Cert.Bird
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Cert

variable
  {R : Type*}
  [CommRing R]

example : birdDet 0 #[] = (Matrix.det !![] : ℤ) := by
  cbv

example : birdDet 1 #[2] = (Matrix.det !![2] : ℤ) := by
  cbv

example : birdDet 2 #[1, 0, 0, 1] = (Matrix.det !![1, 0; 0, 1] : ℤ) := by
  cbv

example (a b c d : R) : birdDet 2 #[a, b, c, d] = a * d - b * c:= by
  simp [birdDet, iter, get, sumFrom_step, sumFrom_stop]
  ring

end Cert
