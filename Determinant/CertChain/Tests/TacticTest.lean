module

public import Determinant.CertChain.Tactic

namespace Tests.Tactic

open BirdDet

variable
  {R : Type*}
  [CommRing R]

example : birdDet 0 (#[] : Array ℤ) = 1 := by
  cert_bird_det

example : birdDet 1 #[5] = (5 : ℤ) := by
  cert_bird_det

example : birdDet 2 #[1, 2, 3, 4] = (-2 : ℤ) := by
  cert_bird_det

example : birdDet 2 #[1, 2, 2, 4] = (0 : ℤ) := by
  cert_bird_det

example (a b c d : R) : birdDet 2 #[a, b, c, d] = a * d - b * c := by
  cert_bird_det

lemma test_case_8 :
    birdDet 8
      (#[ 2,  0, -1,  0,  0,  0,  0,  0,
          0,  2,  0, -1,  0,  0,  0,  0,
         -1,  0,  2, -1,  0,  0,  0,  0,
          0, -1, -1,  2, -1,  0,  0,  0,
          0,  0,  0, -1,  2, -1,  0,  0,
          0,  0,  0,  0, -1,  2, -1,  0,
          0,  0,  0,  0,  0, -1,  2, -1,
          0,  0,  0,  0,  0,  0, -1,  2] : Array ℤ) = 1 := by
  cert_bird_det

end Tests.Tactic
