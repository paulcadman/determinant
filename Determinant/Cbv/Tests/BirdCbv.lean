module

public import Determinant.Cbv.Tactic
public import Determinant.Cbv.CbvOpaqueDefs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Field

namespace Tests.BirdCbv

open CbvOpaqueDefs

variable
  {R : Type*}
  [CommRing R]

lemma test_case_19 (a b c d : R) :
    Bird.birdDetEntry
      2
      (symflat%
        #[a , b,
          c , d ]) = a * d - b * c := by
  cbv_bird_entry_det

lemma test_case_13_direct (a b c : R) :
    Bird.birdDet
      3
      (symflat%
        #[a   , b   , c,
          2*a , b   , 0,
          0   , 2*a , b]) = -a * (b ^2 -4 * a * c) := by
  cbv_bird_det

/--
inst✝.1.1.2.1.1.1 2 a
-/
#guard_msgs (substring := true) in
example (a b c : R) :
    Bird.birdDetEntry
      3
      (#[a   , b   , c,
         2*a , b   , 0,
         0   , 2*a , b]) = -a * (b ^2 -4 * a * c) := by
  conv_lhs =>
    cbv

lemma test_case_13 (a b c : R) :
    Bird.birdDetEntry
      3
      (symflat%
        #[a   , b   , c,
          2*a , b   , 0,
          0   , 2*a , b]) = -a * (b ^2 -4 * a * c) := by
  cbv_bird_entry_det

attribute [cbv_opaque] Polynomial.X
attribute [cbv_opaque] MvPolynomial.X

open MvPolynomial in
lemma test_case_11 :
    Bird.birdDetEntry (R := MvPolynomial (Fin 3) R)
      3
      symflat%
        #[1 , X 0, (X 0) ^ 2,
          1 , X 1, (X 1) ^ 2,
          1 , X 2, (X 2) ^ 2] = (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0) := by
  cbv_bird_entry_det

open Polynomial in
lemma test_case_12 :
    Bird.birdDetEntry (R := R[X])
      2
      symflat%
        #[X - 1 , X,
          X ^ 2 , 1] = - X ^ 3 + X - 1 := by
  cbv_bird_entry_det

lemma test_case_14 (a b c d : R) :
    Bird.birdDetEntry
      5
      (symflat% #[a,     b,     c,     d,     0,
                  0,     a,     b,     c,     d,
                  3 * a, 2 * b, c,     0,     0,
                  0,     3 * a, 2 * b, c,     0,
                  0,     0,     3 * a, 2 * b, c]) =
      -a * (18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3
      - 27 * a ^ 2 * d ^ 2) := by
  cbv_bird_entry_det

lemma test_case_18 {K : Type*} [Field K] (x i j k : K) (hx : x ≠ 0) :
    Bird.birdDetEntry
      3
      (symflat%
        #[x^3 , 0     , 0       ,
          i   , 1 / x , 0       ,
          j   , k     , 1 / x^2 ]) = 1 := by
  cbv_bird_entry_det
  field_simp [hx]

-- set_option Elab.async false in
-- #time lemma test_case_8 :
lemma test_case_8 :
    Bird.birdDetEntry (R := ℤ)
      8
      (#[ 2,  0, -1,  0,  0,  0,  0,  0,
          0,  2,  0, -1,  0,  0,  0,  0,
         -1,  0,  2, -1,  0,  0,  0,  0,
          0, -1, -1,  2, -1,  0,  0,  0,
          0,  0,  0, -1,  2, -1,  0,  0,
          0,  0,  0,  0, -1,  2, -1,  0,
          0,  0,  0,  0,  0, -1,  2, -1,
          0,  0,  0,  0,  0,  0, -1,  2]) = 1 := by
  cbv_bird_entry_det

-- set_option Elab.async false in
lemma sylvesterQuartic (a b c d e : R) :
  Bird.birdDetEntry
    7
    (symflat% #[a     , b     , c     , d     , e     , 0     , 0,
                0     , a     , b     , c     , d     , e     , 0,
                0     , 0     , a     , b     , c     , d     , e,
                4 * a , 3 * b , 2 * c , d     , 0     , 0     , 0,
                0     , 4 * a , 3 * b , 2 * c , d     , 0     , 0,
                0     , 0     , 4 * a , 3 * b , 2 * c , d     , 0,
                0     , 0     , 0     , 4 * a , 3 * b , 2 * c , d]) =
      a * (256 * a ^ 3 * e ^ 3 - 192 * a ^ 2 * b * d * e ^ 2
        - 128 * a ^ 2 * c ^ 2 * e ^ 2 + 144 * a ^ 2 * c * d ^ 2 * e
        - 27 * a ^ 2 * d ^ 4 + 144 * a * b ^ 2 * c * e ^ 2
        - 6 * a * b ^ 2 * d ^ 2 * e - 80 * a * b * c ^ 2 * d * e
        + 18 * a * b * c * d ^ 3 + 16 * a * c ^ 4 * e
        - 4 * a * c ^ 3 * d ^ 2 - 27 * b ^ 4 * e ^ 2
        + 18 * b ^ 3 * c * d * e - 4 * b ^ 3 * d ^ 3
        - 4 * b ^ 2 * c ^ 3 * e + b ^ 2 * c ^ 2 * d ^ 2) := by
  cbv_bird_entry_det

end Tests.BirdCbv
