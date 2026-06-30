module

public import Determinant.CertChain.Tactic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Field
import Qq

namespace Tests.Tactic

open Lean Meta Qq
open BirdDet

variable
  {R : Type*}
  [CommRing R]

-- Normalizer: direct `BirdDet.birdDet`.
run_meta do
  let e : Q(ℤ) := q(BirdDet.birdDet 2 #[1, 2, 3, 4])
  discard <| normalizeBirdDet e

-- Normalizer: checked flat-array `Matrix.det`.
run_meta do
  let e : Q(ℤ) :=
    q(Matrix.det (Matrix.ofFlatArray (m := 2) (n := 2) #[(1 : ℤ), 2, 3, 4] rfl))
  let some _ ← normalizeDetOfFlatArray? e | throwError "expected checked flat-array determinant source"

-- Unsupported arbitrary `Matrix.det` expressions are ignored by the simproc dispatcher.
run_meta do
  let M : Q(Matrix (Fin 2) (Fin 2) ℤ) := q(fun _ _ => (0 : ℤ))
  let e : Q(ℤ) := q(Matrix.det $M)
  match ← normalizeDetOfFlatArray? e with
  | none => pure ()
  | some _ => throwError "unexpected determinant source"

example : birdDet 0 (#[] : Array ℤ) = 1 := by
  eval_det

example : birdDet 1 #[5] = (5 : ℤ) := by
  eval_det

example : birdDet 2 #[1, 2, 3, 4] = (-2 : ℤ) := by
  eval_det

example :
    Matrix.det (Matrix.ofFlatArray (m := 2) (n := 2) #[(1 : ℤ), 2, 3, 4] rfl) =
      (-2 : ℤ) := by
  eval_det

example :
    (Matrix.ofFlatArray (m := 2) (n := 2) #[(1 : ℤ), 2, 3, 4] rfl).det =
      (-2 : ℤ) := by
  eval_det

example (A : Array R) (hA : A.size = 2 * 2) :
    Matrix.det (Matrix.ofFlatArray (m := 2) (n := 2) A hA) =
      Matrix.det (Matrix.ofFlatArray (m := 2) (n := 2) A hA) := by
  rfl

/--
Application type mismatch
-/
#guard_msgs (substring := true) in
#check Matrix.ofFlatArray (m := 2) (n := 2) #[(1 : ℤ), 2, 3] rfl

example : birdDet 2 #[1, 2, 2, 4] = (0 : ℤ) := by
  simp only [norm_det]

/-- error: `simp` made no progress -/
#guard_msgs in
example : birdDet 2 #[1, 2, 2, 4] = (0 : ℤ) := by
  simp

example : birdDet 2 #[1, 2, 2, 4] + birdDet 2 #[2, 3, 4, 5] = -2 := by
  simp only [norm_det]
  norm_num

example : birdDet 2 #[birdDet 2 #[2, 3, 4, 5], 2, 2, 4] = -12 := by
  simp only [norm_det]

example (a b c d : R) : birdDet 2 #[a, b, c, d] = a * d - b * c := by
  simp only [norm_det]
  ring

example (a b c d : R) :
    Matrix.det (Matrix.ofFlatArray (m := 2) (n := 2) #[a, b, c, d] rfl) =
      a * d - b * c := by
  eval_det
  ring

open Polynomial in
example :
    Matrix.det
      (Matrix.ofFlatArray (m := 2) (n := 2)
        #[((X : ℤ[X]) - 1), X,
          X ^ 2,             1] rfl) =
      -X ^ 3 + X - 1 := by
  eval_det
  ring

example : (birdDet 2 #[1, 2, 3, 4] : ℤ) + 3 = 1 := by
  eval_det
  norm_num

lemma test_case_8 :
  birdDet 8
    #[ 2,  0, -1,  0,  0,  0,  0,  0,
       0,  2,  0, -1,  0,  0,  0,  0,
      -1,  0,  2, -1,  0,  0,  0,  0,
       0, -1, -1,  2, -1,  0,  0,  0,
       0,  0,  0, -1,  2, -1,  0,  0,
       0,  0,  0,  0, -1,  2, -1,  0,
       0,  0,  0,  0,  0, -1,  2, -1,
       0,  0,  0,  0,  0,  0, -1,  2] = 1 := by
  simp only [norm_det]

lemma test_case_8_det :
  -- These tests use the checked flat-array constructor to avoid Mathlib's
  -- vector-based matrix notation elaboration while still proving a theorem about
  -- `Matrix.det`.
  Matrix.det (Matrix.ofFlatArray (m := 8) (n := 8)
    #[ 2,  0, -1,  0,  0,  0,  0,  0,
       0,  2,  0, -1,  0,  0,  0,  0,
      -1,  0,  2, -1,  0,  0,  0,  0,
       0, -1, -1,  2, -1,  0,  0,  0,
       0,  0,  0, -1,  2, -1,  0,  0,
       0,  0,  0,  0, -1,  2, -1,  0,
       0,  0,  0,  0,  0, -1,  2, -1,
       0,  0,  0,  0,  0,  0, -1,  2] rfl) = 1 := by
  eval_det

open MvPolynomial in
lemma test_case_11 :
    birdDet (R := MvPolynomial (Fin 3) R)
      3
      #[1 , X 0, (X 0) ^ 2,
        1 , X 1, (X 1) ^ 2,
        1 , X 2, (X 2) ^ 2] = (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 0) := by
  simp only [norm_det]
  ring

lemma sylvesterQuartic (a b c d e : R) :
  birdDet 7
    #[a     , b     , c     , d     , e     , 0     , 0,
      0     , a     , b     , c     , d     , e     , 0,
      0     , 0     , a     , b     , c     , d     , e,
      4 * a , 3 * b , 2 * c , d     , 0     , 0     , 0,
      0     , 4 * a , 3 * b , 2 * c , d     , 0     , 0,
      0     , 0     , 4 * a , 3 * b , 2 * c , d     , 0,
      0     , 0     , 0     , 4 * a , 3 * b , 2 * c , d] =
      a * (256 * a ^ 3 * e ^ 3 - 192 * a ^ 2 * b * d * e ^ 2
        - 128 * a ^ 2 * c ^ 2 * e ^ 2 + 144 * a ^ 2 * c * d ^ 2 * e
        - 27 * a ^ 2 * d ^ 4 + 144 * a * b ^ 2 * c * e ^ 2
        - 6 * a * b ^ 2 * d ^ 2 * e - 80 * a * b * c ^ 2 * d * e
        + 18 * a * b * c * d ^ 3 + 16 * a * c ^ 4 * e
        - 4 * a * c ^ 3 * d ^ 2 - 27 * b ^ 4 * e ^ 2
        + 18 * b ^ 3 * c * d * e - 4 * b ^ 3 * d ^ 3
        - 4 * b ^ 2 * c ^ 3 * e + b ^ 2 * c ^ 2 * d ^ 2) := by
  simp [norm_det]
  ring1

lemma test_case_18 {K : Type*} [Field K] (x i j k : K) (hx : x ≠ 0) :
  birdDet 3
    #[x^3 , 0     , 0       ,
      i   , 1 / x , 0       ,
      j   , k     , 1 / x^2 ] = 1 := by
  simp only [norm_det]
  field_simp [hx]

example (a b c : R) :
  birdDet 10
    #[a , b , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 ,
      c , a , b , 0 , 0 , 0 , 0 , 0 , 0 , 0 ,
      0 , c , a , b , 0 , 0 , 0 , 0 , 0 , 0 ,
      0 , 0 , c , a , b , 0 , 0 , 0 , 0 , 0 ,
      0 , 0 , 0 , c , a , b , 0 , 0 , 0 , 0 ,
      0 , 0 , 0 , 0 , c , a , b , 0 , 0 , 0 ,
      0 , 0 , 0 , 0 , 0 , c , a , b , 0 , 0 ,
      0 , 0 , 0 , 0 , 0 , 0 , c , a , b , 0 ,
      0 , 0 , 0 , 0 , 0 , 0 , 0 , c , a , b ,
      0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , c , a] =
    a ^ 10 - 9 * a ^ 8 * b * c + 28 * a ^ 6 * b ^ 2 * c ^ 2
      - 35 * a ^ 4 * b ^ 3 * c ^ 3 + 15 * a ^ 2 * b ^ 4 * c ^ 4
      - b ^ 5 * c ^ 5 := by
  simp only [norm_det]
  ring

example :
  birdDet 14
    #[ 3,  1, -3,  0,  2,  1, -1,  3,  1,  0,  2, -2, -3, -1,
       1, -3, -1,  2, -1,  1, -2, -3,  3,  1, -2, -3,  1,  1,
      -2,  0,  2, -3, -2,  0, -2, -2, -3,  1, -2,  1, -2,  0,
      -2,  2,  0, -2,  2, -3,  3, -2,  1,  2, -2, -2, -2, -2,
       1,  0,  2,  2, -1, -3,  2,  2, -3,  1, -1, -3,  3,  1,
       2, -3,  1,  1, -3,  1,  0,  0,  2, -1,  0,  3, -1, -2,
       1,  0,  1,  0,  2, -3,  2, -2, -2, -1,  3,  2,  0, -2,
      -3, -2, -1, -2,  1, -1,  0, -3, -2, -3,  1,  3, -1,  3,
       1, -2,  3,  1, -3, -3,  1,  3,  2,  3, -1,  1,  3,  0,
      -2,  2, -3,  1,  0,  2,  2,  1, -1,  1, -2, -3,  2,  2,
       2,  0, -2, -2,  2,  1,  1,  3,  1, -2,  1,  2,  2,  2,
      -3, -3, -3,  2,  2,  0, -1, -3,  1, -2, -3, -1,  3,  2,
      -2,  3,  1,  3,  1,  3,  2, -3,  0,  2,  3, -2, -2,  1,
      -3,  3, -1, -2,  1, -2,  2,  1, -3, -2,  0,  2,  0,  2] = -1257984188 := by
  eval_det

end Tests.Tactic
