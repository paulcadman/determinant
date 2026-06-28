module

public import Determinant.CertChain.Bird
public import Determinant.Correctness.FlatMatrix
public import Determinant.Correctness.Spec
import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace BirdDet

/-!
This file connects the flat-array Bird implementation used by the tactic to the
proof-friendly `Correctness.birdDetSpec`.

The main adapter theorem is:

* `birdDet_eq_birdDetSpec_ofFlatArray`

`Theorem.lean` combines this with `Correctness.birdDetSpec_eq_det` to connect
the flat-array Bird implementation to `Matrix.det`.
-/

variable
  {R : Type*}
  [CommRing R]

theorem get_eq_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n)
    (i j : Fin n) :
    get n A i.val j.val = ofFlatArray (m := n) (n := n) A hA i j := by
  have hidx : n * i.val + j.val < A.size := by
    simpa [hA] using (Fin.mkDivMod i j).isLt
  unfold get ofFlatArray
  simp [Array.getD, hidx, Nat.mul_comm]

theorem sumFrom_eq_sum_Ico (n lo : Nat) (f : Nat → R) :
    sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
      rw [sumFrom]
      split_ifs with h
      · rw [sumFrom_eq_sum_Ico n (lo + 1) f]
        simp [Finset.sum_eq_sum_Ico_succ_bot h f]
      · simp [Finset.Ico_eq_empty h]

/-- Rewrite the Nat interval tail after `i` as a conditional sum over `Fin n`. -/
theorem sum_Ico_succ_eq_sum_fin_tail (n : Nat) (i : Fin n) (f : Nat → R) :
    (∑ k ∈ Finset.Ico (i.val + 1) n, f k) =
      ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if i.val < x then f x else 0) n]
  rw [← Finset.sum_filter]
  rw [show (Finset.range n).filter (fun x => i.val < x) = Finset.Ico (i.val + 1) n by
    ext x
    simp [Finset.mem_Ico, and_comm]]

theorem sumFrom_fin_tail (n : Nat) (i : Fin n) (f : Nat → R) :
    sumFrom n (i.val + 1) f =
      ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by
  rw [sumFrom_eq_sum_Ico]
  exact sum_Ico_succ_eq_sum_fin_tail n i f

theorem iter_eq_correctness
    (n : Nat) (A : Array R) (hA : A.size = n * n)
    (t : Nat) (F : Nat → Nat → R)
    (F' : Fin n → Fin n → R)
    (hF : ∀ i j : Fin n, F i.val j.val = F' i j)
    (i j : Fin n) :
    iter n A t F i.val j.val =
      Correctness.iterEntry (ofFlatArray (m := n) (n := n) A hA) t F' i j := by
  induction t generalizing F F' i j with
  | zero =>
      simp [iter, Correctness.iterEntry, hF]
  | succ t ih =>
      rw [iter_succ, Correctness.iterEntry_succ]
      simp only [Correctness.stepEntry]
      rw [sumFrom_fin_tail n i (fun k => iter n A t F k k)]
      rw [sumFrom_fin_tail n i (fun k => iter n A t F i.val k * get n A k j.val)]
      have hdiag :
          (∑ k : Fin n, if i.val < k.val then iter n A t F k.val k.val else 0) =
            ∑ k : Fin n,
              if i.val < k.val then
                Correctness.iterEntry (ofFlatArray (m := n) (n := n) A hA) t F' k k
              else 0 := by
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hik : i.val < k.val <;> simp [hik, ih F F' hF k k]
      have hoff :
          (∑ k : Fin n,
              if i.val < k.val then iter n A t F i.val k.val * get n A k.val j.val else 0) =
            ∑ k : Fin n,
              if i.val < k.val then
                Correctness.iterEntry (ofFlatArray (m := n) (n := n) A hA) t F' i k *
                  ofFlatArray (m := n) (n := n) A hA k j
              else 0 := by
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hik : i.val < k.val <;> simp [hik, ih F F' hF i k, get_eq_ofFlatArray A hA k j]
      rw [hdiag, hoff]
      rw [get_eq_ofFlatArray A hA i j]
      rfl

-- used
theorem birdDet_eq_birdDetSpec_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    birdDet n A = Correctness.birdDetSpec (ofFlatArray (m := n) (n := n) A hA) := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      simp [birdDet, Correctness.birdDetSpec]
      exact congrArg ((-1 : R) ^ k * ·)
        (iter_eq_correctness (k + 1) A hA k (get (k + 1) A)
          (fun i j => ofFlatArray (m := k + 1) (n := k + 1) A hA i j)
          (by intro i j; exact get_eq_ofFlatArray A hA i j) 0 0)

end BirdDet

end
