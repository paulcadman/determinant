module

public import Determinant.CertChain.Bird
public import Determinant.Correctness.FlatMatrix
public import Determinant.Correctness.Theorem
import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace BirdDet

variable
  {R : Type*}
  [CommRing R]

theorem get_eq_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n)
    (i j : Fin n) :
    get n A i.val j.val = ofFlatArray A hA i j := by
  unfold get ofFlatArray flatIdx
  rw [getD_eq_get_of_lt]

theorem sumFrom_eq_sum_Ico (n lo : Nat) (f : Nat → R) :
    sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  rw [sumFrom]
  split_ifs with h
  · rw [sumFrom_eq_sum_Ico n (lo + 1) f]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Finset.sum_Ico_eq_sum_range]
    have hdiff : n - lo = (n - (lo + 1)) + 1 := by omega
    rw [hdiff, Finset.sum_range_succ']
    rw [add_comm]
    apply congrArg₂ HAdd.hAdd
    · apply Finset.sum_congr rfl
      intro k _hk
      congr 1
      omega
    · simp
  · rw [Finset.Ico_eq_empty_iff.mpr h]
    simp
termination_by n - lo

theorem sumFrom_fin_tail (n : Nat) (i : Fin n) (f : Nat → R) :
    sumFrom n (i.val + 1) f = ∑ k : Fin n, if i < k then f k.val else 0 := by
  rw [sumFrom_eq_sum_Ico]
  calc
    (∑ k ∈ Finset.Ico (i.val + 1) n, f k)
        = ∑ x ∈ Finset.range n,
            if h : x < n then if i < (⟨x, h⟩ : Fin n) then f x else 0 else 0 := by
          symm
          calc
            (∑ x ∈ Finset.range n,
                if h : x < n then if i < (⟨x, h⟩ : Fin n) then f x else 0 else 0)
                = ∑ x ∈ Finset.range n, if i.val < x then f x else 0 := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  have hxlt : x < n := Finset.mem_range.mp hx
                  simp [hxlt, Fin.lt_def]
            _ = ∑ x ∈ (Finset.range n).filter (fun x => i.val < x), f x := by
                  rw [Finset.sum_filter]
            _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by
                  apply Finset.sum_congr
                  · ext x
                    simp [Finset.mem_filter, and_comm]
                  · intro x _hx
                    rfl
    _ = ∑ k : Fin n, if i < k then f k.val else 0 := by
          simpa using (Fin.sum_univ_eq_sum_range
            (fun x : Nat =>
              if h : x < n then if i < (⟨x, h⟩ : Fin n) then f x else 0 else 0) n).symm

theorem iter_eq_correctness
    (n : Nat) (A : Array R) (hA : A.size = n * n)
    (t : Nat) (F : Nat → Nat → R)
    (F' : Fin n → Fin n → R)
    (hF : ∀ i j : Fin n, F i.val j.val = F' i j)
    (i j : Fin n) :
    iter n A t F i.val j.val = Correctness.iterEntry (ofFlatArray A hA) t F' i j := by
  induction t generalizing F F' i j with
  | zero =>
      simp [iter, Correctness.iterEntry, hF]
  | succ t ih =>
      rw [iter_succ, Correctness.iterEntry_succ]
      simp only [Correctness.stepEntry]
      rw [sumFrom_fin_tail n i (fun k => iter n A t F k k)]
      rw [sumFrom_fin_tail n i (fun k => iter n A t F i.val k * get n A k j.val)]
      have hdiag :
          (∑ k : Fin n, if i < k then iter n A t F k.val k.val else 0) =
            ∑ k : Fin n, if i < k then Correctness.iterEntry (ofFlatArray A hA) t F' k k else 0 := by
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hik : i < k <;> simp [hik, ih F F' hF k k]
      have hoff :
          (∑ k : Fin n, if i < k then iter n A t F i.val k.val * get n A k.val j.val else 0) =
            ∑ k : Fin n,
              if i < k then
                Correctness.iterEntry (ofFlatArray A hA) t F' i k * ofFlatArray A hA k j
              else 0 := by
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hik : i < k <;> simp [hik, ih F F' hF i k, get_eq_ofFlatArray A hA k j]
      rw [hdiag, hoff]
      rw [get_eq_ofFlatArray A hA i j]

theorem birdDet_eq_birdDetSpec_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    birdDet n A = Correctness.birdDetSpec (ofFlatArray A hA) := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      simp [birdDet, Correctness.birdDetSpec]
      exact congrArg ((-1 : R) ^ k * ·)
        (iter_eq_correctness (k + 1) A hA k (get (k + 1) A)
          (fun i j => ofFlatArray A hA i j)
          (by intro i j; exact get_eq_ofFlatArray A hA i j) 0 0)

theorem det_ofFlatArray_eq_birdDet
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    Matrix.det (ofFlatArray A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec_ofFlatArray A hA]
  exact (Correctness.birdDetSpec_eq_det (ofFlatArray A hA)).symm

theorem birdDet_eq_det_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    birdDet n A = Matrix.det (ofFlatArray A hA) :=
  (det_ofFlatArray_eq_birdDet A hA).symm

end BirdDet

end
