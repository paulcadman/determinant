module

public import Determinant.CertChain.Bird
public import Determinant.Correctness.FlatMatrix
public import Determinant.Correctness.Spec
import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

/-!
This file contains representation-changing lemmas between the flat-array,
Nat-indexed implementation in `BirdDet` and the Fin-indexed proof
specification in `Correctness`.

The bridge has four parts:

1. `get_eq_ofFlatArray_square` translates flat-array lookup.
2. `sumFrom_fin_tail` translates Nat tail sums to Fin conditional sums.
3. `iter_eq_iterEntry_ofFlatArray` translates the recurrence.
4. `birdDet_eq_birdDetSpec_ofFlatArray` translates the determinant.
-/

namespace BirdDet

variable {R : Type*}

/-- View a Nat-indexed matrix-like function as a Fin-indexed one. -/
def finView {n : Nat} (F : Nat → Nat → R) :
    Fin n → Fin n → R :=
  fun i j => F i.val j.val

@[simp]
theorem finView_apply
    {n : Nat} (F : Nat → Nat → R) (i j : Fin n) :
    finView F i j = F i.val j.val := rfl

variable [CommRing R]

/--
Translate flat-array lookup through the checked rectangular constructor.

This is the only place where the defaulting behavior of `BirdDet.get` is
reconciled with checked array access.
-/
theorem get_eq_ofFlatArray
    {rows cols : Nat}
    (A : Array R)
    (hA : A.size = rows * cols)
    (i : Fin rows) (j : Fin cols) :
    get cols A i.val j.val = Matrix.ofFlatArray (m := rows) (n := cols) A hA i j := by
  have hidx : cols * i.val + j.val < A.size := by
    rw [hA]
    exact (Fin.mkDivMod i j).isLt
  unfold get Matrix.ofFlatArray
  simp [Array.getD, hidx]

/-- Square specialization of `get_eq_ofFlatArray`, used by the determinant bridge. -/
theorem get_eq_ofFlatArray_square
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n)
    (i j : Fin n) :
    get n A i.val j.val = Matrix.ofFlatArray (m := n) (n := n) A hA i j := by
  exact get_eq_ofFlatArray (rows := n) (cols := n) A hA i j

theorem sumFrom_eq_sum_Ico (n lo : Nat) (f : Nat → R) :
    sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
      rw [sumFrom]
      split_ifs with h
      · rw [sumFrom_eq_sum_Ico n (lo + 1) f]
        simp [Finset.sum_eq_sum_Ico_succ_bot h f]
      · simp [Finset.Ico_eq_empty h]

theorem sum_Ico_succ_eq_sum_fin_tail_val (n : Nat) (i : Fin n) (f : Nat → R) :
    (∑ k ∈ Finset.Ico (i.val + 1) n, f k) =
      ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if i.val < x then f x else 0) n]
  rw [← Finset.sum_filter]
  rw [show (Finset.range n).filter (fun x => i.val < x) = Finset.Ico (i.val + 1) n by
    ext x
    simp [Finset.mem_Ico, and_comm]]

/--
Translate the Nat tail `k = i + 1, ..., n - 1` into the Fin-indexed conditional
sum used by `Correctness.stepEntry`.
-/
theorem sumFrom_fin_tail (n : Nat) (i : Fin n) (f : Nat → R) :
    sumFrom n (i.val + 1) f =
      ∑ k : Fin n, if i < k then f k.val else 0 := by
  rw [sumFrom_eq_sum_Ico]
  trans ∑ k : Fin n, if i.val < k.val then f k.val else 0
  · exact sum_Ico_succ_eq_sum_fin_tail_val n i f
  · apply Finset.sum_congr rfl
    intro k _hk
    by_cases h : i < k
    · have hv : i.val < k.val := by
        change i.val < k.val at h
        exact h
      simp [h, hv]
    · have hv : ¬ i.val < k.val := by
        change ¬ i.val < k.val at h
        exact h
      simp [h, hv]

/--
Translate one Nat-indexed Bird step into the Fin-indexed `Correctness.stepEntry`
formula for the checked flat-array matrix.
-/
theorem step_formula_bridge_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n)
    (F : Nat → Nat → R)
    (i j : Fin n) :
    (-(sumFrom n (i.val + 1) fun k => F k k) *
        get n A i.val j.val
      +
      sumFrom n (i.val + 1) fun k =>
        F i.val k * get n A k j.val)
      =
    Correctness.stepEntry
      (Matrix.ofFlatArray (m := n) (n := n) A hA)
      (finView F)
      i j := by
  rw [sumFrom_fin_tail n i (fun k => F k k)]
  rw [sumFrom_fin_tail n i (fun k => F i.val k * get n A k j.val)]
  simp [Correctness.stepEntry, get_eq_ofFlatArray_square A hA]

/--
Main representation bridge: Nat-indexed iteration agrees with Fin-indexed
iteration when the initial Nat-indexed function is viewed through `finView`.
-/
theorem iter_eq_iterEntry_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n)
    (t : Nat)
    (F : Nat → Nat → R)
    (i j : Fin n) :
    iter n A t F i.val j.val =
      Correctness.iterEntry
        (Matrix.ofFlatArray (m := n) (n := n) A hA)
        t
        (finView F)
        i j := by
  induction t generalizing F i j with
  | zero =>
      simp [iter, Correctness.iterEntry, finView]
  | succ t ih =>
      rw [iter_succ, Correctness.iterEntry_succ]
      rw [step_formula_bridge_ofFlatArray A hA (iter n A t F) i j]
      congr
      funext p q
      exact ih F p q

/-- The initial Fin-indexed view of `BirdDet.get` is the checked matrix entry function. -/
theorem finView_get_eq_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    finView (n := n) (get n A) =
      fun i j => Matrix.ofFlatArray (m := n) (n := n) A hA i j := by
  funext i j
  exact get_eq_ofFlatArray_square A hA i j

/--
Translate the flat-array Bird determinant to the proof specification for the
checked flat-array matrix.
-/
theorem birdDet_eq_birdDetSpec_ofFlatArray
    {n : Nat}
    (A : Array R)
    (hA : A.size = n * n) :
    birdDet n A = Correctness.birdDetSpec (Matrix.ofFlatArray (m := n) (n := n) A hA) := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      simp [birdDet, Correctness.birdDetSpec]
      let z : Fin (k + 1) := 0
      have hIter :=
        iter_eq_iterEntry_ofFlatArray A hA k (get (k + 1) A) z z
      rw [finView_get_eq_ofFlatArray A hA] at hIter
      exact congrArg ((-1 : R) ^ k * ·) hIter

end BirdDet

end
