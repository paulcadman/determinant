module

public import Determinant.Correctness.Spec
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.Perm.Fin

open scoped BigOperators

@[expose] public section

namespace Correctness

/-- A length-`m` word of row or column indices in `Fin n`.

This is Mathlib's list-backed vector. It is definitionally a `{l // l.length = m}` subtype and
has the finite instances needed for `Finset.univ`. -/
abbrev Word (n m : Nat) := List.Vector (Fin n) m

/-- The determinant of the submatrix selected by ordered row and column words. -/
def wordDet {R : Type*} [CommRing R] {n m : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (rows cols : Word n m) : R :=
  Matrix.det fun i j => A (rows.get i) (cols.get j)

/-- Empty word. -/
def vnil {n : Nat} : Word n 0 :=
  List.Vector.nil

/-- Prepend one index to a word. -/
def vcons {n p : Nat} (a : Fin n) (w : Word n p) : Word n (p + 1) :=
  List.Vector.ofFn (Fin.cases a fun q => w.get q)

/-- Singleton word. -/
def vsingle {n : Nat} (a : Fin n) : Word n 1 :=
  vcons a vnil

/-- Drop the first index of a nonempty word. -/
def vtail {n p : Nat} (w : Word n (p + 1)) : Word n p :=
  List.Vector.ofFn fun q => w.get q.succ

/-- Remove the index at a given position of a nonempty word. -/
def eraseIdx {n p : Nat} (w : Word n (p + 1)) (r : Fin (p + 1)) : Word n p :=
  List.Vector.ofFn fun q => w.get (r.succAbove q)

/-- The full ordered word `[0, 1, ..., n-1]`. -/
def fullWord (n : Nat) : Word n n :=
  List.Vector.ofFn id

theorem vcons_get_zero {n p : Nat} (a : Fin n) (w : Word n p) :
    (vcons a w).get (0 : Fin (p + 1)) = a := by
  rw [vcons, List.Vector.get_ofFn, Fin.cases_zero]

theorem vcons_get_succ {n p : Nat} (a : Fin n) (w : Word n p) (q : Fin p) :
    (vcons a w).get q.succ = w.get q := by
  rw [vcons, List.Vector.get_ofFn, Fin.cases_succ]

theorem vsingle_get {n : Nat} (a : Fin n) (q : Fin 1) :
    (vsingle a).get q = a := by
  fin_cases q
  exact vcons_get_zero a vnil

theorem vtail_get {n p : Nat} (w : Word n (p + 1)) (q : Fin p) :
    (vtail w).get q = w.get q.succ := by
  rw [vtail, List.Vector.get_ofFn]

theorem eraseIdx_get {n p : Nat} (w : Word n (p + 1)) (r : Fin (p + 1)) (q : Fin p) :
    (eraseIdx w r).get q = w.get (r.succAbove q) := by
  rw [eraseIdx, List.Vector.get_ofFn]

theorem vcons_head {n p : Nat} (a : Fin n) (w : Word n p) :
    List.Vector.head (vcons a w) = a := by
  change (vcons a w).get (0 : Fin (p + 1)) = a
  exact vcons_get_zero a w

theorem vcons_get_succ_succAbove {n p : Nat}
    (i : Fin n) (α : Word n (p + 1)) (k : Fin (p + 1)) (q : Fin (p + 1)) :
    (vcons i α).get (k.succ.succAbove q) = (vcons i (eraseIdx α k)).get q := by
  cases q using Fin.cases with
  | zero =>
      have h : k.succ.succAbove (0 : Fin (p + 1)) = (0 : Fin (p + 2)) := by simp
      rw [h]
      exact (vcons_get_zero i α).trans (vcons_get_zero i (eraseIdx α k)).symm
  | succ q =>
      rw [Fin.succ_succAbove_succ]
      simp [vcons_get_succ, eraseIdx_get]

theorem fullWord_get {n : Nat} (q : Fin n) :
    (fullWord n).get q = q := by
  rw [fullWord, List.Vector.get_ofFn]
  rfl

theorem wordDet_singleton {R : Type*} [CommRing R] {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    wordDet A (vsingle i) (vsingle j) = A i j := by
  simp [wordDet, vsingle_get]

theorem wordDet_duplicate_rows_eq_zero {R : Type*} [CommRing R] {n m : Nat}
    (A : Matrix (Fin n) (Fin n) R) (rows cols : Word n m)
    {a b : Fin m} (hab : a ≠ b) (h : rows.get a = rows.get b) :
    wordDet A rows cols = 0 := by
  unfold wordDet
  apply Matrix.det_zero_of_row_eq hab
  funext c
  simp [h]

theorem wordDet_duplicate_cols_eq_zero {R : Type*} [CommRing R] {n m : Nat}
    (A : Matrix (Fin n) (Fin n) R) (rows cols : Word n m)
    {a b : Fin m} (hab : a ≠ b) (h : cols.get a = cols.get b) :
    wordDet A rows cols = 0 := by
  unfold wordDet
  apply Matrix.det_zero_of_column_eq hab
  intro c
  simp [h]

theorem wordDet_full_eq_det {R : Type*} [CommRing R] {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) :
    wordDet A (fullWord n) (fullWord n) = A.det := by
  simp [wordDet, fullWord]

/-- First-column Laplace expansion for a word determinant, keeping Mathlib's explicit signs.

The follow-up `wordDet_cons_cons_expand` should rewrite the signed cofactors into Bird's
word-order form by moving `α[kpos]` to the front of the column word. -/
theorem wordDet_cons_cons_expand_signed
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n)
    (α : Word n (p + 1)) :
    wordDet A (vcons i α) (vcons j α)
      = A i j * wordDet A α α
        + ∑ kpos : Fin (p + 1),
            (-1 : R) ^ ((kpos : Nat) + 1) * A (α.get kpos) j *
              wordDet A (vcons i (eraseIdx α kpos)) α := by
  unfold wordDet
  rw [Matrix.det_succ_column_zero]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  · simp [Matrix.submatrix, vcons_head, vcons_get_succ]
    change A i j * Matrix.det (fun a b => A (α.get a) (α.get b)) =
      A i j * Matrix.det (fun a b => A (α.get a) (α.get b))
    rfl
  · apply Finset.sum_congr rfl
    intro k _hk
    simp [Matrix.submatrix, Nat.succ_eq_add_one, mul_assoc, vcons_head,
      vcons_get_succ, vcons_get_succ_succAbove]
    change (-1 : R) ^ ((k : Nat) + 1) *
        (A (α.get k) j * Matrix.det (fun a b => A ((vcons i (eraseIdx α k)).get a) (α.get b))) =
      (-1 : R) ^ ((k : Nat) + 1) *
        (A (α.get k) j * Matrix.det (fun a b => A ((vcons i (eraseIdx α k)).get a) (α.get b)))
    rfl

theorem vcons_eraseIdx_get_cycleRange {n p : Nat}
    (α : Word n (p + 1)) (k c : Fin (p + 1)) :
    (vcons (α.get k) (eraseIdx α k)).get (k.cycleRange c) = α.get c := by
  rw [vcons, List.Vector.get_ofFn]
  change (@Fin.cons p (fun _ => Fin n) (α.get k) (fun q : Fin p => (eraseIdx α k).get q)
      (k.cycleRange c)) = α.get c
  rw [Fin.cons_apply_cycleRange]
  rcases Fin.eq_self_or_eq_succAbove k c with rfl | ⟨q, rfl⟩
  · simp
  · simp [eraseIdx]

/-- Reindex columns by the cycle that moves column `k` to the front. -/
theorem wordDet_cycleRange_columns
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (rows : Word n (p + 1))
    (α : Word n (p + 1))
    (k : Fin (p + 1)) :
    wordDet A rows α =
      (-1 : R) ^ (k : Nat) * wordDet A rows (vcons (α.get k) (eraseIdx α k)) := by
  let B : Matrix (Fin (p + 1)) (Fin (p + 1)) R :=
    fun r c => A (rows.get r) ((vcons (α.get k) (eraseIdx α k)).get c)
  have hperm := Matrix.det_permute' (k.cycleRange) B
  calc
    wordDet A rows α = (B.submatrix id (k.cycleRange)).det := by
      unfold wordDet B
      simp [Matrix.submatrix, vcons_eraseIdx_get_cycleRange]
      change Matrix.det (fun i j => A (rows.get i) (α.get j)) =
        Matrix.det (fun i j => A (rows.get i) (α.get j))
      rfl
    _ = ((Equiv.Perm.sign k.cycleRange : ℤˣ) : R) * B.det := hperm
    _ = (-1 : R) ^ (k : Nat) * wordDet A rows (vcons (α.get k) (eraseIdx α k)) := by
      simp [Fin.sign_cycleRange, B, wordDet]

lemma neg_one_pow_mul_self {R : Type*} [CommRing R] (k : Nat) :
    (-1 : R)^k * (-1 : R)^k = 1 := by
  rw [← pow_add, ← two_mul k, pow_mul]
  simp

lemma neg_one_pow_succ_mul_self {R : Type*} [CommRing R] (k : Nat) :
    (-1 : R)^(k + 1) * (-1 : R)^k = -1 := by
  rw [pow_succ, mul_assoc, mul_comm (-1 : R) ((-1 : R)^k), ← mul_assoc,
    neg_one_pow_mul_self]
  simp

/-- First-column Laplace expansion in Bird's ordered-word form. -/
theorem wordDet_cons_cons_expand
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n)
    (α : Word n (p + 1))
    (_hα : StrictMono (fun t : Fin (p + 1) => α.get t)) :
    wordDet A (vcons i α) (vcons j α)
      = A i j * wordDet A α α
        - ∑ kpos : Fin (p + 1),
          A (α.get kpos) j *
            wordDet A
              (vcons i (eraseIdx α kpos))
              (vcons (α.get kpos) (eraseIdx α kpos)) := by
  rw [wordDet_cons_cons_expand_signed]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  rw [wordDet_cycleRange_columns A (vcons i (eraseIdx α k)) α k]
  calc
    (-1 : R) ^ ((k : Nat) + 1) * A (α.get k) j *
        ((-1 : R) ^ (k : Nat) *
          wordDet A (vcons i (eraseIdx α k)) (vcons (α.get k) (eraseIdx α k)))
        = ((-1 : R) ^ ((k : Nat) + 1) * (-1 : R) ^ (k : Nat)) *
            (A (α.get k) j *
              wordDet A (vcons i (eraseIdx α k)) (vcons (α.get k) (eraseIdx α k))) := by
          ac_rfl
    _ = -1 * (A (α.get k) j *
              wordDet A (vcons i (eraseIdx α k)) (vcons (α.get k) (eraseIdx α k))) := by
          rw [neg_one_pow_succ_mul_self]
    _ = -(A (α.get k) j *
              wordDet A (vcons i (eraseIdx α k)) (vcons (α.get k) (eraseIdx α k))) := by
          simp

end Correctness
