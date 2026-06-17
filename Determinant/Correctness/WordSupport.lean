module

public import Determinant.Correctness.WordDet

@[expose] public section

namespace Correctness

/-- The finite set of values appearing in a word. -/
def wordSupport {n p : Nat} (α : Word n p) : Finset (Fin n) :=
  Finset.univ.image fun q : Fin p => α.get q

theorem mem_wordSupport {n p : Nat} {α : Word n p} {k : Fin n} :
    k ∈ wordSupport α ↔ ∃ q : Fin p, α.get q = k := by
  simp [wordSupport]

theorem wordSupport_vcons {n p : Nat} (k : Fin n) (α : Word n p) :
    wordSupport (vcons k α) = insert k (wordSupport α) := by
  ext x
  rw [mem_wordSupport]
  simp only [Finset.mem_insert, mem_wordSupport]
  constructor
  · rintro ⟨q, hq⟩
    cases q using Fin.cases with
    | zero => left; simpa [vcons_get_zero, vcons_head] using hq.symm
    | succ q => right; exact ⟨q, by simpa [vcons_get_succ] using hq⟩
  · rintro (rfl | ⟨q, hq⟩)
    · exact ⟨0, by simp [vcons_head]⟩
    · exact ⟨q.succ, by simp [vcons_get_succ, hq]⟩

theorem wordSupport_eraseIdx_subset
    {n p : Nat} (β : Word n (p + 1)) (r : Fin (p + 1)) :
    wordSupport (eraseIdx β r) ⊆ wordSupport β := by
  intro k hk
  rw [mem_wordSupport] at hk ⊢
  rcases hk with ⟨q, hq⟩
  exact ⟨r.succAbove q, by simpa [eraseIdx_get] using hq⟩

theorem wordSupport_eq_insert_eraseIdx {n p : Nat}
    (β : Word n (p + 1)) (r : Fin (p + 1)) :
    wordSupport β = insert (β.get r) (wordSupport (eraseIdx β r)) := by
  ext x
  constructor
  · intro hx
    rw [mem_wordSupport] at hx
    rw [Finset.mem_insert]
    rcases hx with ⟨q, hq⟩
    by_cases hqr : q = r
    · left
      rw [← hq, hqr]
    · right
      rcases Fin.exists_succAbove_eq hqr with ⟨t, ht⟩
      rw [mem_wordSupport]
      exact ⟨t, by rw [eraseIdx_get, ht, hq]⟩
  · intro hx
    rw [Finset.mem_insert] at hx
    rcases hx with hx | hx
    · rw [mem_wordSupport]
      exact ⟨r, hx.symm⟩
    · exact wordSupport_eraseIdx_subset β r hx

theorem wordSupport_card_eq_of_strictMono {n p : Nat} {α : Word n p}
    (hα : StrictMono fun q : Fin p => α.get q) :
    (wordSupport α).card = p := by
  unfold wordSupport
  rw [Finset.card_image_of_injective]
  · simp
  · exact hα.injective

theorem get_not_mem_eraseIdx
    {n p : Nat}
    (β : Word n (p + 1))
    (r : Fin (p + 1))
    (hβ : StrictMono fun t : Fin (p + 1) => β.get t) :
    β.get r ∉ wordSupport (eraseIdx β r) := by
  intro hmem
  rw [mem_wordSupport] at hmem
  rcases hmem with ⟨q, hq⟩
  have heq : β.get (r.succAbove q) = β.get r := by simpa [eraseIdx_get] using hq
  have hidx : r.succAbove q = r := hβ.injective heq
  exact (Fin.succAbove_ne r q) hidx

theorem wordDet_vcons_duplicate_col_eq_zero
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i k : Fin n)
    (α : Word n p)
    (hmem : k ∈ wordSupport α) :
    wordDet A (vcons i α) (vcons k α) = 0 := by
  rcases (mem_wordSupport.mp hmem) with ⟨q, hq⟩
  apply wordDet_duplicate_cols_eq_zero
    (A := A)
    (rows := vcons i α)
    (cols := vcons k α)
    (a := 0)
    (b := q.succ)
  · exact (Fin.succ_ne_zero q).symm
  · rw [vcons_get_zero, vcons_get_succ]
    exact hq.symm

end Correctness
