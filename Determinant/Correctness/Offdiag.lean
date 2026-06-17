module

public import Determinant.Correctness.WordSupport
public import Determinant.Correctness.TailWords

open scoped BigOperators

@[expose] public section

namespace Correctness

/-- Bird off-diagonal update domain before removing duplicate column terms. -/
def OffdiagAllDomain {n p : Nat} (i : Fin n) :
    Finset (Σ _ : Word n p, Fin n) :=
  (TailWords i p).sigma fun _α =>
    Finset.univ.filter fun k => i < k

/-- Bird off-diagonal update domain without duplicate column terms. -/
def OffdiagDomain {n p : Nat} (i : Fin n) :
    Finset (Σ _ : Word n p, Fin n) :=
  (TailWords i p).sigma fun α =>
    Finset.univ.filter fun k => i < k ∧ k ∉ wordSupport α

/-- Laplace cofactor domain for words in `TailWords i (p+1)` and a removed position. -/
def CofactorDomain {n p : Nat} (i : Fin n) :
    Finset (Σ _ : Word n (p + 1), Fin (p + 1)) :=
  (TailWords i (p + 1)).sigma fun _β => Finset.univ

theorem mem_OffdiagAllDomain {n p : Nat} {i : Fin n}
    {x : Σ _ : Word n p, Fin n} :
    x ∈ OffdiagAllDomain i ↔
      x.1 ∈ TailWords i p ∧ i < x.2 := by
  cases x
  simp [OffdiagAllDomain]

theorem mem_OffdiagDomain {n p : Nat} {i : Fin n} {x : Σ _ : Word n p, Fin n} :
    x ∈ OffdiagDomain i ↔
      x.1 ∈ TailWords i p ∧ i < x.2 ∧ x.2 ∉ wordSupport x.1 := by
  cases x
  simp [OffdiagDomain]

theorem OffdiagDomain_eq_filter_OffdiagAllDomain {n p : Nat} (i : Fin n) :
    OffdiagDomain (i := i) (p := p) =
      (OffdiagAllDomain (i := i) (p := p)).filter
        (fun x => x.2 ∉ wordSupport x.1) := by
  ext x
  simp [mem_OffdiagDomain, mem_OffdiagAllDomain, and_assoc]

theorem mem_CofactorDomain {n p : Nat} {i : Fin n}
    {x : Σ _ : Word n (p + 1), Fin (p + 1)} :
    x ∈ CofactorDomain i ↔ x.1 ∈ TailWords i (p + 1) := by
  cases x
  simp [CofactorDomain]

theorem eraseIdx_mem_TailWords {n p : Nat} {i : Fin n}
    {β : Word n (p + 1)} (r : Fin (p + 1))
    (hβ : β ∈ TailWords i (p + 1)) :
    eraseIdx β r ∈ TailWords i p := by
  rw [mem_TailWords] at hβ ⊢
  refine ⟨?_, ?_⟩
  · intro a b hab
    simpa [eraseIdx_get] using hβ.1 (Fin.strictMono_succAbove r hab)
  · intro t
    simpa [eraseIdx_get] using hβ.2 (r.succAbove t)

/-- Map a Laplace cofactor term to the corresponding non-duplicate Bird update term. -/
def cofactorToOffdiag {n p : Nat}
    (x : Σ _ : Word n (p + 1), Fin (p + 1)) :
    Σ _ : Word n p, Fin n :=
  ⟨eraseIdx x.1 x.2, x.1.get x.2⟩

theorem cofactorToOffdiag_mem
    {n p : Nat} {i : Fin n}
    {x : Σ _ : Word n (p + 1), Fin (p + 1)}
    (hx : x ∈ CofactorDomain i) :
    cofactorToOffdiag x ∈ OffdiagDomain i := by
  cases x with
  | mk β r =>
    rw [mem_CofactorDomain] at hx
    rw [mem_OffdiagDomain]
    refine ⟨eraseIdx_mem_TailWords r hx, ?_, ?_⟩
    · exact (mem_TailWords.mp hx).2 r
    · exact get_not_mem_eraseIdx β r (mem_TailWords.mp hx).1

/-- Insert a missing value into an increasing tail word, then erase it again.

This is stated as existence rather than a concrete `sortedInsert` definition. The witness word is
the increasing enumeration of `insert k (wordSupport α)`. -/
theorem exists_insert_eraseIdx
    {n p : Nat} {i k : Fin n} {α : Word n p}
    (hα : α ∈ TailWords i p)
    (hik : i < k)
    (hnot : k ∉ wordSupport α) :
    ∃ β : Word n (p + 1), ∃ r : Fin (p + 1),
      β ∈ TailWords i (p + 1)
        ∧ β.get r = k
        ∧ eraseIdx β r = α := by
  let s : Finset (Fin n) := insert k (wordSupport α)
  have hαprops := mem_TailWords.mp hα
  have hsupport_card : (wordSupport α).card = p :=
    wordSupport_card_eq_of_strictMono hαprops.1
  have hcard : s.card = p + 1 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem hnot, hsupport_card]
  let β : Word n (p + 1) := List.Vector.ofFn fun t : Fin (p + 1) => (s.orderEmbOfFin hcard) t
  have hβ_get : ∀ t : Fin (p + 1), β.get t = (s.orderEmbOfFin hcard) t := by
    intro t
    simp [β]
  have hβ_strict : StrictMono fun t : Fin (p + 1) => β.get t := by
    intro a b hab
    simp_rw [hβ_get]
    exact (s.orderEmbOfFin hcard).strictMono hab
  have hβ_tail : ∀ t : Fin (p + 1), i < β.get t := by
    intro t
    have hmem : β.get t ∈ s := by
      rw [hβ_get]
      exact Finset.orderEmbOfFin_mem s hcard t
    rw [show s = insert k (wordSupport α) by rfl] at hmem
    rcases Finset.mem_insert.mp hmem with hkt | hsup
    · rw [hkt]
      exact hik
    · rcases mem_wordSupport.mp hsup with ⟨q, hq⟩
      rw [← hq]
      exact hαprops.2 q
  have hβ : β ∈ TailWords i (p + 1) := by
    rw [mem_TailWords]
    exact ⟨hβ_strict, hβ_tail⟩
  have hk_mem_s : k ∈ s := by
    dsimp [s]
    exact Finset.mem_insert_self k (wordSupport α)
  have hk_image : k ∈ Finset.image (fun t : Fin (p + 1) => (s.orderEmbOfFin hcard) t)
      Finset.univ := by
    rw [Finset.image_orderEmbOfFin_univ]
    exact hk_mem_s
  rcases Finset.mem_image.mp hk_image with ⟨r, _hrmem, hr⟩
  refine ⟨β, r, hβ, ?_, ?_⟩
  · rw [hβ_get]
    exact hr
  · apply List.Vector.ext
    intro q
    have herase_tail := mem_TailWords.mp (eraseIdx_mem_TailWords r hβ)
    have hnot_erased : k ∉ wordSupport (eraseIdx β r) := by
      rw [← hr]
      simpa [hβ_get] using get_not_mem_eraseIdx β r hβ_strict
    have herase_mem_support : ∀ q : Fin p, (eraseIdx β r).get q ∈ wordSupport α := by
      intro q
      have hval_s : (eraseIdx β r).get q ∈ s := by
        rw [eraseIdx_get, hβ_get]
        exact Finset.orderEmbOfFin_mem s hcard (r.succAbove q)
      have hval_ne : (eraseIdx β r).get q ≠ k := by
        intro heq
        exact hnot_erased (by rw [← heq]; exact mem_wordSupport.mpr ⟨q, rfl⟩)
      rw [show s = insert k (wordSupport α) by rfl] at hval_s
      rcases Finset.mem_insert.mp hval_s with hval_eq | hval_sup
      · exact (hval_ne hval_eq).elim
      · exact hval_sup
    have hα_order := Finset.orderEmbOfFin_unique hsupport_card
      (fun q : Fin p => mem_wordSupport.mpr ⟨q, rfl⟩) hαprops.1
    have herase_order := Finset.orderEmbOfFin_unique hsupport_card herase_mem_support herase_tail.1
    have h1 := congrFun hα_order q
    have h2 := congrFun herase_order q
    exact h2.trans h1.symm

theorem eraseIdx_get_unique {n p : Nat} {i : Fin n}
    {β γ : Word n (p + 1)} {r s : Fin (p + 1)}
    (hβ : β ∈ TailWords i (p + 1))
    (hγ : γ ∈ TailWords i (p + 1))
    (hget : β.get r = γ.get s)
    (herase : eraseIdx β r = eraseIdx γ s) :
    β = γ ∧ r = s := by
  have hβprops := mem_TailWords.mp hβ
  have hγprops := mem_TailWords.mp hγ
  have hsup : wordSupport β = wordSupport γ := by
    rw [wordSupport_eq_insert_eraseIdx β r, wordSupport_eq_insert_eraseIdx γ s, hget, herase]
  have hcard : (wordSupport β).card = p + 1 :=
    wordSupport_card_eq_of_strictMono hβprops.1
  have hβ_order := Finset.orderEmbOfFin_unique hcard
    (fun q : Fin (p + 1) => mem_wordSupport.mpr ⟨q, rfl⟩) hβprops.1
  have hγ_mem : ∀ q : Fin (p + 1), γ.get q ∈ wordSupport β := by
    intro q
    rw [hsup]
    exact mem_wordSupport.mpr ⟨q, rfl⟩
  have hγ_order := Finset.orderEmbOfFin_unique hcard hγ_mem hγprops.1
  have hβγ : β = γ := by
    apply List.Vector.ext
    intro q
    have h1 := congrFun hβ_order q
    have h2 := congrFun hγ_order q
    exact h1.trans h2.symm
  refine ⟨hβγ, ?_⟩
  have hget' : β.get r = β.get s := by
    simpa [hβγ] using hget
  exact hβprops.1.injective hget'

theorem offdiag_reindex_nonmem
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ x ∈ OffdiagDomain (i := i) (p := p),
        wordDet A (vcons i x.1) (vcons x.2 x.1) * A x.2 j)
      =
    ∑ y ∈ CofactorDomain (i := i) (p := p),
        wordDet A
          (vcons i (eraseIdx y.1 y.2))
          (vcons (y.1.get y.2) (eraseIdx y.1 y.2))
          * A (y.1.get y.2) j := by
  rw [eq_comm]
  refine Finset.sum_bij
    (fun y _hy => cofactorToOffdiag y)
    ?hmem ?hinj ?hsurj ?hfg
  · intro y hy
    exact cofactorToOffdiag_mem hy
  · intro y₁ hy₁ y₂ hy₂ hmap
    cases y₁ with
    | mk β r =>
      cases y₂ with
      | mk γ s =>
        rw [mem_CofactorDomain] at hy₁ hy₂
        have herase : eraseIdx β r = eraseIdx γ s := congrArg Sigma.fst hmap
        have hget : β.get r = γ.get s := congrArg Sigma.snd hmap
        rcases eraseIdx_get_unique hy₁ hy₂ hget herase with ⟨hβγ, hrs⟩
        cases hβγ
        cases hrs
        rfl
  · intro x hx
    cases x with
    | mk α k =>
      rw [mem_OffdiagDomain] at hx
      rcases hx with ⟨hα, hik, hnot⟩
      rcases exists_insert_eraseIdx hα hik hnot with ⟨β, r, hβ, hget, herase⟩
      refine ⟨⟨β, r⟩, ?_, ?_⟩
      · rw [mem_CofactorDomain]
        exact hβ
      · dsimp [cofactorToOffdiag]
        cases herase
        cases hget
        rfl
  · intro _y _hy
    rfl

theorem offdiag_term_eq_zero_of_mem_support
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n)
    (x : Σ _ : Word n p, Fin n)
    (hxmem : x.2 ∈ wordSupport x.1) :
    wordDet A (vcons i x.1) (vcons x.2 x.1) * A x.2 j = 0 := by
  rw [wordDet_vcons_duplicate_col_eq_zero A i x.2 x.1 hxmem]
  simp

theorem offdiag_all_eq_nonmem
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ x ∈ OffdiagAllDomain (i := i) (p := p),
        wordDet A (vcons i x.1) (vcons x.2 x.1) * A x.2 j)
      =
    ∑ x ∈ OffdiagDomain (i := i) (p := p),
        wordDet A (vcons i x.1) (vcons x.2 x.1) * A x.2 j := by
  rw [OffdiagDomain_eq_filter_OffdiagAllDomain]
  rw [eq_comm]
  refine Finset.sum_filter_of_ne ?_
  intro x _hx hne
  by_contra hxnot
  have hxmem : x.2 ∈ wordSupport x.1 := by simpa using hxnot
  exact hne (offdiag_term_eq_zero_of_mem_support A i j x hxmem)

theorem offdiag_reindex
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ x ∈ OffdiagAllDomain (i := i) (p := p),
        wordDet A (vcons i x.1) (vcons x.2 x.1) * A x.2 j)
      =
    ∑ y ∈ CofactorDomain (i := i) (p := p),
        wordDet A
          (vcons i (eraseIdx y.1 y.2))
          (vcons (y.1.get y.2) (eraseIdx y.1 y.2))
          * A (y.1.get y.2) j := by
  rw [offdiag_all_eq_nonmem A i j]
  exact offdiag_reindex_nonmem A i j

theorem offdiag_all_sum_conditional
    {R : Type*} [CommRing R]
    {n p : Nat}
    (i : Fin n)
    (f : (Σ _ : Word n p, Fin n) → R) :
    (∑ x ∈ OffdiagAllDomain (i := i) (p := p), f x) =
      ∑ k : Fin n,
        if i < k then
          ∑ α ∈ TailWords i p, f ⟨α, k⟩
        else 0 := by
  rw [OffdiagAllDomain, Finset.sum_sigma]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hik : i < k
  · simp [hik]
  · simp [hik]

theorem offdiag_reindex_conditional
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ k : Fin n,
        if i < k then
          ∑ α ∈ TailWords i p,
            wordDet A (vcons i α) (vcons k α) * A k j
        else 0)
      =
    ∑ y ∈ CofactorDomain (i := i) (p := p),
        wordDet A
          (vcons i (eraseIdx y.1 y.2))
          (vcons (y.1.get y.2) (eraseIdx y.1 y.2))
          * A (y.1.get y.2) j := by
  rw [← offdiag_all_sum_conditional i
    (fun x => wordDet A (vcons i x.1) (vcons x.2 x.1) * A x.2 j)]
  exact offdiag_reindex A i j

end Correctness
