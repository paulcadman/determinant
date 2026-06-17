module

public import Determinant.Correctness.WordDet
public import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

@[expose] public section

namespace Correctness

/-- Increasing words whose entries all lie strictly after `i`.

This is Bird's `S_p([i+1..n])`. -/
def TailWords {n : Nat} (i : Fin n) (p : Nat) :
    Finset (Word n p) :=
  Finset.univ.filter fun α =>
    StrictMono (fun t : Fin p => α.get t) ∧ ∀ t : Fin p, i < α.get t

theorem mem_TailWords {n p : Nat} {i : Fin n} {α : Word n p} :
    α ∈ TailWords i p ↔
      StrictMono (fun t : Fin p => α.get t) ∧ ∀ t : Fin p, i < α.get t := by
  simp [TailWords]

theorem TailWords_zero {n : Nat} (i : Fin n) :
    TailWords i 0 = {vnil} := by
  ext α
  constructor
  · intro _h
    rw [Finset.mem_singleton]
    exact List.Vector.eq_nil α
  · intro h
    rw [Finset.mem_singleton] at h
    rw [h, mem_TailWords]
    constructor
    · intro t
      exact Fin.elim0 t
    · intro t
      exact Fin.elim0 t

theorem vcons_mem_TailWords {n p : Nat} {i k : Fin n} {α : Word n p}
    (hik : i < k) (hα : α ∈ TailWords k p) :
    vcons k α ∈ TailWords i (p + 1) := by
  rw [mem_TailWords] at hα ⊢
  refine ⟨?_, ?_⟩
  · intro a b hab
    cases a using Fin.cases with
    | zero =>
        cases b using Fin.cases with
        | zero => simp at hab
        | succ b => simpa [vcons_get_zero, vcons_get_succ, vcons_head] using hα.2 b
    | succ a =>
        cases b using Fin.cases with
        | zero => simp at hab
        | succ b =>
            have hab' : a < b := by simpa using hab
            simpa [vcons_get_succ] using hα.1 hab'
  · intro t
    cases t using Fin.cases with
    | zero => simpa [vcons_get_zero, vcons_head] using hik
    | succ t => simpa [vcons_get_succ] using lt_trans hik (hα.2 t)

theorem vtail_mem_TailWords {n p : Nat} {i : Fin n} {β : Word n (p + 1)}
    (hβ : β ∈ TailWords i (p + 1)) :
    vtail β ∈ TailWords (β.get 0) p := by
  rw [mem_TailWords] at hβ ⊢
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h : (a.succ : Fin (p + 1)) < b.succ := by simpa using hab
    simpa [vtail_get] using hβ.1 h
  · intro t
    have h : (0 : Fin (p + 1)) < t.succ := by simp
    simpa [vtail_get] using hβ.1 h

theorem vcons_vtail {n p : Nat} (β : Word n (p + 1)) :
    vcons (β.get 0) (vtail β) = β := by
  apply List.Vector.ext
  intro q
  cases q using Fin.cases with
  | zero => exact vcons_get_zero (β.get 0) (vtail β)
  | succ q => simp [vcons_get_succ, vtail_get]

theorem vcons_injective {n p : Nat} {k l : Fin n} {α β : Word n p}
    (h : vcons k α = vcons l β) : k = l ∧ α = β := by
  constructor
  · have h0 := congrArg (fun w : Word n (p + 1) => w.get 0) h
    simpa [vcons_get_zero, vcons_head] using h0
  · apply List.Vector.ext
    intro q
    have hs := congrArg (fun w : Word n (p + 1) => w.get q.succ) h
    simpa [vcons_get_succ] using hs

theorem TailWords_head_lt {n p : Nat} {i : Fin n} {β : Word n (p + 1)}
    (hβ : β ∈ TailWords i (p + 1)) :
    i < β.get 0 := by
  exact (mem_TailWords.mp hβ).2 0

/-- The source finite set for the constructor bijection
`(k, α) ↦ vcons k α`. -/
def TailWordsConsDomain {n : Nat} (i : Fin n) (p : Nat) :
    Finset (Σ _ : Fin n, Word n p) :=
  (Finset.univ.filter fun k => i < k).sigma fun k => TailWords k p

theorem mem_TailWordsConsDomain {n p : Nat} {i : Fin n}
    {x : Σ _ : Fin n, Word n p} :
    x ∈ TailWordsConsDomain i p ↔ i < x.1 ∧ x.2 ∈ TailWords x.1 p := by
  cases x
  simp [TailWordsConsDomain]

/-- Reindex a sum over `TailWords i (p+1)` by writing each word uniquely as
`vcons k α`, where `i < k` and `α ∈ TailWords k p`. -/
theorem TailWords_cons_bij {n p : Nat} {M : Type*} [AddCommMonoid M]
    (i : Fin n) (f : Word n (p + 1) → M) :
    (∑ x ∈ TailWordsConsDomain i p, f (vcons x.1 x.2)) =
      ∑ β ∈ TailWords i (p + 1), f β := by
  refine Finset.sum_bij
    (fun x _hx => vcons x.1 x.2)
    ?hi ?hinj ?hsurj ?hfg
  · intro x hx
    rw [mem_TailWordsConsDomain] at hx
    exact vcons_mem_TailWords hx.1 hx.2
  · intro x _hx y _hy hxy
    cases x with
    | mk k α =>
      cases y with
      | mk l β =>
        rcases vcons_injective hxy with ⟨hk, hαβ⟩
        cases hk
        cases hαβ
        rfl
  · intro β hβ
    refine ⟨⟨β.get 0, vtail β⟩, ?_, ?_⟩
    · rw [mem_TailWordsConsDomain]
      exact ⟨TailWords_head_lt hβ, vtail_mem_TailWords hβ⟩
    · exact vcons_vtail β
  · intro _x _hx
    rfl

/-- Conditional-sum form of `TailWords_cons_bij`. -/
theorem TailWords_cons_sum {n p : Nat} {M : Type*} [AddCommMonoid M]
    (i : Fin n) (f : Word n (p + 1) → M) :
    (∑ β ∈ TailWords i (p + 1), f β) =
      ∑ k : Fin n, if i < k then ∑ α ∈ TailWords k p, f (vcons k α) else 0 := by
  rw [← TailWords_cons_bij i f]
  simp [TailWordsConsDomain, Finset.sum_sigma, Finset.sum_filter]

/-- The final tail word `[1, 2, ..., k]` in dimension `k + 1`. -/
def finalTailWord (k : Nat) : Word (k + 1) k :=
  List.Vector.ofFn fun t : Fin k => t.succ

theorem finalTailWord_get {k : Nat} (t : Fin k) :
    (finalTailWord k).get t = t.succ := by
  rw [finalTailWord, List.Vector.get_ofFn]

theorem TailWords_final_singleton (k : Nat) :
    TailWords (0 : Fin (k + 1)) k = {finalTailWord k} := by
  ext α
  constructor
  · intro hαmem
    rw [Finset.mem_singleton]
    rw [mem_TailWords] at hαmem
    apply List.Vector.ext
    intro t
    have hcard : (Finset.Ioi (0 : Fin (k + 1))).card = k := by
      simp
    have hαfs : ∀ x : Fin k, α.get x ∈ Finset.Ioi (0 : Fin (k + 1)) := by
      intro x
      rw [Finset.mem_Ioi]
      exact hαmem.2 x
    have hsuccfs : ∀ x : Fin k, (x.succ : Fin (k + 1)) ∈ Finset.Ioi (0 : Fin (k + 1)) := by
      intro x
      rw [Finset.mem_Ioi]
      simp
    have hαeq := congrFun (Finset.orderEmbOfFin_unique hcard hαfs hαmem.1) t
    have hseq := congrFun (Finset.orderEmbOfFin_unique hcard hsuccfs Fin.strictMono_succ) t
    simpa [finalTailWord_get] using hαeq.trans hseq.symm
  · intro hα
    rw [Finset.mem_singleton] at hα
    rw [hα, mem_TailWords]
    constructor
    · intro a b hab
      simpa [finalTailWord_get] using Fin.strictMono_succ hab
    · intro t
      simp [finalTailWord_get]

end Correctness
