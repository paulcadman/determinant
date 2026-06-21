module

public import Determinant.Correctness.Offdiag

open scoped BigOperators

@[expose] public section

namespace Correctness

/-!
This file proves Bird's main invariant for the proof-friendly scalar recurrence.
The structure mirrors the paper:

* `diagonal_formula` is Bird equation (2).
* `offdiag_update_formula` is the off-diagonal part of Bird equation (3) after
  applying the induction hypothesis.
* `sum_wordDet_cons_cons_expand` is the summed first-column Laplace expansion,
  Bird equation (5).
* `offdiag_reindex_conditional` compares the off-diagonal sums in equations (3)
  and (5).
* `iterEntry_formula` is Bird equation (1).
-/

/-- Bird equation (2), assuming the diagonal case of the induction hypothesis. -/
theorem diagonal_formula
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (p : Nat) (i : Fin n)
    (hdiag :
      ∀ k : Fin n,
        Correctness.iterEntry A p (fun i j => A i j) k k =
          (-1 : R)^p *
            (∑ α ∈ TailWords k p,
              wordDet A (vcons k α) (vcons k α))) :
    -(∑ k : Fin n,
        if i < k then
          Correctness.iterEntry A p (fun i j => A i j) k k
        else 0)
      =
      (-1 : R)^(p + 1) *
        (∑ α ∈ TailWords i (p + 1),
          wordDet A α α) := by
  rw [TailWords_cons_sum i (fun α => wordDet A α α)]
  simp_rw [hdiag]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hik : i < k
  · simp [hik, pow_succ]
  · simp [hik]

theorem iterEntry_formula_zero
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    Correctness.iterEntry A 0 (fun i j => A i j) i j =
      (-1 : R)^0 *
        (∑ α ∈ TailWords i 0,
          wordDet A (vcons i α) (vcons j α)) := by
  rw [TailWords_zero]
  simp only [Finset.sum_singleton, pow_zero, one_mul]
  change A i j = wordDet A (vsingle i) (vsingle j)
  rw [wordDet_singleton]

/--
Summed first-column Laplace expansion, Bird equation (5).

It sums the first-column expansion of:

```text
f[iγ, jγ]
```

over all:

```text
γ ∈ S_{p+1}(βᵢ)
```

In Lean, `γ` is a word in `TailWords i (p + 1)`. Choosing
`r : Fin (p + 1)` gives `k = γ.get r`, and `eraseIdx γ r` is Bird's `γ \ k`.
-/
theorem sum_wordDet_cons_cons_expand
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ β ∈ TailWords i (p + 1),
        wordDet A (vcons i β) (vcons j β))
      =
      A i j * (∑ β ∈ TailWords i (p + 1), wordDet A β β)
        -
      ∑ y ∈ CofactorDomain (i := i) (p := p),
        A (y.1.get y.2) j *
          wordDet A
            (vcons i (eraseIdx y.1 y.2))
            (vcons (y.1.get y.2) (eraseIdx y.1 y.2)) := by
  calc
    (∑ β ∈ TailWords i (p + 1),
        wordDet A (vcons i β) (vcons j β))
        = ∑ β ∈ TailWords i (p + 1),
            (A i j * wordDet A β β -
              ∑ r : Fin (p + 1),
                A (β.get r) j *
                  wordDet A
                    (vcons i (eraseIdx β r))
                    (vcons (β.get r) (eraseIdx β r))) := by
          apply Finset.sum_congr rfl
          intro β hβ
          exact wordDet_cons_cons_expand A i j β
    _ = A i j * (∑ β ∈ TailWords i (p + 1), wordDet A β β)
          -
        ∑ y ∈ CofactorDomain (i := i) (p := p),
          A (y.1.get y.2) j *
            wordDet A
              (vcons i (eraseIdx y.1 y.2))
              (vcons (y.1.get y.2) (eraseIdx y.1 y.2)) := by
          rw [Finset.sum_sub_distrib]
          rw [← Finset.mul_sum]
          simp [CofactorDomain, Finset.sum_sigma]

/--
The same identity as `sum_wordDet_cons_cons_expand`, with the product order in
the cofactor sum changed so it matches `offdiagTerm`.
-/
theorem sum_wordDet_cons_cons_expand_wordDet_mul
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ β ∈ TailWords i (p + 1),
        wordDet A (vcons i β) (vcons j β))
      =
      A i j * (∑ β ∈ TailWords i (p + 1), wordDet A β β)
        -
      ∑ y ∈ CofactorDomain (i := i) (p := p),
          wordDet A
            (vcons i (eraseIdx y.1 y.2))
            (vcons (y.1.get y.2) (eraseIdx y.1 y.2)) *
          A (y.1.get y.2) j := by
  rw [sum_wordDet_cons_cons_expand]
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  rw [mul_comm]

lemma neg_one_pow_eq_neg_succ
    {R : Type*} [CommRing R] (p : Nat) :
    (-1 : R)^p = -((-1 : R)^(p + 1)) := by
  rw [pow_succ]
  simp [mul_comm]

lemma neg_one_pow_succ_mul_neg_one
    {R : Type*} [CommRing R] (p : Nat) :
    (-1 : R)^(p + 1) = -((-1 : R)^p) := by
  rw [pow_succ]
  simp [mul_comm]

/--
Bird equation (3), off-diagonal part after applying the induction hypothesis.

Paper form:

```text
∑_{k ∈ βᵢ} x^(p)_{ik} a_{kj}
```

After induction:

```text
(-1)^p ∑_{k ∈ βᵢ} ∑_{α ∈ S_p(βᵢ)}
  f[iα, kα] a_{kj}
```

After sign rewrite and reindexing:

```text
-(-1)^(p+1) ∑_{cofactor domain} cofactorTerm
```

The Lean theorem below is `offdiag_update_formula`.
-/
theorem offdiag_update_formula
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (ih :
      ∀ i j : Fin n,
        Correctness.iterEntry A p (fun i j => A i j) i j =
          (-1 : R)^p *
            (∑ α ∈ TailWords i p,
              wordDet A (vcons i α) (vcons j α)))
    (i j : Fin n) :
    (∑ k : Fin n,
        if i < k then
          Correctness.iterEntry A p (fun i j => A i j) i k * A k j
        else 0)
      =
      -((-1 : R)^(p + 1)) *
        (∑ y ∈ CofactorDomain (i := i) (p := p),
          wordDet A
            (vcons i (eraseIdx y.1 y.2))
            (vcons (y.1.get y.2) (eraseIdx y.1 y.2)) *
          A (y.1.get y.2) j) := by
  calc
    (∑ k : Fin n,
        if i < k then
          Correctness.iterEntry A p (fun i j => A i j) i k * A k j
        else 0)
        = ∑ k : Fin n,
            (-1 : R)^p *
              (if i < k then
                (∑ α ∈ TailWords i p,
                  wordDet A (vcons i α) (vcons k α) * A k j)
              else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [ih i k]
          by_cases hik : i < k
          · simp [hik, Finset.sum_mul, mul_assoc]
          · simp [hik]
    _ = (-1 : R)^p *
          (∑ k : Fin n,
            if i < k then
              ∑ α ∈ TailWords i p,
                offdiagTerm A i j ⟨α, k⟩
            else 0) := by
          rw [Finset.mul_sum]
          simp [offdiagTerm]
    _ = (-1 : R)^p *
        (∑ y ∈ CofactorDomain (i := i) (p := p), cofactorTerm A i j y) := by
          rw [offdiag_reindex_conditional A i j]
    _ = -((-1 : R)^(p + 1)) *
        (∑ y ∈ CofactorDomain (i := i) (p := p), cofactorTerm A i j y) := by
          rw [neg_one_pow_eq_neg_succ]

/--
The induction step follows Bird's paper as follows.

1. Unfold one Bird step. This gives the diagonal part plus the off-diagonal
   part.
2. `diagonal_formula` rewrites the diagonal part to the first sum in equation
   (3).
3. `offdiag_update_formula` rewrites the off-diagonal part to the second sum in
   equation (3), and uses `offdiag_reindex_conditional` to put it in the same
   cofactor domain as equation (5).
4. `sum_wordDet_cons_cons_expand_wordDet_mul` says that the diagonal sum minus
   the cofactor sum is exactly the summed first-column expansion of the target
   determinant sum.
5. The final `ring` step only handles signs and distributivity of the scalar
   factor `(-1)^(p+1)`.
-/
theorem iterEntry_formula_succ
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (ih :
      ∀ i j : Fin n,
        Correctness.iterEntry A p (fun i j => A i j) i j =
          (-1 : R)^p *
            (∑ α ∈ TailWords i p,
              wordDet A (vcons i α) (vcons j α)))
    (i j : Fin n) :
    Correctness.iterEntry A (p + 1) (fun i j => A i j) i j =
      (-1 : R)^(p + 1) *
        (∑ β ∈ TailWords i (p + 1),
          wordDet A (vcons i β) (vcons j β)) := by
  rw [Correctness.iterEntry_succ]
  change Correctness.stepEntry A (Correctness.iterEntry A p (fun i j => A i j)) i j = _
  rw [Correctness.stepEntry_eq]
  rw [diagonal_formula A p i (fun k => ih k k)]
  rw [offdiag_update_formula A ih i j]
  rw [sum_wordDet_cons_cons_expand_wordDet_mul A i j]
  ring

/-- Bird equation (1), the main scalar-entry invariant. -/
theorem iterEntry_formula
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (p : Nat)
    (i j : Fin n) :
    Correctness.iterEntry A p (fun i j => A i j) i j =
      (-1 : R)^p *
        (∑ α ∈ TailWords i p,
          wordDet A (vcons i α) (vcons j α)) := by
  induction p generalizing i j with
  | zero =>
      exact iterEntry_formula_zero A i j
  | succ p ih =>
      exact iterEntry_formula_succ A ih i j

end Correctness
