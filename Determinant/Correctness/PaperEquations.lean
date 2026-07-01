module

public import Determinant.Correctness.Invariant
public import Determinant.Correctness.Theorem

@[expose] public section

open scoped BigOperators

namespace Correctness

theorem paper_eq1_iterEntry_formula
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (p : Nat)
    (i j : Fin n) :
    Correctness.iterEntry A p (fun i j => A i j) i j =
      (-1 : R)^p *
        (∑ α ∈ TailWords i p,
          wordDet A (vcons i α) (vcons j α)) := by
  exact iterEntry_formula A p i j

theorem paper_eq2_diagonal_formula
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
  exact diagonal_formula A p i hdiag

theorem paper_eq3_offdiag_update
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
  exact offdiag_update_formula A ih i j

theorem paper_eq5_laplace_sum
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
  exact sum_wordDet_cons_cons_expand A i j

theorem paper_eq3_eq_eq5_offdiag
    {R : Type*} [CommRing R]
    {n p : Nat}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ k : Fin n,
        if i < k then
          ∑ α ∈ TailWords i p,
            offdiagTerm A i j ⟨α, k⟩
        else 0)
      =
    ∑ y ∈ CofactorDomain (i := i) (p := p), cofactorTerm A i j y := by
  exact offdiag_reindex_conditional A i j

theorem paper_theorem1
    {R : Type*} [CommRing R]
    {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) :
    Correctness.birdDetSpec A = A.det := by
  exact birdDetSpec_eq_det A

end Correctness

end
