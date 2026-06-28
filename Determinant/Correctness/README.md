# Correctness Proof Architecture

This directory formalizes the proof in Section 2 of
`papers/bird-det-2011.pdf`, Richard Bird's "A simple division-free algorithm for
computing determinants".

The proof has two layers:

1. `Spec.lean` through `Theorem.lean` formalize Bird's paper proof for a
   proof-friendly matrix recurrence over `Matrix (Fin n) (Fin n) R`.
2. `FlatMatrix.lean` and `FlatAdapter.lean` connect that proof-friendly theorem
   to the flat-array `birdDet` implementation used by CertChain.

If you are reading the proof next to the paper, start with
`PaperEquations.lean`. It lists the Lean theorem aliases for Bird equations (1),
(2), (3), and (5), the off-diagonal comparison after (5), and the final theorem.
For the paragraph after equation (5), read `Offdiag.lean`; that is where the
informal reindexing argument becomes an explicit bijection.

## Paper Notation To Lean

Bird's paper uses 1-based matrix indices `{1 .. n}`. The Lean development uses
`Fin n`, so indices are 0-based. This is the main off-by-one translation to keep
in mind:

| Paper | Lean |
| --- | --- |
| matrix `A = (a_ij)` | `A : Matrix (Fin n) (Fin n) R` |
| word over `{1 .. n}` | `Word n p`, a `List.Vector (Fin n) p` |
| determinant `f[alpha, beta]` | `wordDet A alpha beta` |
| word `i alpha` | `vcons i alpha` |
| empty word | `vnil` |
| `[1 .. n]` | `fullWord n` |
| tail alphabet `[i + 1 .. n]` | entries strictly greater than `i` |
| `S_p([i + 1 .. n])` | `TailWords i p` |
| remove `k` from a word | `eraseIdx beta r`, where `beta.get r = k` |
| `x_ij^(p)`, entry of `F_A^p(A)` | `iterEntry A p (fun i j => A i j) i j` |

Warning: Bird's tail alphabet `βᵢ = [i+1 .. n]` is not represented as a separate
Lean object. Instead, `TailWords i p` directly represents `S_p(βᵢ)`. Variables
called `β` in the Lean files are usually actual words in a `TailWords` set, not
the paper's alphabet `βᵢ`.

The paper treats words extensionally and writes expressions such as
`alpha \ k`. In Lean, removing a value requires a position, not just the value.
That is why `Offdiag.lean` carries sigma terms like
`Sigma beta, Fin (p + 1)`: the `Fin (p + 1)` is the position being erased.

## The Recurrence

Bird defines `mu(X)` by replacing each diagonal entry by the negated sum of the
diagonal entries below it, zeroing entries below the diagonal, and leaving
entries above the diagonal unchanged. The algorithm then iterates

```text
F_A(X) = mu(X) * A
```

The Lean proof does not define the full matrix `mu(X)`. Instead,
`Spec.lean` defines the scalar entry recurrence directly:

```lean
stepEntry A F i j =
  (-sum over k > i of F k k) * A i j
    + sum over k > i of F i k * A k j
```

This is exactly the `(i, j)` entry of `mu(F) * A`. The iteration
`iterEntry A p (fun i j => A i j)` is the Lean counterpart of the entries of
`F_A^p(A)` in the paper.

## Equation Map

### Equation (1): Main Invariant

Bird's invariant says that the `(i, j)` entry after `p` iterations is a signed
sum of word determinants over tails after `i`.

Lean theorem:

```lean
iterEntry_formula
```

Lean shape:

```lean
iterEntry A p (fun i j => A i j) i j =
  (-1)^p *
    sum alpha in TailWords i p,
      wordDet A (vcons i alpha) (vcons j alpha)
```

This is the central theorem in `Invariant.lean`.

The induction step in `Invariant.lean` follows the paper order. It unfolds one
Bird step, uses `diagonal_formula` for the diagonal part, uses
`offdiag_update_formula` for the off-diagonal part, reindexes that off-diagonal
sum with `offdiag_reindex_conditional`, and then applies
`sum_wordDet_cons_cons_expand_wordDet_mul`. The final `ring` call only tidies up
the signs and scalar distributivity.

### Equation (2): Diagonal Formula

The diagonal entry of `mu(F_A^p(A))` is the negated sum of later diagonal
entries. After applying the induction hypothesis, this becomes the signed sum
over `TailWords i (p + 1)`.

Lean theorem:

```lean
diagonal_formula
```

The Lean proof uses:

```lean
TailWords_cons_sum
```

to rewrite a sum over first choices `k > i` and tails after `k` into a single
sum over all tails after `i`.

### Equation (3): Bird Update After Induction

The off-diagonal part of the matrix product contributes terms of the form

```text
word determinant with rows i alpha and columns k alpha, times A k j
```

Lean names one such term:

```lean
offdiagTerm A i j x
```

The theorem

```lean
offdiag_update_formula
```

is the Lean version of Bird's equation (3), after applying the induction
hypothesis and separating the diagonal and off-diagonal contributions.

### Equation (5): Summed Laplace Expansion

Bird expands each determinant in the right hand side of equation (4) by its
first column, then sums those expansions over all tail words.

Lean theorem:

```lean
sum_wordDet_cons_cons_expand
```

This depends on the first-column expansion in `WordDet.lean`:

```lean
wordDet_cons_cons_expand
```

The raw cofactor expansion has signs and column permutations. `WordDet.lean`
contains the bookkeeping lemmas that move the removed column to the front and
cancel the signs into Bird's ordered-word form.

### Comparing Equations (3) And (5)

The paper says the second sums in equations (3) and (5) are the same after
discarding duplicate-column terms and reindexing. This is the most
bookkeeping-heavy part of the Lean proof.

Lean names one cofactor-side term:

```lean
cofactorTerm A i j y
```

The main comparison theorem is:

```lean
offdiag_reindex_conditional
```

The supporting lemmas do two jobs:

* `wordDet_vcons_duplicate_col_eq_zero` proves terms vanish when a column word
  repeats an index.
* `exists_insert_eraseIdx` and `eraseIdx_get_unique` formalize the bijection
  between inserting a missing `k` into a tail word and erasing that `k` again.

This corresponds to the paragraph after Bird's equation (5).

## Final Theorem

Once equation (1) is proved, `Theorem.lean` specializes it to `p = n - 1`,
`i = 0`, and `j = 0`.

The final tail set is a singleton:

```lean
TailWords_final_singleton
```

and the singleton tail gives the full word:

```lean
vcons_zero_finalTailWord_eq_fullWord
```

Then:

```lean
wordDet_full_eq_det
```

turns the full-word determinant into Mathlib's `Matrix.det`, and the two
factors of `(-1)^(n - 1)` cancel. The final proof-friendly theorem is:

```lean
birdDetSpec_eq_det
```

## File Map

`Spec.lean` defines the scalar recurrence and `birdDetSpec`.

`WordDet.lean` contains word constructors, word determinants, duplicate
row/column facts, the full-word determinant theorem, and the first-column
Laplace expansion.

`TailWords.lean` defines Bird's increasing tail-word domains and the
decomposition of `TailWords i (p + 1)` by first element.

`WordSupport.lean` tracks values appearing in a word and proves duplicate-column
zero lemmas.

`Offdiag.lean` compares Bird equation (3)'s off-diagonal sum with equation
(5)'s cofactor sum.

`Invariant.lean` proves Bird equation (1) from the diagonal formula,
off-diagonal comparison, and summed Laplace expansion.

`Theorem.lean` specializes the invariant to the final singleton tail and proves
`birdDetSpec_eq_det`.

`FlatMatrix.lean` defines the checked rectangular row-major matrix constructor
`ofFlatArray`. Determinant goals use the square specialization
`ofFlatArray (m := n) (n := n) A hA`, where `hA : A.size = n * n`.

`FlatAdapter.lean` connects the flat-array Bird implementation to
`birdDetSpec` and `Matrix.det`.
