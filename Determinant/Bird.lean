module

public import Determinant.FlatMatrix
public import Determinant.CbvOpaqueDefs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open FlatMatrix
open CbvOpaqueDefs

/-!
# Bird's determinant algorithm

This module contains two implementations of Bird's division-free determinant
algorithm using `FlatMatrix`.

The algorithm was first described in 
[A simple division-free algorithm for computing determinants](https://www.sciencedirect.com/science/article/abs/pii/S0020019011002353)
by Richard S. Bird.

# Desription

The implementations are as follows:

1. `birdDet` - constructs each intermediate matrix in the recurrence.

2. `birdDetEntry` - it does not construct the intermediate matrices. It
computes entries of the final matrix lazily and returns only the final `(0,0)
entry needed for the determinant.

The idea is that 2. is better for `cbv` because terms that do not affect the
final entry do not need to be reduced.
-/

namespace Bird

@[expose] public section

variable
  {R : Type*}
  [CommRing R]
  (n : Nat)

/-- Bird's `μ` function. -/
def μ (A : FlatMatrix R) : FlatMatrix R :=
  tabulate n fun i j =>
    let diag : R :=
      rneg (sumRange n fun k => if i < k then get n A k k else rzero)
    if j < i then rzero
    else if i = j then diag
    else get n A i j

/-- Bird's `F` function

`iterF n A k X` performs `k` steps from `X`. -/
def iterF (A : FlatMatrix R) : Nat → FlatMatrix R → FlatMatrix R
  | 0, X => X
  | k + 1, X => mul n (μ n (iterF A k X)) A

/-- Compute a determinant using Bird's algorithm -/
def birdDet (A : FlatMatrix R) : R :=
  match n with
  | 0 => rone
  | k + 1 => rmul (rpow (rneg rone) (n - 1)) (get n (iterF n A k A) 0 0)


/-- Scalar formula for one Bird recurrence step.

If `F_t` represents the entries of the previous step, then this computes the (i,
j) entry of `F_{t+q} = μ(F) * A` without computing the whole matrix `μ(F_t)` or the
product.

```latex
F_{t+1}[i,j] = ((-∑_{k=i+1}^{n-1} F[k,k]) * A[i,j]) + ∑_{k=i+1}^{n-1} F[i,k] * A[k,j]
```
-/
def birdStepEntry (A : FlatMatrix R) (F : Nat → Nat → R) (i j : Nat) : R :=
  radd
    (rmul
      (rneg (sumFrom n (i + 1) (fun k => F k k)))
      (get n A i j))
    (sumFrom n (i + 1) (fun k => rmul (F i k) (get n A k j)))

/-- Scalar-entry version of Bird iteration.

`iterEntry n A t F i j` computes the (i, j) entry after `t` Bird steps. -/
def iterEntry (A : FlatMatrix R) (t : Nat) (F : Nat → Nat → R) : Nat → Nat → R :=
  match t with
  | 0 => F
  | t + 1 => fun i j => birdStepEntry n A (iterEntry A t F) i j

/-- Scalar-entry Bird deterinant

This computes the same value as `birdDet` but it computes just the entry
required by the determinant instead of constructing each intermediate matrix. -/
def birdDetEntry (A : FlatMatrix R) : R :=
  match n with
  | 0 => rone
  | k + 1 =>
    rmul
      (rpow (rneg rone) (n - 1))
      (iterEntry n A k (fun i j => get n A i j) 0 0)

end

end Bird
