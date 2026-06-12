module

public import Mathlib.Algebra.Ring.Defs

@[expose] public section

namespace CertChain

variable
  {R : Type*}
  [CommRing R]

/-- Read a cell from a matrix, represented as an Array with cells in row-major
  order. Returns zero for out-of-bounds entries. -/
def get (n : Nat) (A : Array R) (i j : Nat) : R :=
  A.getD (i * n + j) 0

/-- Sum `f lo + ... + f (n - 1)`. Returns zero when `n <= lo`. -/
def sumFrom (n lo : Nat) (f : Nat → R) : R :=
  if lo < n then f lo + sumFrom n (lo + 1) f else 0

/-- Scalar formula for one Bird recurrence step.

If `F_t` represents the entries of the previous step, then this computes the (i,
j) entry of `F_{t+q} = μ(F) * A` without computing the whole matrix `μ(F_t)` or the
product.

```latex
F_{t+1}[i,j] = ((-∑_{k=i+1}^{n-1} F[k,k]) * A[i,j]) + ∑_{k=i+1}^{n-1} F[i,k] * A[k,j]
```
-/
def iter (n : Nat) (A : Array R) (t : Nat) (F : Nat → Nat → R) : Nat → Nat → R :=
  match t with
  | 0 => F
  | t + 1 => fun i j =>
    -(sumFrom n (i + 1) fun k => iter n A t F k k) * get n A i j
    + sumFrom n (i + 1) fun k => iter n A t F i k * get n A k j

/-- Scalar-entry Bird deterinant

This computes Bird determinant by recurrence on matrix entries required by the
determinant instead of constructing each intermediate matrix. -/
def birdDet (n : Nat) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * iter n A k (get n A) 0 0

theorem sumFrom_step (n lo : Nat) (f : Nat → R) (h : lo < n) :
    sumFrom n lo f = f lo + sumFrom n (lo + 1) f := by
      rw [sumFrom]
      simp [h]

theorem sumFrom_stop (n lo : Nat) (f : Nat → R) (h : ¬ lo < n) :
    sumFrom n lo f = 0 := by
      rw [sumFrom]
      simp [h]

theorem iter_zero (n : Nat) (A : Array R) (F : Nat → Nat → R) (i j : Nat) :
    iter n A 0 F i j = F i j := rfl

theorem iter_succ (n : Nat) (A : Array R) (t : Nat) (F : Nat → Nat → R) (i j : Nat) :
    iter n A (t + 1) F i j =
    -(sumFrom n (i + 1) fun k => iter n A t F k k) * get n A i j
    + sumFrom n (i + 1) fun k => iter n A t F i k * get n A k j := rfl

theorem birdDet_zero (A : Array R) : birdDet 0 A = 1 := rfl

theorem birdDet_eq (n k : Nat) (A : Array R) (hn : n = k + 1) :
    birdDet n A = (-1 : R) ^ k * iter n A k (get n A) 0 0 := by
      subst hn
      rfl

end CertChain

end
