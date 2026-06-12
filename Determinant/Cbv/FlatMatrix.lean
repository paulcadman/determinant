module

public meta import Mathlib.Tactic.Ring
public import Determinant.Cbv.CbvOpaqueDefs
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

open CbvOpaqueDefs

@[expose] public section

/-- A representation of a Matrix as a flat `Array` with row-major ordering-/
abbrev FlatMatrix (R : Type*) := Array R

namespace FlatMatrix

variable
  {R : Type*}
  [CommRing R]
  (n : Nat)

/-- Row-major index for an `n × n` `FlatMatrix`. -/
def idx (n i j : Nat) : Nat :=
  i * n + j

/-- Total `FlatMatrix` read with zero for out-of-bounds entries. -/
def get (A : FlatMatrix R) (i j : Nat) : R :=
  A.getD (idx n i j) rzero

/-- Sum `f lo + ... + f (n - 1)`. -/
def sumFrom (lo : Nat) (f : Nat → R) : R :=
  (List.range' lo (n - lo)).foldl (fun acc k => radd acc (f k)) rzero

/-- Sum `f 0 + ... + f (n - 1)` using `List.range` -/
def sumRange (f : Nat → R) : R := sumFrom n 0 f

/-- Build an `n × n` row-major matrix from a Nat-indexed entry function. -/
def tabulate (f : Nat → Nat → R) : FlatMatrix R :=
  ((List.range (n * n)).map fun p => f (p / n) (p % n)).toArray

/-- `FlatMatrix` multiplication. -/
def mul (A B : FlatMatrix R) : FlatMatrix R :=
  tabulate n fun i j =>
    sumRange n fun k => rmul (get n A i k) (get n B k j)

end FlatMatrix

end

namespace FlatMatrix.Examples

def id2 : FlatMatrix Int :=
  tabulate 2 <| fun i j =>
    match i, j with
    | 0,0 => 1
    | 0,1 => 0
    | 1,0 => 0
    | 1,1 => 1
    | _,_ => 0

def m2 : FlatMatrix Int :=
  tabulate 2 <| fun i j =>
    match i, j with
    | 0,0 => 1
    | 0,1 => 2
    | 1,0 => 2
    | 1,1 => 1
    | _,_ => 0

example : mul 2 id2 m2 = m2 := by
  cbv

example : mul 2 m2 m2 = #[5, 4, 4, 5] := by
  cbv

example : sumRange 5 (fun (n : Nat) => Int.ofNat n + 1) = 15 := by
  cbv

example : sumFrom 5 (lo := 1) (fun (n : Nat) => Int.ofNat n) = 10 := by
  cbv

end FlatMatrix.Examples
