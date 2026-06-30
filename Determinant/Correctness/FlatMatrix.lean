module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

namespace Matrix

/-- Construct a matrix from an array in row-major ordering. -/
def ofFlatArray
    {α : Type*}
    {m n : Nat}
    (A : Array α)
    (hA : A.size = m * n) :
    Matrix (Fin m) (Fin n) α :=
  fun i j => A[Fin.mkDivMod i j]

theorem ofFlatArray_apply
    {α : Type*}
    {m n : Nat}
    (A : Array α)
    (hA : A.size = m * n)
    (i : Fin m) (j : Fin n) :
    ofFlatArray A hA i j =
      A[Fin.mkDivMod i j] := rfl

end Matrix

end
