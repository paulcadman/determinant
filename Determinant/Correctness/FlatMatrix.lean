module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

namespace BirdDet

/-- Construct a matrix from an array in row-major ordering. -/
def ofFlatArray
    {R : Type*}
    {m n : Nat}
    (A : Array R)
    (hA : A.size = m * n) :
    Matrix (Fin m) (Fin n) R :=
  fun i j => A[Fin.mkDivMod i j]

theorem ofFlatArray_apply
    {R : Type*}
    {m n : Nat}
    (A : Array R)
    (hA : A.size = m * n)
    (i : Fin m) (j : Fin n) :
    ofFlatArray A hA i j =
      A[Fin.mkDivMod i j] := rfl

end BirdDet

end
