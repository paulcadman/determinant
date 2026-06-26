module

public import Determinant.CertChain.Bird
public meta import Mathlib.Util.Qq

open Lean Meta Qq
open BirdDet

public meta section

namespace Meta

/-- Parse an array literal into an array of element expressions. -/
def arrayLiteral? (e : Expr) : MetaM (Option (Array Expr)) := do
  if let some elems ← getArrayLit? e then return some elems
  let e ← zetaReduce (← whnf e)
  match_expr e with
  | Array.mk _ xs => getListLit? xs
  | _ => return none

/-- The typed matrix data parsed from a `birdDet` call. -/
structure BirdDetData {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- The dimension of the reified matrix -/
  dimension : Nat
  /-- The quoted dimension expression from the reified determinant call. -/
  dimensionExpr : Q(Nat)
  /-- The array of matrix entries as an Expr -/
  arrayExpr : Q(Array $α)
  /-- An array of matrix entry `Expr`s` -/
  arrayEntries : Array Q($α)

/-- Information parsed by `reifyBirdDet`. -/
structure BirdDetInfo where
  {u : Level}
  {α : Q(Type u)}
  /-- The `CommRing` instance for matrix entries -/
  rα : Q(CommRing $α)
  /-- The typed matrix data parsed from the determinant expression. -/
  data : BirdDetData rα

namespace BirdDetInfo

def dimension (info : BirdDetInfo) : Nat :=
  info.data.dimension

def arrayExpr (info : BirdDetInfo) :=
  info.data.arrayExpr

def arrayEntries (info : BirdDetInfo) :=
  info.data.arrayEntries

end BirdDetInfo

/-- Recognise a `birdDet` call and reify the matrix argument into `BirdDetInfo`. -/
def reifyBirdDet (e : Expr) : MetaM BirdDetInfo := do
  let e ← instantiateMVars e
  let ⟨_, α, _⟩ ← inferTypeQ' e
  let_expr birdDet _ birdRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let some rα ← checkTypeQ birdRingInst q(CommRing $α)
    | throwError "expected `birdDet` ring instance to have type{indentExpr q(CommRing $α)}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionLit ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected the dimension to have type `Nat`, got {dimensionExpr}"
  let some dimension ← getNatValue? dimensionLit
    | throwError "expected the dimension to be a `Nat` literal, got {dimensionLit}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected the array to have type{indentExpr q(Array $α)}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, expected {dimension * dimension}"
  let arrayEntries ← arrayEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry α
      | throwError "expected array entry to have type{indentExpr α}"
    return entry
  return {
    rα
    data := {
      dimension
      dimensionExpr := dimensionLit
      arrayExpr
      arrayEntries
    }
  }

end Meta

end
