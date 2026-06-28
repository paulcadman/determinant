module

public import Determinant.CertChain.Bird
public meta import Mathlib.Util.Qq

/-!
# Reification support for the certificate-chain evaluator

This module contains the meta-level parser used by the certificate-chain
frontend. It recognizes applications of `BirdDet.birdDet` whose matrix argument
is a literal flat array, checks that the array has exactly `n * n` entries, and
packages the result as typed Qq data.

The later certificate construction code relies on these checks: it receives the
exact `CommRing` instance from the original determinant expression, a typed
dimension expression, the typed array expression, and the typed literal entries.
This keeps the lower-level certifier focused on proof construction rather than
on expression validation.
-/

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
