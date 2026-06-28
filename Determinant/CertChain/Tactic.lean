module

public import Determinant.CertChain.Cert
public import Determinant.Correctness.Theorem

/-!
# Tactic frontend for the certificate-chain determinant evaluator

This module exposes the certificate-chain evaluator as simplification
procedures for determinant expressions backed by literal flat arrays.

The `BirdDet.birdDet` simproc reifies a determinant call, constructs a
proof-producing normalization certificate with `Cert.certBirdDet`, then returns
the normalized expression and proof to the simplifier.

For Mathlib determinants, the Matrix simproc recognizes
`Matrix.det (BirdDet.ofFlatArray A hA)`, rewrites it to the corresponding
`BirdDet.birdDet` call using `BirdDet.det_ofFlatArray_eq_birdDet`, and then
runs the same certificate-chain normalizer.

The `eval_det` tactic is a small frontend for running both simprocs:

```lean
by
  eval_det
```

The evaluator is intentionally limited to the literal flat-array form accepted
by `Meta.reifyBirdDet`.
-/

open Lean Meta Elab Tactic Simp
open Qq
open Cert

public meta section

def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let info ← Meta.reifyBirdDet e
  let ctx := Ctx.ofBirdDetInfo info
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

def normalizeDetOfFlatArray (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrix := e
    | throwError "expected `Matrix.det`, got{indentExpr e}"
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  let_expr BirdDet.ofFlatArray _ dimensionExpr columnCountExpr arrayExpr sizeProof := matrix
    | throwError "expected determinant of `BirdDet.ofFlatArray`, got{indentExpr matrix}"
  let some dimensionExpr ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected row dimension to have type `Nat`, got{indentExpr dimensionExpr}"
  let some columnCountExpr ← checkTypeQ columnCountExpr q(Nat)
    | throwError "expected column dimension to have type `Nat`, got{indentExpr columnCountExpr}"
  unless ← isDefEq dimensionExpr columnCountExpr do
    throwError
      "expected square `BirdDet.ofFlatArray`, got dimensions{indentExpr dimensionExpr}{indentExpr columnCountExpr}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected flat array to have type{indentExpr q(Array $α)}"
  let some sizeProof ← withDefault <|
      checkTypeQ sizeProof q(Array.size $arrayExpr = $dimensionExpr * $dimensionExpr)
    | throwError
        "expected flat-array size proof to have type{indentExpr q(Array.size $arrayExpr = $dimensionExpr * $dimensionExpr)}"
  let birdExpr : Q($α) := q(@BirdDet.birdDet $α $detRingInst $dimensionExpr $arrayExpr)
  let matrixDet : Q($α) :=
    q(Matrix.det (BirdDet.ofFlatArray (n := $dimensionExpr) (m := $dimensionExpr)
      $arrayExpr $sizeProof))
  let bridge' : Q($matrixDet = $birdExpr) :=
    q(@BirdDet.det_ofFlatArray_eq_birdDet $α $detRingInst $dimensionExpr $arrayExpr $sizeProof)
  let bridge : Q($e = $birdExpr) :=
    bridge'
  let birdNorm ← normalizeBirdDet birdExpr
  ({expr := birdExpr, proof? := some bridge} : Simp.Result).mkEqTrans birdNorm

/--
Normalize literal `BirdDet.birdDet` calls using the certificate-chain evaluator.
-/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/--
Normalize `Matrix.det` calls whose matrix is the checked flat-array constructor
by rewriting through `BirdDet.det_ofFlatArray_eq_birdDet`.
-/
simproc_decl norm_matrix_det (Matrix.det (BirdDet.ofFlatArray _ _)) := fun e => do
  return .done (← normalizeDetOfFlatArray e)

/-- Normalize supported determinant calls in the target using the certificate-chain simprocs. -/
macro "eval_det" : tactic => `(tactic| simp only [norm_det, norm_matrix_det])

end
