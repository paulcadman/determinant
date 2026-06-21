module

public import Determinant.CertChain.Meta
public import Determinant.CertChain.Cert
public import Determinant.Correctness.Theorem
public import Mathlib.Tactic.Ring
public import Mathlib.Lean.Meta.Simp
import Qq

open Lean Meta Elab Tactic Simp
open Qq
open Mathlib.Tactic.Ring
open Cert

public meta section

def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let info ← Meta.reifyBirdDet e
  let α := info.ringType
  let birdRingInst := info.birdRingInst
  let sαExpr := CtxOps.birdCommSemiring birdRingInst
  let some sα ← checkTypeQ sαExpr q(CommSemiring $α)
    | throwError "cert_bird_det: failed to derive `CommSemiring` from Bird ring instance"
  let cα : Common.Cache sα := {
    rα := some birdRingInst
    dsα := none
    czα := none
  }
  let ops := CtxOps.ofCommRing birdRingInst info.dimensionExpr info.arrayExpr
  let ctx : Ctx sα := {
    cα,
    rc := ringCompute cα,
    birdRingInst
    dimension := info.dimension
    dimensionExpr := info.dimensionExpr
    array := info.arrayExpr
    arrayEntries := info.arrayEntries
    ops
  }
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.eq.rhs, proof? := some detNorm.eq.proof}

def normalizeDetOfFlatArray (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  let ⟨u, α, _⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrix := e
    | throwError "expected `Matrix.det`, got{indentExpr e}"
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  let_expr BirdDet.ofFlatArray _ dimensionExpr columnCountExpr arrayExpr sizeProof := matrix
    | throwError "expected determinant of `BirdDet.ofFlatArray`, got{indentExpr matrix}"
  unless ← isDefEq dimensionExpr columnCountExpr do
    throwError
      "expected square `BirdDet.ofFlatArray`, got dimensions{indentExpr dimensionExpr}{indentExpr columnCountExpr}"
  let some dimensionExpr ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected row dimension to have type `Nat`, got{indentExpr dimensionExpr}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected flat array to have type{indentExpr q(Array $α)}"
  let birdExpr : Q($α) :=
    mkAppN (mkConst ``BirdDet.birdDet [u]) #[
      α, detRingInst, dimensionExpr, arrayExpr]
  let bridge ← mkExpectedTypeHint
    (mkAppN (mkConst ``BirdDet.det_ofFlatArray_eq_birdDet [u]) #[
      α, detRingInst, dimensionExpr, arrayExpr, sizeProof])
    (← mkEq e birdExpr)
  let birdNorm ← normalizeBirdDet birdExpr
  ({expr := birdExpr, proof? := some bridge} : Simp.Result).mkEqTrans birdNorm

/-- Normalize literal `birdDet` calls using the certificate-chain evaluator. -/
simproc ↓ cert_bird_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/--
Normalize `Matrix.det` calls whose matrix is the checked flat-array constructor
by rewriting through `BirdDet.det_ofFlatArray_eq_birdDet`.
-/
simproc ↓ cert_matrix_det (Matrix.det (BirdDet.ofFlatArray _ _)) := fun e => do
  return .done (← normalizeDetOfFlatArray e)

/-- Normalize raw `birdDet` calls in the target using the certificate-chain simproc. -/
macro "eval_bird_det" : tactic => `(tactic| simp only [↓cert_bird_det])

/-- Normalize supported `Matrix.det` calls in the target, without rewriting raw `birdDet` calls. -/
macro "eval_det" : tactic => `(tactic| simp only [↓cert_matrix_det])

/-- Compatibility wrapper around the determinant-normalization simprocs. -/
syntax "cert_bird_det" : tactic
elab_rules : tactic
  | `(tactic| cert_bird_det) => do
    evalTacticSeq
      (← `(tacticSeq|
        eval_bird_det
        try norm_num
        try ring))

end
