module

public import Determinant.CertChain.Meta
public import Determinant.CertChain.Cert
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
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/--
Normalize a literal `birdDet` call using the certificate-chain evaluator.
-/
simproc ↓ cert_bird_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/-- Normalize `birdDet` calls in the target using the certificate-chain simproc. -/
macro "eval_bird_det" : tactic => `(tactic| simp only [↓cert_bird_det])

/-- Compatibility wrapper around the `cert_bird_det` simproc. -/
syntax "cert_bird_det" : tactic
elab_rules : tactic
  | `(tactic| cert_bird_det) => do
    evalTacticSeq
      (← `(tacticSeq|
        eval_bird_det
        try norm_num
        try ring))

end
