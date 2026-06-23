module

public meta import Determinant.CertChain.Meta
public import Determinant.CertChain.Cert
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Lean.Meta.Simp

open Lean Meta Elab Tactic Simp
open Qq
open Mathlib.Tactic.Ring
open Cert

public meta section

def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let info ← Meta.reifyBirdDet e
  let ctx := Ctx.ofBirdDetInfo info
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.eq.rhs, proof? := some detNorm.eq.proof}

/--
Normalize a literal `birdDet` call using the certificate-chain evaluator.
-/
simproc ↓ cert_bird_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/-- Normalize `birdDet` calls in the target using the certificate-chain simproc. -/
macro "eval_bird_det" : tactic => `(tactic| simp only [↓cert_bird_det])

end
