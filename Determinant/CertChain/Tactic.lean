module

public import Determinant.CertChain.Cert

/-!
# Tactic frontend for the certificate-chain determinant evaluator

This module exposes the certificate-chain evaluator as a simplification
procedure for literal `BirdDet.birdDet` calls.

The simproc reifies a determinant call, constructs a proof-producing
normalization certificate with `Cert.certBirdDet`, then returns the normalized
expression and proof to the simplifier. The `eval_det` tactic is a small
frontend for running just this simproc:

```lean
by
  eval_det
```

The evaluator is intentionally limited to the literal flat-array form accepted
by `Meta.reifyBirdDet`.
-/

open Lean Meta Elab Tactic Simp
open Cert

public meta section

def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let info ← Meta.reifyBirdDet e
  let ctx := Ctx.ofBirdDetInfo info
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/--
Normalize a literal `birdDet` call using the certificate-chain evaluator.
-/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/-- Normalize `birdDet` calls in the target using the certificate-chain simproc. -/
macro "eval_det" : tactic => `(tactic| simp only [norm_det])

end
