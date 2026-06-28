module

public import Determinant.CertChain.LegacyMatrixLiteral

/-!
# Tactic frontend for the certificate-chain determinant evaluator

The frontend has three phases:

1. Reify a supported determinant source into a common `DetSource`.
2. Normalize the corresponding `BirdDet.birdDet` expression using the
   certificate evaluator.
3. Compose the optional source bridge proof with the Bird normalization proof.

Supported sources are:

* `BirdDet.birdDet n A`;
* `Matrix.det (BirdDet.ofFlatArray (m := n) (n := n) A hA)`;
* legacy already-elaborated `Matrix.det !![...]` literals.

The legacy `!![...]` path is a compatibility fallback, not the preferred fast
frontend. Its parser and `Matrix.ext` proof construction are isolated in
`Determinant.CertChain.LegacyMatrixLiteral`.
-/

open Lean Meta Elab Tactic Simp

public meta section

/-- Recognize any determinant expression supported by the certificate frontend. -/
def sourceOfExpr? (e : Expr) : MetaM (Option DetSource) := do
  if let some src ← sourceOfBirdDet? e then
    return some src
  if let some src ← sourceOfDetOfFlatArray? e then
    return some src
  if let some src ← LegacyMatrixLiteral.sourceOfMatrixLiteral? e then
    return some src
  return none

/-- Recognize a supported determinant source or report a user-facing error. -/
def sourceOfExpr! (e : Expr) : MetaM DetSource := do
  match ← sourceOfExpr? e with
  | some src => return src
  | none =>
      throwError
        "expected `BirdDet.birdDet ...`, `Matrix.det (BirdDet.ofFlatArray ...)`, \
        or a supported matrix literal; got{indentExpr e}"

/-- Normalize a supported determinant expression, if this frontend recognizes it. -/
def normalizeDetExpr? (e : Expr) : MetaM (Option Simp.Result) := do
  match ← sourceOfExpr? e with
  | none => return none
  | some src => return some (← src.normalize)

/-- Normalize literal `BirdDet.birdDet` calls using the certificate-chain evaluator. -/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  match ← normalizeDetExpr? e with
  | some result => return .done result
  | none => return .continue

/-- Normalize supported `Matrix.det` calls by rewriting through `BirdDet.birdDet`. -/
simproc_decl norm_matrix_det (Matrix.det _) := fun e => do
  match ← normalizeDetExpr? e with
  | some result => return .done result
  | none => return .continue

/-- Normalize supported determinant calls in the target using the certificate-chain simprocs. -/
macro "eval_det" : tactic => `(tactic| simp only [norm_det, norm_matrix_det])

end
