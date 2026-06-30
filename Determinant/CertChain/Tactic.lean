module

public import Determinant.CertChain.Cert
public import Determinant.Correctness.Theorem

/-!
# Tactic frontend for the certificate-chain determinant evaluator

Supported sources are:

* `BirdDet.birdDet n A`;
* `Matrix.det (Matrix.ofFlatArray (m := n) (n := n) A hA)`.
-/

open Lean Meta Elab Tactic Simp
open Qq
open Cert

public meta section

/-- Normalize a direct `BirdDet.birdDet` expression. -/
def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let info ← Meta.reifyBirdDet e
  let ctx := Ctx.ofBirdDetInfo info
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/--
Recognize and normalize `Matrix.det (Matrix.ofFlatArray (m := n) (n := n) A hA)`.

This is deliberately the only `Matrix.det` frontend path here; Mathlib matrix
notation elaborates to a different internal representation and is not handled
by this small recognizer.
-/
def normalizeDetOfFlatArray? (e : Expr) : MetaM (Option Simp.Result) := do
  let e ← instantiateMVars e
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrix := e
    | return none
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  let_expr Matrix.ofFlatArray _ rowsExpr colsExpr arrayExpr sizeProof := matrix
    | return none
  let some rowsExpr ← checkTypeQ rowsExpr q(Nat)
    | throwError "expected row dimension to have type `Nat`, got{indentExpr rowsExpr}"
  let some colsExpr ← checkTypeQ colsExpr q(Nat)
    | throwError "expected column dimension to have type `Nat`, got{indentExpr colsExpr}"
  unless ← isDefEq rowsExpr colsExpr do
    throwError "expected square `ofFlatArray` under `Matrix.det`"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected flat array to have type{indentExpr q(Array $α)}"
  let expectedSizeType := q(Array.size $arrayExpr = $rowsExpr * $rowsExpr)
  let sizeProof ← mkExpectedTypeHint sizeProof expectedSizeType
  let some sizeProof ← checkTypeQ sizeProof expectedSizeType
    | throwError "expected size proof to have type{indentExpr expectedSizeType}"
  let some lhs ← checkTypeQ e α
    | throwError "expected determinant expression to have type{indentExpr α}"
  let birdExpr := q(@BirdDet.birdDet $α $detRingInst $rowsExpr $arrayExpr)
  let flatDet := q(Matrix.det (Matrix.ofFlatArray (m := $rowsExpr) (n := $rowsExpr) $arrayExpr $sizeProof))
  have : $lhs =Q $flatDet := ⟨⟩
  let bridge : Q($lhs = $birdExpr) :=
    q(@BirdDet.det_ofFlatArray_eq_birdDet_square
      $α $detRingInst $rowsExpr $arrayExpr $sizeProof)
  let birdNorm ← normalizeBirdDet birdExpr
  let bridgeResult : Simp.Result := {
    expr := birdExpr
    proof? := some bridge
  }
  let result ← bridgeResult.mkEqTrans birdNorm
  return some result


/-- Normalize literal `BirdDet.birdDet` calls using the certificate-chain evaluator. -/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/-- Normalize supported `Matrix.det` calls by rewriting through `BirdDet.birdDet`. -/
simproc_decl norm_matrix_det (Matrix.det _) := fun e => do
  match ← normalizeDetOfFlatArray? e with
  | some result => return .done result
  | none => return .continue

/-- Normalize supported determinant calls in the target using the certificate-chain simprocs. -/
macro "eval_det" : tactic => `(tactic| simp only [norm_det, norm_matrix_det])

end
