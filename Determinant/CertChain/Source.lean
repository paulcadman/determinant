module

public import Determinant.CertChain.Cert
public import Determinant.Correctness.Theorem

/-!
# Determinant sources for the certificate-chain frontend

The tactic frontend is organized as a small source pipeline:

1. Recognize a supported determinant expression and reify it as a `DetSource`.
2. Normalize the corresponding `BirdDet.birdDet` expression with the
   certificate evaluator.
3. Compose any source bridge proof with the Bird normalization proof.

Supported sources in this module are:

* direct `BirdDet.birdDet n A`;
* `Matrix.det (BirdDet.ofFlatArray (m := n) (n := n) A hA)`.

Elaborated Mathlib matrix notation support for `Matrix.det !![...]` lives in
`Determinant.CertChain.MatrixNotationSource`.
-/

open Lean Meta Simp
open Qq
open Cert

public meta section

/-- A determinant expression reified into the common Bird determinant surface. -/
structure DetSource where
  /-- The determinant expression currently being simplified. -/
  original : Expr
  /-- The corresponding `BirdDet.birdDet n A` expression. -/
  bird : Expr
  /-- A proof `original = bird`, absent when `original` already is `bird`. -/
  bridge? : Option Expr
  /-- Parsed data needed by the certificate evaluator. -/
  info : Meta.BirdDetInfo

/-- Normalize an already reified Bird determinant. -/
def normalizeBirdDetInfo (info : Meta.BirdDetInfo) : MetaM Simp.Result := do
  let ctx := Ctx.ofBirdDetInfo info
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/-- Normalize a `BirdDet.birdDet` expression with the certificate-chain evaluator. -/
def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  normalizeBirdDetInfo (← Meta.reifyBirdDet e)

namespace DetSource

/--
Normalize the source by normalizing its `bird` expression and composing the
optional source bridge proof.
-/
def normalize (src : DetSource) : MetaM Simp.Result := do
  let birdNorm ← normalizeBirdDetInfo src.info
  match src.bridge? with
  | none => pure birdNorm
  | some h =>
      ({expr := src.bird, proof? := some h} : Simp.Result).mkEqTrans birdNorm

end DetSource

/--
Construct a determinant source from a checked flat-array matrix under
`Matrix.det`.

When `matrixEq?` is present, it proves that the original matrix expression is
equal to the checked flat-array matrix. This is used by the matrix notation
source, whose elaborated matrix has Mathlib's vector-based representation.
-/
def sourceFromFlatArrayDetInput
    {u : Level} {α : Q(Type u)}
    (original detFn flatMatrix : Expr)
    (ringInst : Q(CommRing $α))
    (n : Q(Nat))
    (array : Q(Array $α))
    (sizeProof : Q(Array.size $array = $n * $n))
    (matrixEq? : Option Expr) :
    MetaM DetSource := do
  let birdExpr : Q($α) := q(@BirdDet.birdDet $α $ringInst $n $array)
  let flatDetExpr := mkApp detFn flatMatrix
  let flatBridge ← mkExpectedTypeHint
    (← mkAppOptM ``BirdDet.det_ofFlatArray_eq_birdDet_square
      #[some α, some ringInst, some n, some array, some sizeProof])
    (← mkEq flatDetExpr birdExpr)
  let bridge ←
    match matrixEq? with
    | none => pure flatBridge
    | some matrixEq => do
        let detCongr ← mkCongrArg detFn matrixEq
        mkExpectedTypeHint (← mkEqTrans detCongr flatBridge) (← mkEq original birdExpr)
  let bridge ← mkExpectedTypeHint bridge (← mkEq original birdExpr)
  let info ← Meta.reifyBirdDet birdExpr
  return {
    original
    bird := birdExpr
    bridge? := some bridge
    info
  }

/-- Recognize a direct `BirdDet.birdDet` expression as a determinant source. -/
def sourceOfBirdDet? (e : Expr) : MetaM (Option DetSource) := do
  let e ← instantiateMVars e
  unless e.getAppFn.isConstOf ``BirdDet.birdDet do
    return none
  let info ← Meta.reifyBirdDet e
  return some {
    original := e
    bird := e
    bridge? := none
    info
  }

/--
Recognize `Matrix.det (BirdDet.ofFlatArray (m := n) (n := n) A hA)` as a
determinant source.

This recognizer returns `none` for unrelated `Matrix.det` expressions. Once an
`ofFlatArray` matrix is recognized, malformed square dimensions or size proofs
are reported as errors instead of being swallowed.
-/
def sourceOfDetOfFlatArray? (e : Expr) : MetaM (Option DetSource) := do
  let e ← instantiateMVars e
  unless e.getAppFn.isConstOf ``Matrix.det do
    return none
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrix := e
    | return none
  unless matrix.getAppFn.isConstOf ``BirdDet.ofFlatArray do
    return none
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  match_expr matrix with
  | BirdDet.ofFlatArray _ rowsExpr colsExpr arrayExpr sizeProof => do
      let some rowsExpr ← checkTypeQ rowsExpr q(Nat)
        | throwError "expected row dimension to have type `Nat`, got{indentExpr rowsExpr}"
      let some colsExpr ← checkTypeQ colsExpr q(Nat)
        | throwError "expected column dimension to have type `Nat`, got{indentExpr colsExpr}"
      unless ← isDefEq rowsExpr colsExpr do
        throwError "expected square `ofFlatArray` under `Matrix.det`"
      let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
        | throwError "expected flat array to have type{indentExpr q(Array $α)}"
      let expectedSizeType : Q(Prop) := q(Array.size $arrayExpr = $rowsExpr * $rowsExpr)
      let sizeProof ← mkExpectedTypeHint sizeProof expectedSizeType
      let src ← sourceFromFlatArrayDetInput e e.appFn! matrix detRingInst rowsExpr arrayExpr sizeProof none
      return some src
  | _ =>
      throwError "expected determinant of square `BirdDet.ofFlatArray`, got{indentExpr matrix}"

end
