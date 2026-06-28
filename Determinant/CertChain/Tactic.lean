module

public import Determinant.CertChain.Cert
public import Determinant.Correctness.Theorem
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tactic frontend for the certificate-chain determinant evaluator

This module exposes the certificate-chain evaluator as simplification
procedures for determinant expressions backed by literal matrices.

The `BirdDet.birdDet` simproc reifies a determinant call, constructs a
proof-producing normalization certificate with `Cert.certBirdDet`, then returns
the normalized expression and proof to the simplifier.

For Mathlib determinants, the Matrix simproc recognizes checked square
flat-array matrices and ordinary `!![...]` matrix notation. It rewrites these
to the corresponding `BirdDet.birdDet` call using the correctness bridge, and
then runs the same certificate-chain normalizer.

The `eval_det` tactic is a small frontend for running both simprocs:

```lean
by
  eval_det
```

The evaluator is intentionally limited to literal matrix forms that can be
reified as a flat array accepted by `Meta.reifyBirdDet`.
-/

open Lean Meta Elab Tactic Simp
open Qq
open Cert

public meta section

/--
Recognize a vector literal after elaboration.

Mathlib's `![...]`/`!![...]` notation elaborates rows and the outer row vector as
nested `Matrix.vecCons ... Matrix.vecEmpty` terms. This returns the elements in
left-to-right order when `e` has exactly that elaborated shape.
-/
partial def matrixVecLiteral? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← instantiateMVars e
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``Matrix.vecEmpty then
    return some #[]
  else if e.getAppFn.isConstOf ``Matrix.vecCons then
    unless args.size == 4 do
      return none
    let some tail ← matrixVecLiteral? args[3]!
      | return none
    return #[args[2]!] ++ tail
  else
    return none

/--
Recognize the outer `Matrix.of` wrapper used by elaborated `!![...]` notation.

For a matrix literal, the matrix argument seen by the determinant simproc is a
function-like coercion of `Matrix.of` applied to the vector of row functions.
When that exact shape is present, this returns the row-vector expression.
-/
def matrixOfRows? (matrix : Expr) : Option Expr := Id.run do
  let args := matrix.getAppArgs
  if matrix.getAppFn.isConstOf ``DFunLike.coe && args.size == 6 &&
      args[4]!.getAppFn.isConstOf ``Matrix.of then
    some args[5]!
  else
    none

/-- Build a `List` expression from already-elaborated element expressions. -/
def mkListExpr (u : Level) (α : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (init := mkApp (mkConst ``List.nil [u]) α) fun x acc =>
    mkAppN (mkConst ``List.cons [u]) #[α, x, acc]

/-- Build an `Array` expression from already-elaborated element expressions. -/
def mkArrayExpr (u : Level) (α : Expr) (xs : Array Expr) : Expr :=
  mkAppN (mkConst ``Array.mk [u]) #[α, mkListExpr u α xs]

/-- Construct the expression `Fin n`. -/
def mkFinType (n : Nat) : Expr :=
  mkApp (mkConst ``Fin) (mkNatLit n)

/-- Construct the canonical zero element of `Fin n`, when `n` is known to be positive. -/
def mkFinZero (n : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some (mkFinType n), some (mkNatLit 0), none]

/-- Construct `Fin.succ i`, viewed as an element of `Fin (n + 1)`. -/
def mkFinSucc (n : Nat) (i : Expr) : MetaM Expr :=
  mkAppOptM ``Fin.succ #[some (mkNatLit n), some i]

/--
Build a proof by recursively case-splitting an index of type `Fin remaining`.

`targetFor` gives the proposition to prove for the current index expression.
`proofFor` is called at concrete leaves, where the index has reduced to a chain
of `Fin.succ` applications over `0`; these are precisely the cases where matrix
literal entries reduce by `rfl`.
-/
partial def mkFinCasesProof (remaining offset : Nat) (i : Expr)
    (targetFor : Expr → MetaM Expr)
    (proofFor : Nat → Expr → MetaM Expr) : MetaM Expr := do
  match remaining with
  | 0 =>
      mkAppOptM ``Fin.elim0 #[some (← targetFor i), some i]
  | k + 1 =>
      let finTy := mkFinType (k + 1)
      let motive ← withLocalDeclD `x finTy fun x => do
        mkLambdaFVars #[x] (← targetFor x)
      let zero ← mkFinZero (k + 1)
      let zeroProof ← proofFor offset zero
      let succProof ← withLocalDeclD `i (mkFinType k) fun i => do
        let body ← mkFinCasesProof k (offset + 1) i
          (fun i => do targetFor (← mkFinSucc k i))
          (fun idx i => do proofFor idx (← mkFinSucc k i))
        mkLambdaFVars #[i] body
      mkAppOptM ``Fin.cases #[some (mkNatLit k), some motive, some zeroProof, some succProof, some i]

/--
Build a proof of `∀ i : Fin n, targetFor i` by applying `mkFinCasesProof` to
the bound variable.
-/
def mkForallFinCasesProof (n : Nat)
    (targetFor : Expr → MetaM Expr)
    (proofFor : Nat → Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `i (mkFinType n) fun i => do
    let body ← mkFinCasesProof n 0 i targetFor proofFor
    mkLambdaFVars #[i] body

/--
Prove that an elaborated `!![...]` matrix equals the corresponding
`BirdDet.ofFlatArray` matrix.

This deliberately avoids asking Lean for a whole-matrix definitional equality
proof, which is slow for larger literals. Instead it builds a `Matrix.ext` proof
and splits both `Fin n` indices into concrete cases; each cell equality is then
checked by `rfl`.
-/
def mkMatrixLiteralEqProof (dimension : Nat) (indexType α matrix ofFlatMatrix : Expr) :
    MetaM Expr := do
  let cellTarget (i j : Expr) : MetaM Expr :=
    mkEq (mkApp2 matrix i j) (mkApp2 ofFlatMatrix i j)
  let cellProof (i j : Expr) : MetaM Expr := do
    let lhs := mkApp2 matrix i j
    mkExpectedTypeHint (← mkEqRefl lhs) (← cellTarget i j)
  let rowTarget (i : Expr) : MetaM Expr :=
    withLocalDeclD `j indexType fun j => do
      mkForallFVars #[j] (← cellTarget i j)
  let rowProof ← mkForallFinCasesProof dimension rowTarget fun _ i =>
    mkForallFinCasesProof dimension (cellTarget i) fun _ j =>
      cellProof i j
  let proof ← mkAppOptM ``Matrix.ext #[some indexType, some indexType, some α,
    some matrix, some ofFlatMatrix, some rowProof]
  mkExpectedTypeHint proof (← mkEq matrix ofFlatMatrix)

def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let info ← Meta.reifyBirdDet e
  let ctx := Ctx.ofBirdDetInfo info
  let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/--
Normalize square specializations of the checked rectangular flat-array
constructor under `Matrix.det`.

Size proofs written as `rfl` may elaborate with type `A.size = A.size`; for
literal arrays, that is definitionally equal to `A.size = n * n` only after
reducing the literal size. The simproc therefore checks this proof at default
transparency before passing it to the bridge theorem.
-/
def normalizeDetOfFlatArray (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrix := e
    | throwError "expected `Matrix.det`, got{indentExpr e}"
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  match_expr matrix with
  | BirdDet.ofFlatArray _ rowsExpr colsExpr arrayExpr sizeProof => do
      let some rowsExpr ← checkTypeQ rowsExpr q(Nat)
        | throwError "expected row dimension to have type `Nat`, got{indentExpr rowsExpr}"
      let some colsExpr ← checkTypeQ colsExpr q(Nat)
        | throwError "expected column dimension to have type `Nat`, got{indentExpr colsExpr}"
      unless ← isDefEq rowsExpr colsExpr do
        throwError
          "expected square `BirdDet.ofFlatArray`, got dimensions{indentExpr rowsExpr}{indentExpr colsExpr}"
      let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
        | throwError "expected flat array to have type{indentExpr q(Array $α)}"
      let expectedSizeType : Q(Prop) := q(Array.size $arrayExpr = $rowsExpr * $rowsExpr)
      let some sizeProof ← withDefault <| checkTypeQ sizeProof expectedSizeType
        | throwError
            "expected square size proof to have type{indentExpr expectedSizeType}\nactual type:{indentExpr (← inferType sizeProof)}"
      let sizeProof ← mkExpectedTypeHint sizeProof expectedSizeType
      let birdExpr : Q($α) := q(@BirdDet.birdDet $α $detRingInst $rowsExpr $arrayExpr)
      let bridge ← mkAppOptM ``BirdDet.det_ofFlatArray_eq_birdDet_square
        #[some α, some detRingInst, some rowsExpr, some arrayExpr, some sizeProof]
      let birdNorm ← normalizeBirdDet birdExpr
      ({expr := birdExpr, proof? := some bridge} : Simp.Result).mkEqTrans birdNorm
  | _ =>
      throwError "expected determinant of square `BirdDet.ofFlatArray`, got{indentExpr matrix}"

/--
Normalize `Matrix.det !![...]` when the elaborated matrix literal is square over
`Fin n`.

The literal entries are extracted row-major from the nested `Matrix.vecCons`
representation, assembled into a flat array, and connected to
`BirdDet.ofFlatArray` using `mkMatrixLiteralEqProof`. The existing
`BirdDet.det_ofFlatArray_eq_birdDet_square` bridge then hands the problem to
`normalizeBirdDet`.
-/
def normalizeDetOfMatrixLiteral (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det indexType _ _ _ detRingInst matrix := e
    | throwError "expected `Matrix.det`, got{indentExpr e}"
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  let_expr Fin dimensionExpr := indexType
    | throwError "expected determinant index type `Fin n`, got{indentExpr indexType}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionExpr ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected determinant dimension to have type `Nat`, got{indentExpr dimensionExpr}"
  let some dimension ← getNatValue? dimensionExpr
    | throwError "expected determinant dimension to be a `Nat` literal, got{indentExpr dimensionExpr}"
  let some rowsExpr := matrixOfRows? matrix
    | throwError "expected determinant of a `Matrix.of` literal, got{indentExpr matrix}"
  let some rowExprs ← matrixVecLiteral? rowsExpr
    | throwError "expected matrix rows to be a `Matrix.vecCons` literal, got{indentExpr rowsExpr}"
  unless rowExprs.size == dimension do
    throwError "matrix row count mismatch: literal has {rowExprs.size} rows, determinant has {dimension}"
  let mut entries : Array Q($α) := #[]
  for rowExpr in rowExprs do
    let some rowEntries ← matrixVecLiteral? rowExpr
      | throwError "expected matrix row to be a `Matrix.vecCons` literal, got{indentExpr rowExpr}"
    unless rowEntries.size == dimension do
      throwError "matrix column count mismatch: row has {rowEntries.size} entries, expected {dimension}"
    for entry in rowEntries do
      let some entry ← checkTypeQ entry α
        | throwError "expected matrix entry to have type{indentExpr α}"
      entries := entries.push entry
  let arrayExprRaw := mkArrayExpr u α entries
  let some arrayExpr ← checkTypeQ arrayExprRaw q(Array $α)
    | throwError "failed to construct flat array expression of type{indentExpr q(Array $α)}"
  let sizeExpr := mkAppN (mkConst ``Array.size [u]) #[α, arrayExpr]
  let sizeTarget ← mkEq sizeExpr (mkNatLit (dimension * dimension))
  let sizeProof ← mkExpectedTypeHint
    (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) (mkNatLit (dimension * dimension)))
    sizeTarget
  let ofFlatMatrix :=
    mkAppN (mkConst ``BirdDet.ofFlatArray [u]) #[
      α, dimensionExpr, dimensionExpr, arrayExpr, sizeProof]
  let matrixType := mkAppN (mkConst ``Matrix [.zero, .zero, u]) #[indexType, indexType, α]
  let matrixForProof ← mkExpectedTypeHint matrix matrixType
  let ofFlatMatrixForProof ← mkExpectedTypeHint ofFlatMatrix matrixType
  let matrixEqProof ←
    mkMatrixLiteralEqProof dimension indexType α matrixForProof ofFlatMatrixForProof
  let birdExpr : Q($α) := q(@BirdDet.birdDet $α $detRingInst $dimensionExpr $arrayExpr)
  let detFn := e.appFn!
  let detCongr ← mkCongrArg detFn matrixEqProof
  let flatBridge ← mkExpectedTypeHint
    (← mkAppOptM ``BirdDet.det_ofFlatArray_eq_birdDet_square
      #[some α, some detRingInst, some dimensionExpr, some arrayExpr, some sizeProof])
    (← mkEq (mkApp detFn ofFlatMatrixForProof) birdExpr)
  let bridge ← mkExpectedTypeHint (← mkEqTrans detCongr flatBridge) (← mkEq e birdExpr)
  let birdNorm ← normalizeBirdDet birdExpr
  ({expr := birdExpr, proof? := some bridge} : Simp.Result).mkEqTrans birdNorm

/--
Try all determinant normalizers supported by `norm_matrix_det`.

The flat-array form is tried first to preserve the original fast path. If that
does not match, the elaborated matrix-literal path handles normal `!![...]`
notation.
-/
def normalizeDet? (e : Expr) : MetaM (Option Simp.Result) := do
  match ← observing? (normalizeDetOfFlatArray e) with
  | some result => return some result
  | none =>
      match ← observing? (normalizeDetOfMatrixLiteral e) with
      | some result => return some result
      | none => return none

/--
Normalize literal `BirdDet.birdDet` calls using the certificate-chain evaluator.
-/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/--
Normalize supported `Matrix.det` calls by rewriting through `BirdDet.birdDet`.

The supported matrix forms are the checked flat-array constructor
`BirdDet.ofFlatArray` and concrete `!![...]` literals elaborated as
`Matrix.of` over `Matrix.vecCons` rows.
-/
simproc_decl norm_matrix_det (Matrix.det _) := fun e => do
  match ← normalizeDet? e with
  | some result => return .done result
  | none => return .continue

/-- Normalize supported determinant calls in the target using the certificate-chain simprocs. -/
macro "eval_det" : tactic => `(tactic| simp only [norm_det, norm_matrix_det])

end
