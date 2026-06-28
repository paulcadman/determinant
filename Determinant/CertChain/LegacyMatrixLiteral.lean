module

public import Determinant.CertChain.Source
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Legacy elaborated matrix literal support

This module provides compatibility support for already-elaborated Mathlib
`!![...]` matrix literals under `Matrix.det`.

This is not the preferred fast frontend path. The recognizer extracts entries
from elaborated `Matrix.of` / `Matrix.vecCons` / `Matrix.vecEmpty` terms,
constructs a checked flat array, and builds a `Matrix.ext` proof by
case-splitting both `Fin` indices. The resulting source is then normalized by
the common `DetSource` pipeline.
-/

open Lean Meta
open Qq

public meta section

namespace LegacyMatrixLiteral

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

/--
Recognize an already-elaborated `Matrix.det !![...]` literal as a determinant
source.
-/
def sourceOfMatrixLiteral? (e : Expr) : MetaM (Option DetSource) := do
  let e ← instantiateMVars e
  unless e.getAppFn.isConstOf ``Matrix.det do
    return none
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det indexType _ _ _ detRingInst matrix := e
    | return none
  let some rowsExpr := matrixOfRows? matrix
    | return none
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type{indentExpr q(CommRing $α)}"
  let_expr Fin dimensionExpr := indexType
    | throwError "expected determinant index type `Fin n`, got{indentExpr indexType}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionExpr ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected determinant dimension to have type `Nat`, got{indentExpr dimensionExpr}"
  let some dimension ← getNatValue? dimensionExpr
    | throwError "expected determinant dimension to be a `Nat` literal, got{indentExpr dimensionExpr}"
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
  let info ← Meta.reifyBirdDet birdExpr
  return some {
    original := e
    bird := birdExpr
    bridge? := some bridge
    info
  }

end LegacyMatrixLiteral

end
