module

public meta import Determinant.CertChain.Tactic

import Lean
import Qq

namespace CertChain

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring

def assertDefEq (actual expected : Expr) : MetaM Unit := do
  unless (← isDefEq actual expected) do
    throwError m!"expected{indentExpr expected}\ngot{indentExpr actual}"

def assertLevelDefEq (actual expected : Level) : MetaM Unit := do
  unless (← isLevelDefEq actual expected) do
    throwError m!"expected level {expected}, got {actual}"

-- Test destructMul?
run_meta do
  let m := q((2 : ℤ) * 3)
  let some app := destructMul? m
    | throwError m!"{m} is not a multiplication"
  let recombined := mkApp2 app.partialApp app.x app.y
  let value ← reduce recombined
  assertDefEq value q((6 : ℤ))

-- Test destructAdd?
run_meta do
  let m := q((2 : ℤ) + 3)
  let some app := destructAdd? m
    | throwError m!"{m} is not an addition"
  let recombined := mkApp2 app.partialApp app.x app.y
  let value ← reduce recombined
  assertDefEq value q((5 : ℤ))

-- Test destructNeg?
run_meta do
  let m := q(-(2 : ℤ))
  let some app := destructNeg? m
    | throwError m!"{m} is not a negation"
  let recombined := mkApp app.partialApp app.x
  let value ← reduce recombined
  assertDefEq value q((-2 : ℤ))

-- Test mkLtProof
run_meta do
  let expected : Q(Prop) := q(1 < (2 : Nat))
  let pf ← mkLtProof 1 2
  let actual ← inferType pf
  assertDefEq actual expected

-- Test mkNotLtProof
run_meta do
  let expected : Q(Prop) := q(¬ 2 < (1 : Nat))
  let pf ← mkNotLtProof 2 1
  let actual ← inferType pf
  assertDefEq actual expected

-- Test arrayLiteral?
run_meta do
  let arr : Q(Array ℤ) := q(#[1,2,3,4])
  let some elems ← arrayLiteral? arr | throwError m!"{arr} is not an array literal"
  unless elems.size == 4 do
    throwError m!"expected 4 array entries, got {elems.size}"
  assertDefEq elems[0]! q((1 : ℤ))
  assertDefEq elems[1]! q((2 : ℤ))
  assertDefEq elems[2]! q((3 : ℤ))
  assertDefEq elems[3]! q((4 : ℤ))

-- Test reifyBirdDet

run_meta do
  let e : Q(ℤ) := q(birdDet 2 #[1, 2, 3, 4])
  let info ← reifyBirdDet e
  assertLevelDefEq info.level .zero
  assertDefEq info.ringType q(ℤ)
  assertDefEq info.dimensionExpr q((2 : Nat))
  unless info.dimension == 2 do
    throwError m!"expected dimension 2, got {info.dimension}"
  assertDefEq info.arrayExpr q(#[1, 2, 3, 4] : Array ℤ)
  unless info.arrayEntries.size == 4 do
    throwError m!"expected 4 array entries, got {info.arrayEntries.size}"
  assertDefEq info.arrayEntries[0]! q((1 : ℤ))
  assertDefEq info.arrayEntries[1]! q((2 : ℤ))
  assertDefEq info.arrayEntries[2]! q((3 : ℤ))
  assertDefEq info.arrayEntries[3]! q((4 : ℤ))

/-- error: matrix size mismatch: array has 2 entries, expected 4 -/
#guard_msgs in
run_meta do
  let e : Q(ℤ) := q(birdDet 2 #[1, 2])
  reifyBirdDet e

/-- error: expected an application of `birdDet, got #[1, 2].getD 0 0 -/
#guard_msgs in 
run_meta do
  let e : Q(ℤ) := q(#[1, 2].getD 0 0)
  reifyBirdDet e

/-- error: expected the dimension to be a `Nat` literal, got Nat.zero -/
#guard_msgs in 
run_meta do
  let e : Q(ℤ) := q(birdDet .zero #[1, 2])
  reifyBirdDet e

/-- error: expected an array literal matrix, got { toList := [1, 2, 3] } -/
#guard_msgs in 
run_meta do
  let e : Q(ℤ) := q(birdDet 2 (Array.mk [1,2,3]))
  reifyBirdDet e

-- Test zeroProdCert

elab "zero_prod_close" : tactic => Elab.Tactic.withMainContext do
  let g ← Elab.Tactic.getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "zero_prod_close: expected an equality"
  let some ⟨mulP, x, z⟩  := destructMul? lhs
    | throwError "zero_prod_close: expected a product"
  let ⟨u, α, _⟩ ← inferTypeQ' lhs
  let sα : Q(CommSemiring $α) ← synthInstanceQ q(CommSemiring $α)
  let cα ← Common.mkCache sα
  let rc := ringCompute cα
  let proof ← AtomM.run .reducible do
    have z : Q($α) := z
    let resZ ← Common.eval rcℕ rc cα z
    unless isZeroVal resZ.val do
      throwError "zero_prod_close: the right factor does not normalize to zero"
    let c ← zeroProdCert mulP x (toCert resZ)
    pure c.proof
  g.assign proof
  Elab.Tactic.replaceMainGoal []

example (x y : ℤ) : x * (y - y) = 0 := by
  zero_prod_close

end Cert

-- structure EqProof where
--   proof : Expr
--   lhs : Expr
--   rhs : Expr
--
-- /-- Instantiate the lemma `name` and return `{proof, lhs, rhs}` -/
-- def applyEqLemma (name : Name) (u : Level) (args : Array Expr) : MetaM EqProof := do
--   let proof := mkAppN (mkConst name [u]) args
--   let some (_, lhs, rhs) := (← inferType proof).eq?
--     | throwError "applyEqLemms: {name} did not produce an equality"
--   return {proof, lhs, rhs}
--
