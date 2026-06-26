module

public meta import Determinant.CertChain.Meta
public meta import Determinant.CertChain.Cert

import Lean
import Mathlib.Algebra.Ring.Int.Defs
import Qq

namespace Tests

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring
open Cert
open BirdDet
open Meta

@[irreducible] def wrappedIntCommRing : CommRing ℤ := inferInstance

meta def assertDefEq (actual expected : Expr) : MetaM Unit := do
  unless (← isDefEq actual expected) do
    throwError m!"expected{indentExpr expected}\ngot{indentExpr actual}"

meta def assertLevelDefEq (actual expected : Level) : MetaM Unit := do
  unless (← isLevelDefEq actual expected) do
    throwError m!"expected level {expected}, got {actual}"

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
  assertLevelDefEq info.u .zero
  assertDefEq info.α q(ℤ)
  assertDefEq info.rα q(Int.instCommRing)
  unless info.dimension == 2 do
    throwError m!"expected dimension 2, got {info.dimension}"
  assertDefEq info.arrayExpr q(#[1, 2, 3, 4] : Array ℤ)
  unless info.arrayEntries.size == 4 do
    throwError m!"expected 4 array entries, got {info.arrayEntries.size}"
  assertDefEq info.arrayEntries[0]! q((1 : ℤ))
  assertDefEq info.arrayEntries[1]! q((2 : ℤ))
  assertDefEq info.arrayEntries[2]! q((3 : ℤ))
  assertDefEq info.arrayEntries[3]! q((4 : ℤ))

-- The Bird-side instance has to be the exact instance from the reified term.
-- Rebuilding Bird terms with the ring-computation instance can lose
-- definitional equality with the original goal.
run_meta do
  let e0 : Q(ℤ) :=
    q(letI : CommRing ℤ := wrappedIntCommRing; birdDet 1 (#[1] : Array ℤ))
  let e ← zetaReduce e0
  let info ← reifyBirdDet e
  let cα ← Common.mkCache q(Int.instCommSemiring)
  let some rα := cα.rα | unreachable!
  let some birdInst ← checkTypeQ info.rα q(CommRing ℤ) | unreachable!
  let some ringInst ← checkTypeQ rα q(CommRing ℤ) | unreachable!
  let n := info.data.dimensionExpr
  let some A ← checkTypeQ info.data.arrayExpr q(Array ℤ) | unreachable!
  let withBirdInst0 : Q(ℤ) :=
    q(letI : CommRing ℤ := $birdInst; birdDet $n $A)
  let withRingInst0 : Q(ℤ) :=
    q(letI : CommRing ℤ := $ringInst; birdDet $n $A)
  let withBirdInst ← zetaReduce withBirdInst0
  let withRingInst ← zetaReduce withRingInst0
  assertDefEq withBirdInst e
  if ← isDefEq withRingInst e then
    throwError "expected ring-cache instance not to be definitionally equal to the Bird instance"

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

/-- error: matrix size mismatch: array has 3 entries, expected 4 -/
#guard_msgs in 
run_meta do
  let e : Q(ℤ) := q(birdDet 2 (Array.mk [1,2,3]))
  reifyBirdDet e

-- Test zeroProdCert
run_meta do
  let rα : Q(CommRing ℤ) := q(Int.instCommRing)
  let cα : Common.Cache (commSemiringOfCommRing rα) :=
    { rα := some rα, dsα := none, czα := none }
  let rc := ringCompute cα
  let x : Q(ℤ) := q((5 : ℤ))
  let z : Q(ℤ) := q((3 : ℤ) - 3)
  let c ← AtomM.run .reducible do
    let resZ ← Common.eval rcℕ rc cα z
    unless isZeroVal resZ.val do
      throwError "zeroProdCert test: the right factor does not normalize to zero"
    zeroProdCert x (toCert resZ)
  Meta.check c.proof
  assertDefEq c.norm q((0 : ℤ))

/-- Construct a `Ctx` for an integer matrix -/
meta def ctxℤ
  (dimension : Nat)
  (array : Q(Array ℤ))
  : MetaM (Ctx q(Int.instCommRing)) := do
  let some rawEntries ← arrayLiteral? array
    | throwError "Ctxℤ: A is not an array literal"
  let arrayEntries ← rawEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry q(ℤ)
      | throwError "Ctxℤ: array entry does not have type ℤ"
    return entry
  let rα : Q(CommRing ℤ) := q(Int.instCommRing)
  let cα : Common.Cache (commSemiringOfCommRing q(Int.instCommRing)) := {
    rα := some rα
    dsα := none
    czα := none
  }
  let rc := ringCompute cα
  let info : BirdDetData q(Int.instCommRing) := {
    dimension
    dimensionExpr := mkNatLitQ dimension
    arrayExpr := array
    arrayEntries
  }
  return {cα, rc, info}

meta def withCtxℤ
  {α : Type}
  (n : Nat)
  (A : Q(Array ℤ))
  (action : CertM q(Int.instCommRing) α)
  : MetaM α := do
    let ctx ← ctxℤ n A
    action.run' {} |>.run ctx |>.run .reducible

meta def assertCertNorm (c : Cert q(Int.instCommRing)) (expected : Expr) : MetaM Unit := do
  Meta.check c.proof
  assertDefEq c.norm expected

-- Check that the proof returned by `certEntry` is valid
run_meta withCtxℤ 2 q(#[1, 2, 2 + 3, 4]) do
  let ce ← certEntry 1 0
  assertCertNorm ce q((5 : ℤ))

-- A zero entry is flagged `isZero`
run_meta withCtxℤ 2 q(#[1, 2, 2 - 2, 4]) do
  let ce ← certEntry 1 0
  Meta.check ce.proof
  unless ce.isZero do
    throwError "isZero flag not set"
  unless ← isDefEq ce.norm q((0 : ℤ)) do
    throwError "zero entry norm is not definitionally zero"

-- 2x2: iter 2 #[1, 2, 3, 4] 1 F_0 0 0 = -det A = -(1*4 - 2*3) = 2
run_meta withCtxℤ 2 q(#[1, 2, 3, 4]) do
  let cert ← certIter 1 0 0
  assertCertNorm cert q((2 : ℤ))

-- 3x3: iter 2 #[1, 0, 0, 0, 1, 0, 0, 0, 1] 2 F_0 0 0 = det A = 1
run_meta withCtxℤ 3 q(#[1, 0, 0, 0, 1, 0, 0, 0, 1]) do
  assertCertNorm (← certIter 2 0 0) q((1 : ℤ))
  let c01 ← certIter 2 0 1
  assertCertNorm c01 q((0 : ℤ))
  unless c01.isZero do
    throwError "expected iter 2 0 1 to be marked zero"

-- 0x0 determinant is 1
run_meta withCtxℤ 0 q(#[]) do
  assertCertNorm (← certBirdDet) q((1 : ℤ))

-- 1x1 determinant is the single entry
run_meta withCtxℤ 1 q(#[5]) do
  assertCertNorm (← certBirdDet) q((5 : ℤ))

-- 2x2 determinant: 1 * 4 - 2 * 3 = -2
run_meta withCtxℤ 2 q(#[1, 2, 3, 4]) do
  assertCertNorm (← certBirdDet) q((-2 : ℤ))

-- Singular 2x2 matrix follows zero paths and certifies determinant 0
run_meta withCtxℤ 2 q(#[1, 2, 2, 4]) do
  let c ← certBirdDet
  assertCertNorm c q((0 : ℤ))
  unless c.isZero do
    throwError "expected singular 2x2 determinant to be marked zero"

-- 3x3 identity determinant is 1
run_meta withCtxℤ 3 q(#[1, 0, 0, 0, 1, 0, 0, 0, 1]) do
  assertCertNorm (← certBirdDet) q((1 : ℤ))

-- 3x3 diagonal determinant: 2 * 3 * 4 = 24
run_meta withCtxℤ 3 q(#[2, 0, 0, 0, 3, 0, 0, 0, 4]) do
  assertCertNorm (← certBirdDet) q((24 : ℤ))

-- 3x3 upper triangular determinant ignores off-diagonal entries
run_meta withCtxℤ 3 q(#[2, 5, 7, 0, 3, 11, 0, 0, 4]) do
  assertCertNorm (← certBirdDet) q((24 : ℤ))

end Tests
