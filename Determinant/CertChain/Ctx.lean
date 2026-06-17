module

public import Determinant.CertChain.Bird
public import Determinant.CertChain.Meta
public import Mathlib.Tactic.Ring
public import Qq
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues

open Lean Meta Qq
open Mathlib.Tactic.Ring
open BirdDet

public meta section

variable
  {u : Level}
  {α : Q(Type u)}
  {sα : Q(CommSemiring $α)}

structure CtxOps {u : Level} (α : Q(Type u)) where
  getP : Q(Nat → Nat → $α)
  addP : Q($α → $α → $α)
  mulP : Q($α → $α → $α)
  negP : Q($α → $α)
  powP : Q($α → Nat → $α)
  one : Q($α)

namespace CtxOps

def birdCommSemiring {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(CommSemiring $α) :=
  mkAppN (mkConst ``CommRing.toCommSemiring [u]) #[α, birdRingInst]

def birdSemiring {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(Semiring $α) :=
  mkAppN (mkConst ``CommSemiring.toSemiring [u]) #[
    α, birdCommSemiring birdRingInst]

def birdRing {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(Ring $α) :=
  mkAppN (mkConst ``CommRing.toRing [u]) #[α, birdRingInst]

def birdDistrib {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(Distrib $α) :=
  mkAppN (mkConst ``instDistribOfSemiring [u]) #[α, birdSemiring birdRingInst]

def birdMonoid {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(Monoid $α) :=
  mkAppN (mkConst ``Semiring.toMonoid [u]) #[α, birdSemiring birdRingInst]

def birdAddGroupWithOne {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(AddGroupWithOne $α) :=
  mkAppN (mkConst ``Ring.toAddGroupWithOne [u]) #[α, birdRing birdRingInst]

def birdAddMonoidWithOne {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(AddMonoidWithOne $α) :=
  mkAppN (mkConst ``AddGroupWithOne.toAddMonoidWithOne [u]) #[
    α, birdAddGroupWithOne birdRingInst]

def birdNonUnitalCommRing {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(NonUnitalCommRing $α) :=
  mkAppN (mkConst ``CommRing.toNonUnitalCommRing [u]) #[α, birdRingInst]

def birdNonUnitalNonAssocCommRing {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(NonUnitalNonAssocCommRing $α) :=
  mkAppN (mkConst ``NonUnitalCommRing.toNonUnitalNonAssocCommRing [u]) #[
    α, birdNonUnitalCommRing birdRingInst]

def birdNonUnitalNonAssocRing {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q(NonUnitalNonAssocRing $α) :=
  mkAppN (mkConst ``NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing [u]) #[
    α, birdNonUnitalNonAssocCommRing birdRingInst]

def mkAddP {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q($α → $α → $α) :=
  let addInst : Q(Add $α) :=
    mkAppN (mkConst ``Distrib.toAdd [u]) #[α, birdDistrib birdRingInst]
  let hAddInst : Q(HAdd $α $α $α) :=
    mkAppN (mkConst ``instHAdd [u]) #[α, addInst]
  mkAppN (mkConst ``HAdd.hAdd [u, u, u]) #[α, α, α, hAddInst]

def mkMulP {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q($α → $α → $α) :=
  let mulInst : Q(Mul $α) :=
    mkAppN (mkConst ``Distrib.toMul [u]) #[α, birdDistrib birdRingInst]
  let hMulInst : Q(HMul $α $α $α) :=
    mkAppN (mkConst ``instHMul [u]) #[α, mulInst]
  mkAppN (mkConst ``HMul.hMul [u, u, u]) #[α, α, α, hMulInst]

def mkNegP {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q($α → $α) :=
  let mulZeroClass :=
    mkAppN (mkConst ``instMulZeroClassOfSemiring [u]) #[
      α, birdSemiring birdRingInst]
  let hasDistribNeg :=
    mkAppN (mkConst ``NonUnitalNonAssocRing.toHasDistribNeg [u]) #[
      α, birdNonUnitalNonAssocRing birdRingInst]
  let negZeroClass :=
    mkAppN (mkConst ``MulZeroClass.negZeroClass [u]) #[α, mulZeroClass, hasDistribNeg]
  let negInst : Q(Neg $α) :=
    mkAppN (mkConst ``NegZeroClass.toNeg [u]) #[α, negZeroClass]
  mkAppN (mkConst ``Neg.neg [u]) #[α, negInst]

def mkPowP {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q($α → Nat → $α) :=
  let powInst :=
    mkAppN (mkConst ``Monoid.toPow [u]) #[α, birdMonoid birdRingInst]
  let hPowInst : Q(HPow $α Nat $α) :=
    mkAppN (mkConst ``instHPow [u, 0]) #[α, q(Nat), powInst]
  mkAppN (mkConst ``HPow.hPow [u, 0, u]) #[α, q(Nat), α, hPowInst]

def mkOne {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) : Q($α) :=
  let oneInst :=
    mkAppN (mkConst ``AddMonoidWithOne.toOne [u]) #[
      α, birdAddMonoidWithOne birdRingInst]
  let ofNatOneInst :=
    mkAppN (mkConst ``One.toOfNat1 [u]) #[α, oneInst]
  mkAppN (mkConst ``OfNat.ofNat [u]) #[α, mkNatLit 1, ofNatOneInst]

def mkGetP {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) (dimensionExpr : Q(Nat)) (array : Q(Array $α)) :
    Q(Nat → Nat → $α) :=
  mkAppN (mkConst ``BirdDet.get [u]) #[α, birdRingInst, dimensionExpr, array]

def ofCommRing {u : Level} {α : Q(Type u)}
    (birdRingInst : Q(CommRing $α)) (dimensionExpr : Q(Nat)) (array : Q(Array $α)) :
    CtxOps α :=
  { getP := mkGetP birdRingInst dimensionExpr array
    addP := mkAddP birdRingInst
    mulP := mkMulP birdRingInst
    negP := mkNegP birdRingInst
    powP := mkPowP birdRingInst
    one := mkOne birdRingInst }

end CtxOps

/-- The context for a `certBirdDet` computation -/
structure Ctx {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- `Ring` evaluation cache for the scalar ring. -/
  cα : Common.Cache sα
  /-- Proof-producing ring arithmetic. -/
  rc : Common.RingCompute RatCoeff sα
  /--
  The exact `CommRing` instance from the reified `birdDet` term. Bird-side
  terms and ring normalization use this same expression so generated proofs
  remain definitionally aligned with the original goal.
  -/
  birdRingInst : Q(CommRing $α)
  dimension : Nat
  dimensionExpr : Q(Nat)
  array : Q(Array $α)
  arrayEntries : Array Q($α)
  /-- Canonical operations and matrix accessors built from `birdRingInst`. -/
  ops : CtxOps α

namespace Ctx

def applyEqLemma (name : Name) (u : Level) (args : Array Expr) : MetaM (EqProof α) := do
  let proof := mkAppN (mkConst name [u]) args
  Meta.expectProof (α := α) ("Ctx.applyEqLemma: " ++ toString name) proof

def add (ctx : Ctx sα) (x y : Q($α)) : Q($α) :=
  let addP := ctx.ops.addP
  q($addP $x $y)

def mul (ctx : Ctx sα) (x y : Q($α)) : Q($α) :=
  let mulP := ctx.ops.mulP
  q($mulP $x $y)

def neg (ctx : Ctx sα) (x : Q($α)) : Q($α) :=
  let negP := ctx.ops.negP
  q($negP $x)

def pow (ctx : Ctx sα) (x : Q($α)) (k : Nat) : Q($α) :=
  let powP := ctx.ops.powP
  let k : Q(Nat) := mkNatLit k
  q($powP $x $k)

def iterP (ctx : Ctx sα) (t : Nat) : Q(Nat → Nat → $α) :=
  mkAppN
    (mkConst ``iter [u])
    #[α, ctx.birdRingInst, ctx.dimensionExpr, ctx.array, mkNatLit t, ctx.ops.getP]

/-- Returns `fun k => iter n A t F_0 k k -/
def diagFun (ctx : Ctx sα) (t : Nat) : Q(Nat → $α) :=
  let iterP := ctx.iterP t
  q(fun k => $iterP k k)

def iterAt (ctx : Ctx sα) (t i j : Nat) : Q($α) :=
  let i : Q(Nat) := mkNatLit i
  let j : Q(Nat) := mkNatLit j
  let iterP := ctx.iterP t
  q($iterP $i $j)

def sumFrom (ctx : Ctx sα) (lo : Nat) (f : Q(Nat → $α)) : Q($α) :=
  mkAppN (mkConst ``sumFrom [u]) #[
    α, ctx.birdRingInst, ctx.dimensionExpr, mkNatLit lo, f]

def diagSum (ctx : Ctx sα) (t lo : Nat) : Q($α) :=
  ctx.sumFrom lo (ctx.diagFun t)

def tailFun (ctx : Ctx sα) (t i j : Nat) : Q(Nat → $α) :=
  let i : Q(Nat) := mkNatLit i
  let j : Q(Nat) := mkNatLit j
  let iterP := ctx.iterP t
  let getP := ctx.ops.getP
  let mulP := ctx.ops.mulP
  q(fun k => $mulP ($iterP $i k) ($getP k $j))

def birdSign (ctx : Ctx sα) (k : Nat) : Q($α) :=
  ctx.pow (ctx.neg ctx.ops.one) k

def sumFromStopEq (ctx : Ctx sα) (lo : Nat) (f : Q(Nat → $α)) : MetaM (EqProof α) := do
  let hNot ← Meta.mkNotLtProof lo ctx.dimension
  Ctx.applyEqLemma (α := α) ``sumFrom_stop u #[
    (α : Expr), ctx.birdRingInst, ctx.dimensionExpr, mkNatLit lo, f, hNot]

def sumFromStepEq (ctx : Ctx sα) (lo : Nat) (f : Q(Nat → $α)) : MetaM (EqProof α) := do
  let hLt ← Meta.mkLtProof lo ctx.dimension
  Ctx.applyEqLemma (α := α) ``sumFrom_step u #[
    (α : Expr), ctx.birdRingInst, ctx.dimensionExpr, mkNatLit lo, f, hLt]

def iterZeroEq (ctx : Ctx sα) (i j : Nat) : MetaM (EqProof α) :=
  Ctx.applyEqLemma (α := α) ``iter_zero u #[
    (α : Expr), ctx.birdRingInst, ctx.dimensionExpr, ctx.array, ctx.ops.getP,
    mkNatLit i, mkNatLit j]

def iterSuccEq (ctx : Ctx sα) (t i j : Nat) : MetaM (EqProof α) :=
  Ctx.applyEqLemma (α := α) ``iter_succ u #[
    (α : Expr), ctx.birdRingInst, ctx.dimensionExpr, ctx.array, mkNatLit t,
    ctx.ops.getP, mkNatLit i, mkNatLit j]

def birdDetZeroEq (ctx : Ctx sα) : MetaM (EqProof α) :=
  Ctx.applyEqLemma (α := α) ``birdDet_zero u #[
    (α : Expr), ctx.birdRingInst, ctx.array]

def birdDetEq (ctx : Ctx sα) (k : Nat) : MetaM (EqProof α) := do
  let kSucc ← mkAppM ``HAdd.hAdd #[mkNatLit k, mkNatLit 1]
  let hn ← mkExpectedTypeHint (← mkEqRefl ctx.dimensionExpr) (← mkEq ctx.dimensionExpr kSucc)
  Ctx.applyEqLemma (α := α) ``birdDet_eq u #[
    α, ctx.birdRingInst, ctx.dimensionExpr, mkNatLit k, ctx.array, hn]

/-- Constructs an equality between `get i j` and `arrayEntries[i * dimension + j]`.

app: `get ctx.dimension ctx.array i j`
result: `ctx.arrayEntries[i * ctx.dimension + j]`
proof: app = result
-/
def get (ctx : Ctx sα) (i j : Nat) : MetaM (EqProof α) := do
  let lhs := mkApp2 ctx.ops.getP (mkNatLit i) (mkNatLit j)
  let idx := i * ctx.dimension + j
  let zero : Q($α) := q(0)
  let result := ctx.arrayEntries.getD idx zero
  let lhs : Q($α) := lhs
  let rhs : Q($α) := result
  let proof ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
  return {lhs, rhs, proof}

end Ctx

end
