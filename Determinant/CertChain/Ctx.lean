module

public import Determinant.CertChain.Bird
public meta import Determinant.CertChain.Meta
public meta import Mathlib.Tactic.Ring
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues

open Lean Meta Qq
open Mathlib.Tactic.Ring
open BirdDet

public meta section

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

/-- Construct a `CommSemiring` instance from a `CommRing` instance -/
abbrev commSemiringOfCommRing {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) : Q(CommSemiring $α) :=
  q(@CommRing.toCommSemiring $α $rα)

/-- The context for a `certBirdDet` computation -/
structure Ctx {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- `Ring` evaluation cache for the scalar ring. -/
  cα : Common.Cache (commSemiringOfCommRing rα)
  /-- Proof-producing ring arithmetic. -/
  rc : Common.RingCompute RatCoeff (commSemiringOfCommRing rα)
  /-- The reified determinant payload. -/
  info : BirdDetData rα

namespace Ctx

/-- Build the certificate context from a reified `birdDet` call. -/
def ofBirdDetInfo (info : BirdDetInfo) : Ctx info.rα :=
  let sα := commSemiringOfCommRing info.rα
  let cα : Common.Cache sα := { rα := some info.rα
                                dsα := none
                                czα := none }
  { cα
    rc := ringCompute cα
    info := info.data }

def getP (ctx : Ctx rα) : Q(Nat → Nat → $α) :=
  let n : ℕ := ctx.info.dimension
  q(BirdDet.get $n $ctx.info.arrayExpr)

def iterP (ctx : Ctx rα) (t : Nat) : Q(Nat → Nat → $α) :=
  let dim : ℕ := ctx.info.dimension
  q(BirdDet.iter $dim $ctx.info.arrayExpr $t $ctx.getP)

def sumFrom (ctx : Ctx rα) (lo : Nat) (f : Q(Nat → $α)) : Q($α) :=
  let dim : ℕ := ctx.info.dimension
  q(BirdDet.sumFrom $dim $lo $f)

/-- Equality proofs for Bird recurrence equations. -/

def sumFromStopEq (ctx : Ctx rα) (lo : Nat) (f : Q(Nat → $α)) : MetaM (EqProof α) := do
  have dim : ℕ := ctx.info.dimension
  let hNot : Q(¬ $lo < $dim) ← mkDecideProofQ q(¬ $lo < $dim)
  let lhs : Q($α) := q(BirdDet.sumFrom $dim $lo $f)
  let proof : Q($lhs = 0) := q(sumFrom_stop $dim $lo $f $hNot)
  return EqProof.ofQ proof

def sumFromStepEq (ctx : Ctx rα) (lo : Nat) (f : Q(Nat → $α)) : MetaM (EqProof α) := do
  have dim : Nat := ctx.info.dimension
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let lhs : Q($α) := q(BirdDet.sumFrom $dim $lo $f)
  let rhs : Q($α) :=
    q($f $lo + BirdDet.sumFrom $dim ($lo + 1) $f)
  let proof : Q($lhs = $rhs) := q(sumFrom_step $dim $lo $f $hLt)
  return EqProof.ofQ proof

def iterZeroEq (ctx : Ctx rα) (i j : Nat) : MetaM (EqProof α) := do
  let dim : ℕ := ctx.info.dimension
  let proof := q(iter_zero $dim $ctx.info.arrayExpr $ctx.getP $i $j)
  return EqProof.ofQ proof

def iterSuccEq (ctx : Ctx rα) (t i j : Nat) : MetaM (EqProof α) := do
  let dim : ℕ := ctx.info.dimension
  let proof := q(iter_succ $dim $ctx.info.arrayExpr $t $ctx.getP $i $j)
  return EqProof.ofQ proof

def birdDetZeroEq (ctx : Ctx rα) : MetaM (EqProof α) := do
  let proof := q(birdDet_zero $ctx.info.arrayExpr)
  return EqProof.ofQ proof

def birdDetEq (ctx : Ctx rα) (k : Nat) : MetaM (EqProof α) := do
  have dim : Q(ℕ) := mkNatLitQ ctx.info.dimension
  have : $dim =Q $k + 1 := ⟨⟩
  let hn : Q($dim = $k + 1) := q(rfl)
  let proof := q(birdDet_eq $dim $k $ctx.info.arrayExpr $hn)
  return EqProof.ofQ proof

/-- Constructs an equality between `get i j` and `arrayEntries[i * dimension + j]`. -/
def getEntryEq (ctx : Ctx rα) (i j : Nat) : MetaM (EqProof α) := do
  let dim : ℕ := ctx.info.dimension
  let lhs : Q($α) := q(BirdDet.get $dim $ctx.info.arrayExpr $i $j)
  let idx := i * ctx.info.dimension + j
  let rhs : Q($α) := ctx.info.arrayEntries.getD idx q(0)
  have : $lhs =Q $rhs := ⟨⟩
  let proof : Q($lhs = $rhs) := q(rfl)
  return EqProof.ofQ proof

end Ctx

end
