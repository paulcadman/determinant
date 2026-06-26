module

public meta import Determinant.CertChain.Meta
public meta import Mathlib.Tactic.Ring

open Lean Meta Qq
open Mathlib.Tactic.Ring

public meta section

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

/-- Construct a `CommSemiring` instance from a `CommRing` instance -/
abbrev commSemiringOfCommRing {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) : Q(CommSemiring $α) :=
  q(CommRing.toCommSemiring (α := $α) (s := $rα))

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

def iterP (ctx : Ctx rα) (t : Nat) : Q(Nat → Nat → $α) :=
  let dim : Q(Nat) := ctx.info.dimensionExpr
  let A : Q(Array $α) := ctx.info.arrayExpr
  q(BirdDet.iter $dim $A $t (BirdDet.get $dim $A))

def sumFrom (ctx : Ctx rα) (lo : Nat) (f : Q(Nat → $α)) : Q($α) :=
  let dim : Q(Nat) := ctx.info.dimensionExpr
  q(BirdDet.sumFrom $dim $lo $f)

end Ctx

end
