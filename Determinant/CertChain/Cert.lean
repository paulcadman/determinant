module

public import Determinant.CertChain.Bird
public import Determinant.CertChain.Meta
public import Mathlib.Tactic.Ring
public import Qq
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Meta.Transform
public meta import Lean.Elab.Tactic.Basic

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring
open BirdDet

public meta section

/--
A `Cert` represents an equality:

```
subject = norm
```
where the `subject` is the lhs of the `proof`'s type.
-/
structure Cert {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- The `Ring` tactic normal form that the subject is equal to -/
  norm : Q($α)
  /-- The internal ring tactic representation of `norm` -/
  val : Common.ExSum RatCoeff sα norm
  /-- Proof that the `subject` is equal to the `norm` -/
  proof : Expr
  /-- `true` when `norm` is zero, this is computed from `val` during ring evaluation -/
  isZero : Bool

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {sα : Q(CommSemiring $α)}

/-- Extract the certificate's subject
Used for tests and debugging-/
def subject! (c : Cert sα) : MetaM Expr := do
  let some (_, lhs, _) := (← inferType c.proof).eq?
    | throwError "Cert.subject!: proof is not an equality: {c.proof}"
  return lhs

/-- Returns `true` when `val` is `ExSum.zero` -/
def isZeroVal {e : Q($α)} (val : Common.ExSum RatCoeff sα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/-- Repackage a `Ring` evaluation result as a certificate. -/
def toCert {e : Q($α)} (res : Common.Result (Common.ExSum RatCoeff sα) e) : Cert sα :=
  { norm := res.expr, val := res.val, proof := res.proof, isZero := isZeroVal res.val }

/-- Chain an equality proof into a certificate:
if `h : e = c.subject` and `c.proof : c.subject = c.norm`, return `e = c.norm`. -/
def chain (c : Cert sα) (h : Expr) : MetaM (Cert sα) := do
  return {c with proof := ← mkEqTrans h c.proof}

/-- Cast an existing `proof : subject = 0` as a certificate for the canonical zero. -/
def zeroCertOf (subject proof : Expr) : MetaM (Cert sα) := do
  let zero : Q($α) := q(0)
  let proof ← mkExpectedTypeHint proof (← mkEq subject zero)
  return {norm := zero, val := .zero, proof, isZero := true}

/-- Given `cz.proof : cz.subject! = 0`, certify the product `x * cz.subject =
  0` without evaluating `x`.

`mulP` is HMul.hmul, partially applied with types and instances.
-/
def zeroProdCert (mulP x : Expr) (cz : Cert sα) : MetaM (Cert sα) := do
  -- x * (cz.subject) = x * 0
  let h1 ← mkCongrArg (mkApp mulP x) cz.proof
  -- x * 0 = 0
  let h2 ← mkAppM ``mul_zero #[x]
  -- x * (cz.subject) = 0
  let h ← mkEqTrans h1 h2
  let eq ← Meta.expectProof (α := α) "zeroProdCert" h1
  zeroCertOf eq.lhs h

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

/-- Certify the evaluation of `e` using the Ring tactic -/
def eval (ctx : Ctx sα) (e : Q($α)) : AtomM (Cert sα) := do
  let res ← Common.eval rcℕ ctx.rc ctx.cα e
  return toCert res

/-- Certify the evaluation of `a.val + b.val` using the Ring tactic -/
def evalAdd (ctx : Ctx sα) (a b : Cert sα) : AtomM (Cert sα) := do
  let res ← Common.evalAdd ctx.rc rcℕ a.val b.val
  return toCert res

/-- Certify the evaluation of `a.val * b.val` using the Ring tactic -/
def evalMul (ctx : Ctx sα) (a b : Cert sα) : AtomM (Cert sα) := do
  let res ← Common.evalMul ctx.rc rcℕ a.val b.val
  return toCert res

/-- Certify the evaluation of `-a.val` using the Ring tactic -/
def evalNeg (ctx : Ctx sα) (a : Cert sα) : AtomM (Cert sα) := do
  let res ← Common.evalNeg ctx.rc ctx.birdRingInst a.val
  return toCert res

/-- Combine two certificates through addition, then normalize the sum. -/
def certAdd (ctx : Ctx sα) (a b : Cert sα) : AtomM (Cert sα) := do
  let h ← Meta.mkCongrBinop ctx.ops.addP a.proof b.proof
  let c ← ctx.evalAdd a b
  c.chain h

/-- Combine two certificates through multiplication, then normalize the product. -/
def certMul (ctx : Ctx sα) (a b : Cert sα) : AtomM (Cert sα) := do
  let h ← Meta.mkCongrBinop ctx.ops.mulP a.proof b.proof
  let c ← ctx.evalMul a b
  c.chain h

/-- Combine a certificate through negation, then normalize the result. -/
def certNeg (ctx : Ctx sα) (a : Cert sα) : AtomM (Cert sα) := do
  let h ← mkCongrArg ctx.ops.negP a.proof
  let c ← ctx.evalNeg a
  c.chain h

end Ctx

/-- A cache of proof certificates -/
structure CertCache {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- Cache for entry certificates, keyed by matrix indices. -/
  entryCache : Std.HashMap (Nat × Nat) (Cert sα) := {}
  /-- Cache for `iter` certificates, keyed by recursion index and matrix indices. -/
  iterCache : Std.HashMap (Nat × Nat × Nat) (Cert sα) := {}
  /-- Cache for diagonal-tail certificates, keyed by recursion index and lower bound. -/
  diagCache : Std.HashMap (Nat × Nat) (Cert sα) := {}

/-- The Monad used for computing certificates -/
abbrev CertM {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) :=
  StateT (CertCache sα) (ReaderT (Ctx sα) AtomM)

/-- Returns a certificate whose subject is `get n A i j`.

```
get n A i j = elem  -- By rfl
            = norm  -- Ring.eval on the entry
```
-/
def certEntry (i j : Nat) : CertM sα (Cert sα) := do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let elemApp ← ctx.get i j
  let ce ← ctx.eval elemApp.rhs
  let cert ← ce.chain elemApp.proof
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

def certSumFromStop (lo : Nat) (f : Q(Nat → $α)) : CertM sα (Cert sα) := do
  let ctx ← read
  let eqStop ← ctx.sumFromStopEq lo f
  zeroCertOf eqStop.lhs eqStop.proof

/-- Certify one `sumFrom` step by certifying the head and recursive tail, then
normalizing their sum. -/
def certSumFromStep
    (lo : Nat) (f : Q(Nat → $α))
    (head tail : CertM sα (Cert sα)) : CertM sα (Cert sα) := do
  let ctx ← read
  let stepEq ← ctx.sumFromStepEq lo f
  let chead ← head
  let ctail ← tail
  let csum ← ctx.certAdd chead ctail
  csum.chain stepEq.proof

mutual

/-- Returns a certificate whose subject is:

```
iter n A t (get n A) i j
```

```
iter n A (t' + 1) F_0 i j
  = -S * A[i,j] + T       -- iter_succ
  = dNorm + tNorm         -- congruence
  = norm                  -- Ring.evalAdd
```

Where `S = ∑_{k>i} F_t k k` and `T = ∑_{k>i} F_t i k * A[k,j]`

If A[i,j] is certified 0 then S is not required.

-/
partial def certIter (t i j : Nat) : CertM sα (Cert sα) := do
  if let some c := (← get).iterCache[(t, i, j)]? then
    return c
  let ctx ← read
  let cert ← match t with
    | 0 => do
      -- iter n A 0 (get n A) = get n
      let iterZeroPf ← ctx.iterZeroEq i j
      let ce ← certEntry i j
      ce.chain iterZeroPf.proof
    | t' + 1 => do
      let iterSuccPf ← ctx.iterSuccEq t' i j
      let negS := ctx.neg (ctx.diagSum t' (i + 1))
      -- A[i,j]
      let ce ← certEntry i j
      let cd ← 
        if ce.isZero then
          zeroProdCert ctx.ops.mulP negS ce
        else do
          let cdiag ← certDiag t' (i + 1)
          let cneg ← ctx.certNeg cdiag
          ctx.certMul cneg ce
      let f := ctx.tailFun t' i j
      let ct ← certTail t' i j (i + 1) f
      let cs ← ctx.certAdd cd ct
      cs.chain iterSuccPf.proof
  modify fun s => {s with iterCache := s.iterCache.insert (t, i, j) cert}
  return cert


/-- Returns a certificate whose subject is:

```
sumFrom n lo (fun k => iter n A t (get n A) k k)
```

This is the diagonal tail sum in the Bird determinant formula

```
∑_{k=lo}^{n-1} F_t k k
```

It certifies that:

```
sumFrom n lo diagFun
  = diagFun lo + sumFrom n (lo + 1) diagFun   -- sumFrom_step (lo < n)
  = headNorm + tailNorm                       -- congruence
  = norm                                      -- Ring.evalAdd
```

-/
partial def certDiag (t lo : Nat) : CertM sα (Cert sα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let cert ← 
    if lo < ctx.dimension
    then do
      certSumFromStep lo (ctx.diagFun t) (certIter t lo lo) (certDiag t (lo + 1))
    else
      certSumFromStop lo (ctx.diagFun t)
  modify fun s => {s with diagCache := s.diagCache.insert (t, lo) cert}
  return cert

/-- Returns a certificate whose subject is:

```
sumFrom n lo (fun k => iter n A t (get n A) i k * get n A k j)
```

This is the tail sum in the Bird determinant formula:

```
∑_{k=lo}^{n-1} F_t[i,k] * A[k,j].
```

It certifies that:

```
sumFrom n lo f
  = f lo + sumFrom n (lo + 1) f   -- sumFrom_step (lo < n)
  = prodNorm + tailNorm           -- congruence
  = norm                          -- Ring.evalAdd
```

NB: `f lo` reduces to `F_t[i, lo] * A[lo, j]` so we can certify that separately:

```
F_t[i,lo] * A[lo,j]
  = iterNorm * gNorm  -- congruence
  = prodNorm          -- Ring.evalMul
```

And we can check if A[lo,j] is zero and avoid certifying `F_t[i,lo]`.

-/
partial def certTail (t i j lo : Nat) (f : Q(Nat → $α)) : CertM sα (Cert sα) := do
  let ctx ← read
  if lo < ctx.dimension
  then do
    let head := do
      -- Certify F_t[i,lo] * A[lo,j]
      let ce_lo_j ← certEntry lo j
      -- If A[lo,j] = 0 then we can avoid computing the product.
      if ce_lo_j.isZero
      then zeroProdCert ctx.ops.mulP (ctx.iterAt t i lo) ce_lo_j
      else do
        let ci ← certIter t i lo
        ctx.certMul ci ce_lo_j
    certSumFromStep lo f head (certTail t i j (lo + 1) f)
  else
    certSumFromStop lo f

end

def certBirdDet : CertM sα (Cert sα) := do
  let ctx ← read
  if ctx.dimension == 0
  then
    let birdDetZeroPf ← ctx.birdDetZeroEq
    let ce ← ctx.eval birdDetZeroPf.rhs
    ce.chain birdDetZeroPf.proof
  else
    -- The non-zero `birdDet_eq` branch matches `k + 1` 
    -- so we set k := `ctx.dimension - 1`.
    let k := ctx.dimension - 1
    let birdDetEq ← ctx.birdDetEq k
    let cs ← ctx.eval (ctx.birdSign k)
    let ci ← certIter k 0 0
    let cm ← ctx.certMul cs ci
    cm.chain birdDetEq.proof

end Cert


end
