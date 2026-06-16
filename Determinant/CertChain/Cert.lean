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

/-- Prepend an equality proof to a certificate:
if `h : e = c.subject` and `c.proof : c.subject = c.norm`, return `e = c.norm`. -/
def prependProof (c : Cert sα) (h : Expr) : MetaM (Cert sα) := do
  return {c with proof := ← mkEqTrans h c.proof}

/-- Cast an existing `proof : subject = 0` as a certificate for the cannonical zero -/
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
  let eq ← Meta.expectProof (α := α) h1
  zeroCertOf eq.lhs h

/-- The context for a `certBirdDet` computation -/
structure Ctx {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  rα : Q(CommRing $α)
  /-- `Ring` evaluation cache for the scalar ring. -/
  cα : Common.Cache sα
  /-- Proof-producing ring arithmetic. -/
  rc : Common.RingCompute RatCoeff sα
  /-- `CommRing` expression, using the same spelilng as the
    `birdDet goal.-/
  commRingInst : Expr
  dimension : Nat
  dimensionExpr : Expr
  array : Expr
  arrayEntries : Array Expr
  /-- Canonical `@get R inst n A` — both the matrix reader and the initial
  entry function of the recurrence. -/
  getP : Expr

namespace Ctx

def applyEqLemma (name : Name) (u : Level) (args : Array Expr) : MetaM (EqProof α) := do
  let proof := mkAppN (mkConst name [u]) args
  try
    Meta.expectProof (α := α) proof
  catch _ =>
    throwError "Ctx.applyEqLemma: {name} did not produce an equality over{indentExpr α}"

def iterP (ctx : Ctx sα) (t : Nat) : Expr :=
  mkAppN
    (mkConst ``iter [u])
    #[α, ctx.commRingInst, ctx.dimensionExpr, ctx.array, mkNatLit t, ctx.getP]

/-- Returns `fun k => iter n A t F_0 k k -/
def diagFun (ctx : Ctx sα) (t : Nat) : Expr :=
  mkLambda `k .default (mkConst ``Nat) (mkApp2 (iterP ctx t) (.bvar 0) (.bvar 0))

/-- Constructs an equality between `get i j` and arrayEntries[i * dimenstion + j]

app: `get ctx.dimension ctx.array i j`
result: `ctx.arrayEntries[i * ctx.dimension + j]`
proof: app = result
-/
def get (ctx : Ctx sα) (i j : Nat) : MetaM (EqProof α) := do
  let lhs := mkApp2 ctx.getP (mkNatLit i) (mkNatLit j)
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
  let res ← Common.evalNeg ctx.rc ctx.rα a.val
  return toCert res

/-- Combine two certificates through addition, then normalize the sum. -/
def certAdd (ctx : Ctx sα) (addP : Expr) (a b : Cert sα) : AtomM (Cert sα) := do
  let h ← Meta.mkCongrBinop addP a.proof b.proof
  let c ← ctx.evalAdd a b
  c.prependProof h

/-- Combine two certificates through multiplication, then normalize the product. -/
def certMul (ctx : Ctx sα) (mulP : Expr) (a b : Cert sα) : AtomM (Cert sα) := do
  let h ← Meta.mkCongrBinop mulP a.proof b.proof
  let c ← ctx.evalMul a b
  c.prependProof h

/-- Combine a certificate through negation, then normalize the result. -/
def certNeg (ctx : Ctx sα) (negP : Expr) (a : Cert sα) : AtomM (Cert sα) := do
  let h ← mkCongrArg negP a.proof
  let c ← ctx.evalNeg a
  c.prependProof h

end Ctx

/-- A cache of proof certificates -/
structure CertCache {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  /-- Cache for `iterEntry` certificates, keyed by matrix indices -/
  entryCache : Std.HashMap (Nat × Nat) (Cert sα) := {}
  /-- Cache for `iterEntry` certificates keyed by matrix indices and recusion index -/
  iterCache : Std.HashMap (Nat × Nat × Nat) (Cert sα) := {}
  /-- Cache for `diagEntry` certificates keyed by matrix indices -/
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
  let cert ← ce.prependProof elemApp.proof
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

def certSumFromStop (lo : Nat) (f : Expr) : CertM sα (Cert sα) := do
  let ctx ← read
  let hNot ← Meta.mkNotLtProof lo ctx.dimension
  let eqStop ← Ctx.applyEqLemma (α := α) ``sumFrom_stop u #[
    (α : Expr), ctx.commRingInst, ctx.dimensionExpr, mkNatLit lo, f, hNot]
  zeroCertOf eqStop.lhs eqStop.proof

/-- Certify one `sumFrom` step by certifying the head and recursive tail, then
normalizing their sum. -/
def certSumFromStep
    (lo : Nat) (f : Expr)
    (head tail : CertM sα (Cert sα)) : CertM sα (Cert sα) := do
  let ctx ← read
  let hLt ← Meta.mkLtProof lo ctx.dimension
  let stepEq ← Ctx.applyEqLemma (α := α) ``sumFrom_step u #[
    (α : Expr), ctx.commRingInst, ctx.dimensionExpr, mkNatLit lo, f, hLt]
  let addApp ← Meta.expectAdd "certSumFromStep" stepEq.rhs
  let chead ← head
  let ctail ← tail
  let csum ← ctx.certAdd addApp.partialApp chead ctail
  csum.prependProof stepEq.proof

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
      let iterZeroPf ← Ctx.applyEqLemma (α := α) ``iter_zero u #[
        (α : Expr), ctx.commRingInst, ctx.dimensionExpr, ctx.array, ctx.getP, mkNatLit i, mkNatLit j]
      let ce ← certEntry i j
      ce.prependProof iterZeroPf.proof
    | t' + 1 => do
      let iterSuccPf ← Ctx.applyEqLemma (α := α) ``iter_succ u #[
        (α : Expr), ctx.commRingInst, ctx.dimensionExpr, ctx.array, mkNatLit t', ctx.getP,
        mkNatLit i, mkNatLit j]
      let ⟨addP, dTerm, tSum⟩ ← Meta.expectAdd "certIter" iterSuccPf.rhs
      let ⟨mulP, negS, _⟩ ← Meta.expectMul "certIter" dTerm
      let ⟨negP, _⟩ ← Meta.expectNeg "certIter" negS
      -- A[i,j]
      let ce ← certEntry i j
      let cd ← 
        if ce.isZero then
          zeroProdCert mulP negS ce
        else do
          let cdiag ← certDiag t' (i + 1)
          let cneg ← ctx.certNeg negP cdiag
          ctx.certMul mulP cneg ce
      let f ← Meta.expectSumFromFun "certIter" tSum
      let ct ← certTail t' i j (i + 1) f mulP
      let cs ← ctx.certAdd addP cd ct
      cs.prependProof iterSuccPf.proof
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

And we can check if A[lo,j] is zero and avoid certifyin `F_t[i,lo]`.

-/
partial def certTail (t i j lo : Nat) (f mulP : Expr) : CertM sα (Cert sα) := do
  let ctx ← read
  if lo < ctx.dimension
  then do
    let head := do
      -- Certify F_t[i,lo] * A[lo,j]
      let ce_lo_j ← certEntry lo j
      -- If A[lo,j] = 0 then we can avoid computing the product.
      if ce_lo_j.isZero
      then zeroProdCert mulP (mkApp2 (ctx.iterP t) (mkNatLit i) (mkNatLit lo)) ce_lo_j
      else do
        let ci ← certIter t i lo
        ctx.certMul mulP ci ce_lo_j
    certSumFromStep lo f head (certTail t i j (lo + 1) f mulP)
  else
    certSumFromStop lo f

end

def certBirdDet : CertM sα (Cert sα) := do
  let ctx ← read
  if ctx.dimension == 0
  then
    let birdDetZeroPf ← Ctx.applyEqLemma (α := α) ``birdDet_zero u #[
      (α : Expr), ctx.commRingInst, ctx.array]
    let ce ← ctx.eval birdDetZeroPf.rhs
    ce.prependProof birdDetZeroPf.proof
  else
    let k := ctx.dimension - 1
    let kSucc ← mkAppM ``HAdd.hAdd #[mkNatLit k, mkNatLit 1]
    let hn ← mkExpectedTypeHint (← mkEqRefl ctx.dimensionExpr) (← mkEq ctx.dimensionExpr kSucc)
    let birdDetEq ← Ctx.applyEqLemma (α := α) ``birdDet_eq u #[
      α, ctx.commRingInst, ctx.dimensionExpr, mkNatLit k, ctx.array, hn]
    let ⟨mulP, s, _⟩ ← Meta.expectMul "certBirdDet" birdDetEq.rhs
    let cs ← ctx.eval s
    let ci ← certIter k 0 0
    let cm ← ctx.certMul mulP cs ci
    cm.prependProof birdDetEq.proof

end Cert


end
