module

public import Determinant.CertChain.Ctx
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
  /-- Proof that the subject is equal to the `Ring` tactic normal form. -/
  eq : Meta.EqProof α
  /-- The internal ring tactic representation of `norm` -/
  val : Common.ExSum RatCoeff sα eq.rhs
  /-- `true` when `norm` is zero, this is computed from `val` during ring evaluation -/
  isZero : Bool

end

public section

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {sα : Q(CommSemiring $α)}

/-- The certificate subject. -/
def subject (c : Cert sα) : Q($α) :=
  c.eq.lhs

/-- The `Ring` tactic normal form that the subject is equal to. -/
def norm (c : Cert sα) : Q($α) :=
  c.eq.rhs

/-- Proof that the subject is equal to the normal form. -/
def proof (c : Cert sα) : Q($c.subject = $c.norm) :=
  c.eq.proof

end Cert

end

public meta section

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {sα : Q(CommSemiring $α)}

/-- Returns `true` when `val` is `ExSum.zero` -/
def isZeroVal {e : Q($α)} (val : Common.ExSum RatCoeff sα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/-- Repackage a `Ring` evaluation result as a certificate. -/
def toCert {e : Q($α)} (res : Common.Result (Common.ExSum RatCoeff sα) e) : Cert sα :=
  { eq := {lhs := e, rhs := res.expr, proof := res.proof}
    val := res.val
    isZero := isZeroVal res.val }

/-- Chain an equality proof into a certificate:
if `h : e = c.subject` and `c.proof : c.subject = c.norm`, return `e = c.norm`. -/
def chain (c : Cert sα) (h : Meta.EqProof α) : MetaM (Cert sα) := do
  let proof ← mkEqTrans h.proof c.eq.proof
  let proof ← mkExpectedTypeHint proof q($h.lhs = $c.eq.rhs)
  return {
    eq := {lhs := h.lhs, rhs := c.eq.rhs, proof}
    val := c.val
    isZero := c.isZero
  }

/-- Cast an existing `proof : subject = 0` as a certificate for the canonical zero. -/
def zeroCertOf (eq : Meta.EqProof α) : MetaM (Cert sα) := do
  let zero : Q($α) := q(0)
  let proof ← mkExpectedTypeHint eq.proof q($eq.lhs = $zero)
  return {
    eq := {lhs := eq.lhs, rhs := zero, proof}
    val := .zero
    isZero := true
  }

/-- Given `cz.proof : cz.subject! = 0`, certify the product `x * cz.subject =
  0` without evaluating `x`.

`mulP` is HMul.hmul, partially applied with types and instances.
-/
def zeroProdCert (mulP : Q($α → $α → $α)) (x : Q($α)) (cz : Cert sα) :
    MetaM (Cert sα) := do
  -- x * (cz.subject) = x * 0
  let mulX : Q($α → $α) := q($mulP $x)
  let h1 ← Meta.mkCongrUnop mulX cz.eq
  -- x * 0 = 0
  let h2 ← mkAppM ``mul_zero #[x]
  -- x * (cz.subject) = 0
  let h ← mkEqTrans h1.proof h2
  zeroCertOf (← Meta.expectProof (α := α) "zeroProdCert" h)

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

/-- Certify the evaluation of `e` using the Ring tactic. -/
def eval (e : Q($α)) : CertM sα (Cert sα) := do
  let ctx ← read
  let res ← Common.eval rcℕ ctx.rc ctx.cα e
  return toCert res

/-- Certify the evaluation of `a.val + b.val` using the Ring tactic. -/
def evalAdd (a b : Cert sα) : CertM sα (Cert sα) := do
  let ctx ← read
  let res ← Common.evalAdd ctx.rc rcℕ a.val b.val
  return toCert res

/-- Certify the evaluation of `a.val * b.val` using the Ring tactic. -/
def evalMul (a b : Cert sα) : CertM sα (Cert sα) := do
  let ctx ← read
  let res ← Common.evalMul ctx.rc rcℕ a.val b.val
  return toCert res

/-- Certify the evaluation of `-a.val` using the Ring tactic. -/
def evalNeg (a : Cert sα) : CertM sα (Cert sα) := do
  let ctx ← read
  let res ← Common.evalNeg ctx.rc ctx.birdRingInst a.val
  return toCert res

/-- Combine two certificates through addition, then normalize the sum. -/
def certAdd (a b : Cert sα) : CertM sα (Cert sα) := do
  let ctx ← read
  let h ← Meta.mkCongrBinop ctx.ops.addP a.eq b.eq
  let c ← evalAdd a b
  c.chain h

/-- Combine two certificates through multiplication, then normalize the product. -/
def certMul (a b : Cert sα) : CertM sα (Cert sα) := do
  let ctx ← read
  let h ← Meta.mkCongrBinop ctx.ops.mulP a.eq b.eq
  let c ← evalMul a b
  c.chain h

/-- Combine a certificate through negation, then normalize the result. -/
def certNeg (a : Cert sα) : CertM sα (Cert sα) := do
  let ctx ← read
  let h ← Meta.mkCongrUnop ctx.ops.negP a.eq
  let c ← evalNeg a
  c.chain h

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
  let ce ← eval elemApp.rhs
  let cert ← ce.chain elemApp
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

def certSumFromStop (lo : Nat) (f : Q(Nat → $α)) : CertM sα (Cert sα) := do
  let ctx ← read
  let eqStop ← ctx.sumFromStopEq lo f
  zeroCertOf eqStop

/-- Certify one `sumFrom` step by certifying the head and recursive tail, then
normalizing their sum. -/
def certSumFromStep
    (lo : Nat) (f : Q(Nat → $α))
    (head tail : CertM sα (Cert sα)) : CertM sα (Cert sα) := do
  let ctx ← read
  let stepEq ← ctx.sumFromStepEq lo f
  let chead ← head
  let ctail ← tail
  let csum ← certAdd chead ctail
  csum.chain stepEq

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
      ce.chain iterZeroPf
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
          let cneg ← certNeg cdiag
          certMul cneg ce
      let f := ctx.tailFun t' i j
      let ct ← certTail t' i j (i + 1) f
      let cs ← certAdd cd ct
      cs.chain iterSuccPf
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
        certMul ci ce_lo_j
    certSumFromStep lo f head (certTail t i j (lo + 1) f)
  else
    certSumFromStop lo f

end

def certBirdDet : CertM sα (Cert sα) := do
  let ctx ← read
  if ctx.dimension == 0
  then
    let birdDetZeroPf ← ctx.birdDetZeroEq
    let ce ← eval birdDetZeroPf.rhs
    ce.chain birdDetZeroPf
  else
    -- The non-zero `birdDet_eq` branch matches `k + 1` 
    -- so we set k := `ctx.dimension - 1`.
    let k := ctx.dimension - 1
    let birdDetEq ← ctx.birdDetEq k
    let cs ← eval (ctx.birdSign k)
    let ci ← certIter k 0 0
    let cm ← certMul cs ci
    cm.chain birdDetEq

end Cert


end
