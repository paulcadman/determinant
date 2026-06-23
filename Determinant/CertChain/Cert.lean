module

public import Determinant.CertChain.Ctx
public import Mathlib.Tactic.Ring
public import Qq

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring
open BirdDet

public meta section

/-- The ring tactic representation of a normalized certificate expression. -/
abbrev CertVal {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (e : Q($α)) :=
  Common.ExSum RatCoeff (commSemiringOfCommRing rα) e

/-- The ring-normalization result carried by a certificate. -/
abbrev CertResult {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (subject : Q($α)) :=
  Common.Result (CertVal rα) subject

/--
A `Cert` represents an equality:

```
subject = result.expr
```

where `result.expr` is the Ring tacric normal form.
-/
structure Cert {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- The expression being certified. -/
  {subject : Q($α)}
  /-- The resul of evaluating `subject` using the ring tactic. -/
  result : CertResult rα subject
  /-- `true` when `norm` is zero, used as a hint to the evaluator. -/
  isZero : Bool

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

/-- The `Ring` tactic normal form that the subject is equal to. -/
def norm (c : Cert rα) : Q($α) :=
  c.result.expr

/-- The internal ring tactic representation of the normal form. -/
def val (c : Cert rα) : CertVal rα c.norm :=
  c.result.val

/-- Proof that the subject is equal to the normal form. -/
def proof (c : Cert rα) : Q($c.subject = $c.norm) :=
  c.result.proof

/-- Repackage the certificate as the local equality-proof helper. -/
def eq (c : Cert rα) : Meta.EqProof α :=
  { lhs := c.subject, rhs := c.norm, proof := c.proof }

end Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

namespace Meta.EqProof

/-- Extend an equality proof with a certificate for its right-hand side.

If `h : e = c.subject` and `c.proof : c.subject = c.norm`
returns a certificate for `e = c.norm`.
-/
def chain (h : Meta.EqProof α) (c : Cert rα) : MetaM (Cert rα) := do
  have : $h.rhs =Q $c.eq.lhs := ⟨⟩
  let hProof : Q($h.lhs = $c.eq.lhs) := h.proof
  let proof : Q($h.lhs = $c.eq.rhs) := q(Eq.trans $hProof $c.eq.proof)
  let result : CertResult rα h.lhs := {
    expr := c.norm
    val := c.val
    proof
  }
  return {
    result
    isZero := c.isZero
  }

end Meta.EqProof

namespace Cert

/-- Returns `true` when `val` is `ExSum.zero` -/
def isZeroVal {e : Q($α)} (val : CertVal rα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/-- The scalar zero built with the exact ring instance used by the certificate. -/
def scalarZero : Q($α) :=
  q(letI : CommRing $α := $rα; 0)

/-- Repackage a `Ring` evaluation result as a certificate. -/
def toCert {e : Q($α)} (res : Common.Result (CertVal rα) e) : Cert rα :=
  { result := res
    isZero := isZeroVal res.val }

/-- Cast an existing `proof : subject = 0` as a certificate for the canonical zero. -/
def zeroCertOf (eq : Meta.EqProof α) : MetaM (Cert rα) := do
  let zero : Q($α) := q(0)
  have : $eq.rhs =Q $zero := ⟨⟩
  let proof : Q($eq.lhs = $zero) := eq.proof
  let result : CertResult rα eq.lhs := {
    expr := zero
    val := .zero
    proof
  }
  return {
    result
    isZero := true
  }

/-- Given `cz.proof : cz.subject! = 0`, certify the product `x * cz.subject =
  0` without evaluating `x`.
-/
def zeroProdCert (x : Q($α)) (cz : Cert rα) :
    MetaM (Cert rα) := do
  -- x * (cz.subject) = x * 0
  let mulX : Q($α → $α) := q(fun y => $x * y)
  let h1 ← Meta.mkCongrUnop mulX cz.eq
  -- x * 0 = 0
  let xMulZero : Q($α) := q($x * 0)
  let h2 : Q($xMulZero = 0) := q(mul_zero $x)
  -- x * (cz.subject) = 0
  let xMulSubject : Q($α) := q($x * $cz.eq.lhs)
  let ⟨h1Lhs⟩ ← assertDefEqQ h1.lhs xMulSubject
  let ⟨h1Rhs⟩ ← assertDefEqQ h1.rhs xMulZero
  have : $h1.lhs =Q $xMulSubject := h1Lhs
  have : $h1.rhs =Q $xMulZero := h1Rhs
  let h1Proof : Q($xMulSubject = $xMulZero) := h1.proof
  let proof : Q($xMulSubject = 0) := q(Eq.trans $h1Proof $h2)
  zeroCertOf (EqProof.ofQ proof)

/-- A cache of proof certificates -/
structure CertCache {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- Cache for entry certificates, keyed by matrix indices. -/
  entryCache : Std.HashMap (Nat × Nat) (Cert rα) := {}
  /-- Cache for `iter` certificates, keyed by recursion index and matrix indices. -/
  iterCache : Std.HashMap (Nat × Nat × Nat) (Cert rα) := {}
  /-- Cache for diagonal-tail certificates, keyed by recursion index and lower bound. -/
  diagCache : Std.HashMap (Nat × Nat) (Cert rα) := {}

/-- The Monad used for computing certificates -/
abbrev CertM {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) :=
  StateT (CertCache rα) (ReaderT (Ctx rα) AtomM)

/-- Certify the evaluation of `e` using the Ring tactic. -/
def certEval (e : Q($α)) : CertM rα (Cert rα) := do
  let ctx ← read
  let res ← Common.eval rcℕ ctx.rc ctx.cα e
  return toCert res

/-- Combine two certificates through addition, then normalize the sum. -/
def certAdd (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let h ← Meta.mkCongrBinop q(fun x y => x + y) a.eq b.eq
  let c ← toCert <$> Common.evalAdd ctx.rc rcℕ a.val b.val
  h.chain c

/-- Combine two certificates through multiplication, then normalize the product. -/
def certMul (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let h ← Meta.mkCongrBinop q(fun x y => x * y) a.eq b.eq
  let c ← toCert <$> Common.evalMul ctx.rc rcℕ a.val b.val
  h.chain c

/-- Combine a certificate through negation, then normalize the result. -/
def certNeg (a : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let h ← Meta.mkCongrUnop q(fun x => -x) a.eq
  let c ← toCert <$> Common.evalNeg ctx.rc rα a.val
  h.chain c

/-- Certify the sign term in the bird determinant formula -/
def certBirdSign (k : Nat) : CertM rα (Cert rα) := do
  certEval q((-1 : $α) ^ $k)

/-- Returns a certificate whose subject is `get n A i j`.

```
get n A i j = elem  -- By rfl
            = norm  -- Ring.eval on the entry
```
-/
def certEntry (i j : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let elemApp ← ctx.getEntryEq i j
  let ce ← certEval elemApp.rhs
  let cert ← elemApp.chain ce
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

def certSumFromStop (lo : Nat) (f : Q(Nat → $α)) : CertM rα (Cert rα) := do
  let ctx ← read
  let eqStop ← ctx.sumFromStopEq lo f
  zeroCertOf eqStop

def certSumFromStep
    (lo : Nat) (f : Q(Nat → $α))
    (headCert tailCert : CertM rα (Cert rα)) : CertM rα (Cert rα) := do
  let ctx ← read
  let stepEq ← ctx.sumFromStepEq lo f
  let head ← headCert
  let tail ← tailCert
  let sumCert ← certAdd head tail
  stepEq.chain sumCert

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
partial def certIter (t i j : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).iterCache[(t, i, j)]? then
    return c
  let ctx ← read
  let cert ← match t with
    | 0 => do
      -- iter n A 0 (get n A) = get n
      let iterZeroPf ← ctx.iterZeroEq i j
      let ce ← certEntry i j
      iterZeroPf.chain ce
    | t' + 1 => do
      let iterSuccPf ← ctx.iterSuccEq t' i j
      -- First summand in `iter_succ`:
      --   -(sumFrom n (i + 1) fun k => F_t k k) * A[i,j]
      let negDiagSum :=
        q(-$(ctx.sumFrom (i + 1) q(fun k => $(ctx.iterP t') k k)))
      let entryCert ← certEntry i j
      let diagProdCert ←
        if entryCert.isZero then
          zeroProdCert negDiagSum entryCert
        else do
          let diagSumCert ← certDiag t' (i + 1)
          let negDiagSumCert ← certNeg diagSumCert
          certMul negDiagSumCert entryCert
      -- Second summand in `iter_succ`:
      --   sumFrom n (i + 1) fun k => F_t i k * A[k,j]
      -- let tailSummand := ctx.tailFun t' i j
      let tailSumCert ← certTail t' i j (i + 1)
      let rhsCert ← certAdd diagProdCert tailSumCert
      iterSuccPf.chain rhsCert
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
partial def certDiag (t lo : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterP t) k k)
  let cert ←
    if lo < ctx.info.dimension
    then do
      -- Bird term: `sumFrom n lo fun k => F_t k k`.
      let headCert := certIter t lo lo
      let tailCert := certDiag t (lo + 1)
      certSumFromStep
        (lo := lo)
        (f := diagonalSummand)
        (headCert := headCert)
        (tailCert := tailCert)
    else
      certSumFromStop lo diagonalSummand
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
partial def certTail (t i j lo : Nat) : CertM rα (Cert rα) := do
  let ctx ← read
  let tailSummand := q(fun k => $(ctx.iterP t) $i k * $(ctx.getP) k $j)
  if lo < ctx.info.dimension
  then do
    -- Bird term: `sumFrom n lo fun k => F_t i k * A[k,j]`.
    let headCert := do
      -- Certify `F_t[i,lo] * A[lo,j]`.
      let entryCert ← certEntry lo j
      -- If `A[lo,j] = 0`, avoid certifying `F_t[i,lo]`.
      if entryCert.isZero
      then zeroProdCert q($(ctx.iterP t) $i $lo) entryCert
      else do
        let iterCert ← certIter t i lo
        certMul iterCert entryCert
    let tailCert := certTail t i j (lo + 1)
    certSumFromStep
      (lo := lo)
      (f := tailSummand)
      (headCert := headCert)
      (tailCert := tailCert)
  else
    certSumFromStop lo tailSummand

end

def certBirdDet : CertM rα (Cert rα) := do
  let ctx ← read
  if ctx.info.dimension == 0
  then
    let birdDetZeroPf ← ctx.birdDetZeroEq
    let ce ← certEval birdDetZeroPf.rhs
    birdDetZeroPf.chain ce
  else
    -- The non-zero `birdDet_eq` branch matches `k + 1`
    -- so we set k := `ctx.info.dimension - 1`.
    let k := ctx.info.dimension - 1
    let birdDetEq ← ctx.birdDetEq k
    let cs ← certBirdSign k
    let ci ← certIter k 0 0
    let cm ← certMul cs ci
    birdDetEq.chain cm

end Cert


end
