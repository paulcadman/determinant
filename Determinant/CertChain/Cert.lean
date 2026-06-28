module

public import Determinant.CertChain.Ctx

/-!
# Certificate-chain evaluator for `BirdDet`

This file certifies evaluations of the scalar recurrence defined in
`Determinant.CertChain.Bird`.

The flow is deliberately close to the definitions in `Bird.lean`:

* `certEntry` mirrors `BirdDet.get`.
* `certSumFromStop` and `certSumFromStep` mirror `BirdDet.sumFrom_stop` and
  `BirdDet.sumFrom_step`.
* `certIter` mirrors `BirdDet.iter_zero` and `BirdDet.iter_succ`.
* `certBirdDet` mirrors `BirdDet.birdDet_zero` and `BirdDet.birdDet_eq`.

Each `cert*` function first uses the corresponding unfolding theorem from
`Bird.lean` to expose the arithmetic expression, then uses the `Ring` evaluator
to normalize that arithmetic expression while constructing a proof certificate.
-/

open Lean Meta Qq
open Mathlib.Tactic (AtomM)
open Mathlib.Tactic.Ring

public meta section

/-- The internal `ring` normal-form value for a certified scalar expression. -/
abbrev CertVal {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (e : Q($α)) :=
  Common.ExSum RatCoeff (commSemiringOfCommRing rα) e

/-- The `ring` result carried by a certificate for a particular subject. -/
abbrev CertResult {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (subject : Q($α)) :=
  Common.Result (CertVal rα) subject

/--
A proof-producing `ring` normalization result for one scalar expression.

```
c.subject = c.norm
```

A `Cert` stores both the kernel proof of this equality and the internal ring
normal form used to combine this certificate with later certificates. The
`isZero` field is a cached syntactic zero check on the normal form, used by
the zero-skip branch of `certIter`.
-/
structure Cert {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- The expression being certified. -/
  {subject : Q($α)}
  /-- The result of evaluating `subject` using the ring tactic. -/
  result : CertResult rα subject
  /-- `true` when `norm` is zero, used as a hint to the evaluator. -/
  isZero : Bool

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

/-- Return the normalized RHS certified equal to `c.subject`. -/
def norm (c : Cert rα) : Q($α) :=
  c.result.expr

/-- Return the internal `ring` representation of `c.norm`. -/
def val (c : Cert rα) : CertVal rα c.norm :=
  c.result.val

/-- Return the proof `c.subject = c.norm`. -/
def proof (c : Cert rα) : Q($c.subject = $c.norm) :=
  c.result.proof

/-- Prepend an unfolding proof to an existing normalized RHS certificate.

This is the common "Bird equation followed by normalized RHS" step. If
`h : lhs = rhs` is one of the equations from `Bird.lean`, and `c` certifies
`rhs = c.norm`, then `c.chainProof h` certifies `lhs = c.norm`.

The proof RHS must be definitionally equal to `c.subject`. Since `Cert` is not
indexed by its subject, that equality is checked through the `Qq` cast here
rather than by the type of `Cert` itself.
-/
def chainProof {lhs rhs : Q($α)} (c : Cert rα) (h : Q($lhs = $rhs)) :
    Cert rα :=
  have : $rhs =Q $c.subject := ⟨⟩
  let hProof : Q($lhs = $c.subject) := h
  let proof : Q($lhs = $c.norm) := q(Eq.trans $hProof $c.proof)
  let result : CertResult rα lhs := {
    expr := c.norm
    val := c.val
    proof
  }
  {
    result
    isZero := c.isZero
  }

/-- Return `true` when a `ring` normal-form value is syntactic zero. -/
def isZeroVal {e : Q($α)} (val : CertVal rα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/-- Repackage a raw `ring` result as a `Cert`. -/
def toCert {e : Q($α)} (res : Common.Result (CertVal rα) e) : Cert rα :=
  { result := res
    isZero := isZeroVal res.val }

/-- Build a zero certificate from a proof `lhs = 0`. -/
def zeroCertOfProof {lhs : Q($α)} (h : Q($lhs = 0)) : Cert rα :=
  let zero : Q($α) := q(0)
  let proof : Q($lhs = $zero) := h
  let result : CertResult rα lhs := {
    expr := zero
    val := .zero
    proof
  }
  {
    result
    isZero := true
  }

/-- Certify `x * cz.subject = 0` without recursively certifying `x`.

This is used by the zero-skip path in `certIter`. In the first summand of
`BirdDet.iter_succ`,

```
-(sumFrom n (i + 1) fun k => F_t k k) * get n A i j
```

if `get n A i j` has already certified to zero, the diagonal `sumFrom` does not
need to be recursively certified.
-/
def zeroProdCert (x : Q($α)) (cz : Cert rα) :
    MetaM (Cert rα) := do
  let subject : Q($α) := cz.subject
  let norm : Q($α) := cz.norm
  let zero : Q($α) := q(0)
  have : $norm =Q $zero := ⟨⟩
  let subjectZero : Q($subject = $zero) := cz.proof
  let xMulSubject : Q($α) := q($x * $subject)
  let xMulZero : Q($α) := q($x * $zero)
  let h1 : Q($xMulSubject = $xMulZero) :=
    q(congrArg (fun y => $x * y) $subjectZero)
  let h2 : Q($xMulZero = 0) := q(mul_zero $x)
  let proof : Q($xMulSubject = 0) := q(Eq.trans $h1 $h2)
  return zeroCertOfProof proof

/-- Cache certificates that are reused by the recursive Bird evaluator. -/
structure CertCache {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- Cache for entry certificates, keyed by matrix indices. -/
  entryCache : Std.HashMap (Nat × Nat) (Cert rα) := {}
  /-- Cache for `iter` certificates, keyed by recursion index and matrix indices. -/
  iterCache : Std.HashMap (Nat × Nat × Nat) (Cert rα) := {}
  /-- Cache for diagonal-tail certificates, keyed by recursion index and lower bound. -/
  diagCache : Std.HashMap (Nat × Nat) (Cert rα) := {}

/-- Monad used while constructing certificates for one determinant. -/
abbrev CertM {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) :=
  StateT (CertCache rα) (ReaderT (Ctx rα) AtomM)

/-- Certify `e = norm` by evaluating `e` with the `ring` normalizer.

This is the leaf operation for scalar expressions that do not need a Bird
unfolding step first.
-/
def certEval (e : Q($α)) : CertM rα (Cert rα) := do
  let ctx ← read
  let res ← Common.eval rcℕ ctx.rc ctx.cα e
  return toCert res

/-- Certify `a.subject + b.subject` from certificates for `a` and `b`.

The returned certificate uses `Common.evalAdd` to normalize `a.norm + b.norm`
and proves the subject equality by lifting `a.proof` and `b.proof` through `+`.
-/
def certAdd (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalAdd ctx.rc rcℕ a.val b.val
  -- Lift `a.proof` and `b.proof` through the binary `+` in the RHS exposed by
  -- `BirdDet.sumFrom_step` and `BirdDet.iter_succ`.
  let aSubject : Q($α) := a.subject
  let bSubject : Q($α) := b.subject
  let aProof : Q($aSubject = $a.norm) := a.proof
  let bProof : Q($bSubject = $b.norm) := b.proof
  let h : Q($aSubject + $bSubject = $a.norm + $b.norm) :=
    q(congr (congrArg (fun x y => x + y) $aProof) $bProof)
  return c.chainProof h

/-- Certify `a.subject * b.subject` from certificates for `a` and `b`.

The returned certificate uses `Common.evalMul` to normalize `a.norm * b.norm`
and proves the subject equality by lifting `a.proof` and `b.proof` through `*`.
-/
def certMul (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalMul ctx.rc rcℕ a.val b.val
  -- Lift sub-certificates through the products appearing in `BirdDet.iter_succ`
  -- and the final `BirdDet.birdDet_eq` formula.
  let aSubject : Q($α) := a.subject
  let bSubject : Q($α) := b.subject
  let aProof : Q($aSubject = $a.norm) := a.proof
  let bProof : Q($bSubject = $b.norm) := b.proof
  let h : Q($aSubject * $bSubject = $a.norm * $b.norm) :=
    q(congr (congrArg (fun x y => x * y) $aProof) $bProof)
  return c.chainProof h

/-- Certify `-a.subject` from a certificate for `a`.

The returned certificate uses `Common.evalNeg` to normalize `-a.norm` and
proves the subject equality by lifting `a.proof` through unary negation.
-/
def certNeg (a : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
  let c ← toCert <$> Common.evalNeg ctx.rc rα a.val
  -- Lift a certificate through the leading negation of the diagonal sum in
  -- `BirdDet.iter_succ`.
  let aSubject : Q($α) := a.subject
  let aProof : Q($aSubject = $a.norm) := a.proof
  let h : Q(-$aSubject = -$a.norm) :=
    q(congrArg (fun x => -x) $aProof)
  return c.chainProof h

/-- Certify the sign factor `(-1)^k` from `BirdDet.birdDet_eq`.

This is a direct `ring` leaf certificate used by the nonzero branch of
`certBirdDet`.
-/
def certBirdSign (k : Nat) : CertM rα (Cert rα) := do
  certEval q((-1 : $α) ^ $k)

/-- Certify one matrix entry lookup `BirdDet.get n A i j`.

```
get n A i j = elem  -- By the definition of `BirdDet.get` in `Bird.lean`
            = norm  -- Ring.eval on the entry
```

`BirdDet.get` reads the flat row-major array with `Array.getD`. The reifier has
already checked that the array argument is a literal, so `entry` is the literal
cell at index `i * n + j`.
-/
def certEntry (i j : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  have dim : Q(Nat) := ctx.info.dimensionExpr
  have A : Q(Array $α) := ctx.info.arrayExpr
  let lhs : Q($α) := q(BirdDet.get $dim $A $i $j)
  let idx := i * ctx.info.dimension + j
  let entry : Q($α) := ctx.info.arrayEntries.getD idx q(0)
  let ce ← certEval entry
  -- This `rfl` is the unfolding of `BirdDet.get`.
  have : $lhs =Q $entry := ⟨⟩
  let h : Q($lhs = $entry) := q(rfl)
  let cert := ce.chainProof h
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

/-- Certify the stop branch of `BirdDet.sumFrom`.

This corresponds to the `else 0` branch of:

```
sumFrom n lo f = if lo < n then f lo + sumFrom n (lo + 1) f else 0
```

from `Bird.lean`.
-/
def certSumFromStop (lo : Nat) (f : Q(Nat → $α)) : CertM rα (Cert rα) := do
  let ctx ← read
  have dim : Q(Nat) := ctx.info.dimensionExpr
  let hNot : Q(¬ $lo < $dim) ← mkDecideProofQ q(¬ $lo < $dim)
  let proof := q(BirdDet.sumFrom_stop $dim $lo $f $hNot)
  return zeroCertOfProof proof

/-- Certify the step branch of `BirdDet.sumFrom`.

The theorem `BirdDet.sumFrom_step` exposes the RHS
`f lo + sumFrom n (lo + 1) f`. The two recursive certificates supplied by the
caller certify exactly those two summands, and `certAdd` normalizes their sum.
-/
def certSumFromStep
    (lo : Nat) (f : Q(Nat → $α))
    (headCert tailCert : CertM rα (Cert rα)) : CertM rα (Cert rα) := do
  let ctx ← read
  have dim : Q(Nat) := ctx.info.dimensionExpr
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let head ← headCert
  let tail ← tailCert
  let sumCert ← certAdd head tail
  let h := q(BirdDet.sumFrom_step $dim $lo $f $hLt)
  return sumCert.chainProof h

mutual

/-- Certify one entry of `BirdDet.iter`.

The subject is:

```
iter n A t (get n A) i j
```

For `t = 0`, this uses `BirdDet.iter_zero` and delegates to `certEntry`. For
`t = t' + 1`, this uses `BirdDet.iter_succ`, certifies the two summands, then
normalizes their sum.

```
iter n A (t' + 1) F_0 i j
  = -(sumFrom n (i + 1) fun k => F_t k k) * get n A i j
      + sumFrom n (i + 1) fun k => F_t i k * get n A k j
                                      -- BirdDet.iter_succ
  = norm                              -- certAdd diagProdCert tailSumCert
```

The first summand is certified by `certDiag`, `certNeg`, `certEntry`, and
`certMul`. If `get n A i j` certifies to zero, `zeroProdCert` skips the
diagonal sum entirely. The second summand is certified by `certTail`.

-/
partial def certIter (t i j : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).iterCache[(t, i, j)]? then
    return c
  let ctx ← read
  let cert ← match t with
    | 0 => do
      -- `BirdDet.iter_zero` is the `| 0 => F` branch of `BirdDet.iter`.
      let ce ← certEntry i j
      have dim : Q(Nat) := ctx.info.dimensionExpr
      have A : Q(Array $α) := ctx.info.arrayExpr
      let h := q(BirdDet.iter_zero $dim $A (BirdDet.get $dim $A) $i $j)
      pure (ce.chainProof h)
    | t' + 1 => do
      -- First summand in `BirdDet.iter_succ`:
      --   -(sumFrom n (i + 1) fun k => F_t k k) * get n A i j
      let diagSummand := q(fun k => $(ctx.iterP t') k k)
      let negDiagSum :=
        q(-$(ctx.sumFrom (i + 1) diagSummand))
      let entryCert ← certEntry i j
      let diagProdCert ←
        if entryCert.isZero then
          zeroProdCert negDiagSum entryCert
        else do
          let diagSumCert ← certDiag t' (i + 1)
          let negDiagSumCert ← certNeg diagSumCert
          certMul negDiagSumCert entryCert
      -- Second summand in `BirdDet.iter_succ`:
      --   sumFrom n (i + 1) fun k => F_t i k * get n A k j
      let tailSumCert ← certTail t' i j (i + 1)
      let rhsCert ← certAdd diagProdCert tailSumCert
      have dim : Q(Nat) := ctx.info.dimensionExpr
      have A : Q(Array $α) := ctx.info.arrayExpr
      let h := q(BirdDet.iter_succ $dim $A $t' (BirdDet.get $dim $A) $i $j)
      pure (rhsCert.chainProof h)
  modify fun s => {s with iterCache := s.iterCache.insert (t, i, j) cert}
  return cert


/-- Certify the diagonal tail sum from the first summand of `BirdDet.iter_succ`.

The subject is:

```
sumFrom n lo (fun k => iter n A t (get n A) k k)
```

It certifies that:

```
sumFrom n lo diagFun =
  if lo < n then
    diagFun lo + sumFrom n (lo + 1) diagFun   -- BirdDet.sumFrom_step
  else
    0                                         -- BirdDet.sumFrom_stop
```

In the step branch, `diagFun lo` is certified by `certIter t lo lo`, the
remaining tail is certified recursively by `certDiag t (lo + 1)`, and
`certSumFromStep` combines those certificates with `certAdd`.
-/
partial def certDiag (t lo : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterP t) k k)
  let cert ←
    if lo < ctx.info.dimension
    then do
      -- Bird term: `sumFrom n lo fun k => F_t k k`; this is the diagonal
      -- `sumFrom` in the first summand of `BirdDet.iter_succ`.
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

/-- Certify the upper-tail sum from the second summand of `BirdDet.iter_succ`.

The subject is:

```
sumFrom n lo (fun k => iter n A t (get n A) i k * get n A k j)
```

It certifies that:

```
sumFrom n lo f =
  if lo < n then
    f lo + sumFrom n (lo + 1) f   -- BirdDet.sumFrom_step
  else
    0                             -- BirdDet.sumFrom_stop
```

In the step branch, `f lo` reduces to `F_t i lo * get n A lo j`, so the head
term can be certified by `certIter`, `certEntry`, and `certMul`:

```
F_t i lo * get n A lo j = norm
```

If `get n A lo j` certifies to zero, `zeroProdCert` avoids certifying `F_t i lo`.
The remaining tail is certified recursively by `certTail t i j (lo + 1)`, and
`certSumFromStep` combines the head and tail certificates with `certAdd`.

-/
partial def certTail (t i j lo : Nat) : CertM rα (Cert rα) := do
  let ctx ← read
  have dim : Q(Nat) := ctx.info.dimensionExpr
  have A : Q(Array $α) := ctx.info.arrayExpr
  let tailSummand :=
    q(fun k =>
      $(ctx.iterP t) $i k *
        BirdDet.get $dim $A k $j)
  if lo < ctx.info.dimension
  then do
    -- Bird term: `sumFrom n lo fun k => F_t i k * get n A k j`; this is the
    -- second summand in `BirdDet.iter_succ`.
    let headCert := do
      -- Certify `F_t i lo * get n A lo j`.
      let entryCert ← certEntry lo j
      -- If `get n A lo j = 0`, avoid certifying `F_t i lo`.
      if entryCert.isZero
      then
        zeroProdCert
          q($(ctx.iterP t) $i $lo)
          entryCert
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

/-- Certify a top-level `BirdDet.birdDet n A` call.

This follows the two branches of the definition in `Bird.lean`:

```
birdDet 0 A       = 1
birdDet (k + 1) A = (-1)^k * iter (k + 1) A k (get (k + 1) A) 0 0
```
-/
def certBirdDet : CertM rα (Cert rα) := do
  let ctx ← read
  if ctx.info.dimension == 0
  then
    -- `BirdDet.birdDet_zero` is the `| 0 => 1` branch.
    let ce ← certEval q(1 : $α)
    have dim : Q(Nat) := ctx.info.dimensionExpr
    have : $dim =Q 0 := ⟨⟩
    have A : Q(Array $α) := ctx.info.arrayExpr
    let h := q(BirdDet.birdDet_zero $A)
    return ce.chainProof h
  else
    -- The non-zero `BirdDet.birdDet_eq` branch matches `k + 1`
    -- so we set k := `ctx.info.dimension - 1`.
    let k := ctx.info.dimension - 1
    let cs ← certBirdSign k
    let ci ← certIter k 0 0
    let cm ← certMul cs ci
    have dim : Q(Nat) := ctx.info.dimensionExpr
    have kLit := mkNatLitQ k
    have : $dim =Q $kLit + 1 := ⟨⟩
    let hn : Q($dim = $kLit + 1) := q(rfl)
    have A : Q(Array $α) := ctx.info.arrayExpr
    let h := q(BirdDet.birdDet_eq $dim $kLit $A $hn)
    return cm.chainProof h

end Cert


end
