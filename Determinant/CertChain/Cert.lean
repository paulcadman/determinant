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
  val : Common.ExSum RatCoeff sα norm
  /-- Proof that the `subject` is equal to the `norm` -/
  proof : Expr
  /-- `true` when `norm` is zero -/
  isZero : Bool

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {sα : Q(CommSemiring $α)}

def isZeroVal {e : Q($α)} (val : Common.ExSum RatCoeff sα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

structure EqProof where
  lhs : Expr
  rhs : Expr
  proof : Expr

/-- Repackage a `Ring` evaluation result as a certificate. -/
def toCert {e : Q($α)} (res : Common.Result (Common.ExSum RatCoeff sα) e) : Cert sα :=
  { norm := res.expr, val := res.val, proof := res.proof, isZero := isZeroVal res.val }

/-- Cast an existing `proof : subject = 0` as a certificate for the cannonical zero -/
def zeroCertOf (subject proof : Expr) : MetaM (Cert sα) := do
  let zero : Q($α) := q(0)
  let proof ← mkExpectedTypeHint proof (← mkEq subject zero)
  return {norm := zero, val := .zero, proof, isZero := true}

/-- Given `cz.proof : cz.subject! = 0`, certify the product `x * cz.subject =
  0` without evaluating `x`.

`mulP` is HMul.hmul, partially applied with types and instances (see
`destructMul?`).
-/
def zeroProdCert (mulP x : Expr) (cz : Cert sα) : MetaM (Cert sα) := do
  -- x * (cz.subject) = x * 0
  let h1 ← mkCongrArg (mkApp mulP x) cz.proof
  -- x * 0 = 0
  let h2 ← mkAppM ``mul_zero #[x]
  -- x * (cz.subject) = 0
  let h ← mkEqTrans h1 h2
  let some (_, lhs, _) := (← inferType h1).eq? | unreachable!
  zeroCertOf lhs h

/-- Extract the certificate's subject

Used for tests and debugging-/
def subject! (c : Cert sα) : MetaM Expr := do
  let some (_, lhs, _) := (← inferType c.proof).eq?
    | throwError "Cert.subject!: proof is not an equality: {c.proof}"
  return lhs

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

structure AppResult {u : Level} (α : Q(Type u)) where
  /-- The application expression -/
  app : Q($α)
  /-- The result of the application -/
  result : Q($α)
  /-- A proof that app and result are equal -/
  proof : Q($app = $result)

namespace Ctx

def applyEqLemma (name : Name) (u : Level) (args : Array Expr) : MetaM EqProof := do
  let proof := mkAppN (mkConst name [u]) args
  let some (_, lhs, rhs) := (← inferType proof).eq?
    | throwError "Ctx.applyEqLemma: {name} did not produce an equality"
  return {lhs, rhs, proof}

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
def get (ctx : Ctx sα) (i j : Nat) : MetaM (AppResult α) := do
  let app := mkApp2 ctx.getP (mkNatLit i) (mkNatLit j)
  let idx := i * ctx.dimension + j
  let zero : Q($α) := q(0)
  let result := ctx.arrayEntries.getD idx zero
  let app : Q($α) := app
  let result : Q($α) := result
  let proof ← mkExpectedTypeHint (← mkEqRefl result) (← mkEq app result)
  return {app, result, proof}

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

end Ctx

abbrev CertM {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) :=
  ReaderT (Ctx sα) AtomM

/-- Returns a certificate whose subject is `get n A i j`.

```
get n A i j = elem  -- By rfl
            = norm  -- Ring.eval on the entry
```
-/
def certEntry (i j : Nat) : CertM sα (Cert sα) := do
  let ctx ← read
  let elemApp ← ctx.get i j
  let ce ← ctx.eval elemApp.result
  let proof ← mkExpectedTypeHint (← mkEqTrans elemApp.proof ce.proof) (← mkEq elemApp.app ce.norm)
  return {ce with proof}


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
  let ctx ← read
  match t with
  | 0 => do
    -- iter n A 0 (get n A) = get n
    let iterZeroPf ← Ctx.applyEqLemma ``iter_zero u #[
      (α : Expr), ctx.commRingInst, ctx.dimensionExpr, ctx.array, ctx.getP, mkNatLit i, mkNatLit j]
    let ce ← certEntry i j
    return { ce with proof := ← mkEqTrans iterZeroPf.proof ce.proof }
  | t' + 1 => do
    let iterSuccPf ← Ctx.applyEqLemma ``iter_succ u #[
      (α : Expr), ctx.commRingInst, ctx.dimensionExpr, ctx.array, mkNatLit t', ctx.getP,
      mkNatLit i, mkNatLit j]
    let some ⟨addP, dTerm, tSum⟩ := Meta.destructAdd? iterSuccPf.rhs 
      | throwError "certIter: Expected add, got {iterSuccPf.rhs}"
    let some ⟨mulP, negS, _⟩ := Meta.destructMul? dTerm 
      | throwError "certIter: Expected mul, got {dTerm}"
    let some ⟨negP, _⟩ := Meta.destructNeg? negS 
      | throwError "certIter: Expected neg, got {negS}"
    -- A[i,j]
    let ce ← certEntry i j
    let cd ← 
      if ce.isZero then
        zeroProdCert mulP negS ce
      else do
        let cdiag ← certDiag t' (i + 1)
        let cneg ← ctx.evalNeg cdiag
        let h1 ← Meta.mkCongrBinop mulP (← mkCongrArg negP cdiag.proof) ce.proof
        let h2 ← mkCongrFun (← mkCongrArg mulP cneg.proof) ce.norm
        let cm ← ctx.evalMul cneg ce
        pure {cm with proof := ← Meta.trans3 h1 h2 cm.proof}
    let_expr sumFrom _ _ _ _ f := tSum
      | throwError "certIter: expected sumFrom ... got {tSum}"
    let ct ← certTail t' i j (i + 1) f mulP
    let hAdd ← Meta.mkCongrBinop addP cd.proof ct.proof
    let cs ← ctx.evalAdd cd ct
    return {cs with proof := ← Meta.trans3 iterSuccPf.proof hAdd cs.proof}


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
  let ctx ← read
  if lo < ctx.dimension
  then do
    let hLt ← Meta.mkLtProof lo ctx.dimension
    let stepEq ← Ctx.applyEqLemma ``sumFrom_step u #[
      (α : Expr), ctx.commRingInst, ctx.dimensionExpr, mkNatLit lo, ctx.diagFun t, hLt]
    let some addP := Meta.destructAdd? stepEq.rhs
      | throwError "certDiag: unexpected rhs of sumFrom_step {stepEq.rhs}"
    let ci ← certIter t lo lo
    let cd ← certDiag t (lo + 1)
    let hAdd ← Meta.mkCongrBinop addP.partialApp ci.proof cd.proof
    let cs ← ctx.evalAdd ci cd
    return { cs with proof := ← Meta.trans3 stepEq.proof hAdd cs.proof }
  else do
    let hNot ← Meta.mkNotLtProof lo ctx.dimension
    let eqProof ←
      Ctx.applyEqLemma ``sumFrom_stop u #[
        (α : Expr), ctx.commRingInst, ctx.dimensionExpr, mkNatLit lo, ctx.diagFun t, hNot]
    zeroCertOf eqProof.lhs eqProof.proof

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
    let hLt ← Meta.mkLtProof lo ctx.dimension
    let stepEq ← Ctx.applyEqLemma ``sumFrom_step u #[
      (α : Expr), ctx.commRingInst, ctx.dimensionExpr, mkNatLit lo, f, hLt]
    let some addP := Meta.destructAdd? stepEq.rhs
      | throwError "certTail: unexpected rhs of sumFrom_step {stepEq.rhs}"
    -- Certify F_t[i,lo] * A[lo,j]
    let ce_lo_j ← certEntry lo j
    let cp ←
      -- If A[lo,j] = 0 then we can avoid computing the product
      if ce_lo_j.isZero
      then zeroProdCert mulP (mkApp2 (ctx.iterP t) (mkNatLit i) (mkNatLit lo)) ce_lo_j
      else do
        let ci ← certIter t i lo
        let hP ← Meta.mkCongrBinop mulP ci.proof ce_lo_j.proof
        let cm ← ctx.evalMul ci ce_lo_j
        pure {cm with proof := ← mkEqTrans hP cm.proof}
    let ct ← certTail t i j (lo + 1) f mulP
    let hAdd ← Meta.mkCongrBinop addP.partialApp cp.proof ct.proof
    let cs ← ctx.evalAdd cp ct
    return {cs with proof := ← Meta.trans3 stepEq.proof hAdd cs.proof}
  else do
    let hNot ← Meta.mkNotLtProof lo ctx.dimension
    let eqStop ← Ctx.applyEqLemma ``sumFrom_stop u #[
      (α : Expr), ctx.commRingInst, ctx.dimensionExpr, mkNatLit lo, f, hNot]
    zeroCertOf eqStop.lhs eqStop.proof

end

def certBirdDet : CertM sα (Cert sα) := do
  let ctx ← read
  if ctx.dimension == 0
  then
    let birdDetZeroPf ← Ctx.applyEqLemma ``birdDet_zero u #[
      (α : Expr), ctx.commRingInst, ctx.array]
    let ce ← ctx.eval birdDetZeroPf.rhs
    return {ce with proof := ← mkEqTrans birdDetZeroPf.proof ce.proof}
  else
    let k := ctx.dimension - 1
    let kSucc ← mkAppM ``HAdd.hAdd #[mkNatLit k, mkNatLit 1]
    let hn ← mkExpectedTypeHint (← mkEqRefl ctx.dimensionExpr) (← mkEq ctx.dimensionExpr kSucc)
    let birdDetEq ← Ctx.applyEqLemma ``birdDet_eq u #[α, ctx.commRingInst, ctx.dimensionExpr, mkNatLit k, ctx.array, hn]
    let some ⟨mulP, s, _⟩ := Meta.destructMul? birdDetEq.rhs
      | throwError "certBirdDet: expected mul, got: {birdDetEq.rhs}"
    let cs ← ctx.eval s
    let ci ← certIter k 0 0
    let h1 ← Meta.mkCongrBinop mulP cs.proof ci.proof
    let cm ← ctx.evalMul cs ci
    return {cm with proof := ← Meta.trans3 birdDetEq.proof h1 cm.proof}

end Cert


end
