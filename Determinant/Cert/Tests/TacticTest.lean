module

public meta import Determinant.Cert.Tactic

import Lean
import Qq

namespace Cert

open Lean Meta Qq

-- Test destructMul?
run_meta do
  let m := q((2 : ℤ) * 3)
  let some app := destructMul? m
    | throwError m!"{m} is not a multiplication"
  let recombined := mkApp2 app.partialApp app.x app.y
  let value ← reduce recombined
  unless (← isDefEq value q((6 : ℤ))) do
    throwError m!"expected {recombined} to reduce to 6, got {value}"

-- Test destructAdd?
run_meta do
  let m := q((2 : ℤ) + 3)
  let some app := destructAdd? m
    | throwError m!"{m} is not an addition"
  let recombined := mkApp2 app.partialApp app.x app.y
  let value ← reduce recombined
  unless (← isDefEq value q((5 : ℤ))) do
    throwError m!"expected {recombined} to reduce to 5, got {value}"

-- Test destructNeg?
run_meta do
  let m := q(-(2 : ℤ))
  let some app := destructNeg? m
    | throwError m!"{m} is not a negation"
  let recombined := mkApp app.partialApp app.x
  let value ← reduce recombined
  unless (← isDefEq value q((-2 : ℤ))) do
    throwError m!"expected {recombined} to reduce to -2, got {value}"

-- Test mkLtProof
run_meta do
  let expected : Q(Prop) := q(1 < (2 : Nat))
  let pf ← mkLtProof 1 2
  let actual ← inferType pf
  unless (← isDefEq actual expected) do
    throwError m!"expected proof of {expected}, got proof of {actual}"

-- Test mkNotLtProof
run_meta do
  let expected : Q(Prop) := q(¬ 2 < (1 : Nat))
  let pf ← mkNotLtProof 2 1
  let actual ← inferType pf
  unless (← isDefEq actual expected) do
    throwError m!"expected proof of {expected}, got proof of {actual}"

end Cert
