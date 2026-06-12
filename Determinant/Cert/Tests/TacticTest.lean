module

public meta import Determinant.Cert.Tactic

import Lean
import Qq

namespace Cert

open Lean Meta Qq

run_meta do
  let m := q((2 : ℤ) * 3)
  let some app := destructMul? m
    | throwError m!"{m} is not a multiplication"
  let recombined := mkApp2 app.partialApp app.x app.y
  let value ← reduce recombined
  unless (← isDefEq value q((6 : ℤ))) do
    throwError m!"expected {recombined} to reduce to 6, got {value}"

run_meta do
  let m := q((2 : ℤ) + 3)
  let some app := destructAdd? m
    | throwError m!"{m} is not an addition"
  let recombined := mkApp2 app.partialApp app.x app.y
  let value ← reduce recombined
  unless (← isDefEq value q((5 : ℤ))) do
    throwError m!"expected {recombined} to reduce to 5, got {value}"

run_meta do
  let m := q(-(2 : ℤ))
  let some app := destructNeg? m
    | throwError m!"{m} is not a negation"
  let recombined := mkApp app.partialApp app.x
  let value ← reduce recombined
  unless (← isDefEq value q((-2 : ℤ))) do
    throwError m!"expected {recombined} to reduce to -2, got {value}"

end Cert
