module

public import Determinant.Cbv.Simproc
public import Determinant.Cbv.CbvOpaqueDefs
public import Determinant.Cbv.Bird
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

open Lean Meta Elab Tactic
open CbvOpaqueDefs

syntax "cbv_bird_entry_det" : tactic
elab_rules : tactic
  | `(tactic| cbv_bird_entry_det) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some (_, lhs, _) := target.eq?
      | throwError "cbv_bird_det: Expected an equality goal"
    unless lhs.isAppOf' ``Bird.birdDetEntry do
      throwError m!"cbv_bird_entry_det: expected lhs: {lhs} to be an application of Bird.birdDetEntry"
    evalTactic (← `(tactic|
      conv_lhs =>
        cbv
        simp only [rzero, rone, radd, rmul, rneg, rpow, rint, rsub, rdiv, ratom]))
    evalTactic (← `(tactic| try ring_nf))

syntax "cbv_bird_det" : tactic
elab_rules : tactic
  | `(tactic| cbv_bird_det) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some (_, lhs, _) := target.eq?
      | throwError "cbv_bird_det: Expected an equality goal"
    unless lhs.isAppOf' ``Bird.birdDet do
      throwError m!"cbv_bird_det: expected lhs: {lhs} to be an application of Bird.birdDet"
    evalTactic (← `(tactic|
      conv_lhs =>
        cbv
        simp only [rzero, rone, radd, rmul, rneg, rpow, rint, rsub, rdiv, ratom]))
    evalTactic (← `(tactic| try ring_nf))
