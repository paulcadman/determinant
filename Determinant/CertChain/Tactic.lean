module

public import Determinant.CertChain.Meta
public import Determinant.CertChain.Cert
public import Mathlib.Tactic.Ring
import Qq

open Lean Meta Elab Tactic
open Qq
open Mathlib.Tactic.Ring
open Mathlib.Tactic (AtomM)
open Cert

syntax "cert_bird_det" : tactic

elab_rules : tactic
  | `(tactic| cert_bird_det) => withMainContext do
    let g ← getMainGoal
    let target ← getMainTarget
    let some (_, lhs, rhs) := target.eq?
      | throwError "cert_bird_det: Expected an equality goal"
    let info ← Meta.reifyBirdDet lhs
    let u : Level := info.level
    let α : Q(Type u) := info.ringType
    let sα : Q(CommSemiring $α) ← synthInstanceQ q(CommSemiring $α)
    let cα ← Common.mkCache sα
    let some rα := cα.rα
      | throwError "cert_bird_det: `CommRing {α}` instance required"
    let getP := mkAppN (mkConst ``BirdDet.get [u]) #[info.ringType, info.commRingInst, info.dimensionExpr, info.arrayExpr]
    let ctx : Ctx sα := {
      rα,
      cα,
      rc := ringCompute cα,
      commRingInst := info.commRingInst
      dimension := info.dimension
      dimensionExpr := info.dimensionExpr
      array := info.arrayExpr
      arrayEntries := info.arrayEntries
      getP,
    }
    let detNorm ← certBirdDet.run' {} |>.run ctx |>.run .reducible
    let some rhs ← checkTypeQ rhs α
      | throwError "cert_bird_det: RHS does not have expected type{indentExpr α}"
    let .mvar residualGoal ← mkFreshExprMVar (← mkEq detNorm.norm rhs)
      | throwError "cert_bird_det: failed to create residual goal"
    g.assign (← mkEqTrans detNorm.proof (mkMVar residualGoal))
    replaceMainGoal [residualGoal]
    evalTactic (← `(tactic| try norm_num))
    evalTactic (← `(tactic| try ring))
