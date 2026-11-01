import rcic.RcicF3EvalPlanValue
import rcic.RcicF3PropEvalValueAttack

/-!
# The production planned endpoint and member application at actual AccR

This fixture uses the admission-produced Plan of the actual AccR node.
Its production endpoint is literally the new bounded indexed value at the
full recursor valuation. The new member abstraction, applied to the actual
typed parameter, motive, minor and major, computes to that endpoint and
satisfies iota with the generated typed IH.

The produced read support also proves invariance under an arbitrary update
of the recursor's own fresh slot. The old recEnd and every old planned
endpoint remain extensionally different because they miss the same target
type. Only this actual application is claimed; universal member typing,
universal StepAG and the checked apex remain unpaid. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPlanValueAttack
open Rcic.Declarative PiIndex PlanPropEndAttack
open PropEvalUniqueAttack (ctx)

noncomputable def plan : EvalPlan.Plan := EvalPlan.ofNode PlanPropStepAttack.pNode

/-- Exact slicing reconstructs the already fixed actual evaluation context. -/
theorem context_at (P : Premises4) :
    EvalPlanValue.context plan (ctx P).M (ctx P).σ (input P (installed P)) = ctx P := by
  rfl

/-- The production branch returns the bounded indexed value itself. -/
theorem endpoint_eq (P : Premises4) :
    EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)) =
      PropEvalValueAttack.result P := by
  rw [EvalPlanValue.endValue_prop (ctx P).M (ctx P).σ plan _ rfl rfl]
  rw [context_at P]
  rfl

theorem endpoint_typed (P : Premises4) :
    EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)) ∈
      Ed (ctx P).M (fapp (motive P (installed P)) pempty) := by
  rw [endpoint_eq P]
  exact PropEvalValueAttack.result_typed P

theorem endpoint_nonempty (P : Premises4) :
    ¬ Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      pempty := by
  rw [endpoint_eq P]
  exact PropEvalValueAttack.result_nonempty P

/-- Actual endpoint iota consumes the field and the generated typed IH. -/
theorem endpoint_iota (P : Premises4) :
    Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      (fapps (minor P (installed P)) [pempty, PropEvalValueAttack.ihValue P]) := by
  rw [endpoint_eq P]
  exact PropEvalValueAttack.iota P

/-- The actual recursor arguments fit the stored recursor telescope. -/
theorem arguments_fit (P : Premises4) :
    TelFits (ctx P).M (ctx P).σ
      [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
      [parameter, motive P (installed P), minor P (installed P), pempty] :=
  ⟨mem_congr_right (ed_tyv (ctx P).M (U4_dich 0)).symm (parameter_mem P),
    motive_mem P (installed P),
    minor_mem P (installed P) (installed_family P) (installed_constructor P),
    major_mem P (installed P) (installed_family P), True.intro⟩

/-- The new production member actually reaches the replacement endpoint. -/
theorem member_application (P : Premises4) :
    Equiv (fapps (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember)
      [parameter, motive P (installed P), minor P (installed P), pempty])
      (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P))) := by
  exact fapps_piLam (ctx P).M (ctx P).σ
    (EvalPlanValue.endValue_resp (ctx P).M (ctx P).σ plan)
    (.app (.bvar 2) (.bvar 0))
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
    [parameter, motive P (installed P), minor P (installed P), pempty] (arguments_fit P)

theorem application_typed (P : Premises4) :
    fapps (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember)
      [parameter, motive P (installed P), minor P (installed P), pempty] ∈
      Ed (ctx P).M (fapp (motive P (installed P)) pempty) :=
  mem_congr_left (member_application P).symm (endpoint_typed P)

/-- Iota is checked at the actual new member application, not only a helper. -/
theorem member_iota (P : Premises4) :
    Equiv (fapps (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember)
      [parameter, motive P (installed P), minor P (installed P), pempty])
      (fapps (minor P (installed P)) [pempty, PropEvalValueAttack.ihValue P]) :=
  (member_application P).trans (endpoint_iota P)

/-- Actual admission, including the original normalized reads, pays the
entire fresh-update read law without a support callback. -/
theorem fresh_update (P : Premises4) (X : List Nat → PSet.{4}) :
    Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      (EvalPlanValue.endValue (mkM P (upd (installed P) 2 X)) (ctx P).σ plan
        (input P (installed P))) := by
  exact EvalPlanValue.endValue_agreeOn_group P (installed P) (upd (installed P) 2 X)
    plan (ctx P).σ accFamMember [(1, accIntroMember)] .empty rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT
    (agreeOn_upd PlanPropStepAttack.pNode.fresh (installed P) X) (input P (installed P))

/-- The old operation still fails the exact target inhabited by the new endpoint. -/
theorem endpoint_not_recEnd (P : Premises4) :
    ¬ Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      (recEnd (ctx P).M (ctx P).σ fd (input P (installed P))) := by
  intro he
  exact PropEvalValueAttack.old_recEnd_not_mem P (mem_congr_left he (endpoint_typed P))

theorem endpoint_not_old_plan (P : Premises4) (old : List (List FieldShape)) :
    ¬ Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      (RecPlanValue.endValue (ctx P).M (ctx P).σ fd old (input P (installed P))) := by
  intro he
  exact endpoint_not_mem P (installed P) (installed_family P) old
    (mem_congr_left he (endpoint_typed P))

def Witness (P : Premises4) : Prop :=
  PropEvalValueAttack.Witness P ∧
  EvalPlanValue.context plan (ctx P).M (ctx P).σ (input P (installed P)) = ctx P ∧
  EnvResp (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan) ∧
  EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)) ∈
    Ed (ctx P).M (fapp (motive P (installed P)) pempty) ∧
  fapps (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember)
    [parameter, motive P (installed P), minor P (installed P), pempty] ∈
      Ed (ctx P).M (fapp (motive P (installed P)) pempty) ∧
  Equiv (fapps (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember)
    [parameter, motive P (installed P), minor P (installed P), pempty])
    (fapps (minor P (installed P)) [pempty, PropEvalValueAttack.ihValue P]) ∧
  (∀ X : List Nat → PSet.{4},
    Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      (EvalPlanValue.endValue (mkM P (upd (installed P) 2 X)) (ctx P).σ plan
        (input P (installed P)))) ∧
  ¬ Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
    pempty ∧
  ¬ Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
    (recEnd (ctx P).M (ctx P).σ fd (input P (installed P))) ∧
  ∀ old : List (List FieldShape),
    ¬ Equiv (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
      (RecPlanValue.endValue (ctx P).M (ctx P).σ fd old (input P (installed P)))

/-- All read, application, iota and failure-separation conjuncts are produced. -/
theorem component_witness (P : Premises4) : Witness P :=
  ⟨PropEvalValueAttack.component_witness P, context_at P,
    EvalPlanValue.endValue_resp (ctx P).M (ctx P).σ plan, endpoint_typed P,
    application_typed P, member_iota P, fresh_update P, endpoint_nonempty P,
    endpoint_not_recEnd P, endpoint_not_old_plan P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalPlanValueAttack
