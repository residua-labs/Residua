import rcic.RcicF3IndexedPropEvalValue
import rcic.RcicF3NormPropEvalAttack

/-!
# Same-P composition for the separate indexed-bound evaluation producer

Each producer is invoked on the actual admitted AccR fixture at its fixed
normalized-role table. Its predecessor is empty, so the new pointwise
predecessor and its faithfulness inputs are produced directly. No equality
of universal role invariants or completed-group soundness is assumed.

The original AccR bound implies the new bound. The same-P field-bound
witness also retains the separate AccP typed-row witness and its refuted
old all-Prop bound; it is not a BoundGIndexed proof for the whole AccP
environment. The AccR motive universe is 1 and its selected recursive
child domain is empty. Neither fixture is identified with imported Acc.

The installed equation below is the existing concrete AccR equation with
its actual typed indexed IH. It does not supply universal modern recursive
shape-schema iota, or the separate plain-field iota bridge. The checked
tier and its root have not been changed by these local producer modules.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.IndexedPropEvalAttack
open Rcic.Declarative PiIndex PiValueRule RawFamily PropEval PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalAdmittedInputsAttack (bound)
open NormPropEvalAttack (μ C X result)

theorem constructors :
    ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

/-- This is the actual complete AccR bound, obtained by the proved
broadening direction. It is not a whole-environment AccP bound. -/
theorem indexed_bound :
    IndexedFieldBounds.BoundGIndexed bound AccEnv.accEnvWfT :=
  IndexedFieldBounds.of_boundG bound AccEnv.accEnvWfT
    (PlanPropStepAttack.boundG bound)

/-- Only the existing fixture's family equation is used. The new producer
needs faithfulness on its empty predecessor, not on the completed group. -/
theorem family_equation (P : Premises4) :
    ∀ vs, Equiv (μ P (C P).node.a.family.ref vs)
      (ofFrame P (μ P) (famDataOf (C P).node.a)
        (NormPropEval.base P (μ P) (C P)) vs) := by
  intro vs
  have h := (NormRole.table_spec P AccEnv.accEnvWfT).1 0 accFamMember rfl vs
  rw [(NormRoleTableAttack.component_witness P).1] at h
  exact h

theorem parameters_fit (P : Premises4) :
    TelFits (C P).M (C P).σ (C P).node.a.family.parameters ρ0 (C P).parameters :=
  ⟨(NormPropEvalAttack.arguments_fit P).1, True.intro⟩

theorem motive_fits (P : Premises4) :
    (C P).motive ∈ Ed (C P).M (den (C P).M (C P).σ
      (push (C P).parameters ρ0) accMotTy) :=
  (NormPropEvalAttack.arguments_fit P).2.1

theorem minors_fit (P : Premises4) :
    TelFits (C P).M (C P).σ (C P).node.a.minorTypes
      (vcons (C P).motive (push (C P).parameters ρ0)) (C P).minors :=
  ⟨(NormPropEvalAttack.arguments_fit P).2.2.1, True.intro⟩

theorem major_fits (P : Premises4) :
    pempty ∈ Ed (C P).M
      (fapps ((C P).M.μ (C P).node.a.family.ref
        ((canonL (C P).node.a.family.member.arity).map (evalTotal (C P).σ)))
        ((C P).parameters ++ [])) :=
  (NormPropEvalAttack.arguments_fit P).2.2.2.1

theorem valuation_bound (P : Premises4) :
    ∀ u, u ∈ [1] → u ≤ bound (C P).rr := by
  intro u hu
  cases List.mem_singleton.mp hu
  exact Nat.le_refl 1

/-- Actual invocation of the new constructor producer. All semantic
family-only prefixes are constructed inside that theorem. -/
theorem constructor_step (P : Premises4) :
    ∀ vs i z, CtorAt P (μ P) (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node))
      (X P) vs i z → PropEvalCandidate.EvalPredicate (C P) vs i z :=
  IndexedPropEval.constructor_step P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl constructors rfl
    AccEnv.accMembersT indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => by nomatch h)
    (family_equation P) [1] rfl (valuation_bound P) rfl rfl (.param 0)
    (motive_fits P) (minors_fit P)

/-- Actual invocation of the normalized candidate composition. -/
theorem candidate_closed (P : Premises4) :
    Admissible (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) ∧
      Closed P (μ P) (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) :=
  IndexedPropEval.candidate_closed P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl constructors rfl
    AccEnv.accMembersT indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => by nomatch h)
    (family_equation P) [1] rfl (valuation_bound P) rfl rfl (.param 0)
    (motive_fits P) (minors_fit P)

/-- Actual invocation of the new normalized-member totality producer. -/
theorem normalized_evaluates (P : Premises4) :
    ∀ vs i z, z ∈ NormPropEval.base P (μ P) (C P) vs i →
      PropEvalCandidate.EvalPredicate (C P) vs i z :=
  IndexedPropEval.normalized_evaluates P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl constructors rfl
    AccEnv.accMembersT indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => by nomatch h)
    (family_equation P) [1] rfl (valuation_bound P) rfl rfl (.param 0)
    (motive_fits P) (minors_fit P)

/-- The new producer yields evaluation, the guarded carrier and the
actual requested motive membership at the complete fixture key. -/
theorem scalar_spec (P : Premises4) :
    result P ∈ childCarrier (C P) (.param 0) (key [parameter]) ∧
      Eval (C P) (key [parameter]) (result P) ∧
      result P ∈ Ed (C P).M (fapp (C P).motive pempty) :=
  IndexedPropEval.result_spec P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl constructors rfl
    AccEnv.accMembersT indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => by nomatch h)
    (family_equation P) [1] rfl (valuation_bound P) rfl rfl (.param 0)
    (motive_fits P) (minors_fit P) [] pempty (parameters_fit P) True.intro
    (major_fits P)

theorem value_in_domain (P : Premises4) : result P ∈ domain :=
  mem_congr_left (NormPropEvalAttack.value_same P (key [parameter]))
    (PropEvalValueAttack.result_domain P)

theorem value_nonempty (P : Premises4) : ¬ Equiv (result P) pempty :=
  fun he => dataVal_ne_pempty _ _ ((mem_singleton.mp (value_in_domain P)).symm.trans he)

/-- Composition with the concrete installed recursor uses the new
producer's motive membership, not a completed-group EnvSound assumption. -/
theorem installed_member (P : Premises4) :
    fapps (μ P 2 [1])
      [parameter, motive P (installed P), minor P (installed P), pempty] ∈
        Ed (C P).M (fapp (C P).motive pempty) :=
  mem_congr_left (NormPropEvalAttack.application_result P).symm (scalar_spec P).2.2

structure StepWitness (P : Premises4) : Prop where
  field_components : IndexedFieldBounds.Witness P
  bound : IndexedFieldBounds.BoundGIndexed PropEvalAdmittedInputsAttack.bound AccEnv.accEnvWfT
  predecessor : PointwiseRole.GInv P PropEvalAdmittedInputsAttack.bound
    (.empty : EnvWfT emptyEnv)
  motive_universe : (C P).σ 0 = 1
  actual_arguments : TelFits (mkM P (μ P)) (ctx P).σ
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
    [parameter, motive P (installed P), minor P (installed P), pempty]
  empty_child_domain : ∀ zs, ¬ TelFits (C P).M (C P).σ [.bvar 2]
    (vcons pempty (start P (installed P))) zs
  step : ∀ vs i z, CtorAt P (μ P)
    (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) vs i z →
      PropEvalCandidate.EvalPredicate (C P) vs i z

theorem step_witness (P : Premises4) : StepWitness P :=
  ⟨IndexedFieldBounds.component_witness P, indexed_bound,
    PointwiseRole.gInv_empty P bound, rfl, NormPropEvalAttack.arguments_fit P,
    NormPropEvalAttack.no_children P, constructor_step P⟩

theorem step_nonrefutable (P : Premises4) :
    ¬ (StepWitness P → (Premises4 → False)) :=
  fun h => h (step_witness P) P

structure TotalWitness (P : Premises4) : Prop where
  predecessor_component : StepWitness P
  admissible : Admissible (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P)
  closed : Closed P (μ P) (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P)
  total : ∀ vs i z, z ∈ NormPropEval.base P (μ P) (C P) vs i →
    PropEvalCandidate.EvalPredicate (C P) vs i z

theorem total_witness (P : Premises4) : TotalWitness P :=
  ⟨step_witness P, (candidate_closed P).1, (candidate_closed P).2,
    normalized_evaluates P⟩

theorem total_nonrefutable (P : Premises4) :
    ¬ (TotalWitness P → (Premises4 → False)) :=
  fun h => h (total_witness P) P

structure ValueWitness (P : Premises4) : Prop where
  predecessor_component : TotalWitness P
  evaluation : Eval (C P) (key [parameter]) (result P)
  guarded : result P ∈ childCarrier (C P) (.param 0) (key [parameter])
  typed : result P ∈ Ed (C P).M (fapp (C P).motive pempty)
  inhabited : result P ∈ domain
  nonempty : ¬ Equiv (result P) pempty
  typed_ih : NormPropEvalAttack.ihValue P ∈ Ed (C P).M
    (den (C P).M (C P).σ (vcons pempty (start P (installed P))) accIhTy)
  installed_value : Equiv (fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty]) (result P)
  installed_typed : fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty] ∈
      Ed (C P).M (fapp (C P).motive pempty)
  concrete_iota : Equiv (fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty])
    (fapps (minor P (installed P)) [pempty, NormPropEvalAttack.ihValue P])
  invalid_key : Equiv
    (PropEvalValue.result (C P) (.param 0) (key [parameter, datum])) pempty ∧
      PropEvalValue.result (C P) (.param 0) (key [parameter, datum]) ∉ domain
  old_endpoint_rejected : ∀ old : List (List FieldShape),
    RecPlanValue.endValue (mkM P (μ P)) (ctx P).σ fd old (input P (installed P)) ∉
      Ed (mkM P (μ P)) (fapp (motive P (installed P)) pempty)

theorem value_witness (P : Premises4) : ValueWitness P :=
  ⟨total_witness P, (scalar_spec P).2.1, (scalar_spec P).1, (scalar_spec P).2.2,
    value_in_domain P, value_nonempty P, NormPropEvalAttack.ih_typed P,
    NormPropEvalAttack.application_result P, installed_member P,
    NormPropEvalAttack.installed_iota P, NormPropEvalAttack.invalid_key P,
    NormPropEvalAttack.old_endpoint_rejected P⟩

theorem value_nonrefutable (P : Premises4) :
    ¬ (ValueWitness P → (Premises4 → False)) :=
  fun h => h (value_witness P) P

def Witness (P : Premises4) : Prop :=
  StepWitness P ∧ TotalWitness P ∧ ValueWitness P

/-- Every split is recomposed at the same Premises4 instance. -/
theorem component_witness (P : Premises4) : Witness P :=
  ⟨step_witness P, total_witness P, value_witness P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedPropEvalAttack
