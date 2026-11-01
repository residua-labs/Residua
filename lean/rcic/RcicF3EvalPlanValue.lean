import rcic.RcicF3EvalPlan
import rcic.RcicF3EvalPlanScope
import rcic.RcicF3PlanRole

/-!
# Production endpoints carrying the actual admitted evaluation plan

At a Prop family with anySort elimination, the endpoint is the bounded
value of the actual indexed evaluation relation. Parameters, motive,
minors and indices are read from the final recursor environment; the full
universe valuation, including the extra motive slot, is retained.

The propOnly and data branches retain the existing planned endpoint.
Its universal data-frame and recursor typing obligations remain Step 4
work. This module supplies the actual replacement operation, exact input
slicing, environment responsiveness and produced table-read transport.
It does not assert universal StepAG or apex closure. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPlanValue
open Rcic.Declarative PiIndex PropEval

def parameters (p : EvalPlan.Plan) (ρ : Nat → PSet.{4}) : List PSet.{4} :=
  lastVals p.node.a.family.parameters.length
    (shiftρ (p.node.a.family.indices.length + p.node.a.constructors.length + 2) ρ)

def motive (p : EvalPlan.Plan) (ρ : Nat → PSet.{4}) : PSet.{4} :=
  ρ (p.node.a.family.indices.length + p.node.a.constructors.length + 1)

def minors (p : EvalPlan.Plan) (ρ : Nat → PSet.{4}) : List PSet.{4} :=
  minorsOf p.node.a.family.indices.length p.node.a.constructors.length ρ

def indices (p : EvalPlan.Plan) (ρ : Nat → PSet.{4}) : List PSet.{4} :=
  lastVals p.node.a.family.indices.length (shiftρ 1 ρ)

theorem minors_length (p : EvalPlan.Plan) (ρ : Nat → PSet.{4}) :
    (minors p ρ).length = p.node.a.constructors.length := by
  simp only [minors, minorsOf, List.length_map, List.length_range]

/-- The actual node and the entire recursor valuation are unchanged. -/
noncomputable def context (p : EvalPlan.Plan) (M : Interp.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) : Context where
  E := p.E
  E' := p.E'
  f := p.f
  rr := p.rr
  rm := p.rm
  node := p.node
  M := M
  σ := σ
  parameters := parameters p ρ
  motive := motive p ρ
  minors := minors p ρ
  minor_length := minors_length p ρ

/-- This branch returns the actual bounded indexed value, with no callback. -/
noncomputable def endValue (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (ρ : Nat → PSet.{4}) : PSet.{4} :=
  cond M.dec (evalTotal σ p.node.a.family.resultLevel = 0 ∧ p.node.a.policy = .anySort)
    (PropEvalValue.result (context p M σ ρ)
      (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
      (key (parameters p ρ ++ indices p ρ)))
    (RecPlanValue.endValue M σ (famDataOf p.node.a) (RecPlan.nodePlan p.node) ρ)

noncomputable def memberValue (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (m : CheckedMember) : PSet.{4} :=
  piLam M σ (endValue M σ p) ρ0 m.mtype

theorem endValue_prop (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (ρ : Nat → PSet.{4}) (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort) :
    endValue M σ p ρ = PropEvalValue.result (context p M σ ρ)
      (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
      (key (parameters p ρ ++ indices p ρ)) := by
  unfold endValue
  rw [cond_pos ⟨h0, hpolicy⟩]

theorem endValue_fallback (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (ρ : Nat → PSet.{4})
    (hn : ¬ (evalTotal σ p.node.a.family.resultLevel = 0 ∧ p.node.a.policy = .anySort)) :
    endValue M σ p ρ =
      RecPlanValue.endValue M σ (famDataOf p.node.a) (RecPlan.nodePlan p.node) ρ := by
  unfold endValue
  rw [cond_neg hn]

/-- All semantic input slices and the complete quotient key are responsive. -/
theorem endValue_resp (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan) :
    EnvResp (endValue M σ p) := by
  intro ρ ρ' hρ
  unfold endValue
  apply cond_congr Iff.rfl
  · exact PropEvalValue.result_values_key_congr (context p M σ ρ) _
      (parameters p ρ') (motive p ρ') (minors p ρ') (minors_length p ρ')
      (lastVals_congr _ (fun i => hρ _)) (hρ _)
      (minorsOf_congr _ _ hρ) (indices p ρ) (indices p ρ')
      (lastVals_congr _ (fun i => hρ _))
  · exact (RecPlanValue.laws M σ (famDataOf p.node.a) (RecPlan.nodePlan p.node)).1 ρ ρ' hρ

/-- A syntactic support certificate pays all model-dependent evaluation and
guard reads. The data/propOnly fallback depends only on the same decider. -/
theorem endValue_agreeOn (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hAgree : AgreeOn μ₁ μ₂ S) (p : EvalPlan.Plan) (σ : Nat → Nat)
    (hReads : EndpointReads S (context p (mkM P μ₁) σ ρ0))
    (ρ : Nat → PSet.{4}) :
    Equiv (endValue (mkM P μ₁) σ p ρ) (endValue (mkM P μ₂) σ p ρ) := by
  unfold endValue
  apply cond_congr Iff.rfl
  · have hR : EndpointReads S (context p (mkM P μ₁) σ ρ) :=
      hReads.withValues (parameters p ρ) (motive p ρ) (minors p ρ) (minors_length p ρ)
    exact PropEvalValue.result_model_congr (C := context p (mkM P μ₁) σ ρ)
      P μ₁ μ₂ S rfl hAgree hR _ _
  · rw [PlanRole.endpoint_of_dec (M := mkM P μ₁) (M' := mkM P μ₂) rfl]
    exact Equiv.rfl

/-- Actual typed group admission produces the support premise above. -/
theorem endValue_agreeOn_group (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan) (σ : Nat → Nat)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hAgree : AgreeOn μ₁ μ₂ (Dom p.node.E0)) (ρ : Nat → PSet.{4}) :
    Equiv (endValue (mkM P μ₁) σ p ρ) (endValue (mkM P μ₂) σ p ρ) :=
  endValue_agreeOn P μ₁ μ₂ (Dom p.node.E0) hAgree p σ
    (EvalPlanScope.endpointReads_of_group (context p (mkM P μ₁) σ ρ0)
      fm ctors hE hfam hctors hrec hmem) ρ

/-- The actual member abstraction has the corresponding table-read law. -/
theorem memberValue_agreeOn (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop)
    (hAgree : AgreeOn μ₁ μ₂ S) (p : EvalPlan.Plan) (σ : Nat → Nat)
    (hReads : EndpointReads S (context p (mkM P μ₁) σ ρ0))
    (m : CheckedMember) (hm : ExprReads S m.mtype) :
    Equiv (memberValue (mkM P μ₁) σ p m) (memberValue (mkM P μ₂) σ p m) :=
  piLam_agreeOn P hAgree σ (endValue_resp (mkM P μ₁) σ p)
    (endValue_agreeOn P μ₁ μ₂ S hAgree p σ hReads) m.mtype hm ρ0

/-- The parameter slice skips exactly major, indices, minors and motive. -/
theorem parameters_input (p : EvalPlan.Plan) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms is : List PSet.{4}) (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (hps : ps.length = p.node.a.family.parameters.length)
    (hms : ms.length = p.node.a.constructors.length)
    (his : is.length = p.node.a.family.indices.length) :
    parameters p (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) = ps := by
  unfold parameters
  rw [← hps, ← hms, ← his]
  have hl : (mo :: (ms ++ (is ++ [z]))).length = is.length + ms.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  rw [push_append, ← hl, shiftρ_push, lastVals_push]

theorem motive_input (p : EvalPlan.Plan) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms is : List PSet.{4}) (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (hms : ms.length = p.node.a.constructors.length)
    (his : is.length = p.node.a.family.indices.length) :
    motive p (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) = mo := by
  unfold motive
  rw [← hms, ← his, push_cons_eq]
  change push is (push ms (vcons mo (push ps ρ))) (is.length + ms.length) = mo
  rw [Nat.add_comm is.length ms.length, push_ge]
  simpa only [Nat.zero_add] using push_ge ms (vcons mo (push ps ρ)) 0

theorem minors_input (p : EvalPlan.Plan) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms is : List PSet.{4}) (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (hms : ms.length = p.node.a.constructors.length)
    (his : is.length = p.node.a.family.indices.length) :
    minors p (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) = ms :=
  minorsOf_env ps mo ms is z ρ hms his

theorem indices_input (p : EvalPlan.Plan) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms is : List PSet.{4}) (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (his : is.length = p.node.a.family.indices.length) :
    indices p (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) = is := by
  unfold indices
  rw [← his]
  exact recEnv_indices ps mo ms is z ρ

/-- The final environment reconstructs precisely the supplied semantic inputs. -/
theorem context_input (p : EvalPlan.Plan) (M : Interp.{4}) (σ : Nat → Nat)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (hps : ps.length = p.node.a.family.parameters.length)
    (hms : ms.length = p.node.a.constructors.length)
    (his : is.length = p.node.a.family.indices.length) :
    context p M σ (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) =
      (context p M σ ρ0).withValues ps mo ms hms := by
  have hp := parameters_input p ps mo ms is z ρ hps hms his
  have hm := motive_input p ps mo ms is z ρ hms his
  have hmi := minors_input p ps mo ms is z ρ hms his
  simp only [context, Context.withValues, hp, hm, hmi]

/-- The actual branch uses the complete supplied key after exact input slicing. -/
theorem endValue_input (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (hps : ps.length = p.node.a.family.parameters.length)
    (hms : ms.length = p.node.a.constructors.length)
    (his : is.length = p.node.a.family.indices.length) :
    endValue M σ p (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) =
      PropEvalValue.result ((context p M σ ρ0).withValues ps mo ms hms)
        (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
        (key (ps ++ is)) := by
  rw [endValue_prop M σ p _ h0 hpolicy,
    context_input p M σ ps mo ms is z ρ hps hms his,
    parameters_input p ps mo ms is z ρ hps hms his,
    indices_input p ps mo ms is z ρ his]

end Rcic.F3.PSet.EvalPlanValue
