import rcic.RcicF3EvalPlanNormalMono
import rcic.RcicF3EvalRawTable
import rcic.RcicF3EvalPlanAttack
import rcic.RcicF3RawFamilyPropAttack

/-!
# Composition at the actual AccR table and hidden depth-three fields

The admitted AccR group uses the new canonical faithful table. At every
universe vector, the raw presentation with parameter [tyv pempty], field
tuple [pempty], and complete key key [tyv pempty] enters the normalized
operator by the public group producer. The same literal normalized field
tuple is also retained, not merely existential constructor membership.

AccR has family arity zero, so these arbitrary vectors do not test a high
relevant family level. The separate hidden cases test the actual normalized
field data at depth three, relabelled families and a dependent terminal
argument. Their alias environments remain reader fixtures only.
No universal small data frame or repaired StepAG is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormalAttack
open Rcic.Declarative PiIndex
open PiRawIHAttack (field beta delta zeta)

noncomputable def plan : EvalPlan.Plan := EvalPlan.ofNode PlanPropStepAttack.pNode

noncomputable def μ (P : Premises4) : Nat → List Nat → PSet.{4} :=
  EvalRole.rawTable P AccEnv.accEnvWfT

noncomputable def carrier (P : Premises4) : RawFamily.Frame :=
  RawFamily.frame P (μ P) (famDataOf plan.node.a)

def parameter : PSet.{4} := tyv pempty

noncomputable def ctor : Fin (EvalPlanNormal.fd plan).ctors.length :=
  ⟨0, by rw [EvalPlanNormal.ctors_length]; decide⟩

/-- The new field expression, built from the actual cache, removes each
hidden head while preserving all three domains and the dependent argument. -/
theorem hidden_normal : ∀ (f : Nat) (hf : f ∈ [1, 2, 987]),
    ∀ (A : Expr Nat) (hA : A ∈ [field f, beta f, delta f, zeta f]),
      PiValueRule.fieldExpr f [] (EvalPlanNormal.fieldSpec
        (EvalPlan.of_admitted (np := 0) (prior := 0)
          (CandidateScopeAttack.hidden_scans f hf A hA).1)) = field f := by
  intro f hf A hA
  obtain ⟨r, hr, hd, ha⟩ := EvalPlanAttack.hidden_cache f hf A hA
  rw [hr]
  change policyPi r.domains (foldApps (.const f []) r.arguments) = field f
  rw [hd, ha]
  rfl

def Witness (P : Premises4) : Prop :=
  EvalRole.Faithful RawFamily.role P (μ P) (envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  (EvalPlanNormal.fd plan).params = [.sort .zero] ∧
  (EvalPlanNormal.fd plan).indices = [] ∧
  ((EvalPlanNormal.fd plan).ctors.get ctor).2 = [] ∧
  RawFamily.ConstructorMono P (μ P) (EvalPlanNormal.fd plan) ∧
  (∀ vs,
    RawFamily.CtorAt P (μ P) (famDataOf plan.node.a) (carrier P)
      vs (key [parameter]) pempty ∧
    RawFamily.CtorAt P (μ P) (EvalPlanNormal.fd plan) (carrier P)
      vs (key [parameter]) pempty ∧
    TelFits (mkM P (RawFamily.table P (μ P) (famDataOf plan.node.a) (carrier P)))
      (σOf vs) (EvalPlanNormal.fields plan ⟨0, by decide⟩)
      (push [parameter] ρ0) [pempty]) ∧
  (∀ (f : Nat) (hf : f ∈ [1, 2, 987]),
    ∀ (A : Expr Nat) (hA : A ∈ [field f, beta f, delta f, zeta f]),
      PiValueRule.fieldExpr f [] (EvalPlanNormal.fieldSpec
        (EvalPlan.of_admitted (np := 0) (prior := 0)
          (CandidateScopeAttack.hidden_scans f hf A hA).1)) = field f)

/-- The faithful table, inhabited raw presentation, exact normalized tuple,
and public all-vector bridge are composed in the same actual environment. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hfaith := (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    have he : c = (1, accIntroMember) := List.mem_singleton.mp hc
    cases he
    rfl
  refine ⟨hfaith, rfl, rfl, ?_, ?_, ?_, hidden_normal⟩
  · rw [EvalPlanNormal.ctor_get]
    rfl
  · exact EvalPlanNormal.constructorMono_of_group P (μ P) plan accFamMember
      [(1, accIntroMember)] .empty AccEnv.accMembersT
  · intro vs
    let M := mkM P (RawFamily.table P (μ P) (famDataOf plan.node.a) (carrier P))
    have hC : RawFamily.Admissible (famDataOf plan.node.a) (carrier P) :=
      (RawFamilyPropAttack.acc_closed P (μ P)).1
    have ha : parameter ∈ U W4 0 :=
      mem_sImage_tyv.mpr ⟨pempty,
        mem_propSets.mpr (fun _ h => (not_mem_pempty h).elim), Equiv.rfl⟩
    have hp : TelFits M (σOf vs) (famDataOf plan.node.a).params ρ0 [parameter] := by
      refine ⟨?_, True.intro⟩
      exact mem_congr_right (ed_tyv M (U4_dich 0)).symm ha
    have hx : pempty ∈ Ed M
        (den M (σOf vs) (push [parameter] ρ0) accField) := by
      apply mem_congr_right
        (RawFamilyPropAttack.field_read P (μ P) (carrier P) hC parameter ha vs).symm
      refine mem_tv.mpr ⟨?_, Equiv.rfl⟩
      intro x hx
      exact (not_mem_pempty (mem_congr_right
        (ed_tyv (mkM P (μ P))
          (Or.inl (fun _ h => (not_mem_pempty h).elim))) hx)).elim
    have hraw : RawFamily.CtorAt P (μ P) (famDataOf plan.node.a) (carrier P)
        vs (key [parameter]) pempty :=
      ⟨⟨0, by decide⟩, [parameter], [pempty], hp, ⟨hx, True.intro⟩,
        True.intro, rfl, Equiv.rfl⟩
    have hnormal := EvalPlanNormal.ctorAt_of_group RawFamily.role P (μ P)
      (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
      plan accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
      AccEnv.accMembersT (fun _ _ => rfl) hfaith (carrier P)
      vs (key [parameter]) pempty hraw
    have hδ := EvalRoleDelta.bodyEquations_at_node RawFamily.role P (μ P)
      (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
      (fm := accFamMember) (rm := accRecMember) (ctors := [(1, accIntroMember)])
      .empty rfl hctors rfl AccEnv.accMembersT (fun _ _ => rfl) hfaith plan.node
      (RawFamily.ofFrame P (μ P) (famDataOf plan.node.a) (carrier P)) (σOf vs)
    have hf := EvalPlanNormal.fields_forward M plan.node.E0 (σOf vs) hδ
      (plan.constructors ⟨0, by decide⟩).fields (push [parameter] ρ0)
      [pempty] ⟨hx, True.intro⟩
    exact ⟨hraw, hnormal, hf.1⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalPlanNormalAttack
