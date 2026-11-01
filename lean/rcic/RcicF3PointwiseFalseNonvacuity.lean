import rcic.RcicF3PointwisePropPlainGroup
import rcic.RcicF3PointwiseRoleConsumer
import rcic.RcicF3NormFalseNonvacuity

/-!
# Distinguished-False non-vacuity at the separate pointwise table

The original admitted False prefix at slots 0 and 1 and the original
Prop definition at slot 2 are reused literally. The NEW plain Prop group
producer and NEW singleton producer build PointwiseRole.GInv directly;
the semantic statements below use its actual new installer throughout.

Every original TierF3WDChecked environment antecedent is retained. The
same slot-2 fibre contains two inequivalent proposition values, only one
of which has a proof. The new finalizer gives bounded consistency of this
particular environment without a universal local-candidate or A premise.
No old/new invariant or table equality is used. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseFalseNonvacuity
open Rcic.Declarative Rcic.Model.PS
open NormFalseNonvacuity (plan family policy noFun fields_free ctorClasses
  propMember propTyped prop_bound env wf falseRec_present prop_present prop_role
  falseValue trueValue EnvironmentAntecedents environment_antecedents)

/-- The canonical empty-family step uses the new complete recursor package. -/
theorem base_step (P : Premises4) (K : Nat → Nat) :
    PointwiseDataGroup.GroupStepAt P K EnvWfT.empty (f := 0) (fm := falseFamMember)
      (ctors := []) (rr := 1) (rm := falseRecMemberU)
      rfl ctorClasses rfl falseMembersT := by
  apply PointwisePropPlainGroup.group_step P K EnvWfT.empty
    (f := 0) (fm := falseFamMember) (ctors := [])
    (rr := 1) (rm := falseRecMemberU) rfl ctorClasses rfl falseMembersT
  · change UniformProp plan.node.a.family.resultLevel
    intro σ
    rw [(family plan.node).2.2]
    rfl
  · exact policy plan.node
  · exact noFun plan.node
  · exact fields_free plan.node

theorem base_invariant (P : Premises4) (K : Nat → Nat) :
    PointwiseRole.GInv P K falseEnvUWfT :=
  base_step P K (fun _ => ⟨True.intro, True.intro, True.intro⟩)
    (falseEnvUWfT_boundG K) (falseEnvUWfT_boundDG K)
    (PointwiseRole.gInv_empty P K)

/-- The actual singleton producer extends the new False-group invariant. -/
theorem invariant (P : Premises4) (K : Nat → Nat) : PointwiseRole.GInv P K wf := by
  intro α hα ctx hctx plans hplans μ hFaith
  exact PointwiseRole.gInv_singleW P K (E := falseEnvU) (hE := falseEnvUWfT)
    (r := 2) (k := .definitionM) (A := .sort (.succ .zero)) (v := .sort .zero)
    (Or.inl rfl) (falseEnvU_m2 0) (fun _ => rfl) (fun _ => rfl)
    rfl rfl propTyped (prop_bound K) (base_invariant P K)
    α hα ctx hctx plans hplans μ hFaith

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P wf

theorem faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities env)) P (table P) (NormRole.envCtx wf)
      (EvalRole.envPlan wf) env :=
  (PointwiseRole.table_spec P wf).2.1

/-- The value equation is obtained from this same final table's faithfulness. -/
theorem prop_value (P : Premises4) :
    Equiv (table P 2 []) (tyv (U W4 0)) := by
  have h := faithful P 2 propMember prop_present []
  rw [prop_role] at h
  change Equiv (table P 2 [])
    (RoleModel.memberVal (PointwiseRole.familyValue (PointwiseRole.arities env)) P (table P) .plain propMember []) at h
  have e : RoleModel.memberVal (PointwiseRole.familyValue (PointwiseRole.arities env)) P (table P) .plain propMember [] =
      den (mkM P (table P)) (fun _ => 0) ρ0 (.sort .zero) :=
    mem_memberVal_def (Or.inl rfl) (.sort (.succ .zero)) (.sort .zero) []
  rw [e] at h
  exact h

theorem false_mem (P : Premises4) :
    falseValue ∈ Ed (mkM P (table P)) (table P 2 []) :=
  mem_congr_right ((ed_congr (mkM P (table P)) (prop_value P)).trans
    (ed_tyv (mkM P (table P)) (U4_dich 0))).symm (tyv_pempty_mem_U4 P 0)

theorem true_mem (P : Premises4) :
    trueValue ∈ Ed (mkM P (table P)) (table P 2 []) := by
  have ht : trueValue ∈ U W4 0 :=
    mem_sImage_tyv.mpr ⟨tv True,
      mem_propSets.mpr (fun _ hz => (mem_tv.mp hz).2), Equiv.rfl⟩
  exact mem_congr_right ((ed_congr (mkM P (table P)) (prop_value P)).trans
    (ed_tyv (mkM P (table P)) (U4_dich 0))).symm ht

theorem true_inhabited (P : Premises4) : pempty ∈ Ed (mkM P (table P)) trueValue :=
  mem_congr_right (ed_tyv (mkM P (table P)) (dich_tv True)).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

theorem false_empty (P : Premises4) : pempty ∉ Ed (mkM P (table P)) falseValue := by
  intro h
  exact not_mem_pempty (mem_congr_right
    (ed_tyv (mkM P (table P)) (Or.inl (fun _ hz => (not_mem_pempty hz).elim))) h)

theorem distinct (P : Premises4) : ¬ Equiv falseValue trueValue := by
  intro he
  exact false_empty P (mem_congr_right
    (ed_congr (mkM P (table P)) he).symm (true_inhabited P))

theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P)) σ K env n :=
  PointwiseRole.envSound_of_gInv P K wf (invariant P K) σ n

/-- The new finalizer also supplies the bounded consistency conclusion at
this particular admitted environment. This is not the universal tier. -/
theorem consistent (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (D : HasTyT env n [] e (.const 0 [])) (hl : LevelsBelow 4 K D) : False :=
  PointwiseRole.false_of_gInv P K wf (invariant P K) falseRec_present n e D hl

def Witness (P : Premises4) (K : Nat → Nat) : Prop :=
  EnvironmentAntecedents K ∧ PointwiseRole.GInv P K wf ∧
  EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities env)) P (table P) (NormRole.envCtx wf)
    (EvalRole.envPlan wf) env ∧
  EvalRole.ReadsClosed (NormRole.envCtx wf) (EvalRole.envPlan wf) env ∧
  (∀ σ n, EnvSound (mkM P (table P)) σ K env n) ∧
  falseValue ∈ Ed (mkM P (table P)) (table P 2 []) ∧
  trueValue ∈ Ed (mkM P (table P)) (table P 2 []) ∧
  (¬ Equiv falseValue trueValue) ∧
  pempty ∈ Ed (mkM P (table P)) trueValue ∧
  pempty ∉ Ed (mkM P (table P)) falseValue ∧
  (∀ n e (D : HasTyT env n [] e (.const 0 [])), LevelsBelow 4 K D → False)

theorem component_witness (P : Premises4) (K : Nat → Nat) : Witness P K :=
  ⟨environment_antecedents K, invariant P K, faithful P,
    (PointwiseRole.table_spec P wf).2.2, env_sound P K, false_mem P, true_mem P,
    distinct P, true_inhabited P, false_empty P, consistent P K⟩

theorem component_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (Witness P K → (Premises4 → False)) :=
  fun h => h (component_witness P K) P

end Rcic.F3.PSet.PointwiseFalseNonvacuity
