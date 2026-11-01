import rcic.RcicF3NormPropPlainGroup
import rcic.RcicF3NormRoleConsumer

/-!
# A nontrivial normalized model with the distinguished False prefix

The actual admitted False group occupies slots 0 and 1. Its new normalized
group invariant is produced by the plain Prop/anySort constructor and
recursor package. An admitted definition at fresh slot 2 then names Prop.
The singleton producer extends the same invariant, and the produced table
interprets this definition as the universe of proposition values.

Both whole-environment W/D checks and every environment antecedent of the
original TierF3WDChecked statement are supplied, at every K. Two inequivalent
proposition values inhabit the same installed slot-2 fibre; one has a proof
value and the other does not. No old invariant or table is substituted.

This is a particular environment certificate, relative to Premises4. It
assumes no StepAG premise and supplies no universal StepAG producer, no
imported Acc environment, and no universal checked-apex closure.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormFalseNonvacuity
open Rcic.Declarative Rcic.Model.PS
open Rcic.F3.StepWCheck Rcic.F3.StepDGOrder

abbrev Node := RecNode emptyEnv falseEnvU 0 1 falseRecMemberU

theorem family_member (node : Node) : node.a.family.member = falseFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

theorem family (node : Node) : node.a.family.parameters = [] ∧
    node.a.family.indices = [] ∧ node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [family_member node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

theorem count (node : Node) : node.a.constructors.length = 0 :=
  node_ctors_length (ctors := []) node rfl

theorem no_constructor (node : Node) (i : Fin node.a.constructors.length) : False :=
  Nat.not_lt_zero i.val (Nat.lt_of_lt_of_eq i.isLt (count node))

theorem policy (node : Node) : node.a.policy = .anySort := by
  cases h : node.a.policy with
  | anySort => rfl
  | propOnly =>
      have ha := node.a.recursorArity
      rw [family_member node, h] at ha
      change 1 = 0 at ha
      exact False.elim (Nat.noConfusion ha)

theorem noFun (node : Node) : NoFunRec node :=
  fun i => (no_constructor node i).elim

theorem fields_free (node : Node) (i : Fin node.a.constructors.length) A
    (_hA : A ∈ (node.a.constructorViews i).fields) :
    occursConst node.a.family.ref A = false :=
  (no_constructor node i).elim

theorem ctorClasses : ∀ c ∈ ([] : List (Nat × CheckedMember)),
    c.2.mclass = .constructorM :=
  fun c hc => (List.not_mem_nil c hc).elim

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 0) (fm := falseFamMember)
    (ctors := []) (rr := 1) (rm := falseRecMemberU)
    rfl ctorClasses rfl falseMembersT

/-- The canonical empty-family step uses the new complete recursor package. -/
theorem base_step (P : Premises4) (K : Nat → Nat) :
    NormRole.GroupStepAt P K EnvWfT.empty (f := 0) (fm := falseFamMember)
      (ctors := []) (rr := 1) (rm := falseRecMemberU)
      rfl ctorClasses rfl falseMembersT := by
  apply NormPropPlainGroup.group_step P K EnvWfT.empty
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
    NormRole.GInv P K falseEnvUWfT :=
  base_step P K (fun _ => ⟨True.intro, True.intro, True.intro⟩)
    (falseEnvUWfT_boundG K) (falseEnvUWfT_boundDG K)
    (NormRole.gInv_empty P K)

/-- The stored declaration is literally Prop : Type, with an actual typing. -/
def propMember : CheckedMember :=
  ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩

noncomputable def env : ResolvedEnv := extendEnv falseEnvU 2 propMember

def propTyped : HasTyT falseEnvU 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort [] .zero

noncomputable def wf : EnvWfT env :=
  .definition falseEnvU 2 (.sort (.succ .zero)) (.sort .zero)
    (.succ (.succ .zero)) falseEnvUWfT (falseEnvU_m2 0)
    (.sort [] (.succ .zero)) propTyped
    (fun _ => rfl) (fun _ => rfl) rfl rfl

theorem prop_bound (K : Nat → Nat) : LOKt (fun _ => 0) 4 K propTyped := by
  change 1 ≤ 4
  decide

theorem boundG (K : Nat → Nat) : BoundG K wf :=
  ⟨falseEnvUWfT_boundG K, prop_bound K⟩

theorem boundDG (K : Nat → Nat) : BoundDG K wf :=
  falseEnvUWfT_boundDG K

theorem false_present : env.members 0 = some falseFamMember := rfl

theorem falseRec_present : env.members 1 = some falseRecMemberU := rfl

theorem prop_present : env.members 2 = some propMember := rfl

theorem axiom_free : AxiomFreeEnv' env := by
  intro r m hm
  by_cases hr : r = 2
  · subst r
    rw [prop_present] at hm
    cases hm
    exact fun h => MemberClass.noConfusion h
  · change (extendEnv falseEnvU 2 propMember).members r = some m at hm
    rw [members_extend_ne falseEnvU 2 propMember r hr] at hm
    exact falseEnvU_axiomFree r m hm

theorem w_checked : EnvWChecked wf := by
  change EnvWChecked falseEnvUWfT
  refine ⟨True.intro, ?_⟩
  intro node hW _ _
  exact False.elim (hW (falseEnvU_classG.1.2.2 node))

theorem d_side (K : Nat → Nat) (node : Node) : StepDGSide K node :=
  ⟨fun i => (no_constructor node i).elim,
    fun _ _ i => (no_constructor node i).elim,
    fun i => (no_constructor node i).elim⟩

theorem d_checked (K : Nat → Nat) : Rcic.F3.StepWDApex.EnvDChecked K wf :=
  ⟨True.intro, d_side K _⟩

theorem w_check : Rcic.F3.StepWApex.envCheck wf = true :=
  (Rcic.F3.StepWApex.envCheck_pass_iff wf).mpr w_checked

theorem d_check (K : Nat → Nat) : Rcic.F3.StepWDApex.envCheck K wf = true :=
  (Rcic.F3.StepWDApex.envCheck_pass_iff K wf).mpr (d_checked K)

/-- The actual singleton producer extends the new False-group invariant. -/
theorem invariant (P : Premises4) (K : Nat → Nat) : NormRole.GInv P K wf := by
  intro ctx hctx plans hplans μ hFaith
  exact NormRole.gInv_singleW P K (E := falseEnvU) (hE := falseEnvUWfT)
    (r := 2) (k := .definitionM) (A := .sort (.succ .zero)) (v := .sort .zero)
    (Or.inl rfl) (falseEnvU_m2 0) (fun _ => rfl) (fun _ => rfl)
    rfl rfl propTyped (prop_bound K) (base_invariant P K)
    ctx hctx plans hplans μ hFaith

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P wf

theorem faithful (P : Premises4) :
    EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx wf)
      (EvalRole.envPlan wf) env :=
  (NormRole.table_spec P wf).1

theorem prop_role : NormRole.envCtx wf 2 = .plain :=
  NormRole.envCtx_fresh falseEnvUWfT 2 (falseEnvU_m2 0)

/-- The value equation is obtained from this same final table's faithfulness. -/
theorem prop_value (P : Premises4) :
    Equiv (table P 2 []) (tyv (U W4 0)) := by
  have h := faithful P 2 propMember prop_present []
  rw [prop_role] at h
  change Equiv (table P 2 [])
    (RoleModel.memberVal RawFamily.role P (table P) .plain propMember []) at h
  have e : RoleModel.memberVal RawFamily.role P (table P) .plain propMember [] =
      den (mkM P (table P)) (fun _ => 0) ρ0 (.sort .zero) :=
    mem_memberVal_def (Or.inl rfl) (.sort (.succ .zero)) (.sort .zero) []
  rw [e] at h
  exact h

def falseValue : PSet.{4} := tyv pempty

def trueValue : PSet.{4} := tyv (tv True)

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
  NormRole.envSound_of_gInv P K wf (invariant P K) σ n

/-- The new finalizer also supplies the bounded consistency conclusion at
this particular admitted environment. This is not the universal tier. -/
theorem consistent (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (D : HasTyT env n [] e (.const 0 [])) (hl : LevelsBelow 4 K D) : False :=
  NormRole.false_of_gInv P K wf (invariant P K) falseRec_present n e D hl

/-- Exactly the original checked-tier environment antecedents, including
the required stored members at both distinguished slots. -/
def EnvironmentAntecedents (K : Nat → Nat) : Prop :=
  Nonempty (EnvWfT env) ∧ Rcic.F3.StepWApex.envCheck wf = true ∧
  Rcic.F3.StepWDApex.envCheck K wf = true ∧ BoundG K wf ∧ BoundDG K wf ∧
  AxiomFreeEnv' env ∧ env.members 0 = some falseFamMember ∧
  env.members 1 = some falseRecMemberU

theorem environment_antecedents (K : Nat → Nat) : EnvironmentAntecedents K :=
  ⟨⟨wf⟩, w_check, d_check K, boundG K, boundDG K, axiom_free,
    false_present, falseRec_present⟩

def Witness (P : Premises4) (K : Nat → Nat) : Prop :=
  EnvironmentAntecedents K ∧ NormRole.GInv P K wf ∧
  EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx wf)
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
    (NormRole.table_spec P wf).2, env_sound P K, false_mem P, true_mem P,
    distinct P, true_inhabited P, false_empty P, consistent P K⟩

theorem component_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (Witness P K → (Premises4 → False)) :=
  fun h => h (component_witness P K) P

end Rcic.F3.PSet.NormFalseNonvacuity
