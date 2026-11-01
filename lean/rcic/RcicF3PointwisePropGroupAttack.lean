import rcic.RcicF3PointwisePropGroup
import rcic.RcicF3NormPropGroupAttack

/-!
# Actual AccR composition at the separate pointwise table

The new Prop/anySort group and complete recursor producers are called
directly with the original admission, walk and bounds. Every semantic
conjunct below uses the same new installed table. Its original constructor
argument tuple is inhabited, while the selected recursive child domain is
literally empty. No inhabited AccR child or imported Acc-on-Nat.lt is claimed.

The old planned raw-role StepAG refutation is retained literally and uses
the same Premises4. This is a concrete component witness, not a universal
local-candidate, A-axis or checked-apex producer. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropGroupAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PlanPropEndAttack
open EvalPlanValueAttack (plan)
open PropEvalAdmittedInputsAttack (bound)

theorem ctorClasses : ∀ c ∈ [(1, accIntroMember)],
    c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P AccEnv.accEnvWfT

theorem faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities accEnv))
      P (table P) (NormRole.envCtx AccEnv.accEnvWfT)
      (EvalRole.envPlan AccEnv.accEnvWfT) accEnv :=
  (PointwiseRole.table_spec P AccEnv.accEnvWfT).2.1

theorem canonical_plan :
    EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl ctorClasses rfl AccEnv.accMembersT = plan := by
  have h := EvalInstalledAttack.canonical_plan
  change some (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    (rr := 2) (rm := accRecMember) rfl ctorClasses rfl AccEnv.accMembersT) = some plan at h
  exact Option.some.inj h

theorem uniform_prop : UniformProp
    (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl ctorClasses rfl AccEnv.accMembersT).node.a.family.resultLevel := by
  rw [canonical_plan]
  intro σ
  rfl

theorem policy :
    (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl ctorClasses rfl AccEnv.accMembersT).node.a.policy = .anySort := by
  rw [canonical_plan]
  rfl

theorem produced_gInv (P : Premises4) :
    PointwiseRole.GInv P bound AccEnv.accEnvWfT :=
  PointwisePropGroup.group_step P bound .empty rfl ctorClasses rfl AccEnv.accMembersT
    uniform_prop policy ⟨PlanPropStepAttack.pNode, PlanPropStepAttack.pendA⟩
    PlanPropStepAttack.walkAgree (PlanPropStepAttack.boundG bound)
    PlanPropStepAttack.boundDG (PointwiseRole.gInv_empty P bound)

/-- The complete producer is also invoked directly, with the actual
faithful table and the produced empty predecessor. -/
theorem package (P : Premises4) : RecPkg P (table P) bound accEnv 2 accRecMember :=
  PointwisePropRecPkg.rec_pkg P (table P) bound
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    .empty rfl ctorClasses rfl AccEnv.accMembersT
    (PlanPropStepAttack.boundG bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
    uniform_prop policy ⟨PlanPropStepAttack.pNode, PlanPropStepAttack.pendA⟩

theorem all_sound (P : Premises4) : AllSound P (table P) bound accEnv :=
  (produced_gInv P (PointwiseRole.arities accEnv) (PointwiseRole.arities_agree accEnv)
    (NormRole.envCtx AccEnv.accEnvWfT) (fun _ _ => rfl)
    (EvalRole.envPlan AccEnv.accEnvWfT) (fun _ _ => rfl) (table P) (faithful P)).1

theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ [.sort .zero, accField] ρ0 [parameter, pempty] :=
  TelFits.append (PropEvalAttack.parameters_fit P (table P))
    (PropEvalAttack.original_field_fit P (table P))

theorem constructor_mem (P : Premises4) :
    fapps (table P 1 []) [parameter, pempty] ∈
      Ed (mkM P (table P)) (fapp (table P 0 []) parameter) := by
  have hm := ((all_sound P 1 accIntroMember rfl) σ [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1
  change table P 1 [] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi [.sort .zero, accField]
      (accApp (.bvar 1)))) at hm
  exact mem_fapps (mkM P (table P)) σ (accApp (.bvar 1))
    [.sort .zero, accField] ρ0 (table P 1 []) [parameter, pempty] hm (arguments_fit P)

def Witness (P : Premises4) : Prop :=
  PointwiseRole.GInv P bound AccEnv.accEnvWfT ∧
  EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities accEnv))
    P (table P) (NormRole.envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  EvalRole.ReadsClosed (NormRole.envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  AllSound P (table P) bound accEnv ∧
  RecPkg P (table P) bound accEnv 2 accRecMember ∧
  Equiv (Ed (mkM P (table P)) parameter) pempty ∧
  TelFits (mkM P (table P)) σ [.sort .zero, accField] ρ0 [parameter, pempty] ∧
  fapps (table P 1 []) [parameter, pempty] ∈
    Ed (mkM P (table P)) (fapp (table P 0 []) parameter) ∧
  ¬ PlanRole.StepAG role P (fun _ => 1)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨produced_gInv P, faithful P, (PointwiseRole.table_spec P AccEnv.accEnvWfT).2.2,
    all_sound P, package P, parameter_empty P (table P), arguments_fit P,
    constructor_mem P, PlanPropStepAttack.stepAG_false P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwisePropGroupAttack
