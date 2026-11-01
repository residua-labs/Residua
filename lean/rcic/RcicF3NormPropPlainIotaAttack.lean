import rcic.RcicF3NormPropPlainTrue
import rcic.RcicF3PlanPropEndAttack
import rcic.RcicF3NormDPlanBridgeAttack

/-!
# Inhabited data-valued iota at the actual normalized True table

The actual admitted True constructor is an inhabitant of the installed
family. A motive at the extra universe slot returns a singleton data type;
its minor is that type's nonempty data element. All three recursor
arguments fit the original stored telescope in the same installed table.

The new typed iota producer is invoked at the concrete legacy redex, and
its result is compared with the production endpoint through the actual
stored abstraction. This is a nonvacuous semantic equation: both the
installed recursor application and indexed endpoint return the data
element. The retained conjunction carries the actual AccR/W boundaries
and height-omega witness from the prior component. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormPropPlainIotaAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open NormPropPlainTrue (plan table witness)
open PlanPropEndAttack (datum domain)

def bound : Nat → Nat := fun _ => 1
def σ : Nat → Nat := σOf [1]

noncomputable def motive (P : Premises4) : PSet.{4} :=
  piLam (mkM P (table P)) σ (fun _ => tyv domain) ρ0
    (.pi (.const 0 []) (.sort (.param 0)))

noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons datum (vcons (motive P) ρ0)

def domains : List (Expr Nat) :=
  [.pi (.const 0 []) (.sort (.param 0)), .app (.bvar 0) (.const 1 []), .const 0 []]

noncomputable def arguments (P : Premises4) : List PSet.{4} :=
  [motive P, datum, table P 1 []]

noncomputable def result (P : Premises4) : PSet.{4} :=
  EvalPlanValue.endValue (mkM P (table P)) σ plan (push (arguments P) ρ0)

theorem motive_mem (P : Premises4) :
    motive P ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) σ ρ0 (.pi (.const 0 []) (.sort (.param 0)))) := by
  apply piLam_mem (mkM P (table P)) σ (envResp_const _) _
  intro z hz
  exact mem_congr_right (ed_tyv (mkM P (table P)) (U4_dich 1)).symm
    (PiRawIHAnyAttack.type_mem P)

theorem motive_at_intro (P : Premises4) :
    Equiv (fapp (motive P) (table P 1 [])) (tyv domain) :=
  beta_val (mkM P (table P)) (fun _ _ _ => Equiv.rfl)
    (NormPropPlainTrue.inhabited_family P)

theorem minor_mem (P : Premises4) :
    datum ∈ Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) :=
  mem_congr_right (ed_congr (mkM P (table P)) (motive_at_intro P)).symm
    (mem_congr_right (ed_tyv (mkM P (table P)) PiRawIHAnyAttack.domain_dich).symm
      (mem_singleton.mpr Equiv.rfl))

/-- The original stored recursor telescope is inhabited at all its binders. -/
theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ domains ρ0 (arguments P) :=
  ⟨motive_mem P, minor_mem P, NormPropPlainTrue.inhabited_family P, True.intro⟩

theorem application_mem (P : Premises4) :
    fapps (table P 2 [1]) (arguments P) ∈
      Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) := by
  have h := ((NormPropPlainTrue.package P bound).1 σ [.param 0] ρ0 rfl
    (fun l hl => by
      have he : l = .param 0 := List.mem_singleton.mp hl
      subst l
      exact Nat.le_refl 1)).1
  change table P 2 [1] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi domains (.app (.bvar 2) (.bvar 0)))) at h
  exact mem_fapps (mkM P (table P)) σ (.app (.bvar 2) (.bvar 0)) domains ρ0
    (table P 2 [1]) (arguments P) h (arguments_fit P)

theorem canonical_plan : EvalRole.envPlan trueEnvUWfT 2 = some plan := rfl

theorem recursor_role : NormRole.envCtx trueEnvUWfT 2 =
    .recursor (EvalPlanNormal.fd plan) := by
  change groupRoles (EvalPlanNormal.fd plan) 0 2 (fun _ => .plain) 2 = _
  exact groupRoles_at_rr _ (by decide : 0 < 2) _

theorem recursor_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 2 vs)
      (EvalPlanValue.memberValue (mkM P (table P)) (σOf vs) plan trueRecMemberU) := by
  have h := NormPropPlainTrue.faithful P 2 trueRecMemberU rfl vs
  rw [recursor_role, canonical_plan] at h
  exact h

/-- This invokes the new typed iota theorem on the concrete, inhabited
redex. Both endpoints inhabit the same actual motive application. -/
theorem redex_equiv (P : Premises4) :
    Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) datum := by
  have hFamily := NormCandidatePrefix.family_equation_of_group P (table P)
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) EnvWfT.empty rfl NormPropPlainTrue.ctorClasses
    rfl trueMembersT (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (NormPropPlainTrue.faithful P)
  let j : Fin plan.node.a.constructors.length :=
    ⟨0, by rw [NormPropPlainTrue.count]; decide⟩
  have h := NormPropPlainIota.iota_eq P (table P) bound plan trueFamMember
    [(1, trueIntroMember)] EnvWfT.empty rfl NormPropPlainTrue.ctorClasses rfl trueMembersT
    (NormPropPlainTrue.bound bound) (NormRole.gInv_empty P bound)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => nomatch hm)
    hFamily (recursor_value P) (NormPropPlainTrue.noFun plan.node)
    (NormPropPlainTrue.fields_free plan.node) witness rfl rfl j rfl
    (NormPropPlainTrue.constructor_member plan.node j).symm σ (ρ P)
    (by rw [(NormPropPlainTrue.family plan.node).2.2]; rfl)
    (NormPropPlainTrue.policy plan.node)
    (fun u hu => by
      change u ∈ [1] at hu
      rw [List.mem_singleton.mp hu]
      exact Nat.le_refl 1)
    True.intro (application_mem P) (minor_mem P)
  exact h

theorem lhs_application (P : Premises4) :
    den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness) =
      fapps (table P 2 [1]) (arguments P) := rfl

/-- The installed application is the actual production endpoint at the
same fitting argument tuple, not an auxiliary endpoint operation. -/
theorem application_result (P : Premises4) :
    Equiv (fapps (table P 2 [1]) (arguments P)) (result P) := by
  have h := fapps_piLam (mkM P (table P)) σ
    (EvalPlanValue.endValue_resp (mkM P (table P)) σ plan)
    (.app (.bvar 2) (.bvar 0)) domains ρ0 (arguments P) (arguments_fit P)
  change Equiv
    (fapps (EvalPlanValue.memberValue (mkM P (table P)) σ plan trueRecMemberU)
      (arguments P)) (result P) at h
  exact (fapps_congr (recursor_value P [1]) (arguments P)).trans h

theorem result_equiv (P : Premises4) : Equiv (result P) datum := by
  have h := redex_equiv P
  rw [lhs_application] at h
  exact (application_result P).symm.trans h

theorem result_mem (P : Premises4) : result P ∈ domain :=
  mem_congr_left (result_equiv P).symm (mem_singleton.mpr Equiv.rfl)

theorem result_ne_empty (P : Premises4) : ¬ Equiv (result P) pempty :=
  fun h => dataVal_ne_pempty _ _ ((result_equiv P).symm.trans h)

def Witness (P : Premises4) : Prop :=
  NormPropPlainTrue.Witness P bound ∧ NormDPlanBridgeAttack.Witness P ∧
  plan.node.a.family.member.arity = 0 ∧ σ 0 = 1 ∧
  TelFits (mkM P (table P)) σ domains ρ0 (arguments P) ∧
  datum ∈ Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) ∧
  fapps (table P 2 [1]) (arguments P) ∈
    Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) ∧
  Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) datum ∧
  Equiv (fapps (table P 2 [1]) (arguments P)) (result P) ∧
  Equiv (result P) datum ∧ result P ∈ domain ∧ ¬ Equiv (result P) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPropPlainTrue.component_witness P bound,
    NormDPlanBridgeAttack.component_witness P,
    by rw [NormPropPlainTrue.family_member]; rfl,
    rfl, arguments_fit P, minor_mem P, application_mem P, redex_equiv P,
    application_result P, result_equiv P, result_mem P, result_ne_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropPlainIotaAttack
