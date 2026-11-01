import rcic.RcicF3PointwisePropPlainIota
import rcic.RcicF3PointwisePropCtor
import rcic.RcicF3NormPropPlainIotaAttack

/-!
# Inhabited data-valued plain-Prop iota at the pointwise True table

The actual admitted True group and legacy witness are unchanged syntax.
The NEW constructor and complete recursor producers establish membership
at the actual pointwise table. Its extra motive universe is evaluated at 1
and returns a singleton DATA type, so both the installed application and
actual indexed production endpoint return an explicitly nonempty value.

The old True invariant/table is not substituted. The typed argument tuple,
complete legacy redex, full level vector and same-table memberships are
retained. This is a concrete iota component, not universal DATA local
candidate production or apex closure. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropPlainIotaAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open NormPropPlainTrue (plan witness)
open PlanPropEndAttack (datum domain)
open NormPropPlainIotaAttack (bound σ domains)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P trueEnvUWfT

theorem faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities trueEnvU))
      P (table P) (NormRole.envCtx trueEnvUWfT)
      (EvalRole.envPlan trueEnvUWfT) trueEnvU :=
  (PointwiseRole.table_spec P trueEnvUWfT).2.1

theorem uniform_prop : UniformProp plan.node.a.family.resultLevel := by
  intro σ
  rw [(NormPropPlainTrue.family plan.node).2.2]
  rfl

theorem package (P : Premises4) (K : Nat → Nat) :
    RecPkg P (table P) K trueEnvU 2 trueRecMemberU :=
  PointwisePropPlainIota.rec_pkg P (table P) K
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) EnvWfT.empty rfl NormPropPlainTrue.ctorClasses
    rfl trueMembersT (NormPropPlainTrue.bound K) (PointwiseRole.gInv_empty P K)
    (PointwiseRole.arities trueEnvU) (fun _ _ h => nomatch h)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
    uniform_prop (NormPropPlainTrue.policy plan.node)
    (NormPropPlainTrue.noFun plan.node) (NormPropPlainTrue.fields_free plan.node)

theorem constructor_sound (P : Premises4) (K : Nat → Nat) :
    MemberSound P (table P) K 1 trueIntroMember := by
  let j : Fin plan.node.a.constructors.length :=
    ⟨0, by rw [NormPropPlainTrue.count]; decide⟩
  have h := PointwisePropCtor.member_sound P (table P) K
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) EnvWfT.empty rfl NormPropPlainTrue.ctorClasses
    rfl trueMembersT (NormPropPlainTrue.bound K) (PointwiseRole.gInv_empty P K)
    (PointwiseRole.arities trueEnvU) (PointwiseRole.arities_agree trueEnvU)
    (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) uniform_prop j
  change MemberSound P (table P) K 1 (plan.node.a.constructors[j.val]) at h
  rw [NormPropPlainTrue.constructor_member] at h
  exact h

theorem inhabited_family (P : Premises4) :
    table P 1 [] ∈ Ed (mkM P (table P)) (table P 0 []) :=
  (constructor_sound P bound (fun _ => 0) [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1

noncomputable def motive (P : Premises4) : PSet.{4} :=
  piLam (mkM P (table P)) σ (fun _ => tyv domain) ρ0
    (.pi (.const 0 []) (.sort (.param 0)))

noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons datum (vcons (motive P) ρ0)

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
    (inhabited_family P)

theorem minor_mem (P : Premises4) :
    datum ∈ Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) :=
  mem_congr_right (ed_congr (mkM P (table P)) (motive_at_intro P)).symm
    (mem_congr_right (ed_tyv (mkM P (table P)) PiRawIHAnyAttack.domain_dich).symm
      (mem_singleton.mpr Equiv.rfl))

/-- The original stored recursor telescope is inhabited at all its binders. -/
theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ domains ρ0 (arguments P) :=
  ⟨motive_mem P, minor_mem P, inhabited_family P, True.intro⟩

theorem application_mem (P : Premises4) :
    fapps (table P 2 [1]) (arguments P) ∈
      Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) := by
  have h := ((package P bound).1 σ [.param 0] ρ0 rfl
    (fun l hl => by
      have he : l = .param 0 := List.mem_singleton.mp hl
      subst l
      exact Nat.le_refl 1)).1
  change table P 2 [1] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi domains (.app (.bvar 2) (.bvar 0)))) at h
  exact mem_fapps (mkM P (table P)) σ (.app (.bvar 2) (.bvar 0)) domains ρ0
    (table P 2 [1]) (arguments P) h (arguments_fit P)

theorem recursor_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 2 vs)
      (EvalPlanValue.memberValue (mkM P (table P)) (σOf vs) plan trueRecMemberU) := by
  have h := faithful P 2 trueRecMemberU rfl vs
  rw [NormPropPlainIotaAttack.recursor_role, NormPropPlainIotaAttack.canonical_plan] at h
  exact h

/-- This invokes the new typed iota theorem on the concrete, inhabited
redex. Both endpoints inhabit the same actual motive application. -/
theorem redex_equiv (P : Premises4) :
    Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) datum := by
  have hFamily := PointwisePropPrefix.family_equation_of_group P (PointwiseRole.arities trueEnvU) (table P)
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) EnvWfT.empty rfl NormPropPlainTrue.ctorClasses
    rfl trueMembersT (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (faithful P) uniform_prop
  let j : Fin plan.node.a.constructors.length :=
    ⟨0, by rw [NormPropPlainTrue.count]; decide⟩
  have h := PointwisePropPlainIota.iota_eq P (table P) bound plan trueFamMember
    [(1, trueIntroMember)] EnvWfT.empty rfl NormPropPlainTrue.ctorClasses rfl trueMembersT
    (NormPropPlainTrue.bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities trueEnvU) (fun _ _ h => nomatch h)
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
  (∀ K, RecPkg P (table P) K trueEnvU 2 trueRecMemberU ∧
    MemberSound P (table P) K 1 trueIntroMember) ∧
  plan.node.a.family.member.arity = 0 ∧ σ 0 = 1 ∧
  table P 1 [] ∈ Ed (mkM P (table P)) (table P 0 []) ∧
  TelFits (mkM P (table P)) σ domains ρ0 (arguments P) ∧
  datum ∈ Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) ∧
  fapps (table P 2 [1]) (arguments P) ∈
    Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) ∧
  Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) datum ∧
  Equiv (fapps (table P 2 [1]) (arguments P)) (result P) ∧
  Equiv (result P) datum ∧ result P ∈ domain ∧ ¬ Equiv (result P) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨(fun K => ⟨package P K, constructor_sound P K⟩),
    by rw [NormPropPlainTrue.family_member]; rfl,
    rfl, inhabited_family P, arguments_fit P, minor_mem P, application_mem P, redex_equiv P,
    application_result P, result_equiv P, result_mem P, result_ne_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwisePropPlainIotaAttack
