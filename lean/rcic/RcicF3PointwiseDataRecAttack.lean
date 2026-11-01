import rcic.RcicF3PointwiseDataRec
import rcic.RcicF3PointwiseNatInvariant
import rcic.RcicF3PointwiseRoleAttack
import rcic.RcicF3NormDataRecAttack

/-!
# Produced pointwise constructor cases and recursion at the actual W node

The original W base table is updated at its family entry with the new
pointwise frame. The actual W-only global candidate proves a comparison
used to transport the already inhabited motive, both stored minors and
ordinary reader to this update. The predecessor is the newly produced
PointwiseRole Nat invariant. Both new public adapters are invoked directly.

This witness composes, at the same Premises4, the separate new installer's
height-omega family witness and this pointwise-update recursion witness.
It does not identify the two tables, produce a new W group invariant or
assert a universal comparison. The additional motive universe is 1;
the family has arity 0. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataRecAttack
open Rcic.Declarative PiIndex RawFamily PropEval
open RawDataRecAttack (σ K base parameter target motive minors)
open NormDataRecAttack (plan)

noncomputable abbrev candidate (P : Premises4) : Frame :=
  PointwiseDataCases.frame P (base P) PendAW.pNode

noncomputable abbrev updated (P : Premises4) : Nat → List Nat → PSet.{4} :=
  RawFamily.table P (base P) PendAWBridge.fd (candidate P)

noncomputable abbrev model (P : Premises4) : Interp.{4} := mkM P (updated P)

noncomputable abbrev context (P : Premises4) : Context :=
  (RawDataRecAttack.context P).withModel (model P)

theorem frame_comparison (P : Premises4) (vs : List Nat) (i : Index.{4}) :
    Equiv (candidate P vs i) (RawFamily.frame P (base P) PendAWBridge.fd vs i) := by
  have h := PointwiseData.frame_equiv_of_global_candidate P (base P) plan
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    (NormDataRecAttack.small_closed P) vs i
  change Equiv (candidate P vs i)
    (RawFamily.frame P (base P) (EvalPlanNormal.fd plan) vs i) at h
  simpa only [NormDataRecAttack.normalized_descriptor] using h

theorem role_comparison (P : Premises4) (vs : List Nat) :
    Equiv (ofFrame P (base P) PendAWBridge.fd (candidate P) vs)
      (RawFamily.role P (base P) PendAWBridge.fd vs) := by
  have h := PointwiseData.role_equiv_of_global_candidate P (base P) plan
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    (NormDataRecAttack.small_closed P) vs
  change Equiv (ofFrame P (base P) (EvalPlanNormal.fd plan) (candidate P) vs)
    (RawFamily.role P (base P) (EvalPlanNormal.fd plan) vs) at h
  simpa only [NormDataRecAttack.normalized_descriptor] using h

theorem tables (P : Premises4) :
    ∀ r vs, Equiv ((RawDataRecAttack.model P).μ r vs) ((model P).μ r vs) := by
  have hb : ∀ r vs, Equiv (base P r vs) (updated P r vs) :=
    RawFamily.table_equiv P (base P) PendAWBridge.fd (candidate P)
      (fun vs => ((NormPendAWRecPkg.actual_values P).fam vs).trans
        (role_comparison P vs).symm)
  intro r vs
  exact (RawDataRecAttack.tables P r vs).symm.trans (hb r vs)

theorem predecessor_faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities natEnvU))
      P (base P) (NormRole.envCtx PendAWGroup.wft)
        (EvalRole.envPlan PendAWGroup.wft) natEnvU :=
  PointwiseNatInvariant.faithful_of_raw _ P (base P) (PointwiseRole.arities_agree natEnvU)
    _ _ NormDataRecAttack.predecessor_context (NormDataRecAttack.predecessor_faithful P)

theorem environment (P : Premises4) : EnvSound (model P) σ K PendAW.pNode.E0 0 :=
  TableSound.environment P (tables P) σ (RawDataRecAttack.environment P)

theorem motive_typed (P : Premises4) :
    (context P).motive ∈ Ed (context P).M
      (den (context P).M (context P).σ (push (context P).parameters ρ0)
        (policyPi (context P).node.a.family.indices
          (.pi (foldApps (.const (context P).node.a.family.ref
            (canonL (context P).node.a.family.member.arity))
            (policyLocals ((context P).node.a.family.parameters.length +
              (context P).node.a.family.indices.length))) (.sort (.param 0))))) := by
  exact (TableSound.value_mem_iff P (tables P) σ _ _ _).mp
    (RawFamilyIHBuilderAttack.motive_mem P (base P))

theorem minors_typed (P : Premises4) :
    TelFits (model P) σ PendAW.pNode.a.minorTypes
      (vcons (motive P) (push [parameter] ρ0)) (minors P) :=
  (TelFits_tables_equiv P (tables P) σ _ _ _).mp (RawDataRecAttack.minors_typed P)

theorem constructor_data (P : Premises4)
    (j : Fin (context P).node.a.constructors.length) (xs : List PSet.{4})
    (hxs : TelFits (context P).M (context P).σ
      ((context P).node.a.constructorViews j).fields
      (push (context P).parameters ρ0) xs) :
    Equiv ((context P).constructorAt j (context P).parameters xs) (dataVal j.val xs) := by
  have hx := (TelFits_tables_equiv P (tables P) σ _ _ _).mpr hxs
  have he : Equiv ((RawDataRecAttack.context P).constructorAt j [parameter] xs)
      ((context P).constructorAt j [parameter] xs) :=
    fapps_congr (tables P _ _) _
  exact he.symm.trans (RawDataRecAttack.constructor_data P j xs hx)

theorem original_cases (P : Premises4) :
    ∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
      z ∈ candidate P [] i →
      ∃ (j : Fin PendAW.pNode.a.constructors.length) (xs : List PSet.{4}),
        TelFits (model P) σ PendAW.pNode.a.family.parameters ρ0 [parameter] ∧
        TelFits (model P) σ (PendAW.pNode.a.constructorViews j).fields
          (push [parameter] ρ0) xs ∧
        i = key ([parameter] ++ (context P).indicesAt j [parameter] xs) ∧
        Equiv z (dataVal j.val xs) :=
  PointwiseDataCases.original_cases P (base P) K (context P) rfl
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl PendAWGroup.ctorClasses
    rfl PendAW.membersT (PendAWGroup.boundG K) (PendAWGroup.boundDG 1)
    NormDataRecAttack.matching_parameters (PointwiseNatInvariant.gInv P K)
    (PointwiseRole.arities natEnvU) (PointwiseRole.arities_agree natEnvU)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    NormDataRecAttack.predecessor_context NormDataRecAttack.predecessor_plans
    (predecessor_faithful P) (fun _ h => (List.not_mem_nil _ h).elim)
    (by change 1 ≠ 0; decide)

theorem produced (P : Premises4) :
    ∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
      z ∈ candidate P [] i →
      RecPlan.nodeCore (model P) PendAW.pNode (minors P) z ∈
        PiRawMotiveAny.guarded (model P) σ 1 ((model P).μ 4 [])
          (motive P) [parameter] [] (push [parameter] ρ0) i z :=
  PointwiseDataRec.nodeCore_guarded P (base P) K (context P) rfl
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl PendAWGroup.ctorClasses
    rfl PendAW.membersT (PendAWGroup.boundG K) (PendAWGroup.boundDG 1)
    NormDataRecAttack.matching_parameters (PointwiseNatInvariant.gInv P K)
    (PointwiseRole.arities natEnvU) (PointwiseRole.arities_agree natEnvU)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    NormDataRecAttack.predecessor_context NormDataRecAttack.predecessor_plans
    (predecessor_faithful P) (fun _ h => (List.not_mem_nil _ h).elim)
    (by change 1 ≠ 0; decide) (environment P) (.param 0) rfl
    (motive_typed P) (minors_typed P) (constructor_data P)

theorem omega_mem (P : Premises4) : fxZW P ∈ candidate P [] (key [parameter]) :=
  mem_congr_right (frame_comparison P [] _).symm (RawDataRecAttack.omega_mem P)

theorem result_mem (P : Premises4) :
    RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P) ∈ target P := by
  have h := produced P (key [parameter]) (fxZW P) rfl (omega_mem P)
  have hzOld := RawDataRecAttack.family_mem P (fxZW P) (RawDataRecAttack.omega_mem P)
  have hz : fxZW P ∈ Ed (model P) (fapps ((model P).μ 4 []) [parameter]) :=
    mem_congr_right (ed_congr (model P) (fapps_congr (tables P 4 []) [parameter])) hzOld
  have hm := RawDataRecAttack.motive_apply P (fxZW P) hzOld
  have hT : fapps (motive P) [fxZW P] ∈ (model P).U 1 :=
    mem_congr_left hm.symm (RawFamilyIHBuilderAttack.target_type P (base P))
  have hg := PiRawMotiveAny.guarded_key (model P) σ 1 ((model P).μ 4 [])
    (motive P) [parameter] [] (push [parameter] ρ0) [] (fxZW P) True.intro hz hT
  exact mem_congr_right (hg.trans ((ed_congr (model P) hm).trans
    (ed_tyv (model P) (admissible_dich (RawWFrame.raw_admissible P (base P)) [] _)))) h

theorem result_not_empty (P : Premises4) :
    ¬ Equiv (RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P)) pempty := by
  have h := (RawWFrame.raw_admissible P (base P) [] (key [parameter])).2
  change (if (1 : Nat) = 0 then _ else _) at h
  rw [if_neg (by decide : (1 : Nat) ≠ 0)] at h
  exact h _ (result_mem P)

def Witness (P : Premises4) : Prop :=
  PointwiseRoleAttack.Witness P ∧ PointwiseNatInvariant.Witness P ∧
  (∀ vs i, Equiv (candidate P vs i) (RawFamily.frame P (base P) PendAWBridge.fd vs i)) ∧
  EnvSound (model P) σ K PendAW.pNode.E0 0 ∧
  TelFits (model P) σ PendAW.pNode.a.minorTypes
    (vcons (motive P) (push [parameter] ρ0)) (minors P) ∧
  (∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
    z ∈ candidate P [] i →
    ∃ (j : Fin PendAW.pNode.a.constructors.length) (xs : List PSet.{4}),
      TelFits (model P) σ PendAW.pNode.a.family.parameters ρ0 [parameter] ∧
      TelFits (model P) σ (PendAW.pNode.a.constructorViews j).fields
        (push [parameter] ρ0) xs ∧
      i = key ([parameter] ++ (context P).indicesAt j [parameter] xs) ∧
      Equiv z (dataVal j.val xs)) ∧
  (∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
    z ∈ candidate P [] i →
    RecPlan.nodeCore (model P) PendAW.pNode (minors P) z ∈
      PiRawMotiveAny.guarded (model P) σ 1 ((model P).μ 4 [])
        (motive P) [parameter] [] (push [parameter] ρ0) i z) ∧
  fxZW P ∈ candidate P [] (key [parameter]) ∧
  RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P) ∈ target P ∧
  ¬ Equiv (RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P)) pempty ∧
  σ 0 = 1 ∧ σ 0 ≠ σOf [] 0

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseRoleAttack.component_witness P, PointwiseNatInvariant.component_witness P,
    frame_comparison P, environment P, minors_typed P, original_cases P, produced P,
    omega_mem P, result_mem P, result_not_empty P, rfl, by decide⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseDataRecAttack
