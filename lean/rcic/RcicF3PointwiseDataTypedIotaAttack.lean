import rcic.RcicF3PointwiseDataGroupAttack
import rcic.RcicF3NormDataTypedIotaAttack

/-!
# An inhabited typed legacy redex at the SAME new pointwise W table

The existing literal typed witness is reused as syntax/admission data: its
leaf row has no fields, while the other actual W row retains positive Pi
depth. Every semantic argument and endpoint below is rebuilt at the NEW
installed table. Its motive targets the NEW pointwise fibre itself, and
both stored minors are inhabited there by the actual height-omega value.

The complete new member producer pays constructor/recursor constants and
hereditary lookup/application proofs. The public new iota producer is then
called on the actual typed endpoints, full context, original bounds and
extra motive universe 1. No old-table soundness or current-W package is a
supplied premise. This remains the literal legacy leaf equation, with no
shape-iota claim for the higher-order row. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace Rcic.F3.PSet.PointwiseDataTypedIotaAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex
open NormPendAW (plan)
open PointwiseRoleAttack (table)
open RawDataRecAttack (parameter)
open NormDataTypedIotaAttack (σ bound motiveDomain preDomains majorDomain domains body Γ
  resultType rec_type witness lhs_typed rhs_typed typed_iota typed_bounds rec_levels)

private def recStored : CheckedMember :=
  ⟨.recursorM, 1, policyPi domains body, none⟩

private theorem rec_present : PendAW.eAll.members 7 = some recStored :=
  congrArg (fun T => some (CheckedMember.mk .recursorM 1 T none)) rec_type

noncomputable def target (P : Premises4) : PSet.{4} :=
  PointwiseDataAttack.candidate P (table P) [] (key [parameter])

theorem target_type (P : Premises4) : tyv (target P) ∈ U W4 1 := by
  obtain ⟨i, hi⟩ := (PointwiseDataAttack.exact_stage P (table P) [] (key [parameter])).1
  exact mem_sImage_tyv.mpr ⟨target P, mem_sep.mpr
    ⟨i, (dich_congr hi.symm).mp
      (admissible_dich (PointwiseDataAttack.admissible P (table P)) [] _), hi⟩,
    Equiv.rfl⟩

private theorem hsound_bvar (M : Interp.{4}) (i : Nat) (A : Expr Nat)
    (h : lookupType Γ i = some A) :
    HSoundT M σ (HasTyT.bvar (E := PendAW.eAll) (n := 1) Γ i A h) :=
  fun ρ hρ => fits_lookupType M σ Γ ρ hρ i A h

private theorem hsound_app (M : Interp.{4})
    {f a A B : Expr Nat}
    (df : HasTyT PendAW.eAll 1 Γ f (.pi A B))
    (da : HasTyT PendAW.eAll 1 Γ a A)
    (hf : HSoundT M σ df) (ha : HSoundT M σ da) :
    HSoundT M σ (.app Γ f a A B df da) := by
  refine ⟨fun ρ hρ => ?_, hf, ha⟩
  change den M σ ρ (.app f a) ∈ Ed M (den M σ ρ (instantiate0 a B))
  rw [den_inst0]
  exact app_mem M (den_resp M σ ρ B) (hf.root ρ hρ) (ha.root ρ hρ)

/-- Only constant membership, lookup and application soundness are used.
No environment-iota premise occurs in these two hereditary derivations. -/
theorem lhs_hsound (P : Premises4) :
    HSoundT (mkM P (table P)) σ lhs_typed := by
  dsimp only [lhs_typed]
  apply hsound_app
  · apply hsound_app
    · apply hsound_app
      · apply hsound_app
        · apply hsound_app
          · intro ρ _
            exact (PointwiseDataGroupAttack.all_sound P 1 7 recStored rec_present
              σ [.param 0] ρ rfl rec_levels).1
          · exact hsound_bvar _ _ _ _
        · exact hsound_bvar _ _ _ _
      · exact hsound_bvar _ _ _ _
    · exact hsound_bvar _ _ _ _
  · apply hsound_app
    · intro ρ _
      exact (PointwiseDataGroupAttack.all_sound P 1 5 PendAW.leaf rfl σ [] ρ rfl
        (fun _ h => (List.not_mem_nil _ h).elim)).1
    · exact hsound_bvar _ _ _ _

theorem rhs_hsound (P : Premises4) :
    HSoundT (mkM P (table P)) σ rhs_typed := hsound_bvar _ _ _ _

noncomputable def motive (P : Premises4) : PSet.{4} :=
  piLam (mkM P (table P)) σ (fun _ => tyv (target P))
    (push [parameter] ρ0) motiveDomain

noncomputable def major (P : Premises4) : PSet.{4} :=
  fapps (table P 5 []) [parameter]

theorem parameter_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ [.sort (.succ .zero)] ρ0 [parameter] :=
  PendAWBridge.argsFit P (table P) pempty

theorem motive_mem (P : Premises4) :
    motive P ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) σ (push [parameter] ρ0) motiveDomain) := by
  apply piLam_mem (mkM P (table P)) σ (envResp_const _) _
  intro z hz
  exact mem_congr_right (ed_tyv (mkM P (table P)) (U4_dich 1)).symm
    (target_type P)

/-- Constructor membership comes from the new bounded DATA walk/member chain. -/
theorem major_mem (P : Premises4) :
    major P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [parameter]) := by
  have h := (PointwiseDataGroupAttack.all_sound P 1 5 PendAW.leaf rfl σ [] ρ0 rfl
    (fun _ hl => (List.not_mem_nil _ hl).elim)).1
  change table P 5 [] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi [.sort (.succ .zero)]
      (.app (.const 4 []) (.bvar 0)))) at h
  exact mem_fapps (mkM P (table P)) σ (.app (.const 4 []) (.bvar 0))
    [.sort (.succ .zero)] ρ0 (table P 5 []) [parameter] h (parameter_fit P)

theorem node_mem (P : Premises4) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) σ (push [parameter] ρ0) PendAW.field)) :
    fapps (table P 6 []) [parameter, x] ∈
      Ed (mkM P (table P)) (fapps (table P 4 []) [parameter]) := by
  have h := (PointwiseDataGroupAttack.all_sound P 1 6 PendAW.node rfl σ [] ρ0 rfl
    (fun _ hl => (List.not_mem_nil _ hl).elim)).1
  change table P 6 [] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi [.sort (.succ .zero), PendAW.field]
      (.app (.const 4 []) (.bvar 1)))) at h
  exact mem_fapps (mkM P (table P)) σ (.app (.const 4 []) (.bvar 1))
    [.sort (.succ .zero), PendAW.field] ρ0 (table P 6 []) [parameter, x] h
    ⟨(parameter_fit P).1, hx, True.intro⟩

theorem motive_apply (P : Premises4) (z : PSet.{4})
    (hz : z ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [parameter])) :
    Equiv (fapp (motive P) z) (tyv (target P)) :=
  fapps_piLam (mkM P (table P)) σ (envResp_const _) (.sort (.param 0))
    [.app (.const 4 []) (.bvar 0)] (push [parameter] ρ0) [z] ⟨hz, True.intro⟩

theorem omega_in_motive (P : Premises4) (z : PSet.{4})
    (hz : z ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [parameter])) :
    fxZW P ∈ Ed (mkM P (table P)) (fapp (motive P) z) := by
  exact mem_congr_right ((ed_congr (mkM P (table P)) (motive_apply P z hz)).trans
    (ed_tyv (mkM P (table P))
      (admissible_dich (PointwiseDataAttack.admissible P (table P)) [] _))).symm
    (PointwiseDataAttack.omega_mem P (table P))

noncomputable def second (P : Premises4) : PSet.{4} :=
  piLam (mkM P (table P)) σ (fun _ => fxZW P)
    (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
    RawDataRecAttack.nodeMinor

theorem second_mem (P : Premises4) :
    second P ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) σ
        (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
        RawDataRecAttack.nodeMinor) := by
  apply piLam_mem (mkM P (table P)) σ (envResp_const (fxZW P))
  change ∀ x, x ∈ Ed (mkM P (table P)) (den (mkM P (table P)) σ
      (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
      RawDataRecAttack.nodeField) →
    ∀ ih, ih ∈ Ed (mkM P (table P)) (den (mkM P (table P)) σ
      (vcons x (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0))))
      RawDataRecAttack.nodeIH) → _
  intro x hx ih _
  have hd := den_lift0_push (mkM P (table P)) σ [motive P, fxZW P]
    (push [parameter] ρ0) PendAW.field
  change den (mkM P (table P)) σ
    (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
    RawDataRecAttack.nodeField = den (mkM P (table P)) σ
      (push [parameter] ρ0) PendAW.field at hd
  rw [hd] at hx
  change fxZW P ∈ Ed (mkM P (table P))
    (fapp (motive P) (fapps (table P 6 []) [parameter, x]))
  exact omega_in_motive P _ (node_mem P x hx)

noncomputable def prefixValues (P : Premises4) : List PSet.{4} :=
  [parameter, motive P, fxZW P, second P]
noncomputable def ρ (P : Premises4) : Nat → PSet.{4} := push (prefixValues P) ρ0
noncomputable def arguments (P : Premises4) : List PSet.{4} :=
  prefixValues P ++ [major P]

/-- Both minors are present, including the higher-order row's typed IH binder. -/
theorem prefix_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ preDomains ρ0 (prefixValues P) :=
  ⟨(parameter_fit P).1, motive_mem P,
    omega_in_motive P _ (major_mem P), second_mem P, True.intro⟩

theorem context_fits (P : Premises4) : Fits (mkM P (table P)) σ Γ (ρ P) := by
  have h := fits_prefixContext (mkM P (table P)) σ preDomains ρ0
    (prefixValues P) (prefix_fit P) 4 (by decide)
  exact h

theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ domains ρ0 (arguments P) :=
  TelFits.append (prefix_fit P) ⟨major_mem P, True.intro⟩

theorem rhs_mem (P : Premises4) :
    den (mkM P (table P)) σ (ρ P) (iotaRhsOf witness) ∈
      Ed (mkM P (table P)) (den (mkM P (table P)) σ (ρ P) resultType) :=
  omega_in_motive P _ (major_mem P)

/-- The new stored-member producer pays the application before iota is used. -/
theorem lhs_mem (P : Premises4) :
    den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness) ∈
      Ed (mkM P (table P)) (den (mkM P (table P)) σ (ρ P) resultType) := by
  have h := (PointwiseDataGroupAttack.all_sound P 1 7 PendAW.recMem rfl σ [.param 0] ρ0 rfl
    (fun l hl => by
      rw [List.mem_singleton.mp hl]
      exact Nat.le_refl 1)).1
  rw [rec_type] at h
  change table P 7 [1] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi domains body)) at h
  exact mem_fapps (mkM P (table P)) σ body domains ρ0
    (table P 7 [1]) (arguments P) h (arguments_fit P)

theorem recursor_role : NormRole.envCtx PendAWGroup.wft 7 =
    .recursor (EvalPlanNormal.fd plan) := by
  rw [PendAWGroup.wft, NormRole.envCtx_group]
  exact groupRoles_at_rr _ (by decide : 4 < 7) _

theorem recursor_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 7 vs)
      (EvalPlanValue.memberValue (mkM P (table P)) (σOf vs) plan PendAW.recMem) := by
  have h := PointwiseRoleAttack.faithful P 7 PendAW.recMem rfl vs
  rw [recursor_role, NormPendAW.canonical_plan] at h
  exact h

theorem redex_equiv (P : Premises4) :
    Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) (fxZW P) := by
  have hI := PointwiseDataRecPkg.iota_at P (table P) bound
    (f := 4) (fm := PendAW.fam) (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
    (rr := 7) (rm := PendAW.recMem) natEnvUWfT rfl PendAWGroup.ctorClasses
    rfl PendAW.membersT (PendAWGroup.boundG bound) (PendAWGroup.boundDG 1)
    NormDataRecMemAttack.matching_parameters (PointwiseNatInvariant.gInv P bound)
    (PointwiseRole.arities PendAW.eAll) PointwiseRoleAttack.metadata
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (PointwiseRoleAttack.faithful P)
    NormDataRecMemAttack.type_family
    PendAW.eAll (fun _ _ h => h)
  exact hI PendAW.eAll (fun _ _ h => h) witness rfl σ 1 Γ resultType (ρ P)
    lhs_typed (lhs_hsound P) ⟨4, _, P.good _ rfl, typed_bounds.1⟩
    rhs_typed (rhs_hsound P) rec_levels (context_fits P) (lhs_mem P) (rhs_mem P)

noncomputable def result (P : Premises4) : PSet.{4} :=
  EvalPlanValue.endValue (mkM P (table P)) σ plan (push (arguments P) ρ0)

theorem application_result (P : Premises4) :
    Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) (result P) := by
  have h := fapps_piLam (mkM P (table P)) σ
    (EvalPlanValue.endValue_resp (mkM P (table P)) σ plan)
    body domains ρ0 (arguments P) (arguments_fit P)
  have hR := recursor_value P [1]
  change Equiv (table P 7 [1])
    (piLam (mkM P (table P)) σ (EvalPlanValue.endValue (mkM P (table P)) σ plan)
      ρ0 PendAW.recMem.mtype) at hR
  rw [rec_type] at hR
  exact (fapps_congr hR (arguments P)).trans h

theorem result_equiv (P : Premises4) : Equiv (result P) (fxZW P) :=
  (application_result P).symm.trans (redex_equiv P)

theorem result_not_empty (P : Premises4) : ¬ Equiv (result P) pempty := by
  intro he
  have hz : pempty ∈ target P := mem_congr_left
    ((result_equiv P).symm.trans he) (PointwiseDataAttack.omega_mem P (table P))
  exact (PointwiseDataAttack.exact_stage P (table P) [] (key [parameter])).2 hz

/-- The witness keeps its actual typed syntax and same-table semantic inputs. -/
def Witness (P : Premises4) : Prop :=
  PointwiseDataGroupAttack.Witness P ∧
  Nonempty (EnvWfT PendAW.eAll) ∧ PendA PendAW.pNode ∧
  Nonempty (IotaWitness PendAW.eAll) ∧
  witness.ctorRef = 5 ∧ witness.kinds = [] ∧
  witness.ls = [.param 0] ∧ witness.famMember.arity = 0 ∧ σ 0 = 1 ∧
  Nonempty (HasTyT PendAW.eAll 1 Γ (iotaLhsOf witness) resultType) ∧
  Nonempty (HasTyT PendAW.eAll 1 Γ (iotaRhsOf witness) resultType) ∧
  Nonempty (ConvT PendAW.eAll 1 Γ (iotaLhsOf witness) (iotaRhsOf witness) resultType) ∧
  LOKt σ 4 bound lhs_typed ∧ LOKt σ 4 bound rhs_typed ∧
  HSoundT (mkM P (table P)) σ lhs_typed ∧
  HSoundT (mkM P (table P)) σ rhs_typed ∧
  Fits (mkM P (table P)) σ Γ (ρ P) ∧
  TelFits (mkM P (table P)) σ domains ρ0 (arguments P) ∧
  fxZW P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [parameter]) ∧
  den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness) ∈
    Ed (mkM P (table P)) (den (mkM P (table P)) σ (ρ P) resultType) ∧
  den (mkM P (table P)) σ (ρ P) (iotaRhsOf witness) ∈
    Ed (mkM P (table P)) (den (mkM P (table P)) σ (ρ P) resultType) ∧
  Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) (fxZW P) ∧
  Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) (result P) ∧
  Equiv (result P) (fxZW P) ∧ ¬ Equiv (result P) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseDataGroupAttack.component_witness P,
    ⟨PendAWGroup.wft⟩, PendAW.pendA, ⟨witness⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨lhs_typed⟩, ⟨rhs_typed⟩, ⟨typed_iota⟩, typed_bounds.1, typed_bounds.2,
    lhs_hsound P, rhs_hsound P, context_fits P, arguments_fit P,
    PointwiseRoleAttack.installed_height_omega P,
    lhs_mem P, rhs_mem P, redex_equiv P,
    application_result P, result_equiv P, result_not_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseDataTypedIotaAttack
