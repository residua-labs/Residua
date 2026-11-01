import rcic.RcicF3NormDataRecPkg
import rcic.RcicF3NormDataRecMemAttack

/-!
# A typed legacy leaf redex in the actual higher-order W group

The legacy witness is built from the actual stored W declarations. Its
selected leaf row has no fields; the other row is still the admitted
positive-depth W constructor. The original parameter, motive, both stored
minors and leaf major fit one semantic context at the canonical installed
table. The extra motive universe is 1 while the family has arity zero.

The new DATA member producer supplies constructor and recursor membership.
The new DATA iota producer is then called on this actual witness and these
typed endpoints. No current-W RecPkg or iota premise supplies the context
or either endpoint membership. This is the literal legacy leaf equation,
not a shape-iota theorem for the higher-order row. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Rcic.F3.PSet.NormDataTypedIotaAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex
open NormDataRecMemAttack (plan)
open RawDataRecAttack (base parameter target)

abbrev σ : Nat → Nat := RawFamilyIHBuilderAttack.σ
def bound : Nat → Nat := fun _ => 1

def motiveDomain : Expr Nat :=
  .pi (.app (.const 4 []) (.bvar 0)) (.sort (.param 0))
def preDomains : List (Expr Nat) :=
  [.sort (.succ .zero), motiveDomain,
    RawDataRecAttack.leafMinor, RawDataRecAttack.nodeMinor]
def majorDomain : Expr Nat := .app (.const 4 []) (.bvar 3)
def domains : List (Expr Nat) := preDomains ++ [majorDomain]
def body : Expr Nat := .app (.bvar 3) (.bvar 0)
def Γ : LCtx := policyPrefixContext preDomains 4
def resultType : Expr Nat := .app (.bvar 2) (.app (.const 5 []) (.bvar 3))

/- A kernel-checked equation for the actual rebuilt stored recursor type. -/
kernel_rfl_theorem rec_type : PendAW.recMem.mtype = policyPi domains body

private def recStored : CheckedMember :=
  ⟨.recursorM, 1, policyPi domains body, none⟩

private theorem rec_present : PendAW.eAll.members 7 = some recStored :=
  congrArg (fun T => some (CheckedMember.mk .recursorM 1 T none)) rec_type

private noncomputable def head_typed : HasTyT PendAW.eAll 1 Γ
    (.const 7 [.param 0]) (policyPi domains body) :=
  HasTyT.const Γ 7 [.param 0] recStored rec_present rfl rfl

/-- The actual legacy witness constrains its selected leaf row only. -/
noncomputable def witness : IotaWitness PendAW.eAll where
  recRef := 7
  ctorRef := 5
  ls := [.param 0]
  lsC := []
  recMember := PendAW.recMem
  ctorMember := PendAW.leaf
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 3, .bvar 2, .bvar 1, .bvar 0]
  fields := []
  ctorParams := [.bvar 3]
  kinds := []
  minor := .bvar 1
  hlen := rfl
  familyRef := 4
  famMember := PendAW.fam
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 0
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := by rw [rec_type]; rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero)]
  ctorResult := .app (.const 4 []) (.bvar 0)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := domains
  recBody := body
  hpeelRec := by rw [rec_type]; rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by rw [rec_type]; rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .app (.const 4 []) (.bvar 3)
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem witness_lhs : iotaLhsOf witness =
    .app (.app (.app (.app (.app (.const 7 [.param 0]) (.bvar 3))
      (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.const 5 []) (.bvar 3)) := rfl

theorem witness_rhs : iotaRhsOf witness = .bvar 1 := rfl

/-- These derivations use the actual declarations and unchanged local context. -/
noncomputable def lhs_typed : HasTyT PendAW.eAll 1 Γ
    (iotaLhsOf witness) resultType := by
  have h1 := HasTyT.app Γ _ _ _ _ head_typed (HasTyT.bvar Γ 3 _ rfl)
  have h2 := HasTyT.app Γ _ _ _ _ h1 (HasTyT.bvar Γ 2 _ rfl)
  have h3 := HasTyT.app Γ _ _ _ _ h2 (HasTyT.bvar Γ 1 _ rfl)
  have h4 := HasTyT.app Γ _ _ _ _ h3 (HasTyT.bvar Γ 0 _ rfl)
  have hleaf := HasTyT.app Γ _ _ _ _
    (HasTyT.const (E := PendAW.eAll) (n := 1) Γ 5 [] PendAW.leaf rfl rfl rfl)
    (HasTyT.bvar Γ 3 _ rfl)
  exact HasTyT.app Γ _ _ _ _ h4 hleaf

noncomputable def rhs_typed : HasTyT PendAW.eAll 1 Γ
    (iotaRhsOf witness) resultType := HasTyT.bvar Γ 1 resultType rfl

noncomputable def typed_iota : ConvT PendAW.eAll 1 Γ
    (iotaLhsOf witness) (iotaRhsOf witness) resultType :=
  .iota Γ _ _ _ (.of witness) lhs_typed rhs_typed

theorem typed_bounds : LOKt σ 4 bound lhs_typed ∧ LOKt σ 4 bound rhs_typed := by
  constructor
  · change (((((∀ l, l ∈ [Level.param 0] → evalTotal σ l ≤ 1) ∧ True) ∧ True) ∧
      True) ∧ True) ∧ ((∀ l, l ∈ ([] : List Level) → evalTotal σ l ≤ 1) ∧ True)
    refine ⟨⟨⟨⟨⟨?_, True.intro⟩, True.intro⟩, True.intro⟩, True.intro⟩,
      ⟨fun _ h => (List.not_mem_nil _ h).elim, True.intro⟩⟩
    intro l hl
    rw [List.mem_singleton.mp hl]
    exact Nat.le_refl 1
  · exact True.intro

theorem rec_levels : LevelsOK σ (bound 7) witness.ls := by
  intro l hl
  rw [List.mem_singleton.mp hl]
  exact Nat.le_refl 1

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
    HSoundT (mkM P (base P)) σ lhs_typed := by
  dsimp only [lhs_typed]
  apply hsound_app
  · apply hsound_app
    · apply hsound_app
      · apply hsound_app
        · apply hsound_app
          · intro ρ _
            exact (NormDataRecMemAttack.all_sound P 1 7 recStored rec_present
              σ [.param 0] ρ rfl rec_levels).1
          · exact hsound_bvar _ _ _ _
        · exact hsound_bvar _ _ _ _
      · exact hsound_bvar _ _ _ _
    · exact hsound_bvar _ _ _ _
  · apply hsound_app
    · intro ρ _
      exact (NormDataRecMemAttack.all_sound P 1 5 PendAW.leaf rfl σ [] ρ rfl
        (fun _ h => (List.not_mem_nil _ h).elim)).1
    · exact hsound_bvar _ _ _ _

theorem rhs_hsound (P : Premises4) :
    HSoundT (mkM P (base P)) σ rhs_typed := hsound_bvar _ _ _ _

noncomputable def motive (P : Premises4) : PSet.{4} :=
  piLam (mkM P (base P)) σ (fun _ => tyv (target P))
    (push [parameter] ρ0) motiveDomain

noncomputable def major (P : Premises4) : PSet.{4} :=
  fapps (base P 5 []) [parameter]

theorem parameter_fit (P : Premises4) :
    TelFits (mkM P (base P)) σ [.sort (.succ .zero)] ρ0 [parameter] :=
  PendAWBridge.argsFit P (base P) pempty

theorem motive_mem (P : Premises4) :
    motive P ∈ Ed (mkM P (base P))
      (den (mkM P (base P)) σ (push [parameter] ρ0) motiveDomain) := by
  apply piLam_mem (mkM P (base P)) σ (envResp_const _) _
  intro z hz
  exact mem_congr_right (ed_tyv (mkM P (base P)) (U4_dich 1)).symm
    (RawFamilyIHBuilderAttack.target_type P (base P))

/-- Constructor membership comes from the new bounded DATA walk/member chain. -/
theorem major_mem (P : Premises4) :
    major P ∈ Ed (mkM P (base P)) (fapps (base P 4 []) [parameter]) := by
  have h := (NormDataRecMemAttack.all_sound P 1 5 PendAW.leaf rfl σ [] ρ0 rfl
    (fun _ hl => (List.not_mem_nil _ hl).elim)).1
  change base P 5 [] ∈ Ed (mkM P (base P))
    (den (mkM P (base P)) σ ρ0 (policyPi [.sort (.succ .zero)]
      (.app (.const 4 []) (.bvar 0)))) at h
  exact mem_fapps (mkM P (base P)) σ (.app (.const 4 []) (.bvar 0))
    [.sort (.succ .zero)] ρ0 (base P 5 []) [parameter] h (parameter_fit P)

theorem node_mem (P : Premises4) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (base P))
      (den (mkM P (base P)) σ (push [parameter] ρ0) PendAW.field)) :
    fapps (base P 6 []) [parameter, x] ∈
      Ed (mkM P (base P)) (fapps (base P 4 []) [parameter]) := by
  have h := (NormDataRecMemAttack.all_sound P 1 6 PendAW.node rfl σ [] ρ0 rfl
    (fun _ hl => (List.not_mem_nil _ hl).elim)).1
  change base P 6 [] ∈ Ed (mkM P (base P))
    (den (mkM P (base P)) σ ρ0 (policyPi [.sort (.succ .zero), PendAW.field]
      (.app (.const 4 []) (.bvar 1)))) at h
  exact mem_fapps (mkM P (base P)) σ (.app (.const 4 []) (.bvar 1))
    [.sort (.succ .zero), PendAW.field] ρ0 (base P 6 []) [parameter, x] h
    ⟨(parameter_fit P).1, hx, True.intro⟩

theorem motive_apply (P : Premises4) (z : PSet.{4})
    (hz : z ∈ Ed (mkM P (base P)) (fapps (base P 4 []) [parameter])) :
    Equiv (fapp (motive P) z) (tyv (target P)) :=
  fapps_piLam (mkM P (base P)) σ (envResp_const _) (.sort (.param 0))
    [.app (.const 4 []) (.bvar 0)] (push [parameter] ρ0) [z] ⟨hz, True.intro⟩

theorem omega_in_motive (P : Premises4) (z : PSet.{4})
    (hz : z ∈ Ed (mkM P (base P)) (fapps (base P 4 []) [parameter])) :
    fxZW P ∈ Ed (mkM P (base P)) (fapp (motive P) z) := by
  exact mem_congr_right ((ed_congr (mkM P (base P)) (motive_apply P z hz)).trans
    (ed_tyv (mkM P (base P))
      (admissible_dich (RawWFrame.raw_admissible P (base P)) [] _))).symm
    (RawDataRecAttack.omega_mem P)

noncomputable def second (P : Premises4) : PSet.{4} :=
  piLam (mkM P (base P)) σ (fun _ => fxZW P)
    (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
    RawDataRecAttack.nodeMinor

theorem second_mem (P : Premises4) :
    second P ∈ Ed (mkM P (base P))
      (den (mkM P (base P)) σ
        (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
        RawDataRecAttack.nodeMinor) := by
  apply piLam_mem (mkM P (base P)) σ (envResp_const (fxZW P))
  change ∀ x, x ∈ Ed (mkM P (base P)) (den (mkM P (base P)) σ
      (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
      RawDataRecAttack.nodeField) →
    ∀ ih, ih ∈ Ed (mkM P (base P)) (den (mkM P (base P)) σ
      (vcons x (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0))))
      RawDataRecAttack.nodeIH) → _
  intro x hx ih _
  have hd := den_lift0_push (mkM P (base P)) σ [motive P, fxZW P]
    (push [parameter] ρ0) PendAW.field
  change den (mkM P (base P)) σ
    (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
    RawDataRecAttack.nodeField = den (mkM P (base P)) σ
      (push [parameter] ρ0) PendAW.field at hd
  rw [hd] at hx
  change fxZW P ∈ Ed (mkM P (base P))
    (fapp (motive P) (fapps (base P 6 []) [parameter, x]))
  exact omega_in_motive P _ (node_mem P x hx)

noncomputable def prefixValues (P : Premises4) : List PSet.{4} :=
  [parameter, motive P, fxZW P, second P]
noncomputable def ρ (P : Premises4) : Nat → PSet.{4} := push (prefixValues P) ρ0
noncomputable def arguments (P : Premises4) : List PSet.{4} :=
  prefixValues P ++ [major P]

/-- Both minors are present, including the higher-order row's typed IH binder. -/
theorem prefix_fit (P : Premises4) :
    TelFits (mkM P (base P)) σ preDomains ρ0 (prefixValues P) :=
  ⟨(parameter_fit P).1, motive_mem P,
    omega_in_motive P _ (major_mem P), second_mem P, True.intro⟩

theorem context_fits (P : Premises4) : Fits (mkM P (base P)) σ Γ (ρ P) := by
  have h := fits_prefixContext (mkM P (base P)) σ preDomains ρ0
    (prefixValues P) (prefix_fit P) 4 (by decide)
  exact h

theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (base P)) σ domains ρ0 (arguments P) :=
  TelFits.append (prefix_fit P) ⟨major_mem P, True.intro⟩

theorem rhs_mem (P : Premises4) :
    den (mkM P (base P)) σ (ρ P) (iotaRhsOf witness) ∈
      Ed (mkM P (base P)) (den (mkM P (base P)) σ (ρ P) resultType) :=
  omega_in_motive P _ (major_mem P)

/-- The new stored-member producer pays the application before iota is used. -/
theorem lhs_mem (P : Premises4) :
    den (mkM P (base P)) σ (ρ P) (iotaLhsOf witness) ∈
      Ed (mkM P (base P)) (den (mkM P (base P)) σ (ρ P) resultType) := by
  have h := (NormDataRecMemAttack.member_sound P 1 σ [.param 0] ρ0 rfl
    (fun l hl => by
      rw [List.mem_singleton.mp hl]
      exact Nat.le_refl 1)).1
  rw [rec_type] at h
  change base P 7 [1] ∈ Ed (mkM P (base P))
    (den (mkM P (base P)) σ ρ0 (policyPi domains body)) at h
  exact mem_fapps (mkM P (base P)) σ body domains ρ0
    (base P 7 [1]) (arguments P) h (arguments_fit P)

theorem recursor_role : NormRole.envCtx PendAWGroup.wft 7 =
    .recursor (EvalPlanNormal.fd plan) := by
  rw [PendAWGroup.wft, NormRole.envCtx_group]
  exact groupRoles_at_rr _ (by decide : 4 < 7) _

theorem recursor_value (P : Premises4) (vs : List Nat) :
    Equiv (base P 7 vs)
      (EvalPlanValue.memberValue (mkM P (base P)) (σOf vs) plan PendAW.recMem) := by
  have h := NormPendAW.faithful P 7 PendAW.recMem rfl vs
  rw [recursor_role, NormPendAW.canonical_plan] at h
  exact h

theorem redex_equiv (P : Premises4) :
    Equiv (den (mkM P (base P)) σ (ρ P) (iotaLhsOf witness)) (fxZW P) := by
  have hI := NormDataRecPkg.iota_at P (base P) bound
    (f := 4) (fm := PendAW.fam) (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
    (rr := 7) (rm := PendAW.recMem) natEnvUWfT rfl PendAWGroup.ctorClasses
    rfl PendAW.membersT (PendAWGroup.boundG bound) (PendAWGroup.boundDG 1)
    NormDataRecMemAttack.matching_parameters (NormNatInvariant.gInv P bound)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (NormPendAW.faithful P)
    (NormDataRecMemAttack.small_closed P) NormDataRecMemAttack.type_family
    PendAW.eAll (fun _ _ h => h)
  exact hI PendAW.eAll (fun _ _ h => h) witness rfl σ 1 Γ resultType (ρ P)
    lhs_typed (lhs_hsound P) ⟨4, _, P.good _ rfl, typed_bounds.1⟩
    rhs_typed (rhs_hsound P) rec_levels (context_fits P) (lhs_mem P) (rhs_mem P)

noncomputable def result (P : Premises4) : PSet.{4} :=
  EvalPlanValue.endValue (mkM P (base P)) σ plan (push (arguments P) ρ0)

theorem application_result (P : Premises4) :
    Equiv (den (mkM P (base P)) σ (ρ P) (iotaLhsOf witness)) (result P) := by
  have h := fapps_piLam (mkM P (base P)) σ
    (EvalPlanValue.endValue_resp (mkM P (base P)) σ plan)
    body domains ρ0 (arguments P) (arguments_fit P)
  have hR := recursor_value P [1]
  change Equiv (base P 7 [1])
    (piLam (mkM P (base P)) σ (EvalPlanValue.endValue (mkM P (base P)) σ plan)
      ρ0 PendAW.recMem.mtype) at hR
  rw [rec_type] at hR
  exact (fapps_congr hR (arguments P)).trans h

theorem result_equiv (P : Premises4) : Equiv (result P) (fxZW P) :=
  (application_result P).symm.trans (redex_equiv P)

theorem result_not_empty (P : Premises4) : ¬ Equiv (result P) pempty := by
  have h := (RawWFrame.raw_admissible P (base P) [] (key [parameter])).2
  change (if (1 : Nat) = 0 then _ else _) at h
  rw [if_neg (by decide : (1 : Nat) ≠ 0)] at h
  intro he
  exact h _ (RawDataRecAttack.omega_mem P) ((result_equiv P).symm.trans he)

/-- The witness keeps its actual typed syntax and same-table semantic inputs. -/
def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT PendAW.eAll) ∧ PendA PendAW.pNode ∧
  Nonempty (IotaWitness PendAW.eAll) ∧
  witness.ctorRef = 5 ∧ witness.kinds = [] ∧
  witness.ls = [.param 0] ∧ witness.famMember.arity = 0 ∧ σ 0 = 1 ∧
  Nonempty (HasTyT PendAW.eAll 1 Γ (iotaLhsOf witness) resultType) ∧
  Nonempty (HasTyT PendAW.eAll 1 Γ (iotaRhsOf witness) resultType) ∧
  Nonempty (ConvT PendAW.eAll 1 Γ (iotaLhsOf witness) (iotaRhsOf witness) resultType) ∧
  LOKt σ 4 bound lhs_typed ∧ LOKt σ 4 bound rhs_typed ∧
  HSoundT (mkM P (base P)) σ lhs_typed ∧
  HSoundT (mkM P (base P)) σ rhs_typed ∧
  Fits (mkM P (base P)) σ Γ (ρ P) ∧
  TelFits (mkM P (base P)) σ domains ρ0 (arguments P) ∧
  fxZW P ∈ Ed (mkM P (base P)) (fapps (base P 4 []) [parameter]) ∧
  den (mkM P (base P)) σ (ρ P) (iotaLhsOf witness) ∈
    Ed (mkM P (base P)) (den (mkM P (base P)) σ (ρ P) resultType) ∧
  den (mkM P (base P)) σ (ρ P) (iotaRhsOf witness) ∈
    Ed (mkM P (base P)) (den (mkM P (base P)) σ (ρ P) resultType) ∧
  Equiv (den (mkM P (base P)) σ (ρ P) (iotaLhsOf witness)) (fxZW P) ∧
  Equiv (den (mkM P (base P)) σ (ρ P) (iotaLhsOf witness)) (result P) ∧
  Equiv (result P) (fxZW P) ∧ ¬ Equiv (result P) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨⟨PendAWGroup.wft⟩, PendAW.pendA, ⟨witness⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨lhs_typed⟩, ⟨rhs_typed⟩, ⟨typed_iota⟩, typed_bounds.1, typed_bounds.2,
    lhs_hsound P, rhs_hsound P, context_fits P, arguments_fit P,
    NormPendAW.installed_height_omega P,
    lhs_mem P, rhs_mem P, redex_equiv P,
    application_result P, result_equiv P, result_not_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDataTypedIotaAttack
