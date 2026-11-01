import rcic.RcicF3RawFamilyPropAttack
import rcic.RcicF3PiRawIHAnyAttack
import rcic.RcicF3RawFamilyPlanReads

/-!
# The retained Prop endpoint at the actual AccR fixture

A semantic regression for the stored Acc minor, with an inhabited raw
family fibre and a data-valued motive at the extra universe parameter.
The actual endpoint must be checked against these memberships, rather than
inferred from an argument-count discrepancy. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PlanPropEndAttack
open Rcic.Declarative PiIndex RawFamily

abbrev fd : FamData := famDataOf accGroupAdmitted
def σ : Nat → Nat := σOf [1]
def parameter : PSet.{4} := tyv pempty
def datum : PSet.{4} := PiRawIHAnyAttack.datum
def domain : PSet.{4} := PiRawIHAnyAttack.domain

def motive (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : PSet.{4} :=
  piLam (mkM P μ) σ (fun _ => tyv domain) (push [parameter] ρ0) accMotTy

def start (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Nat → PSet.{4} :=
  vcons (motive P μ) (push [parameter] ρ0)

def minor (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : PSet.{4} :=
  piLam (mkM P μ) σ (fun _ => datum) (start P μ) accMinorTy

def inner (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : PSet.{4} :=
  lamVal (mkM P μ) (den (mkM P μ) σ (vcons pempty (start P μ)) accIhTy)
    (fun _ => datum)

theorem parameter_mem (P : Premises4) : parameter ∈ U W4 0 :=
  mem_sImage_tyv.mpr ⟨pempty,
    mem_propSets.mpr (fun _ h => (not_mem_pempty h).elim), Equiv.rfl⟩

theorem parameter_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (Ed (mkM P μ) parameter) pempty :=
  ed_tyv (mkM P μ) (Or.inl (fun _ h => (not_mem_pempty h).elim))

theorem major_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hF : Equiv (μ 0 []) (role P μ fd [])) :
    pempty ∈ Ed (mkM P μ) (fapp (μ 0 []) parameter) := by
  have hp : TelFits (mkM P μ) (σOf []) (fd.params ++ fd.indices) ρ0 [parameter] := by
    exact ⟨mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)).symm (parameter_mem P),
      True.intro⟩
  have he := apply_ofFrame_ed P μ fd (frame P μ fd)
    (RawFamilyPropAttack.acc_closed P μ).1 [] [parameter] hp
  apply mem_congr_right (ed_congr (mkM P μ) (fapp_congr hF Equiv.rfl)).symm
  exact mem_congr_right he.symm (RawFamilyPropAttack.empty_parameter_inhabited P μ [])

theorem motive_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    motive P μ ∈ Ed (mkM P μ)
      (den (mkM P μ) σ (push [parameter] ρ0) accMotTy) := by
  apply piLam_mem (mkM P μ) σ (envResp_const _) accMotTy
  intro z hz
  exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich 1)).symm
    (PiRawIHAnyAttack.type_mem P)

theorem motive_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hF : Equiv (μ 0 []) (role P μ fd [])) :
    Equiv (fapp (motive P μ) pempty) (tyv domain) := by
  exact beta_val (mkM P μ) (fun _ _ _ => Equiv.rfl) (major_mem P μ hF)

theorem field_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ (start P μ) accFieldMinor) := by
  let M := mkM P μ
  change pempty ∈ Ed M (piVal M parameter (fun _ => fapp (μ 0 []) parameter))
  have hp : PiProp M parameter (fun _ => fapp (μ 0 []) parameter) := by
    intro x hx
    exact (not_mem_pempty (mem_congr_right (parameter_empty P μ) hx)).elim
  apply mem_congr_right (ed_piVal_of_prop M hp).symm
  exact mem_tv.mpr ⟨fun x hx =>
    (not_mem_pempty (mem_congr_right (parameter_empty P μ) hx)).elim, Equiv.rfl⟩

theorem ih_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    pempty ∈ Ed (mkM P μ)
      (den (mkM P μ) σ (vcons pempty (start P μ)) accIhTy) := by
  let M := mkM P μ
  change pempty ∈ Ed M (piVal M parameter
    (fun x => fapp (motive P μ) (fapp pempty x)))
  have hp : PiProp M parameter (fun x => fapp (motive P μ) (fapp pempty x)) := by
    intro x hx
    exact (not_mem_pempty (mem_congr_right (parameter_empty P μ) hx)).elim
  apply mem_congr_right (ed_piVal_of_prop M hp).symm
  exact mem_tv.mpr ⟨fun x hx =>
    (not_mem_pempty (mem_congr_right (parameter_empty P μ) hx)).elim, Equiv.rfl⟩

theorem minor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hF : Equiv (μ 0 []) (role P μ fd [])) (hC : Equiv (μ 1 []) pempty) :
    minor P μ ∈ Ed (mkM P μ) (den (mkM P μ) σ (start P μ) accMinorTy) := by
  apply piLam_mem (mkM P μ) σ (envResp_const _) accMinorTy
  intro x hx i hi
  change datum ∈ Ed (mkM P μ) (fapp (motive P μ) (fapps (μ 1 []) [parameter, x]))
  have hc := (fapps_congr hC [parameter, x]).trans (fapps_pempty [parameter, x])
  have he := (fapp_congr (Equiv.refl (motive P μ)) hc).trans (motive_empty P μ hF)
  exact mem_congr_right (ed_congr (mkM P μ) he).symm
    (mem_congr_right (ed_tyv (mkM P μ) PiRawIHAnyAttack.domain_dich).symm
      (mem_singleton.mpr Equiv.rfl))

theorem first_application (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (fapp (minor P μ) pempty) (inner P μ) := by
  apply beta_val (mkM P μ) ?_ (field_mem P μ)
  intro x y h
  exact piLam_congr (mkM P μ) σ (envResp_const datum) _
    (vcons_congr h (fun _ => Equiv.rfl))

theorem second_application (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (fapp (inner P μ) pempty) datum :=
  beta_val (mkM P μ) (fun _ _ _ => Equiv.rfl) (ih_mem P μ)

/-- The residual lambda is strictly above its data result in transitive
membership, so it cannot itself be that result. -/
theorem inner_ne_datum (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ¬ Equiv (inner P μ) datum := by
  let M := mkM P μ
  let A := den M σ (vcons pempty (start P μ)) accIhTy
  have hL : ¬ LamProof M A (fun _ => datum) := by
    intro h
    exact dataVal_ne_pempty 17 [] (h pempty (ih_mem P μ))
  change ¬ Equiv (cond M.dec (LamProof M A (fun _ => datum)) pempty
    (mkLam (fun _ => datum) (Ed M A))) datum
  rw [cond_neg hL]
  intro he
  obtain ⟨i, hi⟩ := ih_mem P μ
  have hp : ordPair pempty datum ∈ mkLam (fun _ => datum) (Ed M A) :=
    ⟨i, ordPair_congr hi Equiv.rfl⟩
  have h1 : datum ∈ pair pempty datum := mem_pair.mpr (Or.inr Equiv.rfl)
  have h2 : pair pempty datum ∈ ordPair pempty datum :=
    mem_pair.mpr (Or.inr Equiv.rfl)
  have ht : MemT datum (mkLam (fun _ => datum) (Ed M A)) :=
    .tail (.tail (.single h1) h2) hp
  have hn : ∀ z : PSet.{4}, ¬ MemT z z := by
    intro z
    induction z using memT_wf.induction with
    | h z ih => intro hzz; exact ih z hzz hzz
  exact hn datum (ht.congr_right he)

def input (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Nat → PSet.{4} :=
  push [parameter, motive P μ, minor P μ, pempty] ρ0

/-- The current planned Prop endpoint still performs only the first minor
application, independently of the supplied admitted plan. -/
theorem endpoint (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (plan : List (List FieldShape)) :
    Equiv (RecPlanValue.endValue (mkM P μ) σ fd plan (input P μ)) (inner P μ) := by
  unfold RecPlanValue.endValue
  rw [cond_pos (show evalTotal σ fd.resLevel = 0 from rfl)]
  unfold recEnd
  rw [cond_pos (show evalTotal σ fd.resLevel = 0 from rfl)]
  exact first_application P μ

/-- A semantic failure, not merely an argument-count discrepancy. -/
theorem endpoint_not_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hF : Equiv (μ 0 []) (role P μ fd [])) (plan : List (List FieldShape)) :
    RecPlanValue.endValue (mkM P μ) σ fd plan (input P μ) ∉
      Ed (mkM P μ) (fapp (motive P μ) pempty) := by
  intro h
  have hd := mem_singleton.mp (mem_congr_right
    ((ed_congr (mkM P μ) (motive_empty P μ hF)).trans
      (ed_tyv (mkM P μ) PiRawIHAnyAttack.domain_dich)) h)
  exact inner_ne_datum P μ ((endpoint P μ plan).symm.trans hd)

/-- Both original arguments are legal and the complete application lands in
the target. Omitting the IH leaves a value outside that same target. -/
theorem typed_failure (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hF : Equiv (μ 0 []) (role P μ fd [])) (hC : Equiv (μ 1 []) pempty)
    (plan : List (List FieldShape)) :
    motive P μ ∈ Ed (mkM P μ)
      (den (mkM P μ) σ (push [parameter] ρ0) accMotTy) ∧
    minor P μ ∈ Ed (mkM P μ) (den (mkM P μ) σ (start P μ) accMinorTy) ∧
    pempty ∈ Ed (mkM P μ) (fapp (μ 0 []) parameter) ∧
    pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ (start P μ) accFieldMinor) ∧
    pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ (vcons pempty (start P μ)) accIhTy) ∧
    fapps (minor P μ) [pempty, pempty] ∈ Ed (mkM P μ) (fapp (motive P μ) pempty) ∧
    RecPlanValue.endValue (mkM P μ) σ fd plan (input P μ) ∉
      Ed (mkM P μ) (fapp (motive P μ) pempty) := by
  refine ⟨motive_mem P μ, minor_mem P μ hF hC, major_mem P μ hF,
    field_mem P μ, ih_mem P μ, ?_, endpoint_not_mem P μ hF plan⟩
  have he : Equiv (fapps (minor P μ) [pempty, pempty]) datum :=
    (fapp_congr (first_application P μ) Equiv.rfl).trans (second_application P μ)
  apply mem_congr_left he.symm
  exact mem_congr_right ((ed_congr (mkM P μ) (motive_empty P μ hF)).trans
    (ed_tyv (mkM P μ) PiRawIHAnyAttack.domain_dich)).symm
      (mem_singleton.mpr Equiv.rfl)

/-- Empty proof-valued abstraction, at every raw telescope. -/
theorem piLam_empty (M : Interp.{4}) (τ : Nat → Nat) (e : Expr Nat)
    (ρ : Nat → PSet.{4}) : Equiv (piLam M τ (fun _ => pempty) ρ e) pempty := by
  induction e generalizing ρ with
  | pi A B _ ih =>
    change Equiv (cond M.dec (LamProof M (den M τ ρ A)
      (fun x => piLam M τ (fun _ => pempty) (vcons x ρ) B)) pempty _) pempty
    rw [cond_pos (show LamProof M (den M τ ρ A)
      (fun x => piLam M τ (fun _ => pempty) (vcons x ρ) B) from fun x _ => ih _)]
    exact Equiv.rfl
  | _ => exact Equiv.rfl

kernel_rfl_theorem family_context : envCtx AccEnv.accEnvWfT 0 = .fam fd
kernel_rfl_theorem constructor_context : envCtx AccEnv.accEnvWfT 1 = .ctor fd 0
kernel_rfl_theorem recursor_context : envCtx AccEnv.accEnvWfT 2 = .recursor fd

noncomputable def installed (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PlanRole.rawTable P AccEnv.accEnvWfT

theorem installed_family (P : Premises4) :
    Equiv (installed P 0 []) (role P (installed P) fd []) := by
  have h := (PlanRole.rawTable_spec P AccEnv.accEnvWfT).1 0 accFamMember rfl []
  rw [family_context] at h
  exact h

theorem installed_constructor (P : Premises4) : Equiv (installed P 1 []) pempty := by
  have h := (PlanRole.rawTable_spec P AccEnv.accEnvWfT).1 1 accIntroMember rfl []
  rw [constructor_context] at h
  change Equiv (installed P 1 [])
    (piLam (mkM P (installed P)) (σOf [])
      (ctorEnd (mkM P (installed P)) (σOf []) fd 0 (nfOf fd 0)) ρ0 accIntroMember.mtype) at h
  have he : ctorEnd (mkM P (installed P)) (σOf []) fd 0 (nfOf fd 0) =
      (fun _ => pempty) := by
    funext ρ
    unfold ctorEnd
    exact cond_pos (show evalTotal (σOf []) fd.resLevel = 0 from rfl) _ _
  rw [he] at h
  exact h.trans (piLam_empty _ _ _ _)

/-- Every assumption of the semantic attack is now produced at the canonical
faithful table of the actual typed AccR environment. -/
theorem installed_failure (P : Premises4) :
    PlanRole.Faithful role P (installed P) (envCtx AccEnv.accEnvWfT)
      (PlanRole.envPlan AccEnv.accEnvWfT) accEnv ∧
    minor P (installed P) ∈ Ed (mkM P (installed P))
      (den (mkM P (installed P)) σ (start P (installed P)) accMinorTy) ∧
    RecPlanValue.endValue (mkM P (installed P)) σ fd
      (PlanRole.envPlan AccEnv.accEnvWfT 2) (input P (installed P)) ∉
      Ed (mkM P (installed P)) (fapp (motive P (installed P)) pempty) := by
  exact ⟨(PlanRole.rawTable_spec P AccEnv.accEnvWfT).1,
    minor_mem P (installed P) (installed_family P) (installed_constructor P),
    endpoint_not_mem P (installed P) (installed_family P) _⟩

/-- The current planned raw-role invariant fails at a live, fully typed AccR
fixture. This theorem itself does not supply the four StepAG antecedents. -/
theorem gInv_false (P : Premises4) :
    ¬ PlanRole.GInv role P (fun _ => 1) AccEnv.accEnvWfT := by
  intro hG
  let μ := installed P
  let M := mkM P μ
  let plan := PlanRole.envPlan AccEnv.accEnvWfT 2
  have hFaith := (PlanRole.rawTable_spec P AccEnv.accEnvWfT).1
  have hAll := (hG (envCtx AccEnv.accEnvWfT) (fun _ _ => rfl)
    (PlanRole.envPlan AccEnv.accEnvWfT) (fun _ _ => rfl) μ hFaith).1
  have hrec := (hAll 2 accRecMember rfl σ [.param 0] ρ0 rfl
    (by intro l hl; cases List.mem_singleton.mp hl; decide)).1
  change μ 2 [1] ∈ Ed M (den M σ ρ0 accRecTy) at hrec
  have hfit : TelFits M σ [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)]
      ρ0 [parameter, motive P μ, minor P μ, pempty] :=
    ⟨mem_congr_right (ed_tyv M (U4_dich 0)).symm (parameter_mem P),
      motive_mem P μ, minor_mem P μ (installed_family P) (installed_constructor P),
      major_mem P μ (installed_family P), True.intro⟩
  have hresult := mem_fapps M σ (.app (.bvar 2) (.bvar 0))
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)]
    ρ0 (μ 2 [1]) [parameter, motive P μ, minor P μ, pempty] hrec hfit
  have hv := hFaith 2 accRecMember rfl [1]
  rw [recursor_context] at hv
  change Equiv (μ 2 [1])
    (piLam M σ (RecPlanValue.endValue M σ fd plan) ρ0 accRecTy) at hv
  have he : Equiv (fapps (μ 2 [1]) [parameter, motive P μ, minor P μ, pempty])
      (RecPlanValue.endValue M σ fd plan (input P μ)) :=
    (fapps_congr hv _).trans (fapps_piLam M σ (RecPlanValue.laws M σ fd plan).1
      (.app (.bvar 2) (.bvar 0)) [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)]
      ρ0 [parameter, motive P μ, minor P μ, pempty] hfit)
  exact endpoint_not_mem P μ (installed_family P) plan (mem_congr_left he hresult)

end Rcic.F3.PSet.PlanPropEndAttack
