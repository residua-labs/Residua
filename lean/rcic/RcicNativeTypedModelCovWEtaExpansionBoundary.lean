import rcic.RcicNativeTypedModelCovWEtaInverseBoundary
import rcic.RcicNativeTypedModelCovWTypedBetaBoundary

/-!
# Direct beta and let failures after finite typed eta observation

The protected lambda accepts a proof of `P`; every direct lambda demand is
bottom. A simultaneous induction on the finite eta derivation proves that
every graph row of this lambda has a clean result even for arbitrary row
inputs. Thus its first application cannot retain `spine 4 []` in a result
field. Subsequent applications and all eta alternatives are included.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelCovUAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelAudit.TypingFin TypedModelCovWTypedAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def cleanMaskUp (S : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => S i

private def cleanEnvOn (S : Nat → Prop) (ρ : EnvT) : Prop :=
  ∀ i c, S i → ρ i c → CovWEtaClean c

private inductive MaskedRigid (E : ResolvedEnv) (S : Nat → Prop) : Expr Nat → Prop
  | bvar (i : Nat) (hi : S i) : MaskedRigid E S (.bvar i)
  | const (r : Nat) (ls : List Level) (hr : RigidConst E r) (hne : r ≠ 4) :
      MaskedRigid E S (.const r ls)
  | app {f x : Expr Nat} (hf : MaskedRigid E S f) (hx : MaskedRigid E S x) :
      MaskedRigid E S (.app f x)

private theorem MaskedRigid.lift_one {E : ResolvedEnv} {S : Nat → Prop} {e : Expr Nat}
    (h : MaskedRigid E S e) : MaskedRigid E (cleanMaskUp S) (Rcic.Declarative.lift 0 1 e) := by
  induction h with
  | bvar i hi =>
      simpa only [Rcic.Declarative.lift, Nat.zero_le, if_pos, Nat.add_one] using
        (MaskedRigid.bvar (E := E) (S := cleanMaskUp S) (Nat.succ i) hi)
  | const r ls hr hn => exact .const r ls hr hn
  | app _ _ ihf ihx => exact .app ihf ihx

private theorem MaskedRigid.foldApps_head {E : ResolvedEnv} {S : Nat → Prop}
    {f : Expr Nat} {xs : List (Expr Nat)}
    (h : MaskedRigid E S (foldApps f xs)) : MaskedRigid E S f := by
  induction xs generalizing f with
  | nil => exact h
  | cons x xs ih =>
      have hh := ih h
      cases hh with
      | app hf _ => exact hf

private theorem cleanEnvOn_cons {S : Nat → Prop} {ρ : EnvT} {us : List CptT}
    (hρ : cleanEnvOn S ρ) (hu : ∀ u ∈ us, CovWEtaClean u) :
    cleanEnvOn (cleanMaskUp S) (EnvT.cons (demandT us) ρ) := by
  intro i c hi hc
  cases i with
  | zero => exact hu c hc
  | succ i => exact hρ i c hi hc

private theorem masked_raw_clean {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat}
    {c : CptT} (h : ApproxTW E ρ e c) {S : Nat → Prop}
    (he : MaskedRigid E S e) (hρ : cleanEnvOn S ρ) : CovWEtaClean c := by
  induction h with
  | bot => exact covWEta_clean_bot
  | bvar hv => cases he with | bvar _ hi => exact hρ _ _ hi hv
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app _ hs _ ihf ihx =>
      cases he with
      | app hf hx =>
          have hh := ihf hf hρ
          rw [CovWEtaClean] at hh
          exact hh _ hs (fun u hu => ihx u hu hx hρ)
  | const _ _ _ _ _ =>
      cases he with
      | const r ls hr hn =>
          rw [CovWEtaClean]
          exact ⟨hn, fun u hu => nomatch hu⟩
  | delta hd _ _ =>
      cases he with
      | const _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | @recursor ρ w ls hnp up uf c hp hf hb ih =>
      cases he with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | appSpine _ _ ihf ihx =>
      cases he with
      | app hf hx => exact covWEta_clean_appSpine (ihf hf hρ) (ihx hx hρ)
  | letE => cases he
  | lit => cases he

private theorem masked_observation_clean {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e : Expr Nat} {c : CptT} (h : ApproxTKWEta E n Γ ρ e c)
    {S : Nat → Prop} (he : MaskedRigid E S e) (hρ : cleanEnvOn S ρ) :
    CovWEtaClean c := by
  induction h generalizing S with
  | bot => exact covWEta_clean_bot
  | free _ h => exact masked_raw_clean h he hρ
  | pi => cases he
  | lam => cases he
  | app _ hs _ ihf ihx =>
      cases he with
      | app hf hx =>
          have hh := ihf hf hρ
          rw [CovWEtaClean] at hh
          exact hh _ hs (fun u hu => ihx u hu hx hρ)
  | appSpine _ _ ihf ihx =>
      cases he with
      | app hf hx => exact covWEta_clean_appSpine (ihf hf hρ) (ihx hx hρ)
  | delta hd _ _ =>
      cases he with
      | const _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | letE => cases he
  | lit => cases he
  | iota w _ _ _ =>
      have hh := MaskedRigid.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ _ =>
      have hh := MaskedRigid.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta _ _ _ _ _ ihD ihb =>
      rw [CovWEtaClean]
      intro s hs hus
      exact ihb s hs (.app he.lift_one (.bvar 0 trivial)) (cleanEnvOn_cons hρ hus)

def covWEtaInvFn : Expr Nat := .lam covUProjP covWEtaInvBody

private theorem invFn_lift : lift 0 1 covWEtaInvFn = covWEtaInvFn := rfl

private def AllRowsClean : CptT → Prop
  | .bot => True
  | .lam g => ∀ s ∈ g, CovWEtaClean s.2
  | _ => False

private inductive Protected (S : Nat → Prop) : Expr Nat → Prop
  | first (arg : Expr Nat) : Protected S (.app covWEtaInvFn arg)
  | app {f x : Expr Nat} (hf : Protected S f) (hx : MaskedRigid covWRevEnv S x) :
      Protected S (.app f x)

private theorem Protected.lift_one {S : Nat → Prop} {e : Expr Nat}
    (h : Protected S e) : Protected (cleanMaskUp S) (Rcic.Declarative.lift 0 1 e) := by
  induction h with
  | first arg =>
      change Protected (cleanMaskUp S)
        (.app (Rcic.Declarative.lift 0 1 covWEtaInvFn) (Rcic.Declarative.lift 0 1 arg))
      rw [invFn_lift]
      exact .first _
  | app _ hx ih => exact .app ih hx.lift_one

private theorem Protected.head {S : Nat → Prop} {e : Expr Nat}
    (h : Protected S e) : headConst e = none := by
  induction h with
  | first => rfl
  | app _ _ ih => exact ih

private theorem headConst_apps (f : Expr Nat) (xs : List (Expr Nat)) :
    headConst (foldApps f xs) = headConst f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

private theorem inv_P_rigid : RigidConst covWRevEnv 3 := by
  intro m hm
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

private theorem inv_body_masked :
    MaskedRigid covWRevEnv (fun i => i = 0) covWEtaInvBody :=
  .app (.const 5 []
    (rigidConst_of_inductiveM covWRevEnv_wf (m := covWRevFam) rfl rfl) (by decide))
    (.bvar 0 rfl)

private theorem inv_raw_rows_clean {ρ : EnvT} {c : CptT}
    (h : ApproxTW covWRevEnv ρ covWEtaInvFn c) : AllRowsClean c := by
  cases h with
  | bot => trivial
  | lam hP ht _ hb =>
      intro s hs
      apply masked_raw_clean (hb s hs) inv_body_masked
      intro i d hi hd
      subst i
      have he := covWEtaInv_P_demands_bot
        (n := 0) (Γ := []) (.free (kFreeT_rigid_const inv_P_rigid []) hP)
        (ht s hs d hd)
      rw [he]
      exact covWEta_clean_bot

private theorem protected_raw_clean {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTW covWRevEnv ρ e c) {S : Nat → Prop}
    (he : Protected S e) (hρ : cleanEnvOn S ρ) : CovWEtaClean c := by
  induction h with
  | bot => exact covWEta_clean_bot
  | bvar => cases he
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app hf hs ha ihf ihx =>
      cases he with
      | first _ => exact inv_raw_rows_clean hf _ hs
      | app hp hx =>
          have hh := ihf hp hρ
          rw [CovWEtaClean] at hh
          exact hh _ hs (fun u hu => masked_raw_clean (ha u hu) hx hρ)
  | const => cases he
  | delta => cases he
  | recursor => cases he
  | appSpine hf ha ihf ihx =>
      cases he with
      | first _ => exact (inv_raw_rows_clean hf).elim
      | app hp hx => exact covWEta_clean_appSpine (ihf hp hρ) (masked_raw_clean ha hx hρ)
  | letE => cases he
  | lit => cases he

/-- Simultaneous finite-derivation invariant. The protected lambda's rows are
clean for arbitrary inputs; an applied protected prefix preserves cleanliness
under the masks needed by later eta-introduced variables. -/
private theorem protected_observation_clean {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTKWEta covWRevEnv n Γ ρ e c) :
    (∀ S, Protected S e → cleanEnvOn S ρ → CovWEtaClean c) ∧
    (e = covWEtaInvFn → AllRowsClean c) := by
  induction h with
  | bot => exact ⟨fun _ _ _ => covWEta_clean_bot, fun _ => trivial⟩
  | free _ h =>
      refine ⟨fun _ he hρ => protected_raw_clean h he hρ, ?_⟩
      intro he
      rw [he] at h
      exact inv_raw_rows_clean h
  | pi =>
      constructor
      · intro S he; cases he
      · intro he; cases he
  | lam hP ht _ hb ihP ihb =>
      constructor
      · intro S he; cases he
      · intro he
        cases he
        intro s hs
        apply masked_observation_clean (hb s hs) inv_body_masked
        intro i d hi hd
        subst i
        rw [covWEtaInv_P_demands_bot hP (ht s hs d hd)]
        exact covWEta_clean_bot
  | app hf hs ha ihf ihx =>
      constructor
      · intro S he hρ
        cases he with
        | first _ => exact ihf.2 rfl _ hs
        | app hp hx =>
            have hh := ihf.1 S hp hρ
            rw [CovWEtaClean] at hh
            exact hh _ hs (fun u hu => masked_observation_clean (ha u hu) hx hρ)
      · intro he; cases he
  | appSpine hf ha ihf ihx =>
      constructor
      · intro S he hρ
        cases he with
        | first _ => exact (ihf.2 rfl).elim
        | app hp hx =>
            exact covWEta_clean_appSpine (ihf.1 S hp hρ)
              (masked_observation_clean ha hx hρ)
      · intro he; cases he
  | delta =>
      constructor
      · intro S he; cases he
      · intro he; cases he
  | letE =>
      constructor
      · intro S he; cases he
      · intro he; cases he
  | lit =>
      constructor
      · intro S he; cases he
      · intro he; cases he
  | iota w _ _ _ =>
      constructor
      · intro S he
        have hh := he.head
        rw [iotaLhsOfS, recCall, headConst_apps] at hh
        cases hh
      · intro he
        simp only [iotaLhsOfS, recCall_eq_app, covWEtaInvFn] at he
        cases he
  | recursorPropK w x _ _ _ _ _ _ _ =>
      constructor
      · intro S he
        have hh := he.head
        rw [recCall, headConst_apps] at hh
        cases hh
      · intro he
        simp only [recCall_eq_app, covWEtaInvFn] at he
        cases he
  | eta _ _ _ _ _ ihD ihb =>
      constructor
      · intro S he hρ
        rw [CovWEtaClean]
        intro s hs hus
        exact (ihb s hs).1 (cleanMaskUp S)
          (.app he.lift_one (.bvar 0 trivial)) (cleanEnvOn_cons hρ hus)
      · intro he
        cases he
        intro s hs
        apply (ihb s hs).1 (fun _ => False)
        · rw [invFn_lift]
          exact .first _
        · intro i d hi
          exact hi.elim

/-- Every observation of the beta source is clean, regardless of valuation. -/
theorem covWEtaInv_source_clean {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvSource c) : CovWEtaClean c :=
  (protected_observation_clean h).1 (fun _ => False) (.first _)
    (fun _ _ hi _ => hi.elim)

theorem covWEtaInv_source_not_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvSource covWEtaInvCompact :=
  fun h => covWEtaInv_compact_not_clean (covWEtaInv_source_clean h)

theorem covWEtaInv_let_not_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvLet covWEtaInvCompact := by
  intro h
  generalize he : covWEtaInvLet = e at h
  generalize hc : covWEtaInvCompact = c at h
  cases h with
  | bot => cases hc
  | free _ h =>
      rw [← he] at h
      cases h with
      | bot => cases hc
      | letE h =>
          apply covWEtaInv_compact_not_clean
          rw [hc]
          exact protected_raw_clean h (.first _) (fun _ _ hi _ => hi.elim)
            (S := fun _ => False)
  | pi => cases hc
  | lam => cases hc
  | app => cases he
  | appSpine => cases he
  | delta => cases he
  | letE h =>
      cases he
      apply covWEtaInv_compact_not_clean
      rw [hc]
      exact covWEtaInv_source_clean h
  | lit => cases he
  | iota =>
      simp only [covWEtaInvLet, iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      simp only [covWEtaInvLet, recCall_eq_app] at he
      cases he
  | eta => cases hc

theorem covWEtaInv_no_source_transport (n : Nat)
    {R : Expr Nat → Expr Nat → Prop} (hR : R covWEtaInvSource covWEtaInvTarget) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) R := by
  intro h
  apply covWEtaInv_source_not_observed n [] EnvT.bot
  exact h EnvT.bot covWEtaInvSource covWEtaInvTarget (.sort .zero) (.succ .zero)
    covWEtaInvCompact .prop ⟨covWRevEnv_wf⟩ ⟨.nil⟩ (envTypedFinAtT_nil _ _)
    ⟨covWEtaInvSource_ty n⟩ ⟨covWEtaInvTarget_ty n⟩ ⟨.sort _ .zero⟩ hR
    (covWEtaInv_target_observed n [] EnvT.bot)
    (covWEtaInv_result_type_observed n [] EnvT.bot)
    covWEtaInv_compact_typed covWEtaInv_compact_nonbottom

theorem covWEtaInv_no_let_transport (n : Nat)
    {R : Expr Nat → Expr Nat → Prop} (hR : R covWEtaInvLet covWEtaInvTarget) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) R := by
  intro h
  apply covWEtaInv_let_not_observed n [] EnvT.bot
  exact h EnvT.bot covWEtaInvLet covWEtaInvTarget (.sort .zero) (.succ .zero)
    covWEtaInvCompact .prop ⟨covWRevEnv_wf⟩ ⟨.nil⟩ (envTypedFinAtT_nil _ _)
    ⟨covWEtaInvLet_ty n⟩ ⟨covWEtaInvTarget_ty n⟩ ⟨.sort _ .zero⟩ hR
    (covWEtaInv_target_observed n [] EnvT.bot)
    (covWEtaInv_result_type_observed n [] EnvT.bot)
    covWEtaInv_compact_typed covWEtaInv_compact_nonbottom

theorem covWEtaInv_no_beta_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) CovWTypedBetaHead :=
  covWEtaInv_no_source_transport n ⟨covUProjP, covWEtaInvBody, covUProjProof, rfl, rfl⟩

theorem covWEtaInv_no_let_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) CovWTypedLetHead :=
  covWEtaInv_no_let_transport n ⟨covUProjP, covUProjProof, covWEtaInvBody, rfl, rfl⟩

theorem covWEtaInv_no_step_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv)
      (WhStepCK2 covWRevEnv n []) :=
  covWEtaInv_no_source_transport n (covWEtaInv_beta_step n)

theorem covWEtaInv_no_red_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv)
      (RedR (WhStepCK2 covWRevEnv n) []) :=
  covWEtaInv_no_source_transport n (redR_single (covWEtaInv_beta_step n))

theorem covWEtaInv_no_conversion_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv)
      (fun e e' => Nonempty (ConvT covWRevEnv n [] e e' (.sort .zero))) :=
  covWEtaInv_no_source_transport n ⟨covWEtaInv_beta_conv n⟩

theorem covWEtaInv_no_let_conversion_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt covWRevEnv n []
      (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv)
      (fun e e' => Nonempty (ConvT covWRevEnv n [] e e' (.sort .zero))) :=
  covWEtaInv_no_let_transport n ⟨covWEtaInv_let_conv n⟩

/-- The sources and their reduct share a nonbottom typed observation after
discarding exactly the forbidden proof field. -/
theorem covWEtaInv_coarse_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvSource (.spine 5 [.bot]) ∧
    ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvLet (.spine 5 [.bot]) ∧
    ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvTarget (.spine 5 [.bot]) ∧
    CTyS covWRevEnv (.spine 5 [.bot]) .prop := by
  have hr : RigidConst covWRevEnv 5 :=
    rigidConst_of_inductiveM covWRevEnv_wf (m := covWRevFam) rfl rfl
  have hnp : ¬ PropCtorT covWRevEnv 5 := by
    rintro ⟨m, fam, fm, hm, hk, _⟩
    have he : m = covWRevFam := Option.some.inj hm.symm
    subst m
    cases hk
  have hF : ∀ (Δ : LCtx) (σ : EnvT),
      ApproxTKWEta covWRevEnv n Δ σ (.const 5 []) (.spine 5 []) :=
    fun Δ σ => .free (kFreeT_rigid_const hr []) (.const σ 5 [] hr hnp)
  have hfun : ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvFn
      (.lam [([], .spine 5 [.bot])]) := by
    refine .lam (covWEtaInv_P_observed n Γ ρ) ?_ ?_ ?_
    · intro s hs u hu
      have he : s = ([], .spine 5 [.bot]) := List.mem_singleton.mp hs
      subst s
      cases hu
    · exact ⟨([], .spine 5 [.bot]), by simp, fun h => CptT.noConfusion h⟩
    · intro s hs
      have he : s = ([], .spine 5 [.bot]) := List.mem_singleton.mp hs
      subst s
      exact .appSpine (hF _ _) (.bot _ _ _)
  have hsource : ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvSource (.spine 5 [.bot]) :=
    .app (s := ([], .spine 5 [.bot])) hfun (by simp) (fun _ hu => nomatch hu)
  refine ⟨hsource, .letE hsource, .appSpine (hF _ _) (.bot _ _ _), ?_⟩
  rw [CTyS]
  exact Or.inr (.spine (m := covWRevFam) rfl rfl)

theorem covWEtaInv_kFree :
    KFreeT covWRevEnv covWEtaInvSource ∧ KFreeT covWRevEnv covWEtaInvLet ∧
    KFreeT covWRevEnv covWEtaInvTarget := by
  have hf := kFreeT_rigid_const
    (rigidConst_of_inductiveM covWRevEnv_wf (r := 5) (m := covWRevFam) rfl rfl) []
  have hp : RigidConst covWRevEnv 4 := by
    intro m hm
    have he : m = covUProjProofMember := Option.some.inj hm.symm
    subst m
    exact ⟨Or.inl rfl, by decide⟩
  have harg := kFreeT_rigid_const hp []
  have hbody := kFreeT_app hf (kFreeT_bvar covWRevEnv 0)
  have hsource := kFreeT_app
    (kFreeT_lam (kFreeT_rigid_const inv_P_rigid []) hbody) harg
  exact ⟨hsource, (kFreeT_letE_iff _ _ _).mpr hsource, kFreeT_app hf harg⟩

/-- Neither recursor in the admitted environment occurs in either source or
in their reduct. -/
theorem covWEtaInv_no_rec_occurrence :
    occursConst 2 covWEtaInvSource = false ∧ occursConst 7 covWEtaInvSource = false ∧
    occursConst 2 covWEtaInvLet = false ∧ occursConst 7 covWEtaInvLet = false ∧
    occursConst 2 covWEtaInvTarget = false ∧ occursConst 7 covWEtaInvTarget = false := by
  decide

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_EXPANSION_BOUNDARY_ROOTS
#print axioms covWEtaInvFn
#print axioms covWEtaInv_source_clean
#print axioms covWEtaInv_source_not_observed
#print axioms covWEtaInv_let_not_observed
#print axioms covWEtaInv_no_source_transport
#print axioms covWEtaInv_no_let_transport
#print axioms covWEtaInv_no_beta_antiReduction
#print axioms covWEtaInv_no_let_antiReduction
#print axioms covWEtaInv_no_step_antiReduction
#print axioms covWEtaInv_no_red_antiReduction
#print axioms covWEtaInv_no_conversion_antiReduction
#print axioms covWEtaInv_no_let_conversion_antiReduction
#print axioms covWEtaInv_coarse_observed
#print axioms covWEtaInv_kFree
#print axioms covWEtaInv_no_rec_occurrence
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_EXPANSION_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
