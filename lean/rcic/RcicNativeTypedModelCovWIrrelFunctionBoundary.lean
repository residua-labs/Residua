import rcic.RcicNativeTypedModelCovWEtaExpansionBoundary

/-!
# Function arguments retain a fine eta and beta boundary

The fresh object-language member `G : (Nat -> Nat) -> Prop` observes the
rigid successor compact in a nonproof argument position. The eta-expanded
successor can supply graph compacts but never that atomic rigid compact.
Strict demands at any observation of the syntactic arrow also reject it.
The finite-derivation invariants below include every old eta alternative.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelAudit.TypingFin TypedModelCovUAudit TypedModelCovVAudit
open TypedModelCovTAudit TypedModelCovWAudit TypedModelCovWTypedAudit
open TypedModelCovWEtaAudit ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWFunctionArrow : Expr Nat := .pi (.const 0 []) (.const 0 [])
def covWFunctionGType : Expr Nat := .pi covWFunctionArrow (.sort .zero)
def covWFunctionGMember : CheckedMember := ⟨.axiomM, 0, covWFunctionGType, none⟩
def covWFunctionEnv : ResolvedEnv := extendEnv natEnvU 4 covWFunctionGMember
def covWFunctionG : Expr Nat := .const 4 []
def covWFunctionSucc : Expr Nat := .const 2 []
def covWFunctionEta : Expr Nat :=
  .lam (.const 0 []) (.app (.const 2 []) (.bvar 0))
def covWFunctionTarget : Expr Nat := .app covWFunctionG covWFunctionSucc
def covWFunctionEtaSource : Expr Nat := .app covWFunctionG covWFunctionEta
def covWFunctionBody : Expr Nat := .app covWFunctionG (.bvar 0)
def covWFunctionFn : Expr Nat := .lam covWFunctionArrow covWFunctionBody
def covWFunctionBetaSource : Expr Nat := .app covWFunctionFn covWFunctionSucc
def covWFunctionAtom : CptT := .spine 2 []
def covWFunctionFine : CptT := .spine 4 [covWFunctionAtom]
def covWFunctionArrowCode : CptT :=
  .pi (.spine 0 []) [([.bot], .spine 0 [])]

def covWFunctionEnv_wf : EnvWfT covWFunctionEnv :=
  .axiom natEnvU 4 covWFunctionGType
    (.imax (.imax (.succ .zero) (.succ .zero)) (.succ .zero)) natEnvUWfT rfl
    (.pi [] covWFunctionArrow (.imax (.succ .zero) (.succ .zero))
      (.sort .zero) (.succ .zero) (covWTypedBetaNatArrow_ty 0 [])
      (.sort _ .zero)) (fun _ => rfl) rfl

def covWFunction_nat_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ (.const 0 []) (.sort (.succ .zero)) :=
  .const Γ 0 [] natFamMember rfl rfl rfl

def covWFunction_arrow_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionArrow
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.const 0 []) (.succ .zero) (.const 0 []) (.succ .zero)
    (covWFunction_nat_ty n Γ) (covWFunction_nat_ty n _)

def covWFunction_g_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionG covWFunctionGType :=
  .const Γ 4 [] covWFunctionGMember rfl rfl rfl

def covWFunction_succ_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionSucc covWFunctionArrow :=
  .const Γ 2 [] natSuccMember rfl rfl rfl

def covWFunction_eta_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionEta covWFunctionArrow :=
  .lam Γ (.const 0 []) (.succ .zero) (.app (.const 2 []) (.bvar 0))
    (.const 0 []) (covWFunction_nat_ty n Γ)
    (.app _ _ _ (.const 0 []) (.const 0 []) (covWFunction_succ_ty n _)
      (.bvar _ 0 _ rfl))

def covWFunction_target_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionTarget (.sort .zero) :=
  .app Γ covWFunctionG covWFunctionSucc covWFunctionArrow (.sort .zero)
    (covWFunction_g_ty n Γ) (covWFunction_succ_ty n Γ)

def covWFunction_eta_source_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionEtaSource (.sort .zero) :=
  .app Γ covWFunctionG covWFunctionEta covWFunctionArrow (.sort .zero)
    (covWFunction_g_ty n Γ) (covWFunction_eta_ty n Γ)

def covWFunction_body_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n (.assumption covWFunctionArrow :: Γ)
      covWFunctionBody (.sort .zero) :=
  .app _ _ _ covWFunctionArrow (.sort .zero) (covWFunction_g_ty n _)
    (.bvar _ 0 _ rfl)

def covWFunction_beta_source_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionBetaSource (.sort .zero) :=
  .app Γ covWFunctionFn covWFunctionSucc covWFunctionArrow (.sort .zero)
    (.lam Γ covWFunctionArrow (.imax (.succ .zero) (.succ .zero))
      covWFunctionBody (.sort .zero) (covWFunction_arrow_ty n Γ)
      (covWFunction_body_ty n Γ))
    (covWFunction_succ_ty n Γ)

def covWFunction_eta_conv (n : Nat) (Γ : LCtx) :
    ConvT covWFunctionEnv n Γ covWFunctionEtaSource covWFunctionTarget (.sort .zero) :=
  .app Γ covWFunctionG covWFunctionG covWFunctionEta covWFunctionSucc
    covWFunctionArrow (.sort .zero)
    (.refl Γ covWFunctionG covWFunctionGType (covWFunction_g_ty n Γ))
    (.eta Γ covWFunctionSucc (.const 0 []) (.const 0 []) (covWFunction_succ_ty n Γ))

def covWFunction_beta_conv (n : Nat) (Γ : LCtx) :
    ConvT covWFunctionEnv n Γ covWFunctionBetaSource covWFunctionTarget (.sort .zero) :=
  .beta Γ covWFunctionArrow covWFunctionBody covWFunctionSucc (.sort .zero)
    (.imax (.succ .zero) (.succ .zero))
    (covWFunction_arrow_ty n Γ) (covWFunction_body_ty n Γ) (covWFunction_succ_ty n Γ)

theorem covWFunction_beta_step (n : Nat) (Γ : LCtx) :
    WhStepCK2 covWFunctionEnv n Γ covWFunctionBetaSource covWFunctionTarget :=
  .ctx (.beta covWFunctionArrow covWFunctionBody covWFunctionSucc)

theorem covWFunction_nat_rigid : RigidConst covWFunctionEnv 0 :=
  rigidConst_of_inductiveM covWFunctionEnv_wf (m := natFamMember) rfl rfl

theorem covWFunction_succ_rigid : RigidConst covWFunctionEnv 2 := by
  intro m hm
  have he : m = natSuccMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covWFunction_g_rigid : RigidConst covWFunctionEnv 4 := by
  intro m hm
  have he : m = covWFunctionGMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covWFunction_nat_not_propCtor : ¬ PropCtorT covWFunctionEnv 0 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = natFamMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWFunction_succ_not_propCtor : ¬ PropCtorT covWFunctionEnv 2 := by
  rintro ⟨m, fam, fm, hm, _, hh, hf, hp⟩
  have he : m = natSuccMember := Option.some.inj hm.symm
  subst m
  have he : fam = 0 := Option.some.inj hh.symm
  subst fam
  have he : fm = natFamMember := Option.some.inj hf.symm
  subst fm
  cases hp

theorem covWFunction_g_not_propCtor : ¬ PropCtorT covWFunctionEnv 4 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covWFunctionGMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWFunction_succ_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionSucc covWFunctionAtom :=
  .free (kFreeT_rigid_const covWFunction_succ_rigid [])
    (.const ρ 2 [] covWFunction_succ_rigid covWFunction_succ_not_propCtor)

theorem covWFunction_g_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionG (.spine 4 []) :=
  .free (kFreeT_rigid_const covWFunction_g_rigid [])
    (.const ρ 4 [] covWFunction_g_rigid covWFunction_g_not_propCtor)

theorem covWFunction_target_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionTarget covWFunctionFine :=
  .appSpine (covWFunction_g_observed n Γ ρ) (covWFunction_succ_observed n Γ ρ)

theorem covWFunction_result_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWFunctionEnv n Γ ρ (.sort .zero) .prop :=
  .free (kFreeT_sort covWFunctionEnv .zero) (.sort ρ .zero)

theorem covWFunction_fine_typed : CTyS covWFunctionEnv covWFunctionFine .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covWFunctionGMember) rfl rfl)

theorem covWFunction_fine_nonbottom : covWFunctionFine ≠ .bot :=
  fun h => CptT.noConfusion h

theorem covWFunction_arrow_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionArrow covWFunctionArrowCode := by
  refine .pi
    (.free (kFreeT_rigid_const covWFunction_nat_rigid [])
      (.const ρ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor)) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .free (kFreeT_rigid_const covWFunction_nat_rigid [])
      (.const _ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor)

theorem covWFunction_nat_not_prop (args : List CptT) :
    ¬ IsPropCT covWFunctionEnv (.spine 0 args) := by
  intro h
  cases h with
  | spine hm hs =>
      have he : _ = natFamMember := Option.some.inj hm.symm
      subst he
      cases hs

theorem covWFunction_arrow_not_prop :
    ¬ IsPropCT covWFunctionEnv covWFunctionArrowCode := by
  intro h
  cases h with
  | pi _ hg =>
      exact covWFunction_nat_not_prop []
        (hg ([.bot], .spine 0 []) (List.mem_singleton.mpr rfl))

/-- A direct arrow observation, even with eta alternatives, cannot type a spine. -/
theorem covWFunction_pi_demand_no_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {A B : Expr Nat} {a : CptT} {r : Nat} {args : List CptT}
    (h : ApproxTKWEta E n Γ ρ (.pi A B) a) (ht : CTyS E (.spine r args) a) : False := by
  generalize he : Expr.pi A B = e at h
  cases h with
  | bot => exact CptT.noConfusion (ctyS_bot_inv ht)
  | free _ h =>
      rw [← he] at h
      rcases approxT_pi_inv (approxTN_forget (approxTW_forget h)) with
        rfl | ⟨a, f, rfl, _, _⟩
      · exact CptT.noConfusion (ctyS_bot_inv ht)
      · rcases ctyS_pi_inv ht with hb | ⟨f, hf, _⟩
        · exact CptT.noConfusion hb
        · exact CptT.noConfusion hf
  | pi =>
      rcases ctyS_pi_inv ht with hb | ⟨f, hf, _⟩
      · exact CptT.noConfusion hb
      · exact CptT.noConfusion hf
  | lam => cases he
  | app => cases he
  | appSpine => cases he
  | delta => cases he
  | letE => cases he
  | lit => cases he
  | iota =>
      simp only [iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      simp only [recCall_eq_app] at he
      cases he
  | eta => exact CptT.noConfusion (ctyS_lam_inv ht)

/-- Immediate spine fields exclude only the distinguished atomic function
compact. Graph outputs are checked extensionally at non-atomic row inputs. -/
def CovWFunctionClean : CptT → Prop
  | .spine r args => (r ≠ 2 ∨ args ≠ []) ∧ ∀ u ∈ args, u ≠ covWFunctionAtom
  | .lam g => ∀ s ∈ g, (∀ u ∈ s.1, u ≠ covWFunctionAtom) → CovWFunctionClean s.2
  | _ => True
termination_by c => sizeOf c
decreasing_by
  simp_wf
  have hs := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have ho := sizeOfT_snd_lt s
  omega

private def functionMaskUp (S : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => S i

private def functionEnvOn (S : Nat → Prop) (ρ : EnvT) : Prop :=
  ∀ i c, S i → ρ i c → c ≠ covWFunctionAtom

private theorem functionEnvOn_cons {S : Nat → Prop} {ρ : EnvT} {us : List CptT}
    (hρ : functionEnvOn S ρ) (hu : ∀ u ∈ us, u ≠ covWFunctionAtom) :
    functionEnvOn (functionMaskUp S) (EnvT.cons (demandT us) ρ) := by
  intro i c hi hc
  cases i with
  | zero => exact hu c hc
  | succ i => exact hρ i c hi hc

private inductive FunctionArg (S : Nat → Prop) : Expr Nat → Prop
  | bvar (i : Nat) (hi : S i) : FunctionArg S (.bvar i)
  | lam (A b : Expr Nat) : FunctionArg S (.lam A b)

private theorem FunctionArg.lift_one {S : Nat → Prop} {e : Expr Nat}
    (h : FunctionArg S e) : FunctionArg (functionMaskUp S) (lift 0 1 e) := by
  cases h with
  | bvar i hi =>
      simpa only [lift, Nat.zero_le, if_pos, Nat.add_one] using
        (FunctionArg.bvar (S := functionMaskUp S) (Nat.succ i) hi)
  | lam A b => exact .lam _ _

private theorem functionArg_raw_not_atom {E : ResolvedEnv} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTW E ρ e c)
    {S : Nat → Prop} (he : FunctionArg S e) (hρ : functionEnvOn S ρ) :
    c ≠ covWFunctionAtom := by
  cases h with
  | bot => intro h; cases h
  | bvar hv => cases he with | bvar _ hi => exact hρ _ _ hi hv
  | sort => cases he
  | pi => cases he
  | lam => intro h; cases h
  | app => cases he
  | const => cases he
  | delta => cases he
  | recursor => cases he
  | appSpine => cases he
  | letE => cases he
  | lit => cases he

private theorem functionArg_not_atom {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e : Expr Nat} {c : CptT} (h : ApproxTKWEta E n Γ ρ e c)
    {S : Nat → Prop} (he : FunctionArg S e) (hρ : functionEnvOn S ρ) :
    c ≠ covWFunctionAtom := by
  cases h with
  | bot => intro h; cases h
  | free _ h => exact functionArg_raw_not_atom h he hρ
  | pi => cases he
  | lam => intro h; cases h
  | app => cases he
  | appSpine => cases he
  | delta => cases he
  | letE => cases he
  | lit => cases he
  | iota =>
      simp only [iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      simp only [recCall_eq_app] at he
      cases he
  | eta => intro h; cases h

private inductive FunctionRigid (E : ResolvedEnv) (S : Nat → Prop) : Expr Nat → Prop
  | const (r : Nat) (ls : List Level) (hr : RigidConst E r) (hn : r ≠ 2) :
      FunctionRigid E S (.const r ls)
  | app {f x : Expr Nat} (hf : FunctionRigid E S f) (hx : FunctionArg S x) :
      FunctionRigid E S (.app f x)

private theorem FunctionRigid.lift_one {E : ResolvedEnv} {S : Nat → Prop} {e : Expr Nat}
    (h : FunctionRigid E S e) : FunctionRigid E (functionMaskUp S) (lift 0 1 e) := by
  induction h with
  | const r ls hr hn => exact .const r ls hr hn
  | app _ hx ih => exact .app ih hx.lift_one

private theorem FunctionRigid.foldApps_head {E : ResolvedEnv} {S : Nat → Prop}
    {f : Expr Nat} {xs : List (Expr Nat)}
    (h : FunctionRigid E S (foldApps f xs)) : FunctionRigid E S f := by
  induction xs generalizing f with
  | nil => exact h
  | cons x xs ih =>
      have hh := ih h
      cases hh with
      | app hf _ => exact hf

private theorem function_clean_bot : CovWFunctionClean .bot := by
  simp [CovWFunctionClean]

private theorem function_clean_appSpine {r : Nat} {args : List CptT} {u : CptT}
    (hf : CovWFunctionClean (.spine r args)) (hu : u ≠ covWFunctionAtom) :
    CovWFunctionClean (.spine r (args ++ [u])) := by
  rw [CovWFunctionClean] at hf ⊢
  refine ⟨Or.inr (by simp), ?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hf.2 v hv
  · have he : v = u := List.mem_singleton.mp hv
    subst v
    exact hu

private theorem function_rigid_raw_clean {E : ResolvedEnv} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTW E ρ e c)
    {S : Nat → Prop} (he : FunctionRigid E S e) (hρ : functionEnvOn S ρ) :
    CovWFunctionClean c := by
  induction h with
  | bot => exact function_clean_bot
  | bvar => cases he
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app _ hs ha ihf _ =>
      cases he with
      | app hf hx =>
          have hh := ihf hf hρ
          rw [CovWFunctionClean] at hh
          exact hh _ hs (fun u hu => functionArg_raw_not_atom (ha u hu) hx hρ)
  | const _ _ _ _ _ =>
      cases he with
      | const r ls hr hn =>
          rw [CovWFunctionClean]
          exact ⟨Or.inl hn, fun u hu => nomatch hu⟩
  | delta hd _ _ =>
      cases he with
      | const _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | @recursor ρ w ls hnp up uf c hp hf hb ih =>
      cases he with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | appSpine _ ha ihf _ =>
      cases he with
      | app hf hx =>
          exact function_clean_appSpine (ihf hf hρ) (functionArg_raw_not_atom ha hx hρ)
  | letE => cases he
  | lit => cases he

private theorem function_rigid_clean {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e : Expr Nat} {c : CptT} (h : ApproxTKWEta E n Γ ρ e c)
    {S : Nat → Prop} (he : FunctionRigid E S e) (hρ : functionEnvOn S ρ) :
    CovWFunctionClean c := by
  induction h generalizing S with
  | bot => exact function_clean_bot
  | free _ h => exact function_rigid_raw_clean h he hρ
  | pi => cases he
  | lam => cases he
  | app _ hs ha ihf _ =>
      cases he with
      | app hf hx =>
          have hh := ihf hf hρ
          rw [CovWFunctionClean] at hh
          exact hh _ hs (fun u hu => functionArg_not_atom (ha u hu) hx hρ)
  | appSpine _ ha ihf _ =>
      cases he with
      | app hf hx =>
          exact function_clean_appSpine (ihf hf hρ) (functionArg_not_atom ha hx hρ)
  | delta hd _ _ =>
      cases he with
      | const _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | letE => cases he
  | lit => cases he
  | iota w _ _ _ =>
      have hh := FunctionRigid.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ _ =>
      have hh := FunctionRigid.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta _ _ _ _ _ ihD ihb =>
      rw [CovWFunctionClean]
      intro s hs hus
      exact ihb s hs (.app he.lift_one (.bvar 0 trivial))
        (functionEnvOn_cons hρ hus)

theorem covWFunction_fine_not_clean : ¬ CovWFunctionClean covWFunctionFine := by
  intro h
  rw [covWFunctionFine, CovWFunctionClean] at h
  exact h.2 covWFunctionAtom (by simp) rfl

theorem covWFunction_eta_source_clean {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionEtaSource c) :
    CovWFunctionClean c :=
  function_rigid_clean h
    (.app (.const 4 [] covWFunction_g_rigid (by decide)) (.lam _ _))
    (S := fun _ => False) (fun _ _ hi _ => hi.elim)

theorem covWFunction_eta_source_absent (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionEtaSource covWFunctionFine :=
  fun h => covWFunction_fine_not_clean (covWFunction_eta_source_clean h)

theorem covWFunction_arrow_kFree : KFreeT covWFunctionEnv covWFunctionArrow :=
  kFreeT_pi (kFreeT_rigid_const covWFunction_nat_rigid [])
    (kFreeT_rigid_const covWFunction_nat_rigid [])

private theorem function_body_masked :
    FunctionRigid covWFunctionEnv (fun i => i = 0) covWFunctionBody :=
  .app (.const 4 [] covWFunction_g_rigid (by decide)) (.bvar 0 rfl)

private theorem functionFn_lift : lift 0 1 covWFunctionFn = covWFunctionFn := rfl

private def FunctionRowsClean : CptT → Prop
  | .bot => True
  | .lam g => ∀ s ∈ g, CovWFunctionClean s.2
  | _ => False

private inductive FunctionProtected (S : Nat → Prop) : Expr Nat → Prop
  | first (arg : Expr Nat) : FunctionProtected S (.app covWFunctionFn arg)
  | app {f x : Expr Nat} (hf : FunctionProtected S f) (hx : FunctionArg S x) :
      FunctionProtected S (.app f x)

private theorem FunctionProtected.lift_one {S : Nat → Prop} {e : Expr Nat}
    (h : FunctionProtected S e) : FunctionProtected (functionMaskUp S) (lift 0 1 e) := by
  induction h with
  | first arg =>
      change FunctionProtected (functionMaskUp S)
        (.app (lift 0 1 covWFunctionFn) (lift 0 1 arg))
      rw [functionFn_lift]
      exact .first _
  | app _ hx ih => exact .app ih hx.lift_one

private theorem FunctionProtected.head {S : Nat → Prop} {e : Expr Nat}
    (h : FunctionProtected S e) : headConst e = none := by
  induction h with
  | first => rfl
  | app _ _ ih => exact ih

private theorem function_headConst_apps (f : Expr Nat) (xs : List (Expr Nat)) :
    headConst (foldApps f xs) = headConst f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

private theorem function_raw_rows_clean {ρ : EnvT} {c : CptT}
    (h : ApproxTW covWFunctionEnv ρ covWFunctionFn c) : FunctionRowsClean c := by
  cases h with
  | bot => trivial
  | lam hA ht _ hb =>
      intro s hs
      apply function_rigid_raw_clean (hb s hs) function_body_masked
      intro i d hi hd he
      subst i
      subst d
      exact covWFunction_pi_demand_no_spine
        (n := 0) (Γ := []) (.free covWFunction_arrow_kFree hA) (ht s hs _ hd)

private theorem function_protected_raw_clean {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTW covWFunctionEnv ρ e c) {S : Nat → Prop}
    (he : FunctionProtected S e) (hρ : functionEnvOn S ρ) : CovWFunctionClean c := by
  induction h with
  | bot => exact function_clean_bot
  | bvar => cases he
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app hf hs ha ihf _ =>
      cases he with
      | first _ => exact function_raw_rows_clean hf _ hs
      | app hp hx =>
          have hh := ihf hp hρ
          rw [CovWFunctionClean] at hh
          exact hh _ hs (fun u hu => functionArg_raw_not_atom (ha u hu) hx hρ)
  | const => cases he
  | delta => cases he
  | recursor => cases he
  | appSpine hf ha ihf _ =>
      cases he with
      | first _ => exact (function_raw_rows_clean hf).elim
      | app hp hx =>
          exact function_clean_appSpine (ihf hp hρ) (functionArg_raw_not_atom ha hx hρ)
  | letE => cases he
  | lit => cases he

/-- The lambda's rows are clean independently of the tested argument.
The second conjunct handles every eta graph of that same lambda. -/
private theorem function_protected_clean {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTKWEta covWFunctionEnv n Γ ρ e c) :
    (∀ S, FunctionProtected S e → functionEnvOn S ρ → CovWFunctionClean c) ∧
    (e = covWFunctionFn → FunctionRowsClean c) := by
  induction h with
  | bot => exact ⟨fun _ _ _ => function_clean_bot, fun _ => trivial⟩
  | free _ h =>
      refine ⟨fun _ he hρ => function_protected_raw_clean h he hρ, ?_⟩
      intro he
      rw [he] at h
      exact function_raw_rows_clean h
  | pi =>
      constructor
      · intro S he; cases he
      · intro he; cases he
  | lam hA ht _ hb ihA ihb =>
      constructor
      · intro S he; cases he
      · intro he
        cases he
        intro s hs
        apply function_rigid_clean (hb s hs) function_body_masked
        intro i d hi hd he
        subst i
        subst d
        exact covWFunction_pi_demand_no_spine hA (ht s hs _ hd)
  | app hf hs ha ihf _ =>
      constructor
      · intro S he hρ
        cases he with
        | first _ => exact ihf.2 rfl _ hs
        | app hp hx =>
            have hh := ihf.1 S hp hρ
            rw [CovWFunctionClean] at hh
            exact hh _ hs (fun u hu => functionArg_not_atom (ha u hu) hx hρ)
      · intro he; cases he
  | appSpine hf ha ihf _ =>
      constructor
      · intro S he hρ
        cases he with
        | first _ => exact (ihf.2 rfl).elim
        | app hp hx =>
            exact function_clean_appSpine (ihf.1 S hp hρ)
              (functionArg_not_atom ha hx hρ)
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
        rw [iotaLhsOfS, recCall, function_headConst_apps] at hh
        cases hh
      · intro he
        simp only [iotaLhsOfS, recCall_eq_app, covWFunctionFn] at he
        cases he
  | recursorPropK w x _ _ _ _ _ _ _ =>
      constructor
      · intro S he
        have hh := he.head
        rw [recCall, function_headConst_apps] at hh
        cases hh
      · intro he
        simp only [recCall_eq_app, covWFunctionFn] at he
        cases he
  | eta _ _ _ _ _ ihD ihb =>
      constructor
      · intro S he hρ
        rw [CovWFunctionClean]
        intro s hs hus
        exact (ihb s hs).1 (functionMaskUp S)
          (.app he.lift_one (.bvar 0 trivial)) (functionEnvOn_cons hρ hus)
      · intro he
        cases he
        intro s hs
        apply (ihb s hs).1 (fun _ => False)
        · rw [functionFn_lift]
          exact .first _
        · intro i d hi
          exact hi.elim

theorem covWFunction_beta_source_clean {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionBetaSource c) :
    CovWFunctionClean c :=
  (function_protected_clean h).1 (fun _ => False) (.first _)
    (fun _ _ hi _ => hi.elim)

theorem covWFunction_beta_source_absent (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionBetaSource covWFunctionFine :=
  fun h => covWFunction_fine_not_clean (covWFunction_beta_source_clean h)

theorem covWFunction_target_normal (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 covWFunctionEnv n) Γ covWFunctionTarget :=
  covV_body_free_spine_normal
    (rfl : covWFunctionEnv.members 4 = some covWFunctionGMember) rfl (by decide)
    [] [covWFunctionSucc]

theorem covWFunction_eta_source_normal (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 covWFunctionEnv n) Γ covWFunctionEtaSource :=
  covV_body_free_spine_normal
    (rfl : covWFunctionEnv.members 4 = some covWFunctionGMember) rfl (by decide)
    [] [covWFunctionEta]

theorem covWFunction_kFree :
    KFreeT covWFunctionEnv covWFunctionTarget ∧
    KFreeT covWFunctionEnv covWFunctionEtaSource ∧
    KFreeT covWFunctionEnv covWFunctionBetaSource := by
  have hg := kFreeT_rigid_const covWFunction_g_rigid []
  have hs := kFreeT_rigid_const covWFunction_succ_rigid []
  have hn := kFreeT_rigid_const covWFunction_nat_rigid []
  have hv := kFreeT_bvar covWFunctionEnv 0
  exact ⟨kFreeT_app hg hs, kFreeT_app hg (kFreeT_lam hn (kFreeT_app hs hv)),
    kFreeT_app (kFreeT_lam covWFunction_arrow_kFree (kFreeT_app hg hv)) hs⟩

theorem covWFunction_no_rec_occurrence :
    occursConst 3 covWFunctionTarget = false ∧
    occursConst 3 covWFunctionEtaSource = false ∧
    occursConst 3 covWFunctionBetaSource = false := by decide

/-- Native and semantic hypotheses for both closed failures are actual data. -/
structure CovWFunctionOldFailureAt (n : Nat) : Prop where
  envWf : Nonempty (EnvWfT covWFunctionEnv)
  ctxWf : Nonempty (CtxWfT covWFunctionEnv n [])
  realized : CovWEtaRealized covWFunctionEnv n 2 [] EnvT.bot SubstT.id
  valuation : EnvTypedFinAtT
    (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv) [] EnvT.bot
  coherence : CtxEnvM
    (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv) [] EnvT.bot
  arrowTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionArrow
    (.sort (.imax (.succ .zero) (.succ .zero))))
  succTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionSucc covWFunctionArrow)
  etaTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionEta covWFunctionArrow)
  gTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionG covWFunctionGType)
  targetTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionTarget (.sort .zero))
  etaSourceTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionEtaSource (.sort .zero))
  betaSourceTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionBetaSource (.sort .zero))
  typeTy : Nonempty (HasTyT covWFunctionEnv n [] (.sort .zero) (.sort (.succ .zero)))
  etaConversion : Nonempty
    (ConvT covWFunctionEnv n [] covWFunctionEtaSource covWFunctionTarget (.sort .zero))
  betaConversion : Nonempty
    (ConvT covWFunctionEnv n [] covWFunctionBetaSource covWFunctionTarget (.sort .zero))
  betaStep : WhStepCK2 covWFunctionEnv n [] covWFunctionBetaSource covWFunctionTarget
  betaReadback : RedR (WhStepCK2 covWFunctionEnv n) [] covWFunctionBetaSource covWFunctionTarget
  targetNormal : NormalR (WhStepCK2 covWFunctionEnv n) [] covWFunctionTarget
  etaSourceNormal : NormalR (WhStepCK2 covWFunctionEnv n) [] covWFunctionEtaSource
  targetObservation : ApproxTKWEta covWFunctionEnv n [] EnvT.bot
    covWFunctionTarget covWFunctionFine
  typeObservation : ApproxTKWEta covWFunctionEnv n [] EnvT.bot (.sort .zero) .prop
  arrowObservation : ApproxTKWEta covWFunctionEnv n [] EnvT.bot
    covWFunctionArrow covWFunctionArrowCode
  arrowNonproof : ¬ IsPropCT covWFunctionEnv covWFunctionArrowCode
  demand : CTyS covWFunctionEnv covWFunctionFine .prop
  nonbottom : covWFunctionFine ≠ .bot
  etaNoFine : ¬ ApproxTKWEta covWFunctionEnv n [] EnvT.bot
    covWFunctionEtaSource covWFunctionFine
  betaNoFine : ¬ ApproxTKWEta covWFunctionEnv n [] EnvT.bot
    covWFunctionBetaSource covWFunctionFine

theorem covWFunction_old_inhabited (n : Nat) : CovWFunctionOldFailureAt n where
  envWf := ⟨covWFunctionEnv_wf⟩
  ctxWf := ⟨.nil⟩
  realized := covWEta_realized_nil _ _ _
  valuation := envTypedFinAtT_nil _ _
  coherence := fun _ _ hv => Option.noConfusion hv
  arrowTy := ⟨covWFunction_arrow_ty n []⟩
  succTy := ⟨covWFunction_succ_ty n []⟩
  etaTy := ⟨covWFunction_eta_ty n []⟩
  gTy := ⟨covWFunction_g_ty n []⟩
  targetTy := ⟨covWFunction_target_ty n []⟩
  etaSourceTy := ⟨covWFunction_eta_source_ty n []⟩
  betaSourceTy := ⟨covWFunction_beta_source_ty n []⟩
  typeTy := ⟨.sort [] .zero⟩
  etaConversion := ⟨covWFunction_eta_conv n []⟩
  betaConversion := ⟨covWFunction_beta_conv n []⟩
  betaStep := covWFunction_beta_step n []
  betaReadback := redR_single (covWFunction_beta_step n [])
  targetNormal := covWFunction_target_normal n []
  etaSourceNormal := covWFunction_eta_source_normal n []
  targetObservation := covWFunction_target_observed n [] EnvT.bot
  typeObservation := covWFunction_result_type_observed n [] EnvT.bot
  arrowObservation := covWFunction_arrow_observed n [] EnvT.bot
  arrowNonproof := covWFunction_arrow_not_prop
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  etaNoFine := covWFunction_eta_source_absent n [] EnvT.bot
  betaNoFine := covWFunction_beta_source_absent n [] EnvT.bot

theorem covWFunction_old_no_eta_conversion_transport (n : Nat) :
    ¬ covWTyped_antiReductionAt covWFunctionEnv n []
      (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv)
      (fun e e' => Nonempty (ConvT covWFunctionEnv n [] e e' (.sort .zero))) := by
  intro h
  have hi := covWFunction_old_inhabited n
  exact hi.etaNoFine
    (h EnvT.bot covWFunctionEtaSource covWFunctionTarget (.sort .zero) (.succ .zero)
      covWFunctionFine .prop hi.envWf hi.ctxWf hi.valuation hi.etaSourceTy hi.targetTy
      hi.typeTy hi.etaConversion hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_old_no_beta_transport (n : Nat) :
    ¬ covWTyped_antiReductionAt covWFunctionEnv n []
      (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv) CovWTypedBetaHead := by
  intro h
  have hi := covWFunction_old_inhabited n
  exact hi.betaNoFine
    (h EnvT.bot covWFunctionBetaSource covWFunctionTarget (.sort .zero) (.succ .zero)
      covWFunctionFine .prop hi.envWf hi.ctxWf hi.valuation hi.betaSourceTy hi.targetTy
      hi.typeTy ⟨covWFunctionArrow, covWFunctionBody, covWFunctionSucc, rfl, rfl⟩
      hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_old_same_stage (n : Nat) :
    CovWEtaRealized covWFunctionEnv n 2 [] EnvT.bot SubstT.id ∧
    ApproxTKWEtaStage covWFunctionEnv n 2 [] EnvT.bot covWFunctionTarget covWFunctionFine ∧
    ApproxTKWEtaStage covWFunctionEnv n 2 [] EnvT.bot (.sort .zero) .prop := by
  refine ⟨covWEta_realized_nil _ _ _,
    ⟨covWFunction_target_observed n [] EnvT.bot, ?_⟩,
    ⟨covWFunction_result_type_observed n [] EnvT.bot, ?_⟩⟩
  all_goals simp [covTObservationBudget, covWFunctionFine, covWFunctionAtom]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FUNCTION_BOUNDARY_ROOTS
#print axioms covWFunctionArrow
#print axioms covWFunctionGType
#print axioms covWFunctionGMember
#print axioms covWFunctionEnv
#print axioms covWFunctionG
#print axioms covWFunctionSucc
#print axioms covWFunctionEta
#print axioms covWFunctionTarget
#print axioms covWFunctionEtaSource
#print axioms covWFunctionBody
#print axioms covWFunctionFn
#print axioms covWFunctionBetaSource
#print axioms covWFunctionAtom
#print axioms covWFunctionFine
#print axioms covWFunctionArrowCode
#print axioms covWFunctionEnv_wf
#print axioms covWFunction_nat_ty
#print axioms covWFunction_arrow_ty
#print axioms covWFunction_g_ty
#print axioms covWFunction_succ_ty
#print axioms covWFunction_eta_ty
#print axioms covWFunction_target_ty
#print axioms covWFunction_eta_source_ty
#print axioms covWFunction_body_ty
#print axioms covWFunction_beta_source_ty
#print axioms covWFunction_eta_conv
#print axioms covWFunction_beta_conv
#print axioms covWFunction_beta_step
#print axioms covWFunction_nat_rigid
#print axioms covWFunction_succ_rigid
#print axioms covWFunction_g_rigid
#print axioms covWFunction_nat_not_propCtor
#print axioms covWFunction_succ_not_propCtor
#print axioms covWFunction_g_not_propCtor
#print axioms covWFunction_succ_observed
#print axioms covWFunction_g_observed
#print axioms covWFunction_target_observed
#print axioms covWFunction_result_type_observed
#print axioms covWFunction_fine_typed
#print axioms covWFunction_fine_nonbottom
#print axioms covWFunction_arrow_observed
#print axioms covWFunction_nat_not_prop
#print axioms covWFunction_arrow_not_prop
#print axioms covWFunction_pi_demand_no_spine
#print axioms CovWFunctionClean
#print axioms covWFunction_fine_not_clean
#print axioms covWFunction_eta_source_clean
#print axioms covWFunction_eta_source_absent
#print axioms covWFunction_arrow_kFree
#print axioms covWFunction_beta_source_clean
#print axioms covWFunction_beta_source_absent
#print axioms covWFunction_target_normal
#print axioms covWFunction_eta_source_normal
#print axioms covWFunction_kFree
#print axioms covWFunction_no_rec_occurrence
#print axioms CovWFunctionOldFailureAt
#print axioms covWFunction_old_inhabited
#print axioms covWFunction_old_no_eta_conversion_transport
#print axioms covWFunction_old_no_beta_transport
#print axioms covWFunction_old_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FUNCTION_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
