import rcic.RcicNativeTypedModelCovWEtaAligned
import rcic.RcicNativeTypedModelCovWRevealed

/-!
# A typed inverse-substitution boundary after finite eta observation

The observed result is a proposition *code*, whose strict demand is typed at
the actual observation of `Prop`. Its argument field retains the rigid compact
of the proof `p`. Every strict binder demand at the observed proposition `P`
is bottom, so no finite demand list can reconstruct that result in the body.
The proof covers the complete new finite grammar, including recursive eta.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelAudit.TypingFin
open TypedModelCovUAudit TypedModelCovVAudit TypedModelCovWAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Rigid expressions that do not mention the distinguished proof constant. -/
inductive CovWEtaRigidTerm (E : ResolvedEnv) : Expr Nat → Prop
  | bvar (i : Nat) : CovWEtaRigidTerm E (.bvar i)
  | const (r : Nat) (ls : List Level) (hr : RigidConst E r) (hne : r ≠ 4) :
      CovWEtaRigidTerm E (.const r ls)
  | app {f x : Expr Nat} (hf : CovWEtaRigidTerm E f) (hx : CovWEtaRigidTerm E x) :
      CovWEtaRigidTerm E (.app f x)

theorem CovWEtaRigidTerm.lift {E : ResolvedEnv} {e : Expr Nat}
    (h : CovWEtaRigidTerm E e) (k d : Nat) :
    CovWEtaRigidTerm E (lift k d e) := by
  induction h with
  | bvar i =>
      change CovWEtaRigidTerm E (if k ≤ i then .bvar (i + d) else .bvar i)
      split <;> exact .bvar _
  | const r ls hr hn => exact .const r ls hr hn
  | app _ _ ihf ihx => exact .app ihf ihx

theorem CovWEtaRigidTerm.foldApps_head {E : ResolvedEnv}
    {f : Expr Nat} {xs : List (Expr Nat)}
    (h : CovWEtaRigidTerm E (foldApps f xs)) : CovWEtaRigidTerm E f := by
  induction xs generalizing f with
  | nil => exact h
  | cons x xs ih =>
      have hfx := ih h
      cases hfx with
      | app hf _ => exact hf

/-- Lambda rows preserve cleanliness when their finite inputs are clean.
Spines retain cleanliness in every argument field. -/
def CovWEtaClean : CptT → Prop
  | .spine r args => r ≠ 4 ∧ ∀ u ∈ args, CovWEtaClean u
  | .lam g => ∀ s ∈ g, (∀ u ∈ s.1, CovWEtaClean u) → CovWEtaClean s.2
  | _ => True
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have h := List.sizeOf_lt_of_mem (show u ∈ args from ‹_›); omega)
    | (have hs := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have hu := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have hf := sizeOfT_fst_lt s
       omega)
    | (have hs := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have ho := sizeOfT_snd_lt s
       omega)

def CovWEtaCleanEnv (ρ : EnvT) : Prop :=
  ∀ i c, ρ i c → CovWEtaClean c

theorem covWEta_clean_bot : CovWEtaClean .bot := by simp [CovWEtaClean]

theorem covWEta_cleanEnv_bot : CovWEtaCleanEnv EnvT.bot := by
  intro i c hc
  change c = .bot at hc
  subst c
  exact covWEta_clean_bot

theorem covWEta_cleanEnv_cons {ρ : EnvT} {us : List CptT}
    (hρ : CovWEtaCleanEnv ρ) (hus : ∀ u ∈ us, CovWEtaClean u) :
    CovWEtaCleanEnv (EnvT.cons (demandT us) ρ) := by
  intro i c hc
  cases i with
  | zero => exact hus c hc
  | succ i => exact hρ i c hc

theorem covWEta_clean_appSpine {r : Nat} {args : List CptT} {u : CptT}
    (hf : CovWEtaClean (.spine r args)) (hu : CovWEtaClean u) :
    CovWEtaClean (.spine r (args ++ [u])) := by
  rw [CovWEtaClean] at hf ⊢
  refine ⟨hf.1, ?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hf.2 v hv
  · have he : v = u := List.mem_singleton.mp hv
    subst v
    exact hu

/-- A raw derivation cannot manufacture the omitted rigid proof compact. -/
theorem covWEta_raw_clean {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTW E ρ e c) (he : CovWEtaRigidTerm E e)
    (hρ : CovWEtaCleanEnv ρ) : CovWEtaClean c := by
  induction h with
  | bot => exact covWEta_clean_bot
  | bvar hv => exact hρ _ _ hv
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

/-- The finite eta rule preserves the same invariant. The induction uses its
recursive body premise, so it covers every alternate eta derivation. -/
theorem covWEta_observation_clean {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKWEta E n Γ ρ e c) (he : CovWEtaRigidTerm E e)
    (hρ : CovWEtaCleanEnv ρ) : CovWEtaClean c := by
  induction h with
  | bot => exact covWEta_clean_bot
  | free _ h => exact covWEta_raw_clean h he hρ
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
      have hh := CovWEtaRigidTerm.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ _ =>
      have hh := CovWEtaRigidTerm.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta _ _ _ _ _ ihD ihb =>
      rw [CovWEtaClean]
      intro s hs hus
      exact ihb s hs (.app (he.lift 0 1) (.bvar 0))
        (covWEta_cleanEnv_cons hρ hus)

def covWEtaInvBody : Expr Nat := .app (.const 5 []) (.bvar 0)
def covWEtaInvTarget : Expr Nat := .app (.const 5 []) covUProjProof
def covWEtaInvCompact : CptT := .spine 5 [.spine 4 []]
def covWEtaInvSource : Expr Nat :=
  .app (.lam covUProjP covWEtaInvBody) covUProjProof
def covWEtaInvLet : Expr Nat := .letE covUProjP covUProjProof covWEtaInvBody

private theorem covWEtaInv_P_rigid : RigidConst covWRevEnv 3 := by
  intro m hm
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

private theorem covWEtaInv_fam_rigid : RigidConst covWRevEnv 5 :=
  rigidConst_of_inductiveM covWRevEnv_wf (m := covWRevFam) rfl rfl

private theorem covWEtaInv_P_not_propCtor : ¬ PropCtorT covWRevEnv 3 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  cases hk

private theorem covWEtaInv_fam_not_propCtor : ¬ PropCtorT covWRevEnv 5 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covWRevFam := Option.some.inj hm.symm
  subst m
  cases hk

/-- Eta can add a lambda code for `P`; that code also admits only bottom
strict demands. This statement does not assume that every code of `P` is a
positive proposition code. -/
theorem covWEtaInv_P_demands_bot {n : Nat} {Γ : LCtx} {ρ : EnvT} {a u : CptT}
    (h : ApproxTKWEta covWRevEnv n Γ ρ covUProjP a)
    (ht : CTyS covWRevEnv u a) : u = .bot := by
  generalize he : covUProjP = e at h
  cases h with
  | bot => exact ctyS_bot_inv ht
  | free _ h =>
      rw [← he] at h
      have ho := approxTN_forget (approxTW_forget h)
      rcases approxT_rigid_const_inv covWEtaInv_P_rigid ho with rfl | rfl
      · exact ctyS_bot_inv ht
      · exact ctyS_prop_bot (.spine (m := covUProjPMember) rfl rfl) ht
  | pi => cases he
  | lam => cases he
  | app => cases he
  | appSpine => cases he
  | delta hd _ =>
      cases he
      exact (not_rigidConst_of_deltaConst hd covWEtaInv_P_rigid).elim
  | letE => cases he
  | lit => cases he
  | iota =>
      simp only [covUProjP, iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      simp only [covUProjP, recCall_eq_app] at he
      cases he
  | eta => exact ctyS_lam_inv ht

theorem covWEtaInv_body_clean : CovWEtaRigidTerm covWRevEnv covWEtaInvBody :=
  .app (.const 5 [] covWEtaInv_fam_rigid (by decide)) (.bvar 0)

theorem covWEtaInv_compact_not_clean : ¬ CovWEtaClean covWEtaInvCompact := by
  intro h
  rw [covWEtaInvCompact, CovWEtaClean] at h
  have hp := h.2 (.spine 4 []) (by simp)
  rw [CovWEtaClean] at hp
  exact hp.1 rfl

/-- No typed finite binder demand reconstructs the observed result, even
when the observed domain code is chosen existentially. -/
theorem covWEtaInv_no_typed_factor (n : Nat) :
    ¬ ∃ (a : CptT) (us : List CptT),
      ApproxTKWEta covWRevEnv n [] EnvT.bot covUProjP a ∧
      (∀ u ∈ us, CTyS covWRevEnv u a) ∧
      (∀ u ∈ us, ApproxTKWEta covWRevEnv n [] EnvT.bot covUProjProof u) ∧
      ApproxTKWEta covWRevEnv n [.assumption covUProjP]
        (EnvT.cons (demandT us) EnvT.bot) covWEtaInvBody covWEtaInvCompact := by
  rintro ⟨a, us, ha, ht, _, hb⟩
  have hs : ∀ u ∈ us, CovWEtaClean u := by
    intro u hu
    rw [covWEtaInv_P_demands_bot ha (ht u hu)]
    exact covWEta_clean_bot
  exact covWEtaInv_compact_not_clean (covWEta_observation_clean hb
    covWEtaInv_body_clean (covWEta_cleanEnv_cons covWEta_cleanEnv_bot hs))

def covWEtaInvBody_ty (n : Nat) :
    HasTyT covWRevEnv n [.assumption covUProjP] covWEtaInvBody (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 5 [] covWRevFam rfl rfl rfl) (.bvar _ 0 _ rfl)

def covWEtaInvLetBody_ty (n : Nat) :
    HasTyT covWRevEnv n [.letBinding covUProjP covUProjProof]
      covWEtaInvBody (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 5 [] covWRevFam rfl rfl rfl) (.bvar _ 0 _ rfl)

def covWEtaInvTarget_ty (n : Nat) :
    HasTyT covWRevEnv n [] covWEtaInvTarget (.sort .zero) :=
  covWRevFamily_ty n [] (covWRevIndex_ty n [])

def covWEtaInvSource_ty (n : Nat) :
    HasTyT covWRevEnv n [] covWEtaInvSource (.sort .zero) :=
  .app _ _ _ _ _
    (.lam _ _ _ _ _ (covWRevP_ty n []) (covWEtaInvBody_ty n))
    (covWRevIndex_ty n [])

def covWEtaInvLet_ty (n : Nat) :
    HasTyT covWRevEnv n [] covWEtaInvLet (.sort .zero) :=
  .letE [] covUProjP .zero covUProjProof (.sort .zero) covWEtaInvBody
    (covWRevP_ty n []) (covWRevIndex_ty n []) (covWEtaInvLetBody_ty n)

def covWEtaInv_beta_conv (n : Nat) :
    ConvT covWRevEnv n [] covWEtaInvSource covWEtaInvTarget (.sort .zero) :=
  .beta [] covUProjP covWEtaInvBody covUProjProof (.sort .zero) .zero
    (covWRevP_ty n []) (covWEtaInvBody_ty n) (covWRevIndex_ty n [])

def covWEtaInv_let_conv (n : Nat) :
    ConvT covWRevEnv n [] covWEtaInvLet covWEtaInvTarget (.sort .zero) :=
  .zeta [] covUProjP covUProjProof covWEtaInvBody (.sort .zero) .zero
    (covWRevP_ty n []) (covWRevIndex_ty n []) (covWEtaInvLetBody_ty n)

theorem covWEtaInv_beta_step (n : Nat) :
    WhStepCK2 covWRevEnv n [] covWEtaInvSource covWEtaInvTarget :=
  .ctx (.beta covUProjP covWEtaInvBody covUProjProof)

theorem covWEtaInv_let_step (n : Nat) :
    WhStepCK2 covWRevEnv n [] covWEtaInvLet covWEtaInvTarget :=
  .ctx (.zeta covUProjP covUProjProof covWEtaInvBody)

theorem covWEtaInv_normal (n : Nat) :
    NormalR (WhStepCK2 covWRevEnv n) [] covWEtaInvTarget :=
  covV_body_free_spine_normal (m := covWRevFam)
    (rfl : covWRevEnv.members 5 = some covWRevFam) rfl (by decide)
    [] [covUProjProof]

theorem covWEtaInv_subst :
    instantiate0 covUProjProof covWEtaInvBody = covWEtaInvTarget := rfl

theorem covWEtaInv_P_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWRevEnv n Γ ρ covUProjP (.spine 3 []) :=
  .free (kFreeT_rigid_const covWEtaInv_P_rigid [])
    (.const ρ 3 [] covWEtaInv_P_rigid covWEtaInv_P_not_propCtor)

theorem covWEtaInv_arg_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWRevEnv n Γ ρ covUProjProof (.spine 4 []) :=
  covWEta_of_old (covWRev_index_observed n Γ ρ)

theorem covWEtaInv_target_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWRevEnv n Γ ρ covWEtaInvTarget covWEtaInvCompact :=
  .appSpine
    (.free (kFreeT_rigid_const covWEtaInv_fam_rigid [])
      (.const ρ 5 [] covWEtaInv_fam_rigid covWEtaInv_fam_not_propCtor))
    (covWEtaInv_arg_observed n Γ ρ)

theorem covWEtaInv_result_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWRevEnv n Γ ρ (.sort .zero) .prop :=
  .free (kFreeT_sort covWRevEnv .zero) (.sort ρ .zero)

/-- The result compact itself satisfies the strict top-level demand at the
actual observed result type. Its retained proof argument is what fails the
binder's stricter demand check. -/
theorem covWEtaInv_compact_typed : CTyS covWRevEnv covWEtaInvCompact .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covWRevFam) rfl rfl)

theorem covWEtaInv_compact_nonbottom : covWEtaInvCompact ≠ .bot :=
  fun h => CptT.noConfusion h

theorem covWEtaInv_proof_demand_rejected :
    IsPropCT covWRevEnv (.spine 3 []) ∧
    ¬ CTyS covWRevEnv (.spine 4 []) (.spine 3 []) := by
  have hp : IsPropCT covWRevEnv (.spine 3 []) :=
    .spine (m := covUProjPMember) rfl rfl
  refine ⟨hp, ?_⟩
  intro ht
  exact CptT.noConfusion (ctyS_prop_bot hp ht)

/-- The unrestricted finite factor is present. The failed premise is exactly
strict typing of its proof demand at the observed domain code. -/
theorem covWEtaInv_untyped_factor (n : Nat) :
    (∀ u ∈ [.spine 4 []],
      ApproxTKWEta covWRevEnv n [] EnvT.bot covUProjProof u) ∧
    ApproxTKWEta covWRevEnv n [.assumption covUProjP]
      (EnvT.cons (demandT [.spine 4 []]) EnvT.bot) covWEtaInvBody covWEtaInvCompact := by
  constructor
  · intro u hu
    have he : u = .spine 4 [] := List.mem_singleton.mp hu
    subst u
    exact covWEtaInv_arg_observed n [] EnvT.bot
  · exact .appSpine
      (.free (kFreeT_rigid_const covWEtaInv_fam_rigid [])
        (.const _ 5 [] covWEtaInv_fam_rigid covWEtaInv_fam_not_propCtor))
      (.free (kFreeT_bvar covWRevEnv 0) (.bvar (by simp [EnvT.cons, demandT])))

/-- Fully typed inverse substitution, allowing any actually observed domain
code and any finite list of argument demands. -/
def covWEta_typed_inverseAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Prop :=
  ∀ (ρ : EnvT) (D body arg B : Expr Nat) (lD lB : Level) (c b : CptT),
    Nonempty (EnvWfT E) → Nonempty (CtxWfT E n Γ) →
    EnvTypedFinAtT (⟨ApproxTKWEta E n Γ⟩ : CtxModelT E) Γ ρ →
    Nonempty (HasTyT E n Γ D (.sort lD)) →
    Nonempty (HasTyT E n Γ arg D) →
    Nonempty (HasTyT E n (.assumption D :: Γ) B (.sort lB)) →
    Nonempty (HasTyT E n (.assumption D :: Γ) body B) →
    Nonempty (HasTyT E n Γ (instantiate0 arg body) (instantiate0 arg B)) →
    ApproxTKWEta E n Γ ρ (instantiate0 arg body) c →
    ApproxTKWEta E n Γ ρ (instantiate0 arg B) b → CTyS E c b → c ≠ .bot →
    ∃ (a : CptT) (us : List CptT),
      ApproxTKWEta E n Γ ρ D a ∧
      (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, ApproxTKWEta E n Γ ρ arg u) ∧
      ApproxTKWEta E n (.assumption D :: Γ)
        (EnvT.cons (demandT us) ρ) body c

theorem covWEtaInv_no_typed_inverse (n : Nat) :
    ¬ covWEta_typed_inverseAt covWRevEnv n [] := by
  intro h
  apply covWEtaInv_no_typed_factor n
  exact h EnvT.bot covUProjP covWEtaInvBody covUProjProof (.sort .zero)
    .zero (.succ .zero) covWEtaInvCompact .prop
    ⟨covWRevEnv_wf⟩ ⟨.nil⟩ (envTypedFinAtT_nil _ _)
    ⟨covWRevP_ty n []⟩ ⟨covWRevIndex_ty n []⟩ ⟨.sort _ .zero⟩
    ⟨covWEtaInvBody_ty n⟩ ⟨covWEtaInvTarget_ty n⟩
    (covWEtaInv_target_observed n [] EnvT.bot)
    (covWEtaInv_result_type_observed n [] EnvT.bot)
    covWEtaInv_compact_typed covWEtaInv_compact_nonbottom

/-- Every native and semantic premise of the boundary is inhabited. The
source beta and let terms have the same explicit normal reduct. -/
theorem covWEtaInv_inhabited (n : Nat) :
    Nonempty (EnvWfT covWRevEnv) ∧ Nonempty (CtxWfT covWRevEnv n []) ∧
    CovWEtaRealized covWRevEnv n 2 [] EnvT.bot SubstT.id ∧
    EnvTypedFinAtT (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) [] EnvT.bot ∧
    Nonempty (HasTyT covWRevEnv n [] covUProjP (.sort .zero)) ∧
    Nonempty (HasTyT covWRevEnv n [] covUProjProof covUProjP) ∧
    Nonempty (HasTyT covWRevEnv n [.assumption covUProjP] covWEtaInvBody (.sort .zero)) ∧
    Nonempty (HasTyT covWRevEnv n [] covWEtaInvSource (.sort .zero)) ∧
    Nonempty (HasTyT covWRevEnv n [] covWEtaInvLet (.sort .zero)) ∧
    Nonempty (HasTyT covWRevEnv n [] covWEtaInvTarget (.sort .zero)) ∧
    Nonempty (HasTyT covWRevEnv n [] (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT covWRevEnv n [] covWEtaInvSource covWEtaInvTarget (.sort .zero)) ∧
    Nonempty (ConvT covWRevEnv n [] covWEtaInvLet covWEtaInvTarget (.sort .zero)) ∧
    RedR (WhStepCK2 covWRevEnv n) [] covWEtaInvSource covWEtaInvTarget ∧
    RedR (WhStepCK2 covWRevEnv n) [] covWEtaInvLet covWEtaInvTarget ∧
    NormalR (WhStepCK2 covWRevEnv n) [] covWEtaInvTarget ∧
    ApproxTKWEta covWRevEnv n [] EnvT.bot covUProjP (.spine 3 []) ∧
    ApproxTKWEta covWRevEnv n [] EnvT.bot covUProjProof (.spine 4 []) ∧
    ApproxTKWEta covWRevEnv n [] EnvT.bot covWEtaInvTarget covWEtaInvCompact ∧
    ApproxTKWEta covWRevEnv n [] EnvT.bot (.sort .zero) .prop ∧
    CTyS covWRevEnv covWEtaInvCompact .prop ∧ covWEtaInvCompact ≠ .bot ∧
    ¬ covWEta_typed_inverseAt covWRevEnv n [] :=
  ⟨⟨covWRevEnv_wf⟩, ⟨.nil⟩, covWEta_realized_nil _ _ _, envTypedFinAtT_nil _ _,
    ⟨covWRevP_ty n []⟩, ⟨covWRevIndex_ty n []⟩, ⟨covWEtaInvBody_ty n⟩,
    ⟨covWEtaInvSource_ty n⟩, ⟨covWEtaInvLet_ty n⟩, ⟨covWEtaInvTarget_ty n⟩,
    ⟨.sort _ .zero⟩, ⟨covWEtaInv_beta_conv n⟩, ⟨covWEtaInv_let_conv n⟩,
    redR_single (covWEtaInv_beta_step n), redR_single (covWEtaInv_let_step n),
    covWEtaInv_normal n, covWEtaInv_P_observed n [] EnvT.bot,
    covWEtaInv_arg_observed n [] EnvT.bot, covWEtaInv_target_observed n [] EnvT.bot,
    covWEtaInv_result_type_observed n [] EnvT.bot, covWEtaInv_compact_typed,
    covWEtaInv_compact_nonbottom, covWEtaInv_no_typed_inverse n⟩

/-- One information stage contains the result, its actual result-type code,
the actual domain code, and the displayed proof observation. -/
theorem covWEtaInv_same_stage (n : Nat) :
    CovWEtaRealized covWRevEnv n 2 [] EnvT.bot SubstT.id ∧
    ApproxTKWEtaStage covWRevEnv n 2 [] EnvT.bot covUProjP (.spine 3 []) ∧
    ApproxTKWEtaStage covWRevEnv n 2 [] EnvT.bot covUProjProof (.spine 4 []) ∧
    ApproxTKWEtaStage covWRevEnv n 2 [] EnvT.bot covWEtaInvTarget covWEtaInvCompact ∧
    ApproxTKWEtaStage covWRevEnv n 2 [] EnvT.bot (.sort .zero) .prop :=
  ⟨covWEta_realized_nil _ _ _,
    ⟨covWEtaInv_P_observed n [] EnvT.bot, by simp [TypedModelCovTAudit.covTObservationBudget]⟩,
    ⟨covWEtaInv_arg_observed n [] EnvT.bot, by simp [TypedModelCovTAudit.covTObservationBudget]⟩,
    ⟨covWEtaInv_target_observed n [] EnvT.bot, by simp [TypedModelCovTAudit.covTObservationBudget, covWEtaInvCompact]⟩,
    ⟨covWEtaInv_result_type_observed n [] EnvT.bot, by simp [TypedModelCovTAudit.covTObservationBudget]⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_INVERSE_BOUNDARY_ROOTS
#print axioms CovWEtaRigidTerm
#print axioms CovWEtaRigidTerm.lift
#print axioms CovWEtaRigidTerm.foldApps_head
#print axioms CovWEtaClean
#print axioms CovWEtaCleanEnv
#print axioms covWEta_clean_bot
#print axioms covWEta_cleanEnv_bot
#print axioms covWEta_cleanEnv_cons
#print axioms covWEta_clean_appSpine
#print axioms covWEta_raw_clean
#print axioms covWEta_observation_clean
#print axioms covWEtaInvBody
#print axioms covWEtaInvTarget
#print axioms covWEtaInvCompact
#print axioms covWEtaInvSource
#print axioms covWEtaInvLet
#print axioms covWEtaInv_P_demands_bot
#print axioms covWEtaInv_body_clean
#print axioms covWEtaInv_compact_not_clean
#print axioms covWEtaInv_no_typed_factor
#print axioms covWEtaInvBody_ty
#print axioms covWEtaInvLetBody_ty
#print axioms covWEtaInvTarget_ty
#print axioms covWEtaInvSource_ty
#print axioms covWEtaInvLet_ty
#print axioms covWEtaInv_beta_conv
#print axioms covWEtaInv_let_conv
#print axioms covWEtaInv_beta_step
#print axioms covWEtaInv_let_step
#print axioms covWEtaInv_normal
#print axioms covWEtaInv_subst
#print axioms covWEtaInv_P_observed
#print axioms covWEtaInv_arg_observed
#print axioms covWEtaInv_target_observed
#print axioms covWEtaInv_result_type_observed
#print axioms covWEtaInv_compact_typed
#print axioms covWEtaInv_compact_nonbottom
#print axioms covWEtaInv_proof_demand_rejected
#print axioms covWEtaInv_untyped_factor
#print axioms covWEta_typed_inverseAt
#print axioms covWEtaInv_no_typed_inverse
#print axioms covWEtaInv_inhabited
#print axioms covWEtaInv_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_INVERSE_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
