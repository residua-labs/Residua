import rcic.RcicNativeTypedModelCovWEtaControls
import rcic.RcicNativeTypedModelCovWEtaInverseBoundary

/-!
# The existing nonbottom proof-demand control distinguishes native proofs

This is a measurement of the landed `ApproxTKWEta` relation.  The admitted
`covSProofFnEnv` contains `p : True` and `f : True → Prop`. Native proof
irrelevance gives `p ≡ True.intro`, and application congruence gives
`f p ≡ f True.intro`. The old full spine observation of `f p` is absent
from `f True.intro`, even allowing every finite eta derivation.

The invariant below only tracks omission of a rigid reference. It does not
claim normalization, native type injectivity, or completeness of the old
observation grammar. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelAudit.TypingFin
open TypedModelCovPAudit TypedModelCovRAudit TypedModelCovSAudit
open TypedModelCovUAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A rigid application expression omitting the chosen reference. -/
inductive CovWIrrelOldAvoidTerm (bad : Nat) (E : ResolvedEnv) : Expr Nat → Prop
  | bvar (i : Nat) : CovWIrrelOldAvoidTerm bad E (.bvar i)
  | const (r : Nat) (ls : List Level) (hr : RigidConst E r) (hne : r ≠ bad) :
      CovWIrrelOldAvoidTerm bad E (.const r ls)
  | app {f x : Expr Nat}
      (hf : CovWIrrelOldAvoidTerm bad E f) (hx : CovWIrrelOldAvoidTerm bad E x) :
      CovWIrrelOldAvoidTerm bad E (.app f x)

theorem CovWIrrelOldAvoidTerm.lift {bad : Nat} {E : ResolvedEnv} {e : Expr Nat}
    (h : CovWIrrelOldAvoidTerm bad E e) (k d : Nat) :
    CovWIrrelOldAvoidTerm bad E (lift k d e) := by
  induction h with
  | bvar i =>
      change CovWIrrelOldAvoidTerm bad E (if k ≤ i then .bvar (i + d) else .bvar i)
      split <;> exact .bvar _
  | const r ls hr hn => exact .const r ls hr hn
  | app _ _ ihf ihx => exact .app ihf ihx

theorem CovWIrrelOldAvoidTerm.foldApps_head {bad : Nat} {E : ResolvedEnv}
    {f : Expr Nat} {xs : List (Expr Nat)}
    (h : CovWIrrelOldAvoidTerm bad E (foldApps f xs)) :
    CovWIrrelOldAvoidTerm bad E f := by
  induction xs generalizing f with
  | nil => exact h
  | cons x xs ih =>
      have hfx := ih h
      cases hfx with
      | app hf _ => exact hf

/-- A graph preserves absence of the reference whenever its inputs do. -/
def CovWIrrelOldClean (bad : Nat) : CptT → Prop
  | .spine r args => r ≠ bad ∧ ∀ u ∈ args, CovWIrrelOldClean bad u
  | .lam g => ∀ s ∈ g,
      (∀ u ∈ s.1, CovWIrrelOldClean bad u) → CovWIrrelOldClean bad s.2
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

def CovWIrrelOldCleanEnv (bad : Nat) (ρ : EnvT) : Prop :=
  ∀ i c, ρ i c → CovWIrrelOldClean bad c

theorem covWIrrelOld_clean_bot (bad : Nat) : CovWIrrelOldClean bad .bot := by
  simp [CovWIrrelOldClean]

theorem covWIrrelOld_cleanEnv_bot (bad : Nat) : CovWIrrelOldCleanEnv bad EnvT.bot := by
  intro i c hc
  change c = .bot at hc
  subst c
  exact covWIrrelOld_clean_bot bad

theorem covWIrrelOld_cleanEnv_cons {bad : Nat} {ρ : EnvT} {us : List CptT}
    (hρ : CovWIrrelOldCleanEnv bad ρ)
    (hus : ∀ u ∈ us, CovWIrrelOldClean bad u) :
    CovWIrrelOldCleanEnv bad (EnvT.cons (demandT us) ρ) := by
  intro i c hc
  cases i with
  | zero => exact hus c hc
  | succ i => exact hρ i c hc

theorem covWIrrelOld_clean_appSpine {bad r : Nat} {args : List CptT} {u : CptT}
    (hf : CovWIrrelOldClean bad (.spine r args)) (hu : CovWIrrelOldClean bad u) :
    CovWIrrelOldClean bad (.spine r (args ++ [u])) := by
  rw [CovWIrrelOldClean] at hf ⊢
  refine ⟨hf.1, ?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hf.2 v hv
  · have he : v = u := List.mem_singleton.mp hv
    subst v
    exact hu

/-- The complete landed raw grammar preserves the omitted-reference invariant. -/
theorem covWIrrelOld_raw_clean {bad : Nat} {E : ResolvedEnv}
    {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTW E ρ e c) (he : CovWIrrelOldAvoidTerm bad E e)
    (hρ : CovWIrrelOldCleanEnv bad ρ) : CovWIrrelOldClean bad c := by
  induction h with
  | bot => exact covWIrrelOld_clean_bot bad
  | bvar hv => exact hρ _ _ hv
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app _ hs _ ihf ihx =>
      cases he with
      | app hf hx =>
          have hh := ihf hf hρ
          rw [CovWIrrelOldClean] at hh
          exact hh _ hs (fun u hu => ihx u hu hx hρ)
  | const _ _ _ _ _ =>
      cases he with
      | const r ls hr hn =>
          rw [CovWIrrelOldClean]
          exact ⟨hn, fun u hu => nomatch hu⟩
  | delta hd _ _ =>
      cases he with
      | const _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | @recursor ρ w ls hnp up uf c hp hf hb ih =>
      cases he with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | appSpine _ _ ihf ihx =>
      cases he with
      | app hf hx => exact covWIrrelOld_clean_appSpine (ihf hf hρ) (ihx hx hρ)
  | letE => cases he
  | lit => cases he

/-- This induction covers recursive eta, with its actual fresh-application premise. -/
theorem covWIrrelOld_observation_clean {bad : Nat} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKWEta E n Γ ρ e c) (he : CovWIrrelOldAvoidTerm bad E e)
    (hρ : CovWIrrelOldCleanEnv bad ρ) : CovWIrrelOldClean bad c := by
  induction h with
  | bot => exact covWIrrelOld_clean_bot bad
  | free _ h => exact covWIrrelOld_raw_clean h he hρ
  | pi => cases he
  | lam => cases he
  | app _ hs _ ihf ihx =>
      cases he with
      | app hf hx =>
          have hh := ihf hf hρ
          rw [CovWIrrelOldClean] at hh
          exact hh _ hs (fun u hu => ihx u hu hx hρ)
  | appSpine _ _ ihf ihx =>
      cases he with
      | app hf hx => exact covWIrrelOld_clean_appSpine (ihf hf hρ) (ihx hx hρ)
  | delta hd _ _ =>
      cases he with
      | const _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | letE => cases he
  | lit => cases he
  | iota w _ _ _ =>
      have hh := CovWIrrelOldAvoidTerm.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ _ =>
      have hh := CovWIrrelOldAvoidTerm.foldApps_head he
      cases hh with
      | const _ _ hr _ => exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta _ _ _ _ _ ihD ihb =>
      rw [CovWIrrelOldClean]
      intro s hs hus
      exact ihb s hs (.app (he.lift 0 1) (.bvar 0))
        (covWIrrelOld_cleanEnv_cons hρ hus)

theorem covWIrrelProofDemand_intro_rigid : RigidConst covSProofFnEnv 1 := by
  intro m hm
  have he : m = trueIntroMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

/-- The actual comparison term contains the admitted True constructor. -/
theorem covWIrrelProofDemand_intro_avoids :
    CovWIrrelOldAvoidTerm 3 covSProofFnEnv (.app (.const 4 []) (.const 1 [])) :=
  .app (.const 4 [] (neutralHeadP_rigid covSProofFn_neutral) (by decide))
    (.const 1 [] covWIrrelProofDemand_intro_rigid (by decide))

theorem covWIrrelProofDemand_full_not_clean :
    ¬ CovWIrrelOldClean 3 (.spine 4 [.spine 3 []]) := by
  intro h
  rw [CovWIrrelOldClean] at h
  have hp := h.2 (.spine 3 []) (by simp)
  rw [CovWIrrelOldClean] at hp
  exact hp.1 rfl

/-- No old eta observation of `f True.intro` retains the reference of `p`. -/
theorem covWIrrelProofDemand_intro_full_excluded (n : Nat) (Γ : LCtx) :
    ¬ ApproxTKWEta covSProofFnEnv n Γ EnvT.bot
      (.app (.const 4 []) (.const 1 [])) (.spine 4 [.spine 3 []]) := by
  intro h
  exact covWIrrelProofDemand_full_not_clean
    (covWIrrelOld_observation_clean h covWIrrelProofDemand_intro_avoids
      (covWIrrelOld_cleanEnv_bot 3))

/-- The distinguishing result is itself a strict demand at the observed
result type `Prop`; the erased field is the input proof observation. -/
theorem covWIrrelProofDemand_full_typed :
    CTyS covSProofFnEnv (.spine 4 [.spine 3 []]) .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covSProofFnMember) rfl rfl)

/-- Restricting transport to result compacts typed at the actual result
type observation still does not preserve this old proof-argument spine. -/
theorem covWIrrelProofDemand_old_typed_transport_no (n : Nat) (Γ : LCtx) :
    ¬ (∀ c, CTyS covSProofFnEnv c .prop →
      ApproxTKWEta covSProofFnEnv n Γ EnvT.bot (.app (.const 4 []) (.const 3 [])) c →
      ApproxTKWEta covSProofFnEnv n Γ EnvT.bot (.app (.const 4 []) (.const 1 [])) c) := by
  intro h
  exact covWIrrelProofDemand_intro_full_excluded n Γ
    (h _ covWIrrelProofDemand_full_typed
      (covWEta_proof_demand_observed n Γ EnvT.bot))

/-- All native premises and the distinguishing old observation are inhabited.
The result conversion uses application congruence with the supplied native irr. -/
theorem covWIrrelProofDemand_old_irr_violation (n : Nat) :
    Nonempty (EnvWfT covSProofFnEnv) ∧ Nonempty (CtxWfT covSProofFnEnv n []) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.sort .zero)) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 1 []))
      (.sort .zero)) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.sort .zero)) ∧
    ApproxTKWEta covSProofFnEnv n [] EnvT.bot (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) ∧
    ¬ ApproxTKWEta covSProofFnEnv n [] EnvT.bot (.app (.const 4 []) (.const 1 []))
      (.spine 4 [.spine 3 []]) := by
  obtain ⟨hW, hΓ, hT, hf, hp, hq, hi, hfp, hfq, hfc, _⟩ :=
    covSProofFn_nonbottom_demand_control n
  exact ⟨hW, hΓ, hT, hp, hq, hi, hfp, hfq, hfc,
    covWEta_proof_demand_observed n [] EnvT.bot,
    covWIrrelProofDemand_intro_full_excluded n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_PROOF_DEMAND_ROOTS
#print axioms CovWIrrelOldAvoidTerm
#print axioms CovWIrrelOldAvoidTerm.lift
#print axioms CovWIrrelOldAvoidTerm.foldApps_head
#print axioms CovWIrrelOldClean
#print axioms CovWIrrelOldCleanEnv
#print axioms covWIrrelOld_clean_bot
#print axioms covWIrrelOld_cleanEnv_bot
#print axioms covWIrrelOld_cleanEnv_cons
#print axioms covWIrrelOld_clean_appSpine
#print axioms covWIrrelOld_raw_clean
#print axioms covWIrrelOld_observation_clean
#print axioms covWIrrelProofDemand_intro_rigid
#print axioms covWIrrelProofDemand_intro_avoids
#print axioms covWIrrelProofDemand_full_not_clean
#print axioms covWIrrelProofDemand_intro_full_excluded
#print axioms covWIrrelProofDemand_full_typed
#print axioms covWIrrelProofDemand_old_typed_transport_no
#print axioms covWIrrelProofDemand_old_irr_violation
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_PROOF_DEMAND_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
