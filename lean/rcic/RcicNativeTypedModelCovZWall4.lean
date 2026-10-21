import rcic.RcicNativeTypedModelCovZContract
import rcic.RcicNativeTypedModelCovYEtaCoverage
import rcic.RcicNativeTypedModelCovYTransport

/-!
# A relevant function alias at a constructed hereditary code

The domain in this module may be any native type reading back to
`Prop → Prop`. Its raw model observation is never assumed. The inner code
contains an empty-demand row, and the outer code keeps the actual function
demand. These proofs measure the relevant-position shape of the separate
Wall-4 fixture without copying that fixture or assuming a global escape law.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit TypedModelKAudit TypedModelKControlAudit
open TypedModelCovRelAudit TypedModelCovXAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit

variable {E : ResolvedEnv} {n : Nat}

/-- The relevant domain has a uniform empty-demand proposition row. -/
def covZPropArrowCode : CptT := .pi .prop [([], .prop)]

/-- The outer code retains the observed relevant function demand. -/
def covZRelevantAppCode : CptT :=
  .pi covZPropArrowCode [([.lam [([.bot], .pi .bot [])]], .prop)]

private theorem covZ_prop_probe_ctyS (E : ResolvedEnv) :
    CTyS E (.pi .bot []) .prop := by
  rw [CTyS]
  exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))

private theorem covZ_relevant_demand_ctyS (E : ResolvedEnv) :
    CTyS E (.lam [([.bot], .pi .bot [])]) covZPropArrowCode := by
  change CTyS E (.lam [([.bot], .pi .bot [])]) (.pi .prop [([], .prop)])
  rw [CTyS]
  refine Or.inr ⟨[([.bot], .pi .bot [])], rfl,
    not_isPropCT_pi_singleton [] (not_isPropCT_prop E), ?_, ?_, ?_⟩
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs row hr _
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hr
    exact covZ_prop_probe_ctyS E
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact Or.inr ⟨([], .prop), List.mem_singleton_self _,
      fun _ hu => (List.not_mem_nil _ hu).elim⟩

/-- The inner function demand is typed at the empty-demand domain code.
The code's tested row need not repeat the value row's automatic bottom. -/
theorem covZ_relevant_demand_typing (C : CovTyping E) (hS : CovTypingIncludesS C) :
    C.ty (.lam [([.bot], .pi .bot [])]) covZPropArrowCode :=
  hS _ _ (covZ_relevant_demand_ctyS E)

/-- The actual outer lambda observation meets the constructed Pi gate. -/
theorem covZ_relevant_app_typing (C : CovTyping E) (hS : CovTypingIncludesS C) :
    C.ty (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])])
      covZRelevantAppCode := by
  apply hS
  apply ctyS_lam_singleton (not_isPropCT_prop E)
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact covZ_relevant_demand_ctyS E
  · exact covZ_prop_probe_ctyS E

/-- At an alias of `Prop → Prop`, every related demand realizes this
particular constructed code. Both codomain indices and the binder body are
checked at actual sort observations in their respective contexts. -/
theorem hereditaryCovRealizationYAt_relevant_domain (C : CovTyping E)
    (n : Nat) {Γ : LCtx} (ρ : EnvT) {D x y : Expr Nat} {c : CptT}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hc : LRSCoreCovY C (WhStepCK2 E n) n Γ x y D c covZPropArrowCode) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ D c covZPropArrowCode := by
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨lrSCoreCovY_typing C hc, Or.inr ⟨.sort .zero, .sort .zero,
    hr, lrSCoreCovY_pi_coverage C hc, ?_⟩⟩
  intro ds out ha hnb row hrow hsel N N' hN hN' hconv hd
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := Γ) (ρ := ρ) (.refl _)
      (by simpa only [sortCode_zero] using lrSCoreCovY_typing C (hd u hu))
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := .assumption (.sort .zero) :: Γ)
      (ρ := EnvT.cons (demandT ds) ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := Γ) (ρ := ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := Γ) (ρ := ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)

/-- Exact-code hereditary escape for the relevant outer function pattern.
The alias domain is visited through its readback when an actual related
function demand is tested, with no raw domain observation premise. -/
theorem hereditaryCovRealizationYAt_relevant_app (C : CovTyping E)
    (n : Nat) {Γ : LCtx} (ρ : EnvT) {D x y : Expr Nat} {c : CptT}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hc : LRSCoreCovY C (WhStepCK2 E n) n Γ x y (.pi D (.sort .zero))
      c covZRelevantAppCode) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi D (.sort .zero)) c covZRelevantAppCode := by
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨lrSCoreCovY_typing C hc, Or.inr ⟨D, .sort .zero,
    .refl _, lrSCoreCovY_pi_coverage C hc, ?_⟩⟩
  intro ds out ha hnb row hrow hsel N N' hN hN' hconv hd
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hereditaryCovRealizationYAt_relevant_domain C n ρ hr (hd u hu)
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := .assumption D :: Γ) (ρ := EnvT.cons (demandT ds) ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := Γ) (ρ := ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)

  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := Γ) (ρ := ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)

private theorem covZ_apply_prop_beta (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (Q N : Expr Nat) :
    RedR (WhStepCK2 E n) Γ
      (.app (.lam (.pi (.sort .zero) (.sort .zero))
        (.app (.bvar 0) (lift 0 1 Q))) N) (.app N Q) := by
  have hi : instantiate0 N (.app (.bvar 0) (lift 0 1 Q)) = .app N Q := by
    change Expr.app N (instantiate0 N (lift 0 1 Q)) = Expr.app N Q
    exact congrArg (fun z => Expr.app N z) (instantiate_lift_id 0 N Q)
  have hs := (readbackLaws_whStepCK2 E n).beta Γ
    (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)) N
  rw [hi] at hs
  exact .step hs (.refl _)

/-- Applying a related relevant function demand to an actual proposition
supplies the outer function edge. The proof uses its inner applicative
clause and relation-side beta expansion; it needs no model beta expansion.
The native type of the demanded function is aligned by readback invariance. -/
theorem lrSCoreCovY_relevant_app (C : CovTyping E) (hS : CovTypingIncludesS C)
    (hW : EnvWfT E) (n : Nat) {Γ : LCtx} {D Q : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hQ : HasTyT E n Γ Q (.sort .zero)) :
    LRSCoreCovY C (WhStepCK2 E n) n Γ
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])])
      covZRelevantAppCode := by
  have hgate := covZ_relevant_app_typing C hS
  rw [LRSCoreCovY.eq_def]
  refine ⟨hgate, Or.inr ⟨D, .sort .zero, .refl _,
    covYActionCoverage_lam_of_typing C hgate, ?_⟩⟩
  intro ds out ha row hrow hsel N N' hN hN' hconv hd
  obtain rfl := List.mem_singleton.mp hrow
  cases ha with
  | bot =>
      exact ⟨lrSCoreCovY_bot C _ _ _ _ _, lrSCoreCovY_bot C _ _ _ _ _⟩
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      have hu : (.lam [([.bot], .pi .bot [])] : CptT) ∈ ds := by
        rcases approxT_bvar_inv
          (hx (.lam [([.bot], .pi .bot [])]) (List.mem_singleton_self _)) with hb | hm
        · exact CptT.noConfusion hb
        · exact hm
      have hinner := (lrSCoreCovY_type_readback_iff C (readbackLaws_whStepCK2 E n)
        (detR_whStepCK2 hW) hr (.lam [([.bot], .pi .bot [])]) covZPropArrowCode).mp
          (hd _ hu)
      have haInner : CovXCompactAction E (.lam [([.bot], .pi .bot [])])
          [.bot] (.pi .bot []) := by
        refine .app (List.mem_singleton_self _) ?_
        intro u humem
        obtain rfl := List.mem_singleton.mp humem
        exact .bot _ _
      have hselInner : CovYSelectedRow C [.bot] (.pi .bot []) ([], .prop) :=
        ⟨fun _ hm => (List.not_mem_nil _ hm).elim, hS _ _ (covZ_prop_probe_ctyS E)⟩
      have hout := (lrSCoreCovY_pi_action C (readbackLaws_whStepCK2 E n)
        hinner haInner (List.mem_singleton_self _) hselInner Q Q hQ hQ
          ⟨.refl _ _ _ hQ⟩ (fun u humem => by
            obtain rfl := List.mem_singleton.mp humem
            exact lrSCoreCovY_bot C _ _ _ _ _)).1
      have hexpand := lrSCoreCovY_expand_red_both C (readbackLaws_whStepCK2 E n)
        .prop (covZ_apply_prop_beta E n Γ Q N)
          (covZ_apply_prop_beta E n Γ Q N') hout
      exact ⟨hexpand, hexpand⟩

/-- Both endpoints receive the same explicitly constructed hereditary
code at every two valuations, on an actual non-bottom function compact. -/
theorem covZ_relevant_app_joint (C : CovTyping E) (hS : CovTypingIncludesS C)
    (hW : EnvWfT E) (n : Nat) {Γ : LCtx} (ρ ρ' : EnvT) {D Q : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hQ : HasTyT E n Γ Q (.sort .zero)) :
    CovZJointCodeAt C (ctxModelT_approxTK E n) (WhStepCK2 E n)
      n Γ ρ ρ'
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])])
      covZRelevantAppCode := by
  have hc := lrSCoreCovY_relevant_app C hS hW n hr hQ
  exact ⟨hc, hereditaryCovRealizationYAt_relevant_app C n ρ hr hc,
    hereditaryCovRealizationYAt_relevant_app C n ρ' hr hc⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_WALL4_ROOTS
#print axioms covZPropArrowCode
#print axioms covZRelevantAppCode
#print axioms covZ_relevant_demand_typing
#print axioms covZ_relevant_app_typing
#print axioms hereditaryCovRealizationYAt_relevant_domain
#print axioms hereditaryCovRealizationYAt_relevant_app
#print axioms lrSCoreCovY_relevant_app
#print axioms covZ_relevant_app_joint
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_WALL4_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit
