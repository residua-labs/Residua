import rcic.RcicNativeTypedModelCovZOrder

/-!
# Raising codes: the typing gate and exact realization are distinct walls

There is no landed order on CptT. The only order laws used here are explicit
parameters. Raising a bottom Nat-arrow domain to the zero-constructor code
loses the rigid C2 gate. This refutes bare upward Core transport, not a
version already assuming the target gate or actual target observation.

The Eq proposition control has both C2 gates and both Core relations, but
raising prop to sort loses exact hereditary realization. It is therefore
not a counterexample to Core monotonicity; it refutes upward transport of
the complete Core/H/H synthesis target. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKControlAudit
open TypedModelKFailureAudit TypedModelCovRelAudit TypedModelCovRelEscapeAudit
open TypedModelCovNormCov2Audit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovYAudit TypedModelCovYEtaAudit

def covZBottomNatCode : CptT := .pi .bot [([], .spine 0 [])]

def covZWrongNatCode : CptT := .pi (.spine 1 []) [([], .spine 0 [])]

theorem covZBottomNatCode_not_prop : ¬ IsPropCT natEnvU covZBottomNatCode := by
  intro h
  cases h with
  | pi _ hout =>
      exact not_isPropCT_natEnvU_nat_spine []
        (hout ([], .spine 0 []) (List.mem_singleton.mpr rfl))

theorem approxTK_covZBottomNatCode (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covZBottomNatCode := by
  refine ApproxTK.pi (.bot _ _ _) ?_ ?_
  · intro row hr u hu
    obtain rfl := List.mem_singleton.mp hr
    exact (List.not_mem_nil _ hu).elim
  · intro row hr
    obtain rfl := List.mem_singleton.mp hr
    exact ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)

theorem covZ_natSucc_bottom_code_typed :
    (C2 natEnvU).ty (.spine 2 []) covZBottomNatCode :=
  ctyCov2_natSucc_spine
    (approxTK_forget (approxTK_covZBottomNatCode 0 [] EnvT.bot))
    covZBottomNatCode_not_prop

theorem covZ_natSucc_bottom_coverage :
    CovYActionCoverage (C2 natEnvU) (.spine 2 []) .bot [([], .spine 0 [])] := by
  intro ds out ha hd
  apply covY_natSucc_uniform_coverage ds out ha
  intro u hu
  rw [(C2 natEnvU).bot_inv (hd u hu)]
  exact (C2 natEnvU).bot _

theorem covZ_natSucc_bottom_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomNatCode := by
  rw [covZBottomNatCode, lrSCoreCovY_pi_iff]
  refine ⟨covZ_natSucc_bottom_code_typed,
    Or.inr ⟨.const 0 [], .const 0 [], .refl _, covZ_natSucc_bottom_coverage, ?_⟩⟩
  intro ds out ha row hr hs N N' hN hN' hc hd
  apply lrSCoreCovY_pi_action (C2 natEnvU) (readbackLaws_whStepCK2 natEnvU n)
    (covY_natSucc_related n Γ) ha hr hs N N' hN hN' hc
  intro u hu
  have he := (C2 natEnvU).bot_inv
    (lrSCoreCovY_typing (C2 natEnvU) (hd u hu))
  rw [he]
  exact lrSCoreCovY_bot (C2 natEnvU) Γ N N' (.const 0 []) (.spine 0 [])

theorem covZ_natSucc_bottom_realized (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomNatCode := by
  rw [covZBottomNatCode, HereditaryCovRealizationYAt.eq_def]
  refine ⟨covZ_natSucc_bottom_code_typed,
    Or.inr ⟨.const 0 [], .const 0 [], .refl _, covZ_natSucc_bottom_coverage, ?_⟩⟩
  intro ds out ha hne row hr hs N N' hN hN' hc hd
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨?_, covY_nat_hereditary_at n (.assumption (.const 0 []) :: Γ)
    (EnvT.cons (demandT ds) ρ) out hs.2,
    covY_nat_hereditary_at n Γ ρ out hs.2,
    covY_nat_hereditary_at n Γ ρ out hs.2⟩
  intro u hu
  rw [(C2 natEnvU).bot_inv (lrSCoreCovY_typing (C2 natEnvU) (hd u hu))]
  exact hereditaryCovRealizationYAt_bot (C2 natEnvU)
    (ctxModelT_approxTK natEnvU n) (WhStepCK2 natEnvU n) n Γ ρ (.const 0 []) .bot

theorem not_covZ_natSucc_wrong_code_typed :
    ¬ (C2 natEnvU).ty (.spine 2 []) covZWrongNatCode := by
  intro h
  change CTyCov2 natEnvU (.spine 2 [])
    (.pi (.spine 1 []) [([], .spine 0 [])]) at h
  rw [CTyCov2] at h
  rcases h with ⟨_, m, ls, hm, _, hls, _, T, hT, ho⟩
  change some natSuccMember = some m at hm
  cases Option.some.inj hm
  change ls.length = 0 at hls
  have hnil := List.length_eq_zero.mp hls
  subst ls
  change some (.pi (.const 0 []) (.const 0 [])) = some T at hT
  cases Option.some.inj hT
  rcases approxT_pi_inv ho with hb | ⟨d, g, he, hd, _⟩
  · cases hb
  · cases he
    rcases approxT_rigid_const_inv rigidConst_natEnvU_nat hd with hb | he
    · cases hb
    · cases he

theorem not_covZ_natSucc_wrong_related (n : Nat) (Γ : LCtx) :
    ¬ LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZWrongNatCode :=
  fun h => not_covZ_natSucc_wrong_code_typed (lrSCoreCovY_typing (C2 natEnvU) h)

/-- The bare upward counterexample has the same inhabited native and
two-sided environment guards as the stronger row-deletion control. Its
source is an actual observed, related and realized non-bottom compact. -/
theorem covZ_natSucc_domain_raise_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot ∧
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) covZBottomNatCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomNatCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomNatCode ∧
    (¬ (C2 natEnvU).ty (.spine 2 []) covZWrongNatCode) ∧
    (.spine 2 [] : CptT) ≠ .bot := by
  obtain ⟨hw, hΓ, ht, ht', he, he', ho, ho', _⟩ :=
    covZ_natSucc_row_deletion_control n
  exact ⟨hw, hΓ, ht, ht', he, he', ho, ho', approxTK_covZBottomNatCode n [] EnvT.bot,
    covZ_natSucc_bottom_related n [], covZ_natSucc_bottom_realized n [] EnvT.bot,
    not_covZ_natSucc_wrong_code_typed, fun h => CptT.noConfusion h⟩

/-- Only the displayed order comparisons are used. The target gate fails,
so this theorem intentionally makes no claim about gated upward transport. -/
theorem not_covZ_core_upward_of_domain_raise (n : Nat)
    (le : CptT → CptT → Prop)
    (hbot : le .bot (.spine 1 []))
    (hdom : ∀ d d', le d d' →
      le (.pi d [([], .spine 0 [])]) (.pi d' [([], .spine 0 [])])) :
    ¬ (∀ {a b : CptT}, le a b →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
        (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) a →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
        (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) b) := by
  intro h
  exact not_covZ_natSucc_wrong_related n []
    (h (hdom .bot (.spine 1 []) hbot) (covZ_natSucc_bottom_related n []))

/-- The Eq example keeps both gates and both relations, including actual
native typings, non-bottom observations and both hereditary environment
guards. Only realization at the raised code is false. -/
theorem covZ_eq_prop_sort_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (.sort .zero)) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (.sort .zero)) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
    EnvTypedCovYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot ∧
    EnvTypedCovYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot ∧
    (C2 eqEnvT).ty (.pi .bot []) .prop ∧ (C2 eqEnvT).ty (.pi .bot []) .sort ∧
    LRSCoreCovY (C2 eqEnvT) (WhStepCK2 eqEnvT n) n eqGapCtx
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop ∧
    LRSCoreCovY (C2 eqEnvT) (WhStepCK2 eqEnvT n) n eqGapCtx
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .sort ∧
    HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) .prop ∧
    (¬ HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) .sort) ∧
    (.pi .bot [] : CptT) ≠ .bot := by
  obtain ⟨hw, hΓ, ht, ho, he, hrs, hn, hrp, hp, hnb⟩ :=
    covY_code_anchor_control (C2 eqEnvT) (C2_includesS eqEnvT) n
  have gates := covY_idPiProp_two_code_gates (C2 eqEnvT) (C2_includesS eqEnvT)
  exact ⟨hw, hΓ, ht, ht, ho, ho, he, he, gates.2, gates.1, hrp, hrs, hp, hn, hnb⟩

/-- Even though the Core relation holds at both codes, exact hereditary
realization cannot be raised from prop to sort. -/
theorem not_covZ_realization_upward_prop_sort (n : Nat)
    (le : CptT → CptT → Prop) (hps : le .prop .sort) :
    ¬ (∀ {a b : CptT}, le a b →
      (C2 eqEnvT).ty (.pi .bot []) b →
      LRSCoreCovY (C2 eqEnvT) (WhStepCK2 eqEnvT n) n eqGapCtx
        idPiProp idPiProp (.sort .zero) (.pi .bot []) b →
      HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) a →
      HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) b) := by
  intro h
  exact not_covY_idPiProp_realized_at_sort_code (C2 eqEnvT) n eqGapCtx EnvT.bot
    (h hps (covY_idPiProp_two_code_gates (C2 eqEnvT) (C2_includesS eqEnvT)).1
      (covY_idPiProp_two_relation_codes (C2 eqEnvT) (C2_includesS eqEnvT) n).1
      (covY_idPiProp_realized_at_prop_code (C2 eqEnvT) (C2_includesS eqEnvT)
        n eqGapCtx EnvT.bot))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_ORDER_UP_ROOTS
#print axioms covZBottomNatCode
#print axioms covZWrongNatCode
#print axioms covZBottomNatCode_not_prop
#print axioms approxTK_covZBottomNatCode
#print axioms covZ_natSucc_bottom_code_typed
#print axioms covZ_natSucc_bottom_coverage
#print axioms covZ_natSucc_bottom_related
#print axioms covZ_natSucc_bottom_realized
#print axioms not_covZ_natSucc_wrong_code_typed
#print axioms not_covZ_natSucc_wrong_related
#print axioms covZ_natSucc_domain_raise_control
#print axioms not_covZ_core_upward_of_domain_raise
#print axioms covZ_eq_prop_sort_control
#print axioms not_covZ_realization_upward_prop_sort
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_ORDER_UP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit
