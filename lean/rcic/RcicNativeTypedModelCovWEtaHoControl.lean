import rcic.RcicNativeTypedModelCovWEtaAligned
import rcic.RcicNativeTypedModelCovVRestriction

/-!
# Ineligible proposition recursion stays bottom-only after typed eta

This is an induction over the new grammar, including its eta constructor.
It does not project new observations into the old grammar. Eta preserves a
constant application-spine head, so any nonbottom eta row at an excluded
head would contain a strictly smaller observation at that same excluded
head. The unchanged old computation-source checks handle iota and K.

The higher-order divergent type retains its actual native typing, closing
realizer, bottom observation and lack of a normal reduct. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit FamModelLRSAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelW6IotaAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit

private theorem covWEta_headConst_lift (e : Expr Nat) (cutoff amount : Nat) :
    headConst (lift cutoff amount e) = headConst e := by
  induction e with
  | bvar i =>
      by_cases hi : cutoff ≤ i <;> simp [lift, hi, headConst]
  | sort => rfl
  | const => rfl
  | app f x ihf _ => exact ihf
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit => rfl

private theorem covWEta_old_ineligible_head {E : ResolvedEnv} {ρ : EnvT}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef) :
    ∀ (e : Expr Nat) (c : CptT), ApproxTN E ρ e c →
      headConst e = some w.recRef → c = .bot := by
  intro e
  induction e with
  | bvar i => intro c h hh; cases hh
  | sort l => intro c h hh; cases hh
  | const r ls =>
      intro c h hh
      exact covV_ineligible_prop_const_only_bot w hP hnF hnP
        (Option.some.inj hh) h
  | app f x ihf _ =>
      intro c h hh
      exact covV_app_only_bot (fun u hu => ihf u hu hh) h
  | lam A b _ _ => intro c h hh; cases hh
  | pi A B _ _ => intro c h hh; cases hh
  | letE A v b _ _ _ => intro c h hh; cases hh
  | lit t => intro c h hh; cases hh

/-- The exclusion is proved for the new observation derivation itself.
It is stable under eta because eta's body has the same constant head. -/
theorem covWEta_ineligible_prop_head_only_bot {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef)
    (h : ApproxTKWEta E n Γ ρ e c)
    (hh : headConst e = some w.recRef) : c = .bot := by
  revert hh
  induction h with
  | bot => intro _; rfl
  | free _ h =>
      intro hh
      exact covWEta_old_ineligible_head w hP hnF hnP _ _ (approxTW_forget h) hh
  | pi => intro hh; cases hh
  | lam => intro hh; cases hh
  | app _ _ _ ihf _ =>
      intro hh
      cases ihf hh
  | appSpine _ _ ihf _ =>
      intro hh
      cases ihf hh
  | @delta Γ ρ r ls m b c hd _ _ =>
      intro hh
      have hr : r = w.recRef := Option.some.inj hh
      exact (not_deltaConst_of_recursor w (hr ▸ hd)).elim
  | letE => intro hh; cases hh
  | lit => intro hh; cases hh
  | iota _ hsource _ _ =>
      intro hh
      exact covWEta_old_ineligible_head w hP hnF hnP _ _ hsource hh
  | recursorPropK _ _ _ _ _ _ hsource _ _ =>
      intro hh
      exact covWEta_old_ineligible_head w hP hnF hnP _ _ hsource hh
  | eta _ _ _ hne _ _ ihb =>
      intro hh
      obtain ⟨s, hs, hnb⟩ := hne
      exact (hnb (ihb s hs (by
        simpa only [headConst, covWEta_headConst_lift] using hh))).elim

/-- Every finite spine of every ineligible proposition recursor is still
bottom-only, with an actual new-model bottom observation. -/
theorem covWEta_ineligible_prop_spine {E : ResolvedEnv}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) (ls : List Level) (args : List (Expr Nat)) :
    ApproxTKWEta E n Γ ρ (foldApps (.const w.recRef ls) args) .bot ∧
    ∀ c, ApproxTKWEta E n Γ ρ (foldApps (.const w.recRef ls) args) c → c = .bot := by
  refine ⟨.bot _ _ _, ?_⟩
  intro c h
  exact covWEta_ineligible_prop_head_only_bot w hP hnF hnP h
    (by simp only [headConst_foldApps, headConst])

theorem covWEtaHo_type_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta covUHoEnv n Γ ρ covUHoType c) : c = .bot :=
  covWEta_ineligible_prop_head_only_bot covUHoWitness
    (covVHo_rec_family_prop covUHoWitness rfl)
    covUHo_not_kFreeRec covUHo_not_kProjRec h rfl

/-- Actual supply and exact classification hold for arbitrary contexts and
valuations; no global model-soundness premise is used. -/
theorem covWEtaHo_type_observation_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT) :
    ApproxTKWEta covUHoEnv n Γ ρ covUHoType c ↔ c = .bot := by
  constructor
  · exact covWEtaHo_type_only_bot
  · intro hc
    subst c
    exact .bot _ _ _

theorem covWEtaHo_repaired_instance (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    CovWEtaRealized covUHoEnv n 1 [] EnvT.bot SubstT.id ∧
    Nonempty (HasTyT covUHoEnv n [] covUHoType (.sort (.succ .zero))) ∧
    ApproxTKWEtaStage covUHoEnv n 1 [] EnvT.bot covUHoType .bot ∧
    (∀ c, ApproxTKWEta covUHoEnv n [] EnvT.bot covUHoType c → c = .bot) ∧
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, covWEta_realized_nil covUHoEnv n 1,
    ⟨covUHoType_hasTy n []⟩, ⟨.bot _ _ _, by simp [covTObservationBudget]⟩,
    (fun _ h => covWEtaHo_type_only_bot h), covUHoType_no_normal_head n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_HO_CONTROL_ROOTS
#print axioms covWEta_ineligible_prop_head_only_bot
#print axioms covWEta_ineligible_prop_spine
#print axioms covWEtaHo_type_only_bot
#print axioms covWEtaHo_type_observation_iff
#print axioms covWEtaHo_repaired_instance
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_HO_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
