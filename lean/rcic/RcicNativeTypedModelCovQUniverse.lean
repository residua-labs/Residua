import rcic.RcicNativeTypedModelCovPIdentity
import rcic.RcicNativeTypedModelCovPReflection

/-!
# Instantiated universe membership after positive collapse and Pi reflection

The actual native term `k Prop idPiProp` has type `Sort 0`, but its observed
rigid spine is not recognized by the frozen declaration-only `IsPropCT`.
Exact sort realization therefore fails independently of the action quantifier
order. All native premises of the closed control are imported inhabitants.

`CTyCovQ` measures a separate universe-reflection addition by composition.
It adds ordinary body-free neutral spines at the universe code `.prop` only;
positive proposition collapse, bottom inversion and all other atomic target
arms are retained. This compact-only candidate is deliberately broad. Each
positive native control supplies its actual typing and observation separately.
No global soundness, proof-collapse supplier, new core relation or full
polymorphic identity realization is asserted. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovQAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit ReadbackCK2Audit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovYAudit
open TypedModelCovZMeasureAudit TypedModelCovPAudit

variable {E : ResolvedEnv}

/-- The stored declaration ends in a variable. Its actual instantiation at
Prop is invisible to the declaration-only proposition-code predicate. -/
theorem covQ_identity_spine_not_old_prop (us : List CptT) :
    ¬ IsPropCT covZRigidIdEnv (.spine 0 us) := by
  intro h
  cases h with
  | spine hm hs =>
      injection hm with he
      subst he
      change (Expr.bvar 1 : Expr Nat) = .sort .zero at hs
      exact Expr.noConfusion hs

theorem covQ_identity_spine_no_P_universe (reflect : Bool) (us : List CptT) :
    ¬ CTyCovP2 reflect covZRigidIdEnv (.spine 0 us) .prop := by
  intro ht
  rcases ctyCovP2_prop_inv ht with hb | hp
  · exact CptT.noConfusion hb
  · exact covQ_identity_spine_not_old_prop us hp

/-- This no-code result uses only the exact sort leaf and its compact
typing projection. It does not use a compact action or a selected row. -/
theorem covQ_identity_spine_no_P_sort_code (reflect : Bool)
    (Rel : CovPDemandRelation) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (us : List CptT) :
    ∀ a, ¬ HereditaryCovRealizationPAt (CTyCovP2 reflect covZRigidIdEnv) Rel
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      Γ ρ (.sort .zero) (.spine 0 us) a := by
  intro a h
  have he := covP_hereditary_sort_zero_code
    (C2P reflect covZRigidIdEnv).bot_inv n (fun hb => CptT.noConfusion hb) h
  subst a
  exact covQ_identity_spine_no_P_universe reflect us
    (hereditaryCovRealizationPAt_typing h)

/-- The obstructed universe instance is an actual closed native application
in an admitted environment, with native reflexive conversion and observation. -/
theorem covQ_identity_universe_P_control (reflect : Bool)
    (Rel : CovPDemandRelation) (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n []
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.sort .zero)) ∧
    Nonempty (ConvT covZRigidIdEnv n []
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.sort .zero)) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.spine 0 [.bot, .bot]) ∧
    (CptT.spine 0 [.bot, .bot]) ≠ .bot ∧
    ¬ ∃ a, HereditaryCovRealizationPAt (CTyCovP2 reflect covZRigidIdEnv) Rel
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot (.sort .zero) (.spine 0 [.bot, .bot]) a := by
  obtain ⟨⟨ht⟩, _, ho, _⟩ := covP_rigidId_two_application_control n [] EnvT.bot
  exact ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    ho, CptT.noConfusion,
    fun ⟨a, ha⟩ => covQ_identity_spine_no_P_sort_code reflect Rel n [] EnvT.bot
      [.bot, .bot] a ha⟩

/-- The frozen CoreY typing gate cannot use the exact universe code for
this spine, regardless of the supplied endpoints. -/
theorem covQ_identity_spine_no_old_core_prop (R : Readback) (n : Nat)
    (Γ : LCtx) (x y A : Expr Nat) (us : List CptT) :
    ¬ LRSCoreCovY (C2 covZRigidIdEnv) R n Γ x y A (.spine 0 us) .prop := by
  intro h
  have ht := lrSCoreCovY_typing (C2 covZRigidIdEnv) h
  exact covQ_identity_spine_no_P_universe true us
    (ctyCovP2_of_ctyCov2 true _ _ ht)

/-- Composition-only universe reflection. `.prop` is the target universe
code; this addition does not classify it as a positive proposition. -/
def CTyCovQ (E : ResolvedEnv) (u a : CptT) : Prop :=
  CTyCovP2 true E u a ∨
    (a = .prop ∧ ∃ h us, u = .spine h us ∧ NeutralHeadP E h)

theorem ctyCovQ_of_P {u a : CptT} (ht : CTyCovP2 true E u a) : CTyCovQ E u a :=
  Or.inl ht

theorem ctyCovQ_of_C2 {u a : CptT} (ht : CTyCov2 E u a) : CTyCovQ E u a :=
  ctyCovQ_of_P (ctyCovP2_of_ctyCov2 true u a ht)

theorem ctyCovQ_of_S {u a : CptT} (ht : CTyS E u a) : CTyCovQ E u a :=
  ctyCovQ_of_P (ctyCovP2_of_ctyS true ht)

theorem ctyCovQ_bot (E : ResolvedEnv) (a : CptT) : CTyCovQ E .bot a :=
  ctyCovQ_of_P (CTyCovP2.bot a)

theorem ctyCovQ_univNeutral {r : Nat} {us : List CptT} (hh : NeutralHeadP E r) :
    CTyCovQ E (.spine r us) .prop :=
  Or.inr ⟨rfl, r, us, rfl, hh⟩

theorem ctyCovQ_univProp {u : CptT} (hp : IsPropCT E u) : CTyCovQ E u .prop :=
  ctyCovQ_of_P (CTyCovP2.univProp hp)

theorem ctyCovQ_univType {u : CptT} (ht : TyCodeCT u) : CTyCovQ E u .sort :=
  ctyCovQ_of_P (CTyCovP2.univType ht)

theorem ctyCovQ_reflectedPi {r : Nat} {us : List CptT} {a : CptT}
    {g : List (List CptT × CptT)} (hh : NeutralHeadP E r)
    (hnp : ¬ IsPropCTP E (.pi a g)) : CTyCovQ E (.spine r us) (.pi a g) :=
  ctyCovQ_of_P (CTyCovP2.reflectedPi rfl hh hnp)

theorem ctyCovQ_nonprop_iff {u a : CptT} (ha : a ≠ .prop) :
    CTyCovQ E u a ↔ CTyCovP2 true E u a := by
  constructor
  · rintro (ht | ⟨he, _⟩)
    · exact ht
    · exact (ha he).elim
  · exact ctyCovQ_of_P

theorem ctyCovQ_positive_iff {u a : CptT} (hp : IsPropCTP E a) :
    CTyCovQ E u a ↔ CTyCovP2 true E u a := by
  apply ctyCovQ_nonprop_iff
  intro he
  subst a
  exact not_isPropCTP_prop E hp

theorem ctyCovQ_bot_inv {u : CptT} (ht : CTyCovQ E u .bot) : u = .bot :=
  ctyCovP2_bot_inv ((ctyCovQ_nonprop_iff CptT.noConfusion).mp ht)

theorem ctyCovQ_prop_bot {u a : CptT} (hp : IsPropCTP E a)
    (ht : CTyCovQ E u a) : u = .bot :=
  ctyCovP2_prop_bot hp ((ctyCovQ_positive_iff hp).mp ht)

/-- Universe membership now exposes the additional neutral alternative.
It does not supply the frozen old `CovTyping.prop_inv` field. -/
theorem ctyCovQ_prop_inv {u : CptT} (ht : CTyCovQ E u .prop) :
    u = .bot ∨ IsPropCT E u ∨ ∃ r us, u = .spine r us ∧ NeutralHeadP E r := by
  rcases ht with hp | ⟨_, hn⟩
  · rcases ctyCovP2_prop_inv hp with hb | hp
    · exact Or.inl hb
    · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hn)

theorem ctyCovQ_sort_inv {u : CptT} (ht : CTyCovQ E u .sort) :
    u = .bot ∨ TyCodeCT u :=
  ctyCovP2_sort_inv ((ctyCovQ_nonprop_iff CptT.noConfusion).mp ht)

theorem ctyCovQ_lam_inv {u : CptT} {g : List (List CptT × CptT)}
    (ht : CTyCovQ E u (.lam g)) : u = .bot :=
  ctyCovP2_lam_inv ((ctyCovQ_nonprop_iff CptT.noConfusion).mp ht)

theorem ctyCovQ_spine_inv {u : CptT} {r : Nat} {args : List CptT}
    (ht : CTyCovQ E u (.spine r args)) :
    u = .bot ∨ ∃ r' args', u = .spine r' args' :=
  (C2P true E).spine_inv ((ctyCovQ_nonprop_iff CptT.noConfusion).mp ht)

theorem ctyCovQ_pi_inv {u a : CptT} {g : List (List CptT × CptT)}
    (ht : CTyCovQ E u (.pi a g)) :
    u = .bot ∨ (∃ f, u = .lam f ∧ CovLamTyping (CTyCovQ E) a g f) ∨
      ∃ r args, u = .spine r args := by
  rcases (C2P true E).pi_inv ((ctyCovQ_nonprop_iff CptT.noConfusion).mp ht) with
    hb | ⟨f, he, hd, hc⟩ | hs
  · exact Or.inl hb
  · refine Or.inr (Or.inl ⟨f, he, ?_, ?_⟩)
    · intro s hs v hv
      exact ctyCovQ_of_P (hd s hs v hv)
    · intro s hs
      rcases hc s hs with hb | ⟨t, ht, hsub, hout⟩
      · exact Or.inl hb
      · exact Or.inr ⟨t, ht, hsub, ctyCovQ_of_P hout⟩
  · exact Or.inr (Or.inr hs)

/-- A genuine positive proposition code still cannot type a non-bottom
neutral spine under the universe-reflection addition. -/
theorem ctyCovQ_positive_excludes_spine {a : CptT} {r : Nat} {us : List CptT}
    (hp : IsPropCTP E a) : ¬ CTyCovQ E (.spine r us) a :=
  fun ht => CptT.noConfusion (ctyCovQ_prop_bot hp ht)

/-- The frozen universe inversion is genuinely changed. The concrete
native instance below separately certifies why the extra membership is needed. -/
theorem covQ_old_prop_inv_fails :
    ¬ (∀ {u}, CTyCovQ covZRigidIdEnv u .prop →
      u = .bot ∨ IsPropCT covZRigidIdEnv u) := by
  intro h
  rcases h (ctyCovQ_univNeutral (us := [.bot, .bot]) covPIdentity_neutral_head) with
    hb | hp
  · exact CptT.noConfusion hb
  · exact covQ_identity_spine_not_old_prop [.bot, .bot] hp

/-- Exact sort realization at the extended universe typing is a supplier
for the displayed code. The demand relation is arbitrary and unused at a leaf. -/
theorem covQ_hereditary_sort_zero (Rel : CovPDemandRelation) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) {c : CptT} (ht : CTyCovQ E c .prop) :
    HereditaryCovRealizationPAt (CTyCovQ E) Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.sort .zero) c .prop := by
  rw [HereditaryCovRealizationPAt.eq_def]
  refine ⟨ht, Or.inr ⟨.sort .zero, .refl _, normalR_sortCK2 Γ .zero, ?_⟩⟩
  change ApproxTK E n Γ ρ (.sort .zero) .prop
  simpa only [sortCode_zero] using approxTK_sort_code E n Γ ρ .zero

/-- The fully instantiated native identity result now has hereditary
realization at `.prop`; this supplies no code for the polymorphic head. -/
theorem covQ_identity_universe_realized (Rel : CovPDemandRelation) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv) Rel
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      Γ ρ (.sort .zero) (.spine 0 [.bot, .bot]) .prop :=
  covQ_hereditary_sort_zero Rel n Γ ρ
    (ctyCovQ_univNeutral covPIdentity_neutral_head)

/-- Repaired hereditary realization cannot be paired at the same code
with the old CoreY universe gate. This names the remaining integration debt. -/
theorem covQ_identity_universe_no_old_joint (Rel : CovPDemandRelation) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (x y : Expr Nat) :
    ¬ ∃ a, LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n
      Γ x y (.sort .zero) (.spine 0 [.bot, .bot]) a ∧
      HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv) Rel
        (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
        Γ ρ (.sort .zero) (.spine 0 [.bot, .bot]) a := by
  rintro ⟨a, hc, hh⟩
  have he := covP_hereditary_sort_zero_code ctyCovQ_bot_inv n
    (fun hb => CptT.noConfusion hb) hh
  subst a
  exact covQ_identity_spine_no_old_core_prop _ n Γ x y (.sort .zero) [.bot, .bot] hc

/-- All native/model premises of the newly positive universe control are
inhabited. The old same-code joint target remains explicitly false. -/
theorem covQ_identity_universe_control (Rel : CovPDemandRelation) (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n []
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.sort .zero)) ∧
    Nonempty (ConvT covZRigidIdEnv n []
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.sort .zero)) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.spine 0 [.bot, .bot]) ∧
    (CptT.spine 0 [.bot, .bot]) ≠ .bot ∧
    HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv) Rel
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot (.sort .zero) (.spine 0 [.bot, .bot]) .prop ∧
    (¬ ∃ a, LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n []
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.sort .zero) (.spine 0 [.bot, .bot]) a ∧
      HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv) Rel
        (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
        [] EnvT.bot (.sort .zero) (.spine 0 [.bot, .bot]) a) := by
  obtain ⟨⟨ht⟩, _, ho, _⟩ := covP_rigidId_two_application_control n [] EnvT.bot
  exact ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    ho, CptT.noConfusion, covQ_identity_universe_realized Rel n [] EnvT.bot,
    covQ_identity_universe_no_old_joint Rel n [] EnvT.bot _ _⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_UNIVERSE_ROOTS
#print axioms covQ_identity_spine_not_old_prop
#print axioms covQ_identity_spine_no_P_universe
#print axioms covQ_identity_spine_no_P_sort_code
#print axioms covQ_identity_universe_P_control
#print axioms covQ_identity_spine_no_old_core_prop
#print axioms CTyCovQ
#print axioms ctyCovQ_of_P
#print axioms ctyCovQ_of_C2
#print axioms ctyCovQ_of_S
#print axioms ctyCovQ_bot
#print axioms ctyCovQ_univNeutral
#print axioms ctyCovQ_univProp
#print axioms ctyCovQ_univType
#print axioms ctyCovQ_reflectedPi
#print axioms ctyCovQ_nonprop_iff
#print axioms ctyCovQ_positive_iff
#print axioms ctyCovQ_bot_inv
#print axioms ctyCovQ_prop_bot
#print axioms ctyCovQ_prop_inv
#print axioms ctyCovQ_sort_inv
#print axioms ctyCovQ_lam_inv
#print axioms ctyCovQ_spine_inv
#print axioms ctyCovQ_pi_inv
#print axioms ctyCovQ_positive_excludes_spine
#print axioms covQ_old_prop_inv_fails
#print axioms covQ_hereditary_sort_zero
#print axioms covQ_identity_universe_realized
#print axioms covQ_identity_universe_no_old_joint
#print axioms covQ_identity_universe_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_UNIVERSE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovQAudit
