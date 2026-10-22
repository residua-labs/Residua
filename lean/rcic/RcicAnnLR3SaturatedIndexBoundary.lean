import rcic.RcicAnnLR3EqHead
import rcic.RcicAnnLR3NormalDemand

/-!
# The static normality gap at an inhabited saturated Eq call

The assumption and let contexts have the same source call. Static
`ApartA3` ignores the context. A certificate at the assumption call would
therefore give one at the let call, contradicting the supplied let K frame.
The assumption context is well formed and closed by an explicit typed
substitution, and its canonical erased index guard fails under `TableWF`.

This does not turn erased nonconversion into annotated nonconversion.
In particular, no exclusion of every annotated K frame is asserted.
Instead, the final chain inversion identifies that exact missing obligation:
any supplied terminal chain from this call must start with an actual K frame.
The same exclusion is proved below for every structurally eligible target,
using only stored layout, independently of a frame or its conversion guard.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.SaturatedIndexBoundary

open Rcic.Declarative Rcic.Syn EqLargeFixture RouteCKContext

/-- The first static certificate language has no contextual premises. -/
theorem staticApartRecontext {E : ResolvedEnvA} {I J : IotaIfaceA}
    {n m : Nat} {Γ Δ : LCtxA} {a : ExprA}
    (h : ApartA3 E I n Γ a) : ApartA3 E J m Δ a := by
  cases h with
  | nonApp h => exact .nonApp h
  | nonConstHead h => exact .nonConstHead h
  | noGroup hh hg => exact .noGroup hh hg
  | short hh hm hn => exact .short hh hm hn
  | long hh hm hn => exact .long hh hm hn
  | layout hh hg hb => exact .layout hh hg hb

private theorem sourceRecRef {s : KStage.Shape} {e : ExprA} {r : Nat} {ls : List Level}
    (he : s.source = e) (hh : (appsSpineA e).1 = .const r ls) : s.recRef = r := by
  have h := (congrArg (fun a => (appsSpineA a).1) he).trans hh
  simp only [KStage.Shape.source, KStage.Shape.prefix, appsSpineA, appsSpineA_foldAppsA] at h
  exact (ExprA.const.inj h).1

private theorem targetGroup {E : ResolvedEnvA} {s : KStage.Shape}
    (w : KStage.Target E s) {e : ExprA} {r : Nat} {ls : List Level}
    (he : s.source = e) (hh : (appsSpineA e).1 = .const r ls) :
    iotaGroupA E r (r - 1) = some s.group := by
  have hr := sourceRecRef he hh
  have hc : s.ctorRef = r - 1 := by
    have hn := w.ctorNext
    omega
  simpa only [hr, hc] using w.group

private theorem targetArity {E : ResolvedEnvA} {s : KStage.Shape}
    (w : KStage.Target E s) {e : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (he : s.source = e) (hh : (appsSpineA e).1 = .const r ls)
    (hm : E.members r = some m) : (appsSpineA e).2.length = piCountA m.mtypeA := by
  have hr := sourceRecRef he hh
  have hres := (iotaGroupA_some w.group).1
  rw [hr] at hres
  have hmem := Option.some.inj (hres.symm.trans hm)
  have hcount : (appsSpineA s.source).2.length = piCountA s.group.recM.mtypeA := by
    simpa only [KStage.Shape.source, KStage.Shape.prefix, appsSpineA,
      appsSpineA_foldAppsA, List.nil_append, List.length_append,
      List.length_cons, List.length_nil] using w.arity
  simpa only [he, hmem] using hcount

/-- A full eligible target is outside the static certificate language,
whether or not its indices admit any annotated conversion. -/
theorem targetNotStaticApart {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {s : KStage.Shape} (w : KStage.Target E s) :
    ¬ ApartA3 E I n Γ s.source := by
  intro h
  cases h with
  | nonApp h => exact h.not_app s.prefix s.major rfl
  | nonConstHead h =>
      have hh : (appsSpineA s.source).1 = .const s.recRef s.recLevels := by
        simp only [KStage.Shape.source, KStage.Shape.prefix, appsSpineA, appsSpineA_foldAppsA]
      exact h.not_const _ _ hh
  | noGroup hh hg => exact Option.noConfusion ((targetGroup w rfl hh).symm.trans hg)
  | short hh hm hn => have hc := targetArity w rfl hh hm; omega
  | long hh hm hn => have hc := targetArity w rfl hh hm; omega
  | layout hh hg hbad =>
      have hgroup := Option.some.inj (hg.symm.trans (targetGroup w rfl hh))
      subst hgroup
      cases hbad with
      | zeroMinors h => have hc := w.oneConstructor; omega
      | manyMinors h => have hc := w.oneConstructor; omega
      | fewerParams h => have hc := w.noFields; omega
      | hasFields h => have hc := w.noFields; omega
      | otherTail h => rw [w.propFamily] at h; exact Bool.noConfusion h

/-- Consequently the current positive normality grammar cannot certify any
saturated target source. This is a statement about this specific grammar. -/
theorem normalA3_target_source_false {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {s : KStage.Shape} (w : KStage.Target E s) :
    ¬ NormalA3 E I n Γ s.source :=
  fun h => targetNotStaticApart w h.apart

/-- The existing let K frame refutes static apartness of this syntax in
every context, without asserting a K frame in any other context. -/
theorem contextCallNotStaticApart (Γ : LCtxA) :
    ¬ ApartA3 env (iotaIfaceA env) 0 Γ contextCall := by
  intro h
  have hl : ApartA3 env (iotaIfaceA env) 0 letContext contextCall :=
    staticApartRecontext h
  obtain ⟨w⟩ := KEqPositive.letFrame
  exact hl.excludes w rfl

theorem contextCallNotNormal (Γ : LCtxA) :
    ¬ NormalA3 env (iotaIfaceA env) 0 Γ contextCall :=
  fun h => contextCallNotStaticApart Γ h.apart

theorem assumptionCallOldNone :
    hStepFnA env (iotaIfaceA env).fn assumptionContext contextCall = none := by
  decide

/-- A head witness at a source without static apartness must supply a K
frame. Its declared indices are left unrestricted, as the actual rule does. -/
theorem headFrameOfNoStaticApart {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {a b T : ExprA}
    (ha : ¬ ApartA3 E I n Γ a) (h : HeadA3 E I n Γ a b T) :
    ∃ s, Nonempty (KStage.Frame E I n Γ s) ∧ s.source = a ∧ s.minor = b := by
  cases h.rule with
  | primitive _ _ _ hap _ => exact (ha hap).elim
  | app _ _ _ hap _ => exact (ha hap).elim
  | major _ _ _ hap _ _ _ _ _ _ => exact (ha hap).elim
  | k _ _ s hs hsa hsb => exact ⟨s, hs, hsa, hsb⟩

/-- Every current head step at a saturated target supplies an actual K
frame for the same source. The original shape's unstored fields are not
identified with the supplied frame's fields. -/
theorem targetHeadRequiresFrame {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {s : KStage.Shape} {b T : ExprA}
    (w : KStage.Target E s) (h : HeadA3 E I n Γ s.source b T) :
    ∃ t, Nonempty (KStage.Frame E I n Γ t) ∧ t.source = s.source ∧ t.minor = b :=
  headFrameOfNoStaticApart (targetNotStaticApart w) h

/-- Terminal reduction of a saturated target in the current head layer
must start by supplying a K frame. -/
theorem targetWhTyRequiresFrame {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {s : KStage.Shape} {N : ExprA}
    (w : KStage.Target E s)
    (h : WhTyA3 E I n (contextualHeadLayerA3 E I n) Γ s.source N) :
    ∃ t, Nonempty (KStage.Frame E I n Γ t) ∧ t.source = s.source := by
  rcases whTyA3_headDemand h with hn | ⟨u, b, hs⟩
  · exact (normalA3_target_source_false w hn).elim
  · obtain ⟨t, ht, he, _⟩ := targetHeadRequiresFrame w hs
    exact ⟨t, ht, he⟩

/-- Semantic relatedness at a sort retains that same K-frame demand. -/
theorem targetRelatedAtSortRequiresFrame {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {s : KStage.Shape} {b : ExprA} {l : Level}
    {ρ₀ : Nat → Nat} {k : Nat} (w : KStage.Target E s)
    (h : LRRelA3 E I n (contextualHeadLayerA3 E I n) ρ₀ k Γ (.sort l) s.source b) :
    ∃ t, Nonempty (KStage.Frame E I n Γ t) ∧ t.source = s.source := by
  obtain ⟨N, hN⟩ := (lrRelA3_sort_normalDemand h).1
  exact targetWhTyRequiresFrame w hN

theorem contextCallHeadRequiresFrame {Γ : LCtxA} {b T : ExprA}
    (h : HeadA3 env (iotaIfaceA env) 0 Γ contextCall b T) :
    ∃ s, Nonempty (KStage.Frame env (iotaIfaceA env) 0 Γ s) ∧
      s.source = contextCall ∧ s.minor = b :=
  headFrameOfNoStaticApart (contextCallNotStaticApart Γ) h

/-- An actual terminal chain cannot be reflexive here. Its first step
therefore exposes an actual arbitrary K frame in the assumption context. -/
theorem assumptionCallWhTyRequiresFrame {N : ExprA}
    (h : WhTyA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0)
      assumptionContext contextCall N) :
    ∃ s, Nonempty (KStage.Frame env (iotaIfaceA env) 0 assumptionContext s) ∧
      s.source = contextCall := by
  rcases whTyA3_headDemand h with hn | ⟨u, b, hs⟩
  · exact (contextCallNotNormal assumptionContext hn).elim
  ·
      obtain ⟨s, hw, he, _⟩ := contextCallHeadRequiresFrame hs
      exact ⟨s, hw, he⟩

/-- This implication is a measured demand, not a frame or semantic supplier. -/
theorem assumptionCallRelatedAtSortRequiresFrame {ρ₀ : Nat → Nat} {k : Nat}
    {l : Level} {b : ExprA}
    (h : LRRelA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) ρ₀ k
      assumptionContext (.sort l) contextCall b) :
    ∃ s, Nonempty (KStage.Frame env (iotaIfaceA env) 0 assumptionContext s) ∧
      s.source = contextCall := by
  obtain ⟨N, hN⟩ := (lrRelA3_sort_normalDemand h).1
  exact assumptionCallWhTyRequiresFrame hN

/-- All premises of the static-certificate gap are supplied: admitted Eq,
typed saturated call, closing substitution, old head stopped, and an apart
canonical erased index pair under an inhabited well-formed table. -/
theorem inhabited_saturated_static_boundary :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 assumptionContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext contextCall (.sort one)) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution assumptionContext) ∧
    NormalA3 env (iotaIfaceA env) 0 assumptionContext (.bvar 0) ∧
    TableWF [] ∧ ¬ assumptionErasedGuard [] ∧
    hStepFnA env (iotaIfaceA env).fn assumptionContext contextCall = none ∧
    ¬ ApartA3 env (iotaIfaceA env) 0 assumptionContext contextCall ∧
    ¬ NormalA3 env (iotaIfaceA env) 0 assumptionContext contextCall :=
  ⟨erase_env, wf, ⟨assumptionContextWf⟩,
    contextCallTyped assumptionContextWf rfl rfl,
    ⟨assumptionClosingSubstitution⟩, .neutral (.bvar 0 rfl), emptyTable_wf,
    assumptionErasedGuard_fails emptyTable_wf, assumptionCallOldNone,
    contextCallNotStaticApart assumptionContext, contextCallNotNormal assumptionContext⟩

#print axioms staticApartRecontext
#print axioms targetNotStaticApart
#print axioms normalA3_target_source_false
#print axioms contextCallNotStaticApart
#print axioms contextCallNotNormal
#print axioms assumptionCallOldNone
#print axioms headFrameOfNoStaticApart
#print axioms targetHeadRequiresFrame
#print axioms targetWhTyRequiresFrame
#print axioms targetRelatedAtSortRequiresFrame
#print axioms contextCallHeadRequiresFrame
#print axioms assumptionCallWhTyRequiresFrame
#print axioms assumptionCallRelatedAtSortRequiresFrame
#print axioms inhabited_saturated_static_boundary

end Rcic.Declarative.Ann.LR3.SaturatedIndexBoundary
