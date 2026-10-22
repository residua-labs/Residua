import rcic.RcicAnnLR3Positive

/-!
# A typed contextual head strategy with positive K priority

The K rule ignores its proof major and uses the old-stage frame.  Every
other route carries positive `ApartA3` evidence at its source.  Application
heads and recursor majors recurse through this new strategy, so K steps
inside those positions are represented in the relation as well.

The old evaluator appears only at primitive leaves.  A positive leaf
witness rules out an old recursive application/major choice that could
conflict with the new strategy.  Determinism and old typed-conversion
soundness are proved, not fields of the interface.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- A primitive application arm, before recursive major evaluation. -/
inductive ActiveA3 (E : ResolvedEnvA) (I : IotaIfaceA) (f a : ExprA) : Prop
  | iota (b : ExprA) (hs : structPosA E f = false) (hi : I.fn (.app f a) = some b)
  | unit (mn : ExprA) (hs : structPosA E f = false) (hi : I.fn (.app f a) = none)
      (hr : recAtMajorA E f = true) (hu : unitMinorA E f = some mn)
  | structArm (b : ExprA) (hs : structPosA E f = true) (hb : structArmA E f a = some b)

/-- The old evaluator is consulted only where its choice is primitive.
The application case has a positive neutral prefix and an active primitive
arm, so it cannot hide a recursive old-major choice. -/
inductive OldLeafA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : ExprA → Prop
  | beta (A : ExprA) (u : Level) (body arg : ExprA) :
      OldLeafA3 E I n Γ (.app (.lam A u body) arg)
  | zeta (A v b : ExprA) : OldLeafA3 E I n Γ (.letE A v b)
  | varE (i : Nat) : OldLeafA3 E I n Γ (.bvar i)
  | constE (r : Nat) (ls : List Level) : OldLeafA3 E I n Γ (.const r ls)
  | litE (t : Nat) : OldLeafA3 E I n Γ (.lit t)
  | application {f a : ExprA} (hf : NeutralA3 E I n Γ f) (ha : ActiveA3 E I f a) :
      OldLeafA3 E I n Γ (.app f a)

theorem OldLeafA3.app_normal {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {f a : ExprA} (h : OldLeafA3 E I n Γ (.app f a)) : NormalA3 E I n Γ f := by
  cases h with
  | beta A u body arg => exact .lam A u body
  | application hf _ => exact .neutral hf

theorem OldLeafA3.no_major {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {f a : ExprA} (h : OldLeafA3 E I n Γ (.app f a))
    (hs : structPosA E f = false) (hi : I.fn (.app f a) = none)
    (hr : recAtMajorA E f = true) (hu : unitMinorA E f = none) : False := by
  cases h with
  | beta A u body arg =>
      rw [recAtMajorA_not_lam] at hr
      exact Bool.noConfusion hr
  | application _ ha =>
      cases ha with
      | iota _ _ hi' => exact Option.noConfusion (hi'.symm.trans hi)
      | unit _ _ _ _ hu' => exact Option.noConfusion (hu'.symm.trans hu)
      | structArm _ hs' _ => exact Bool.noConfusion (hs'.symm.trans hs)

/-- The operational skeleton, used to prove strategy facts independently
of the choice of typing derivations. -/
inductive HeadRuleA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    ExprA → ExprA → Prop
  | primitive (a b : ExprA) (hl : OldLeafA3 E I n Γ a) (ha : ApartA3 E I n Γ a)
      (hs : hStepFnA E I.fn Γ a = some b) : HeadRuleA3 E I n Γ a b
  | app (f f' a : ExprA) (ha : ApartA3 E I n Γ (.app f a))
      (h : HeadRuleA3 E I n Γ f f') : HeadRuleA3 E I n Γ (.app f a) (.app f' a)
  | major (f a a' : ExprA) (ha : ApartA3 E I n Γ (.app f a))
      (hf : NeutralA3 E I n Γ f) (hs : structPosA E f = false)
      (hi : I.fn (.app f a) = none) (hr : recAtMajorA E f = true)
      (hu : unitMinorA E f = none) (h : HeadRuleA3 E I n Γ a a') :
      HeadRuleA3 E I n Γ (.app f a) (.app f a')
  | k (a b : ExprA) (s : KStage.Shape) (hw : Nonempty (KStage.Frame E I n Γ s))
      (hs : s.source = a) (hr : s.minor = b) : HeadRuleA3 E I n Γ a b

/-- Positive normal syntax excludes every new head route. -/
theorem HeadRuleA3.not_normal {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {a b : ExprA} (h : HeadRuleA3 E I n Γ a b) : ¬ NormalA3 E I n Γ a := by
  induction h with
  | primitive a b _ _ hs =>
      intro hn
      exact Option.noConfusion (hn.old_none.symm.trans hs)
  | app f f' a _ _ ih =>
      intro hn
      cases hn with
      | neutral hn =>
          cases hn with
          | appIdle hf _ _ _ _ => exact ih (.neutral hf)
          | appMajor hf _ _ _ _ _ _ => exact ih (.neutral hf)
  | major f a a' _ _ _ _ hr _ _ ih =>
      intro hn
      cases hn with
      | neutral hn =>
          cases hn with
          | appIdle _ _ _ _ hr' => exact Bool.noConfusion (hr'.symm.trans hr)
          | appMajor _ _ _ _ _ _ hx => exact ih hx
  | k a b s hw hs _ =>
      intro hn
      obtain ⟨w⟩ := hw
      exact hn.apart.excludes w hs

theorem headRuleA3_deterministic {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {a b c : ExprA} (h : HeadRuleA3 E I n Γ a b)
    (h' : HeadRuleA3 E I n Γ a c) : b = c := by
  induction h generalizing c with
  | primitive a b hl ha hs =>
      cases h' with
      | primitive _ _ _ _ hs' => exact Option.some.inj (hs.symm.trans hs')
      | app f f' a ha' hf => exact (hf.not_normal hl.app_normal).elim
      | major f a a' ha' hf hst hi hr hu hx => exact (hl.no_major hst hi hr hu).elim
      | k _ _ s hw he _ =>
          obtain ⟨w⟩ := hw
          exact (ha.excludes w he).elim
  | app f f' a ha hf ih =>
      cases h' with
      | primitive _ _ hl _ _ => exact (hf.not_normal hl.app_normal).elim
      | app _ f'' _ _ hf' => exact congrArg (fun g => ExprA.app g a) (ih hf')
      | major _ _ a' _ hnf _ _ _ _ _ => exact (hf.not_normal (.neutral hnf)).elim
      | k _ _ s hw he _ =>
          obtain ⟨w⟩ := hw
          exact (ha.excludes w he).elim
  | major f a a' ha hnf hs hi hr hu hx ih =>
      cases h' with
      | primitive _ _ hl _ _ => exact (hl.no_major hs hi hr hu).elim
      | app _ f' _ _ hf => exact (hf.not_normal (.neutral hnf)).elim
      | major _ _ a'' _ _ _ _ _ _ hx' => exact congrArg (ExprA.app f) (ih hx')
      | k _ _ s hw he _ =>
          obtain ⟨w⟩ := hw
          exact (ha.excludes w he).elim
  | k a b s hw he hb =>
      obtain ⟨w⟩ := hw
      cases h' with
      | primitive _ _ _ ha _ => exact (ha.excludes w he).elim
      | app _ _ _ ha _ => exact (ha.excludes w he).elim
      | major _ _ _ ha _ _ _ _ _ _ => exact (ha.excludes w he).elim
      | k _ _ t ht he' hc =>
          obtain ⟨v⟩ := ht
          exact hb.symm.trans ((w.minor_eq_of_source_eq v (he.trans he'.symm)).trans hc)

/-- A step of an application either already has a positively normal
function, or is exactly a step of that function.  The K case uses the
derived neutral-prefix theorem for its supplied target. -/
theorem headRuleA3_app_inversion {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hR : IotaRecHeadA E I) {Γ : LCtxA} {f a b : ExprA}
    (h : HeadRuleA3 E I n Γ (.app f a) b) :
    NormalA3 E I n Γ f ∨
      ∃ f', HeadRuleA3 E I n Γ f f' ∧ b = .app f' a := by
  cases h with
  | primitive _ _ hl _ _ => exact .inl hl.app_normal
  | app _ f' _ _ hf => exact .inr ⟨f', hf, rfl⟩
  | major _ _ _ _ hf _ _ _ _ _ => exact .inl (.neutral hf)
  | k _ _ s hw hs _ =>
      obtain ⟨w⟩ := hw
      change ExprA.app s.prefix s.major = ExprA.app f a at hs
      have he := (ExprA.app.inj hs).1
      rw [← he]
      exact .inl (.neutral (target_prefix_neutral hR Γ w.target))

/-- Typed rules for the same strategy.  Their conversion proof is derived
below from old primitive reduction, dependent application congruence, and
the old-stage K soundness theorem. -/
inductive HeadA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    ExprA → ExprA → ExprA → Prop
  | primitive (a b T : ExprA) (hl : OldLeafA3 E I n Γ a) (ha : ApartA3 E I n Γ a)
      (h : Nonempty (TyHRedA E I n Γ a b T)) : HeadA3 E I n Γ a b T
  | app (f f' a A B T₀ : ExprA) (u v : Level)
      (h : HeadA3 E I n Γ f f' T₀) (hc : TyConvA E I n Γ T₀ (.pi A u B v))
      (hat : HasTyA E I n Γ a A) (ha : ApartA3 E I n Γ (.app f a)) :
      HeadA3 E I n Γ (.app f a) (.app f' a) (instantiate0A a B)
  | major (f a a' A B T₀ : ExprA) (u v : Level)
      (h : HeadA3 E I n Γ a a' T₀) (hc : TyConvA E I n Γ T₀ A)
      (hft : HasTyA E I n Γ f (.pi A u B v))
      (ha : ApartA3 E I n Γ (.app f a)) (hf : NeutralA3 E I n Γ f)
      (hs : structPosA E f = false) (hi : I.fn (.app f a) = none)
      (hr : recAtMajorA E f = true) (hu : unitMinorA E f = none) :
      HeadA3 E I n Γ (.app f a) (.app f a') (instantiate0A a B)
  | convert (a b T U : ExprA) (h : HeadA3 E I n Γ a b T) (hc : TyConvA E I n Γ T U) :
      HeadA3 E I n Γ a b U
  | k (s : KStage.Shape) (h : Nonempty (KStage.Frame E I n Γ s)) :
      HeadA3 E I n Γ s.source s.minor s.resultType

theorem HeadA3.rule {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {a b T : ExprA} (h : HeadA3 E I n Γ a b T) : HeadRuleA3 E I n Γ a b := by
  induction h with
  | primitive a b T hl ha h =>
      obtain ⟨h⟩ := h
      exact .primitive a b hl ha (tyHRedA_hStep h)
  | app f f' a A B T₀ u v _ _ _ ha ih => exact .app f f' a ha ih
  | major f a a' A B T₀ u v _ _ _ ha hf hs hi hr hu ih =>
      exact .major f a a' ha hf hs hi hr hu ih
  | convert a b T U _ _ ih => exact ih
  | k s h => exact .k s.source s.minor s h rfl rfl

theorem headA3_deterministic {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {a b c T U : ExprA} (h : HeadA3 E I n Γ a b T) (h' : HeadA3 E I n Γ a c U) : b = c :=
  headRuleA3_deterministic h.rule h'.rule

theorem normalA3_no_head {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {a b T : ExprA} (hn : NormalA3 E I n Γ a) (h : HeadA3 E I n Γ a b T) : False :=
  h.rule.not_normal hn

theorem HeadA3.conv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {a b T : ExprA}
    (h : HeadA3 E I n Γ a b T) : Nonempty (ConvA E I n Γ a b T) := by
  induction h with
  | primitive a b T _ _ h =>
      obtain ⟨h⟩ := h
      exact ⟨tyHRedA_conv h⟩
  | app f f' a A B T₀ u v _ hc hat _ ih =>
      obtain ⟨c⟩ := ih
      exact ⟨KStage.appCongr hE hI hR hIS hΓ (convA_of_tyConvA c hc)
        (.refl Γ a A hat)⟩
  | major f a a' A B T₀ u v _ hc hft _ _ _ _ _ _ ih =>
      obtain ⟨c⟩ := ih
      exact ⟨KStage.appCongr hE hI hR hIS hΓ (.refl Γ f _ hft)
        (convA_of_tyConvA c hc)⟩
  | convert a b T U _ hc ih =>
      obtain ⟨c⟩ := ih
      exact ⟨convA_of_tyConvA c hc⟩
  | k s h =>
      obtain ⟨w⟩ := h
      exact w.sound hE hI hR hIS hΓ

theorem HeadA3.leftTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {a b T : ExprA}
    (h : HeadA3 E I n Γ a b T) : Nonempty (HasTyA E I n Γ a T) := by
  obtain ⟨hc⟩ := h.conv hE hI hR hIS hΓ
  exact ⟨convA_hasTy_left hE hI hR hIS hΓ hc⟩

theorem HeadA3.rightTyped {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {a b T : ExprA}
    (h : HeadA3 E I n Γ a b T) : Nonempty (HasTyA E I n Γ b T) := by
  obtain ⟨hc⟩ := h.conv hE hI hR hIS hΓ
  exact ⟨convA_hasTy_right hE hI hR hIS hΓ hc⟩

#print axioms ActiveA3
#print axioms OldLeafA3
#print axioms OldLeafA3.app_normal
#print axioms OldLeafA3.no_major
#print axioms HeadRuleA3
#print axioms HeadRuleA3.not_normal
#print axioms headRuleA3_deterministic
#print axioms headRuleA3_app_inversion
#print axioms HeadA3
#print axioms HeadA3.rule
#print axioms headA3_deterministic
#print axioms normalA3_no_head
#print axioms HeadA3.conv
#print axioms HeadA3.leftTyped
#print axioms HeadA3.rightTyped

end Rcic.Declarative.Ann.LR3
