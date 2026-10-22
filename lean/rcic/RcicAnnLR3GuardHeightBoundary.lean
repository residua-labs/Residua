import rcic.RcicAnnLR3Core
import rcic.RcicAnnLR3EqHead

/-!
# An inhabited non-decreasing height at a K guard

The outer equality is over `A = Sort 0 : Sort 1`; its motive returns
`Sort 1`. Its actual index is an inner equality recursor returning a
proposition. The supplied index conversion really contains proof
irrelevance on an equality over that same `A`, followed by application
congruence and old iota. The occurrence is recorded on the conversion
derivation itself.

Thus the equality carrier's typing height is 1 and the outer Type-sort
clause asks for its results at height 1. This refutes the blanket numerical
claim that every guard carrier has strictly lower height.

The immediate proposition consumed by `irr` still has height 0. Its
proposition key might be supplied syntactically; the witnessed occurrence
does not prove that minimal proposition-key coherence needs height 1.
In particular, this is not a refutation of a height argument whose actual
coherence requests have first been restricted to that smaller fragment.

All frame, environment, context, typing and closing-substitution premises
are supplied. This does not refute coherence or a larger mutual measure.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.GuardHeightBoundary

open Rcic.Declarative EqLargeFixture

/-- An explicit `irr` occurrence whose proposition is equality over `A`.
Only the conversion constructors needed by the witnessed guard are
traversed; this is an occurrence certificate, not a conversion decision. -/
def UsesEqCarrierIrr (A : ExprA) : {Γ : LCtxA} → {a b T : ExprA} →
    ConvA env (iotaIfaceA env) 0 Γ a b T → Prop
  | _, _, _, _, .irr _ P _ _ _ _ _ =>
      ∃ x y, P = foldAppsA (.const 63 []) [A, x, y]
  | _, _, _, _, .symm _ _ _ _ h => UsesEqCarrierIrr A h
  | _, _, _, _, .trans _ _ _ _ _ h h' => UsesEqCarrierIrr A h ∨ UsesEqCarrierIrr A h'
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ hf ha _ _ =>
      UsesEqCarrierIrr A hf ∨ UsesEqCarrierIrr A ha
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h _ _ _ _ hc =>
      UsesEqCarrierIrr A h ∨ UsesEqCarrierIrr A hc
  | _, _, _, _, _ => False

private def applyE {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) :=
  convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface hΓ
    (KStage.appCongr closed liftIface (iotaFnA_recHead env) substIface hΓ
      (.refl Γ f _ hf) (.refl Γ a D ha))

private def propVar {Γ : LCtxA} : HasTyA env (iotaIfaceA env) 0
    (.assumption (.sort .zero) :: Γ) (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) one rfl (.sort _ .zero)

abbrev innerTail (a : ExprA) : ExprA :=
  .pi (eqAt parameter a) .zero (.sort one) two

abbrev innerBody : ExprA := .lam (eqAt parameter (.bvar 0)) .zero (.sort .zero)
abbrev innerMotive : ExprA := .lam (.sort .zero) one innerBody
abbrev innerMotiveTy : ExprA :=
  .pi (.sort .zero) one (innerTail (.bvar 0)) (.imax .zero two)
abbrev innerMotiveAt (a p : ExprA) : ExprA := .app (.app innerMotive a) p

private def tailLamTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ
      (.lam (eqAt parameter a) .zero (.sort .zero)) (innerTail a) :=
  .lam Γ (eqAt parameter a) .zero (.sort .zero) (.sort one) two
    (eqTyped hΓ parameterTyped ha) (.sort _ one) (.sort _ .zero)

def innerMotiveTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ innerMotive innerMotiveTy :=
  .lam Γ (.sort .zero) one innerBody (innerTail (.bvar 0)) (.imax .zero two)
    (.sort Γ .zero)
    (.pi _ (eqAt parameter (.bvar 0)) .zero (.sort one) two
      (eqTyped (.assumption hΓ (.sort Γ .zero)) parameterTyped propVar) (.sort _ one))
    (tailLamTyped (.assumption hΓ (.sort Γ .zero)) propVar)

def innerMotiveAtTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    HasTyA env (iotaIfaceA env) 0 Γ (innerMotiveAt a p) (.sort one) :=
  applyE hΓ (applyE hΓ (innerMotiveTyped hΓ) ha) hp

def innerMotiveBeta {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    ConvA env (iotaIfaceA env) 0 Γ (innerMotiveAt a p) (.sort .zero) (.sort one) := by
  have hfirst : ConvA env (iotaIfaceA env) 0 Γ (.app innerMotive a)
      (.lam (eqAt parameter a) .zero (.sort .zero)) (innerTail a) :=
    .beta Γ (.sort .zero) one innerBody a (innerTail (.bvar 0)) (.sort Γ .zero)
      (tailLamTyped (.assumption hΓ (.sort Γ .zero)) propVar) ha (tailLamTyped hΓ ha)
  have hc : ConvA env (iotaIfaceA env) 0 Γ (innerMotiveAt a p)
      (.app (.lam (eqAt parameter a) .zero (.sort .zero)) p) (.sort one) :=
    .app Γ _ _ p p (eqAt parameter a) (.sort one) .zero two
      hfirst (.refl Γ p _ hp) (.sort _ one) (applyE hΓ (tailLamTyped hΓ ha) hp)
  exact .trans Γ _ _ _ _ hc
    (.beta Γ (eqAt parameter a) .zero (.sort .zero) p (.sort one)
      (eqTyped hΓ parameterTyped ha) (.sort _ .zero) hp (.sort Γ .zero))

def innerMotiveTypeConv {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    TyConvA env (iotaIfaceA env) 0 Γ (innerMotiveAt a p) (.sort .zero) :=
  .of Γ _ _ one one one (innerMotiveAtTyped hΓ ha hp) (eqNA_refl _)
    (.sort Γ .zero) (eqNA_refl _) (innerMotiveBeta hΓ ha hp)

theorem recConstOneTyped (Γ : LCtxA) : Nonempty
    (HasTyA env (iotaIfaceA env) 0 Γ (.const 65 [one]) (instantiateLevelsA [one] recTy)) := by
  obtain ⟨w, ⟨hT⟩⟩ := recTyTypedNoIota
  have h0 := hasTyA_instLevels (envWfA_levels prefixWf) noIotaA_levels
    (n := 0) (ls := [one]) rfl rfl hT
  have h1 := hasTyA_env_iface prefix_in_env prefix_iface h0
  have h2 := hasTyClosedWeakenA closed liftIface
    (fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide)))
    (fun _ => rfl) Γ h1
  exact ⟨.const Γ 65 [one] recMember (instLevel [one] w) rfl rfl rfl h2⟩

abbrev innerPrefix : ExprA :=
  foldAppsA (.const 65 [one]) [.sort .zero, parameter, innerMotive, parameter, parameter]
abbrev innerCall (p : ExprA) : ExprA := .app innerPrefix p

theorem innerPrefixTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ innerPrefix
      (.pi domain .zero (innerMotiveAt parameter (.bvar 0)) one)) := by
  obtain ⟨hr⟩ := recConstOneTyped Γ
  have h0 := applyE hΓ hr (.sort Γ .zero)
  have h1 := applyE hΓ h0 parameterTyped
  have h2 := applyE hΓ h1 (innerMotiveTyped hΓ)
  have hm := hasTyA_of_tyConvA
    (parameterTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := Γ))
    (innerMotiveTypeConv hΓ parameterTyped (reflTyped hΓ parameterTyped)).symm
  exact ⟨applyE hΓ (applyE hΓ h2 hm) parameterTyped⟩

/-- The inner recursor conversion has a certified `irr` node over
`A = Sort 0`. It is not merely an inhabited pair of endpoints. -/
theorem innerConversionUsesIrr {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {p : ExprA} (hp : HasTyA env (iotaIfaceA env) 0 Γ p domain) :
    ∃ hc : ConvA env (iotaIfaceA env) 0 Γ (innerCall p) parameter (.sort .zero),
      UsesEqCarrierIrr (.sort .zero) hc := by
  obtain ⟨hf⟩ := innerPrefixTyped hΓ
  have hr := reflTyped hΓ (parameterTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := Γ))
  have tcp := innerMotiveTypeConv hΓ parameterTyped hp
  have tcr := innerMotiveTypeConv hΓ parameterTyped hr
  have hfr := applyE hΓ hf hr
  have hfrP := hasTyA_of_tyConvA hfr (.trans Γ _ _ _ tcr tcp.symm)
  let hirr : ConvA env (iotaIfaceA env) 0 Γ p (reflAt parameter) domain :=
    .irr Γ domain p (reflAt parameter) (eqTyped hΓ parameterTyped parameterTyped) hp hr
  have hbody := (hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface hΓ hf).2).2
  let hc := ConvA.app Γ innerPrefix innerPrefix p (reflAt parameter) domain
    (innerMotiveAt parameter (.bvar 0)) .zero one (.refl Γ _ _ hf) hirr hbody hfrP
  let hc' : ConvA env (iotaIfaceA env) 0 Γ (innerCall p)
      (innerCall (reflAt parameter)) (.sort .zero) :=
    .tyConv Γ _ _ (innerMotiveAt parameter p) (.sort .zero) one one one hc
      (innerMotiveAtTyped hΓ parameterTyped hp) (eqNA_refl _)
      (.sort Γ .zero) (eqNA_refl _) (innerMotiveBeta hΓ parameterTyped hp)
  have hι : (iotaIfaceA env).rel env Γ (innerCall (reflAt parameter)) parameter :=
    ⟨by decide, rfl⟩
  refine ⟨.trans Γ _ _ _ _ hc'
    (.iota Γ _ _ _ hι (hasTyA_of_tyConvA hfr tcr) parameterTyped), ?_⟩
  exact Or.inl (Or.inl (Or.inr ⟨parameter, parameter, rfl⟩))

abbrev actualIndex : ExprA := innerCall (.bvar 0)

theorem actualIndexTyped : Nonempty
    (HasTyA env (iotaIfaceA env) 0 context actualIndex (.sort .zero)) := by
  obtain ⟨hc, _⟩ := innerConversionUsesIrr contextWf majorTyped
  exact ⟨convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc⟩

abbrev outerShape : KStage.Shape :=
  KEqPositive.shape actualIndex (motiveAt (liftA 0 1 actualIndex) (.bvar 0)) (.bvar 0)

theorem indicesDiffer : outerShape.declaredIndices ≠ outerShape.actualIndices := by decide

theorem outerOldHeadNone :
    hStepFnA env (iotaIfaceA env).fn context outerShape.source = none := by decide

/-- All premises of an actual K frame, using the certified inner conversion
as its index guard. Its actual proof major is retyped by that same guard. -/
theorem frameWithGuardIrr :
    ∃ hg : ConvA env (iotaIfaceA env) 0 context parameter actualIndex (.sort .zero),
      UsesEqCarrierIrr (.sort .zero) hg ∧
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 context outerShape) := by
  obtain ⟨hi, huses⟩ := innerConversionUsesIrr contextWf majorTyped
  let hg := ConvA.symm context actualIndex parameter (.sort .zero) hi
  have ha := convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hi
  have hfamily : ConvA env (iotaIfaceA env) 0 context
      domain (eqAt parameter actualIndex) (.sort .zero) :=
    .app context _ _ parameter actualIndex (.sort .zero) (.sort .zero) one one
      (.refl context _ _ (KEqPositive.familyHeadTyped contextWf)) hg
      (.sort _ .zero) (eqTyped contextWf parameterTyped ha)
  have hfamilyTy : TyConvA env (iotaIfaceA env) 0 context domain (eqAt parameter actualIndex) :=
    .of context _ _ .zero .zero .zero (eqTyped contextWf parameterTyped parameterTyped)
      (eqNA_refl _) (eqTyped contextWf parameterTyped ha) (eqNA_refl _) hfamily
  have hp := hasTyA_of_tyConvA majorTyped hfamilyTy
  obtain ⟨hr⟩ := recConstTyped context
  have h0 := applyE contextWf hr (.sort context .zero)
  have h1 := applyE contextWf h0 parameterTyped
  have h2 := applyE contextWf h1 (motiveTyped contextWf)
  have hm := hasTyA_of_tyConvA
    (resultTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := context))
    (motiveTypeConv contextWf parameterTyped (reflTyped contextWf parameterTyped)).symm
  have hf := applyE contextWf (applyE contextWf h2 hm) ha
  refine ⟨hg, huses, ⟨{
    target := KEqPositive.target _ _ _
    familyTelescope := KEqPositive.familyTelescope
    telescope := rfl
    familyHeadType := KEqPositive.familyHeadTyped contextWf
    indexGuard := .cons (.sort .zero) one (.sort .zero) one parameter actualIndex [] []
      ⟨hg⟩ (.nil (.sort .zero))
    familyResult := rfl
    prefixType := hf
    majorType := hp
    canonicalType := reflTyped contextWf parameterTyped
    canonicalIota := ⟨by decide, by decide⟩
    minorType := ?_
  }⟩⟩
  exact hasTyA_of_tyConvA resultTyped (motiveTypeConv contextWf ha hp).symm

abbrev closeContext : SubstA := fun _ => reflAt parameter

def contextClosingTyped : SubstTyA env (iotaIfaceA env) 0 [] closeContext context where
  ty := fun i A h => by
    cases i with
    | zero => cases h; exact reflTyped .nil parameterTyped
    | succ i => cases h
  val := fun i A v _ h => by
    cases i with
    | zero => cases h
    | succ i => cases h

theorem outerHeadSort : HeadA3 env (iotaIfaceA env) 0 context
    outerShape.source result (.sort one) := by
  obtain ⟨_, _, ⟨w⟩⟩ := frameWithGuardIrr
  obtain ⟨ha⟩ := actualIndexTyped
  exact .convert _ _ _ _ (.k outerShape ⟨w⟩)
    (motiveTypeConv contextWf ha w.majorType)

theorem outerCallTyped : Nonempty (HasTyA env (iotaIfaceA env) 0 context
    outerShape.source (.sort one)) :=
  outerHeadSort.leftTyped closed liftIface (iotaFnA_recHead env) substIface contextWf

theorem outerWhTy : WhTyA3 env (iotaIfaceA env) 0
    (contextualHeadLayerA3 env (iotaIfaceA env) 0) context outerShape.source result := by
  obtain ⟨ht⟩ := outerCallTyped
  exact whTyA3_cons ht outerHeadSort
    (whTyA3_of_hasTy resultTyped (LR3EqHead.resultNormal context))

/-- At the `Sort 1` term clause, LR3's lower type-validity obligation is
at height 1. This is the height compared with the actual Eq carrier below. -/
theorem sortOneCarrierDemand {ρ₀ : Nat → Nat} {k : Nat} {Γ : LCtxA} {a b : ExprA}
    (h : LRRelA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) ρ₀ k Γ (.sort one) a b) :
    ∃ R, LRTyA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) ρ₀ 1 Γ a R := by
  let H := contextualHeadLayerA3 env (iotaIfaceA env) 0
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA3_eq] at hR
  have hS : WhTyA3 env (iotaIfaceA env) 0 H Γ (.sort one) (.sort one) :=
    whTyA3_sort Γ one
  cases hR with
  | prop hA _ hP =>
      have he := whTyA3_det hA hS
      subst he
      exact absurd hP (not_isPropTyA3_sort env (iotaIfaceA env) 0 H Γ one)
  | sortT hA _ _ =>
      have he := whTyA3_det hA hS
      cases he
      exact hab.2.1
  | sortP hA hz =>
      have he := whTyA3_det hA hS
      cases he
      exact Bool.noConfusion hz
  | pi hA _ _ _ _ _ _ _ _ =>
      have he := whTyA3_det hA hS
      cases he
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA3_det hA hS) (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hA hN =>
      have he := whTyA3_det hA hS
      subst he
      exact (hN.2 (by trivial)).elim

/-- The actual typed carrier occurring in the guard is not strictly below
the lower height demanded by the motive's Type-sort interpretation. -/
theorem inhabited_guard_height_boundary (ρ₀ : Nat → Nat) :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeContext context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (.sort .zero) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context parameter (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context actualIndex (.sort .zero)) ∧
    outerShape.declaredIndices ≠ outerShape.actualIndices ∧
    hStepFnA env (iotaIfaceA env).fn context outerShape.source = none ∧
    (∃ hg : ConvA env (iotaIfaceA env) 0 context parameter actualIndex (.sort .zero),
      UsesEqCarrierIrr (.sort .zero) hg ∧
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 context outerShape)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context outerShape.source (.sort one)) ∧
    HeadA3 env (iotaIfaceA env) 0 context outerShape.source result (.sort one) ∧
    WhTyA3 env (iotaIfaceA env) 0 (contextualHeadLayerA3 env (iotaIfaceA env) 0)
      context outerShape.source result ∧
    ht ρ₀ one = 1 ∧ ¬ ht ρ₀ one < 1 :=
  ⟨erase_env, wf, ⟨contextWf⟩, ⟨contextClosingTyped⟩, ⟨.sort context .zero⟩,
    ⟨parameterTyped⟩, actualIndexTyped, indicesDiffer, outerOldHeadNone,
    frameWithGuardIrr, outerCallTyped,
    outerHeadSort, outerWhTy, rfl, Nat.lt_irrefl 1⟩

#print axioms UsesEqCarrierIrr
#print axioms innerTail
#print axioms innerBody
#print axioms innerMotive
#print axioms innerMotiveTy
#print axioms innerMotiveAt
#print axioms innerMotiveTyped
#print axioms innerMotiveAtTyped
#print axioms innerMotiveBeta
#print axioms innerMotiveTypeConv
#print axioms recConstOneTyped
#print axioms innerPrefix
#print axioms innerCall
#print axioms innerPrefixTyped
#print axioms innerConversionUsesIrr
#print axioms actualIndex
#print axioms actualIndexTyped
#print axioms outerShape
#print axioms indicesDiffer
#print axioms outerOldHeadNone
#print axioms frameWithGuardIrr
#print axioms closeContext
#print axioms contextClosingTyped
#print axioms outerHeadSort
#print axioms outerCallTyped
#print axioms outerWhTy
#print axioms sortOneCarrierDemand
#print axioms inhabited_guard_height_boundary

end Rcic.Declarative.Ann.LR3.GuardHeightBoundary
