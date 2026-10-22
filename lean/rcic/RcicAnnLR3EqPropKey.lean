import rcic.RcicAnnLR3GuardHeightBoundary

/-!
# The actual Eq-shaped irrelevance query has a supplied relational key

The proposition at the recorded `irr` node of `innerConversionUsesIrr` is
`Eq Prop parameter parameter`. Its sort is synthesized from the stored Eq
telescope. None of its index arguments is recursively interpreted or
normalized. This supplies the key for that concrete query, independently
of `EnvSemA`, `EnvSem3`, and declarative sort uniqueness.

The stronger raw syntax statement for `eqAt a b` is intentional: relational
inference does not check an application's argument. It is a key theorem,
not a typing theorem for arbitrary `a` or `b`. The final bundle includes
the actual admitted environment, context, proposition typing, and key.
Consequently the previous equal-carrier-height fixture cannot by itself
be used as an obstruction to descent of its immediate proposition key.

The selected-occurrence certificate below follows exactly the five cases
of the landed `UsesEqCarrierIrr` predicate (the `irr` node and the `symm`,
`trans`, `app`, and `tyConv` paths). It retains the original `hP` as an
index. This is not the exhaustive mutual traversal of irrelevance nodes;
`convIrrQueriesA3` supplies that separate traversal.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.EqPropKey

open Rcic.Declarative EqLargeFixture

private abbrev firstPartialType : ExprA :=
  .pi (.sort .zero) one
    (.pi (.sort .zero) one (.sort .zero) one) (.imax one one)

private def firstPartialTypeTyped (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ firstPartialType
      (.sort (.imax one (.imax one one))) :=
  .pi Γ (.sort .zero) one _ (.imax one one) (.sort Γ .zero)
    (.pi _ (.sort .zero) one (.sort .zero) one (.sort _ .zero) (.sort _ .zero))

private def finalPartialTypeTyped (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ KEqPositive.familyTelescope
      (.sort (.imax one one)) :=
  .pi Γ (.sort .zero) one (.sort .zero) one (.sort Γ .zero) (.sort _ .zero)

/-- The Eq telescope fixes this raw inference result without inspecting either
index. The finite witnesses normalize only the stored intermediate Pi types. -/
theorem eqAtInferA3 (H : HeadLayerA3 env (iotaIfaceA env) 0)
    (Γ : LCtxA) (a b : ExprA) :
    InferA3 env (iotaIfaceA env) 0 H Γ (eqAt a b) (.sort .zero) := by
  have h₀ : InferA3 env (iotaIfaceA env) 0 H Γ (.const 63 []) famTy :=
    .const (m := fam) rfl rfl
  have h₁ : InferA3 env (iotaIfaceA env) 0 H Γ
      (.app (.const 63 []) (.sort .zero)) firstPartialType :=
    .app h₀ (whTyA3_of_hasTy famTyTyped (H.normal_pi _ _ _ _ _))
  have h₂ : InferA3 env (iotaIfaceA env) 0 H Γ
      (foldAppsA (.const 63 []) [.sort .zero, a]) KEqPositive.familyTelescope :=
    .app h₁ (whTyA3_of_hasTy (firstPartialTypeTyped Γ) (H.normal_pi _ _ _ _ _))
  exact .app h₂
    (whTyA3_of_hasTy (finalPartialTypeTyped Γ) (H.normal_pi _ _ _ _ _))

/-- The actual relational sort-synthesis witness; it contains no key-coherence
hypothesis or recursive semantic obligation for the indices. -/
theorem eqAtSortOfA3 (H : HeadLayerA3 env (iotaIfaceA env) 0)
    (Γ : LCtxA) (a b : ExprA) :
    SortOfA3 env (iotaIfaceA env) 0 H Γ (eqAt a b) .zero :=
  ⟨.sort .zero, eqAtInferA3 H Γ a b, whTyA3_sort Γ .zero⟩

theorem eqAtIsPropTyA3 (H : HeadLayerA3 env (iotaIfaceA env) 0)
    (Γ : LCtxA) (a b : ExprA) :
    IsPropTyA3 env (iotaIfaceA env) 0 H Γ (eqAt a b) :=
  ⟨.zero, eqAtSortOfA3 H Γ a b, rfl⟩

/-- The proposition queried by the recorded irrelevance node in the guard
height fixture has its key positively supplied, with all regularity premises. -/
theorem inhabitedGuardPropositionKeyA3
    (H : HeadLayerA3 env (iotaIfaceA env) 0) :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context domain (.sort .zero)) ∧
    SortOfA3 env (iotaIfaceA env) 0 H context domain .zero ∧
    IsPropTyA3 env (iotaIfaceA env) 0 H context domain :=
  ⟨erase_env, wf, ⟨contextWf⟩,
    ⟨eqTyped contextWf parameterTyped parameterTyped⟩,
    eqAtSortOfA3 H context parameter parameter,
    eqAtIsPropTyA3 H context parameter parameter⟩

/-- A selected original irrelevance premise, along the paths admitted by
`UsesEqCarrierIrr`. The selected proposition typing is an index, and `here`
uses that exact proof as the `irr` constructor's original premise. This
deliberately is not an exhaustive occurrence relation. -/
inductive EqIrrSelectedA3 {Δ : LCtxA} {P : ExprA}
    (hP : HasTyA env (iotaIfaceA env) 0 Δ P (.sort .zero)) :
    {Γ : LCtxA} → {a b T : ExprA} →
      ConvA env (iotaIfaceA env) 0 Γ a b T → Prop
  | here (p q : ExprA)
      (hp : HasTyA env (iotaIfaceA env) 0 Δ p P)
      (hq : HasTyA env (iotaIfaceA env) 0 Δ q P) :
      EqIrrSelectedA3 hP (.irr Δ P p q hP hp hq)
  | symm {Γ : LCtxA} {a b T : ExprA}
      {h : ConvA env (iotaIfaceA env) 0 Γ a b T}
      (selected : EqIrrSelectedA3 hP h) :
      EqIrrSelectedA3 hP (.symm Γ a b T h)
  | transLeft {Γ : LCtxA} {a b c T : ExprA}
      {h₁ : ConvA env (iotaIfaceA env) 0 Γ a b T}
      {h₂ : ConvA env (iotaIfaceA env) 0 Γ b c T}
      (selected : EqIrrSelectedA3 hP h₁) :
      EqIrrSelectedA3 hP (.trans Γ a b c T h₁ h₂)
  | transRight {Γ : LCtxA} {a b c T : ExprA}
      {h₁ : ConvA env (iotaIfaceA env) 0 Γ a b T}
      {h₂ : ConvA env (iotaIfaceA env) 0 Γ b c T}
      (selected : EqIrrSelectedA3 hP h₂) :
      EqIrrSelectedA3 hP (.trans Γ a b c T h₁ h₂)
  | appFunction {Γ : LCtxA} {f g a b D C : ExprA} {u v : Level}
      {hf : ConvA env (iotaIfaceA env) 0 Γ f g (.pi D u C v)}
      {ha : ConvA env (iotaIfaceA env) 0 Γ a b D}
      {hC : HasTyA env (iotaIfaceA env) 0 (.assumption D :: Γ) C (.sort v)}
      {hr : HasTyA env (iotaIfaceA env) 0 Γ (.app g b) (instantiate0A a C)}
      (selected : EqIrrSelectedA3 hP hf) :
      EqIrrSelectedA3 hP (.app Γ f g a b D C u v hf ha hC hr)
  | appArgument {Γ : LCtxA} {f g a b D C : ExprA} {u v : Level}
      {hf : ConvA env (iotaIfaceA env) 0 Γ f g (.pi D u C v)}
      {ha : ConvA env (iotaIfaceA env) 0 Γ a b D}
      {hC : HasTyA env (iotaIfaceA env) 0 (.assumption D :: Γ) C (.sort v)}
      {hr : HasTyA env (iotaIfaceA env) 0 Γ (.app g b) (instantiate0A a C)}
      (selected : EqIrrSelectedA3 hP ha) :
      EqIrrSelectedA3 hP (.app Γ f g a b D C u v hf ha hC hr)
  | tyConvTerm {Γ : LCtxA} {a b A A' : ExprA} {l l' u : Level}
      {h : ConvA env (iotaIfaceA env) 0 Γ a b A}
      {hAl : HasTyA env (iotaIfaceA env) 0 Γ A (.sort l)} {hlu : eqN l u}
      {hA'l : HasTyA env (iotaIfaceA env) 0 Γ A' (.sort l')} {hl'u : eqN l' u}
      {hA : ConvA env (iotaIfaceA env) 0 Γ A A' (.sort u)}
      (selected : EqIrrSelectedA3 hP h) :
      EqIrrSelectedA3 hP (.tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA)
  | tyConvType {Γ : LCtxA} {a b A A' : ExprA} {l l' u : Level}
      {h : ConvA env (iotaIfaceA env) 0 Γ a b A}
      {hAl : HasTyA env (iotaIfaceA env) 0 Γ A (.sort l)} {hlu : eqN l u}
      {hA'l : HasTyA env (iotaIfaceA env) 0 Γ A' (.sort l')} {hl'u : eqN l' u}
      {hA : ConvA env (iotaIfaceA env) 0 Γ A A' (.sort u)}
      (selected : EqIrrSelectedA3 hP hA) :
      EqIrrSelectedA3 hP (.tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA)

/-- Refine the landed occurrence certificate to an actual original `hP`
with its relational key. The recursion follows only the certificate's
selected conversion paths, not arbitrary typing premises. -/
theorem usesEqCarrierIrr_keyedOccurrenceA3
    (H : HeadLayerA3 env (iotaIfaceA env) 0) :
    {Γ : LCtxA} → {a b T : ExprA} →
    (h : ConvA env (iotaIfaceA env) 0 Γ a b T) →
    GuardHeightBoundary.UsesEqCarrierIrr (.sort .zero) h →
    ∃ (Δ : LCtxA) (P : ExprA)
      (hP : HasTyA env (iotaIfaceA env) 0 Δ P (.sort .zero)),
      EqIrrSelectedA3 hP h ∧
      (∃ x y : ExprA, P = eqAt x y) ∧
      IsPropTyA3 env (iotaIfaceA env) 0 H Δ P
  | _, _, _, _, .refl _ _ _ _, hu => nomatch hu
  | _, _, _, _, .symm _ _ _ _ h, hu => by
      obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H h hu
      exact ⟨Δ, P, hP, .symm hs, he, hk⟩
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, hu => by
      rcases hu with hu | hu
      · obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H h₁ hu
        exact ⟨Δ, P, hP, .transLeft hs, he, hk⟩
      · obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H h₂ hu
        exact ⟨Δ, P, hP, .transRight hs, he, hk⟩
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .iota _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .lit _ _ _ _, hu => nomatch hu
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ hf ha _ _, hu => by
      rcases hu with hu | hu
      · obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H hf hu
        exact ⟨Δ, P, hP, .appFunction hs, he, hk⟩
      · obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H ha hu
        exact ⟨Δ, P, hP, .appArgument hs, he, hk⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .sorts _ _ _ _, hu => nomatch hu
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _, hu => nomatch hu
  | _, _, _, _, .eta _ _ _ _ _ _ _ _, hu => nomatch hu
  | Γ, _, _, _, .irr _ P p q hP hp hq, hu => by
      obtain ⟨x, y, he⟩ := hu
      refine ⟨Γ, P, hP, .here p q hp hq, ⟨x, y, he⟩, ?_⟩
      rw [he]
      exact eqAtIsPropTyA3 H Γ x y
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h _ _ _ _ hA, hu => by
      rcases hu with hu | hu
      · obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H h hu
        exact ⟨Δ, P, hP, .tyConvTerm hs, he, hk⟩
      · obtain ⟨Δ, P, hP, hs, he, hk⟩ := usesEqCarrierIrr_keyedOccurrenceA3 H hA hu
        exact ⟨Δ, P, hP, .tyConvType hs, he, hk⟩

/-- The existing inhabited frame and a keyed original irrelevance premise
of that frame's actual guard are supplied together. No new frame proof is
constructed, and the selected proposition need not be identified with a
separately supplied semantic witness. -/
theorem actualGuardHasKeyedOccurrenceA3
    (H : HeadLayerA3 env (iotaIfaceA env) 0) :
    ∃ hg : ConvA env (iotaIfaceA env) 0 context parameter
        GuardHeightBoundary.actualIndex (.sort .zero),
      GuardHeightBoundary.UsesEqCarrierIrr (.sort .zero) hg ∧
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 context
        GuardHeightBoundary.outerShape) ∧
      ∃ (Δ : LCtxA) (P : ExprA)
        (hP : HasTyA env (iotaIfaceA env) 0 Δ P (.sort .zero)),
        EqIrrSelectedA3 hP hg ∧
        (∃ x y : ExprA, P = eqAt x y) ∧
        IsPropTyA3 env (iotaIfaceA env) 0 H Δ P := by
  obtain ⟨hg, hu, hf⟩ := GuardHeightBoundary.frameWithGuardIrr
  exact ⟨hg, hu, hf, usesEqCarrierIrr_keyedOccurrenceA3 H hg hu⟩

#print axioms eqAtInferA3
#print axioms eqAtSortOfA3
#print axioms eqAtIsPropTyA3
#print axioms inhabitedGuardPropositionKeyA3
#print axioms EqIrrSelectedA3
#print axioms EqIrrSelectedA3.here
#print axioms EqIrrSelectedA3.symm
#print axioms EqIrrSelectedA3.transLeft
#print axioms EqIrrSelectedA3.transRight
#print axioms EqIrrSelectedA3.appFunction
#print axioms EqIrrSelectedA3.appArgument
#print axioms EqIrrSelectedA3.tyConvTerm
#print axioms EqIrrSelectedA3.tyConvType
#print axioms usesEqCarrierIrr_keyedOccurrenceA3
#print axioms actualGuardHasKeyedOccurrenceA3

end Rcic.Declarative.Ann.LR3.EqPropKey
