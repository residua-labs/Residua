import rcic.RcicAnnLR3SortCoherenceBoundary

/-!
# The finite normalization data hidden in typing-to-sort synthesis

`SortOfA3` normalizes the inferred type of its subject, not the subject
itself. The two inversions below expose the exact finite data required at
variables and variable-headed applications. They do not identify the
synthesized sort with a declarative sort.

An existence principle for all sort-typed subjects consequently supplies
these finite chains. In particular, bind `x : T` when `T` converts to a
sort and retype `x` at that sort. Synthesis of `x` normalizes the actual
lifted declared type `T` in the extended context. No strengthening or
normalization in the original context is silently assumed.

The final control records that raw synthesis alone is not declarative
typing: its Pi rule intentionally reads annotations without validating
the domain. The coherence predicates in the preceding module correctly
retain their separate declarative typing premise. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- Sort synthesis at a variable contains a terminal typed chain of its
actual context type. It does not normalize the variable itself. -/
theorem sortOfA3_bvar_declared_chain
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    {Γ : LCtxA} {i : Nat} {T : ExprA} {l : Level}
    (hlookup : lookupTypeA Γ i = some T)
    (hs : SortOfA3 E I n H Γ (.bvar i) l) :
    WhTyA3 E I n H Γ T (.sort l) := by
  obtain ⟨U, hi, hw⟩ := hs
  have he : U = T := inferA3_det H hi (.bvar hlookup)
  cases he
  exact hw

/-- Application synthesis must already carry a terminal Pi chain for the
function's inferred type. At a variable that is its declared context type. -/
theorem sortOfA3_app_bvar_declared_pi_chain
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    {Γ : LCtxA} {i : Nat} {a T : ExprA} {l : Level}
    (hlookup : lookupTypeA Γ i = some T)
    (hs : SortOfA3 E I n H Γ (.app (.bvar i) a) l) :
    ∃ D u B v, WhTyA3 E I n H Γ T (.pi D u B v) := by
  obtain ⟨U, hi, _⟩ := hs
  cases hi with
  | app hf hTf =>
      have he := inferA3_det H hf (.bvar hlookup)
      cases he
      exact ⟨_, _, _, _, hTf⟩

/-- Existence of relational sort synthesis for every already sort-typed
subject. No agreement of the resulting level is included. -/
def TypeSortSynthesisA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ (A : ExprA) (u : Level),
    HasTyA E I n Γ A (.sort u) → ∃ v, SortOfA3 E I n H Γ A v

theorem propSynthesisA3_of_typeSortSynthesis
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (h : TypeSortSynthesisA3 E I n H) : PropSynthesisA3 E I n H :=
  fun Γ hΓ P ht => h Γ hΓ P .zero ht

/-- A typing-to-synthesis theorem would supply the finite Pi normalization
needed to type a variable-headed application by synthesis. -/
theorem declaredPiChain_of_typeSortSynthesisA3
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (h : TypeSortSynthesisA3 E I n H)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {i : Nat} {a T : ExprA} {u : Level}
    (hlookup : lookupTypeA Γ i = some T)
    (ht : HasTyA E I n Γ (.app (.bvar i) a) (.sort u)) :
    ∃ D v B w, WhTyA3 E I n H Γ T (.pi D v B w) := by
  obtain ⟨l, hs⟩ := h Γ hΓ _ u ht
  exact sortOfA3_app_bvar_declared_pi_chain hlookup hs

private def declaredSortProbeTyped
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    {Γ : LCtxA} {T : ExprA} {w u : Level}
    (hT : HasTyA E I n Γ T (.sort w))
    (hc : TyConvA E I n Γ T (.sort u)) :
    HasTyA E I n (.assumption T :: Γ) (.bvar 0) (.sort u) := by
  have hT' : HasTyA E I n (.assumption T :: Γ) (liftA 0 1 T) (.sort w) :=
    hasTyWeakenA hE hI (.assumption T) (c := 0) (Nat.zero_le _) hT
  have hx : HasTyA E I n (.assumption T :: Γ) (.bvar 0) (liftA 0 1 T) :=
    .bvar _ 0 _ w rfl hT'
  exact hasTyA_of_tyConvA hx
    (tyConvA_weaken hE hI (.assumption T) (c := 0) (Nat.zero_le _) hc)

/-- The supplied synthesis principle normalizes a sort-convertible declared
type after binding it. The lift and the extended context are essential. -/
theorem declaredSortChain_of_typeSortSynthesisA3
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : TypeSortSynthesisA3 E I n H)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {T : ExprA} {w u : Level}
    (hT : HasTyA E I n Γ T (.sort w))
    (hc : TyConvA E I n Γ T (.sort u)) :
    ∃ v, WhTyA3 E I n H (.assumption T :: Γ) (liftA 0 1 T) (.sort v) := by
  obtain ⟨v, hs⟩ := h _ (.assumption hΓ hT) (.bvar 0) u
    (declaredSortProbeTyped hE hI hT hc)
  exact ⟨v, sortOfA3_bvar_declared_chain (i := 0) rfl hs⟩

/-- Even Prop-only synthesis contains finite normalization at every
declared type convertible to `sort 0`; existence alone does not give its key. -/
theorem declaredZeroChain_of_propSynthesisA3
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : PropSynthesisA3 E I n H)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {T : ExprA} {w : Level}
    (hT : HasTyA E I n Γ T (.sort w))
    (hc : TyConvA E I n Γ T (.sort .zero)) :
    ∃ v, WhTyA3 E I n H (.assumption T :: Γ) (liftA 0 1 T) (.sort v) := by
  obtain ⟨v, hs⟩ := h _ (.assumption hΓ hT) (.bvar 0)
    (declaredSortProbeTyped hE hI hT hc)
  exact ⟨v, sortOfA3_bvar_declared_chain (i := 0) rfl hs⟩

/-- The direct irrelevance-key bridge supplies both the finite chain and
its zero key in this declared-type probe. -/
theorem declaredZeroChain_of_typedPropKeyA3
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : TypedPropKeyA3 E I n H)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {T : ExprA} {w : Level}
    (hT : HasTyA E I n Γ T (.sort w))
    (hc : TyConvA E I n Γ T (.sort .zero)) :
    ∃ v, WhTyA3 E I n H (.assumption T :: Γ) (liftA 0 1 T) (.sort v) ∧
      isZero v = true := by
  obtain ⟨v, hs, hz⟩ := h _ (.assumption hΓ hT) (.bvar 0)
    (declaredSortProbeTyped hE hI hT hc)
  exact ⟨v, sortOfA3_bvar_declared_chain (i := 0) rfl hs, hz⟩

/-- An intentionally ill-scoped Pi used only to distinguish raw syntax
synthesis from declarative typing. -/
def uncheckedPiProbeA3 : ExprA := .pi (.bvar 0) .zero (.sort .zero) .zero

theorem uncheckedPiProbeA3_isProp
    (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) :
    IsPropTyA3 E I n H [] uncheckedPiProbeA3 :=
  (isPropTyA3_pi_iff E I n H [] (.bvar 0) .zero (.sort .zero) .zero).mpr rfl

theorem uncheckedPiProbeA3_untypable
    (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (T : ExprA) :
    ¬ Nonempty (HasTyA E I n [] uncheckedPiProbeA3 T) := by
  rintro ⟨ht⟩
  have hb := hasTyA_boundOk ht
  change false = true at hb
  cases hb

/-- All displayed ambient and synthetic premises of the raw-syntax
counterexample are inhabited; its failure is precisely missing typing. -/
theorem relationalPropKey_does_not_supply_typing3
    (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) :
    Nonempty (CtxWfA E I n []) ∧ IsPropTyA3 E I n H [] uncheckedPiProbeA3 ∧
      ∀ T, ¬ Nonempty (HasTyA E I n [] uncheckedPiProbeA3 T) :=
  ⟨⟨.nil⟩, uncheckedPiProbeA3_isProp E I n H, uncheckedPiProbeA3_untypable E I n⟩

#print axioms sortOfA3_bvar_declared_chain
#print axioms sortOfA3_app_bvar_declared_pi_chain
#print axioms TypeSortSynthesisA3
#print axioms propSynthesisA3_of_typeSortSynthesis
#print axioms declaredPiChain_of_typeSortSynthesisA3
#print axioms declaredSortChain_of_typeSortSynthesisA3
#print axioms declaredZeroChain_of_propSynthesisA3
#print axioms declaredZeroChain_of_typedPropKeyA3
#print axioms uncheckedPiProbeA3
#print axioms uncheckedPiProbeA3_isProp
#print axioms uncheckedPiProbeA3_untypable
#print axioms relationalPropKey_does_not_supply_typing3

end Rcic.Declarative.Ann.LR3
