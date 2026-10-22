import rcic.RcicAnnLR3Sort
import rcic.RcicAnnFamHeight
import rcic.RcicAnnSubstTy

/-!
# Positive relational family-key supply

A typed conversion walk through the declared telescope supplies relational
inference of the entire application. Each application crosses a syntactic
Pi whose typing and positive normality are available independently of the
logical relation. Substitution supplies the typing of the remaining telescope.

A complete walk ending at a sort therefore supplies an actual `SortOfA3`
witness, and only then is the proposition key compared with that sort's
Boolean zero test. No old fuelled synthesis, logical-relation validity of
index domains, semantic environment, or conversion decision is used.

The law is proved for every explicit `HeadLayerA3`; its concrete contextual
instance and a closed positive large-index example are supplied below.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

section Walk

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
variable (H : HeadLayerA3 E I n)
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)

include hE hI hR hIS hΓ

/-- A declared typed walk supplies inference of the application and a
typed remaining telescope. This is a construction, not a key equivalence. -/
theorem inferA3_typedConvArgs {f T : ExprA} {v : Level} {xs ys : List ExprA}
    (hf : InferA3 E I n H Γ f T) (hT : HasTyA E I n Γ T (.sort v))
    (hargs : ConvArgsA E I n Γ T xs ys) :
    ∃ U, applyTelA xs T = some U ∧ InferA3 E I n H Γ (foldAppsA f xs) U ∧
      ∃ u, Nonempty (HasTyA E I n Γ U (.sort u)) := by
  induction hargs generalizing f v with
  | nil T => exact ⟨T, rfl, hf, v, ⟨hT⟩⟩
  | cons A u B w a b xs ys hab htail ih =>
      obtain ⟨hab⟩ := hab
      have hp := hasTyA_pi_parts hT
      have ha := convA_hasTy_left hE hI hR hIS hΓ hab
      have hB : HasTyA E I n Γ (instantiate0A a B) (.sort w) :=
        hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hp.2 ha hp.1
      have hfa : InferA3 E I n H Γ (.app f a) (instantiate0A a B) :=
        .app hf (whTyA3_of_hasTy hT (H.normal_pi Γ A u B w))
      obtain ⟨U, hU, hi, uU, htU⟩ := ih hfa hB
      exact ⟨U, hU, hi, uU, htU⟩

/-- Finishing the declared telescope at a sort supplies that exact
relational sort-synthesis witness. -/
theorem sortOfA3_typedConvArgs {f T : ExprA} {v u : Level} {xs ys : List ExprA}
    (hf : InferA3 E I n H Γ f T) (hT : HasTyA E I n Γ T (.sort v))
    (hargs : ConvArgsA E I n Γ T xs ys)
    (hfull : applyTelA xs T = some (.sort u)) :
    SortOfA3 E I n H Γ (foldAppsA f xs) u := by
  obtain ⟨U, hU, hi, _⟩ := inferA3_typedConvArgs H hE hI hR hIS hΓ hf hT hargs
  have he := Option.some.inj (hU.symm.trans hfull)
  cases he
  exact ⟨.sort u, hi, whTyA3_sort Γ u⟩

/-- A family/member application gets its sort witness from the stored
telescope, followed by the exact Boolean proposition key. -/
theorem familyKeyA3_typedConvArgs {r : Nat} {m : CheckedMemberA}
    {ls : List Level} {v u : Level} {xs ys : List ExprA}
    (hm : E.members r = some m) (hlen : ls.length = m.arity)
    (hT : HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort v))
    (hargs : ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) xs ys)
    (hfull : applyTelA xs (instantiateLevelsA ls m.mtypeA) = some (.sort u)) :
    SortOfA3 E I n H Γ (foldAppsA (.const r ls) xs) u ∧
      (IsPropTyA3 E I n H Γ (foldAppsA (.const r ls) xs) ↔ isZero u = true) := by
  have hs := sortOfA3_typedConvArgs H hE hI hR hIS hΓ (.const hm hlen) hT hargs hfull
  exact ⟨hs, isPropTyA3_iff_of_sort H hs⟩

/-- Two supplied typed walks produce both sort witnesses and compatible
keys whenever their declared result levels agree under `eqN`. -/
theorem familyKeyA3_cross {f g T T' : ExprA} {v v' u u' : Level}
    {xs ys xs' ys' : List ExprA}
    (hf : InferA3 E I n H Γ f T) (hT : HasTyA E I n Γ T (.sort v))
    (hargs : ConvArgsA E I n Γ T xs ys) (hfull : applyTelA xs T = some (.sort u))
    (hg : InferA3 E I n H Γ g T') (hT' : HasTyA E I n Γ T' (.sort v'))
    (hargs' : ConvArgsA E I n Γ T' xs' ys') (hfull' : applyTelA xs' T' = some (.sort u'))
    (hu : eqN u u') :
    SortOfA3 E I n H Γ (foldAppsA f xs) u ∧
    SortOfA3 E I n H Γ (foldAppsA g xs') u' ∧
    (IsPropTyA3 E I n H Γ (foldAppsA f xs) ↔
      IsPropTyA3 E I n H Γ (foldAppsA g xs')) := by
  have hl := sortOfA3_typedConvArgs H hE hI hR hIS hΓ hf hT hargs hfull
  have hr := sortOfA3_typedConvArgs H hE hI hR hIS hΓ hg hT' hargs' hfull'
  refine ⟨hl, hr, ?_⟩
  rw [isPropTyA3_iff_of_sort H hl, isPropTyA3_iff_of_sort H hr, isZero_eqN hu]

end Walk

/-- The family-key obligation on a head layer, retaining positive sort
synthesis as part of the conclusion. -/
def FamilyKeyLawA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA) (r : Nat) (m : CheckedMemberA) (ls : List Level)
    (v u : Level) (xs ys : List ExprA),
    CtxWfA E I n Γ → E.members r = some m → ls.length = m.arity →
    HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort v) →
    ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) xs ys →
    applyTelA xs (instantiateLevelsA ls m.mtypeA) = some (.sort u) →
    SortOfA3 E I n H Γ (foldAppsA (.const r ls) xs) u ∧
      (IsPropTyA3 E I n H Γ (foldAppsA (.const r ls) xs) ↔ isZero u = true)

/-- The existing certified Pi/sort normality is sufficient for the law. -/
theorem familyKeyLawA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadA E I) (hIS : IotaSubstA I) : FamilyKeyLawA3 E I n H := by
  intro Γ r m ls v u xs ys hΓ hm hlen hT hargs hfull
  exact familyKeyA3_typedConvArgs H hE hI hR hIS hΓ hm hlen hT hargs hfull

/-- The requested concrete contextual head layer supplies the key law. -/
theorem contextualFamilyKeyLawA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    FamilyKeyLawA3 E I n (contextualHeadLayerA3 E I n) :=
  familyKeyLawA3 (contextualHeadLayerA3 E I n) hE hI hR hIS

/-- The large-index family obtains its relational key from a typed index
conversion, with no logical-relation assumption at the index's height. -/
theorem pinFamF0_sortOf_indexA3 (n : Nat)
    (H : HeadLayerA3 (pinFamFEnvA 0) noIotaA n) {Γ : LCtxA}
    (hΓ : CtxWfA (pinFamFEnvA 0) noIotaA n Γ) {a b : ExprA}
    (hab : ConvA (pinFamFEnvA 0) noIotaA n Γ a b (.sort (.succ .zero))) :
    SortOfA3 (pinFamFEnvA 0) noIotaA n H Γ (.app (.const 0 []) a) (.succ .zero) := by
  have hargs : ConvArgsA (pinFamFEnvA 0) noIotaA n Γ (pinFamFA 0).mtypeA [a] [b] :=
    .cons (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort (.succ .zero)) (.succ (.succ .zero)) a b [] [] ⟨hab⟩
      (.nil (.sort (.succ .zero)))
  exact sortOfA3_typedConvArgs H (pinFamF_closed 0) noIotaA_lift
    (noIotaA_recHead (pinFamFEnvA 0)) noIotaA_subst hΓ
    (.const (ls := []) (pinFamF_members 0) rfl)
    (pinFamFTypeTy 0 (pinFamFEnvA 0) n Γ) hargs rfl

/-- The actual closed large-index instance supplies admission, typing,
relational sort synthesis, and its negative proposition key. -/
theorem pinFamF0_largeIndexKeySupplyA3 :
    Nonempty (EnvWfA noIotaA (pinFamFEnvA 0)) ∧
    Nonempty (HasTyA (pinFamFEnvA 0) noIotaA 0 [] pinFamFAppA (.sort (.succ .zero))) ∧
    SortOfA3 (pinFamFEnvA 0) noIotaA 0
      (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA 0) [] pinFamFAppA (.succ .zero) ∧
    ¬ IsPropTyA3 (pinFamFEnvA 0) noIotaA 0
      (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA 0) [] pinFamFAppA := by
  let H := contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA 0
  have hs : SortOfA3 (pinFamFEnvA 0) noIotaA 0 H [] pinFamFAppA (.succ .zero) :=
    pinFamF0_sortOf_indexA3 0 H .nil (.refl [] (.sort .zero) (.sort (.succ .zero)) (.sort [] .zero))
  exact ⟨⟨pinFamFEnvWfA 0 pinFamF0ViewA⟩,
    ⟨pinFamFAppTy (pinFamF_members 0) 0 []⟩, hs,
    not_isPropTyA3_of_sort H hs rfl⟩

#print axioms inferA3_typedConvArgs
#print axioms sortOfA3_typedConvArgs
#print axioms familyKeyA3_typedConvArgs
#print axioms familyKeyA3_cross
#print axioms FamilyKeyLawA3
#print axioms familyKeyLawA3
#print axioms contextualFamilyKeyLawA3
#print axioms pinFamF0_sortOf_indexA3
#print axioms pinFamF0_largeIndexKeySupplyA3

end Rcic.Declarative.Ann.LR3
