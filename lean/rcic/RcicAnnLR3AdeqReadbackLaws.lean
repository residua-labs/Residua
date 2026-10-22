import rcic.RcicAnnLR3AdeqNeutralObstructions
import rcic.RcicAnnLR3StratifiedCandidates
import rcic.RcicAnnErase

/-!
# Adequacy Readback Laws, Annotated-to-Native Transfer, and Stratified Neutral Repairs

This module extends `RcicAnnLR3AdeqRelation` and `RcicAnnLR3AdeqNeutralObstructions` with
three kernel-checked components of the CCFMLMW adequacy / readback architecture for RCIC:

1. **Sort-level equality, annotated `ExprA` Π-inversion, and erasure to native `ConvT`/`TyConvT` (§1)**:
   - `eqN_of_nativeRelatedCode_sorts`, `eqN_of_nativeSemTypeRel_sorts`,
     `eqN_of_annRelatedCode_sorts`, `eqN_of_annSemTypeRel_sorts`: under `PairedFundamental`
     (resp. `NativePairedFundamental`) and `NeutralSupport`, any two sort-typed expressions
     `Γ ⊢ X : .sort u` and `Γ ⊢ Y : .sort u'` that are related by `RelatedCode` at the
     generic reflected environment automatically have level-equal sorts `eqN u u'`.
   - `annPiInj_of_adequacy`: combines `PairedFundamental`, `UniverseTransport`,
     `NeutralSupport`, `AnnSemPiInj`, `AnnTypeReadback`, and `hasTyA_ctxConv` to invert any
     semantically related (in particular, any `ConvA`- or `TyConvA`-convertible) pair of
     well-typed annotated Π types `.pi A u B v` and `.pi A' u' B' v'` into:
     `eqN u u'`, `eqN v v'`, `Nonempty (ConvA E I n Γ A A' (.sort u))`,
     `Nonempty (ConvA E I n (.assumption A :: Γ) B B' (.sort v))`, and `TyConvA` on both.
   - `erasedPiComponents_of_annAdequacy`: erases the annotated Π-component conversions
     via `convT_of_convA` and `tyConvT_of_tyConvA` (`RcicAnnErase`) into native `ConvT` and
     `TyConvT` in `eraseEnv E` and `eraseCtx Γ`.

2. **Kripke-glued term and neutral spine readback combinators (CCFMLMW §§2.6–2.8) (§2)**:
   - `reify_native_pi_type`, `reify_ann_pi_type`: reifies domain and reflected-variable
     codomain conversions into a Π-type conversion (`ConvT.pi` / `ConvA.pi`).
   - `reify_native_pi_term_eta`, `reify_ann_pi_term_eta`: reifies two functions
     `f, g : Π A, B` whose applications to the reflected variable `.bvar 0` in
     `.assumption A :: Γ` reify at `B`, closing by `Conv.lam` and `Conv.eta` on both sides.
   - `reify_native_bvar`, `reify_native_const`, `reify_native_app`: neutral spine
     reflection and congruence combinators.
   - `reify_native_forward_k_step`, `reify_ann_forward_k_step`: general syntactic readback
     of a forward `NeutralK.Seed.k` edge (`Conv.irr` aligning the neutral major `p` with
     `reflTerm` after retyping along the reified `Guard` endpoint conversion + `Conv.app` +
     `Conv.iota`), proving in general why readback never needs the K converse (`ExactK`).

3. **Candidate-retaining (`StratifiedCandidates`) resolution of the two neutral-PER obstructions (§3)**:
   - `namedNeutralCode_separates_distinct_names`: resolves Obstruction 1
     (`neutralCodes_universe_collapses_distinct_names`) in `StratifiedCandidates.Code (k + 1)`
     by seeding each neutral type `.neutralType (some (k + 1)) name` with its name-specific
     spine relation `namedSpineRel k name`, so `r₁ ≠ r₂ ⟹ ¬ CodeRelated (k + 1) (namedNeutralCode k r₁) (namedNeutralCode k r₂)`.
   - `stratified_large_k_transport_resolves_obstruction`: resolves Obstruction 2
     (`inhabited_large_k_pi_domain_obstruction`) in `StratifiedCandidates.Code 1` by
     equipping both `reify (.neutralType (some 1) name)` and `EqLargeFixture.result` with
     the neutral-completed lifted `InductiveCodeControls.productPER` via `predicative 0`,
     yielding `CodeRelated 1 (largeKCallCode name) largeKResultCode` and
     `(universeCode 1).relation` despite `¬ ValueEq`.

No `sorry`, no `Classical.choice`, no `native_decide`, no new axioms.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.AdeqReadbackLaws

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralExtraction PairedStatements
open InductiveCodes AdeqRelation AdeqNeutralObstructions

/-! ## §1 Sort-Level Equality, Annotated `ExprA` Π-Inversion, and Erasure to Native `ConvT` -/

/-- Whenever two sort-typed native expressions `Γ ⊢ X : .sort u` and `Γ ⊢ Y : .sort u'`
have `RelatedCode`-related images at `nativeGeneric S ν Γ` for all valuations `ν`,
`NativePairedFundamental` and `NativeNeutralSupport` imply `eqN u u'`. -/
theorem eqN_of_nativeRelatedCode_sorts {M : NativeSemantics} {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n) (S : NativeNeutralSupport M)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y : Expr Nat} {u u' : Level}
    (hrel : ∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (nativeGeneric S ν Γ) X)
        (M.image ν Γ (nativeGeneric S ν Γ) Y))
    (hX : HasTyT E n Γ X (.sort u))
    (hY : HasTyT E n Γ Y (.sort u')) :
    eqN u u' := by
  intro ν
  have hMem := native_membership_of_paired S hF hW
  obtain ⟨hSortX, hDefX⟩ := hMem ν Γ X u hΓ hX
  obtain ⟨hSortY, hDefY⟩ := hMem ν Γ Y u' hΓ hY
  obtain ⟨k, R, T, hc⟩ := hrel ν
  have hkX : eval ν u = k :=
    sortMember_unique hSortX (M.level hc.left_code) hDefX
  have hkY : k = eval ν u' :=
    sortMember_unique (M.level hc.right_code) hSortY hDefY
  exact hkX.trans hkY

/-- Sort-level equality from `NativeSemTypeRel` on sort-typed native expressions. -/
theorem eqN_of_nativeSemTypeRel_sorts {M : NativeSemantics} {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n) (S : NativeNeutralSupport M)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y : Expr Nat} {u u' : Level}
    (hrel : NativeSemTypeRel M S Γ X Y)
    (hX : HasTyT E n Γ X (.sort u))
    (hY : HasTyT E n Γ Y (.sort u')) :
    eqN u u' := by
  rcases hrel with rfl | hsem
  · exact native_sortUniq_of_paired S hF hW hΓ hX hY
  · exact eqN_of_nativeRelatedCode_sorts hW hF S hΓ hsem hX hY

/-- Annotated counterpart: whenever `Γ ⊢ X : .sort u` and `Γ ⊢ Y : .sort u'` have
`RelatedCode`-related images at `generic S ν Γ` for all `ν`, `PairedFundamental` and
`NeutralSupport` imply `eqN u u'`. -/
theorem eqN_of_annRelatedCode_sorts {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (S : NeutralSupport M) (hF : PairedFundamental M E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {X Y : ExprA} {u u' : Level}
    (hrel : ∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (generic S ν Γ) X)
        (M.image ν Γ (generic S ν Γ) Y))
    (hX : HasTyA E I n Γ X (.sort u))
    (hY : HasTyA E I n Γ Y (.sort u')) :
    eqN u u' := by
  intro ν
  have hMem := ann_membership_of_paired S hF
  obtain ⟨hSortX, hDefX⟩ := hMem ν Γ X u hΓ hX
  obtain ⟨hSortY, hDefY⟩ := hMem ν Γ Y u' hΓ hY
  obtain ⟨k, R, T, hc⟩ := hrel ν
  have hkX : eval ν u = k :=
    sortMember_unique hSortX (M.level hc.left_code) hDefX
  have hkY : k = eval ν u' :=
    sortMember_unique (M.level hc.right_code) hSortY hDefY
  exact hkX.trans hkY

/-- Sort-level equality from `AnnSemTypeRel` on sort-typed annotated expressions. -/
theorem eqN_of_annSemTypeRel_sorts {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (S : NeutralSupport M) (hF : PairedFundamental M E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {X Y : ExprA} {u u' : Level}
    (hrel : AnnSemTypeRel M S Γ X Y)
    (hX : HasTyA E I n Γ X (.sort u))
    (hY : HasTyA E I n Γ Y (.sort u')) :
    eqN u u' := by
  rcases hrel with rfl | hsem
  · exact ann_sortUniq_of_paired S hF hΓ hX hY
  · exact eqN_of_annRelatedCode_sorts S hF hΓ hsem hX hY

/-- Annotated Π-inversion from adequacy: given `PairedFundamental`, `NeutralSupport`,
`AnnSemPiInj`, and `AnnTypeReadback`, any two well-typed annotated Π types `.pi A u B v`
and `.pi A' u' B' v'` related by `AnnSemTypeRel` have `=ₙ` domain/codomain sort annotations
and `ConvA`-convertible (hence `TyConvA`-convertible) domains and codomains. -/
theorem annPiInj_of_adequacy {M : AnnSemantics} {S : NeutralSupport M}
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hF : PairedFundamental M E I n)
    (hPi : AnnSemPiInj M S E I n)
    (hReify : AnnTypeReadback M S E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A B A' B' T₀ T₁ : ExprA} {u v u' v' : Level}
    (hpiL : HasTyA E I n Γ (.pi A u B v) T₀)
    (hpiR : HasTyA E I n Γ (.pi A' u' B' v') T₁)
    (hsem : AnnSemTypeRel M S Γ (.pi A u B v) (.pi A' u' B' v')) :
    eqN u u' ∧ eqN v v' ∧
      Nonempty (ConvA E I n Γ A A' (.sort u)) ∧
      Nonempty (ConvA E I n (.assumption A :: Γ) B B' (.sort v)) ∧
      Nonempty (TyConvA E I n Γ A A') ∧
      Nonempty (TyConvA E I n (.assumption A :: Γ) B B') := by
  obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts hpiL
  obtain ⟨hA'u', hB'v'⟩ := hasTyA_pi_parts hpiR
  rcases hsem with heq | hrel
  · injection heq with hAA' huu' hBB' hvv'
    subst hAA'; subst huu'; subst hBB'; subst hvv'
    exact ⟨eqNA_refl u, eqNA_refl v,
      ⟨.refl Γ A (.sort u) hAu⟩,
      ⟨.refl (.assumption A :: Γ) B (.sort v) hBv⟩,
      ⟨.refl Γ A⟩,
      ⟨.refl (.assumption A :: Γ) B⟩⟩
  · obtain ⟨hdom, hcod⟩ := hPi.piInj hΓ hrel
    have hu : eqN u u' := eqN_of_annRelatedCode_sorts S hF hΓ hdom hAu hA'u'
    obtain ⟨hconvA⟩ := hReify hΓ hdom hAu hA'u'
    have hA'u : HasTyA E I n Γ A' (.sort u) := hasTyA_sortEqN hA'u' (eqNA_symm hu)
    have hcc : CtxConvA E I n (.assumption A' :: Γ) (.assumption A :: Γ) :=
      .assumption (ctxConvA_refl Γ) ⟨hA'u⟩ ⟨hAu⟩ ⟨.symm Γ A A' (.sort u) hconvA⟩
    obtain ⟨hB'Γ⟩ := hasTyA_ctxConv hE hI hR hcc hB'v'
    have hΓA : CtxWfA E I n (.assumption A :: Γ) := .assumption hΓ hAu
    have hv : eqN v v' := eqN_of_annRelatedCode_sorts S hF hΓA hcod hBv hB'Γ
    obtain ⟨hconvB⟩ := hReify hΓA hcod hBv hB'Γ
    have hB'v : HasTyA E I n (.assumption A :: Γ) B' (.sort v) :=
      hasTyA_sortEqN hB'Γ (eqNA_symm hv)
    exact ⟨hu, hv, ⟨hconvA⟩, ⟨hconvB⟩,
      ⟨.of Γ A A' u u u hAu (eqNA_refl u) hA'u (eqNA_refl u) hconvA⟩,
      ⟨.of (.assumption A :: Γ) B B' v v v hBv (eqNA_refl v) hB'v (eqNA_refl v) hconvB⟩⟩

/-- Specialisation of `annPiInj_of_adequacy` to a `TyConvA` chain between two well-typed
annotated Π types. -/
theorem annPiInj_of_tyConvA {M : AnnSemantics} {S : NeutralSupport M}
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hF : PairedFundamental M E I n) (U : UniverseTransport M.toCodeSystem)
    (hPi : AnnSemPiInj M S E I n)
    (hReify : AnnTypeReadback M S E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A B A' B' T₀ T₁ : ExprA} {u v u' v' : Level}
    (hpiL : HasTyA E I n Γ (.pi A u B v) T₀)
    (hpiR : HasTyA E I n Γ (.pi A' u' B' v') T₁)
    (h : TyConvA E I n Γ (.pi A u B v) (.pi A' u' B' v')) :
    eqN u u' ∧ eqN v v' ∧
      Nonempty (ConvA E I n Γ A A' (.sort u)) ∧
      Nonempty (ConvA E I n (.assumption A :: Γ) B B' (.sort v)) ∧
      Nonempty (TyConvA E I n Γ A A') ∧
      Nonempty (TyConvA E I n (.assumption A :: Γ) B B') :=
  annPiInj_of_adequacy hE hI hR hF hPi hReify hΓ hpiL hpiR
    (annSemTypeRel_of_tyConvA hF U S hΓ h)

/-- Erasing the annotated Π-component conversions from `annPiInj_of_adequacy` via
`convT_of_convA` and `tyConvT_of_tyConvA` (`RcicAnnErase`) produces native `ConvT` and
`TyConvT` component conversions in `eraseEnv E` and `eraseCtx Γ`. -/
theorem erasedPiComponents_of_annAdequacy {M : AnnSemantics} {S : NeutralSupport M}
    {J : IotaIfaceA} {E : ResolvedEnvA} {n : Nat}
    (hW : EnvWfA J E) (hNS : IotaErasesA E)
    (hF : PairedFundamental M E (iotaIfaceA E) n)
    (U : UniverseTransport M.toCodeSystem)
    (hPi : AnnSemPiInj M S E (iotaIfaceA E) n)
    (hReify : AnnTypeReadback M S E (iotaIfaceA E) n)
    {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {A B A' B' T₀ T₁ : ExprA} {u v u' v' : Level}
    (hpiL : HasTyA E (iotaIfaceA E) n Γ (.pi A u B v) T₀)
    (hpiR : HasTyA E (iotaIfaceA E) n Γ (.pi A' u' B' v') T₁)
    (h : TyConvA E (iotaIfaceA E) n Γ (.pi A u B v) (.pi A' u' B' v')) :
    Nonempty (ConvT (eraseEnv E) n (eraseCtx Γ) (erase A) (erase A') (.sort u)) ∧
      Nonempty (ConvT (eraseEnv E) n (.assumption (erase A) :: eraseCtx Γ)
        (erase B) (erase B') (.sort v)) ∧
      Nonempty (TyConvT (eraseEnv E) n (eraseCtx Γ) (erase A) (erase A')) ∧
      Nonempty (TyConvT (eraseEnv E) n (.assumption (erase A) :: eraseCtx Γ)
        (erase B) (erase B')) := by
  have hE : EnvClosedA E := envWfA_closed hW
  have hEN : EnvNormClosedA E := envWfA_normClosed hW
  have hI : IotaLiftA (iotaIfaceA E) := iotaFnA_lift hE hEN
  have hR : IotaRecHeadTypedA E (iotaIfaceA E) := iotaRecHeadTypedA_of (iotaFnA_recHead E)
  obtain ⟨_, _, ⟨hcA⟩, ⟨hcB⟩, ⟨htA⟩, ⟨htB⟩⟩ :=
    annPiInj_of_tyConvA hE hI hR hF U hPi hReify hΓ hpiL hpiR h
  exact ⟨convT_of_convA hW hNS hcA,
    convT_of_convA hW hNS hcB,
    tyConvT_of_tyConvA hW hNS htA,
    tyConvT_of_tyConvA hW hNS htB⟩

/-! ## §2 Kripke-Glued Term & Neutral Spine Readback Combinators (CCFMLMW §§2.6–2.8) -/

/-- Native Π-type reification: reified domain conversion at `Γ` and reified codomain
conversion at `.assumption A :: Γ` (evaluated at the reflected variable `.bvar 0`) assemble
via `ConvT.pi` into a Π-type conversion at `.sort (.imax u v)`. -/
theorem reify_native_pi_type {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    Nonempty (ConvT E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))) :=
  ⟨.pi Γ A A' B B' u v hA hB⟩

/-- Annotated Π-type reification via `ConvA.pi`. -/
theorem reify_ann_pi_type {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {A A' B B' : ExprA} {u u' v v' : Level}
    (hu : eqN u u') (hv : eqN v v')
    (hA : ConvA E I n Γ A A' (.sort u))
    (hB : ConvA E I n (.assumption A :: Γ) B B' (.sort v))
    (hrt : HasTyA E I n Γ (.pi A' u' B' v') (.sort (.imax u v))) :
    Nonempty (ConvA E I n Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v))) :=
  ⟨.pi Γ A A' B B' u u' v v' hu hv hA hB hrt⟩

/-- Native Π-term readback via η-expansion at the reflected variable `.bvar 0`:
if `f, g : .pi A B` and applying the weakened functions `lift 0 1 f` and `lift 0 1 g`
to `.bvar 0` in `.assumption A :: Γ` reifies to `ConvT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) (.app (lift 0 1 g) (.bvar 0)) B`,
then `ConvT E n Γ f g (.pi A B)` follows by `ConvT.lam` and `ConvT.eta`. -/
theorem reify_native_pi_term_eta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g A B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hf : HasTyT E n Γ f (.pi A B))
    (hg : HasTyT E n Γ g (.pi A B))
    (happ : ConvT E n (.assumption A :: Γ)
      (.app (lift 0 1 f) (.bvar 0))
      (.app (lift 0 1 g) (.bvar 0)) B) :
    Nonempty (ConvT E n Γ f g (.pi A B)) := by
  have hlam : ConvT E n Γ
      (.lam A (.app (lift 0 1 f) (.bvar 0)))
      (.lam A (.app (lift 0 1 g) (.bvar 0))) (.pi A B) :=
    .lam Γ A A _ _ B u (.refl Γ A (.sort u) hA) happ
  have hetaF : ConvT E n Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) :=
    .symm Γ _ _ (.pi A B) (.eta Γ f A B hf)
  have hetaG : ConvT E n Γ (.lam A (.app (lift 0 1 g) (.bvar 0))) g (.pi A B) :=
    .eta Γ g A B hg
  exact ⟨.trans Γ _ _ _ (.pi A B) (.trans Γ _ _ _ (.pi A B) hetaF hlam) hetaG⟩

/-- Annotated Π-term readback via η-expansion at the reflected variable `.bvar 0`. -/
theorem reify_ann_pi_term_eta {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {f g A B : ExprA} {u v : Level}
    (hA : HasTyA E I n Γ A (.sort u))
    (hf : HasTyA E I n Γ f (.pi A u B v))
    (hg : HasTyA E I n Γ g (.pi A u B v))
    (hlamF : HasTyA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v))
    (hlamG : HasTyA E I n Γ (.lam A u (.app (liftA 0 1 g) (.bvar 0))) (.pi A u B v))
    (happ : ConvA E I n (.assumption A :: Γ)
      (.app (liftA 0 1 f) (.bvar 0))
      (.app (liftA 0 1 g) (.bvar 0)) B) :
    Nonempty (ConvA E I n Γ f g (.pi A u B v)) := by
  have hlam : ConvA E I n Γ
      (.lam A u (.app (liftA 0 1 f) (.bvar 0)))
      (.lam A u (.app (liftA 0 1 g) (.bvar 0))) (.pi A u B v) :=
    .lam Γ A A _ _ B u u v (eqNA_refl u) (.refl Γ A (.sort u) hA) happ hlamG
  have hetaF : ConvA E I n Γ f (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v) :=
    .symm Γ _ _ (.pi A u B v) (.eta Γ f A B u v hf hlamF)
  have hetaG : ConvA E I n Γ (.lam A u (.app (liftA 0 1 g) (.bvar 0))) g (.pi A u B v) :=
    .eta Γ g A B u v hg hlamG
  exact ⟨.trans Γ _ _ _ (.pi A u B v) (.trans Γ _ _ _ (.pi A u B v) hetaF hlam) hetaG⟩

/-- Neutral variable readback at a context lookup `lookupType Γ i = some A`. -/
theorem reify_native_bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType Γ i = some A) :
    Nonempty (ConvT E n Γ (.bvar i) (.bvar i) A) :=
  ⟨.refl Γ (.bvar i) A (.bvar Γ i A h)⟩

/-- Neutral constant readback from `eqNList ls ls'`. -/
theorem reify_native_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (heq : eqNList ls ls') :
    Nonempty (ConvT E n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype)) :=
  ⟨.consts Γ r ls ls' m hres hlen hwf hwf' heq⟩

/-- Neutral spine application congruence: reified head conversion and reified argument
conversion compose via `ConvT.app`. -/
theorem reify_native_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B))
    (ha : ConvT E n Γ a b A) :
    Nonempty (ConvT E n Γ (.app f a) (.app g b) (instantiate0 a B)) :=
  ⟨.app Γ f g a b A B hf ha⟩

/-- General syntactic readback of a forward `NeutralK.Seed.k` step on native `Expr Nat`:
given a partially applied recursor spine `recPrefix : .pi eqTy motive` where
`eqTy : .sort .zero`, a neutral major proof `p : eqTy`, the reflexivity constructor
`reflTerm : eqTy` (retyped along the reified `Guard` endpoint conversion), and a
`DerivedIota` step from `.app recPrefix reflTerm` to `minor`, the stuck call
`.app recPrefix p` converts to `minor` in two steps (`ConvT.irr` + `ConvT.app`, then
`ConvT.iota`), without any converse K (`ExactK`) premise. -/
theorem reify_native_forward_k_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {recPrefix eqTy motive p reflTerm minor : Expr Nat}
    (hEq : HasTyT E n Γ eqTy (.sort .zero))
    (hf : HasTyT E n Γ recPrefix (.pi eqTy motive))
    (hp : HasTyT E n Γ p eqTy)
    (hrefl : HasTyT E n Γ reflTerm eqTy)
    (hι : DerivedIota E (.app recPrefix reflTerm) minor)
    (hlhs : HasTyT E n Γ (.app recPrefix reflTerm) (instantiate0 p motive))
    (hrhs : HasTyT E n Γ minor (instantiate0 p motive)) :
    Nonempty (ConvT E n Γ (.app recPrefix p) minor (instantiate0 p motive)) := by
  have hirr : ConvT E n Γ p reflTerm eqTy := .irr Γ eqTy p reflTerm hEq hp hrefl
  have happ : ConvT E n Γ (.app recPrefix p) (.app recPrefix reflTerm) (instantiate0 p motive) :=
    .app Γ recPrefix recPrefix p reflTerm eqTy motive (.refl Γ recPrefix (.pi eqTy motive) hf) hirr
  have hiota : ConvT E n Γ (.app recPrefix reflTerm) minor (instantiate0 p motive) :=
    .iota Γ (.app recPrefix reflTerm) minor (instantiate0 p motive) hι hlhs hrhs
  exact ⟨.trans Γ _ _ _ (instantiate0 p motive) happ hiota⟩

/-- Annotated counterpart of `reify_native_forward_k_step` on `ConvA`. -/
theorem reify_ann_forward_k_step {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {recPrefix eqTy motive p reflTerm minor : ExprA} {v : Level}
    (hEq : HasTyA E I n Γ eqTy (.sort .zero))
    (hf : HasTyA E I n Γ recPrefix (.pi eqTy .zero motive v))
    (hB : HasTyA E I n (.assumption eqTy :: Γ) motive (.sort v))
    (hp : HasTyA E I n Γ p eqTy)
    (hrefl : HasTyA E I n Γ reflTerm eqTy)
    (hι : I.rel E Γ (.app recPrefix reflTerm) minor)
    (hlhs : HasTyA E I n Γ (.app recPrefix reflTerm) (instantiate0A p motive))
    (hrhs : HasTyA E I n Γ minor (instantiate0A p motive)) :
    Nonempty (ConvA E I n Γ (.app recPrefix p) minor (instantiate0A p motive)) := by
  have hirr : ConvA E I n Γ p reflTerm eqTy := .irr Γ eqTy p reflTerm hEq hp hrefl
  have happ : ConvA E I n Γ (.app recPrefix p) (.app recPrefix reflTerm) (instantiate0A p motive) :=
    .app Γ recPrefix recPrefix p reflTerm eqTy motive .zero v
      (.refl Γ recPrefix (.pi eqTy .zero motive v) hf) hirr hB hlhs
  have hiota : ConvA E I n Γ (.app recPrefix reflTerm) minor (instantiate0A p motive) :=
    .iota Γ (.app recPrefix reflTerm) minor (instantiate0A p motive) hι hlhs hrhs
  exact ⟨.trans Γ _ _ _ (instantiate0A p motive) happ hiota⟩

/-! ## §3 `StratifiedCandidates` Resolution of Both Neutral-PER Obstructions -/

/-- Name-specific spine relation on `StratifiedCandidates.Carrier (k + 1)` for a neutral
type named `name`: relates `.inl (neutralTypeValue (some (k + 1)) name)` to itself. -/
def namedSpineRel (k name : Nat) :
    StratifiedCandidates.Carrier (k + 1) → StratifiedCandidates.Carrier (k + 1) → Prop :=
  fun x y => x = y ∧ x = .inl (NeutralCodes.neutralTypeValue (some (k + 1)) name)

theorem namedSpineRel_laws (k name : Nat) :
    NeutralDataFamily.RelLaws (namedSpineRel k name) where
  symm := fun ⟨hxy, hx⟩ => ⟨hxy.symm, hxy.symm.trans hx⟩
  trans := fun ⟨hxy, hx⟩ ⟨hyz, _⟩ => ⟨hxy.trans hyz, hx⟩

/-- Name-sensitive neutral type code in `StratifiedCandidates.Code (k + 1)`. Unlike
`NeutralCodes.Descriptor.Related` (and `StratifiedCandidates.neutralCode`), which collapse
all neutral type names at a given universe level, `namedNeutralCode k name` retains
`namedSpineRel k name` inside `predicative k`. -/
def namedNeutralCode (k name : Nat) : StratifiedCandidates.Code (k + 1) :=
  StratifiedCandidates.predicative k
    (NeutralCodes.neutralTypeValue (some (k + 1)) name)
    (NeutralCodes.reify_level (.neutralType (some (k + 1)) name))
    (NeutralCodes.reify_defined (.neutralType (some (k + 1)) name))
    (namedSpineRel k name)
    (namedSpineRel_laws k name)

/-- `neutralTypeValue (some (k + 1)) name` is never a `RawNeutral (k + 1)`, because
`neutralTypeValue` satisfies `SortMember (some (k + 1))` whereas `neutralAtom` fails
`SortMember`. -/
theorem neutralTypeValue_not_rawNeutral (k name : Nat) :
    ¬ StratifiedCandidates.RawNeutral (k + 1)
        (.inl (NeutralCodes.neutralTypeValue (some (k + 1)) name)) := by
  rintro ⟨a, ha⟩
  have hval : NeutralCodes.neutralTypeValue (some (k + 1)) name = NeutralPER.neutralAtom a :=
    Sum.inl.inj ha
  have hsort : SortMember (some (k + 1)) (NeutralPER.neutralAtom a) := by
    rw [← hval]
    exact NeutralCodes.reify_level (.neutralType (some (k + 1)) name)
  exact NeutralPER.neutralAtom_not_sort_member a (some (k + 1)) hsort

/-- Resolution of Obstruction 1 (`neutralCodes_universe_collapses_distinct_names`) in
`StratifiedCandidates`: for any `k : Nat` and `r₁ ≠ r₂`, `namedNeutralCode k r₁` and
`namedNeutralCode k r₂` are valid `universeCode (k + 1)` members with distinct raw values,
and they are NOT `CodeRelated (k + 1)` (nor related in `(universeCode (k + 1)).relation`). -/
theorem namedNeutralCode_separates_distinct_names (k : Nat) {r₁ r₂ : Nat} (hne : r₁ ≠ r₂) :
    (StratifiedCandidates.universeCode (k + 1)).relation
      (StratifiedCandidates.encode (k + 1) (namedNeutralCode k r₁))
      (StratifiedCandidates.encode (k + 1) (namedNeutralCode k r₁)) ∧
    (StratifiedCandidates.universeCode (k + 1)).relation
      (StratifiedCandidates.encode (k + 1) (namedNeutralCode k r₂))
      (StratifiedCandidates.encode (k + 1) (namedNeutralCode k r₂)) ∧
    (¬ ValueEq (StratifiedCandidates.view (k + 1) (namedNeutralCode k r₁)).value
        (StratifiedCandidates.view (k + 1) (namedNeutralCode k r₂)).value) ∧
    (¬ StratifiedCandidates.CodeRelated (k + 1)
        (namedNeutralCode k r₁) (namedNeutralCode k r₂)) ∧
    (¬ (StratifiedCandidates.universeCode (k + 1)).relation
        (StratifiedCandidates.encode (k + 1) (namedNeutralCode k r₁))
        (StratifiedCandidates.encode (k + 1) (namedNeutralCode k r₂))) := by
  have hnotValEq : ¬ ValueEq (StratifiedCandidates.view (k + 1) (namedNeutralCode k r₁)).value
      (StratifiedCandidates.view (k + 1) (namedNeutralCode k r₂)).value := by
    intro heq
    have hd := NeutralCodes.reify_injective
      (d := .neutralType (some (k + 1)) r₁) (e := .neutralType (some (k + 1)) r₂) heq
    exact hne (NeutralCodes.Descriptor.neutralType.inj hd).2
  have hnotRel : ¬ StratifiedCandidates.CodeRelated (k + 1)
      (namedNeutralCode k r₁) (namedNeutralCode k r₂) := by
    intro hrel
    let x : StratifiedCandidates.Carrier (k + 1) :=
      .inl (NeutralCodes.neutralTypeValue (some (k + 1)) r₁)
    have hx₁ : (namedNeutralCode k r₁).relation x x := Or.inl ⟨rfl, rfl⟩
    have hx₂ : (namedNeutralCode k r₂).relation x x := (hrel.transport x x).mp hx₁
    rcases hx₂ with ⟨_, heq⟩ | ⟨_, hraw⟩
    · have hv : ValueEq (NeutralCodes.neutralTypeValue (some (k + 1)) r₁)
          (NeutralCodes.neutralTypeValue (some (k + 1)) r₂) := by
        rw [Sum.inl.inj heq]
        exact ValueEq.refl _
      exact hnotValEq hv
    · exact neutralTypeValue_not_rawNeutral k r₁ hraw
  exact ⟨StratifiedCandidates.universe_member (k + 1) (namedNeutralCode k r₁),
    StratifiedCandidates.universe_member (k + 1) (namedNeutralCode k r₂),
    hnotValEq, hnotRel, hnotRel⟩

/-- Lifted `InductiveCodeControls.productPER` on `StratifiedCandidates.Carrier 1`. -/
def erasedProductRel : StratifiedCandidates.Carrier 1 → StratifiedCandidates.Carrier 1 → Prop :=
  fun x y => InductiveCodeControls.productPER
    (StratifiedCandidates.erase 1 x) (StratifiedCandidates.erase 1 y)

theorem erasedProductRel_laws : NeutralDataFamily.RelLaws erasedProductRel := by
  have hLaws := InductiveCodes.code_laws InductiveCodeControls.product_source_code
  exact ⟨fun h => hLaws.symm h, fun h g => hLaws.trans h g⟩

/-- Candidate-retaining `StratifiedCandidates.Code 1` for `EqLargeFixture.result`,
equipped with the neutral-completed `erasedProductRel`. -/
def largeKResultCode : StratifiedCandidates.Code 1 :=
  StratifiedCandidates.predicative 0
    (UnitModel.denote InductiveCodeControls.zeroValuation EnvI.bot EqLargeFixture.result)
    (InductiveCodes.code_level InductiveCodeControls.product_source_code)
    (InductiveCodes.code_defined InductiveCodeControls.product_source_code)
    erasedProductRel
    erasedProductRel_laws

/-- Candidate-retaining `StratifiedCandidates.Code 1` for the guarded large-K neutral
type value `reify (.neutralType (some 1) name)` transporting `erasedProductRel` across
the forward `Seed.k` edge. -/
def largeKCallCode (name : Nat) : StratifiedCandidates.Code 1 :=
  StratifiedCandidates.predicative 0
    (NeutralCodes.reify (.neutralType (some 1) name))
    (NeutralCodes.reify_level (.neutralType (some 1) name))
    (NeutralCodes.reify_defined (.neutralType (some 1) name))
    erasedProductRel
    erasedProductRel_laws

/-- Resolution of Obstruction 2 (`inhabited_large_k_pi_domain_obstruction`) in
`StratifiedCandidates`: when the guarded large-K neutral type value
`reify (.neutralType (some 1) name)` retains the minor's candidate PER
`Extend erasedProductRel (RawNeutral 1)` in `StratifiedCandidates.Code 1`,
`largeKCallCode name` and `largeKResultCode` have distinct raw values (`¬ ValueEq`),
contain all level-1 reflected neutrals `raw 1 (neutralAtom a)`, preserve
`InductiveCodeControls.productPER`, AND satisfy `CodeRelated 1` and
`(universeCode 1).relation`. -/
theorem stratified_large_k_transport_resolves_obstruction (name : Nat) :
    (StratifiedCandidates.view 1 (largeKCallCode name)).value =
      NeutralCodes.reify (.neutralType (some 1) name) ∧
    (StratifiedCandidates.view 1 largeKResultCode).value =
      UnitModel.denote InductiveCodeControls.zeroValuation EnvI.bot EqLargeFixture.result ∧
    (¬ ValueEq (StratifiedCandidates.view 1 (largeKCallCode name)).value
        (StratifiedCandidates.view 1 largeKResultCode).value) ∧
    (∀ a : Nat, (largeKCallCode name).relation
      (StratifiedCandidates.raw 1 (NeutralPER.neutralAtom a))
      (StratifiedCandidates.raw 1 (NeutralPER.neutralAtom a))) ∧
    (∀ a : Nat, largeKResultCode.relation
      (StratifiedCandidates.raw 1 (NeutralPER.neutralAtom a))
      (StratifiedCandidates.raw 1 (NeutralPER.neutralAtom a))) ∧
    StratifiedCandidates.CodeRelated 1 (largeKCallCode name) largeKResultCode ∧
    (StratifiedCandidates.universeCode 1).relation
      (StratifiedCandidates.encode 1 (largeKCallCode name))
      (StratifiedCandidates.encode 1 largeKResultCode) := by
  have hnotValEq : ¬ ValueEq (StratifiedCandidates.view 1 (largeKCallCode name)).value
      (StratifiedCandidates.view 1 largeKResultCode).value := by
    intro heq
    exact old_code_not_pi (NeutralCodes.code (.neutralType (some 1) name))
      (old_code_bot (NeutralCodes.code_universe (some 0)))
      (heq.trans InductiveCodeControls.product_image)
  have hRel : StratifiedCandidates.CodeRelated 1 (largeKCallCode name) largeKResultCode :=
    ⟨fun _ _ => Iff.rfl, fun a => (largeKCallCode name).point_member a⟩
  exact ⟨rfl, rfl, hnotValEq,
    fun a => (largeKCallCode name).point_member a,
    fun a => largeKResultCode.point_member a,
    hRel, hRel⟩

end Rcic.Declarative.Ann.LR3.AdeqReadbackLaws
