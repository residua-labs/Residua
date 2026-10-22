import rcic.RcicPiRowLiftNat
import rcic.RcicAnnLR3EnvironmentLambdaArms

/-!
# Adequacy (glued readback) interface for `TypedRowsWf.piRow` and `CodeI` Π-inversion

This module designs and kernel-checks the generic adequacy / readback bridge from the
`RcicAnnLR3*` paired PER model to syntactic Π-injectivity (`TypedRowsWf.piRow` on native
`Expr Nat`, and annotated Π component conversion on `ExprA`), following the adequacy
architecture of Carneiro–Coquand–Frabetti Mathieu–Lennon-Bertrand–Melliès–Weirich,
"Definitional Inversion, Without Normalisation" (arXiv:2607.13662, §§2.6–2.8) adapted to
RCIC's paired PER semantics.

## Architectural Decomposition

1. **Native adequacy factorisation through `RcicPiRowLiftNat` (`Expr Nat`)**:
   - `NativeSemTypeRel M S Γ X Y`: two native types are semantically related at the
     generic reflected environment `nativeGeneric S ν Γ` (with explicit reflexive
     allowance for the untyped `TyConvT.refl` edge required by `no_piRowInjT_of_envWfT`).
   - `erasedRowsAt_of_nativePairedFundamental`: from `NativePairedFundamental M E n`,
     `UniverseTransport M.toCodeSystem`, `S : NativeNeutralSupport M`, and semantic
     Π-injectivity `NativeSemPiInj M S E n`, we discharge `ErasedRowsAt E n (NativeSemTypeRel M S)`.
     Crucially, `nativeGeneric S ν (.assumption A :: Γ)` extends `nativeGeneric S ν Γ`
     by the reflected neutral `S.reflect (M.image ν Γ ρ A) Γ.length`, aligning semantic
     codomain fibre evaluation with syntactic context extension `.assumption A :: Γ`.
   - `liftNatAt_of_nativeTypeReadback`: from `NativeTypeReadback M S E n` (reifying
     `RelatedCode` at the generic environment to `ConvT E n Γ X Y (.sort u)` when both
     types are sort-typed), we discharge `LiftNatAt E n (NativeSemTypeRel M S)`.
   - `piRow_of_nativeAdequacy` and `piRowInjTyped_of_nativeAdequacy`: compose the two
     half-bridges with `RcicPiRowLiftNat.piRow_of_liftNat` to obtain `TypedRowsWf.piRow`.

2. **Annotated adequacy and concrete `CodeI` semantic Π-injectivity (`ExprA`)**:
   - `AnnSemTypeRel M S Γ X Y`, `annSemTypeRel_of_convA`, `annSemTypeRel_of_tyConvA`,
     and `annPiComponents_of_adequacy` provide the annotated (`ExprA`) counterpart
     directly consuming `PairedFundamental M E I n`.
   - `codeI_pi_valueEq_injective` and `environmentEval_pi_injective_of_valueEq` prove
     concrete semantic Π-injectivity for `InductiveCodes.CodeI` and
     `EnvironmentEval.denote`: two `CodeI`-coded Π types with `ValueEq` images have
     `RelatedCode`-related domains and `RelatedCode`-related codomains at every pair of
     domain-related arguments (in particular, at any reflected neutral member).

3. **Glued adequacy relation (`NativeGluedTypeSemantics` / `AnnGluedTypeSemantics`)**:
   - Packages the CCFMLMW glued type-level adequacy relation coupling semantic
     `RelatedCode` with syntactic sort-level `ConvT` / `ConvA`, where type readback is
     an immediate projection (`nativeTypeReadback_of_glued`).

No `sorry`, no `Classical.choice`, no `native_decide`, no new axioms.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.AdeqRelation

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralExtraction PairedStatements InductiveCodes

/-! ## §1 Native Adequacy Factorisation through `ErasedRowsAt` and `LiftNatAt` -/

/-- Unfolding law for `nativeGeneric` at an assumption binder: extending the syntactic
context with `.assumption A` pushes the reflected neutral at fresh level `Γ.length`
onto the generic semantic environment. -/
theorem nativeGeneric_assumption {M : NativeSemantics} (S : NativeNeutralSupport M)
    (ν : Valuation) (Γ : LCtx) (A : Expr Nat) :
    nativeGeneric S ν (.assumption A :: Γ) =
      EnvI.cons (S.reflect (M.image ν Γ (nativeGeneric S ν Γ) A) Γ.length)
        (nativeGeneric S ν Γ) := rfl

/-- Unfolding law for `nativeGeneric` at a let-binding: extending the syntactic context
with `.letBinding A v` pushes the semantic image of `v` onto the generic environment. -/
theorem nativeGeneric_letBinding {M : NativeSemantics} (S : NativeNeutralSupport M)
    (ν : Valuation) (Γ : LCtx) (A v : Expr Nat) :
    nativeGeneric S ν (.letBinding A v :: Γ) =
      EnvI.cons (M.image ν Γ (nativeGeneric S ν Γ) v)
        (nativeGeneric S ν Γ) := rfl

/-- Native paired judgment at a sort yields `RelatedCode` of the two type images
once `UniverseTransport` is supplied. -/
theorem NativePairedJudgment.related_types {M : NativeSemantics} {ν μ : Valuation}
    {Γ : LCtx} {ρ σ : EnvI} {A B : Expr Nat} {u : Level}
    (U : UniverseTransport M.toCodeSystem)
    (h : NativePairedJudgment M ν μ Γ ρ σ A B (.sort u)) :
    RelatedCode M.toCodeSystem (M.image ν Γ ρ A) (M.image μ Γ σ B) := by
  obtain ⟨l, R, S, hc, hr⟩ := h
  have hcode : M.Code l (universeValue (eval ν u)) R := by
    simpa only [M.sort_image] using hc.left_code
  have hu : M.universePER (eval ν u) (M.image ν Γ ρ A) (M.image μ Γ σ B) :=
    (M.coherent hcode (M.universe_code _) _ _).mp hr
  obtain ⟨T, V, ht⟩ := U.relate hu
  exact ⟨eval ν u, T, V, ht⟩

/-- Generic semantic type relation on native `Expr Nat` induced by a paired model `M`
and neutral support `S`. The left disjunct `X = Y` accommodates untyped `TyConvT.refl` chains,
while the right disjunct asserts `RelatedCode` at `nativeGeneric S ν Γ` for all valuations `ν`. -/
def NativeSemTypeRel (M : NativeSemantics) (S : NativeNeutralSupport M)
    (Γ : LCtx) (X Y : Expr Nat) : Prop :=
  X = Y ∨
    ∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (nativeGeneric S ν Γ) X)
        (M.image ν Γ (nativeGeneric S ν Γ) Y)

theorem nativeSemTypeRel_refl (M : NativeSemantics) (S : NativeNeutralSupport M)
    (Γ : LCtx) (X : Expr Nat) : NativeSemTypeRel M S Γ X X :=
  Or.inl rfl

theorem nativeSemTypeRel_symm {M : NativeSemantics} {S : NativeNeutralSupport M}
    {Γ : LCtx} {X Y : Expr Nat} (h : NativeSemTypeRel M S Γ X Y) :
    NativeSemTypeRel M S Γ Y X := by
  rcases h with rfl | hrel
  · exact Or.inl rfl
  · exact Or.inr (fun ν => (hrel ν).symm)

theorem nativeSemTypeRel_trans {M : NativeSemantics} {S : NativeNeutralSupport M}
    {Γ : LCtx} {X Y Z : Expr Nat}
    (hXY : NativeSemTypeRel M S Γ X Y) (hYZ : NativeSemTypeRel M S Γ Y Z) :
    NativeSemTypeRel M S Γ X Z := by
  rcases hXY with rfl | hrelXY
  · exact hYZ
  · rcases hYZ with rfl | hrelYZ
    · exact Or.inr hrelXY
    · exact Or.inr (fun ν => (hrelXY ν).trans (hrelYZ ν))

/-- Every single sort-level `ConvT` step is sound for `NativeSemTypeRel` under
`NativePairedFundamental` and `UniverseTransport`. -/
theorem nativeSemTypeRel_of_convT {M : NativeSemantics} {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n)
    (U : UniverseTransport M.toCodeSystem) (S : NativeNeutralSupport M)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y : Expr Nat} {u : Level}
    (hc : ConvT E n Γ X Y (.sort u)) :
    NativeSemTypeRel M S Γ X Y := by
  refine Or.inr (fun ν => ?_)
  have hρ := native_generic_self_related S hF hW ν Γ hΓ
  have hJ := (hF hW).2 hΓ hc ν ν (nativeGeneric S ν Γ) (nativeGeneric S ν Γ)
    (ValuationRel.refl ν) hρ
  exact NativePairedJudgment.related_types U hJ

/-- Every `TyConvT` chain is sound for `NativeSemTypeRel` under
`NativePairedFundamental` and `UniverseTransport`. -/
theorem nativeSemTypeRel_of_tyConvT {M : NativeSemantics} {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n)
    (U : UniverseTransport M.toCodeSystem) (S : NativeNeutralSupport M)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y : Expr Nat}
    (h : TyConvT E n Γ X Y) :
    NativeSemTypeRel M S Γ X Y := by
  induction h with
  | refl _ => exact nativeSemTypeRel_refl M S _ _
  | of _ _ _ hc => exact nativeSemTypeRel_of_convT hW hF U S hΓ hc
  | trans _ _ _ _ _ ih1 ih2 => exact nativeSemTypeRel_trans ih1 ih2

/-- Semantic Π-injectivity at the generic reflected environment: if `.pi A B` and
`.pi A' B'` have related codes at `nativeGeneric S ν Γ`, then their domains `A` and `A'`
have related codes at `nativeGeneric S ν Γ`, and their codomains `B` and `B'` have
related codes at `nativeGeneric S ν (.assumption A :: Γ)` (which pushes the reflected
neutral `S.reflect (M.image ν Γ ρ A) Γ.length`). -/
structure NativeSemPiInj (M : NativeSemantics) (S : NativeNeutralSupport M)
    (E : ResolvedEnv) (n : Nat) : Prop where
  piInj : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (nativeGeneric S ν Γ) (.pi A B))
        (M.image ν Γ (nativeGeneric S ν Γ) (.pi A' B'))) →
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (nativeGeneric S ν Γ) A)
        (M.image ν Γ (nativeGeneric S ν Γ) A')) ∧
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν (.assumption A :: Γ) (nativeGeneric S ν (.assumption A :: Γ)) B)
        (M.image ν (.assumption A :: Γ) (nativeGeneric S ν (.assumption A :: Γ)) B'))

/-- `NativePairedFundamental` + `UniverseTransport` + `NativeSemPiInj` discharges the
`ErasedRowsAt` premise of `RcicPiRowLiftNat.piRow_of_liftNat`. -/
theorem erasedRowsAt_of_nativePairedFundamental {M : NativeSemantics}
    {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n)
    (U : UniverseTransport M.toCodeSystem) (S : NativeNeutralSupport M)
    (hPi : NativeSemPiInj M S E n) :
    ErasedRowsAt E n (NativeSemTypeRel M S) where
  es := fun {_} hΓ {_ _} h => nativeSemTypeRel_of_tyConvT hW hF U S hΓ h
  piInj := by
    intro Γ hΓ A B A' B' h
    rcases h with heq | hrel
    · injection heq with hA hB
      subst hA; subst hB
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨hdom, hcod⟩ := hPi.piInj hΓ hrel
      exact ⟨Or.inr hdom, Or.inr hcod⟩

/-- Type-level readback (reification) obligation for native `Expr Nat`: whenever two
sort-typed expressions `X` and `Y` denote `RelatedCode`-related type values at the
generic reflected environment `nativeGeneric S ν Γ`, they are syntactically convertible
at the left sort (`ConvT E n Γ X Y (.sort u)`). -/
def NativeTypeReadback (M : NativeSemantics) (S : NativeNeutralSupport M)
    (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {X Y : Expr Nat} {u u' : Level},
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (nativeGeneric S ν Γ) X)
        (M.image ν Γ (nativeGeneric S ν Γ) Y)) →
    HasTyT E n Γ X (.sort u) → HasTyT E n Γ Y (.sort u') →
    Nonempty (ConvT E n Γ X Y (.sort u))

/-- `NativeTypeReadback` immediately discharges `LiftNatAt E n (NativeSemTypeRel M S)`. -/
theorem liftNatAt_of_nativeTypeReadback {M : NativeSemantics}
    {S : NativeNeutralSupport M} {E : ResolvedEnv} {n : Nat}
    (hReify : NativeTypeReadback M S E n) :
    LiftNatAt E n (NativeSemTypeRel M S) := by
  intro Γ hΓ X Y u u' hrel hX hY
  rcases hrel with rfl | hsem
  · exact ⟨.refl Γ X (.sort u) hX⟩
  · exact hReify hΓ hsem hX hY

/-- Main native adequacy reduction: `NativePairedFundamental` + `UniverseTransport` +
`NativeSemPiInj` + `NativeTypeReadback` yields `TypedRowsWf.piRow`. -/
theorem piRow_of_nativeAdequacy {M : NativeSemantics} {S : NativeNeutralSupport M}
    {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n)
    (U : UniverseTransport M.toCodeSystem)
    (hPi : NativeSemPiInj M S E n)
    (hReify : NativeTypeReadback M S E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_liftNat hW
    (erasedRowsAt_of_nativePairedFundamental hW hF U S hPi)
    (liftNatAt_of_nativeTypeReadback hReify)

/-- Typed-input strong form of `piRow` from native adequacy. -/
def piRowInjTyped_of_nativeAdequacy {M : NativeSemantics} {S : NativeNeutralSupport M}
    {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hF : NativePairedFundamental M E n)
    (U : UniverseTransport M.toCodeSystem)
    (hPi : NativeSemPiInj M S E n)
    (hReify : NativeTypeReadback M S E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A' B' T₀ : Expr Nat}
    (hpi : HasTyT E n Γ (.pi A B) T₀)
    (h : TyConvT E n Γ (.pi A B) (.pi A' B')) :
    Σ' (u v : Level), Nonempty (ConvT E n Γ A A' (.sort u)) ×'
      Nonempty (ConvT E n (.assumption A :: Γ) B B' (.sort v)) :=
  piRowInjTyped_of_liftNat hW
    (erasedRowsAt_of_nativePairedFundamental hW hF U S hPi)
    (liftNatAt_of_nativeTypeReadback hReify) hΓ hpi h

/-! ## §2 Annotated Adequacy (`ExprA`) and Concrete `CodeI` Semantic Π-Injectivity -/

/-- Unfolding law for annotated `generic` at an assumption binder. -/
theorem generic_assumption {M : AnnSemantics} (S : NeutralSupport M)
    (ν : Valuation) (Γ : LCtxA) (A : ExprA) :
    generic S ν (.assumption A :: Γ) =
      EnvI.cons (S.reflect (M.image ν Γ (generic S ν Γ) A) Γ.length)
        (generic S ν Γ) := rfl

/-- Generic semantic type relation on annotated `ExprA`. -/
def AnnSemTypeRel (M : AnnSemantics) (S : NeutralSupport M)
    (Γ : LCtxA) (X Y : ExprA) : Prop :=
  X = Y ∨
    ∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (generic S ν Γ) X)
        (M.image ν Γ (generic S ν Γ) Y)

theorem annSemTypeRel_refl (M : AnnSemantics) (S : NeutralSupport M)
    (Γ : LCtxA) (X : ExprA) : AnnSemTypeRel M S Γ X X :=
  Or.inl rfl

theorem annSemTypeRel_symm {M : AnnSemantics} {S : NeutralSupport M}
    {Γ : LCtxA} {X Y : ExprA} (h : AnnSemTypeRel M S Γ X Y) :
    AnnSemTypeRel M S Γ Y X := by
  rcases h with rfl | hrel
  · exact Or.inl rfl
  · exact Or.inr (fun ν => (hrel ν).symm)

theorem annSemTypeRel_trans {M : AnnSemantics} {S : NeutralSupport M}
    {Γ : LCtxA} {X Y Z : ExprA}
    (hXY : AnnSemTypeRel M S Γ X Y) (hYZ : AnnSemTypeRel M S Γ Y Z) :
    AnnSemTypeRel M S Γ X Z := by
  rcases hXY with rfl | hrelXY
  · exact hYZ
  · rcases hYZ with rfl | hrelYZ
    · exact Or.inr hrelXY
    · exact Or.inr (fun ν => (hrelXY ν).trans (hrelYZ ν))

/-- Annotated `ConvA` at a sort yields `AnnSemTypeRel` under `PairedFundamental`
and `UniverseTransport`. -/
theorem annSemTypeRel_of_convA {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental M E I n) (U : UniverseTransport M.toCodeSystem)
    (S : NeutralSupport M) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {X Y : ExprA} {u : Level} (hc : ConvA E I n Γ X Y (.sort u)) :
    AnnSemTypeRel M S Γ X Y := by
  refine Or.inr (fun ν => ?_)
  have hρ := generic_self_related S hF ν Γ hΓ
  have hJ := hF.2 hc hΓ ν ν (generic S ν Γ) (generic S ν Γ) (ValuationRel.refl ν) hρ
  exact PairedJudgment.related_types U hJ

/-- Annotated `TyConvA` chain yields `AnnSemTypeRel` under `PairedFundamental`
and `UniverseTransport`. -/
theorem annSemTypeRel_of_tyConvA {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental M E I n) (U : UniverseTransport M.toCodeSystem)
    (S : NeutralSupport M) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {X Y : ExprA} (h : TyConvA E I n Γ X Y) :
    AnnSemTypeRel M S Γ X Y := by
  induction h with
  | refl _ => exact annSemTypeRel_refl M S _ _
  | of _ _ _ _ _ _ _ _ _ hc => exact annSemTypeRel_of_convA hF U S hΓ hc
  | trans _ _ _ _ _ ih1 ih2 => exact annSemTypeRel_trans ih1 ih2

/-- Annotated semantic Π-injectivity at the generic reflected environment. -/
structure AnnSemPiInj (M : AnnSemantics) (S : NeutralSupport M)
    (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop where
  piInj : ∀ {Γ : LCtxA}, CtxWfA E I n Γ → ∀ {A B A' B' : ExprA} {u v u' v' : Level},
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (generic S ν Γ) (.pi A u B v))
        (M.image ν Γ (generic S ν Γ) (.pi A' u' B' v'))) →
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (generic S ν Γ) A)
        (M.image ν Γ (generic S ν Γ) A')) ∧
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν (.assumption A :: Γ) (generic S ν (.assumption A :: Γ)) B)
        (M.image ν (.assumption A :: Γ) (generic S ν (.assumption A :: Γ)) B'))

/-- Annotated type readback obligation: `RelatedCode` at `generic S ν Γ` reifies to
`ConvA E I n Γ X Y (.sort u)` when both endpoints are sort-typed. -/
def AnnTypeReadback (M : AnnSemantics) (S : NeutralSupport M)
    (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ {Γ : LCtxA}, CtxWfA E I n Γ → ∀ {X Y : ExprA} {u u' : Level},
    (∀ ν : Valuation,
      RelatedCode M.toCodeSystem
        (M.image ν Γ (generic S ν Γ) X)
        (M.image ν Γ (generic S ν Γ) Y)) →
    HasTyA E I n Γ X (.sort u) → HasTyA E I n Γ Y (.sort u') →
    Nonempty (ConvA E I n Γ X Y (.sort u))

/-- Concrete semantic Π-injectivity for `InductiveCodes.CodeI`: if two Π values
`piValue l₁ A₁ C₁` and `piValue l₂ A₂ C₂` are `CodeI`-coded and `ValueEq`, then their
domain codes form a `CodePair` (hence `RelatedCode legacyUniverseSystem A₁ A₂`), and for
every domain-related pair `RA₁ x y` their codomain fibre applications form a `CodePair`
(hence `RelatedCode legacyUniverseSystem (applyValue C₁ x) (applyValue C₂ y)`). -/
theorem codeI_pi_valueEq_injective {k₁ k₂ l₁ l₂ : Option Nat}
    {A₁ C₁ A₂ C₂ : Value} {R₁ R₂ : Relation}
    (hA₁ : A₁ .bot) (hA₂ : A₂ .bot)
    (h₁ : CodeI k₁ (piValue l₁ A₁ C₁) R₁)
    (h₂ : CodeI k₂ (piValue l₂ A₂ C₂) R₂)
    (heq : ValueEq (piValue l₁ A₁ C₁) (piValue l₂ A₂ C₂)) :
    ∃ (kA : Option Nat) (RA₁ RA₂ : Relation) (kB : Option Nat) (RB₁ RB₂ : Value → Relation),
      CodePair legacyUniverseSystem kA A₁ A₂ RA₁ RA₂ ∧
      (∀ x y : Value, RA₁ x y →
        CodePair legacyUniverseSystem kB
          (NeutralPi.applyValue C₁ x) (NeutralPi.applyValue C₂ y)
          (RB₁ x) (RB₂ y)) := by
  obtain ⟨kA₁, kB₁, RA₁, RB₁, hdom₁, hfib₁, hcoh₁, _⟩ := code_pi_view hA₁ h₁
  obtain ⟨kA₂, kB₂, RA₂, RB₂, hdom₂, hfib₂, hcoh₂, _⟩ := code_pi_view hA₂ h₂
  obtain ⟨_, heA, heC⟩ := piValue_injective hA₁ hA₂ heq
  have hSameA : Same RA₁ RA₂ := code_coherent_values hdom₁ hdom₂ heA
  have hkA : kA₁ = kA₂ :=
    sortMember_unique (code_level hdom₁)
      (sortMember_congr heA.symm (code_level hdom₂)) (code_defined hdom₁)
  subst kA₂
  have hPairA : CodePair legacyUniverseSystem kA₁ A₁ A₂ RA₁ RA₂ :=
    ⟨hdom₁, hdom₂, hSameA⟩
  refine ⟨kA₁, RA₁, RA₂, kB₁, RB₁, RB₂, hPairA, ?_⟩
  intro x y hxy
  have hx : Member RA₁ x := left_member (code_laws hdom₁) hxy
  have hy : Member RA₂ y := (hSameA y y).mp (right_member (code_laws hdom₁) hxy)
  have hxy₂ : RA₂ x y := (hSameA x y).mp hxy
  have hBx₁ : CodeI kB₁ (NeutralPi.applyValue C₁ x) (RB₁ x) := hfib₁ x x hx
  have hBx₂ : CodeI kB₂ (NeutralPi.applyValue C₂ x) (RB₂ x) :=
    hfib₂ x x ((hSameA x x).mp hx)
  have hBy₂ : CodeI kB₂ (NeutralPi.applyValue C₂ y) (RB₂ y) := hfib₂ y y hy
  have hkB : kB₁ = kB₂ :=
    sortMember_unique (code_level hBx₁)
      (sortMember_congr (heC x).symm (code_level hBx₂)) (code_defined hBx₁)
  subst kB₂
  have hSameBx : Same (RB₁ x) (RB₂ x) :=
    code_coherent_values hBx₁ hBx₂ (heC x)
  have hSameBxy : Same (RB₂ x) (RB₂ y) := hcoh₂ x y hxy₂
  exact ⟨hBx₁, hBy₂, fun u v => (hSameBx u v).trans (hSameBxy u v)⟩

/-- Specialisation of `codeI_pi_valueEq_injective` to `EnvironmentEval.denote`:
two `CodeI`-coded annotated Π expressions with `ValueEq` denotations have
`RelatedCode`-related domain denotations and, at any reflected neutral member `x` of the
left domain PER, `RelatedCode`-related codomain denotations in the extended environment
`EnvI.cons x ρ`. -/
theorem environmentEval_pi_injective_of_valueEq
    {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {A B A' B' : ExprA} {u v u' v' : Level}
    {k₁ k₂ : Option Nat} {R₁ R₂ : Relation}
    (h₁ : CodeI k₁ (EnvironmentEval.denote E H ν ρ (.pi A u B v)) R₁)
    (h₂ : CodeI k₂ (EnvironmentEval.denote E H ν ρ (.pi A' u' B' v')) R₂)
    (heq : ValueEq
      (EnvironmentEval.denote E H ν ρ (.pi A u B v))
      (EnvironmentEval.denote E H ν ρ (.pi A' u' B' v'))) :
    RelatedCode legacyUniverseSystem
      (EnvironmentEval.denote E H ν ρ A)
      (EnvironmentEval.denote E H ν ρ A') ∧
    ∃ kA RA₁ RA₂,
      CodePair legacyUniverseSystem kA
        (EnvironmentEval.denote E H ν ρ A)
        (EnvironmentEval.denote E H ν ρ A') RA₁ RA₂ ∧
      ∀ x : Value, Member RA₁ x →
        RelatedCode legacyUniverseSystem
          (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B)
          (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B') := by
  have hpi₁ := EnvironmentEval.denote_pi_value E H ν ρ A B u v
  have hpi₂ := EnvironmentEval.denote_pi_value E H ν ρ A' B' u' v'
  have hc₁ := code_value_eq h₁ hpi₁
  have hc₂ := code_value_eq h₂ hpi₂
  have heqPi : ValueEq
      (piValue (imaxLevel (eval ν u) (eval ν v))
        (EnvironmentEval.denote E H ν ρ A)
        (EnvironmentEval.denote E H ν ρ (.lam A u B)))
      (piValue (imaxLevel (eval ν u') (eval ν v'))
        (EnvironmentEval.denote E H ν ρ A')
        (EnvironmentEval.denote E H ν ρ (.lam A' u' B'))) :=
    hpi₁.symm.trans (heq.trans hpi₂)
  obtain ⟨kA, RA₁, RA₂, kB, RB₁, RB₂, hPairA, hPairB⟩ :=
    codeI_pi_valueEq_injective
      (EnvironmentEval.denote_bot E H ν ρ A)
      (EnvironmentEval.denote_bot E H ν ρ A')
      hc₁ hc₂ heqPi
  refine ⟨⟨kA, RA₁, RA₂, hPairA⟩, kA, RA₁, RA₂, hPairA, ?_⟩
  intro x hx
  have hB := hPairB x x hx
  have happ₁ := EnvironmentEval.denote_lambda_application E H ν ρ A B u x
  have happ₂ := EnvironmentEval.denote_lambda_application E H ν ρ A' B' u' x
  exact ⟨kB, RB₁ x, RB₂ x,
    ⟨code_value_eq hB.left_code happ₁,
     code_value_eq hB.right_code happ₂,
     hB.transport⟩⟩

/-! ## §3 Glued Adequacy Logical Relation (CCFMLMW §§2.6–2.8 for RCIC) -/

/-- A glued type-level adequacy relation over a native semantics `M` and neutral support
`S`: relates two expressions `X, Y` in context `Γ` whenever they are semantically
`RelatedCode`-related at `nativeGeneric S ν Γ` AND, whenever both are sort-typed, they are
syntactically `ConvT`-convertible at the left sort. -/
def NativeGluedTypeRel (M : NativeSemantics) (S : NativeNeutralSupport M)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (X Y : Expr Nat) : Prop :=
  NativeSemTypeRel M S Γ X Y ∧
    ∀ {u u' : Level},
      HasTyT E n Γ X (.sort u) → HasTyT E n Γ Y (.sort u') →
      Nonempty (ConvT E n Γ X Y (.sort u))

theorem nativeGluedTypeRel_refl (M : NativeSemantics) (S : NativeNeutralSupport M)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (X : Expr Nat) :
    NativeGluedTypeRel M S E n Γ X X :=
  ⟨Or.inl rfl, fun hX _ => ⟨.refl Γ X _ hX⟩⟩

/-- Projecting the syntactic conversion half of `NativeGluedTypeRel` immediately
supplies `LiftNatAt E n (NativeGluedTypeRel M S E n)`. -/
theorem liftNatAt_of_nativeGluedTypeRel (M : NativeSemantics)
    (S : NativeNeutralSupport M) (E : ResolvedEnv) (n : Nat) :
    LiftNatAt E n (NativeGluedTypeRel M S E n) := by
  intro Γ _ X Y u u' hGlued hX hY
  exact hGlued.2 hX hY

/-- If every `NativeSemTypeRel` implies the syntactic half of `NativeGluedTypeRel`
(i.e. `NativeTypeReadback` holds), then `NativeSemTypeRel` and `NativeGluedTypeRel`
are logically equivalent. -/
theorem nativeSemTypeRel_iff_glued {M : NativeSemantics} {S : NativeNeutralSupport M}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hReify : NativeTypeReadback M S E n) (X Y : Expr Nat) :
    NativeSemTypeRel M S Γ X Y ↔ NativeGluedTypeRel M S E n Γ X Y := by
  constructor
  · intro hSem
    refine ⟨hSem, ?_⟩
    intro u u' hX hY
    exact liftNatAt_of_nativeTypeReadback hReify hΓ hSem hX hY
  · exact And.left

end Rcic.Declarative.Ann.LR3.AdeqRelation
