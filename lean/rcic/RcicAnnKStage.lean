import rcic.RcicAnnIotaLaws
import rcic.RcicAnnSubstTy
import rcic.RcicAnnKIndexLaws
import rcic.RcicAnnSpineConv

/-!
# A context-aware K stage over an unchanged annotated interface

The guard below is a list of conversions in the *old* interface `I`.
The family conversion is derived from those index conversions.  The K
conclusion is derived by retyping the canonical proof, proof irrelevance,
application congruence, and one old canonical iota step.  No conversion in
a proposed new interface, and no conversion of the whole K call, is a premise.

This is a typed relational stage.  It does not claim the context-free
`IotaIfaceA.fn` laws for a context-sensitive guard, nor supply the semantic
environment or the generic typing of a recursor's minor.
-/

namespace Rcic.Declarative.Ann.KStage

open Rcic.Declarative

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

section Congruence

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)

include hE hI hR hIS hΓ

/-- Dependent application congruence, deriving its right endpoint typing. -/
def appCongr {f g a b D C : ExprA} {u v : Level}
    (hfg : ConvA E I n Γ f g (.pi D u C v))
    (hab : ConvA E I n Γ a b D) :
    ConvA E I n Γ (.app f a) (.app g b) (instantiate0A a C) := by
  have hg := convA_hasTy_left hE hI hR hIS hΓ (.symm Γ _ _ _ hfg)
  have ha := convA_hasTy_left hE hI hR hIS hΓ hab
  have hb := convA_hasTy_left hE hI hR hIS hΓ (.symm Γ _ _ _ hab)
  have hp := hasTyA_pi_parts (hasTyA_regular hE hI hR hIS hΓ hg).2
  have hCa : HasTyA E I n Γ (instantiate0A a C) (.sort v) :=
    hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hp.2 ha hp.1
  have hCb : HasTyA E I n Γ (instantiate0A b C) (.sort v) :=
    hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hp.2 hb hp.1
  have hC : ConvA E I n Γ (instantiate0A a C) (instantiate0A b C) (.sort v) :=
    hasTyA_func0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hp.2 hab hp.1
  have hgb : HasTyA E I n Γ (.app g b) (instantiate0A b C) :=
    .app Γ g b D C u v v hp.2 hCb hg hb
  have hrt : HasTyA E I n Γ (.app g b) (instantiate0A a C) :=
    hasTyA_of_tyConvA hgb
      (.of Γ _ _ v v v hCb (eqNA_refl _) hCa (eqNA_refl _)
        (.symm Γ _ _ _ hC))
  exact .app Γ f g a b D C u v hfg hab hp.2 hrt

/-- Pointwise old-interface conversions yield a conversion of the entire
family application.  The resulting type is the left telescope instance. -/
theorem foldAppsCongr {T : ExprA} {xs ys : List ExprA}
    (hargs : ConvArgsA E I n Γ T xs ys) :
    ∀ {f g : ExprA}, ConvA E I n Γ f g T →
      ∃ U, applyTelA xs T = some U ∧
        Nonempty (ConvA E I n Γ (foldAppsA f xs) (foldAppsA g ys) U) := by
  induction hargs with
  | nil T =>
      intro f g hfg
      exact ⟨T, rfl, ⟨hfg⟩⟩
  | cons A u B v a b xs ys hab htail ih =>
      intro f g hfg
      obtain ⟨hab⟩ := hab
      obtain ⟨U, hU, hc⟩ := ih (appCongr hE hI hR hIS hΓ hfg hab)
      exact ⟨U, hU, hc⟩

end Congruence

/-- The syntax read by the stage.  One minor is present because the target
has one constructor; the canonical constructor application has no fields. -/
structure Shape where
  recRef : Nat
  ctorRef : Nat
  group : IotaGroupA
  recLevels : List Level
  familyLevels : List Level
  ctorLevels : List Level
  params : List ExprA
  declaredIndices : List ExprA
  actualIndices : List ExprA
  motive : ExprA
  minor : ExprA
  major : ExprA
  body : ExprA
  codSort : Level

def Shape.pre (s : Shape) : List ExprA :=
  s.params ++ [s.motive, s.minor] ++ s.actualIndices

def Shape.prefix (s : Shape) : ExprA :=
  foldAppsA (.const s.recRef s.recLevels) s.pre

def Shape.familyHead (s : Shape) : ExprA :=
  foldAppsA (.const s.group.familyRef s.familyLevels) s.params

def Shape.actualProp (s : Shape) : ExprA :=
  foldAppsA s.familyHead s.actualIndices

def Shape.declaredProp (s : Shape) : ExprA :=
  foldAppsA s.familyHead s.declaredIndices

def Shape.canonical (s : Shape) : ExprA :=
  foldAppsA (.const s.ctorRef s.ctorLevels) s.params

def Shape.source (s : Shape) : ExprA := .app s.prefix s.major

def Shape.canonicalCall (s : Shape) : ExprA := .app s.prefix s.canonical

def Shape.resultType (s : Shape) : ExprA := instantiate0A s.major s.body

/-- Static K target: the selected stored layout has one constructor, a
Prop-valued family, and no constructor fields after its parameters. -/
structure Target (E : ResolvedEnvA) (s : Shape) : Prop where
  group : iotaGroupA E s.recRef s.ctorRef = some s.group
  oneConstructor : s.group.nMinors = 1
  propFamily : piBodyA s.group.famM.mtypeA = .sort .zero
  noFields : piCountA (s.group.ctorM.normA.getD s.group.ctorM.mtypeA) = s.group.nparams
  paramCount : s.params.length = s.group.nparams
  arity : s.pre.length + 1 = piCountA s.group.recM.mtypeA

/-- Target recognition fixes the number of supplied actual indices. -/
theorem Target.indexCount {E : ResolvedEnvA} {s : Shape} (w : Target E s) :
    s.actualIndices.length = s.group.nindices := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := iotaGroupA_some w.group
  have ha := w.arity
  simp only [Shape.pre, List.length_append, List.length_cons, List.length_nil] at ha
  rw [w.paramCount] at ha
  rw [w.oneConstructor] at hc
  omega

/-- All derivation premises live in the unchanged old interface.  In
particular `indexGuard` is independent of the relation defined below.

`canonicalType` and `minorType` are explicit typed-boundary obligations;
this record does not claim that syntactic target recognition supplies them.
-/
structure Frame (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (s : Shape) where
  target : Target E s
  familyTelescope : ExprA
  telescope : applyTelA s.params
    (instantiateLevelsA s.familyLevels s.group.famM.mtypeA) = some familyTelescope
  familyHeadType : HasTyA E I n Γ s.familyHead familyTelescope
  indexGuard : ConvArgsA E I n Γ familyTelescope s.declaredIndices s.actualIndices
  familyResult : applyTelA s.declaredIndices familyTelescope = some (.sort .zero)
  prefixType : HasTyA E I n Γ s.prefix (.pi s.actualProp .zero s.body s.codSort)
  majorType : HasTyA E I n Γ s.major s.actualProp
  canonicalType : HasTyA E I n Γ s.canonical s.declaredProp
  canonicalIota : I.rel E Γ s.canonicalCall s.minor
  minorType : HasTyA E I n Γ s.minor s.resultType

/-- The declared indices in the guard have that same exact arity. -/
theorem Frame.declaredIndexCount {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {s : Shape} (w : Frame E I n Γ s) :
    s.declaredIndices.length = s.group.nindices :=
  (convArgsA_length w.indexGuard).trans w.target.indexCount

section Soundness

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
variable {s : Shape}

include hE hI hR hIS hΓ

/-- The declared-index guard supplies the family-type conversion. -/
theorem Frame.familyConversion (w : Frame E I n Γ s) :
    Nonempty (ConvA E I n Γ s.declaredProp s.actualProp (.sort .zero)) := by
  obtain ⟨U, hU, hc⟩ := foldAppsCongr hE hI hR hIS hΓ w.indexGuard
    (.refl Γ s.familyHead w.familyTelescope w.familyHeadType)
  rw [w.familyResult] at hU
  cases hU
  exact hc

/-- K soundness in OLD annotated conversion: family congruence, canonical
proof retyping, proof irrelevance, application congruence, then old iota. -/
theorem Frame.canonicalAlignment (w : Frame E I n Γ s) :
    Nonempty (ConvA E I n Γ s.source s.canonicalCall s.resultType) := by
  obtain ⟨hFamily⟩ := w.familyConversion hE hI hR hIS hΓ
  have hQ := convA_hasTy_left hE hI hR hIS hΓ hFamily
  have hP := convA_hasTy_left hE hI hR hIS hΓ (.symm Γ _ _ _ hFamily)
  have hcanonical : HasTyA E I n Γ s.canonical s.actualProp :=
    .conv Γ s.canonical s.declaredProp s.actualProp .zero .zero
      w.canonicalType hQ (eqNA_refl _) hP hFamily
  have hproof : ConvA E I n Γ s.major s.canonical s.actualProp :=
    .irr Γ s.actualProp s.major s.canonical hP w.majorType hcanonical
  have happ := appCongr hE hI hR hIS hΓ
    (.refl Γ s.prefix _ w.prefixType) hproof
  exact ⟨happ⟩

/-- The canonical old iota step completes the K conversion. -/
theorem Frame.sound (w : Frame E I n Γ s) :
    Nonempty (ConvA E I n Γ s.source s.minor s.resultType) := by
  obtain ⟨happ⟩ := w.canonicalAlignment hE hI hR hIS hΓ
  have hcanonicalCall := convA_hasTy_left hE hI hR hIS hΓ (.symm Γ _ _ _ happ)
  exact ⟨.trans Γ s.source s.canonicalCall s.minor s.resultType happ
    (.iota Γ s.canonicalCall s.minor s.resultType
      w.canonicalIota hcanonicalCall w.minorType)⟩

omit hE hI hR hIS hΓ in
/-- A K source has the same exact recursor head/arity invariant as old iota. -/
theorem Frame.recHead (w : Frame E I n Γ s) :
    ∃ r ls m, (appsSpineA s.source).1 = .const r ls ∧
      E.members r = some m ∧ m.mclass = .recursorM ∧
      (appsSpineA s.source).2.length = piCountA m.mtypeA := by
  obtain ⟨hres, hcls, _⟩ := iotaGroupA_some w.target.group
  refine ⟨s.recRef, s.recLevels, s.group.recM, ?_, hres, hcls, ?_⟩
  · simp [Shape.source, Shape.prefix, appsSpineA, appsSpineA_foldAppsA]
  · simpa [Shape.source, Shape.prefix, appsSpineA, appsSpineA_foldAppsA]
      using w.target.arity

/-- Typed substitution of the derived K conversion.  This is a conversion
law, not the raw `IotaSubstA` law of a context-free function. -/
theorem Frame.sound_subst {Δ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) (w : Frame E I n Γ s) :
    Nonempty (ConvA E I n Δ (substA σ s.source) (substA σ s.minor)
      (substA σ s.resultType)) := by
  obtain ⟨hc⟩ := w.sound hE hI hR hIS hΓ
  exact ⟨convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hc⟩

end Soundness

#print axioms appCongr
#print axioms foldAppsCongr
#print axioms Shape
#print axioms Shape.pre
#print axioms Shape.prefix
#print axioms Shape.familyHead
#print axioms Shape.actualProp
#print axioms Shape.declaredProp
#print axioms Shape.canonical
#print axioms Shape.source
#print axioms Shape.canonicalCall
#print axioms Shape.resultType
#print axioms Target
#print axioms Target.indexCount
#print axioms Frame
#print axioms Frame.declaredIndexCount
#print axioms Frame.familyConversion
#print axioms Frame.canonicalAlignment
#print axioms Frame.sound
#print axioms Frame.recHead
#print axioms Frame.sound_subst

end Rcic.Declarative.Ann.KStage
