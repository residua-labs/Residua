import rcic.RcicAnnLR3KPiEtaReflection
import rcic.RcicAnnLR3GuardedConversionUniverse

/-!
# Typed neutral spines in the actual conversion universe of propositions

Every reflected payload is an existing proposition-certified code. Reflection
preserves the entire neutral payload in its tagged type image, and conversion
between reflected codes is exactly equality of those payload values.

The final action uses a full extended `Code j` domain and `Code 0` codomain,
with conversion as their relation. Its complete graph and exact application law
are constructed from finite demand. The level-one-domain instance supplies a
complete Pi kernel with the actual source type image. The existing sealed
legacy Pi producer still has a different carrier; certification by an additive
producer and a general source evaluator are separate.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CertifiedUniverseEta

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open TaggedSaturatedTower (Kernel KernelIso)
open GuardedTaggedCode
open KPiEtaReflection

universe u

def reflectCode (n : Value) (hn : CandidatePi.Neutral n) : Code.{u} 0 :=
  Code.legacy (TaggedSaturatedTower.Code.proposition.{u} (propReflect n hn).code)

def reflectIso (n m : Value) (hn : CandidatePi.Neutral n)
    (hm : CandidatePi.Neutral m) (h : ValueEq n m) :
    KernelIso (reflectCode.{u} n hn).kernel (reflectCode.{u} m hm).kernel where
  forward := fun x => x
  backward := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  type_image := tagged_congr (some 0) h
  element_image := fun _ => ValueEq.refl _
  point_image := fun _ => rfl
  relation := fun _ _ => Iff.rfl

theorem reflect_converts_iff (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) :
    Converts (reflectCode.{u} n hn) (reflectCode.{u} m hm) ↔ ValueEq n m := by
  constructor
  · intro h
    exact tagged_injective (some 0) (converts_type_image h)
  · intro h
    exact ⟨reflectIso n m hn hm h⟩

/-- Reflection lands in the actual canonical conversion universe, with no
extension to its sealed code carrier. -/
def reflect (n : Value) (hn : CandidatePi.Neutral n) :
    (GuardedConversionUniverse.conversionUniverse.{u} 0).Element :=
  GuardedConversionUniverse.encode 0 (reflectCode n hn)

theorem reflect_member (n : Value) (hn : CandidatePi.Neutral n) :
    (GuardedConversionUniverse.conversionUniverse.{u} 0).view.relation
      (reflect n hn) (reflect n hn) :=
  GuardedConversionUniverse.member 0 (reflectCode n hn)

theorem reify_reflect (n : Value) (hn : CandidatePi.Neutral n) :
    (GuardedConversionUniverse.conversionUniverse.{u} 0).erase (reflect n hn) =
      InductiveCodes.taggedValue (some 0) n := rfl

theorem reflect_relation_iff (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) :
    (GuardedConversionUniverse.conversionUniverse.{u} 0).view.relation
      (reflect n hn) (reflect m hm) ↔ ValueEq n m :=
  reflect_converts_iff n m hn hm

def reflectApplication {j : Nat} (n : Value) (hn : CandidatePi.Neutral n) (A : Code.{u} j) :
    Code.{u} 0 :=
  reflectCode (NeutralPi.applyValue n A.view.value)
    (.app hn _ (CandidatePi.typeDefined_nonempty A.view.defined))

theorem reflectApplication_reify {j : Nat} (n : Value) (hn : CandidatePi.Neutral n)
    (A : Code.{u} j) :
    (reflectApplication n hn A).view.value =
      InductiveCodes.taggedValue (some 0) (NeutralPi.applyValue n A.view.value) := rfl

theorem reflectApplication_related {j : Nat} (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m)
    (h : ValueEq n m) {A B : Code.{u} j} (hAB : Converts A B) :
    Converts (reflectApplication n hn A) (reflectApplication m hm B) :=
  (reflect_converts_iff _ _ _ _).mpr
    (NeutralPi.applyValue_congr h (converts_type_image hAB))

/-- Tagging preserves the concrete finite demands of native application.
No membership or finite-demand interface is assumed. -/
theorem taggedApplication_finite (n : Value) :
    UnifiedPi.LegalFiniteDemand (fun _ _ => True)
      (fun a => InductiveCodes.taggedValue (some 0) (NeutralPi.applyValue n a)) := by
  intro a _ c hc
  rcases hc with hc | ⟨l, p, hc, hl, hp⟩
  · exact ⟨[], by simp, fun _ _ _ => Or.inl hc⟩
  · obtain ⟨us, hus, hrow⟩ :=
      UnifiedPi.application_legalFiniteDemand (fun _ _ => True) n a True.intro p hp
    exact ⟨us, hus, fun b _ hb => Or.inr ⟨l, p, hc, hl, hrow b True.intro hb⟩⟩

def etaGraph (n : Value) : Value :=
  UnifiedPi.legalGraph (fun _ _ => True)
    (fun a => InductiveCodes.taggedValue (some 0) (NeutralPi.applyValue n a))

theorem etaGraph_application (n a : Value) :
    ValueEq (NeutralPi.applyValue (etaGraph n) a)
      (InductiveCodes.taggedValue (some 0) (NeutralPi.applyValue n a)) :=
  UnifiedPi.applyValue_legalGraph (fun _ _ => Or.inl rfl)
    (taggedApplication_finite n) True.intro

/-- The heterogeneous action quantifies over the actual full extended carrier
at any object level, with proposition codes as results. -/
abbrev ConversionAction (j : Nat) :=
  SaturatedPiElements.ElementAction
    (fun A : Code.{u} j => A.view.value) (fun B : Code.{u} 0 => B.view.value)
    (fun A B => Converts A B) (fun _ A B => Converts A B)

def reflectAction (j : Nat) (n : Value) (hn : CandidatePi.Neutral n) : ConversionAction.{u} j where
  value := etaGraph n
  run := reflectApplication n hn
  erased := fun A => etaGraph_application n A.view.value
  respect := fun _ _ h => reflectApplication_related n n hn hn (ValueEq.refl n) h

theorem reflectAction_member (j : Nat) (n : Value) (hn : CandidatePi.Neutral n) :
    SaturatedPiElements.ElementRel (reflectAction.{u} j n hn) (reflectAction.{u} j n hn) :=
  SaturatedPiElements.elementRel_refl _

theorem reflectAction_run (j : Nat) (n : Value) (hn : CandidatePi.Neutral n) (A : Code.{u} j) :
    (reflectAction j n hn).run A = reflectApplication n hn A := rfl

theorem reflectAction_application (j : Nat) (n : Value) (hn : CandidatePi.Neutral n)
    (A : Code.{u} j) :
    ValueEq (NeutralPi.applyValue (reflectAction j n hn).value A.view.value)
      ((reflectAction j n hn).run A).view.value :=
  (reflectAction j n hn).erased A

theorem reflectAction_respect (j : Nat) (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) (h : ValueEq n m) :
    SaturatedPiElements.ElementRel (reflectAction.{u} j n hn) (reflectAction.{u} j m hm) :=
  fun _ hA => reflectApplication_related n m hn hm h hA

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

/-- The source type for a function from the universe of all level-one codes
to the universe of all proposition codes. -/
def sourceType : ExprA := .pi (.sort one) two (.sort .zero) one

/-- A fully constructed semantic Pi kernel over the full extended Code 1
carrier. Its source type image, PER laws and neutral-reflected points are
all supplied here. Certification by an additive producer is separate. -/
def conversionPiKernel (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : Kernel.{u+1} 2 where
  Element := ConversionAction.{u} 1
  erase := fun f => f.value
  per := {
    value := EnvironmentEval.denote E F ν ρ sourceType
    level := by
      have h := CandidateActionProducts.source_pi_level E F ν ρ
        (.sort one) (.sort .zero) two one
      exact h
    defined := CandidateActionProducts.source_pi_defined E F ν ρ
      (.sort one) (.sort .zero) two one
    relation := SaturatedPiElements.ElementRel
    lawful := SaturatedPiElements.elementRel_laws
      (fun _ _ => GuardedConversionUniverse.converts_laws 0)
    point := fun name => reflectAction 1 (NeutralPER.neutralAtom name) (.atom name)
    point_member := fun name => reflectAction_member 1 (NeutralPER.neutralAtom name) (.atom name)
    irrelevant := fun h => False.elim (Nat.noConfusion h) }

theorem conversionPiKernel_image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    (conversionPiKernel.{u} E F ν ρ).per.value =
      EnvironmentEval.denote E F ν ρ sourceType := rfl

theorem conversionPiKernel_member (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n) :
    (conversionPiKernel.{u} E F ν ρ).per.relation
      (reflectAction 1 n hn) (reflectAction 1 n hn) :=
  reflectAction_member 1 n hn

/-- Paired application quantifies over every converted pair in the full
extended level-one carrier, including guarded codes. -/
theorem conversionPiKernel_paired
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI)
    {f g : (conversionPiKernel.{u} E F ν ρ).Element}
    (hfg : (conversionPiKernel.{u} E F ν ρ).per.relation f g)
    {A B : Code.{u} 1} (hAB : Converts A B) :
    Converts (f.run A) (g.run B) :=
  SaturatedPiElements.elementRel_paired
    (GuardedConversionUniverse.converts_laws 1)
    (fun _ _ => GuardedConversionUniverse.converts_laws 0) hfg hAB

theorem conversionPiKernel_application
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (conversionPiKernel.{u} E F ν ρ).Element)
    (A : Code.{u} 1) :
    ValueEq (NeutralPi.applyValue ((conversionPiKernel E F ν ρ).erase f) A.view.value)
      (f.run A).view.value := f.erased A

/-- The conversion-based action PER does preserve its reified applications,
including the paired equation at converted argument codes. -/
theorem conversionPiKernel_reify_paired
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI)
    {f g : (conversionPiKernel.{u} E F ν ρ).Element}
    (hfg : (conversionPiKernel.{u} E F ν ρ).per.relation f g)
    {A B : Code.{u} 1} (hAB : Converts A B) :
    ValueEq (NeutralPi.applyValue ((conversionPiKernel E F ν ρ).erase f) A.view.value)
      (NeutralPi.applyValue ((conversionPiKernel E F ν ρ).erase g) B.view.value) :=
  (f.erased A).trans
    ((converts_type_image (conversionPiKernel_paired E F ν ρ hfg hAB)).trans
      (g.erased B).symm)

/-- Reconstructing the eta graph preserves the entire retained run and is
related to the original function at the actual conversion-based Pi PER. -/
theorem conversionPiKernel_eta_roundtrip
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (conversionPiKernel.{u} E F ν ρ).Element) :
    (conversionPiKernel E F ν ρ).per.relation (KPiEtaReflection.etaAction f) f :=
  KPiEtaReflection.etaAction_related f

theorem conversionPiKernel_eta_reify
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (conversionPiKernel.{u} E F ν ρ).Element)
    (A : Code.{u} 1) :
    ValueEq (NeutralPi.applyValue
      ((conversionPiKernel E F ν ρ).erase (KPiEtaReflection.etaAction f)) A.view.value)
      (NeutralPi.applyValue ((conversionPiKernel E F ν ρ).erase f) A.view.value) :=
  UnifiedPi.etaGraph_application (fun _ _ => True) f.value True.intro

/-- True-branch transport is handled by actual conversion of argument codes. -/
theorem reflected_guarded_argument_true {G : Prop}
    (M F : Code.{u} 1) (I : GuardedKernel.TypeImage G M.kernel F.kernel)
    (hG : G) (n : Value) (hn : CandidatePi.Neutral n) :
    Converts ((reflectAction 1 n hn).run (Code.guarded G M F I))
      ((reflectAction 1 n hn).run M) :=
  (reflectAction 1 n hn).respect _ _ (guarded_converts_true M F I hG)

/-- False-branch transport is separate; no decision of the guard is needed. -/
theorem reflected_guarded_argument_false {G : Prop}
    (M F : Code.{u} 1) (I : GuardedKernel.TypeImage G M.kernel F.kernel)
    (hG : ¬ G) (n : Value) (hn : CandidatePi.Neutral n) :
    Converts ((reflectAction 1 n hn).run (Code.guarded G M F I))
      ((reflectAction 1 n hn).run F) :=
  (reflectAction 1 n hn).respect _ _ (guarded_converts_false M F I hG)

end Rcic.Declarative.Ann.LR3.CertifiedUniverseEta
