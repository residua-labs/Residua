import rcic.RcicAnnLR3CertifiedUniverseEta
import rcic.RcicAnnLR3ReflectiveConversionUniverse

/-!
# Additive certification of the conversion-based heterogeneous Pi

The new producer certifies exactly the fully constructed kernel for
`Pi X : Sort 1, Sort 0`. Its domain is every extended `Code 1`, including
guarded codes, and its result carrier is every extended `Code 0`.
Existing producers are retained under a separate constructor. There is no
constructor from an arbitrary kernel or an unproved reflection interface.

The package universe has all these new codes as its actual carrier and
KernelRelated as its element relation. This makes the new Pi a real universe
element. It is not a general dependent-Pi closure theorem or a source reader.
The source formation, reflection, application, paired transport and eta
laws below are all supplied. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SemanticPiCode

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open TaggedSaturatedTower (Kernel KernelRelated)

universe u

inductive Tag where
  | existing : GuardedTaggedCode.Tag → Tag
  | conversionPi : Tag
  deriving DecidableEq

inductive Producer : Tag → {k : Nat} → Kernel.{u+1} k → Type (u+2) where
  | existing {k : Nat} (C : GuardedTaggedCode.Code.{u+1} k) :
      Producer (.existing C.tag) C.kernel
  | conversionPi (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
      (ν : Valuation) (ρ : EnvI) :
      Producer .conversionPi (CertifiedUniverseEta.conversionPiKernel.{u} E F ν ρ)

structure Code (k : Nat) where
  kernel : Kernel.{u+1} k
  tag : Tag
  producer : Producer tag kernel

abbrev Code.Element {k : Nat} (C : Code.{u} k) := C.kernel.Element
def Code.erase {k : Nat} (C : Code.{u} k) : C.Element → Value := C.kernel.erase
def Code.view {k : Nat} (C : Code.{u} k) := C.kernel.per

def Code.existing {k : Nat} (C : GuardedTaggedCode.Code.{u+1} k) : Code.{u} k :=
  ⟨C.kernel, .existing C.tag, .existing C⟩

def conversionPi (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : Code.{u} 2 :=
  ⟨CertifiedUniverseEta.conversionPiKernel.{u} E F ν ρ,
    .conversionPi, .conversionPi E F ν ρ⟩

def Converts {k : Nat} (C D : Code.{u} k) : Prop := KernelRelated C.kernel D.kernel

theorem converts_refl {k : Nat} (C : Code.{u} k) : Converts C C :=
  TaggedSaturatedTower.kernelRelated_refl C.kernel

theorem converts_symm {k : Nat} {C D : Code.{u} k} (h : Converts C D) : Converts D C :=
  TaggedSaturatedTower.kernelRelated_symm h

theorem converts_trans {k : Nat} {C D E : Code.{u} k}
    (h : Converts C D) (j : Converts D E) : Converts C E :=
  TaggedSaturatedTower.kernelRelated_trans h j

theorem converts_laws (k : Nat) : RelLaws (@Converts.{u} k) :=
  ⟨converts_symm, converts_trans⟩

theorem existing_converts_iff {k : Nat} (C D : GuardedTaggedCode.Code.{u+1} k) :
    Converts (Code.existing C) (Code.existing D) ↔ GuardedTaggedCode.Converts C D := Iff.rfl

def source_formed {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (Γ : LCtxA) :
    HasTyA E I n Γ CertifiedUniverseEta.sourceType
      (.sort (.imax CertifiedUniverseEta.two CertifiedUniverseEta.one)) :=
  .pi Γ (.sort CertifiedUniverseEta.one) CertifiedUniverseEta.two
    (.sort .zero) CertifiedUniverseEta.one (.sort Γ CertifiedUniverseEta.one) (.sort _ .zero)

theorem source_level (ν : Valuation) :
    eval ν (.imax CertifiedUniverseEta.two CertifiedUniverseEta.one) = some 2 := rfl

theorem source_formation_packet :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      CertifiedUniverseEta.sourceType
      (.sort (.imax CertifiedUniverseEta.two CertifiedUniverseEta.one))) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨source_formed []⟩⟩

def reflect (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n) :
    (conversionPi.{u} E F ν ρ).Element := CertifiedUniverseEta.reflectAction 1 n hn

theorem reflect_member (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n) :
    (conversionPi.{u} E F ν ρ).view.relation
      (reflect E F ν ρ n hn) (reflect E F ν ρ n hn) :=
  CertifiedUniverseEta.conversionPiKernel_member E F ν ρ n hn

theorem point_reflect (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (name : Nat) :
    (conversionPi.{u} E F ν ρ).view.point name =
      reflect E F ν ρ (NeutralPER.neutralAtom name) (.atom name) := rfl

theorem type_image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    (conversionPi.{u} E F ν ρ).view.value =
      EnvironmentEval.denote E F ν ρ CertifiedUniverseEta.sourceType := rfl

theorem application (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (conversionPi.{u} E F ν ρ).Element)
    (A : GuardedTaggedCode.Code.{u} 1) :
    ValueEq (NeutralPi.applyValue ((conversionPi E F ν ρ).erase f) A.view.value)
      (f.run A).view.value := f.erased A

theorem paired (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) {f g : (conversionPi.{u} E F ν ρ).Element}
    (hfg : (conversionPi E F ν ρ).view.relation f g)
    {A B : GuardedTaggedCode.Code.{u} 1} (hAB : GuardedTaggedCode.Converts A B) :
    GuardedTaggedCode.Converts (f.run A) (g.run B) :=
  CertifiedUniverseEta.conversionPiKernel_paired E F ν ρ hfg hAB

theorem codomain_reflect (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n)
    (A : GuardedTaggedCode.Code.{u} 1) :
    (reflect E F ν ρ n hn).run A =
      ReflectiveConversionUniverse.reflect (NeutralPi.applyValue n A.view.value)
        (.app hn _ (CandidatePi.typeDefined_nonempty A.view.defined)) := rfl

theorem codomain_member (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (conversionPi.{u} E F ν ρ).Element)
    (A : GuardedTaggedCode.Code.{u} 1) :
    ReflectiveConversionUniverse.zero.view.relation (f.run A) (f.run A) :=
  GuardedTaggedCode.converts_refl _

theorem eta_roundtrip (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (conversionPi.{u} E F ν ρ).Element) :
    (conversionPi E F ν ρ).view.relation (KPiEtaReflection.etaAction f) f :=
  CertifiedUniverseEta.conversionPiKernel_eta_roundtrip E F ν ρ f

/-- The new package really is the universe carrier; it is not an external
tag attached to a raw type image. Its conversion relation has no tag test. -/
def universeKernel (k : Nat) : Kernel.{u+2} (k+1) :=
  TaggedSaturatedTower.universeKernel k (Code.{u} k)
    (fun C => TaggedSaturatedTower.raiseKernel.{u+1,u+2} C.kernel)
    (@Converts.{u} k) (converts_laws k)
    (fun name => Code.existing
      (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{u+1} k name)))
    converts_refl

def universeLegacyCode (k : Nat) : TaggedSaturatedTower.Code.{u+2} (k+1) where
  kernel := universeKernel k
  tag := .univ
  witness := TaggedSaturatedTower.Witness.univ k (Code.{u} k)
    (fun C => TaggedSaturatedTower.raiseKernel.{u+1,u+2} C.kernel)
    (@Converts.{u} k) (converts_laws k)
    (fun name => Code.existing
      (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{u+1} k name)))
    converts_refl
    (fun _ _ h => TaggedSaturatedTower.kernelRelated_raise.{u+1,u+1,u+2} h)
    (fun _ => ValueEq.refl _)

def universeCode (k : Nat) : GuardedTaggedCode.Code.{u+2} (k+1) :=
  .legacy (universeLegacyCode k)

theorem universe_relation (k : Nat) (C D : Code.{u} k) :
    (universeCode k).view.relation C D ↔ Converts C D := Iff.rfl

theorem universe_member (k : Nat) (C : Code.{u} k) :
    (universeCode k).view.relation C C := converts_refl C

theorem universe_element_image (k : Nat) (C : Code.{u} k) :
    (universeCode k).erase C = C.view.value := rfl

theorem conversionPi_universe_member (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    (universeCode.{u} 2).view.relation (conversionPi E F ν ρ) (conversionPi E F ν ρ) :=
  universe_member 2 (conversionPi E F ν ρ)

end Rcic.Declarative.Ann.LR3.SemanticPiCode
