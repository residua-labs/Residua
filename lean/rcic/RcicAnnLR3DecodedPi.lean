import rcic.RcicAnnLR3FunctionEval
import rcic.RcicAnnLR3ReflectionDemand

/-!
# Dependent function fibres decoded without selecting presentations

`decodedEl` is a relation, so its existential presentation stays in Prop.
It is an actual element Code whenever the type value belongs to its
universe. Related type values give transport between these decoded PERs.
No family of descriptors or relations is chosen from existential proofs.

The dependent function relation below quantifies over the full legal
domain and uses these actual decoded fibres. Reflection is the complete
legal graph of the canonical, type-indexed reflection operation. Finite
demand of code values supplies finite demand of their reflections; native
bodies supply that code demand. The identity family over a universe gives
an inhabited control with different fibres and reflected results. The
type-code grammar itself is not enlarged by this file. In particular,
an inhabitant of a function PER is not mislabeled as a Pi Code.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.DecodedPi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- An element relation decoded entirely in Prop. -/
def decodedEl (k : Option Nat) (V : Value) : Relation := fun x y =>
  ∃ R : Relation, NeutralCodes.Code k V R ∧ R x y

theorem decodedEl_same {k : Option Nat} {V : Value} {R : Relation}
    (hR : NeutralCodes.Code k V R) : Same (decodedEl k V) R := by
  intro x y
  constructor
  · rintro ⟨S, hS, hxy⟩
    exact (NeutralCodes.code_coherent hS hR x y).mp hxy
  · intro hxy
    exact ⟨R, hR, hxy⟩

theorem decodedEl_laws (k : Option Nat) (V : Value) : Laws (decodedEl k V) where
  symm := by
    rintro x y ⟨R, hR, hxy⟩
    exact ⟨R, hR, (NeutralCodes.code_lawful hR).symm hxy⟩
  trans := by
    rintro x y z ⟨R, hR, hxy⟩ ⟨S, hS, hyz⟩
    exact ⟨R, hR, (NeutralCodes.code_lawful hR).trans hxy
      ((NeutralCodes.code_coherent hS hR y z).mp hyz)⟩

theorem decodedEl_code {k : Option Nat} {V : Value} {R : Relation}
    (hR : NeutralCodes.Code k V R) : NeutralCodes.Code k V (decodedEl k V) := by
  obtain ⟨d, hd, hv, hD⟩ := hR
  have hcode : NeutralCodes.Code k V R := ⟨d, hd, hv, hD⟩
  exact ⟨d, hd, hv, fun x y => (decodedEl_same hcode x y).trans (hD x y)⟩

theorem decodedEl_code_of_universe {k : Option Nat} {V : Value}
    (hV : Member (NeutralCodes.UniversePER k) V) :
    NeutralCodes.Code k V (decodedEl k V) := by
  obtain ⟨R, hR⟩ := NeutralCodes.decode (NeutralCodes.code_universe k) hV
  exact decodedEl_code hR

theorem decodedEl_transport {k : Option Nat} {V W : Value}
    (hVW : NeutralCodes.UniversePER k V W) : Same (decodedEl k V) (decodedEl k W) :=
  NeutralCodes.el_transport
    (decodedEl_code_of_universe (left_member (NeutralCodes.universePER_laws k) hVW))
    (decodedEl_code_of_universe (right_member (NeutralCodes.universePER_laws k) hVW)) hVW

theorem decodedEl_reflection {k : Option Nat} {V W : Value}
    (hVW : NeutralCodes.UniversePER k V W) (name : Nat) :
    decodedEl k V (NeutralCodes.reflect V name) (NeutralCodes.reflect W name) :=
  NeutralCodes.reflect_relation
    (decodedEl_code_of_universe (left_member (NeutralCodes.universePER_laws k) hVW))
    (decodedEl_code_of_universe (right_member (NeutralCodes.universePER_laws k) hVW))
    (decodedEl_transport hVW) name

/-- The supplied type-valued operation is related at all related legal
arguments. It need not have the same raw value on different arguments. -/
def CodeFamily (k : Option Nat) (D : Relation) (V : Value → Value) : Prop :=
  ∀ x y : Value, D x y → NeutralCodes.UniversePER k (V x) (V y)

theorem codeFamily_decodes {k : Option Nat} {D : Relation} {V : Value → Value}
    (hV : CodeFamily k D V) {x : Value} (hx : Member D x) :
    NeutralCodes.Code k (V x) (decodedEl k (V x)) :=
  decodedEl_code_of_universe (hV x x hx)

theorem codeFamily_coherent {k : Option Nat} {D : Relation} {V : Value → Value}
    (hV : CodeFamily k D V) : FamilyCoherent D (fun x => decodedEl k (V x)) :=
  fun x y hxy => decodedEl_transport (hV x y hxy)

def functionPER (k : Option Nat) (D : Relation) (V : Value → Value) : Relation :=
  FunctionPER NeutralPi.applyValue D (fun x => decodedEl k (V x))

theorem functionPER_lawful {k : Option Nat} {D : Relation} {V : Value → Value}
    (hD : Laws D) (hV : CodeFamily k D V) : Laws (functionPER k D V) :=
  functionPER_laws NeutralPi.applyValue hD
    (fun x _ => decodedEl_laws k (V x)) (codeFamily_coherent hV)

def reflectionGraph (D : Relation) (V : Value → Value) (name : Nat) : Value :=
  UnifiedPi.legalGraph D (fun x => NeutralCodes.reflect (V x) name)

theorem reflection_bot {k : Option Nat} {V : Value}
    (hV : Member (NeutralCodes.UniversePER k) V) (name : Nat) :
    NeutralCodes.reflect V name .bot :=
  FunctionEval.code_member_bot (decodedEl_code_of_universe hV)
    (NeutralCodes.reflect_member (decodedEl_code_of_universe hV) name)

/-- This preliminary graph law explicitly consumes finite demand of the
reflected operation. A code-demand producer below removes that extra
premise for the current code algebra. -/
theorem reflectionGraph_application_of_reflectedDemand
    {k : Option Nat} {D : Relation} {V : Value → Value}
    (hV : CodeFamily k D V) (name : Nat)
    (hfinite : UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflect (V x) name))
    {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue (reflectionGraph D V name) x)
      (NeutralCodes.reflect (V x) name) :=
  UnifiedPi.applyValue_legalGraph
    (fun x hx => reflection_bot (hV x x hx) name) hfinite hx

theorem reflectionGraph_member_of_reflectedDemand
    {k : Option Nat} {D : Relation} {V : Value → Value}
    (hD : Laws D) (hV : CodeFamily k D V) (name : Nat)
    (hfinite : UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflect (V x) name)) :
    Member (functionPER k D V) (reflectionGraph D V name) := by
  change Member (FunctionPER NeutralPi.applyValue D (fun x => decodedEl k (V x)))
    (UnifiedPi.legalGraph D (fun x => NeutralCodes.reflect (V x) name))
  exact UnifiedPi.legalGraph_function_member hD
    (fun x hx => reflection_bot (hV x x hx) name) hfinite
    (fun x y hxy => decodedEl_reflection (hV x y hxy) name)

/-- Paired type operations may use different raw type images. -/
theorem reflectionGraphs_related_of_reflectedDemand
    {k : Option Nat} {D : Relation} {V W : Value → Value}
    (hD : Laws D) (hV : CodeFamily k D V) (hW : CodeFamily k D W)
    (hVW : ∀ x y : Value, D x y → NeutralCodes.UniversePER k (V x) (W y))
    (name : Nat)
    (hfiniteV : UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflect (V x) name))
    (hfiniteW : UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflect (W x) name)) :
    functionPER k D V (reflectionGraph D V name) (reflectionGraph D W name) := by
  change FunctionPER NeutralPi.applyValue D (fun x => decodedEl k (V x))
    (UnifiedPi.legalGraph D (fun x => NeutralCodes.reflect (V x) name))
    (UnifiedPi.legalGraph D (fun x => NeutralCodes.reflect (W x) name))
  exact UnifiedPi.legalGraph_function_related hD
    (fun x hx => reflection_bot (hV x x hx) name)
    (fun x hx => reflection_bot (hW x x hx) name)
    hfiniteV hfiniteW (fun x y hxy => decodedEl_reflection (hVW x y hxy) name)

theorem identity_codeFamily (k : Option Nat) :
    CodeFamily k (NeutralCodes.UniversePER k) (fun x => x) := fun _ _ h => h

theorem identity_legalFiniteDemand (D : Relation) :
    UnifiedPi.LegalFiniteDemand D (fun x => x) := by
  intro x _ c hc
  refine ⟨[c], ?_, ?_⟩
  · intro u hu
    have hu' : u = c := List.mem_singleton.mp hu
    rw [hu']
    exact hc
  · intro y _ hy
    exact hy c (by simp)

/-- The additional reflected-demand premise is discharged from the
finite demand of the code operation itself. Code presentations remain
existential inside Prop. -/
theorem reflectionGraph_application
    {k : Option Nat} {D : Relation} {V : Value → Value}
    (hV : CodeFamily k D V) (hfinite : UnifiedPi.LegalFiniteDemand D V)
    (name : Nat) {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue (reflectionGraph D V name) x)
      (NeutralCodes.reflect (V x) name) :=
  reflectionGraph_application_of_reflectedDemand hV name
    (ReflectionDemand.reflection_finiteDemand_of_codes hfinite
      (fun y hy => ⟨k, decodedEl k (V y), codeFamily_decodes hV hy⟩) name) hx

theorem reflectionGraph_member
    {k : Option Nat} {D : Relation} {V : Value → Value}
    (hD : Laws D) (hV : CodeFamily k D V)
    (hfinite : UnifiedPi.LegalFiniteDemand D V) (name : Nat) :
    Member (functionPER k D V) (reflectionGraph D V name) :=
  reflectionGraph_member_of_reflectedDemand hD hV name
    (ReflectionDemand.reflection_finiteDemand_of_codes hfinite
      (fun x hx => ⟨k, decodedEl k (V x), codeFamily_decodes hV hx⟩) name)

theorem reflectionGraphs_related
    {k : Option Nat} {D : Relation} {V W : Value → Value}
    (hD : Laws D) (hV : CodeFamily k D V) (hW : CodeFamily k D W)
    (hVW : ∀ x y : Value, D x y → NeutralCodes.UniversePER k (V x) (W y))
    (hfiniteV : UnifiedPi.LegalFiniteDemand D V)
    (hfiniteW : UnifiedPi.LegalFiniteDemand D W) (name : Nat) :
    functionPER k D V (reflectionGraph D V name) (reflectionGraph D W name) :=
  reflectionGraphs_related_of_reflectedDemand hD hV hW hVW name
    (ReflectionDemand.reflection_finiteDemand_of_codes hfiniteV
      (fun x hx => ⟨k, decodedEl k (V x), codeFamily_decodes hV hx⟩) name)
    (ReflectionDemand.reflection_finiteDemand_of_codes hfiniteW
      (fun x hx => ⟨k, decodedEl k (W x), codeFamily_decodes hW hx⟩) name)

/-- The inherited finite-approximation theorem supplies the only finite
demand premise. The paired code-family condition is the codomain typing
obligation, not a fundamental theorem premise. -/
theorem native_reflectionGraph_member {k : Option Nat} {D : Relation}
    (hD : Laws D) (ρ : EnvI) (body : Expr Nat)
    (hV : CodeFamily k D (fun x => denI (EnvI.cons x ρ) body)) (name : Nat) :
    Member (functionPER k D (fun x => denI (EnvI.cons x ρ) body))
      (reflectionGraph D (fun x => denI (EnvI.cons x ρ) body) name) :=
  reflectionGraph_member hD hV (UnifiedPi.native_body_legalFiniteDemand D ρ body) name

theorem native_reflectionGraph_application {k : Option Nat} {D : Relation}
    (ρ : EnvI) (body : Expr Nat)
    (hV : CodeFamily k D (fun x => denI (EnvI.cons x ρ) body)) (name : Nat)
    {x : Value} (hx : Member D x) :
    ValueEq
      (NeutralPi.applyValue
        (reflectionGraph D (fun y => denI (EnvI.cons y ρ) body) name) x)
      (NeutralCodes.reflect (denI (EnvI.cons x ρ) body) name) :=
  reflectionGraph_application hV (UnifiedPi.native_body_legalFiniteDemand D ρ body) name hx

/-- Reflection for the complete identity code family, at every Option
Nat level, including `none`. This is a constructed dependent function. -/
def universeSection (k : Option Nat) (name : Nat) : Value :=
  reflectionGraph (NeutralCodes.UniversePER k) (fun x => x) name

theorem universeSection_member (k : Option Nat) (name : Nat) :
    Member (functionPER k (NeutralCodes.UniversePER k) (fun x => x))
      (universeSection k name) :=
  reflectionGraph_member (NeutralCodes.universePER_laws k) (identity_codeFamily k)
    (identity_legalFiniteDemand (NeutralCodes.UniversePER k)) name

theorem universeSection_application (k : Option Nat) (name : Nat)
    {x : Value} (hx : Member (NeutralCodes.UniversePER k) x) :
    ValueEq (NeutralPi.applyValue (universeSection k name) x)
      (NeutralCodes.reflect x name) :=
  reflectionGraph_application (identity_codeFamily k)
    (identity_legalFiniteDemand (NeutralCodes.UniversePER k)) name hx

namespace VaryingFibreControl

def typeArgument : Value := NeutralCodes.reify (.neutralType (some 1) 701)
def universeArgument : Value := universeValue (some 0)

theorem typeArgument_member : Member (NeutralCodes.UniversePER (some 1)) typeArgument :=
  NeutralCodes.code_member_universe (NeutralCodes.code (.neutralType (some 1) 701))

theorem universeArgument_member :
    Member (NeutralCodes.UniversePER (some 1)) universeArgument :=
  NeutralCodes.universe_member (some 0)

theorem section_at_type (name : Nat) :
    ValueEq (NeutralPi.applyValue (universeSection (some 1) name) typeArgument)
      (NeutralPER.neutralAtom name) :=
  (universeSection_application (some 1) name typeArgument_member).trans
    (NeutralCodes.reflect_at (ValueEq.refl (NeutralCodes.reify (.neutralType (some 1) 701))) name)

theorem section_at_universe (name : Nat) :
    ValueEq (NeutralPi.applyValue (universeSection (some 1) name) universeArgument)
      (NeutralCodes.reify (.neutralType (some 0) name)) :=
  (universeSection_application (some 1) name universeArgument_member).trans
    (NeutralCodes.reflect_at (ValueEq.refl (NeutralCodes.reify (.univ (some 0)))) name)

theorem fibres_differ :
    ¬ Same (decodedEl (some 1) typeArgument) (decodedEl (some 1) universeArgument) := by
  intro h
  have ht : Member (decodedEl (some 1) typeArgument) (NeutralPER.neutralAtom 703) :=
    (decodedEl_same (NeutralCodes.code (.neutralType (some 1) 701)) _ _).mpr
      (NeutralCodes.reflectDescriptor_member (.neutralType (some 1) 701) 703)
  have hu : Member (NeutralCodes.UniversePER (some 0)) (NeutralPER.neutralAtom 703) :=
    (decodedEl_same (NeutralCodes.code_universe (some 0)) _ _).mp ((h _ _).mp ht)
  exact NeutralPER.neutralAtom_not_sort_member 703 (some 0)
    (NeutralCodes.universe_elim (NeutralCodes.code_universe (some 0)) hu).1

theorem outputs_differ (name : Nat) :
    ¬ ValueEq
      (NeutralPi.applyValue (universeSection (some 1) name) typeArgument)
      (NeutralPi.applyValue (universeSection (some 1) name) universeArgument) := by
  intro h
  have he := (section_at_type name).symm.trans (h.trans (section_at_universe name))
  exact NeutralPER.neutralAtom_not_sort_member name (some 0)
    (sortMember_congr he.symm (NeutralCodes.reify_level (.neutralType (some 0) name)))

/-- The corresponding dependent product is well formed in the actual
empty admitted source environment. This is not its missing Pi Code. -/
def sourceType : ExprA :=
  .pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.succ .zero)

def source_admitted : EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA := .empty

def source_type_formed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] sourceType
      (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  .pi [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.succ .zero)
    (.sort [] (.succ .zero))
    (.bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero))
      (.succ (.succ .zero)) rfl (.sort _ (.succ .zero)))

theorem control_inhabited (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] sourceType
      (.sort (.imax (.succ (.succ .zero)) (.succ .zero)))) ∧
    NeutralCodes.Code (some 2) (universeValue (some 1))
      (NeutralCodes.UniversePER (some 1)) ∧
    Member (NeutralCodes.UniversePER (some 1)) typeArgument ∧
    Member (NeutralCodes.UniversePER (some 1)) universeArgument ∧
    Laws (functionPER (some 1) (NeutralCodes.UniversePER (some 1)) (fun x => x)) ∧
    Member (functionPER (some 1) (NeutralCodes.UniversePER (some 1)) (fun x => x))
      (universeSection (some 1) name) ∧
    (¬ Same (decodedEl (some 1) typeArgument) (decodedEl (some 1) universeArgument)) ∧
    (¬ ValueEq
      (NeutralPi.applyValue (universeSection (some 1) name) typeArgument)
      (NeutralPi.applyValue (universeSection (some 1) name) universeArgument)) :=
  ⟨⟨source_admitted⟩, ⟨.nil⟩, ⟨source_type_formed⟩,
    NeutralCodes.code_universe (some 1), typeArgument_member, universeArgument_member,
    functionPER_lawful (NeutralCodes.universePER_laws (some 1)) (identity_codeFamily (some 1)),
    universeSection_member (some 1) name, fibres_differ, outputs_differ name⟩

end VaryingFibreControl

end Rcic.Declarative.Ann.LR3.DecodedPi
