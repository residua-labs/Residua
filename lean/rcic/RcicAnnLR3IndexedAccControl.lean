import rcic.RcicAnnLR3IndexedFamilyDecoder
import rcic.RcicAnnLR3EnvironmentEval
import rcic.RcicAnnLR3InductiveCodes

/-!
# Indexed Acc data and the actual evaluator's guarded-domain boundary

The legal index quotient has distinct inhabited classes. An explicit
two-binder position carries the recursive index and a legal guard value;
its child map and the constructor result map descend without choice.
The result and child projections agree with the actual EnvironmentEval
images of the indices extracted from the admitted Acc constructor.

The chosen guard PER below is a supplied semantic skeleton, not a claimed
interpretation of the source guard. The final inhabited boundary shows
exactly why: the current raw Pi-axiom policy gives the actual source R y x
a non-type-tagged spine observation. It has no existing CodeI, even with
the actual admission, source typing and paired realization supplied.
This refutes that evaluator policy, not the admitted Acc class.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.IndexedAccControl

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open TypedInductive NeutralDataFamily FiniteFamilyLabels

abbrev indexDomain : Relation := NeutralCodes.UniversePER (some 0)

def indexTelescope : Telescope 1 := .snoc .empty (fun _ => indexDomain)

theorem indexCoherent : Coherent indexTelescope :=
  coherent_snoc coherent_empty (fun _ _ => NeutralCodes.universePER_laws (some 0))
    (fun _ _ _ _ _ => Iff.rfl)

abbrev Index := Class indexCoherent
abbrev IndexLabel := Label indexTelescope

def indexLabel (P : Prop) : IndexLabel :=
  snocLabel emptyLabel (NeutralCodes.proofCodeValue P)
    ⟨.proof P, .proof P, rfl, NeutralCodes.related_refl _, ValueEq.refl _, ValueEq.refl _⟩

def index (P : Prop) : Index := classify indexCoherent (indexLabel P)

theorem indices_distinct : index False ≠ index True := by
  intro h
  have hr : LabelRel (indexLabel False) (indexLabel True) := Quotient.exact h
  obtain ⟨d, e, _, hde, hd, he⟩ := hr.2
  have ed : d = .proof False := NeutralCodes.reify_injective hd.symm
  have ee : e = .proof True := NeutralCodes.reify_injective he.symm
  subst d
  subst e
  exact hde.mpr True.intro

abbrev guardDomain : Relation := NeutralCodes.El (.proof False)

/-- The two inner binders remain explicit data. The code for the actual
source guard is deliberately not claimed here. -/
structure Position (_q : Index) where
  recursiveIndex : IndexLabel
  guardValue : Value
  guardMember : Member guardDomain guardValue

def positionIndex {q : Index} (p : Position q) : Index :=
  classify indexCoherent p.recursiveIndex

theorem positionIndex_transport {q r : Index} (h : q = r) (p : Position q) :
    positionIndex (DependentFamily.transport Position h p) = positionIndex p := by
  cases h
  rfl

/-- The result/child data are supplied here, not assumed as a decoder. -/
def semanticData : IndexedFamilyDecoder.RawData (labelSetoid indexCoherent) Position Index where
  result := classify indexCoherent
  result_coherent := fun _ _ h => classify_related indexCoherent h
  child := fun _ p => positionIndex p
  child_coherent := fun _ _ h p => (positionIndex_transport (Quotient.sound h) p).symm

abbrev signature := IndexedFamilyDecoder.signature semanticData
def leafRel (_i : Index) (a b : Nat) : Prop := a = b
theorem leaf_laws (i : Index) : RelLaws (leafRel i) := ⟨Eq.symm, Eq.trans⟩

def recursivePosition : Position (index False) :=
  ⟨indexLabel True, NeutralPER.neutralAtom 7,
    NeutralCodes.reflectDescriptor_member (.proof False) 7⟩

theorem result_index :
    IndexedFamilyDecoder.result semanticData (index False) = index False := rfl

theorem child_index :
    IndexedFamilyDecoder.child semanticData (index False) recursivePosition = index True := rfl

def children (q : Index) : IndexedFamilyDecoder.Children semanticData (fun _ => Nat) leafRel q :=
  fun p => legalNeutral signature (fun _ => Nat) leafRel
    (IndexedFamilyDecoder.child semanticData q p) 7 rfl

def major : IndexedFamilyDecoder.Legal semanticData (fun _ => Nat) leafRel (index False) :=
  IndexedFamilyDecoder.nodeClass semanticData (fun _ => Nat) leafRel (index False)
    (children (index False))

theorem indexed_major_inhabited :
    IndexedFamilyDecoder.result semanticData (index False) = index False ∧
    IndexedFamilyDecoder.child semanticData (index False) recursivePosition = index True ∧
    index False ≠ index True ∧ Bisim signature (fun _ => Nat) leafRel major.1 major.1 :=
  ⟨result_index, child_index, indices_distinct, major.2⟩

/-- Exact index expressions retained by the actual admitted source view. -/
theorem extracted_indices :
    (AdmittedFamilyExtractor.indices (pinAccIntroViewA noIotaA).typed).map
      AdmittedFamilyExtractor.IndexTask.arguments = [[.bvar 1], [.bvar 0]] := rfl

theorem extracted_domains :
    (AdmittedFamilyExtractor.domains (pinAccIntroViewA noIotaA).typed).map
      AdmittedFamilyExtractor.DomainTask.type = [.sort .zero, .sort .zero, pinAccGuardA] := rfl

abbrev resultEnvironment : EnvI := EnvI.cons (NeutralCodes.proofCodeValue False) EnvI.bot
abbrev guardEnvironment : EnvI := EnvI.cons (NeutralCodes.proofCodeValue True) resultEnvironment
abbrev childEnvironment : EnvI := EnvI.cons (NeutralPER.neutralAtom 7) guardEnvironment

/-- Exact images for the two extracted index projections, not a general
variable contract or a source family interpretation. -/
theorem result_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    ValueEq (EnvironmentEval.denote pinAccGroupEnvA F ν resultEnvironment (.bvar 0))
      (NeutralCodes.proofCodeValue False) := by
  apply (EnvironmentEval.denote_core pinAccGroupEnvA F ν resultEnvironment
    (e := .bvar 0) True.intro).trans
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with h | h
    · cases h
      exact Or.inl rfl
    · exact h
  · intro hc
    exact .bvar hc

theorem child_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    ValueEq (EnvironmentEval.denote pinAccGroupEnvA F ν childEnvironment (.bvar 1))
      (NeutralCodes.proofCodeValue True) := by
  apply (EnvironmentEval.denote_core pinAccGroupEnvA F ν childEnvironment
    (e := .bvar 1) True.intro).trans
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with h | h
    · cases h
      exact Or.inl rfl
    · exact h
  · intro hc
    exact .bvar hc

abbrev guardContext : LCtxA := [.assumption (.sort .zero), .assumption (.sort .zero)]

def admitted : EnvWfA noIotaA pinAccGroupEnvA := pinAccGroupWfA noIotaA

def guardContext_wf : CtxWfA pinAccGroupEnvA noIotaA 0 guardContext :=
  .assumption (.assumption .nil (.sort [] .zero)) (.sort _ .zero)

def guard_typed : HasTyA pinAccGroupEnvA noIotaA 0 guardContext pinAccGuardA (.sort .zero) :=
  pinAccGuardTy (E := pinAccGroupEnvA) (I := noIotaA) (n := 0) (Γ := []) rfl

def model (F : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  EnvironmentEval.annSemantics InductiveCodes.legacyUniverseSystem pinAccGroupEnvA F

theorem proposition_code (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (Γ : LCtxA) (ρ : EnvI) :
    (model F).Code (some 1) ((model F).image ν Γ ρ (.sort .zero)) indexDomain := by
  rw [(model F).sort_image]
  exact .old (NeutralCodes.code_universe (some 0))

theorem guard_realises (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    PairedRealises (model F) ν ν guardContext guardEnvironment guardEnvironment :=
  .assumption
    (.assumption (.nil EnvI.bot EnvI.bot)
      (CodePair.diagonal (proposition_code F ν [] EnvI.bot)) (indexLabel False).2.2)
    (CodePair.diagonal (proposition_code F ν _ resultEnvironment)) (indexLabel True).2.2

/-- The actual Pi-valued axiom is still interpreted as a raw atom. Both
applications consequently contain this non-type-tagged spine observation. -/
theorem guard_observed (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote pinAccGroupEnvA F ν ρ pinAccGuardA (.spine 9 [.bot, .bot]) := by
  refine ⟨.app (.app (.const 9 []) (.bvar 0)) (.bvar 1), ?_, ?_⟩
  · exact .app (.app (.constRigid rfl) (.bvar 0)) (.bvar 1)
  · exact ApproxI.appSpine
      (ApproxI.appSpine (ApproxI.const ρ 9 []) (ApproxI.bot ρ (.bvar 0)))
      (ApproxI.bot ρ (.bvar 1))

theorem raw_guard_no_code (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (k : Option Nat) (R : Relation) :
    ¬ InductiveCodes.CodeI k (EnvironmentEval.denote pinAccGroupEnvA F ν ρ pinAccGuardA) R := by
  intro hc
  have htag := InductiveCodes.code_level hc _ (guard_observed F ν ρ)
  cases htag

/-- Every source, context and realization premise of this failed code
synthesis instance is inhabited. It names the raw Pi-axiom policy, not a
failure of the indexed Acc class or of quotient descent. -/
theorem inhabited_guard_boundary (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    Nonempty (EnvWfA noIotaA pinAccGroupEnvA) ∧
    Nonempty (CtxWfA pinAccGroupEnvA noIotaA 0 guardContext) ∧
    Nonempty (HasTyA pinAccGroupEnvA noIotaA 0 guardContext pinAccGuardA (.sort .zero)) ∧
    PairedRealises (model F) ν ν guardContext guardEnvironment guardEnvironment ∧
    ValuationRel ν ν ∧
    (AdmittedFamilyExtractor.domains (pinAccIntroViewA noIotaA).typed).map
      AdmittedFamilyExtractor.DomainTask.type = [.sort .zero, .sort .zero, pinAccGuardA] ∧
    (¬ ∃ R, InductiveCodes.CodeI (some 0)
      (EnvironmentEval.denote pinAccGroupEnvA F ν guardEnvironment pinAccGuardA) R) :=
  ⟨⟨admitted⟩, ⟨guardContext_wf⟩, ⟨guard_typed⟩, guard_realises F ν,
    ValuationRel.refl ν, extracted_domains, fun ⟨R, hR⟩ => raw_guard_no_code F ν _ _ R hR⟩

end Rcic.Declarative.Ann.LR3.IndexedAccControl
