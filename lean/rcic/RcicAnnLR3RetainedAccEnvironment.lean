import rcic.RcicAnnLR3RetainedAccFamily
import rcic.RcicAnnLR3EnvironmentTelescopeInsertion
import rcic.RcicAnnLR3CandidateAction

/-!
# Positive source-domain supply for the retained Acc family

The actual EnvironmentEval telescope policy interprets the admitted
binary type-valued axiom R. Its source application R y x has the native
retained proposition code used in RetainedAccFamily, uniformly in the
environment and valuation. Both ordinary domains, the guarded inner
domain, and the extracted source index projections have exact images.

Every retained proposition code is covered: CandidateAction.close adds
only bottom to its type value and preserves its entire element PER.
The original and closed codes have equal quotient indices. Thus source
variables have exact erasures without restricting the candidate domain.

These are concrete domain/index supplies for the admitted Acc shape.
Source constructor/recursor hooks and a complete enriched Fundamental
theorem remain separate obligations. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.RetainedAccEnvironment

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily RetainedAccFamily

abbrev closed (A : IndexCode) : CandidateAction.ClosedCode 0 := CandidateAction.close 0 A
abbrev codeValue (A : IndexCode) : Value := CandidateAction.eraseCode (closed A)

theorem close_index (A : IndexCode) : classify (closed A).code = classify A :=
  (classify_related (CandidateAction.completeCode_related 0 A)).symm

theorem close_fibre (A : IndexCode) :
    (StratifiedCandidates.view 0 (closed A).code).relation =
      (StratifiedCandidates.view 0 A).relation := CandidateAction.close_preserves_fibre 0 A

theorem closed_index_member (A : IndexCode) :
    (StratifiedCandidates.universeCode 0).relation
      (StratifiedCandidates.encode 0 (closed A).code)
      (StratifiedCandidates.encode 0 (closed A).code) :=
  StratifiedCandidates.universe_member 0 (closed A).code

def resultEnvironment (A : IndexCode) : EnvI := EnvI.cons (codeValue A) EnvI.bot
def guardEnvironment (A B : IndexCode) : EnvI := EnvI.cons (codeValue B) (resultEnvironment A)
def childEnvironment (A B : IndexCode) (name : Nat) : EnvI :=
  EnvI.cons (NeutralPER.neutralAtom name) (guardEnvironment A B)

/-- Exact source result-index projection for every retained candidate. -/
theorem result_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (A : IndexCode) :
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (resultEnvironment A) (.bvar 0)) (codeValue A) :=
  CandidateAction.bound_image
    (EnvironmentTelescopeInsertion.internalView pinAccGroupEnvA)
    (EnvironmentTelescopeInsertion.hook pinAccGroupEnvA F) ν (resultEnvironment A)
    0 (codeValue A) rfl (closed A).bot

/-- Exact source recursive-index projection below both actual inner
binders; no arbitrary variable-arm supplier is assumed. -/
theorem child_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (A B : IndexCode) (name : Nat) :
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (childEnvironment A B name) (.bvar 1)) (codeValue B) :=
  CandidateAction.bound_image
    (EnvironmentTelescopeInsertion.internalView pinAccGroupEnvA)
    (EnvironmentTelescopeInsertion.hook pinAccGroupEnvA F) ν (childEnvironment A B name)
    1 (codeValue B) rfl (closed B).bot

/-- Exact source image of R y x under the new compositional policy.
The retained code itself is produced by NativeMemberValues. -/
theorem guard_retained (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (StratifiedCandidates.universeCode 0).relation
      (StratifiedCandidates.encode 0 guardCode) (StratifiedCandidates.encode 0 guardCode) ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν ρ pinAccGuardA)
      (StratifiedCandidates.erase 1 (StratifiedCandidates.encode 0 guardCode)) :=
  EnvironmentTelescopeInsertion.retained_telescope_two
    (E := pinAccGroupEnvA) (r := 9) (m := pinAccRelA) (l := .zero) (k := 0)
    rfl rfl F ν ρ [] (.bvar 0) (.bvar 1) rfl

theorem guard_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν ρ pinAccGuardA)
      (StratifiedCandidates.view 0 guardCode).value :=
  (guard_retained F ν ρ).2

theorem sort_domain_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν ρ (.sort .zero))
      (StratifiedCandidates.view 1 (StratifiedCandidates.universeCode 0)).value := by
  rw [EnvironmentTelescopeInsertion.image_sort]
  exact ValueEq.refl _

/-- All three nonrecursive domain tasks in the actual FieldsTy
extraction have supplied retained codes and exact source images. -/
theorem extracted_domain_images (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (A B : IndexCode) :
    (AdmittedFamilyExtractor.domains (pinAccIntroViewA noIotaA).typed).map
      AdmittedFamilyExtractor.DomainTask.type = [.sort .zero, .sort .zero, pinAccGuardA] ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν EnvI.bot (.sort .zero))
      (StratifiedCandidates.view 1 (StratifiedCandidates.universeCode 0)).value ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (resultEnvironment A) (.sort .zero))
      (StratifiedCandidates.view 1 (StratifiedCandidates.universeCode 0)).value ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (guardEnvironment A B) pinAccGuardA) (StratifiedCandidates.view 0 guardCode).value :=
  ⟨rfl, sort_domain_image F ν EnvI.bot, sort_domain_image F ν _, guard_image F ν _⟩

/-- The actual guard fibres agree across both source realizations.
Their relation is supplied, not recovered from an existential code. -/
theorem paired_guard (F : EnvironmentEval.FamilySyntax) (ν μ : Valuation) (ρ σ : EnvI) :
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν ρ pinAccGuardA)
      (StratifiedCandidates.view 0 guardCode).value ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F μ σ pinAccGuardA)
      (StratifiedCandidates.view 0 guardCode).value ∧
    StratifiedCandidates.CodeRelated 0 guardCode guardCode :=
  ⟨guard_image F ν ρ, guard_image F μ σ,
    StratifiedCandidates.related_refl (StratifiedCandidates.view 0 guardCode)⟩

/-- Explicit positions can use the closed recursive code without
changing the family index, and their guard membership is supplied. -/
theorem source_position (A B : IndexCode) (name : Nat) :
    Member guardPER (NeutralPER.neutralAtom name) ∧
    IndexedFamilyDecoder.child semanticData (classify (closed A).code)
      (position (classify (closed A).code) (closed B).code name) = classify B :=
  ⟨guard_reflection name, close_index B⟩

abbrev guardContext : LCtxA := [.assumption (.sort .zero), .assumption (.sort .zero)]

def guardContext_wf : CtxWfA pinAccGroupEnvA noIotaA 0 guardContext :=
  .assumption (.assumption .nil (.sort [] .zero)) (.sort _ .zero)

def guard_typed : HasTyA pinAccGroupEnvA noIotaA 0 guardContext pinAccGuardA (.sort .zero) :=
  pinAccGuardTy (E := pinAccGroupEnvA) (I := noIotaA) (n := 0) (Γ := []) rfl

/-- Admission and source typing are inhabited, both source index
images are supplied for every original retained code, and the guard
has an actual universe code and explicit proof-neutral members. -/
theorem positive_source_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (A B : IndexCode) (name : Nat) :
    Nonempty (EnvWfA noIotaA pinAccGroupEnvA) ∧
    Nonempty (CtxWfA pinAccGroupEnvA noIotaA 0 guardContext) ∧
    Nonempty (HasTyA pinAccGroupEnvA noIotaA 0 guardContext pinAccGuardA (.sort .zero)) ∧
    (StratifiedCandidates.universeCode 0).relation
      (StratifiedCandidates.encode 0 (closed A).code)
      (StratifiedCandidates.encode 0 (closed A).code) ∧
    (StratifiedCandidates.universeCode 0).relation
      (StratifiedCandidates.encode 0 (closed B).code)
      (StratifiedCandidates.encode 0 (closed B).code) ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (resultEnvironment A) (.bvar 0)) (codeValue A) ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (childEnvironment A B name) (.bvar 1)) (codeValue B) ∧
    ValueEq (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν
      (guardEnvironment A B) pinAccGuardA) (StratifiedCandidates.view 0 guardCode).value ∧
    Member guardPER (NeutralPER.neutralAtom name) :=
  ⟨⟨pinAccGroupWfA noIotaA⟩, ⟨guardContext_wf⟩, ⟨guard_typed⟩,
    closed_index_member A, closed_index_member B, result_image F ν A,
    child_image F ν A B name, guard_image F ν _, guard_reflection name⟩

end Rcic.Declarative.Ann.LR3.RetainedAccEnvironment
