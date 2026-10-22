import rcic.RcicAnnLR3EnrichedReflectionBoundary
import rcic.RcicAnnLR3ConfiguredAliasBoundary

/-!
# The same assembly failure for relational membership

The positive-stage obstruction does not depend on selecting a section or
on requiring a data-valued decoder. Even the weaker proposition saying
that each application has some legal retained representative is false.
Only two existential witnesses are eliminated, inside Prop.

The source application uses the one configured EnvironmentEval policy.
Its two raw environments are equal while its required retained fibres
have disjoint legal erasures. The source admission, context and typing
are actual constructors; the identity codomain producer is supplied by
the imported boundary. No source class or context is removed.

The separate alias control has actual legacy NeutralSupport, yet neither
its fundamental theorem nor its extracted membership port is true. This
prevents treating the valid extraction composition as a producer of its
missing fundamental input. These are boundaries of the specified assembly,
not counterexamples to source SortUniq/ZSC. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.RelationalAssemblyBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open StratifiedCandidates CandidateAction EnrichedReflectionBoundary

/-- A purely relational representative condition. There is no chosen
representative function, and no witness is extracted into Type. -/
def RawMember (C : Code 1) (v : Value) : Prop :=
  ∃ x : Carrier 1, (view 1 C).relation x x ∧
    ValueEq v (StratifiedCandidates.erase 1 x)

theorem rawMember_congr {C : Code 1} {v w : Value}
    (h : ValueEq v w) (hv : RawMember C v) : RawMember C w := by
  obtain ⟨x, hx, he⟩ := hv
  exact ⟨x, hx, h.symm.trans he⟩

theorem no_common_raw_member (v : Value) :
    ¬ (RawMember universeFibre v ∧ RawMember neutralFibre v) := by
  rintro ⟨⟨x, hx, he⟩, ⟨y, hy, hf⟩⟩
  exact legal_erasures_disjoint hx hy (he.symm.trans hf)

/-- Already the proposition-valued product membership obligation fails.
This is weaker than supplying the section refuted in the preceding file. -/
theorem no_relational_raw_application (f : Value) :
    ¬ (∀ C : Code 1, RawMember C (NeutralPi.applyValue f (view 1 C).value)) := by
  intro h
  exact no_common_raw_member _ ⟨h universeFibre, h neutralFibre⟩

theorem no_relational_closed_application (f : Value) :
    ¬ (∀ C : ClosedCode 1,
      RawMember C.code (NeutralPi.applyValue f (eraseCode C))) := by
  intro h
  obtain ⟨x, hx, he⟩ := h closedUniverseFibre
  obtain ⟨y, hy, hf⟩ := h closedNeutralFibre
  exact closed_legal_erasures_disjoint hx hy (he.symm.trans hf)

/-- The source application from the inhabited context, evaluated by the
single configured member policy required by the assembly brief. -/
def applicationImage (ν : Valuation) (ρ : EnvI) (C : ClosedCode 1) : Value :=
  EnvironmentTelescopeInsertion.image emptyEnvA EnvironmentEval.neutralFamilySyntax
    ν (EnvI.cons (eraseCode C) ρ) (.app (.bvar 1) (.bvar 0))

theorem application_images_equal (ν : Valuation) (ρ : EnvI) :
    applicationImage ν ρ closedUniverseFibre =
      applicationImage ν ρ closedNeutralFibre := rfl

/-- No PER saturation or relational reformulation can satisfy these
unchanged fibres at the equal fixed images of the actual application. -/
theorem configured_application_refuted (ν : Valuation) (ρ : EnvI) :
    ¬ (∀ C : ClosedCode 1, RawMember C.code (applicationImage ν ρ C)) := by
  intro h
  obtain ⟨x, hx, he⟩ := h closedUniverseFibre
  obtain ⟨y, hy, hf⟩ := h closedNeutralFibre
  exact closed_legal_erasures_disjoint hx hy (he.symm.trans hf)

theorem relational_boundary_inhabited (ν : Valuation) (ρ : EnvI) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext
      (.app (.bvar 1) (.bvar 0)) (.bvar 0)) ∧
    RawMember universeFibre
      (StratifiedCandidates.erase 1 (universeFibre.point 0)) ∧
    RawMember neutralFibre
      (StratifiedCandidates.erase 1 (neutralFibre.point 0)) ∧
    (∀ f : Value, ¬ (∀ C : ClosedCode 1,
      RawMember C.code (NeutralPi.applyValue f (eraseCode C)))) ∧
    (¬ (∀ C : ClosedCode 1, RawMember C.code (applicationImage ν ρ C))) :=
  ⟨⟨.empty⟩, ⟨application_context_wf⟩, ⟨source_application_typed⟩,
    ⟨universeFibre.point 0, universe_fibre_member 0, ValueEq.refl _⟩,
    ⟨neutralFibre.point 0, neutral_fibre_member 0, ValueEq.refl _⟩,
    no_relational_closed_application, configured_application_refuted ν ρ⟩

/-- A concrete configured model on the old neutral-code fragment. It is
used only as an inhabited extraction control, not as the enriched model. -/
def aliasModel : AnnSemantics :=
  ConfiguredAliasBoundary.model NeutralCodes.codeSystem EnvironmentEval.neutralFamilySyntax

def aliasNeutralSupport : NeutralExtraction.NeutralSupport aliasModel :=
  NeutralCodes.neutralSupport aliasModel.image aliasModel.sort_image

theorem alias_fundamental_refuted :
    ¬ PairedFundamental aliasModel ConfiguredAliasBoundary.env
      (iotaIfaceA ConfiguredAliasBoundary.env) 0 :=
  ConfiguredAliasBoundary.configured_fundamental_refuted _ _

theorem alias_generic_membership_refuted :
    ¬ AnnSortMembershipSound ConfiguredAliasBoundary.env
      (iotaIfaceA ConfiguredAliasBoundary.env) 0
      (NeutralExtraction.genericImage aliasNeutralSupport) :=
  ConfiguredAliasBoundary.configured_sort_membership_refuted _
    (NeutralExtraction.generic aliasNeutralSupport)

/-- All algebra, neutral support, source admission and the empty paired
realization exist. The missing Fundamental is genuinely false for this
fixed policy, so the conditional extraction cannot be instantiated. -/
theorem supported_alias_boundary_inhabited :
    Nonempty (NeutralExtraction.NeutralSupport aliasModel) ∧
    Nonempty (EnvWfA (iotaIfaceA ConfiguredAliasBoundary.env) ConfiguredAliasBoundary.env) ∧
    Nonempty (CtxWfA ConfiguredAliasBoundary.env
      (iotaIfaceA ConfiguredAliasBoundary.env) 0 []) ∧
    Nonempty (HasTyA ConfiguredAliasBoundary.env (iotaIfaceA ConfiguredAliasBoundary.env)
      0 [] (.const 95 []) (.sort .zero)) ∧
    PairedRealises aliasModel ConfiguredAliasBoundary.zeroValuation
      ConfiguredAliasBoundary.zeroValuation [] EnvI.bot EnvI.bot ∧
    (¬ PairedFundamental aliasModel ConfiguredAliasBoundary.env
      (iotaIfaceA ConfiguredAliasBoundary.env) 0) ∧
    (¬ AnnSortMembershipSound ConfiguredAliasBoundary.env
      (iotaIfaceA ConfiguredAliasBoundary.env) 0
      (NeutralExtraction.genericImage aliasNeutralSupport)) :=
  ⟨⟨aliasNeutralSupport⟩, ⟨ConfiguredAliasBoundary.admitted⟩, ⟨.nil⟩,
    ⟨ConfiguredAliasBoundary.source_converted []⟩, .nil _ _,
    alias_fundamental_refuted, alias_generic_membership_refuted⟩

end Rcic.Declarative.Ann.LR3.RelationalAssemblyBoundary
