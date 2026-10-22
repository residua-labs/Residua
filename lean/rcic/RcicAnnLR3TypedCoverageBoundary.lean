import rcic.RcicAnnLR3TypedArmBoundary

/-!
# Exact Realises/Representative boundary, in an axiom-free admitted family

The source environment contains only the empty inductive Prop family, no
source axiom. Its context with an assumed proof is well formed, but has no
realisation in the concrete truth-valued code system. Thus Representative,
the additional input of ann_membership_of_fundamental, is actually false
for this candidate. This does not refute source sort uniqueness or a
relative fundamental theorem on realised contexts.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedCoverageBoundary
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TruthAxiomBoundary TypedConstantModel

abbrev emptyContext : LCtxA := [.assumption emptyType]

def emptyContext_wf : CtxWfA familyEnv (iotaIfaceA familyEnv) 0 emptyContext :=
  .assumption .nil (emptyType_typed rfl)

def emptyMajor_typed : HasTyA familyEnv (iotaIfaceA familyEnv) 0 emptyContext
    (.bvar 0) emptyType :=
  .bvar emptyContext 0 emptyType .zero rfl (emptyType_typed rfl)

theorem emptyContext_no_realization (ν : Valuation) :
    ¬ ∃ ρ : EnvI, Realises model ν emptyContext ρ := by
  rintro ⟨ρ, hρ⟩
  cases hρ with
  | assumption tail code member =>
      exact code_at_empty_no_member code _ member

theorem representative_false (choose : Valuation → LCtxA → EnvI) :
    ¬ Representative model familyEnv (iotaIfaceA familyEnv) 0 choose := by
  intro h
  exact emptyContext_no_realization (fun _ => none)
    ⟨choose (fun _ => none) emptyContext, h (fun _ => none) emptyContext emptyContext_wf⟩

/-- No source axiom is hidden in this environment. -/
theorem familyEnv_no_axioms :
    ∀ r m, familyEnv.members r = some m → m.mclass ≠ .axiomM := by
  intro r m hm
  by_cases hr : r = 80
  · subst r
    have he : emptyFamily = m := Option.some.inj hm
    subst m
    intro h
    cases h
  · have hf : familyEnv.members r = none := by
      simp only [familyEnv, extendEnvA, emptyEnvA, if_neg hr]
    rw [hf] at hm
    cases hm

theorem inhabited_coverage_boundary :
    Nonempty (EnvWfA (iotaIfaceA familyEnv) familyEnv) ∧
    (∀ r m, familyEnv.members r = some m → m.mclass ≠ .axiomM) ∧
    Nonempty (CtxWfA familyEnv (iotaIfaceA familyEnv) 0 emptyContext) ∧
    Nonempty (HasTyA familyEnv (iotaIfaceA familyEnv) 0 [] emptyType (.sort .zero)) ∧
    Nonempty (HasTyA familyEnv (iotaIfaceA familyEnv) 0 emptyContext (.bvar 0) emptyType) ∧
    Nonempty (HasTyA familyEnv (iotaIfaceA familyEnv) 0 emptyContext
      (.sort .zero) (.sort (.succ .zero))) ∧
    (∀ ν, ¬ ∃ ρ, Realises model ν emptyContext ρ) ∧
    (∀ choose, ¬ Representative model familyEnv (iotaIfaceA familyEnv) 0 choose) :=
  ⟨⟨family_admitted _⟩, familyEnv_no_axioms, ⟨emptyContext_wf⟩,
    ⟨emptyType_typed rfl⟩, ⟨emptyMajor_typed⟩, ⟨.sort emptyContext .zero⟩,
    emptyContext_no_realization, representative_false⟩

end Rcic.Declarative.Ann.LR3.TypedCoverageBoundary
