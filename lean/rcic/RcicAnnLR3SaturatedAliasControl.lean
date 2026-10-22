import rcic.RcicAnnLR3ConfiguredAliasBoundary
import rcic.RcicAnnLR3NeutralControls

/-!
# Exact source const control for the admitted alias environment

This adapter turns two independently proved evaluator equations into the
exact PairedArms.Ty_const contract for the two-member alias fixture. The
target uses the existing exact SortPER universe attachment, which accepts
native tagged values. It is a local control attachment, not the requested
unified enriched source model. Concrete equations are supplied separately;
this helper is not counted as a uniform source supplier. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SaturatedAliasControl

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

def model (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  EnvironmentEval.annSemantics NeutralControls.codeSystem E F

structure Equations (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) : Prop where
  alias_image : ∀ ν ρ, ValueEq (EnvironmentEval.denote E F ν ρ (.const 94 []))
    (universeValue (some 0))
  member_image : ∀ ν ρ, ValueEq (EnvironmentEval.denote E F ν ρ (.const 95 []))
    (NativeMemberValues.value (some 0) 95)

theorem alias_type_goal {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    (h : Equations E F) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    PairedTyGoal (model E F) ConfiguredAliasBoundary.env I n Γ
      (.const 94 []) (.sort ConfiguredAliasBoundary.one) := by
  intro hΓ ν μ ρ σ hν hρ
  have hs := PairedArms.ty_sort_supplied (model E F) ConfiguredAliasBoundary.env
    I n Γ .zero hΓ ν μ ρ σ hν hρ
  have hl : (model E F).image ν Γ ρ (.const 94 []) =
      (model E F).image ν Γ ρ (.sort .zero) := by
    rw [(model E F).sort_image]
    exact NeutralCodes.valueEq_eq (h.alias_image ν ρ)
  have hr : (model E F).image μ Γ σ (.const 94 []) =
      (model E F).image μ Γ σ (.sort .zero) := by
    rw [(model E F).sort_image]
    exact NeutralCodes.valueEq_eq (h.alias_image μ σ)
  simpa only [PairedJudgment, hl, hr] using hs

theorem member_goal {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    (h : Equations E F) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    PairedTyGoal (model E F) ConfiguredAliasBoundary.env I n Γ
      (.const 95 []) (.const 94 []) := by
  intro _ ν μ ρ σ _ _
  have hl := h.member_image ν ρ
  have hr := h.member_image μ σ
  refine ⟨some 1, SortPER (some 0), SortPER (some 0), ?_, ?_⟩
  · refine ⟨?_, ?_, fun _ _ => Iff.rfl⟩
    · change NeutralControls.Code (some 1)
        (EnvironmentEval.denote E F ν ρ (.const 94 [])) (SortPER (some 0))
      rw [NeutralCodes.valueEq_eq (h.alias_image ν ρ)]
      exact NeutralControls.code_universe (some 0)
    · change NeutralControls.Code (some 1)
        (EnvironmentEval.denote E F μ σ (.const 94 [])) (SortPER (some 0))
      rw [NeutralCodes.valueEq_eq (h.alias_image μ σ)]
      exact NeutralControls.code_universe (some 0)
  · exact ⟨sortMember_congr hl.symm (NativeMemberValues.value_level _ _),
      typeDefined_congr hl.symm (NativeMemberValues.value_defined _ _),
      hl.trans hr.symm⟩

/-- Resolution in the admitted fixture has exactly the two real members. -/
theorem member_resolution {r : Nat} {m : CheckedMemberA}
    (h : ConfiguredAliasBoundary.env.members r = some m) :
    (r = 94 ∧ m = ConfiguredAliasBoundary.aliasMember) ∨
      (r = 95 ∧ m = ConfiguredAliasBoundary.member) := by
  by_cases h95 : r = 95
  · subst r
    exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
  · by_cases h94 : r = 94
    · subst r
      exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
    · simp [ConfiguredAliasBoundary.env, ConfiguredAliasBoundary.aliasEnv,
        extendEnvA, emptyEnvA, h95, h94] at h

theorem ty_const_of_equations {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    (h : Equations E F) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_const (model E F) ConfiguredAliasBoundary.env I n := by
  intro Γ r ls m _ hres hlen _ _ _
  rcases member_resolution hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hnil : ls = [] := List.length_eq_zero.mp hlen
    subst ls
    exact alias_type_goal h I n Γ
  · have hnil : ls = [] := List.length_eq_zero.mp hlen
    subst ls
    exact member_goal h I n Γ

end Rcic.Declarative.Ann.LR3.SaturatedAliasControl
