import rcic.RcicAnnLR3IndexFamilyHook
import rcic.RcicAnnLR3GuardedNeutralBoundary

/-!
# What the reflected proof of an Eq type must do (AnySort Eq on the Target)

On the Target `annSemantics C (view E) (hook hE (indexHook E))` for the
admitted AnySort Eq environment, the recursor `65` evaluates a call at major
value `h` to `h` applied to its case selector (`recursor_value`,
`recN_apply`). Hence the behaviour of a large-elimination call is decided by
the reflected proof alone:

- **(F1) A neutral proof gives no type** (`neutral_major_not_sort`). If the
  major is a neutral atom, the image of any call `Eq.rec … h` is not a sort
  member at any level. So a large elimination into `Prop` at such a proof
  has no type image, and no code system can decode it.
- **(F2) A refl-shaped proof computes** (`refl_major_computes`, a concrete
  instance). If the major is `refl Prop x`, the call computes to the minor,
  whatever `x` is.

Reading (analysis, not a theorem here): `NeutralSupport` reflects a proof
variable `h : Eq A a b` into the relation of `Eq A a b` for every `a, b`.
For the large elimination to have a type image at the reflected proof, by
(F1) the reflection must not be a neutral atom; a refl-shaped reflection
computes as in (F2). For apart indices the transport `Eq.rec (motive := λ b _. b)`
then sends a closed proof of `a` to a realizer of `b`. That is acceptable in
a level (unit) model, where every type is inhabited and only levels matter,
and it contradicts consistency on closed realizers in a content model.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EqReflectionChoice

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open IotaRecursor AdmissionUniverseReadback EqTargetIota IndexFamilyHook EqLargeFixture

theorem eq_group_counts :
    (iotaGroupA env 65 64).map (fun g => (g.nparams, g.nMinors, g.nindices)) = some (2, 1, 1) := by
  decide

/-- A call of the AnySort Eq recursor with five leading arguments and a
major. -/
def jcall (u : Level) (A a motive minor b major : ExprA) : ExprA :=
  foldAppsA (.const 65 [u]) [A, a, motive, minor, b, major]

/-- (F1) At a neutral major, the call is not a sort member at any level. -/
theorem neutral_major_not_sort (hE : EnvWfA (iotaIfaceA env) env)
    (ν : Valuation) (ρ : EnvI) (u : Level) (A a motive minor b : ExprA) (name : Nat)
    (k : Option Nat) :
    ¬ SortMember k (EnvironmentEval.denote (SemanticMemberEval.view env)
      (hook hE (indexHook env)) ν (EnvI.cons (NeutralPER.neutralAtom name) ρ)
      (jcall u A a motive minor b (.bvar 0))) := by
  obtain ⟨g, hg, hcounts⟩ : ∃ g, iotaGroupA env 65 64 = some g ∧
      (g.nparams, g.nMinors, g.nindices) = (2, 1, 1) := by
    cases h : iotaGroupA env 65 64 with
    | none => have := eq_group_counts; rw [h] at this; cases this
    | some g =>
        have := eq_group_counts
        rw [h] at this
        exact ⟨g, rfl, Option.some.inj this⟩
  simp only [Prod.mk.injEq] at hcounts
  obtain ⟨hnp, hnm, hni⟩ := hcounts
  have hroute := routes_target_of hE eq_ctorRecPi _ (indexHook_ctorRec env)
  let V := SemanticMemberEval.view env
  let H := hook hE (indexHook env)
  let ρ' := EnvI.cons (NeutralPER.neutralAtom name) ρ
  have hrec := recursor_value hroute hg ν ρ' [u]
  rw [hnp, hnm, hni] at hrec
  have hmaj : EnvironmentEval.denote V H ν ρ' (.bvar 0) = NeutralPER.neutralAtom name := by
    rw [NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image V H ν ρ' 0)]
    funext c
    exact propext ⟨fun h => h.elim (fun e => e ▸ .bot _ _) id, Or.inr⟩
  have himg : EnvironmentEval.denote V H ν ρ' (jcall u A a motive minor b (.bvar 0)) =
      NeutralPi.applyValue (NeutralPER.neutralAtom name)
        (denI (bodyEnv (fixValue (genN 2 1 1 (compsN env 65 2 1 1)) ρ') ρ'
          (([A, a, motive, minor, b].map (EnvironmentEval.denote V H ν ρ')).drop 3 |>.take 1)
          (NeutralPER.neutralAtom name)) (selN (compsN env 65 2 1 1))) := by
    show EnvironmentEval.denote V H ν ρ' (foldAppsA (.const 65 [u]) [A, a, motive, minor, b, .bvar 0]) = _
    rw [denote_foldAppsA]
    have hsplit : [A, a, motive, minor, b, ExprA.bvar 0].map (EnvironmentEval.denote V H ν ρ') =
        [A, a, motive, minor, b].map (EnvironmentEval.denote V H ν ρ') ++
          [EnvironmentEval.denote V H ν ρ' (.bvar 0)] := by simp
    rw [hsplit, hrec, hmaj]
    exact recN_apply 2 1 1 _ ρ' _ (by simp) _ (.bot _ _)
  rw [himg]
  exact GuardedNeutralBoundary.atom_application_not_sort name _ (denI_bot _ _) k

/-- (F2) A concrete refl-shaped major: the call computes to its minor. -/
theorem refl_major_computes (hE : EnvWfA (iotaIfaceA env) env)
    (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ
        (jcall (.succ .zero) (.sort .zero) (.sort .zero) (.sort .zero) (.sort .zero) (.sort .zero)
          (reflAt (.sort .zero))) =
      EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ
        (.sort .zero) :=
  denote_iota (routes_target_of hE eq_ctorRecPi _ (indexHook_ctorRec env))
    EqTracer.eq_firstOrderArity (by decide) ν ρ

end Rcic.Declarative.Ann.LR3.EqReflectionChoice
