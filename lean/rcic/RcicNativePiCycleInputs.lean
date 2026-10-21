import rcic.RcicNativeTypedModelRel

/-!
# Pi-cycle audit: the raw backward-transport input is inconsistent

`ReadbackLaws` contains beta for every raw expression.  `ApproxT` has typed
lambda demands.  These facts forbid raw backward compact transport, even at
the exact `pi bot []` observation and for every environment and model valuation.

Take a lambda expression `D` as the domain annotation of an identity function.
Every compact of `D` is bottom or a lambda compact, and `CTyS` admits only bottom
at either such code.  The identity's output is therefore bottom only.  Applying
it to a syntactic Pi nevertheless beta-reduces to that Pi, which always has the
Pi probe.  The raw beta step is deliberately not a typed redex: the audited
input quantifies over all raw steps and supplies no source typing hypothesis.

The final theorem uses the exact main-language forall shape of the backward
input being audited.  No pending-branch definition is imported or copied.  This
refutes that input's compatibility with `ReadbackLaws`; it does not refute a
typing-restricted replacement or a derivation-size decrease theorem.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiCycleInputAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

/-- A variable in demands typed at an approximant of a syntactic lambda has
only the bottom compact.  This is the demanded-variable obstruction before
any application or readback is involved. -/
theorem approxT_bvar_lamDomain_bot {E : ResolvedEnv} {ρ : EnvT}
    {A body : Expr Nat} {a c : CptT} {us : List CptT}
    (hA : ApproxT E ρ (.lam A body) a)
    (hT : ∀ u ∈ us, CTyS E u a)
    (hc : ApproxT E (EnvT.cons (demandT us) ρ) (.bvar 0) c) : c = .bot := by
  rcases approxT_bvar_inv hc with hbot | hmem
  · exact hbot
  · have htyped := hT c hmem
    rcases approxT_lam_inv hA with hbot | ⟨a', g, heq, _⟩
    · rw [hbot] at htyped
      exact ctyS_bot_inv htyped
    · rw [heq] at htyped
      exact ctyS_lam_inv htyped

/-- An identity annotated by a lambda domain cannot transmit a nonbottom
compact from any argument.  The proof consumes the actual typed-demand
clauses of the landed model. -/
theorem approxT_app_identity_lamDomain_bot {E : ResolvedEnv} {ρ : EnvT}
    {A body arg : Expr Nat} {c : CptT}
    (h : ApproxT E ρ (.app (.lam (.lam A body) (.bvar 0)) arg) c) : c = .bot := by
  rcases approxT_app_inv h with hbot | ⟨g, s, heq, hf, hs, _⟩ |
      ⟨r, args, u, _, hf, _⟩
  · exact hbot
  · rcases approxT_lam_inv hf with hbot | ⟨a, g', hg, hA, _, hb⟩
    · exact CptT.noConfusion hbot
    · injection hg with hgg
      subst g'
      exact heq.trans (approxT_bvar_lamDomain_bot hA (hb s hs).1 (hb s hs).2)
  · rcases approxT_lam_inv hf with hbot | ⟨a, g, heq, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion heq

/-- Even the demanded factorization at the Pi probe fails for this raw beta
redex.  Thus an unrestricted typed-demand beta-expansion assumption cannot
be treated as a paid port of the untyped model's substitution law. -/
theorem no_pi_probe_lamDomain_factorization (E : ResolvedEnv) (ρ : EnvT)
    (A body : Expr Nat) :
    ¬ ∃ (a : CptT) (us : List CptT),
      ApproxT E ρ (.lam A body) a ∧ (∀ u ∈ us, CTyS E u a) ∧
      ApproxT E (EnvT.cons (demandT us) ρ) (.bvar 0) (.pi .bot []) := by
  rintro ⟨a, us, hA, hT, hbody⟩
  exact CptT.noConfusion (approxT_bvar_lamDomain_bot hA hT hbody)

/-- A concrete witness, uniform in the environment, context, valuation and
readback: beta exists, the reduct has the exact Pi probe, and the source lacks it. -/
theorem pi_probe_backward_obstruction {R : Readback} {E : ResolvedEnv}
    (hL : ReadbackLaws E R) (Γ : LCtx) (ρ : EnvT) :
    let D : Expr Nat := .lam (.sort .zero) (.bvar 0)
    let P : Expr Nat := .pi (.sort .zero) (.sort .zero)
    R Γ (.app (.lam D (.bvar 0)) P) P ∧
      ApproxT E ρ P (.pi .bot []) ∧
      ¬ ApproxT E ρ (.app (.lam D (.bvar 0)) P) (.pi .bot []) := by
  dsimp only
  refine ⟨hL.beta _ _ _ _, approxT_pi_bot_nil _ _ _ _, ?_⟩
  intro h
  exact CptT.noConfusion (approxT_app_identity_lamDomain_bot h)

/-- Restricting raw backward transport to `pi bot []` does not repair the
problem.  No normal-form uniqueness or fundamental lemma is used in the refutation. -/
theorem not_raw_pi_probe_back {R : Readback} {E : ResolvedEnv}
    (hL : ReadbackLaws E R) (Γ : LCtx) (ρ : EnvT) :
    ¬ (∀ {a b : Expr Nat}, R Γ a b →
      ApproxT E ρ b (.pi .bot []) → ApproxT E ρ a (.pi .bot [])) := by
  intro hinv
  obtain ⟨hs, hp, hnot⟩ := pi_probe_backward_obstruction hL Γ ρ
  exact hnot (hinv hs hp)

/-- The exact unrestricted backward-input shape is false for every readback
satisfying the landed readback laws, even at a single fixed context and valuation. -/
theorem not_raw_approxT_back {R : Readback} {E : ResolvedEnv}
    (hL : ReadbackLaws E R) (Γ : LCtx) (ρ : EnvT) :
    ¬ (∀ {a b : Expr Nat} {c : CptT},
      R Γ a b → ApproxT E ρ b c → ApproxT E ρ a c) := by
  intro hinv
  exact not_raw_pi_probe_back hL Γ ρ (fun hs hc => hinv hs hc)

/-- There is no witness to the pair of readback laws and raw ApproxT backward
transport.  This is an unsatisfiable hypothesis package, independently of any
claimed derivation-size induction or Π-injectivity conclusion. -/
theorem no_readback_with_raw_approxT_back (E : ResolvedEnv) (Γ : LCtx) (ρ : EnvT) :
    ¬ ∃ R : Readback, ReadbackLaws E R ∧
      (∀ {a b : Expr Nat} {c : CptT},
        R Γ a b → ApproxT E ρ b c → ApproxT E ρ a c) := by
  rintro ⟨R, hL, hinv⟩
  exact not_raw_approxT_back hL Γ ρ hinv

-- BEGIN RCIC_PI_CYCLE_INPUT_ROOTS
#print axioms approxT_bvar_lamDomain_bot
#print axioms approxT_app_identity_lamDomain_bot
#print axioms no_pi_probe_lamDomain_factorization
#print axioms pi_probe_backward_obstruction
#print axioms not_raw_pi_probe_back
#print axioms not_raw_approxT_back
#print axioms no_readback_with_raw_approxT_back
-- END RCIC_PI_CYCLE_INPUT_ROOTS

end Rcic.Declarative.NativeValleys.PiCycleInputAudit
