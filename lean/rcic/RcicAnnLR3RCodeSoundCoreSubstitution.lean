import rcic.RcicAnnLR3RCodeSoundPiControl
import rcic.RcicAnnSubstTy

/-!
# CoreFree source substitution for contextual sound sections

CoreFree is closed under the actual annotated lift and instantiation
operations. On that fragment the inherited evaluator agrees with the
native core interpretation, so its exact insert/drop substitution law
transfers to the environment-aware evaluator. The zero-index specialization
uses the actual cons environment.

For an already constructed uniform Section, substitution of an actual
domain fragment evaluates to the retained section output in the matching
extended world. The argument erasure law supplies the required equality
of raw environments. A separate source-typing construction applies the
existing hasTyA_inst0 theorem with its explicit environment and iota
stability hypotheses. No source-evaluator closure premise is substituted
for either conclusion.

Constants and literals are excluded by the displayed CoreFree premises.
The type-image theorem additionally requires CoreFree of the codomain.
These results connect an existing common body to source substitution;
they do not construct a Section from pointwise realizations or one fresh
readback, establish general Kripke naturality, or certify a Pi generator.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentEval

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel

theorem core_free_lift (e : ExprA) (c k : Nat) :
    CoreFree e → CoreFree (liftA c k e) := by
  induction e generalizing c with
  | bvar i =>
      intro _
      simp only [liftA]
      split <;> trivial
  | sort l => intro _; trivial
  | const r ls => intro h; exact False.elim h
  | app f a ihf iha =>
      intro h
      exact ⟨ihf c h.1, iha c h.2⟩
  | lam A u b ihA ihb =>
      intro h
      exact ⟨ihA c h.1, ihb (c + 1) h.2⟩
  | pi A u B v ihA ihB =>
      intro h
      exact ⟨ihA c h.1, ihB (c + 1) h.2⟩
  | letE A v b ihA ihv ihb =>
      intro h
      exact ⟨ihA c h.1, ihv c h.2.1, ihb (c + 1) h.2.2⟩
  | lit n => intro h; exact False.elim h

theorem core_free_instantiate (e : ExprA) (j : Nat) (s : ExprA) :
    CoreFree e → CoreFree s → CoreFree (instantiateA j s e) := by
  induction e generalizing j s with
  | bvar i =>
      intro _ hs
      simp only [instantiateA]
      split
      · exact hs
      · split <;> trivial
  | sort l => intro _ _; trivial
  | const r ls => intro h _; exact False.elim h
  | app f a ihf iha =>
      intro h hs
      exact ⟨ihf j s h.1 hs, iha j s h.2 hs⟩
  | lam A u b ihA ihb =>
      intro h hs
      exact ⟨ihA j s h.1 hs,
        ihb (j + 1) (liftA 0 1 s) h.2 (core_free_lift s 0 1 hs)⟩
  | pi A u B v ihA ihB =>
      intro h hs
      exact ⟨ihA j s h.1 hs,
        ihB (j + 1) (liftA 0 1 s) h.2 (core_free_lift s 0 1 hs)⟩
  | letE A v b ihA ihv ihb =>
      intro h hs
      exact ⟨ihA j s h.1 hs, ihv j s h.2.1 hs,
        ihb (j + 1) (liftA 0 1 s) h.2.2 (core_free_lift s 0 1 hs)⟩
  | lit n => intro h _; exact False.elim h

theorem core_free_instantiate0 (s e : ExprA) (hs : CoreFree s) (he : CoreFree e) :
    CoreFree (instantiate0A s e) := core_free_instantiate e 0 s he hs

/-- Exact substitution with the evaluator's own argument image. The
replacement is evaluated in drop rho j, and lifted by j in the source,
exactly as in the inherited native substitution theorem. -/
theorem denote_core_substitution (E : ResolvedEnvA) (F : FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (j : Nat) (s e : ExprA)
    (hs : CoreFree s) (he : CoreFree e) :
    ValueEq (denote E F ν ρ (instantiateA j (liftA 0 j s) e))
      (denote E F ν (EnvI.insert ρ j (denote E F ν (EnvI.drop ρ j) s)) e) := by
  have hi : CoreFree (instantiateA j (liftA 0 j s) e) :=
    core_free_instantiate e j (liftA 0 j s) he (core_free_lift s 0 j hs)
  have hsEq := NeutralCodes.valueEq_eq (denote_core E F ν (EnvI.drop ρ j) hs)
  rw [hsEq]
  apply (denote_core E F ν ρ hi).trans
  apply (show ValueEq (UnitModel.denote ν ρ (instantiateA j (liftA 0 j s) e))
      (UnitModel.denote ν
        (EnvI.insert ρ j (UnitModel.denote ν (EnvI.drop ρ j) s)) e) from
    fun c => UnitModel.denote_substitution ν ρ j s e c).trans
  exact (denote_core E F ν
    (EnvI.insert ρ j (UnitModel.denote ν (EnvI.drop ρ j) s)) he).symm

theorem denote_core_substitution0 (E : ResolvedEnvA) (F : FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (s e : ExprA)
    (hs : CoreFree s) (he : CoreFree e) :
    ValueEq (denote E F ν ρ (instantiate0A s e))
      (denote E F ν (EnvI.cons (denote E F ν ρ s) ρ) e) := by
  simpa only [liftA_zero, EnvI.insert_zero, EnvI.drop_zero] using
    denote_core_substitution E F ν ρ 0 s e hs he

end Rcic.Declarative.Ann.LR3.EnvironmentEval

namespace Rcic.Declarative.Ann.LR3.RCodeSoundPi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower RCodeSoundInterface

universe u v w z

variable {W : World} {a b : Nat} {A : RCodeSound.{u,v} W a}
variable {B : ExprA} {lB : Level}

/-- The explicit CoreFree codomain premise makes the instantiated source
type image agree with the retained fibre at the evaluated argument. -/
theorem Family.core_substitution_type_image (D : Family.{u,v,w,z} A b B lB)
    (arg : A.Fragment) (harg : EnvironmentEval.CoreFree (A.source arg).term)
    (hB : EnvironmentEval.CoreFree B) :
    ValueEq (W.evaluate (instantiate0A (A.source arg).term B))
      (D.fibre (A.evalSem arg)).code.view.value := by
  have hsub := EnvironmentEval.denote_core_substitution0 W.env W.family W.valuation
    W.rawEnvironment (A.source arg).term B harg hB
  have hargEq : EnvironmentEval.denote W.env W.family W.valuation W.rawEnvironment
      (A.source arg).term = A.code.erase (A.evalSem arg).val :=
    (NeutralCodes.valueEq_eq (A.erasure arg)).symm
  rw [hargEq] at hsub
  exact hsub.trans (D.codomainImage (A.evalSem arg))

/-- This connects the existing one-source-body section to actual source
substitution. It does not construct its fragments or its respect law. -/
theorem Section.core_substitution {D : Family.{u,v,w,z} A b B lB}
    (s : Section D) (arg : A.Fragment)
    (harg : EnvironmentEval.CoreFree (A.source arg).term)
    (hbody : EnvironmentEval.CoreFree s.body) :
    ValueEq (W.evaluate (instantiate0A (A.source arg).term s.body))
      ((D.fibre (A.evalSem arg)).erase
        ((D.fibre (A.evalSem arg)).evalSem (s.fragment (A.evalSem arg)))) := by
  have hsub := EnvironmentEval.denote_core_substitution0 W.env W.family W.valuation
    W.rawEnvironment (A.source arg).term s.body harg hbody
  have hargEq : EnvironmentEval.denote W.env W.family W.valuation W.rawEnvironment
      (A.source arg).term = A.code.erase (A.evalSem arg).val :=
    (NeutralCodes.valueEq_eq (A.erasure arg)).symm
  rw [hargEq] at hsub
  exact hsub.trans (s.sourceBody.image (A.evalSem arg))

/-- Actual source substitution typing uses the inherited syntactic
theorem. These environment/iota hypotheses are explicit and are not
silently inferred from the Sound world's weaker admission fields. -/
def Section.substitutionTyped {D : Family.{u,v,w,z} A b B lB}
    (s : Section D) (arg : A.Fragment)
    (hE : EnvClosedA W.env) (hI : IotaLiftA W.iota)
    (hR : IotaRecHeadTypedA W.env W.iota) (hIS : IotaSubstA W.iota) :
    HasTyA W.env W.iota W.levelCount W.context
      (instantiate0A (A.source arg).term s.body)
      (instantiate0A (A.source arg).term B) :=
  hasTyA_inst0 hE hI hR hIS W.contextWf s.bodyTyped (A.source arg).typed A.typeTyped

def Section.substitutedSource {D : Family.{u,v,w,z} A b B lB}
    (s : Section D) (arg : A.Fragment)
    (hE : EnvClosedA W.env) (hI : IotaLiftA W.iota)
    (hR : IotaRecHeadTypedA W.env W.iota) (hIS : IotaSubstA W.iota) :
    Source W (instantiate0A (A.source arg).term B) :=
  ⟨instantiate0A (A.source arg).term s.body, s.substitutionTyped arg hE hI hR hIS⟩

theorem Section.core_substitution_typed {D : Family.{u,v,w,z} A b B lB}
    (s : Section D) (arg : A.Fragment)
    (harg : EnvironmentEval.CoreFree (A.source arg).term)
    (hbody : EnvironmentEval.CoreFree s.body)
    (hE : EnvClosedA W.env) (hI : IotaLiftA W.iota)
    (hR : IotaRecHeadTypedA W.env W.iota) (hIS : IotaSubstA W.iota) :
    Nonempty (HasTyA W.env W.iota W.levelCount W.context
      (instantiate0A (A.source arg).term s.body)
      (instantiate0A (A.source arg).term B)) ∧
    ValueEq (W.evaluate (instantiate0A (A.source arg).term s.body))
      ((D.fibre (A.evalSem arg)).erase
        ((D.fibre (A.evalSem arg)).evalSem (s.fragment (A.evalSem arg)))) :=
  ⟨⟨s.substitutionTyped arg hE hI hR hIS⟩, s.core_substitution arg harg hbody⟩

end Rcic.Declarative.Ann.LR3.RCodeSoundPi
