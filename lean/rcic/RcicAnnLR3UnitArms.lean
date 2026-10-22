import rcic.RcicAnnLR3UnitLevels
import rcic.RcicAnnKEqPositive

/-!
# Initial constructor equations for the nonbottom-unit Eq probe

The primitive operations are interpreted compositionally. The six-argument
J equation is proved for arbitrary target expressions, not by recognizing
the fixture's endpoints. Eq iota and K's unit equation follow from it.
The source beta/substitution equations are already supplied by UnitTranslate.

Irrelevance here consumes semantic proof membership. The actual fixture
supplies that premise; no theorem turning arbitrary source proof typing
into such membership is assumed or claimed. Likewise the Pi/lambda
congruences below quantify over every target environment extension, not
merely the as-yet-unsupplied class of source-typed extensions.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

/-- The target recursor is an ordinary curried combinator. -/
theorem j_six_beta (A a C c b p : Expr Nat) :
    betaRun 6 (foldApps jTerm [A,a,C,c,b,p]) = jOperation C c b p := by
  simp (disch := omega) [betaRun, betaStep, foldApps, jTerm, jOperation,
    instantiate0, instantiate, lift, lift_shift_comp_idx,
    instantiate_lift_cancel, lift_zero]

theorem refl_two_beta (A a : Expr Nat) :
    betaRun 2 (foldApps reflTerm [A,a]) = unitTerm := by
  simp [betaRun, betaStep, foldApps, reflTerm, unitTerm, instantiate0, instantiate, lift]

theorem eq_three_beta (A a b : Expr Nat) :
    betaRun 3 (foldApps eqTerm [A,a,b]) =
      taggedTerm (some 0) (.app (.app (.app (.const 12 []) A) a) b) := by
  simp (disch := omega) [betaRun, betaStep, foldApps, eqTerm, taggedTerm,
    levelTerm, instantiate0, instantiate, lift, lift_shift_comp_idx,
    instantiate_lift_cancel, lift_zero]

theorem translate_foldApps (ν : Valuation) (f : ExprA) (xs : List ExprA) :
    translate ν (foldAppsA f xs) = foldApps (translate ν f) (xs.map (translate ν)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

/-- General reflexivity operation, not just the fixture's parameter. -/
theorem refl_value (ν : Valuation) (ρ : EnvI) (ls : List Level) (A a : ExprA) :
    ProofMember ρ (denote ν ρ (foldAppsA (.const 64 ls) [A,a])) := by
  change SemEqI ρ (translate ν (foldAppsA (.const 64 ls) [A,a])) unitTerm
  rw [translate_foldApps]
  exact eq_of_betaRun (ρ := ρ) (refl_two_beta (translate ν A) (translate ν a))

/-- The concrete Eq family has its actual tagged proposition image. -/
theorem eq_family_value (ν : Valuation) (ρ : EnvI) (ls : List Level) (A a b : ExprA) :
    SemEqI ρ (translate ν (foldAppsA (.const 63 ls) [A,a,b]))
      (taggedTerm (some 0)
        (.app (.app (.app (.const 12 []) (translate ν A)) (translate ν a)) (translate ν b))) := by
  rw [translate_foldApps]
  exact eq_of_betaRun (ρ := ρ) (eq_three_beta (translate ν A) (translate ν a) (translate ν b))

theorem eq_family_member (ν : Valuation) (ρ : EnvI) (ls : List Level) (A a b : ExprA) :
    SortMember (some 0) (denote ν ρ (foldAppsA (.const 63 ls) [A,a,b])) ∧
    TypeDefined (denote ν ρ (foldAppsA (.const 63 ls) [A,a,b])) := by
  have he := eq_family_value ν ρ ls A a b
  exact ⟨sortMember_congr (ValueEq.symm he) (tagged_member ρ _ _),
    typeDefined_congr (ValueEq.symm he) (tagged_defined ρ _ _)⟩

/-- Generic source Eq-recursion equation for a semantic proof unit. It
contains no source conversion, K guard, LR, synthesis, or normality premise. -/
theorem eq_rec_unit (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (A a C c b p : ExprA) (hp : ProofMember ρ (denote ν ρ p)) :
    InterpretedEq ν ρ (foldAppsA (.const 65 ls) [A,a,C,c,b,p]) c := by
  change SemEqI ρ (translate ν (foldAppsA (.const 65 ls) [A,a,C,c,b,p])) (translate ν c)
  rw [translate_foldApps]
  exact SemEqI.trans
    (eq_of_betaRun (ρ := ρ)
      (j_six_beta (translate ν A) (translate ν a) (translate ν C)
        (translate ν c) (translate ν b) (translate ν p)))
    (jOperation_unit (translate ν C) (translate ν c) (translate ν b) (translate ν p) hp)

/-- General canonical Eq iota equation in the chosen interpretation. -/
theorem eq_iota_value (ν : Valuation) (ρ : EnvI) (ls ks : List Level)
    (A a C c : ExprA) :
    InterpretedEq ν ρ
      (foldAppsA (.const 65 ls) [A,a,C,c,a,foldAppsA (.const 64 ks) [A,a]]) c :=
  eq_rec_unit ν ρ ls A a C c a _ (refl_value ν ρ ks A a)

/-- The irrelevance value equation from actual semantic membership. The
missing global source-typing-to-membership theorem is NOT hidden here. -/
theorem irr_value {ν : Valuation} {ρ : EnvI} {p q : ExprA}
    (hp : ProofMember ρ (denote ν ρ p)) (hq : ProofMember ρ (denote ν ρ q)) :
    InterpretedEq ν ρ p q := proofPER_irr hp hq

/-- K's unit equation is valid on the actual Eq proof carrier, whose
membership includes endpoint agreement. This is a semantic equation, not a
global supplier of source guard or proof-membership soundness. -/
theorem eq_K_value (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (A a C c b p : ExprA)
    (hp : EqProofMember ρ (translate ν a) (translate ν b) (denote ν ρ p)) :
    InterpretedEq ν ρ (foldAppsA (.const 65 ls) [A,a,C,c,b,p]) c :=
  eq_rec_unit ν ρ ls A a C c b p hp.2

/-- The exact landed stage-one Eq K frame and its semantic equation are
supplied together, so the concrete K test is not merely a conditional arm. -/
theorem inhabited_K_arm :
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 EqLargeFixture.context) ∧
    Nonempty (KStage.Frame EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context KEqPositive.eqShape) ∧
    KStage.Head EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 EqLargeFixture.context
      (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result KEqPositive.eqShape.resultType ∧
    ∀ ν : Valuation, FitsFixture ν fixtureEnv ∧
      InterpretedEq ν fixtureEnv KEqPositive.eqShape.source KEqPositive.eqShape.minor :=
  ⟨EqLargeFixture.wf, ⟨EqLargeFixture.contextWf⟩, KEqPositive.eqFrame, KEqPositive.eqHead,
    fun ν => ⟨fixtureEnv_fits ν, open_conversion_sound (fixtureEnv_fits ν)⟩⟩

/-- An actual source beta derivation, in addition to the general supplied
value equation, with all its typing leaves already supplied on main. -/
theorem inhabited_beta_arm :
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
      (.app (.lam (.sort EqLargeFixture.one) EqLargeFixture.two (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort EqLargeFixture.one)) ∧
    ∀ (ν : Valuation) (ρ : EnvI), InterpretedEq ν ρ
      (.app (.lam (.sort EqLargeFixture.one) EqLargeFixture.two (.bvar 0)) (.sort .zero))
      (.sort .zero) :=
  ⟨EqLargeFixture.wf, ⟨idSort1_beta _ _ _⟩,
    fun ν ρ => beta_sound ν ρ (.sort EqLargeFixture.one) (.bvar 0) (.sort .zero) EqLargeFixture.two⟩

theorem sorts_value (ν : Valuation) (ρ : EnvI) {u v : Level} (h : eqN u v) :
    InterpretedEq ν ρ (.sort u) (.sort v) := by
  change ValueEq (denI ρ (sortTerm (eval ν u))) (denI ρ (sortTerm (eval ν v)))
  rw [h ν]
  exact ValueEq.refl _

/-- Constants' level arguments do not change their operations in this
fixed Eq environment. Universe instantiation still acts on every sort
and Pi annotation through the independently proved valuation law. -/
theorem consts_value (ν : Valuation) (ρ : EnvI) (r : Nat) (ls ks : List Level) :
    InterpretedEq ν ρ (.const r ls) (.const r ks) := ValueEq.refl _

theorem lam_value_congruence {ν : Valuation} {ρ : EnvI} {A A' b b' : ExprA} {u u' : Level}
    (hb : ∀ S : Value, InterpretedEq ν (EnvI.cons S ρ) b b') :
    InterpretedEq ν ρ (.lam A u b) (.lam A' u' b') := semEqI_lam hb

theorem pi_value_congruence {ν : Valuation} {ρ : EnvI} {A A' B B' : ExprA}
    {u u' v v' : Level} (hu : eqN u u') (hv : eqN v v')
    (hA : InterpretedEq ν ρ A A')
    (hB : ∀ S : Value, InterpretedEq ν (EnvI.cons S ρ) B B') :
    InterpretedEq ν ρ (.pi A u B v) (.pi A' u' B' v') := by
  have hlevel : eval ν (.imax u v) = eval ν (.imax u' v') := by
    simp only [eval, hu ν, hv ν]
  change SemEqI ρ (taggedTerm (eval ν (.imax u v)) (.pi (translate ν A) (translate ν B)))
    (taggedTerm (eval ν (.imax u' v')) (.pi (translate ν A') (translate ν B')))
  rw [hlevel]
  exact semEqI_app (SemEqI.refl ρ _) (semEqI_pi hA hB)

end Rcic.Declarative.Ann.LR3.UnitModel
