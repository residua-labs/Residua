import rcic.RcicAnnLR3UnitCore

/-!
# Derivation-free compositional interpretation for the scoped Eq test

`translate` never consults a source typing/conversion derivation, synthesis,
or a logical relation. Its constants 63--65 implement the admitted fixture.
The full expression map is useful for stating substitution and beta exactly;
this file does NOT claim soundness of all source typing or irrelevance rules.
The scoped proposition carrier is the singleton PER of `UnitCore`.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

/-- Only the concrete fixture's Eq, refl and recursor have special meanings. -/
def constantTerm (r : Nat) : Expr Nat :=
  if r = 63 then eqTerm else if r = 64 then reflTerm else if r = 65 then jTerm
  else .const r []

def translate (ν : Valuation) : ExprA → Expr Nat
  | .bvar i => .bvar i
  | .sort l => sortTerm (eval ν l)
  | .const r _ => constantTerm r
  | .app f a => .app (translate ν f) (translate ν a)
  | .lam A _ b => .lam (translate ν A) (translate ν b)
  | .pi A u B v => taggedTerm (eval ν (.imax u v)) (.pi (translate ν A) (translate ν B))
  | .letE A v b => .letE (translate ν A) (translate ν v) (translate ν b)
  | .lit t => .lit t

def denote (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value := denI ρ (translate ν e)
def InterpretedEq (ν : Valuation) (ρ : EnvI) (a b : ExprA) : Prop :=
  ValueEq (denote ν ρ a) (denote ν ρ b)

theorem constantTerm_lift (r c k : Nat) : lift c k (constantTerm r) = constantTerm r := by
  unfold constantTerm
  split <;> (try split) <;> (try split) <;>
    simp (disch := omega) [eqTerm, reflTerm, jTerm, unitTerm, taggedTerm, levelTerm, lift]

theorem constantTerm_instantiate (r j : Nat) (s : Expr Nat) :
    instantiate j s (constantTerm r) = constantTerm r := by
  unfold constantTerm
  split <;> (try split) <;> (try split) <;>
    simp (disch := omega) only [eqTerm, reflTerm, jTerm, unitTerm, taggedTerm, levelTerm, instantiate, if_neg]

theorem translate_lift (ν : Valuation) (e : ExprA) (c k : Nat) :
    translate ν (liftA c k e) = lift c k (translate ν e) := by
  induction e generalizing c with
  | bvar i => simp only [liftA, translate, lift]; split <;> rfl
  | sort l => rfl
  | const r ls => exact (constantTerm_lift r c k).symm
  | app f a ihf iha => simp only [liftA, translate, lift, ihf, iha]
  | lam A u b ihA ihb => simp only [liftA, translate, lift, ihA, ihb]
  | pi A u B v ihA ihB =>
      simp only [liftA, translate, taggedTerm, levelTerm, lift, ihA, ihB]
  | letE A v b ihA ihv ihb => simp only [liftA, translate, lift, ihA, ihv, ihb]
  | lit t => rfl

theorem translate_instantiate (ν : Valuation) (e : ExprA) (j : Nat) (s : ExprA) :
    translate ν (instantiateA j s e) = instantiate j (translate ν s) (translate ν e) := by
  induction e generalizing j s with
  | bvar i =>
      simp only [instantiateA, translate, instantiate]
      split <;> (try split) <;> rfl
  | sort l => rfl
  | const r ls => exact (constantTerm_instantiate r j (translate ν s)).symm
  | app f a ihf iha => simp only [instantiateA, translate, instantiate, ihf, iha]
  | lam A u b ihA ihb =>
      simp only [instantiateA, translate, instantiate, ihA, ihb, translate_lift]
  | pi A u B v ihA ihB =>
      simp only [instantiateA, translate, taggedTerm, levelTerm, instantiate, ihA, ihB, translate_lift]
  | letE A v b ihA ihv ihb =>
      simp only [instantiateA, translate, instantiate, ihA, ihv, ihb, translate_lift]
  | lit t => rfl

theorem translate_instantiate0 (ν : Valuation) (s e : ExprA) :
    translate ν (instantiate0A s e) = instantiate0 (translate ν s) (translate ν e) :=
  translate_instantiate ν e 0 s

/-- Exact substitution/environment law, supplied, not merely postulated.
It is a composition with the landed finitary substitution theorem. -/
theorem denote_substitution (ν : Valuation) (ρ : EnvI) (j : Nat) (s e : ExprA) (c : CptI) :
    denote ν ρ (instantiateA j (liftA 0 j s) e) c ↔
      denote ν (EnvI.insert ρ j (denote ν (EnvI.drop ρ j) s)) e c := by
  change ApproxI ρ (translate ν (instantiateA j (liftA 0 j s) e)) c ↔ _
  rw [translate_instantiate, translate_lift]
  exact approxI_subst_iff ρ j (translate ν s) (translate ν e) c

/-- Source beta is sound independently of any typing/row premise. -/
theorem beta_sound (ν : Valuation) (ρ : EnvI) (A body arg : ExprA) (u : Level) :
    InterpretedEq ν ρ (.app (.lam A u body) arg) (instantiate0A arg body) := by
  change SemEqI ρ (.app (.lam (translate ν A) (translate ν body)) (translate ν arg))
    (translate ν (instantiate0A arg body))
  rw [translate_instantiate0]
  exact approxI_beta ρ _ _ _

theorem zeta_sound (ν : Valuation) (ρ : EnvI) (A value body : ExprA) :
    InterpretedEq ν ρ (.letE A value body) (instantiate0A value body) := by
  change SemEqI ρ (.letE (translate ν A) (translate ν value) (translate ν body))
    (translate ν (instantiate0A value body))
  rw [translate_instantiate0]
  exact approxI_zeta ρ _ _ _

theorem app_congruence {ν : Valuation} {ρ : EnvI} {f g a b : ExprA}
    (hf : InterpretedEq ν ρ f g) (ha : InterpretedEq ν ρ a b) :
    InterpretedEq ν ρ (.app f a) (.app g b) := semEqI_app hf ha

/-- Level instantiation changes the valuation; it does not preserve a fixed
zero bit. This is uniform in every partial valuation. -/
theorem translate_levels (ν : Valuation) (ls : List Level) (e : ExprA) :
    translate ν (instantiateLevelsA ls e) = translate (instantiateValuation ν ls) e := by
  induction e with
  | bvar i => rfl
  | sort l => exact congrArg sortTerm (eval_instLevel ls ν l)
  | const r ks => rfl
  | app f a ihf iha => simp only [instantiateLevelsA, translate, ihf, iha]
  | lam A u b ihA ihb => simp only [instantiateLevelsA, translate, ihA, ihb]
  | pi A u B v ihA ihB =>
      simp only [instantiateLevelsA, translate, ihA, ihB]
      rw [← instLevel_imax, eval_instLevel]
      rfl
  | letE A v b ihA ihv ihb => simp only [instantiateLevelsA, translate, ihA, ihv, ihb]
  | lit t => rfl

end Rcic.Declarative.Ann.LR3.UnitModel
