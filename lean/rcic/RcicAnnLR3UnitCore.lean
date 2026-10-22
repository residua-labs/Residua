import rcic.RcicNativeFamModel
import rcic.RcicAnnEqLargeFixture

/-!
# A scoped nonbottom-unit model, with exact level observations

The applicative carrier is the landed finitary set interpretation `ApproxI`.
Nothing from the source conversion or the LR is used to define it. The one
proof value is a nonbottom Church unit; the proposition PER has exactly its
semantic-equivalence class as carrier. `jTerm` consumes that unit, using the
motive's result as its type argument, and returns the minor. These are model
operations, not a global soundness claim for the annotated calculus.

Universe observations retain `Option Nat`, exactly the codomain of `eval`.
This includes the unassigned case rather than conflating it with a positive
level. All later source-soundness claims state their precise scope.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

abbrev Valuation := Nat → Option Nat
abbrev Value := CptI → Prop

def ValueEq (x y : Value) : Prop := ∀ c, x c ↔ y c

theorem ValueEq.refl (x : Value) : ValueEq x x := fun _ => Iff.rfl
theorem ValueEq.symm {x y : Value} (h : ValueEq x y) : ValueEq y x := fun c => (h c).symm
theorem ValueEq.trans {x y z : Value} (h : ValueEq x y) (g : ValueEq y z) :
    ValueEq x z := fun c => (h c).trans (g c)

def bottom : Value := fun c => c = .bot

/-- Exact evaluation index, including `none`. -/
def levelRef : Option Nat → Nat
  | none => 100
  | some k => 101 + k

theorem levelRef_injective {i j : Option Nat} (h : levelRef i = levelRef j) : i = j := by
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some b => simp only [levelRef] at h; omega
  | some a =>
      cases j with
      | none => simp only [levelRef] at h; omega
      | some b =>
          have hab : a = b := by simp only [levelRef] at h; omega
          exact congrArg some hab

def levelTerm (i : Option Nat) : Expr Nat := .const (levelRef i) []
def taggedTerm (i : Option Nat) (payload : Expr Nat) : Expr Nat :=
  .app (.app (.const 10 []) (levelTerm i)) payload

/-- The source `Sort l` code is explicitly indexed by `eval nu l`.
Its own universe is the successor index. -/
def sortTerm (i : Option Nat) : Expr Nat :=
  taggedTerm (i.map Nat.succ) (.app (.const 11 []) (levelTerm i))

/-- A nonbottom unit, accepting the motive type and then its inhabitant.
Only the singleton PER below interprets this as a proof value. -/
def unitTerm : Expr Nat :=
  .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

def unitValue (ρ : EnvI) : Value := denI ρ unitTerm

def ProofMember (ρ : EnvI) (x : Value) : Prop := ValueEq x (unitValue ρ)
def ProofPER (ρ : EnvI) (x y : Value) : Prop := ProofMember ρ x ∧ ProofMember ρ y

theorem proofPER_symm {ρ : EnvI} {x y : Value} (h : ProofPER ρ x y) : ProofPER ρ y x :=
  ⟨h.2, h.1⟩
theorem proofPER_trans {ρ : EnvI} {x y z : Value}
    (h : ProofPER ρ x y) (g : ProofPER ρ y z) : ProofPER ρ x z := ⟨h.1, g.2⟩
theorem proofPER_irr {ρ : EnvI} {x y : Value} (hx : ProofMember ρ x) (hy : ProofMember ρ y) :
    ValueEq x y := hx.trans hy.symm

theorem unit_member (ρ : EnvI) : ProofMember ρ (unitValue ρ) := ValueEq.refl _

/-- A nonempty function graph that returns a nonbottom argument. The
nonbottom proof does not rely only on the vacuous empty lambda graph. -/
def unitProbe : CptI := .lam [([], .lam [([.spine 99 []], .spine 99 [])])]
theorem unit_observed (ρ : EnvI) : unitValue ρ unitProbe := by
  refine ApproxI.lam ?_
  intro s hs
  obtain rfl := List.mem_singleton.mp hs
  refine ApproxI.lam ?_
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  exact .bvar (List.mem_singleton.mpr rfl)

theorem unit_nonbottom (ρ : EnvI) : ¬ ValueEq (unitValue ρ) bottom := by
  intro h
  have he := (h unitProbe).mp (unit_observed ρ)
  cases he

/-- Primitive Eq, reflexivity, and J are interpreted as closed combinators.
All call spines are interpreted by ordinary compositional application. -/
def eqTerm : Expr Nat :=
  .lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero)
    (taggedTerm (some 0)
      (.app (.app (.app (.const 12 []) (.bvar 2)) (.bvar 1)) (.bvar 0)))))

def reflTerm : Expr Nat := .lam (.sort .zero) (.lam (.sort .zero) unitTerm)

def jTerm : Expr Nat :=
  .lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero)
    (.lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero)
      (.app (.app (.bvar 0) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))) (.bvar 2)))))))

/-- A target-only beta/zeta machine. It does not inspect source conversion,
source typing, source K guards, or any source logical relation. -/
def betaStep : Expr Nat → Option (Expr Nat)
  | .app (.lam _ b) a => some (instantiate0 a b)
  | .app f a => (betaStep f).map (fun g => .app g a)
  | .letE _ v b => some (instantiate0 v b)
  | _ => none

def betaRun : Nat → Expr Nat → Expr Nat
  | 0, e => e
  | k + 1, e => match betaStep e with
      | none => e
      | some e' => betaRun k e'

theorem betaStep_sound (ρ : EnvI) : ∀ (e e' : Expr Nat), betaStep e = some e' → SemEqI ρ e e' := by
  intro e
  induction e with
  | bvar i => intro e' h; cases h
  | sort l => intro e' h; cases h
  | const r ls => intro e' h; cases h
  | lit t => intro e' h; cases h
  | lam A b ihA ihb => intro e' h; cases h
  | pi A B ihA ihB => intro e' h; cases h
  | letE A v b ihA ihv ihb =>
      intro e' h
      have he : instantiate0 v b = e' := Option.some.inj h
      subst e'
      exact approxI_zeta ρ A v b
  | app f a ihf iha =>
      intro e' h
      cases f with
      | lam A b =>
          have he : instantiate0 a b = e' := Option.some.inj h
          subst e'
          exact approxI_beta ρ A b a
      | bvar i => cases h
      | sort l => cases h
      | const r ls => cases h
      | pi A B => cases h
      | lit t => cases h
      | letE A v b =>
          have he : Expr.app (instantiate0 v b) a = e' := Option.some.inj h
          subst e'
          exact semEqI_app (ihf _ rfl) (SemEqI.refl ρ a)
      | app f x =>
          change (betaStep (.app f x)).map (fun g => .app g a) = some e' at h
          cases hs : betaStep (.app f x) with
          | none => simp only [hs, Option.map_none] at h; cases h
          | some g =>
              rw [hs] at h
              have he : Expr.app g a = e' := Option.some.inj h
              subst e'
              exact semEqI_app (ihf _ hs) (SemEqI.refl ρ a)

theorem betaRun_sound (k : Nat) (ρ : EnvI) (e : Expr Nat) : SemEqI ρ e (betaRun k e) := by
  induction k generalizing e with
  | zero => exact SemEqI.refl ρ e
  | succ k ih =>
      cases hs : betaStep e with
      | none => simpa only [betaRun, hs] using SemEqI.refl ρ e
      | some e' =>
          simpa only [betaRun, hs] using SemEqI.trans (betaStep_sound ρ e e' hs) (ih e')

/-- Certified target computations may be used as finite model equations. -/
theorem eq_of_betaRun {k : Nat} {ρ : EnvI} {e e' : Expr Nat}
    (h : betaRun k e = e') : SemEqI ρ e e' := h ▸ betaRun_sound k ρ e

/-- Partial valuations are the literal domain of the repository's `eqN`. -/
theorem eqN_iff_evaluated_codes (u v : Level) :
    eqN u v ↔ ∀ ν : Valuation, levelRef (eval ν u) = levelRef (eval ν v) := by
  constructor
  · intro h ν; exact congrArg levelRef (h ν)
  · intro h ν; exact levelRef_injective (h ν)

def instantiateValuation (ν : Valuation) (ls : List Level) : Valuation :=
  fun i => eval ν ((ls[i]?).getD (.param i))

theorem level_code_inst (ν : Valuation) (ls : List Level) (l : Level) :
    levelTerm (eval ν (instLevel ls l)) = levelTerm (eval (instantiateValuation ν ls) l) :=
  congrArg levelTerm (eval_instLevel ls ν l)

end Rcic.Declarative.Ann.LR3.UnitModel
