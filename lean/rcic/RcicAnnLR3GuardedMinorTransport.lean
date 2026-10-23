import rcic.RcicAnnLR3GuardedOpenEqCall

/-!
# Actual Pi-minor transport across valuations and environments

The minor is the closed source Pi P : Prop, Prop. Its action carrier and
PER are definitionally independent of the input valuation/environment.
The type image and the captured constant-lambda points require genuine
evaluation arguments; those are proved below. The resulting KernelIso
preserves the actual heterogeneous-kernel fields, including point_image.
No image law for the guarded recursor result is asserted. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedMinorTransport

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower

universe u v

private def EnvIndependent (e : Expr Nat) : Prop :=
  ∀ ρ σ : EnvI, ValueEq (denI ρ e) (denI σ e)

private theorem independent_const (r : Nat) (ls : List Level) :
    EnvIndependent (.const r ls) := by
  intro ρ σ c
  have step (τ υ : EnvI) (h : ApproxI τ (.const r ls) c) :
      ApproxI υ (.const r ls) c := by
    rcases approxI_const_inv h with h | h
    · subst c
      exact .bot _ _
    · subst c
      exact .const _ _ _
  exact ⟨step ρ σ, step σ ρ⟩

private theorem independent_app {f a : Expr Nat}
    (hf : EnvIndependent f) (ha : EnvIndependent a) :
    EnvIndependent (.app f a) := by
  intro ρ σ
  exact (NeutralPi.applyValue_denI ρ f a).symm.trans
    ((NeutralPi.applyValue_congr (hf ρ σ) (ha ρ σ)).trans
      (NeutralPi.applyValue_denI σ f a))

private theorem independent_pi {A B : Expr Nat}
    (hA : EnvIndependent A) (hB : EnvIndependent B) :
    EnvIndependent (.pi A B) := by
  intro ρ σ c
  have step (τ υ : EnvI) (h : ApproxI τ (.pi A B) c) :
      ApproxI υ (.pi A B) c := by
    rcases approxI_pi_inv h with h | ⟨a, f, h, ha, hb⟩
    · subst c
      exact .bot _ _
    · subst c
      exact .pi ((hA τ υ a).mp ha)
        (fun s hs =>
          (hB (EnvI.cons (demand s.1) τ) (EnvI.cons (demand s.1) υ) s.2).mp
            (hb s hs))
  exact ⟨step ρ σ, step σ ρ⟩

private theorem independent_level (i : Option Nat) : EnvIndependent (levelTerm i) :=
  independent_const (levelRef i) []

private theorem independent_tagged (i : Option Nat) {e : Expr Nat}
    (h : EnvIndependent e) : EnvIndependent (taggedTerm i e) :=
  independent_app (independent_app (independent_const 10 []) (independent_level i)) h

private theorem independent_sort (i : Option Nat) : EnvIndependent (sortTerm i) :=
  independent_tagged (i.map Nat.succ)
    (independent_app (independent_const 11 []) (independent_level i))

private theorem independent_result :
    EnvIndependent
      (taggedTerm (some 1) (.pi (sortTerm (some 0)) (sortTerm (some 0)))) :=
  independent_tagged (some 1)
    (independent_pi (independent_sort (some 0)) (independent_sort (some 0)))

/-- A real lambda returning its captured first environment entry is
independent of the remaining environment and of its erased annotation. -/
theorem captured_lambda_image (V : Value) (ρ σ : EnvI) (A B : Expr Nat) :
    ValueEq (denI (EnvI.cons V ρ) (.lam A (.bvar 1)))
      (denI (EnvI.cons V σ) (.lam B (.bvar 1))) := by
  intro c
  have step (τ υ : EnvI) (D E : Expr Nat)
      (h : ApproxI (EnvI.cons V τ) (.lam D (.bvar 1)) c) :
      ApproxI (EnvI.cons V υ) (.lam E (.bvar 1)) c := by
    rcases approxI_lam_inv h with h | ⟨f, h, hb⟩
    · subst c
      exact .bot _ _
    · subst c
      apply ApproxI.lam
      intro s hs
      rcases approxI_bvar_inv (hb s hs) with hbot | hv
      · rw [hbot]
        exact .bot _ _
      · exact .bvar hv
  exact ⟨step ρ σ A B, step σ ρ B A⟩

private abbrev minor (ν : Valuation) (ρ : EnvI) : Code.{0} 1 :=
  TaggedKPiFixture.code EqLargeFixture.env TaggedKEvaluation.eqSyntax ν ρ

theorem minor_type_image (ν μ : Valuation) (ρ σ : EnvI) :
    ValueEq (minor ν ρ).view.value (minor μ σ).view.value := by
  have h : ValueEq (UnitModel.denote ν ρ EqLargeFixture.result)
      (UnitModel.denote μ σ EqLargeFixture.result) := independent_result ρ σ
  exact (TaggedKEvaluation.denote_agrees ν ρ
    (e := EqLargeFixture.result) (by trivial)).trans
    (h.trans (TaggedKEvaluation.denote_agrees μ σ
      (e := EqLargeFixture.result) (by trivial)).symm)

theorem minor_point_value (ν μ : Valuation) (ρ σ : EnvI) (name : Nat) :
    ValueEq ((minor ν ρ).view.point name).value
      ((minor μ σ).view.point name).value := by
  let V := StratifiedCandidates.erase 1 (SaturatedTower.reflect 1 name)
  change ValueEq
    (TaggedKEvaluation.image ν (EnvI.cons V ρ)
      (.lam (.sort .zero) TaggedKPiFixture.one (.bvar 1)))
    (TaggedKEvaluation.image μ (EnvI.cons V σ)
      (.lam (.sort .zero) TaggedKPiFixture.one (.bvar 1)))
  have h : ValueEq
      (UnitModel.denote ν (EnvI.cons V ρ)
        (.lam (.sort .zero) TaggedKPiFixture.one (.bvar 1)))
      (UnitModel.denote μ (EnvI.cons V σ)
        (.lam (.sort .zero) TaggedKPiFixture.one (.bvar 1))) :=
    captured_lambda_image V ρ σ (sortTerm (some 0)) (sortTerm (some 0))
  exact (TaggedKEvaluation.denote_agrees ν (EnvI.cons V ρ)
    (e := .lam (.sort .zero) TaggedKPiFixture.one (.bvar 1)) (by trivial)).trans
    (h.trans (TaggedKEvaluation.denote_agrees μ (EnvI.cons V σ)
      (e := .lam (.sort .zero) TaggedKPiFixture.one (.bvar 1)) (by trivial)).symm)

private theorem action_ext {α : Type u} {β : Type v}
    {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {R : α → β → β → Prop}
    {f g : SaturatedPiElements.ElementAction eraseA eraseB D R}
    (hv : f.value = g.value) (hr : f.run = g.run) : f = g := by
  cases f
  cases g
  cases hv
  cases hr
  rfl

theorem minor_point_eq (ν μ : Valuation) (ρ σ : EnvI) (name : Nat) :
    (minor ν ρ).view.point name = (minor μ σ).view.point name := by
  apply action_ext
  · exact NeutralCodes.valueEq_eq (minor_point_value ν μ ρ σ name)
  · rfl

/-- The same retained actions work at every input valuation/environment;
the actual type and point image laws are proved above. -/
def minorIso (ν μ : Valuation) (ρ σ : EnvI) :
    KernelIso (minor ν ρ).kernel (minor μ σ).kernel where
  forward := fun f => f
  backward := fun f => f
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  type_image := minor_type_image ν μ ρ σ
  element_image := fun _ => ValueEq.refl _
  point_image := minor_point_eq ν μ ρ σ
  relation := fun _ _ => Iff.rfl

theorem minor_related (ν μ : Valuation) (ρ σ : EnvI) :
    CodeRelated (minor ν ρ) (minor μ σ) :=
  ⟨rfl, ⟨minorIso ν μ ρ σ⟩⟩

def openMinorIso (ν μ : Valuation) (a b : GuardedReaderSource.IndexAssignment) :
    KernelIso (GuardedOpenEqCall.minorCode ν a).kernel
      (GuardedOpenEqCall.minorCode μ b).kernel :=
  minorIso ν μ (GuardedReaderSource.rawEnvironment a) (GuardedReaderSource.rawEnvironment b)

end Rcic.Declarative.Ann.LR3.GuardedMinorTransport
