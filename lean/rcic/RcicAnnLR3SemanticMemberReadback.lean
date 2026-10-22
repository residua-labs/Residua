import rcic.RcicAnnLR3SemanticMemberEval

/-!
# Finite semantic interpretation of stored universe types

This producer covers the sort/delta fragment, with arbitrary references,
level instantiation and finite transparent chains. Its result is justified
against the same EnvironmentEval for every final hook. The member hook
first interprets the actual stored type, then dispatches on that result.
No general Pi/element stored-type interpreter is claimed. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SemanticMemberReadback
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements SemanticMemberEval

/-- A finite interpretation result, not a normalized source expression. -/
def readUniverse : Nat → ResolvedEnvA → Valuation → ExprA → Option (Option Nat)
  | 0, _, _, _ => none
  | _ + 1, _, ν, .sort l => some (eval ν l)
  | fuel + 1, E, ν, .const r ls =>
      (EnvironmentEval.definitionBody E r ls).bind (readUniverse fuel E ν)
  | _ + 1, _, _, _ => none

/-- Expose the existing delta producer from its actual lookup result. -/
theorem denote_of_body {E : ResolvedEnvA} {r : Nat} {ls : List Level} {b : ExprA}
    (h : EnvironmentEval.definitionBody E r ls = some b)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.const r ls))
      (EnvironmentEval.denote E F ν ρ b) := by
  cases hm : E.members r with
  | none => simp [EnvironmentEval.definitionBody, hm] at h
  | some m =>
      cases ht : transparent m.mclass with
      | false => simp [EnvironmentEval.definitionBody, hm, ht] at h
      | true =>
          cases hb : m.bodyA with
          | none => simp [EnvironmentEval.definitionBody, hm, ht, hb] at h
          | some raw =>
              have he : instantiateLevelsA ls raw = b := by
                simpa [EnvironmentEval.definitionBody, hm, ht, hb] using h
              cases he
              exact EnvironmentEval.denote_delta hm hb ht F ν ρ

theorem readUniverse_sound (fuel : Nat) (E : ResolvedEnvA) (ν : Valuation)
    (A : ExprA) (k : Option Nat) (h : readUniverse fuel E ν A = some k)
    (F : EnvironmentEval.FamilySyntax) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote E F ν ρ A) (universeValue k) := by
  induction fuel generalizing A with
  | zero => simp [readUniverse] at h
  | succ fuel ih =>
      cases A with
      | sort l =>
          have he : eval ν l = k := by simpa [readUniverse] using h
          cases he
          exact (sortMeaning E ν l).image F ρ
      | const r ls =>
          cases hb : EnvironmentEval.definitionBody E r ls with
          | none => simp [readUniverse, hb] at h
          | some b =>
              have hr : readUniverse fuel E ν b = some k := by
                simpa [readUniverse, hb] using h
              exact (denote_of_body hb F ν ρ).trans (ih b hr)
      | bvar i => simp [readUniverse] at h
      | app f a => simp [readUniverse] at h
      | lam A u b => simp [readUniverse] at h
      | pi A u B v => simp [readUniverse] at h
      | letE A v b => simp [readUniverse] at h
      | lit n => simp [readUniverse] at h

/-- Turn the computed semantic result into retained evidence. -/
def meaning (fuel : Nat) (E : ResolvedEnvA) (ν : Valuation) (A : ExprA)
    (k : Option Nat) (h : readUniverse fuel E ν A = some k) :
    UniverseMeaning E ν A :=
  ⟨k, fun F ρ => readUniverse_sound fuel E ν A k h F ρ⟩

/-- Read the member's instantiated stored type in the final evaluator view.
The fallback is explicit for types outside this finite interpreted fragment. -/
def hook (fuel : Nat) (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) :
    EnvironmentEval.FamilySyntax := fun ν r ls fallback =>
  match E.members r with
  | none => F ν r ls fallback
  | some m =>
      match readUniverse fuel (view E) ν (instantiateLevelsA ls m.mtypeA) with
      | some k => NativeMemberValues.term k r
      | none => F ν r ls m

def image (fuel : Nat) (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value :=
  EnvironmentEval.denote (view E) (hook fuel E F) ν ρ e

theorem rigid_member_image {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hm : E.members r = some m)
    (hc : m.mclass = .axiomM ∨ m.mclass = .opaqueM)
    (fuel : Nat) (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (k : Option Nat)
    (hr : readUniverse fuel (view E) ν (instantiateLevelsA ls m.mtypeA) = some k) :
    ValueEq (image fuel E F ν ρ (.const r ls)) (NativeMemberValues.value k r) := by
  have hd : EnvironmentEval.definitionBody (view E) r ls = none := by
    rw [definitionBody_preserved]
    rcases hc with hc | hc <;> simp [EnvironmentEval.definitionBody, hm, hc, transparent]
  have ht : EnvironmentEval.rigidTerm (view E) (hook fuel E F) ν r ls =
      NativeMemberValues.term k r := by
    rcases hc with hc | hc <;>
      simp [EnvironmentEval.rigidTerm, view, hm, route, hc, hook, hr]
    all_goals
      change (match readUniverse fuel (view E) ν (instantiateLevelsA ls m.mtypeA) with
        | some j => NativeMemberValues.term j r
        | none => F ν r ls m) = NativeMemberValues.term k r
      rw [hr]
  exact (EnvironmentEval.denote_rigid hd (hook fuel E F) ν ρ).trans
    (by rw [ht]; exact NativeMemberValues.environment ρ k r)

theorem axiom_image {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hm : E.members r = some m) (hc : m.mclass = .axiomM)
    (fuel : Nat) (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (k : Option Nat)
    (hr : readUniverse fuel (view E) ν (instantiateLevelsA ls m.mtypeA) = some k) :
    ValueEq (image fuel E F ν ρ (.const r ls)) (NativeMemberValues.value k r) :=
  rigid_member_image hm (Or.inl hc) fuel F ν ρ k hr

theorem opaque_image {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hm : E.members r = some m) (hc : m.mclass = .opaqueM)
    (fuel : Nat) (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (k : Option Nat)
    (hr : readUniverse fuel (view E) ν (instantiateLevelsA ls m.mtypeA) = some k) :
    ValueEq (image fuel E F ν ρ (.const r ls)) (NativeMemberValues.value k r) :=
  rigid_member_image hm (Or.inr hc) fuel F ν ρ k hr

theorem axiom_type_image {E : ResolvedEnvA} {ls : List Level} {m : CheckedMemberA}
    (fuel : Nat) (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (k : Option Nat)
    (hr : readUniverse fuel (view E) ν (instantiateLevelsA ls m.mtypeA) = some k) :
    ValueEq (image fuel E F ν ρ (instantiateLevelsA ls m.mtypeA)) (universeValue k) :=
  readUniverse_sound fuel (view E) ν _ k hr (hook fuel E F) ρ

namespace Alias
open ConfiguredAliasBoundary

def configuredView : ResolvedEnvA := view env

def configuredHook : EnvironmentEval.FamilySyntax :=
  hook 2 env EnvironmentEval.neutralFamilySyntax

def image (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value :=
  EnvironmentEval.denote configuredView configuredHook ν ρ e

theorem stored_type_computed (ν : Valuation) :
    readUniverse 2 configuredView ν (instantiateLevelsA [] member.mtypeA) =
      some (some 0) := rfl

theorem alias_image (ν : Valuation) (ρ : EnvI) :
    ValueEq (image ν ρ (.const 94 [])) (universeValue (some 0)) :=
  readUniverse_sound 2 configuredView ν (.const 94 []) (some 0) rfl configuredHook ρ

theorem member_image (ν : Valuation) (ρ : EnvI) :
    ValueEq (image ν ρ (.const 95 [])) (NativeMemberValues.value (some 0) 95) :=
  axiom_image (m := member) rfl rfl 2 EnvironmentEval.neutralFamilySyntax ν ρ
    (some 0) (stored_type_computed ν)

end Alias
end Rcic.Declarative.Ann.LR3.SemanticMemberReadback


namespace Rcic.Declarative.Ann.LR3.SemanticMemberReadback
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements SemanticMemberEval

/-- Successful interpretations agree whenever the same evaluator
identifies the stored types. The finite budgets may differ. -/
theorem readUniverse_congr {E : ResolvedEnvA} {ν : Valuation}
    {A B : ExprA} {i j : Option Nat} {fuel fuel' : Nat}
    (hA : readUniverse fuel E ν A = some i)
    (hB : readUniverse fuel' E ν B = some j)
    (F : EnvironmentEval.FamilySyntax) (ρ : EnvI)
    (h : ValueEq (EnvironmentEval.denote E F ν ρ A)
      (EnvironmentEval.denote E F ν ρ B)) : i = j := by
  apply UnitModel.sort_code_injective (ρ := EnvI.bot)
  exact (readUniverse_sound fuel E ν A i hA F ρ).symm.trans
    (h.trans (readUniverse_sound fuel' E ν B j hB F ρ))

theorem readUniverse_delta_code {E : ResolvedEnvA} {ν : Valuation}
    {r : Nat} {ls : List Level} {b : ExprA}
    {i j : Option Nat} {fuel fuel' : Nat}
    (hb : EnvironmentEval.definitionBody E r ls = some b)
    (hA : readUniverse fuel E ν (.const r ls) = some i)
    (hB : readUniverse fuel' E ν b = some j) : i = j :=
  readUniverse_congr hA hB EnvironmentEval.neutralFamilySyntax EnvI.bot
    (denote_of_body hb EnvironmentEval.neutralFamilySyntax ν EnvI.bot)

theorem dispatch_read_congr {E : ResolvedEnvA} {ν : Valuation}
    {A B : ExprA} {i j : Option Nat} {fuel fuel' : Nat}
    (hA : readUniverse fuel E ν A = some i)
    (hB : readUniverse fuel' E ν B = some j)
    (F : EnvironmentEval.FamilySyntax) (ρ : EnvI)
    (h : ValueEq (EnvironmentEval.denote E F ν ρ A)
      (EnvironmentEval.denote E F ν ρ B)) (name : Nat) :
    dispatch (meaning fuel E ν A i hA) name =
      dispatch (meaning fuel' E ν B j hB) name := by
  change NativeMemberValues.term i name = NativeMemberValues.term j name
  rw [readUniverse_congr hA hB F ρ h]

end Rcic.Declarative.Ann.LR3.SemanticMemberReadback
