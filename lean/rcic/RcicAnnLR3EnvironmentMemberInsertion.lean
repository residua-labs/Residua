import rcic.RcicAnnLR3NativeMemberValues
import rcic.RcicAnnLR3EnvironmentEvalComposition

/-!
# Compositional typed-member insertion through EnvironmentEval

The source environment remains E. A separate internal lookup view routes
eligible rigid members through the existing native hook; its transparent
bodies, stored types and level arities are preserved. The view is never
claimed admitted. The evaluator itself is the existing finite
EnvironmentEval, so the member meaning is used at every occurrence,
including inside binders and transparent bodies.

The actual producer presently recognizes axioms and opaque members whose
stored type is a sort. Their raw values have exact tags and retained
universe-code memberships. These are new native representations, not the
legacy CodeI attachment. General member telescopes remain open. No source
constructor arm or external evaluator port is supplied here.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentMemberInsertion

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

def eligibleLevel (m : CheckedMemberA) : Option Level :=
  match m.mclass, m.mtypeA with
  | .axiomM, .sort l => some l
  | .opaqueM, .sort l => some l
  | _, _ => none

/-- Only the internal dispatch class changes. All source member data
used by transparent unfolding and level instantiation are retained. -/
def route (m : CheckedMemberA) : CheckedMemberA :=
  match eligibleLevel m with
  | some _ => { m with mclass := .inductiveM }
  | none => m

def internalView (E : ResolvedEnvA) : ResolvedEnvA where
  members := fun r => (E.members r).map route

theorem route_type (m : CheckedMemberA) : (route m).mtypeA = m.mtypeA := by
  unfold route
  split <;> rfl

theorem route_body (m : CheckedMemberA) : (route m).bodyA = m.bodyA := by
  unfold route
  split <;> rfl

theorem route_arity (m : CheckedMemberA) : (route m).arity = m.arity := by
  unfold route
  split <;> rfl

theorem route_transparent (m : CheckedMemberA) :
    transparent (route m).mclass = transparent m.mclass := by
  rcases m with ⟨mc, ar, ty, body, np, norm⟩
  cases mc <;> cases ty <;> rfl

theorem eligible_rigid {m : CheckedMemberA} {l : Level}
    (h : eligibleLevel m = some l) : transparent m.mclass = false := by
  rcases m with ⟨mc, ar, ty, body, np, norm⟩
  cases mc <;> cases ty <;> simp_all [eligibleLevel, transparent]

theorem definitionBody_preserved (E : ResolvedEnvA) (r : Nat) (ls : List Level) :
    EnvironmentEval.definitionBody (internalView E) r ls =
      EnvironmentEval.definitionBody E r ls := by
  cases hm : E.members r with
  | none => simp [EnvironmentEval.definitionBody, internalView, hm]
  | some m =>
      simp [EnvironmentEval.definitionBody, internalView, hm, route_body, route_transparent]

/-- Eligible source members receive actual closed native meanings.
Original family hooks receive their original, unmodified member data. -/
def hook (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) :
    EnvironmentEval.FamilySyntax := fun ν r ls fallback =>
  match E.members r with
  | none => F ν r ls fallback
  | some m =>
      match eligibleLevel m with
      | some l => NativeMemberValues.term (eval ν (instLevel ls l)) r
      | none => F ν r ls m

/-- This is an ordinary EnvironmentEval interpretation with an internal
dispatch view, not a top-level image override. -/
def image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value :=
  EnvironmentEval.denote (internalView E) (hook E F) ν ρ e

theorem image_bot (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (e : ExprA) : image E F ν ρ e .bot :=
  EnvironmentEval.denote_bot _ _ _ _ _

theorem image_sort (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (l : Level) :
    image E F ν ρ (.sort l) = universeValue (eval ν l) :=
  (EnvironmentEval.annSemantics NeutralCodes.codeSystem (internalView E) (hook E F)).sort_image
    ν [] ρ l

theorem rigid_term {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hl : eligibleLevel m = some l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ls : List Level) :
    EnvironmentEval.rigidTerm (internalView E) (hook E F) ν r ls =
      NativeMemberValues.term (eval ν (instLevel ls l)) r := by
  simp [EnvironmentEval.rigidTerm, internalView, hm, route, hl, hook]

/-- Actual semantic insertion, uniform in source nesting environments,
level arguments and partial valuations. -/
theorem image_member {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hl : eligibleLevel m = some l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (.const r ls))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) := by
  have hd : EnvironmentEval.definitionBody (internalView E) r ls = none := by
    rw [definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, eligible_rigid hl]
  apply (EnvironmentEval.denote_rigid hd (hook E F) ν ρ).trans
  rw [rigid_term hm hl F ν ls]
  exact NativeMemberValues.environment ρ _ _

theorem image_axiom {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hc : m.mclass = .axiomM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (.const r ls))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) :=
  image_member hm (by simp [eligibleLevel, hc, ht]) F ν ρ ls

theorem image_opaque {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hc : m.mclass = .opaqueM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (.const r ls))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) :=
  image_member hm (by simp [eligibleLevel, hc, ht]) F ν ρ ls

/-- Transparent unfolding is preserved for the original source member,
and its body is evaluated with the same compositional typed insertion. -/
theorem image_delta {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (image E F ν ρ (.const r ls))
      (image E F ν ρ (instantiateLevelsA ls b)) := by
  apply EnvironmentEval.denote_delta (m := route m)
  · simp [internalView, hm]
  · rw [route_body]
    exact hb
  · rw [route_transparent]
    exact ht

/-- Actual retained universe membership and the evaluator erasure agree.
The membership is produced by nativeCode, not assumed by this theorem. -/
theorem retained_member {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {l : Level} {k : Nat} (hm : E.members r = some m)
    (hl : eligibleLevel m = some l) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (hk : eval ν (instLevel ls l) = some k) :
    (StratifiedCandidates.universeCode k).relation
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r))
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r)) ∧
    ValueEq (image E F ν ρ (.const r ls))
      (StratifiedCandidates.erase (k + 1)
        (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r))) := by
  refine ⟨NativeMemberValues.universe_member k r, ?_⟩
  rw [NativeMemberValues.universe_erasure]
  have h := image_member hm hl F ν ρ ls
  rw [hk] at h
  exact h

theorem undefined_member {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {l : Level} (hm : E.members r = some m) (hl : eligibleLevel m = some l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (hk : eval ν (instLevel ls l) = none) :
    Member (NoneUniverseBoundary.TaggedChaos none) (image E F ν ρ (.const r ls)) := by
  have h := image_member hm hl F ν ρ ls
  rw [hk] at h
  rw [NeutralCodes.valueEq_eq h]
  exact NativeMemberValues.none_member r

end Rcic.Declarative.Ann.LR3.EnvironmentMemberInsertion
