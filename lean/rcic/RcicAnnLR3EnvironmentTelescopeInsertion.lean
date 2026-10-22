import rcic.RcicAnnLR3NativeTelescopeValues
import rcic.RcicAnnLR3EnvironmentMemberInsertion

/-!
# Compositional insertion for rigid sort-ending telescopes

The source environment is retained. A preliminary internal dispatch
view routes axioms and opaque members with a syntactic Pi telescope
ending in Sort to a closed native lambda tower. The compiled sort-member
insertion then handles its original fragment. Transparent bodies keep
their original source syntax and are interpreted by the same configured
EnvironmentEval at every nesting depth.

After all telescope arguments the actual retained result code is
supplied. This constructs, in particular, the type-valued binary axiom
needed by the Acc guard. Arbitrary dependent member result types, a
uniform source Ty_const arm and a complete enriched CodeSystem remain
open. Neither internal lookup view is claimed admitted.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentTelescopeInsertion

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

def sortTail : ExprA → Option (Nat × Level)
  | .sort l => some (0, l)
  | .pi _ _ B _ => (sortTail B).map (fun p => (p.1 + 1, p.2))
  | _ => none

/-- Depth zero is left to the already compiled sort-member producer. -/
def eligible (m : CheckedMemberA) : Option (Nat × Level) :=
  match m.mclass, sortTail m.mtypeA with
  | .axiomM, some (n + 1, l) => some (n + 1, l)
  | .opaqueM, some (n + 1, l) => some (n + 1, l)
  | _, _ => none

def route (m : CheckedMemberA) : CheckedMemberA :=
  match eligible m with
  | some _ => { m with mclass := .inductiveM }
  | none => m

def telescopeView (E : ResolvedEnvA) : ResolvedEnvA where
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

theorem eligible_rigid {m : CheckedMemberA} {p : Nat × Level}
    (h : eligible m = some p) : transparent m.mclass = false := by
  rcases m with ⟨mc, ar, ty, body, np, norm⟩
  cases mc <;> simp_all [eligible, transparent]

theorem route_transparent (m : CheckedMemberA) :
    transparent (route m).mclass = transparent m.mclass := by
  cases h : eligible m with
  | none => simp [route, h]
  | some p =>
      simp only [route, h]
      exact (eligible_rigid h).symm

theorem telescopeView_definitionBody (E : ResolvedEnvA) (r : Nat) (ls : List Level) :
    EnvironmentEval.definitionBody (telescopeView E) r ls =
      EnvironmentEval.definitionBody E r ls := by
  cases hm : E.members r with
  | none => simp [EnvironmentEval.definitionBody, telescopeView, hm]
  | some m =>
      simp [EnvironmentEval.definitionBody, telescopeView, hm, route_body, route_transparent]

def telescopeHook (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) :
    EnvironmentEval.FamilySyntax := fun ν r ls fallback =>
  match E.members r with
  | none => F ν r ls fallback
  | some m =>
      match eligible m with
      | some (depth, l) =>
          NativeTelescopeValues.term depth (eval ν (instLevel ls l)) r
      | none => F ν r ls m

/-- The final view and hook are compositions of the existing dispatch
configuration. There is still one EnvironmentEval interpretation. -/
def internalView (E : ResolvedEnvA) : ResolvedEnvA :=
  EnvironmentMemberInsertion.internalView (telescopeView E)

def hook (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) :
    EnvironmentEval.FamilySyntax :=
  EnvironmentMemberInsertion.hook (telescopeView E) (telescopeHook E F)

def image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value :=
  EnvironmentEval.denote (internalView E) (hook E F) ν ρ e

theorem definitionBody_preserved (E : ResolvedEnvA) (r : Nat) (ls : List Level) :
    EnvironmentEval.definitionBody (internalView E) r ls =
      EnvironmentEval.definitionBody E r ls := by
  rw [internalView, EnvironmentMemberInsertion.definitionBody_preserved,
    telescopeView_definitionBody]

theorem image_bot (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (e : ExprA) : image E F ν ρ e .bot :=
  EnvironmentEval.denote_bot _ _ _ _ _

theorem image_sort (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (l : Level) :
    image E F ν ρ (.sort l) = universeValue (eval ν l) :=
  (EnvironmentEval.annSemantics NeutralCodes.codeSystem (internalView E) (hook E F)).sort_image
    ν [] ρ l

theorem rigid_term {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {depth : Nat} {l : Level} (hm : E.members r = some m)
    (he : eligible m = some (depth, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ls : List Level) :
    EnvironmentEval.rigidTerm (internalView E) (hook E F) ν r ls =
      NativeTelescopeValues.term depth (eval ν (instLevel ls l)) r := by
  simp [EnvironmentEval.rigidTerm, internalView, hook,
    EnvironmentMemberInsertion.internalView, EnvironmentMemberInsertion.route,
    EnvironmentMemberInsertion.eligibleLevel, EnvironmentMemberInsertion.hook,
    telescopeView, route, hm, he, telescopeHook]

/-- The native telescope is installed at every occurrence, including
under binders and inside transparent source definitions. -/
theorem image_telescope {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {depth : Nat} {l : Level} (hm : E.members r = some m)
    (he : eligible m = some (depth, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (.const r ls))
      (NativeTelescopeValues.value depth (eval ν (instLevel ls l)) r) := by
  have hd : EnvironmentEval.definitionBody (internalView E) r ls = none := by
    rw [definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, eligible_rigid he]
  apply (EnvironmentEval.denote_rigid hd (hook E F) ν ρ).trans
  rw [rigid_term hm he F ν ls]
  exact NativeTelescopeValues.environment depth ρ _ _

/-- Existing sort-typed axioms keep the compiled typed insertion. -/
theorem image_axiom {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hc : m.mclass = .axiomM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (.const r ls))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) := by
  apply EnvironmentMemberInsertion.image_axiom (m := m) ?_ hc ht
  simp [telescopeView, hm, route, eligible, hc, ht, sortTail]

theorem image_opaque {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hc : m.mclass = .opaqueM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (.const r ls))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) := by
  apply EnvironmentMemberInsertion.image_opaque (m := m) ?_ hc ht
  simp [telescopeView, hm, route, eligible, hc, ht, sortTail]

theorem image_delta {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (image E F ν ρ (.const r ls))
      (image E F ν ρ (instantiateLevelsA ls b)) := by
  apply EnvironmentMemberInsertion.image_delta (m := route m)
  · simp [telescopeView, hm]
  · rw [route_body]
    exact hb
  · rw [route_transparent]
    exact ht

def applySource : ExprA → List ExprA → ExprA
  | f, [] => f
  | f, a :: args => applySource (.app f a) args

theorem image_applications (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : ExprA) (args : List ExprA) :
    ValueEq (image E F ν ρ (applySource f args))
      (NativeTelescopeValues.applyArgs (image E F ν ρ f) (args.map (image E F ν ρ))) := by
  induction args generalizing f with
  | nil => exact ValueEq.refl _
  | cons a args ih =>
      exact (ih (.app f a)).trans
        (NativeTelescopeValues.applyArgs_congr
          (EnvironmentEval.denote_application (internalView E) (hook E F) ν ρ f a)
          (args.map (image E F ν ρ)))

/-- The result type image after a full syntactic telescope is supplied
by exact EnvironmentEval composition, not by a source application IH. -/
theorem image_telescope_applied {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {l : Level} (args : List ExprA) (hm : E.members r = some m)
    (he : eligible m = some (args.length, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (image E F ν ρ (applySource (.const r ls) args))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) := by
  apply (image_applications E F ν ρ (.const r ls) args).trans
  apply (NativeTelescopeValues.applyArgs_congr (image_telescope hm he F ν ρ ls)
    (args.map (image E F ν ρ))).trans
  simpa only [List.length_map] using
    NativeTelescopeValues.applications (args.map (image E F ν ρ))
      (eval ν (instLevel ls l)) r

theorem image_telescope_two {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {l : Level} (hm : E.members r = some m) (he : eligible m = some (2, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (a b : ExprA) :
    ValueEq (image E F ν ρ (.app (.app (.const r ls) a) b))
      (NativeMemberValues.value (eval ν (instLevel ls l)) r) :=
  image_telescope_applied [a, b] hm he F ν ρ ls

theorem retained_telescope {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {l : Level} {k : Nat} (args : List ExprA) (hm : E.members r = some m)
    (he : eligible m = some (args.length, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (hk : eval ν (instLevel ls l) = some k) :
    (StratifiedCandidates.universeCode k).relation
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r))
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r)) ∧
    ValueEq (image E F ν ρ (applySource (.const r ls) args))
      (StratifiedCandidates.erase (k + 1)
        (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r))) := by
  refine ⟨NativeMemberValues.universe_member k r, ?_⟩
  rw [NativeMemberValues.universe_erasure]
  have h := image_telescope_applied args hm he F ν ρ ls
  rw [hk] at h
  exact h

theorem retained_telescope_two {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    {l : Level} {k : Nat} (hm : E.members r = some m) (he : eligible m = some (2, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (a b : ExprA) (hk : eval ν (instLevel ls l) = some k) :
    (StratifiedCandidates.universeCode k).relation
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r))
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r)) ∧
    ValueEq (image E F ν ρ (.app (.app (.const r ls) a) b))
      (StratifiedCandidates.erase (k + 1)
        (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k r))) :=
  retained_telescope [a, b] hm he F ν ρ ls hk

/-- Explicit proof neutrals inhabit the retained proposition result. -/
theorem proposition_result_neutral (r name : Nat) :
    (StratifiedCandidates.view 0 (NativeMemberValues.neutralCode 0 r)).relation
      (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) :=
  CandidatePi.decode_reflection _ (.atom name)

end Rcic.Declarative.Ann.LR3.EnvironmentTelescopeInsertion
