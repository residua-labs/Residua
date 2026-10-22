import rcic.RcicAnnLR3TypedPER
import rcic.RcicAnnRecPins

/-!
# Constructive least constructor closure and the admitted Loop control

This is a positive inductive relation, with arbitrary indexed branching.
It supplies the least-fixed-point predicate, not a source recursor
interpreter. In particular a fold to Prop does not supply a choice-free
value-valued eliminator which factors through a proof-irrelevant carrier.
Empty and one-recursive-field Loop signatures have empty least closures.
The latter is attached to the existing admitted Loop source environment.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedInductive
open Rcic.Declarative
open UnitModel TypedPER
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
universe u v w z

structure Signature (Index : Type u) where
  Rule : Index → Type v
  Premise : (i : Index) → Rule i → Type w
  child : (i : Index) → (r : Rule i) → Premise i r → Index

/-- No recursive El, no negative occurrence, and no induction-recursion. -/
inductive Closure {Index : Type u} (S : Signature.{u,v,w} Index) : Index → Prop
  | node (i : Index) (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Closure S (S.child i r p)) : Closure S i

/-- Data-valued constructor evidence supports ordinary well-founded folds.
This is not obtained by choosing evidence from Closure in Prop. -/
inductive Evidence {Index : Type u} (S : Signature.{u,v,w} Index) : Index → Type (max u v w)
  | node (i : Index) (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Evidence S (S.child i r p)) : Evidence S i

/-- Primitive evidence recursor into any Sort. `noncomputable` only avoids
Lean 4.14 code generation for a Sort-polymorphic recursor; the term uses
no classical choice and its equation is kernel-definitional. -/
noncomputable def fold {Index : Type u} {S : Signature.{u,v,w} Index} {Result : Index → Sort z}
    (algebra : ∀ i (r : S.Rule i), (∀ p : S.Premise i r, Result (S.child i r p)) → Result i) :
    ∀ {i}, Evidence S i → Result i :=
  fun {i} h => Evidence.rec (motive := fun i _ => Result i)
    (fun i r _children ih => algebra i r ih) h

theorem fold_iota {Index : Type u} {S : Signature.{u,v,w} Index} {Result : Index → Sort z}
    (algebra : ∀ i (r : S.Rule i), (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (i : Index) (r : S.Rule i) (children : ∀ p : S.Premise i r, Evidence S (S.child i r p)) :
    fold algebra (Evidence.node i r children) = algebra i r (fun p => fold algebra (children p)) := rfl

theorem evidence_to_closure {Index : Type u} {S : Signature.{u,v,w} Index} {i : Index}
    (h : Evidence S i) : Closure S i := by
  induction h with
  | node i r children ih => exact .node i r ih

def Step {Index : Type u} (S : Signature.{u,v,w} Index)
    (P : Index → Prop) (i : Index) : Prop :=
  ∃ r : S.Rule i, ∀ p : S.Premise i r, P (S.child i r p)

theorem step_monotone {Index : Type u} (S : Signature.{u,v,w} Index)
    {P Q : Index → Prop} (h : ∀ i, P i → Q i) {i : Index} :
    Step S P i → Step S Q i :=
  fun ⟨r, hr⟩ => ⟨r, fun p => h _ (hr p)⟩

theorem closure_unfold {Index : Type u} (S : Signature.{u,v,w} Index) (i : Index) :
    Closure S i ↔ Step S (Closure S) i := by
  constructor
  · intro h; cases h with | node i r hs => exact ⟨r, hs⟩
  · rintro ⟨r, hs⟩; exact .node i r hs

/-- The leastness/fold theorem eliminates into Prop; it does not select a
value or recursive evidence from a mere existence proof. -/
theorem closure_least {Index : Type u} (S : Signature.{u,v,w} Index)
    {P : Index → Prop} (closed : ∀ i, Step S P i → P i) :
    ∀ i, Closure S i → P i := by
  intro i h
  induction h with
  | node i r hs ih => exact closed i ⟨r, ih⟩

def TruthFamilyPER {Index : Type u} (S : Signature.{u,v,w} Index) (i : Index) : Relation :=
  TruthPER (Closure S i)

theorem truthFamilyPER_laws {Index : Type u} (S : Signature.{u,v,w} Index) (i : Index) :
    Laws (TruthFamilyPER S i) := truthPER_laws _

def emptySignature : Signature Unit where
  Rule := fun _ => Empty
  Premise := fun _ _ => Unit
  child := fun _ _ _ => ()

theorem emptyClosure_false {i : Unit} (h : Closure emptySignature i) : False := by
  cases h with | node _ r _ => exact nomatch r

/-- The one-constructor, one-recursive-field signature of the admitted Loop. -/
def loopSignature : Signature Unit where
  Rule := fun _ => Unit
  Premise := fun _ _ => Unit
  child := fun _ _ _ => ()

theorem loopClosure_false {i : Unit} (h : Closure loopSignature i) : False :=
  closure_least loopSignature (P := fun _ => False)
    (fun _ ⟨_, hs⟩ => hs ()) i h

abbrev loopContext : LCtxA := [.assumption (.const 60 [])]

def loopContext_wf : CtxWfA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 loopContext :=
  .assumption .nil (pinLoopConstTy rfl)

def loopMajor_typed : HasTyA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 loopContext
    (.bvar 0) (.const 60 []) := pinLoopVarTy rfl 0 rfl

def LoopRealises (ρ : EnvI) : Prop := Member (TruthFamilyPER loopSignature ()) (ρ 0)

theorem loopContext_no_realization : ¬ ∃ ρ, LoopRealises ρ := by
  rintro ⟨ρ, hρ⟩
  exact loopClosure_false hρ.1

/-- This source environment is a real groupRec admission, without adding an
axiom declaration. The empty-context-realisation gap is therefore not only
about arbitrary source axioms. -/
theorem inhabited_loop_context_boundary :
    Nonempty (EnvWfA (iotaIfaceA pinLoopEnvA) pinLoopEnvA) ∧
    Nonempty (CtxWfA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 loopContext) ∧
    Nonempty (HasTyA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 [] (.const 60 []) (.sort .zero)) ∧
    Nonempty (HasTyA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 loopContext
      (.bvar 0) (.const 60 [])) ∧
    Nonempty (HasTyA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 loopContext
      (.sort .zero) (.sort (.succ .zero))) ∧
    (¬ ∃ ρ, LoopRealises ρ) :=
  ⟨⟨pinLoop_wf⟩, ⟨loopContext_wf⟩, ⟨pinLoopConstTy rfl⟩,
    ⟨loopMajor_typed⟩, ⟨.sort loopContext .zero⟩, loopContext_no_realization⟩

end Rcic.Declarative.Ann.LR3.TypedInductive
