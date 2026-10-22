import rcic.RcicAnnLR3NeutralPER

/-!
# Constructor closure with neutral leaves on the existing carrier

The carrier is a positive inductive predicate on `UnitModel.Value`.  Its
neutral leaves and constructor outputs are explicit semantic values.
Constructor closure consumes extended child memberships, including neutral
children, without selecting values or constructor evidence from Prop.

The leastness theorem eliminates into Prop.  It does not supply a
value-valued recursor or prove that an eliminator respects the indiscrete
proof PER.  Constructor operations remain explicit parameters.  The Loop
example supplies a real unary target spine operation and its denotation
equation, but asserts no source constructor or recursor soundness theorem.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.NeutralFamily
open Rcic.Declarative
open UnitModel TypedPER TypedInductive
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
universe u v w

abbrev ConstructorOp {Index : Type u} (S : Signature.{u,v,w} Index) :=
  ∀ (i : Index) (r : S.Rule i), (S.Premise i r → Value) → Value

/-- Positive constructor closure over values supplied by the caller.
There is no extraction of a child value from an existential proof. -/
inductive NeutralClosure {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S) : Index → Value → Prop
  | neutral (i : Index) (x : Value) (hx : N i x) : NeutralClosure S N ctor i x
  | node (i : Index) (r : S.Rule i) (xs : S.Premise i r → Value)
      (children : ∀ p : S.Premise i r, NeutralClosure S N ctor (S.child i r p) (xs p)) :
      NeutralClosure S N ctor i (ctor i r xs)

def Step {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S)
    (P : Index → Value → Prop) (i : Index) (x : Value) : Prop :=
  N i x ∨ ∃ (r : S.Rule i) (xs : S.Premise i r → Value),
    x = ctor i r xs ∧ ∀ p : S.Premise i r, P (S.child i r p) (xs p)

theorem step_monotone {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S)
    {P Q : Index → Value → Prop} (h : ∀ i x, P i x → Q i x) {i : Index} {x : Value} :
    Step S N ctor P i x → Step S N ctor Q i x := by
  intro hx
  rcases hx with hn | ⟨r, xs, he, hp⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, xs, he, fun p => h _ _ (hp p)⟩

theorem closure_unfold {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S) (i : Index) (x : Value) :
    NeutralClosure S N ctor i x ↔ Step S N ctor (NeutralClosure S N ctor) i x := by
  constructor
  · intro hx
    cases hx with
    | neutral i x hn => exact Or.inl hn
    | node i r xs children => exact Or.inr ⟨r, xs, rfl, children⟩
  · intro hx
    rcases hx with hn | ⟨r, xs, he, children⟩
    · exact .neutral i x hn
    · subst x
      exact .node i r xs children

/-- Leastness into Prop; no recursor result is selected from membership. -/
theorem closure_least {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S)
    {P : Index → Value → Prop}
    (closed : ∀ i x, Step S N ctor P i x → P i x) :
    ∀ i x, NeutralClosure S N ctor i x → P i x := by
  intro i x hx
  induction hx with
  | neutral i x hn => exact closed i x (Or.inl hn)
  | node i r xs children ih => exact closed i (ctor i r xs) (Or.inr ⟨r, xs, rfl, ih⟩)

theorem closure_mono_neutrals {Index : Type u} (S : Signature.{u,v,w} Index)
    {N M : Index → Value → Prop} (ctor : ConstructorOp S)
    (hNM : ∀ i x, N i x → M i x) {i : Index} {x : Value}
    (hx : NeutralClosure S N ctor i x) : NeutralClosure S M ctor i x := by
  induction hx with
  | neutral i x hn => exact .neutral i x (hNM i x hn)
  | node i r xs children ih => exact .node i r xs ih

/-- All inhabitants of a proposition-valued family are related.  The
observational values of a neutral and of a constructor remain available. -/
def FamilyPER {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S) (i : Index) (x y : Value) : Prop :=
  NeutralClosure S N ctor i x ∧ NeutralClosure S N ctor i y

theorem familyPER_laws {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S) (i : Index) :
    Laws (FamilyPER S N ctor i) where
  symm := fun h => ⟨h.2, h.1⟩
  trans := fun h g => ⟨h.1, g.2⟩

theorem familyPER_member_iff {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S) (i : Index) (x : Value) :
    Member (FamilyPER S N ctor i) x ↔ NeutralClosure S N ctor i x :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem familyPER_irrelevant {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} {ctor : ConstructorOp S} {i : Index} {x y : Value}
    (hx : Member (FamilyPER S N ctor i) x) (hy : Member (FamilyPER S N ctor i) y) :
    FamilyPER S N ctor i x y := ⟨hx.1, hy.1⟩

theorem neutral_member {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S) {i : Index} {x : Value}
    (hx : N i x) : Member (FamilyPER S N ctor i) x :=
  ⟨.neutral i x hx, .neutral i x hx⟩

/-- The constructor arm consumes membership in this extended carrier at
every recursive position, so neutral children are admitted directly. -/
theorem constructor_member {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S)
    (i : Index) (r : S.Rule i) (xs : S.Premise i r → Value)
    (children : ∀ p : S.Premise i r,
      Member (FamilyPER S N ctor (S.child i r p)) (xs p)) :
    Member (FamilyPER S N ctor i) (ctor i r xs) :=
  ⟨.node i r xs (fun p => (children p).1),
    .node i r xs (fun p => (children p).1)⟩

theorem constructor_related {Index : Type u} (S : Signature.{u,v,w} Index)
    (N : Index → Value → Prop) (ctor : ConstructorOp S)
    (i : Index) (r : S.Rule i) (xs ys : S.Premise i r → Value)
    (children : ∀ p : S.Premise i r,
      FamilyPER S N ctor (S.child i r p) (xs p) (ys p)) :
    FamilyPER S N ctor i (ctor i r xs) (ctor i r ys) :=
  ⟨.node i r xs (fun p => (children p).1),
    .node i r ys (fun p => (children p).2)⟩

/-- The zero-constructor case still contains exactly its chosen neutrals. -/
theorem empty_closure_iff (N : Unit → Value → Prop) (ctor : ConstructorOp emptySignature)
    (i : Unit) (x : Value) : NeutralClosure emptySignature N ctor i x ↔ N i x := by
  constructor
  · intro h
    cases h with
    | neutral i x hx => exact hx
    | node i r xs children => exact nomatch r
  · exact fun hx => .neutral i x hx

theorem empty_familyPER_iff (N : Unit → Value → Prop) (ctor : ConstructorOp emptySignature)
    (i : Unit) (x y : Value) : FamilyPER emptySignature N ctor i x y ↔ N i x ∧ N i y :=
  ⟨fun h => ⟨(empty_closure_iff N ctor i x).mp h.1,
    (empty_closure_iff N ctor i y).mp h.2⟩,
    fun h => ⟨(empty_closure_iff N ctor i x).mpr h.1,
      (empty_closure_iff N ctor i y).mpr h.2⟩⟩

/-- A concrete constructor operation, retaining the child's observations
as an argument of a unary target constant spine. -/
def unarySpine (head : Nat) (x : Value) : Value :=
  fun c => c = .bot ∨ ∃ a : CptI, x a ∧ c = .spine head [a]

theorem unarySpine_observed (head : Nat) {x : Value} {a : CptI} (hx : x a) :
    unarySpine head x (.spine head [a]) := Or.inr ⟨a, hx, rfl⟩

theorem unarySpine_nonbottom (head : Nat) {x : Value} {a : CptI} (hx : x a) :
    ¬ ValueEq (unarySpine head x) bottom := by
  intro h
  have hb := (h (.spine head [a])).mp (unarySpine_observed head hx)
  cases hb

/-- The operation agrees with inherited compositional target application
on a denoted argument.  This equation does not rely on source typing. -/
theorem unarySpine_denI (ρ : EnvI) (head : Nat) (e : Expr Nat) :
    ValueEq (unarySpine head (denI ρ e)) (denI ρ (.app (.const head []) e)) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨a, ha, hc⟩
    · subst c
      exact ApproxI.bot ρ _
    · subst c
      exact approxI_famApp head [] (.cons ha .nil)
  · intro hc
    rcases approxI_foldApps_const_inv (r := head) (ls := []) (xs := [e]) hc
      with hc | ⟨us, he, hs⟩
    · exact Or.inl hc
    · cases hs with
      | cons ha hs =>
        cases hs
        subst c
        exact Or.inr ⟨_, ha, rfl⟩

def loopNeutral (leaf : Nat) : Unit → Value → Prop :=
  fun _ => NeutralPER.AtomNeutral leaf

def loopCtor (head : Nat) : ConstructorOp loopSignature :=
  fun _ _ xs => unarySpine head (xs ())

theorem loop_leaf_member (head leaf : Nat) :
    Member (FamilyPER loopSignature (loopNeutral leaf) (loopCtor head) ())
      (NeutralPER.neutralAtom leaf) :=
  neutral_member loopSignature (loopNeutral leaf) (loopCtor head)
    (NeutralPER.neutralAtom_is_neutral leaf)

theorem loop_constructor_member (head leaf : Nat) :
    Member (FamilyPER loopSignature (loopNeutral leaf) (loopCtor head) ())
      (unarySpine head (NeutralPER.neutralAtom leaf)) :=
  constructor_member loopSignature (loopNeutral leaf) (loopCtor head) () ()
    (fun _ => NeutralPER.neutralAtom leaf) (fun _ => loop_leaf_member head leaf)

theorem loop_constructor_target (head leaf : Nat) :
    ValueEq (loopCtor head () () (fun _ => NeutralPER.neutralAtom leaf))
      (denI EnvI.bot (.app (.const head []) (.const leaf []))) :=
  unarySpine_denI EnvI.bot head (.const leaf [])

theorem loop_constructor_not_atomNeutral (head leaf : Nat) :
    ¬ NeutralPER.AtomNeutral leaf (unarySpine head (NeutralPER.neutralAtom leaf)) := by
  intro h
  have ho := unarySpine_observed head (NeutralPER.neutralAtom_observed leaf)
  have ha := (h _).mp ho
  rcases approxI_const_inv ha with hb | hs
  · cases hb
  · cases hs

/-- This node really uses the constructor branch: it is not an atom leaf,
while the previous closure with no neutral leaves remains empty. -/
theorem loop_extended_constructor_control (head leaf : Nat) :
    Member (FamilyPER loopSignature (loopNeutral leaf) (loopCtor head) ())
      (NeutralPER.neutralAtom leaf) ∧
    Member (FamilyPER loopSignature (loopNeutral leaf) (loopCtor head) ())
      (unarySpine head (NeutralPER.neutralAtom leaf)) ∧
    (¬ NeutralPER.AtomNeutral leaf (unarySpine head (NeutralPER.neutralAtom leaf))) ∧
    (¬ Closure loopSignature ()) :=
  ⟨loop_leaf_member head leaf, loop_constructor_member head leaf,
    loop_constructor_not_atomNeutral head leaf, loopClosure_false⟩

end Rcic.Declarative.Ann.LR3.NeutralFamily
