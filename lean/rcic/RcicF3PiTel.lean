import rcic.RcicF3KTWG

/-!
# Dependent Pi telescopes as guarded-W branch addresses

This is a semantic telescope, independent of raw expression syntax. Its
length is arbitrary; each domain can depend on all earlier arguments.
Flattening turns a nested function field into a function on dependent-sum
addresses. No choice or finiteness of the domains is used.

This module does not extract telescopes from `HasTyT` and does not claim
`StepAG`. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet

universe u v

/-- A dependent telescope with exactly `m` binders. -/
inductive PiTel : Nat → Type (u + 1) where
  | nil : PiTel 0
  | cons {m : Nat} (A : Type u) (B : A → PiTel m) : PiTel (m + 1)

/-- Full argument tuples, including the dependencies between arguments. -/
def PiTel.Path : {m : Nat} → PiTel.{u} m → Type u
  | _, .nil => PUnit
  | _, .cons A B => (a : A) × (B a).Path

/-- Nested dependent functions, with a result type at each complete path. -/
def PiTel.Value : {m : Nat} → (t : PiTel.{u} m) → (t.Path → Type (max u v)) → Type (max u v)
  | _, .nil, X => X PUnit.unit
  | _, .cons _ B, X => (a : _) → (B a).Value (fun p => X ⟨a, p⟩)

/-- Evaluate the nested field at a full path. -/
def PiTel.flatten : {m : Nat} → (t : PiTel.{u} m) →
    {X : t.Path → Type (max u v)} → t.Value X → (p : t.Path) → X p
  | _, .nil, _, f, .unit => f
  | _, .cons _ B, _, f, p => (B p.1).flatten (f p.1) p.2

/-- Rebuild a nested field from its values at full paths. -/
def PiTel.unflatten : {m : Nat} → (t : PiTel.{u} m) →
    {X : t.Path → Type (max u v)} → ((p : t.Path) → X p) → t.Value X
  | _, .nil, _, f => f PUnit.unit
  | _, .cons _ B, _, f => fun a => (B a).unflatten (fun p => f ⟨a, p⟩)

/-- Flattening after rebuilding preserves the complete assignment. -/
theorem PiTel.flatten_unflatten {m : Nat} (t : PiTel.{u} m)
    {X : t.Path → Type (max u v)} (f : (p : t.Path) → X p) :
    t.flatten (t.unflatten f) = f := by
  induction t with
  | nil => funext p; cases p; rfl
  | cons A B ih =>
      funext p
      exact congrFun (ih p.1 (fun q => f ⟨p.1, q⟩)) p.2

/-- Rebuilding after flattening preserves the nested dependent function. -/
theorem PiTel.unflatten_flatten {m : Nat} (t : PiTel.{u} m)
    {X : t.Path → Type (max u v)} (f : t.Value X) :
    t.unflatten (t.flatten f) = f := by
  induction t with
  | nil => rfl
  | cons A B ih =>
      funext a
      exact ih a (f a)

/-- A unary logical relation lifted through the dependent function field. -/
def PiTel.All : {m : Nat} → (t : PiTel.{u} m) →
    {X : t.Path → Type (max u v)} →
    ((p : t.Path) → X p → Prop) → t.Value X → Prop
  | _, .nil, _, R, f => R .unit f
  | _, .cons _ B, _, R, f => ∀ a, (B a).All (fun p => R ⟨a, p⟩) (f a)

/-- Lifting the relation through every binder is equivalent to testing
every complete dependent address. -/
theorem PiTel.all_iff {m : Nat} (t : PiTel.{u} m)
    {X : t.Path → Type (max u v)} (R : (p : t.Path) → X p → Prop)
    (f : t.Value X) : t.All R f ↔ ∀ p, R p (t.flatten f p) := by
  induction t with
  | nil =>
    constructor
    · intro h p; cases p; exact h
    · intro h; exact h .unit
  | cons A B ih =>
    constructor
    · intro h p
      exact (ih p.1 _ _).mp (h p.1) p.2
    · intro h a
      exact (ih a _ _).mpr (fun p => h ⟨a, p⟩)

/-- A guarded constructor signature whose recursive fields are given in
nested dependent-function form. Shapes include nonrecursive parameters;
`Field s` can be empty, so nullary constructors have no artificial child. -/
structure PiSig where
  Sh : Type u
  Field : Sh → Type u
  depth : (s : Sh) → Field s → Nat
  tel : (s : Sh) → (k : Field s) → PiTel.{u} (depth s k)
  code : (s : Sh) → ((k : Field s) →
    PiTel.Value.{u, u + 1} (tel s k) (fun _ => PSet.{u})) → PSet.{u}
  ok : (s : Sh) → ((k : Field s) →
    PiTel.Value.{u, u + 1} (tel s k) (fun _ => PSet.{u})) → Prop
  code_congr : ∀ s f g,
    (∀ k p, Equiv ((tel s k).flatten (f k) p) ((tel s k).flatten (g k) p)) →
    Equiv (code s f) (code s g)
  ok_congr : ∀ s f g,
    (∀ k p, Equiv ((tel s k).flatten (f k) p) ((tel s k).flatten (g k) p)) →
    ok s f → ok s g

/-- Compose telescope flattening with the landed guarded-W construction.
The guards still see the complete decoded child assignment. -/
def PiSig.toGSig (S : PiSig.{u}) : GSig.{u} where
  Sh := S.Sh
  br := fun s => (k : S.Field s) × (S.tel s k).Path
  code := fun s h => S.code s (fun k => (S.tel s k).unflatten (fun p => h ⟨k, p⟩))
  ok := fun s h => S.ok s (fun k => (S.tel s k).unflatten (fun p => h ⟨k, p⟩))
  code_congr := by
    intro s h h' eh
    apply S.code_congr
    intro k p
    simpa only [PiTel.flatten_unflatten] using eh ⟨k, p⟩
  ok_congr := by
    intro s h h' eh hok
    apply S.ok_congr s _ _ _ hok
    intro k p
    simpa only [PiTel.flatten_unflatten] using eh ⟨k, p⟩

/-- A constructor with its recursive arguments in nested function form. -/
def PiSig.roll (S : PiSig.{u}) (s : S.Sh)
    (f : (k : S.Field s) → (S.tel s k).Value (fun _ => GT S.toGSig)) : GT S.toGSig :=
  .sup s (fun p => (S.tel s p.1).flatten (f p.1) p.2)

/-- Structural induction expressed in the original nested function fields.
Every recursive child contributes an induction hypothesis, at arbitrary
dependent telescope depth. No accepted-shape or finite-height premise. -/
theorem PiSig.induction (S : PiSig.{u}) (Q : GT S.toGSig → Prop)
    (step : ∀ s f, (∀ k, (S.tel s k).All (fun _ w => Q w) (f k)) →
      Q (S.roll s f)) : ∀ w, Q w := by
  intro w
  induction w with
  | sup s g ih =>
    have h := step s (fun k => (S.tel s k).unflatten (fun p => g ⟨k, p⟩))
      (fun k => (PiTel.all_iff _ _ _).mpr (fun p => by
        simpa only [PiTel.flatten_unflatten] using ih ⟨k, p⟩))
    simpa only [PiSig.roll, PiTel.flatten_unflatten] using h

/-- Guarded construction in nested-field form. The guard is tested on
the decoded assignment; it is not dropped by branch flattening. -/
theorem PiSig.roll_valid (S : PiSig.{u}) (s : S.Sh)
    (f : (k : S.Field s) → (S.tel s k).Value (fun _ => GT S.toGSig))
    (hf : ∀ k, (S.tel s k).All (fun _ w => ValidW S.toGSig w) (f k))
    (hok : S.ok s (fun k => (S.tel s k).unflatten
      (fun p => decG S.toGSig ((S.tel s k).flatten (f k) p)))) :
    ValidW S.toGSig (S.roll s f) := by
  apply ValidW.sup
  · intro p
    exact (PiTel.all_iff _ _ _).mp (hf p.1) p.2
  · exact hok

end Rcic.F3.PSet
