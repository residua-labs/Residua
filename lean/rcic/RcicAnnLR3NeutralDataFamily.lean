import rcic.RcicAnnLR3NeutralFamily

/-!
# Data families with neutral leaves and a constructive quotient recursor

The input of the recursor is explicit data, not a proof of membership in
`NeutralClosure`.  Its structural PER preserves constructors and relates
neutral leaves by an arbitrary supplied leaf PER.  The fold has a separate
neutral branch and its two computation rules are definitional.

Restricting to self-related trees gives a setoid.  A fold whose neutral
branch respects leaf equivalence factors through its quotient by an actual
`Quotient.lift`; constructor compatibility is derived from function
congruence.  No representative or recursive evidence is selected from Prop.

An explicit interpreter maps these trees to the existing `UnitModel.Value`.
It supplies membership in the earlier neutral constructor closure and a
relational interpretation theorem.  Paired values retain their tree data,
so the quotient recursor also operates on those pairs constructively.  No
factorisation through bare observational values, source family decoder, or
source recursor soundness theorem is asserted here.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Rcic.Declarative.Ann.LR3.NeutralDataFamily
open UnitModel TypedInductive
universe u v w l z

structure RelLaws {A : Sort z} (R : A → A → Prop) : Prop where
  symm : ∀ {x y}, R x y → R y x
  trans : ∀ {x y t}, R x y → R y t → R x t

/-- Indexed, data-valued trees.  Neutral leaf data is retained explicitly. -/
inductive Tree {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) : Index → Type (max u v w l)
  | neutral (i : Index) (a : Leaf i) : Tree S Leaf i
  | node (i : Index) (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)) : Tree S Leaf i

/-- Constructor-sensitive bisimulation, with an arbitrary PER on leaves. -/
inductive Bisim {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop) :
    {i : Index} → Tree S Leaf i → Tree S Leaf i → Prop
  | neutral (i : Index) (a b : Leaf i) (h : RN i a b) :
      Bisim S Leaf RN (.neutral i a) (.neutral i b)
  | node (i : Index) (r : S.Rule i)
      (xs ys : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p))
      (children : ∀ p : S.Premise i r, Bisim S Leaf RN (xs p) (ys p)) :
      Bisim S Leaf RN (.node i r xs) (.node i r ys)

theorem bisim_symm {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    (hRN : ∀ i, RelLaws (RN i)) {i : Index} {x y : Tree S Leaf i}
    (hxy : Bisim S Leaf RN x y) : Bisim S Leaf RN y x := by
  induction hxy with
  | neutral i a b hab => exact .neutral i b a ((hRN i).symm hab)
  | node i r xs ys children ih => exact .node i r ys xs ih

theorem bisim_trans {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    (hRN : ∀ i, RelLaws (RN i)) {i : Index} {x y t : Tree S Leaf i}
    (hxy : Bisim S Leaf RN x y) (hyt : Bisim S Leaf RN y t) :
    Bisim S Leaf RN x t := by
  induction hxy with
  | neutral i a b hab =>
    cases hyt with
    | neutral i b c hbc => exact .neutral i a c ((hRN i).trans hab hbc)
  | node i r xs ys children ih =>
    cases hyt with
    | node i r ys zs hyz => exact .node i r xs zs (fun p => ih p (hyz p))

theorem bisim_laws {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop)
    (hRN : ∀ i, RelLaws (RN i)) (i : Index) :
    RelLaws (fun x y : Tree S Leaf i => Bisim S Leaf RN x y) where
  symm := bisim_symm hRN
  trans := bisim_trans hRN

theorem bisim_refl {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    (hRN : ∀ i a, RN i a a) {i : Index} (t : Tree S Leaf i) :
    Bisim S Leaf RN t t := by
  induction t with
  | neutral i a => exact .neutral i a a (hRN i a)
  | node i r children ih => exact .node i r children children ih

theorem neutral_not_bisim_node {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    (i : Index) (a : Leaf i) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)) :
    ¬ Bisim S Leaf RN (.neutral i a) (.node i r children) := by
  intro h
  cases h

theorem bisim_node_labels {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {i : Index} {r s : S.Rule i}
    {xs : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)}
    {ys : ∀ p : S.Premise i s, Tree S Leaf (S.child i s p)}
    (h : Bisim S Leaf RN (.node i r xs) (.node i s ys)) : r = s := by
  cases h
  rfl

/-- A data-valued fold, including an explicit neutral-stuck operation.
`noncomputable` only avoids Lean 4.14 code generation for this nested
indexed recursor.  The term uses no choice, and both equations are rfl. -/
noncomputable def fold {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {Result : Index → Type z}
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i) :
    ∀ {i}, Tree S Leaf i → Result i :=
  fun {i} t => Tree.rec (motive := fun i _ => Result i)
    (fun i a => neutral i a)
    (fun i r _children ih => algebra i r ih) t

theorem fold_neutral {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {Result : Index → Type z}
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (i : Index) (a : Leaf i) :
    fold neutral algebra (Tree.neutral i a) = neutral i a := rfl

theorem fold_node {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {Result : Index → Type z}
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)) :
    fold neutral algebra (Tree.node i r children) =
      algebra i r (fun p => fold neutral algebra (children p)) := rfl

/-- A compositional relation theorem, proved by induction on bisimulation. -/
theorem fold_respects {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {Result : Index → Type z} (Q : ∀ i, Result i → Result i → Prop)
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → Q i (neutral i a) (neutral i b))
    (hc : ∀ i (r : S.Rule i)
      (xs ys : ∀ p : S.Premise i r, Result (S.child i r p)),
      (∀ p, Q (S.child i r p) (xs p) (ys p)) → Q i (algebra i r xs) (algebra i r ys))
    {i : Index} {x y : Tree S Leaf i} (hxy : Bisim S Leaf RN x y) :
    Q i (fold neutral algebra x) (fold neutral algebra y) := by
  induction hxy with
  | neutral i a b hab => exact hn i a b hab
  | node i r xs ys children ih => exact hc i r _ _ ih

/-- For equality-valued factorisation, constructor congruence is supplied
by the actual algebra function.  Only leaf-equivalence respect is input. -/
theorem fold_respects_eq {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {Result : Index → Type z}
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b)
    {i : Index} {x y : Tree S Leaf i} (hxy : Bisim S Leaf RN x y) :
    fold neutral algebra x = fold neutral algebra y :=
  fold_respects (fun _ a b => a = b) neutral algebra hn
    (fun i r _ _ h => congrArg (algebra i r) (funext h)) hxy

abbrev LegalTree {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop) (i : Index) :=
  {t : Tree S Leaf i // Bisim S Leaf RN t t}

def legalNeutral {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop)
    (i : Index) (a : Leaf i) (ha : RN i a a) : LegalTree S Leaf RN i :=
  ⟨.neutral i a, .neutral i a a ha⟩

def legalNode {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop)
    (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)) :
    LegalTree S Leaf RN i :=
  ⟨.node i r (fun p => (children p).1),
    .node i r _ _ (fun p => (children p).2)⟩

def treeSetoid {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop)
    (hRN : ∀ i, RelLaws (RN i)) (i : Index) : Setoid (LegalTree S Leaf RN i) where
  r x y := Bisim S Leaf RN x.1 y.1
  iseqv := ⟨fun x => x.2, fun h => bisim_symm hRN h,
    fun h g => bisim_trans hRN h g⟩

/-- An actual constructive factor through the PER quotient.  Quotient
elimination applies the already-defined fold; it chooses no tree. -/
noncomputable def quotientFold {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {Result : Index → Type z} (hRN : ∀ i, RelLaws (RN i))
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b) {i : Index} :
    Quotient (treeSetoid S Leaf RN hRN i) → Result i :=
  Quotient.lift (fun t : LegalTree S Leaf RN i => fold neutral algebra t.1)
    (fun _ _ h => fold_respects_eq neutral algebra hn h)

theorem quotientFold_mk {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {Result : Index → Type z} (hRN : ∀ i, RelLaws (RN i))
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b)
    {i : Index} (t : LegalTree S Leaf RN i) :
    quotientFold hRN neutral algebra hn (Quotient.mk _ t) = fold neutral algebra t.1 := rfl

theorem quotientFold_neutral {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {Result : Index → Type z} (hRN : ∀ i, RelLaws (RN i))
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b)
    (i : Index) (a : Leaf i) (ha : RN i a a) :
    quotientFold hRN neutral algebra hn
      (Quotient.mk _ (legalNeutral S Leaf RN i a ha)) = neutral i a := rfl

theorem quotientFold_node {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {Result : Index → Type z} (hRN : ∀ i, RelLaws (RN i))
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b)
    (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)) :
    quotientFold hRN neutral algebra hn (Quotient.mk _ (legalNode S Leaf RN i r children)) =
      algebra i r (fun p => quotientFold hRN neutral algebra hn (Quotient.mk _ (children p))) := rfl

def interpret {Index : Type u} {S : Signature.{u,v,w} Index} {Leaf : Index → Type l}
    (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : Tree S Leaf i) : Value := fold leafValue ctor t

theorem interpret_neutral {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} (leafValue : ∀ i, Leaf i → Value)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) (a : Leaf i) :
    interpret leafValue ctor (Tree.neutral i a) = leafValue i a := rfl

theorem interpret_node {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} (leafValue : ∀ i, Leaf i → Value)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)) :
    interpret leafValue ctor (Tree.node i r children) =
      ctor i r (fun p => interpret leafValue ctor (children p)) := rfl

theorem interpret_closure {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} (N : Index → Value → Prop)
    (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S)
    (hn : ∀ i a, N i (leafValue i a)) {i : Index} (t : Tree S Leaf i) :
    NeutralFamily.NeutralClosure S N ctor i (interpret leafValue ctor t) := by
  induction t with
  | neutral i a => exact .neutral i _ (hn i a)
  | node i r children ih => exact .node i r _ ih

theorem interpret_proof_member {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} (N : Index → Value → Prop)
    (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S)
    (hn : ∀ i a, N i (leafValue i a)) {i : Index} (t : Tree S Leaf i) :
    TypedPER.Member (NeutralFamily.FamilyPER S N ctor i) (interpret leafValue ctor t) :=
  ⟨interpret_closure N leafValue ctor hn t, interpret_closure N leafValue ctor hn t⟩

def LeafValueEq {Index : Type u} {Leaf : Index → Type l}
    (leafValue : ∀ i, Leaf i → Value) (i : Index) (a b : Leaf i) : Prop :=
  ValueEq (leafValue i a) (leafValue i b)

theorem leafValueEq_laws {Index : Type u} {Leaf : Index → Type l}
    (leafValue : ∀ i, Leaf i → Value) (i : Index) : RelLaws (LeafValueEq leafValue i) where
  symm := fun h => h.symm
  trans := fun h g => h.trans g

def ConstructorCongruent {Index : Type u} {S : Signature.{u,v,w} Index}
    (ctor : NeutralFamily.ConstructorOp S) : Prop :=
  ∀ i (r : S.Rule i) (xs ys : S.Premise i r → Value),
    (∀ p, ValueEq (xs p) (ys p)) → ValueEq (ctor i r xs) (ctor i r ys)

theorem interpret_bisim_valueEq {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} (leafValue : ∀ i, Leaf i → Value)
    (ctor : NeutralFamily.ConstructorOp S) (hc : ConstructorCongruent ctor)
    {i : Index} {x y : Tree S Leaf i}
    (hxy : Bisim S Leaf (LeafValueEq leafValue) x y) :
    ValueEq (interpret leafValue ctor x) (interpret leafValue ctor y) :=
  fold_respects (fun _ => ValueEq) leafValue ctor (fun _ _ _ h => h) hc hxy

/-- A pair retains the explicit recursor input and its semantic denotation.
Its representation equation is data supplied when forming the pair. -/
structure Paired {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop)
    (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S) (i : Index) where
  tree : Tree S Leaf i
  admitted : Bisim S Leaf RN tree tree
  value : Value
  value_eq : value = interpret leafValue ctor tree

def pair {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : LegalTree S Leaf RN i) : Paired S Leaf RN leafValue ctor i :=
  ⟨t.1, t.2, interpret leafValue ctor t.1, rfl⟩

def PairPER {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S} {i : Index}
    (x y : Paired S Leaf RN leafValue ctor i) : Prop := Bisim S Leaf RN x.tree y.tree

theorem pairPER_laws {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    (hRN : ∀ i, RelLaws (RN i)) (i : Index) :
    RelLaws (fun x y : Paired S Leaf RN leafValue ctor i => PairPER x y) where
  symm := fun h => bisim_symm hRN h
  trans := fun h g => bisim_trans hRN h g

def pairedClass {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    (hRN : ∀ i, RelLaws (RN i)) {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    Quotient (treeSetoid S Leaf RN hRN i) := Quotient.mk _ ⟨p.tree, p.admitted⟩

noncomputable def pairedFold {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {Result : Index → Type z} (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    {i : Index} (p : Paired S Leaf RN leafValue ctor i) : Result i :=
  fold neutral algebra p.tree

theorem pairedFold_factors {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {Result : Index → Type z} (hRN : ∀ i, RelLaws (RN i))
    (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b)
    {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    quotientFold hRN neutral algebra hn (pairedClass hRN p) = pairedFold neutral algebra p := rfl

theorem pairedFold_respects {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {Result : Index → Type z} (neutral : ∀ i, Leaf i → Result i)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)
    (hn : ∀ i a b, RN i a b → neutral i a = neutral i b)
    {i : Index} {p q : Paired S Leaf RN leafValue ctor i} (hpq : PairPER p q) :
    pairedFold neutral algebra p = pairedFold neutral algebra q :=
  fold_respects_eq neutral algebra hn hpq

theorem paired_closure {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    (N : Index → Value → Prop) (hn : ∀ i a, N i (leafValue i a))
    {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    NeutralFamily.NeutralClosure S N ctor i p.value := by
  rw [p.value_eq]
  exact interpret_closure N leafValue ctor hn p.tree

theorem paired_values_related {Index : Type u} {S : Signature.{u,v,w} Index}
    {Leaf : Index → Type l} {leafValue : ∀ i, Leaf i → Value}
    {ctor : NeutralFamily.ConstructorOp S} (hc : ConstructorCongruent ctor)
    {i : Index} {p q : Paired S Leaf (LeafValueEq leafValue) leafValue ctor i}
    (hpq : PairPER p q) : ValueEq p.value q.value := by
  rw [p.value_eq, q.value_eq]
  exact interpret_bisim_valueEq leafValue ctor hc hpq

/-- Concrete neutral leaves carry their semantic value and its proof of
neutrality as ordinary subtype data.  The value is never chosen from Prop. -/
abbrev SemanticLeaf {Index : Type u} (N : Index → Value → Prop) (i : Index) :=
  {x : Value // N i x}

def semanticLeafValue {Index : Type u} (N : Index → Value → Prop)
    (i : Index) (a : SemanticLeaf N i) : Value := a.1

def semanticInterpret {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : Tree S (SemanticLeaf N) i) : Value :=
  interpret (semanticLeafValue N) ctor t

theorem semanticInterpret_closure {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : Tree S (SemanticLeaf N) i) :
    NeutralFamily.NeutralClosure S N ctor i (semanticInterpret ctor t) :=
  interpret_closure N (semanticLeafValue N) ctor (fun _ a => a.2) t

theorem semantic_bisim_refl {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} {i : Index} (t : Tree S (SemanticLeaf N) i) :
    Bisim S (SemanticLeaf N) (LeafValueEq (semanticLeafValue N)) t t :=
  bisim_refl (Leaf := SemanticLeaf N) (RN := LeafValueEq (semanticLeafValue N))
    (fun (i : Index) (a : SemanticLeaf N i) => ValueEq.refl a.1) t

/-- Every explicit semantic tree supplies its own paired value and data-PER
membership.  The caller need not postulate the assembled membership. -/
def semanticPair {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : Tree S (SemanticLeaf N) i) :
    Paired S (SemanticLeaf N) (LeafValueEq (semanticLeafValue N))
      (semanticLeafValue N) ctor i :=
  pair (semanticLeafValue N) ctor ⟨t, semantic_bisim_refl t⟩

theorem semanticPair_value {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : Tree S (SemanticLeaf N) i) :
    (semanticPair ctor t).value = semanticInterpret ctor t := rfl

theorem semanticPair_closure {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} (t : Tree S (SemanticLeaf N) i) :
    NeutralFamily.NeutralClosure S N ctor i (semanticPair ctor t).value :=
  paired_closure N (fun _ a => a.2) (semanticPair ctor t)

theorem semanticPair_related {Index : Type u} {S : Signature.{u,v,w} Index}
    {N : Index → Value → Prop} (ctor : NeutralFamily.ConstructorOp S)
    {i : Index} {x y : Tree S (SemanticLeaf N) i}
    (hxy : Bisim S (SemanticLeaf N) (LeafValueEq (semanticLeafValue N)) x y) :
    PairPER (semanticPair ctor x) (semanticPair ctor y) := hxy

theorem unarySpine_congr (head : Nat) {x y : Value} (hxy : ValueEq x y) :
    ValueEq (NeutralFamily.unarySpine head x) (NeutralFamily.unarySpine head y) := by
  intro c
  constructor
  · intro h
    rcases h with hb | ⟨a, ha, he⟩
    · exact Or.inl hb
    · exact Or.inr ⟨a, (hxy a).mp ha, he⟩
  · intro h
    rcases h with hb | ⟨a, ha, he⟩
    · exact Or.inl hb
    · exact Or.inr ⟨a, (hxy a).mpr ha, he⟩

theorem loopCtor_congr (head : Nat) : ConstructorCongruent (NeutralFamily.loopCtor head) :=
  fun _ _ _ _ h => unarySpine_congr head (h ())

def loopLeaf (leaf : Nat) : Tree loopSignature (SemanticLeaf (NeutralFamily.loopNeutral leaf)) () :=
  .neutral () ⟨NeutralPER.neutralAtom leaf, NeutralPER.neutralAtom_is_neutral leaf⟩

def loopNode (leaf : Nat) : Tree loopSignature (SemanticLeaf (NeutralFamily.loopNeutral leaf)) () :=
  .node () () (fun _ => loopLeaf leaf)

theorem loopLeaf_interpret (head leaf : Nat) :
    semanticInterpret (NeutralFamily.loopCtor head) (loopLeaf leaf) = NeutralPER.neutralAtom leaf := rfl

theorem loopNode_interpret (head leaf : Nat) :
    semanticInterpret (NeutralFamily.loopCtor head) (loopNode leaf) =
      NeutralFamily.unarySpine head (NeutralPER.neutralAtom leaf) := rfl

theorem loop_data_interpretation (head leaf : Nat) :
    NeutralFamily.NeutralClosure loopSignature (NeutralFamily.loopNeutral leaf)
      (NeutralFamily.loopCtor head) ()
      (semanticInterpret (NeutralFamily.loopCtor head) (loopLeaf leaf)) ∧
    NeutralFamily.NeutralClosure loopSignature (NeutralFamily.loopNeutral leaf)
      (NeutralFamily.loopCtor head) ()
      (semanticInterpret (NeutralFamily.loopCtor head) (loopNode leaf)) :=
  ⟨semanticInterpret_closure _ (loopLeaf leaf), semanticInterpret_closure _ (loopNode leaf)⟩

end Rcic.Declarative.Ann.LR3.NeutralDataFamily
