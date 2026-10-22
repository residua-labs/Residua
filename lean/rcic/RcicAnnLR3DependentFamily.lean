import rcic.RcicAnnLR3NeutralDataFamily

/-!
# Major-dependent elimination on explicit neutral data

The motive depends on the actual major tree.  The constructor algebra
receives its children as data as well as their dependent recursive results.
A heterogeneous result relation gives a compositional bisimulation theorem.

Legal trees retain those data.  A motive on their quotient has canonical
transport along bisimulation, and the dependent eliminator factors through
that quotient by an actual `Quotient.lift` of result pairs.  No tree is
selected from a proposition or a quotient.  A tree motive without this
descent data is not asserted to factor through the quotient.

The final adapter treats major-dependent PER motives on the fixed native
value carrier.  This is an explicit-tree semantic eliminator and its local
computation/transport laws, not a source recursor theorem or a completed
fundamental statement.  `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.DependentFamily

open UnitModel TypedInductive NeutralDataFamily

universe u v w l z a b

section Explicit

variable {Index : Type u} {S : Signature.{u,v,w} Index}
  {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
  {Motive : ∀ i, Tree S Leaf i → Type z}

/-- The recursive result type may depend on the entire major tree.
`noncomputable` only avoids code generation for the indexed recursor. -/
noncomputable def eliminate
    (neutral : ∀ i a, Motive i (.neutral i a))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) → Motive i (.node i r children)) :
    ∀ {i} (t : Tree S Leaf i), Motive i t :=
  fun {i} t => Tree.rec (motive := Motive) neutral algebra t

theorem eliminate_neutral
    (neutral : ∀ i a, Motive i (.neutral i a))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) → Motive i (.node i r children))
    (i : Index) (a : Leaf i) :
    eliminate neutral algebra (.neutral i a) = neutral i a := rfl

theorem eliminate_node
    (neutral : ∀ i a, Motive i (.neutral i a))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) → Motive i (.node i r children))
    (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)) :
    eliminate neutral algebra (.node i r children) =
      algebra i r children (fun p => eliminate neutral algebra (children p)) := rfl

/-- A relation between results whose types may have different majors. -/
abbrev ResultRelation (M : ∀ i, Tree S Leaf i → Type z) :=
  ∀ i (x y : Tree S Leaf i), M i x → M i y → Prop

structure ResultLaws (Q : ResultRelation Motive) : Prop where
  symm : ∀ {i} {x y : Tree S Leaf i} {a : Motive i x} {b : Motive i y},
    Bisim S Leaf RN x y → Q i x y a b → Q i y x b a
  trans : ∀ {i} {x y t : Tree S Leaf i}
    {a : Motive i x} {b : Motive i y} {c : Motive i t},
    Bisim S Leaf RN x y → Bisim S Leaf RN y t →
    Q i x y a b → Q i y t b c → Q i x t a c

def totalResultPER (Q : ResultRelation Motive) {i : Index}
    (x y : Sigma (Motive i)) : Prop :=
  Bisim S Leaf RN x.1 y.1 ∧ Q i x.1 y.1 x.2 y.2

theorem totalResultPER_laws (hRN : ∀ i, RelLaws (RN i))
    (Q : ResultRelation Motive) (hQ : ResultLaws (RN := RN) Q) (i : Index) :
    RelLaws (fun x y : Sigma (Motive i) => totalResultPER (RN := RN) Q x y) where
  symm := fun h => ⟨bisim_symm hRN h.1, hQ.symm h.1 h.2⟩
  trans := fun h g => ⟨bisim_trans hRN h.1 g.1, hQ.trans h.1 g.1 h.2 g.2⟩

/-- The induction hypothesis relates results in the two actual child
fibres; the motive is not restricted to depend only on `Index`. -/
theorem eliminate_respects (Q : ResultRelation Motive)
    (neutral : ∀ i a, Motive i (.neutral i a))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) → Motive i (.node i r children))
    (hn : ∀ i a b, RN i a b →
      Q i (.neutral i a) (.neutral i b) (neutral i a) (neutral i b))
    (hc : ∀ i (r : S.Rule i)
      (xs ys : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p))
      (us : ∀ p, Motive (S.child i r p) (xs p))
      (vs : ∀ p, Motive (S.child i r p) (ys p)),
      (∀ p, Bisim S Leaf RN (xs p) (ys p)) →
      (∀ p, Q (S.child i r p) (xs p) (ys p) (us p) (vs p)) →
      Q i (.node i r xs) (.node i r ys) (algebra i r xs us) (algebra i r ys vs))
    {i : Index} {x y : Tree S Leaf i} (hxy : Bisim S Leaf RN x y) :
    Q i x y (eliminate neutral algebra x) (eliminate neutral algebra y) := by
  induction hxy with
  | neutral i a b hab => exact hn i a b hab
  | node i r xs ys children ih => exact hc i r xs ys _ _ children ih

theorem bisim_neutral_self {i : Index} {a : Leaf i}
    (h : Bisim S Leaf RN (.neutral i a) (.neutral i a)) : RN i a a := by
  cases h with
  | neutral i a a ha => exact ha

theorem bisim_node_self {i : Index} {r : S.Rule i}
    {xs : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p)}
    (h : Bisim S Leaf RN (.node i r xs) (.node i r xs)) :
    ∀ p, Bisim S Leaf RN (xs p) (xs p) := by
  cases h with
  | node i r xs xs hs => exact hs

end Explicit

section Legal

variable {Index : Type u} {S : Signature.{u,v,w} Index}
  {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
  {Motive : ∀ i, LegalTree S Leaf RN i → Type z}

/-- Self-bisimulation is used only to prove legality of already present
children.  The recursive data come from the supplied major tree. -/
noncomputable def legalEliminate
    (neutral : ∀ i a (ha : RN i a a), Motive i (legalNeutral S Leaf RN i a ha))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) →
      Motive i (legalNode S Leaf RN i r children))
    {i : Index} (t : LegalTree S Leaf RN i) : Motive i t :=
  eliminate (Motive := fun i t => ∀ h : Bisim S Leaf RN t t, Motive i ⟨t, h⟩)
    (fun i a h => neutral i a (bisim_neutral_self h))
    (fun i r children ih h =>
      algebra i r (fun p => ⟨children p, bisim_node_self h p⟩)
        (fun p => ih p (bisim_node_self h p))) t.1 t.2

theorem legalEliminate_neutral
    (neutral : ∀ i a (ha : RN i a a), Motive i (legalNeutral S Leaf RN i a ha))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) →
      Motive i (legalNode S Leaf RN i r children))
    (i : Index) (a : Leaf i) (ha : RN i a a) :
    legalEliminate neutral algebra (legalNeutral S Leaf RN i a ha) = neutral i a ha := rfl

theorem legalEliminate_node
    (neutral : ∀ i a (ha : RN i a a), Motive i (legalNeutral S Leaf RN i a ha))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) →
      Motive i (legalNode S Leaf RN i r children))
    (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)) :
    legalEliminate neutral algebra (legalNode S Leaf RN i r children) =
      algebra i r children (fun p => legalEliminate neutral algebra (children p)) := rfl

theorem legalEliminate_respects
    (Q : ∀ i (x y : LegalTree S Leaf RN i), Motive i x → Motive i y → Prop)
    (neutral : ∀ i a (ha : RN i a a), Motive i (legalNeutral S Leaf RN i a ha))
    (algebra : ∀ i (r : S.Rule i)
      (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)),
      (∀ p, Motive (S.child i r p) (children p)) →
      Motive i (legalNode S Leaf RN i r children))
    (hn : ∀ i a b (ha : RN i a a) (hb : RN i b b), RN i a b →
      Q i (legalNeutral S Leaf RN i a ha) (legalNeutral S Leaf RN i b hb)
        (neutral i a ha) (neutral i b hb))
    (hc : ∀ i (r : S.Rule i)
      (xs ys : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p))
      (us : ∀ p, Motive (S.child i r p) (xs p))
      (vs : ∀ p, Motive (S.child i r p) (ys p)),
      (∀ p, Bisim S Leaf RN (xs p).1 (ys p).1) →
      (∀ p, Q (S.child i r p) (xs p) (ys p) (us p) (vs p)) →
      Q i (legalNode S Leaf RN i r xs) (legalNode S Leaf RN i r ys)
        (algebra i r xs us) (algebra i r ys vs))
    {i : Index} {x y : LegalTree S Leaf RN i} (hxy : Bisim S Leaf RN x.1 y.1) :
    Q i x y (legalEliminate neutral algebra x) (legalEliminate neutral algebra y) := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change Bisim S Leaf RN x y at hxy
  induction hxy with
  | neutral i a b hab => exact hn i a b _ _ hab
  | node i r xs ys children ih =>
      exact hc i r
        (fun p => ⟨xs p, bisim_node_self hx p⟩)
        (fun p => ⟨ys p, bisim_node_self hy p⟩) _ _ children
        (fun p => ih p (bisim_node_self hx p) (bisim_node_self hy p))

end Legal

section Transport

/-- Ordinary equality transport, kept explicit at quotient boundaries. -/
def transport {A : Type a} (M : A → Type b) {x y : A} (h : x = y) (u : M x) : M y :=
  h ▸ u

theorem transport_refl {A : Type a} (M : A → Type b) {x : A} (u : M x) :
    transport M rfl u = u := rfl

theorem transport_trans {A : Type a} (M : A → Type b) {x y z : A}
    (h : x = y) (g : y = z) (u : M x) :
    transport M (h.trans g) u = transport M g (transport M h u) := by
  cases h
  cases g
  rfl

theorem transport_reverse {A : Type a} (M : A → Type b) {x y : A}
    (h : x = y) {u : M x} {v : M y} (huv : transport M h u = v) :
    transport M h.symm v = u := by
  cases h
  exact huv.symm

theorem sigma_eq_of_transport {A : Type a} (M : A → Type b) {x y : A}
    (h : x = y) {u : M x} {v : M y} (huv : transport M h u = v) :
    (⟨x, u⟩ : Sigma M) = ⟨y, v⟩ := by
  cases h
  cases huv
  rfl

/-- A dependent quotient lift constructed by first lifting a data pair.
Its first component records the quotient major. -/
def quotientLiftPair {A : Type a} (s : Setoid A) (M : Quotient s → Type b)
    (f : ∀ x : A, M (Quotient.mk s x))
    (hf : ∀ x y (h : s.r x y),
      transport M (Quotient.sound h) (f x) = f y) : Quotient s → Sigma M :=
  Quotient.lift (fun x => ⟨Quotient.mk s x, f x⟩)
    (fun x y h => sigma_eq_of_transport M (Quotient.sound h) (hf x y h))

theorem quotientLiftPair_major {A : Type a} (s : Setoid A) (M : Quotient s → Type b)
    (f : ∀ x : A, M (Quotient.mk s x))
    (hf : ∀ x y (h : s.r x y),
      transport M (Quotient.sound h) (f x) = f y) (q : Quotient s) :
    (quotientLiftPair s M f hf q).1 = q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

def dependentQuotientLift {A : Type a} (s : Setoid A) (M : Quotient s → Type b)
    (f : ∀ x : A, M (Quotient.mk s x))
    (hf : ∀ x y (h : s.r x y),
      transport M (Quotient.sound h) (f x) = f y) (q : Quotient s) : M q :=
  transport M (quotientLiftPair_major s M f hf q) (quotientLiftPair s M f hf q).2

theorem dependentQuotientLift_mk {A : Type a} (s : Setoid A) (M : Quotient s → Type b)
    (f : ∀ x : A, M (Quotient.mk s x))
    (hf : ∀ x y (h : s.r x y),
      transport M (Quotient.sound h) (f x) = f y) (x : A) :
    dependentQuotientLift s M f hf (Quotient.mk s x) = f x := rfl

end Transport

section Quotient

variable {Index : Type u} {S : Signature.{u,v,w} Index}
  {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
  (hRN : ∀ i, RelLaws (RN i))

abbrev FamilyQuotient (i : Index) := Quotient (treeSetoid S Leaf RN hRN i)

def treeClass {i : Index} (t : LegalTree S Leaf RN i) :
    FamilyQuotient (S := S) (Leaf := Leaf) hRN i :=
  Quotient.mk _ t

variable (Motive : ∀ i, FamilyQuotient (S := S) (Leaf := Leaf) hRN i → Type z)

/-- Equality after the canonical transport along the major bisimulation. -/
def FibreRelation {i : Index} (x y : LegalTree S Leaf RN i)
    (a : Motive i (treeClass hRN x)) (b : Motive i (treeClass hRN y)) : Prop :=
  ∃ h : Bisim S Leaf RN x.1 y.1,
    transport (Motive i) (Quotient.sound h) a = b

theorem fibreRelation_refl {i : Index} (x : LegalTree S Leaf RN i)
    (a : Motive i (treeClass hRN x)) : FibreRelation hRN Motive x x a a :=
  ⟨x.2, rfl⟩

theorem fibreRelation_symm {i : Index} {x y : LegalTree S Leaf RN i}
    {a : Motive i (treeClass hRN x)} {b : Motive i (treeClass hRN y)}
    (h : FibreRelation hRN Motive x y a b) : FibreRelation hRN Motive y x b a := by
  rcases h with ⟨hxy, hab⟩
  exact ⟨bisim_symm hRN hxy, transport_reverse (Motive i) (Quotient.sound hxy) hab⟩

theorem fibreRelation_trans {i : Index} {x y t : LegalTree S Leaf RN i}
    {a : Motive i (treeClass hRN x)} {b : Motive i (treeClass hRN y)}
    {c : Motive i (treeClass hRN t)}
    (h : FibreRelation hRN Motive x y a b) (g : FibreRelation hRN Motive y t b c) :
    FibreRelation hRN Motive x t a c := by
  rcases h with ⟨hxy, hab⟩
  rcases g with ⟨hyt, hbc⟩
  refine ⟨bisim_trans hRN hxy hyt, ?_⟩
  exact (transport_trans (Motive i) (Quotient.sound hxy) (Quotient.sound hyt) a).trans
    ((congrArg (transport (Motive i) (Quotient.sound hyt)) hab).trans hbc)

/-- The dependent fibres form a lawful relation on explicit total pairs. -/
theorem fibreRelation_laws (i : Index) :
    RelLaws (fun x y : Sigma (fun t : LegalTree S Leaf RN i => Motive i (treeClass hRN t)) =>
      FibreRelation hRN Motive x.1 y.1 x.2 y.2) where
  symm := fibreRelation_symm hRN Motive
  trans := fibreRelation_trans hRN Motive

variable
  (neutral : ∀ i a (ha : RN i a a),
    Motive i (treeClass hRN (legalNeutral S Leaf RN i a ha)))
  (algebra : ∀ i (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)),
    (∀ p, Motive (S.child i r p) (treeClass hRN (children p))) →
    Motive i (treeClass hRN (legalNode S Leaf RN i r children)))
  (hn : ∀ i a b (ha : RN i a a) (hb : RN i b b), RN i a b →
    FibreRelation hRN Motive (legalNeutral S Leaf RN i a ha) (legalNeutral S Leaf RN i b hb)
      (neutral i a ha) (neutral i b hb))
  (hc : ∀ i (r : S.Rule i)
    (xs ys : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p))
    (us : ∀ p, Motive (S.child i r p) (treeClass hRN (xs p)))
    (vs : ∀ p, Motive (S.child i r p) (treeClass hRN (ys p))),
    (∀ p, Bisim S Leaf RN (xs p).1 (ys p).1) →
    (∀ p, FibreRelation hRN Motive (xs p) (ys p) (us p) (vs p)) →
    FibreRelation hRN Motive (legalNode S Leaf RN i r xs) (legalNode S Leaf RN i r ys)
      (algebra i r xs us) (algebra i r ys vs))

include hn hc in
theorem quotient_eliminate_transport {i : Index} {x y : LegalTree S Leaf RN i}
    (hxy : Bisim S Leaf RN x.1 y.1) :
    transport (Motive i) (Quotient.sound hxy)
      (legalEliminate (Motive := fun i t => Motive i (treeClass hRN t)) neutral algebra x) =
      legalEliminate (Motive := fun i t => Motive i (treeClass hRN t)) neutral algebra y := by
  obtain ⟨_, h⟩ := legalEliminate_respects
    (Motive := fun i t => Motive i (treeClass hRN t)) (fun _ => FibreRelation hRN Motive)
    neutral algebra hn hc hxy
  exact h

/-- The data-valued major-dependent eliminator descends to its legal-tree
quotient.  The lift retains the quotient major in its result pair. -/
noncomputable def quotientEliminate {i : Index}
    (q : FamilyQuotient (S := S) (Leaf := Leaf) hRN i) : Motive i q :=
  dependentQuotientLift (treeSetoid S Leaf RN hRN i) (Motive i)
    (legalEliminate (Motive := fun i t => Motive i (treeClass hRN t)) neutral algebra)
    (fun _ _ h => quotient_eliminate_transport hRN Motive neutral algebra hn hc h) q

theorem quotientEliminate_mk {i : Index} (t : LegalTree S Leaf RN i) :
    quotientEliminate hRN Motive neutral algebra hn hc (treeClass hRN t) =
      legalEliminate (Motive := fun i t => Motive i (treeClass hRN t)) neutral algebra t := rfl

theorem quotientEliminate_neutral (i : Index) (a : Leaf i) (ha : RN i a a) :
    quotientEliminate hRN Motive neutral algebra hn hc
      (treeClass hRN (legalNeutral S Leaf RN i a ha)) = neutral i a ha := rfl

theorem quotientEliminate_node (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)) :
    quotientEliminate hRN Motive neutral algebra hn hc
      (treeClass hRN (legalNode S Leaf RN i r children)) =
      algebra i r children (fun p =>
        quotientEliminate hRN Motive neutral algebra hn hc (treeClass hRN (children p))) := rfl

/-- The semantic value and the major tree stay together.  The eliminator
reads the explicit tree field, never a membership existential. -/
noncomputable def pairedEliminate
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    Motive i (pairedClass hRN p) :=
  legalEliminate (Motive := fun i t => Motive i (treeClass hRN t))
    neutral algebra ⟨p.tree, p.admitted⟩

theorem pairedEliminate_factors
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    quotientEliminate hRN Motive neutral algebra hn hc (pairedClass hRN p) =
      pairedEliminate hRN Motive neutral algebra p := rfl

include hn hc in
theorem pairedEliminate_transport
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {i : Index} {p q : Paired S Leaf RN leafValue ctor i} (hpq : PairPER p q) :
    transport (Motive i) (Quotient.sound hpq) (pairedEliminate hRN Motive neutral algebra p) =
      pairedEliminate hRN Motive neutral algebra q :=
  quotient_eliminate_transport hRN Motive neutral algebra hn hc
    (x := ⟨p.tree, p.admitted⟩) (y := ⟨q.tree, q.admitted⟩)
    (show Bisim S Leaf RN p.tree q.tree from hpq)

end Quotient

section ValueMotive

variable {Index : Type u} {S : Signature.{u,v,w} Index}
  {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}

/-- The raw carrier can remain `Value` while its result PER depends on
the entire major.  Related majors supply the required fibre transport. -/
def ValueMotiveCoherent (C : ∀ i, Tree S Leaf i → TypedPER.Relation) : Prop :=
  ∀ i (x y : Tree S Leaf i), Bisim S Leaf RN x y → TypedPER.Same (C i x) (C i y)

theorem valueMotive_resultLaws (hRN : ∀ i, RelLaws (RN i))
    (C : ∀ i, Tree S Leaf i → TypedPER.Relation)
    (hC : ∀ i (t : Tree S Leaf i), Bisim S Leaf RN t t → TypedPER.Laws (C i t))
    (hcoh : ValueMotiveCoherent (RN := RN) C) :
    ResultLaws (RN := RN) (Motive := fun _ _ => Value) (fun i x _ a b => C i x a b) where
  symm := by
    intro i x y a b hxy hab
    have hx := bisim_trans hRN hxy (bisim_symm hRN hxy)
    exact (hcoh i x y hxy b a).mp ((hC i x hx).symm hab)
  trans := by
    intro i x y t a b c hxy hyt hab hbc
    have hx := bisim_trans hRN hxy (bisim_symm hRN hxy)
    exact (hC i x hx).trans hab ((hcoh i x y hxy b c).mpr hbc)

theorem valueEliminate_related
    (C : ∀ i, Tree S Leaf i → TypedPER.Relation)
    (neutral : ∀ i, Leaf i → Value)
    (algebra : ∀ i (r : S.Rule i),
      (∀ p : S.Premise i r, Tree S Leaf (S.child i r p)) →
      (S.Premise i r → Value) → Value)
    (hn : ∀ i a b, RN i a b → C i (.neutral i a) (neutral i a) (neutral i b))
    (hc : ∀ i (r : S.Rule i)
      (xs ys : ∀ p : S.Premise i r, Tree S Leaf (S.child i r p))
      (us vs : S.Premise i r → Value),
      (∀ p, Bisim S Leaf RN (xs p) (ys p)) →
      (∀ p, C (S.child i r p) (xs p) (us p) (vs p)) →
      C i (.node i r xs) (algebra i r xs us) (algebra i r ys vs))
    {i : Index} {x y : Tree S Leaf i} (hxy : Bisim S Leaf RN x y) :
    C i x (eliminate (Motive := fun _ _ => Value) neutral algebra x)
      (eliminate (Motive := fun _ _ => Value) neutral algebra y) :=
  eliminate_respects (Motive := fun _ _ => Value)
    (fun i x _ a b => C i x a b) neutral algebra hn hc hxy

end ValueMotive

section MajorControl

/-- A concrete major-dependent result type: its cardinality changes from
one to two when a constructor is added to the neutral major. -/
noncomputable def loopDepth {i : Unit} (t : Tree loopSignature (fun _ => Unit) i) : Nat :=
  NeutralDataFamily.fold (fun _ _ => 0) (fun _ _ children => children () + 1) t

noncomputable def loopPosition {i : Unit} (t : Tree loopSignature (fun _ => Unit) i) :
    Fin (loopDepth t + 1) :=
  eliminate (Motive := fun _ t => Fin (loopDepth t + 1))
    (fun _ _ => ⟨0, Nat.zero_lt_succ 0⟩)
    (fun _ _ _ ih => (ih ()).succ) t

theorem loopPosition_neutral (i : Unit) (a : Unit) :
    (loopPosition (Tree.neutral (S := loopSignature) (Leaf := fun _ => Unit) i a)).val = 0 := rfl

theorem loopPosition_node (i : Unit) (r : loopSignature.Rule i)
    (children : ∀ p : loopSignature.Premise i r,
      Tree loopSignature (fun _ => Unit) (loopSignature.child i r p)) :
    (loopPosition (Tree.node i r children)).val = (loopPosition (children ())).val + 1 := rfl

theorem transport_fin_val {A : Type a} (bound : A → Nat) {x y : A}
    (h : x = y) (u : Fin (bound x)) :
    (transport (fun x => Fin (bound x)) h u).val = u.val := by
  cases h
  rfl

def loopLeafRelation (_i : Unit) (a b : Unit) : Prop := a = b

theorem loopLeafRelation_laws (i : Unit) : RelLaws (loopLeafRelation i) where
  symm := Eq.symm
  trans := Eq.trans

abbrev LoopLegal (i : Unit) :=
  LegalTree loopSignature (fun _ => Unit) loopLeafRelation i

abbrev LoopQuotient (i : Unit) :=
  FamilyQuotient (S := loopSignature) (Leaf := fun _ => Unit) loopLeafRelation_laws i

noncomputable def loopQuotientDepth {i : Unit} (q : LoopQuotient i) : Nat :=
  NeutralDataFamily.quotientFold (Result := fun _ => Nat) loopLeafRelation_laws
    (fun _ _ => 0) (fun _ _ children => children () + 1) (fun _ _ _ _ => rfl) q

noncomputable def LoopMotive (i : Unit) (q : LoopQuotient i) : Type :=
  Fin (loopQuotientDepth q + 1)

noncomputable def loopNeutralResult (i : Unit) (a : Unit)
    (ha : loopLeafRelation i a a) :
    LoopMotive i (treeClass loopLeafRelation_laws
      (legalNeutral loopSignature (fun _ => Unit) loopLeafRelation i a ha)) :=
  ⟨0, Nat.zero_lt_succ 0⟩

noncomputable def loopNodeResult (i : Unit) (r : loopSignature.Rule i)
    (children : ∀ p : loopSignature.Premise i r, LoopLegal (loopSignature.child i r p))
    (results : ∀ p, LoopMotive (loopSignature.child i r p)
      (treeClass loopLeafRelation_laws (children p))) :
    LoopMotive i (treeClass loopLeafRelation_laws
      (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r children)) :=
  (results ()).succ

theorem loopNeutralResult_respects (i : Unit) (a b : Unit)
    (ha : loopLeafRelation i a a) (hb : loopLeafRelation i b b)
    (hab : loopLeafRelation i a b) :
    FibreRelation loopLeafRelation_laws LoopMotive
      (legalNeutral loopSignature (fun _ => Unit) loopLeafRelation i a ha)
      (legalNeutral loopSignature (fun _ => Unit) loopLeafRelation i b hb)
      (loopNeutralResult i a ha) (loopNeutralResult i b hb) := by
  have related : Bisim loopSignature (fun _ => Unit) loopLeafRelation
      (Tree.neutral (S := loopSignature) (Leaf := fun _ => Unit) i a)
      (Tree.neutral (S := loopSignature) (Leaf := fun _ => Unit) i b) :=
    @Bisim.neutral Unit loopSignature (fun _ => Unit) loopLeafRelation i a b hab
  have classEq :
      treeClass loopLeafRelation_laws
        (legalNeutral loopSignature (fun _ => Unit) loopLeafRelation i a ha) =
      treeClass loopLeafRelation_laws
        (legalNeutral loopSignature (fun _ => Unit) loopLeafRelation i b hb) :=
    Quotient.sound related
  refine ⟨related, Fin.ext ?_⟩
  exact transport_fin_val (fun q : LoopQuotient i => loopQuotientDepth q + 1)
    classEq (loopNeutralResult i a ha)

theorem loopNodeResult_respects (i : Unit) (r : loopSignature.Rule i)
    (xs ys : ∀ p : loopSignature.Premise i r, LoopLegal (loopSignature.child i r p))
    (us : ∀ p, LoopMotive (loopSignature.child i r p) (treeClass loopLeafRelation_laws (xs p)))
    (vs : ∀ p, LoopMotive (loopSignature.child i r p) (treeClass loopLeafRelation_laws (ys p)))
    (hchildren : ∀ p, Bisim loopSignature (fun _ => Unit) loopLeafRelation (xs p).1 (ys p).1)
    (hresults : ∀ p, FibreRelation loopLeafRelation_laws LoopMotive (xs p) (ys p) (us p) (vs p)) :
    FibreRelation loopLeafRelation_laws LoopMotive
      (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r xs)
      (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r ys)
      (loopNodeResult i r xs us) (loopNodeResult i r ys vs) := by
  have related : Bisim loopSignature (fun _ => Unit) loopLeafRelation
      (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r xs).1
      (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r ys).1 :=
    .node i r (fun p => (xs p).1) (fun p => (ys p).1) hchildren
  have classEq :
      treeClass loopLeafRelation_laws
        (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r xs) =
      treeClass loopLeafRelation_laws
        (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r ys) :=
    Quotient.sound related
  obtain ⟨childRelated, childTransport⟩ := hresults ()
  have childEq : treeClass loopLeafRelation_laws (xs ()) =
      treeClass loopLeafRelation_laws (ys ()) := Quotient.sound childRelated
  have childVals : (us ()).val = (vs ()).val :=
    (transport_fin_val (fun q : LoopQuotient () => loopQuotientDepth q + 1)
      childEq (us ())).symm.trans (congrArg Fin.val childTransport)
  refine ⟨related, Fin.ext ?_⟩
  exact (transport_fin_val (fun q : LoopQuotient i => loopQuotientDepth q + 1)
    classEq (loopNodeResult i r xs us)).trans (congrArg Nat.succ childVals)

/-- Every operation and compatibility premise of the quotient eliminator
is constructed for this motive.  Its fibres vary with the quotient major. -/
noncomputable def loopQuotientPosition {i : Unit} (q : LoopQuotient i) : LoopMotive i q :=
  quotientEliminate loopLeafRelation_laws LoopMotive loopNeutralResult loopNodeResult
    loopNeutralResult_respects loopNodeResult_respects q

theorem loopQuotientPosition_neutral (i : Unit) (a : Unit)
    (ha : loopLeafRelation i a a) :
    (loopQuotientPosition (treeClass loopLeafRelation_laws
      (legalNeutral loopSignature (fun _ => Unit) loopLeafRelation i a ha))).val = 0 := rfl

theorem loopQuotientPosition_node (i : Unit) (r : loopSignature.Rule i)
    (children : ∀ p : loopSignature.Premise i r, LoopLegal (loopSignature.child i r p)) :
    (loopQuotientPosition (treeClass loopLeafRelation_laws
      (legalNode loopSignature (fun _ => Unit) loopLeafRelation i r children))).val =
      (loopQuotientPosition (treeClass loopLeafRelation_laws (children ()))).val + 1 := rfl

def loopLegalNeutral : LoopLegal () :=
  legalNeutral loopSignature (fun _ => Unit) loopLeafRelation () () rfl

def loopLegalConstructor : LoopLegal () :=
  legalNode loopSignature (fun _ => Unit) loopLeafRelation () () (fun _ => loopLegalNeutral)

/-- An inhabited neutral major and an inhabited constructor major exercise
the actual dependent quotient eliminator, with fibres `Fin 1` and `Fin 2`. -/
theorem loopQuotient_control :
    loopQuotientDepth (treeClass loopLeafRelation_laws loopLegalNeutral) = 0 ∧
    loopQuotientDepth (treeClass loopLeafRelation_laws loopLegalConstructor) = 1 ∧
    (loopQuotientPosition (treeClass loopLeafRelation_laws loopLegalNeutral)).val = 0 ∧
    (loopQuotientPosition (treeClass loopLeafRelation_laws loopLegalConstructor)).val = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

end MajorControl

end Rcic.Declarative.Ann.LR3.DependentFamily
