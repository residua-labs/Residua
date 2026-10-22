import rcic.RcicAnnLR3TypedInductive

/-!
# Neutral extensions on the existing semantic carrier

An explicit semantic predicate supplies the extra proof inhabitants.  The
canonical branch still requires truth and the old nonbottom unit class;
the neutral branch does not assert truth.  Proof irrelevance is the product
of these memberships, so it relates neutral and canonical inhabitants
without identifying their underlying observations by `ValueEq`.

The construction uses `UnitModel.Value` throughout.  It neither constructs
a universe decoder nor proves a source fundamental theorem.  In particular,
neutral membership alone gives no exact universe membership.  Inserting a
neutral into the unchanged `TypedPER.SortPER` requires `SortMember` and
`TypeDefined`, and a single such value cannot have two distinct indices.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.NeutralPER
open UnitModel TypedPER TypedInductive
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
universe u v w

abbrev NeutralPredicate := Value → Prop

/-- Optional stability under equality of the existing finitary observations.
The PER laws themselves do not require a decision procedure for neutrals. -/
def ExtensionalNeutral (N : NeutralPredicate) : Prop :=
  ∀ {x y : Value}, ValueEq x y → (N x ↔ N y)

def ProofMember (N : NeutralPredicate) (truth : Prop) (x : Value) : Prop :=
  (truth ∧ UnitModel.ProofMember EnvI.bot x) ∨ N x

def ProofPER (N : NeutralPredicate) (truth : Prop) (x y : Value) : Prop :=
  ProofMember N truth x ∧ ProofMember N truth y

theorem proofPER_laws (N : NeutralPredicate) (truth : Prop) :
    Laws (ProofPER N truth) where
  symm := fun h => ⟨h.2, h.1⟩
  trans := fun h g => ⟨h.1, g.2⟩

theorem proofPER_member_iff (N : NeutralPredicate) (truth : Prop) (x : Value) :
    Member (ProofPER N truth) x ↔ ProofMember N truth x :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem proofMember_of_truth {N : NeutralPredicate} {truth : Prop} {x : Value}
    (ht : truth) (hx : UnitModel.ProofMember EnvI.bot x) : ProofMember N truth x :=
  Or.inl ⟨ht, hx⟩

theorem proofMember_of_neutral {N : NeutralPredicate} {truth : Prop} {x : Value}
    (hx : N x) : ProofMember N truth x := Or.inr hx

theorem unit_member_of_truth (N : NeutralPredicate) {truth : Prop} (ht : truth) :
    Member (ProofPER N truth) (unitValue EnvI.bot) :=
  ⟨Or.inl ⟨ht, unit_member _⟩, Or.inl ⟨ht, unit_member _⟩⟩

theorem neutral_member (N : NeutralPredicate) (truth : Prop) {x : Value} (hx : N x) :
    Member (ProofPER N truth) x := ⟨Or.inr hx, Or.inr hx⟩

theorem proofPER_irrelevant {N : NeutralPredicate} {truth : Prop} {x y : Value}
    (hx : Member (ProofPER N truth) x) (hy : Member (ProofPER N truth) y) :
    ProofPER N truth x y := ⟨hx.1, hy.1⟩

/-- Existing truth-valued proof relations embed without changing them. -/
theorem old_truthPER_included {N : NeutralPredicate} {truth : Prop} {x y : Value}
    (h : TypedPER.TruthPER truth x y) : ProofPER N truth x y :=
  ⟨Or.inl ⟨h.1, h.2.1⟩, Or.inl ⟨h.1, h.2.2⟩⟩

theorem no_neutrals_recovers_truthPER (truth : Prop) :
    Same (ProofPER (fun _ => False) truth) (TypedPER.TruthPER truth) := by
  intro x y
  constructor
  · intro h
    rcases h.1 with hx | hx
    · rcases h.2 with hy | hy
      · exact ⟨hx.1, hx.2, hy.2⟩
      · exact hy.elim
    · exact hx.elim
  · exact old_truthPER_included

theorem false_member_iff (N : NeutralPredicate) (x : Value) :
    Member (ProofPER N False) x ↔ N x := by
  constructor
  · intro h
    rcases h.1 with h | h
    · exact h.1.elim
    · exact h
  · exact neutral_member N False

theorem falsePER_iff (N : NeutralPredicate) (x y : Value) :
    ProofPER N False x y ↔ N x ∧ N y := by
  constructor
  · intro h
    exact ⟨(false_member_iff N x).mp ⟨h.1, h.1⟩,
      (false_member_iff N y).mp ⟨h.2, h.2⟩⟩
  · intro h
    exact ⟨Or.inr h.1, Or.inr h.2⟩

theorem member_of_false_truth_iff (N : NeutralPredicate) {truth : Prop}
    (ht : ¬ truth) (x : Value) : Member (ProofPER N truth) x ↔ N x := by
  constructor
  · intro h
    rcases h.1 with h | h
    · exact (ht h.1).elim
    · exact h
  · exact neutral_member N truth

theorem nonneutral_member_truth {N : NeutralPredicate} {truth : Prop} {x : Value}
    (hx : Member (ProofPER N truth) x) (hn : ¬ N x) : truth := by
  rcases hx.1 with h | h
  · exact h.1
  · exact (hn h).elim

/-- Neutral inhabitance replaces the old truth-only inhabitance equivalence. -/
theorem proofPER_inhabited_iff (N : NeutralPredicate) (truth : Prop) :
    (∃ x : Value, Member (ProofPER N truth) x) ↔ truth ∨ ∃ x : Value, N x := by
  constructor
  · rintro ⟨x, hx⟩
    rcases hx.1 with h | h
    · exact Or.inl h.1
    · exact Or.inr ⟨x, h⟩
  · intro h
    rcases h with ht | ⟨x, hx⟩
    · exact ⟨unitValue EnvI.bot, unit_member_of_truth N ht⟩
    · exact ⟨x, neutral_member N truth hx⟩

theorem proofMember_value_congr {N : NeutralPredicate} (hN : ExtensionalNeutral N)
    {truth : Prop} {x y : Value} (hxy : ValueEq x y) :
    ProofMember N truth x ↔ ProofMember N truth y := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨h.1, hxy.symm.trans h.2⟩
    · exact Or.inr ((hN hxy).mp h)
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨h.1, hxy.trans h.2⟩
    · exact Or.inr ((hN hxy).mpr h)

theorem proofMember_parameters_iff {N M : NeutralPredicate} {truth other : Prop}
    (ht : truth ↔ other) (hN : ∀ x, N x ↔ M x) (x : Value) :
    ProofMember N truth x ↔ ProofMember M other x := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨ht.mp h.1, h.2⟩
    · exact Or.inr ((hN x).mp h)
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨ht.mpr h.1, h.2⟩
    · exact Or.inr ((hN x).mpr h)

theorem proofPER_same {N M : NeutralPredicate} {truth other : Prop}
    (ht : truth ↔ other) (hN : ∀ x, N x ↔ M x) :
    Same (ProofPER N truth) (ProofPER M other) := by
  intro x y
  exact ⟨fun h => ⟨(proofMember_parameters_iff ht hN x).mp h.1,
    (proofMember_parameters_iff ht hN y).mp h.2⟩,
    fun h => ⟨(proofMember_parameters_iff ht hN x).mpr h.1,
      (proofMember_parameters_iff ht hN y).mpr h.2⟩⟩

def EqPER (N : NeutralPredicate) (R : Relation) (a b : Value) : Relation :=
  ProofPER N (R a b)

theorem eqPER_laws (N : NeutralPredicate) (R : Relation) (a b : Value) :
    Laws (EqPER N R a b) := proofPER_laws N (R a b)

theorem eqPER_inhabited_iff (N : NeutralPredicate) (R : Relation) (a b : Value) :
    (∃ p : Value, Member (EqPER N R a b) p) ↔ R a b ∨ ∃ p : Value, N p :=
  proofPER_inhabited_iff N (R a b)

theorem eqPER_refl (N : NeutralPredicate) {R : Relation} {a : Value}
    (ha : Member R a) : Member (EqPER N R a a) (unitValue EnvI.bot) :=
  unit_member_of_truth N ha

theorem eqPER_neutral (N : NeutralPredicate) (R : Relation) (a b : Value)
    {p : Value} (hp : N p) : Member (EqPER N R a b) p :=
  neutral_member N (R a b) hp

theorem false_eqPER_member_iff (N : NeutralPredicate) {R : Relation} {a b : Value}
    (hab : ¬ R a b) (p : Value) : Member (EqPER N R a b) p ↔ N p :=
  member_of_false_truth_iff N hab p

/-- The original positive least closure supplies truth; no constructor
evidence is selected from a neutral proof. -/
def FamilyPER {Index : Type u} (N : NeutralPredicate)
    (S : Signature.{u,v,w} Index) (i : Index) : Relation :=
  ProofPER N (Closure S i)

theorem familyPER_laws {Index : Type u} (N : NeutralPredicate)
    (S : Signature.{u,v,w} Index) (i : Index) : Laws (FamilyPER N S i) :=
  proofPER_laws N (Closure S i)

theorem familyPER_inhabited_iff {Index : Type u} (N : NeutralPredicate)
    (S : Signature.{u,v,w} Index) (i : Index) :
    (∃ p : Value, Member (FamilyPER N S i) p) ↔ Closure S i ∨ ∃ p : Value, N p :=
  proofPER_inhabited_iff N (Closure S i)

theorem familyPER_of_closure {Index : Type u} (N : NeutralPredicate)
    {S : Signature.{u,v,w} Index} {i : Index} (hi : Closure S i) :
    Member (FamilyPER N S i) (unitValue EnvI.bot) := unit_member_of_truth N hi

theorem familyPER_constructor {Index : Type u} (N : NeutralPredicate)
    {S : Signature.{u,v,w} Index} (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Closure S (S.child i r p)) :
    Member (FamilyPER N S i) (unitValue EnvI.bot) :=
  familyPER_of_closure N (.node i r children)

theorem familyPER_neutral {Index : Type u} (N : NeutralPredicate)
    (S : Signature.{u,v,w} Index) (i : Index) {p : Value} (hp : N p) :
    Member (FamilyPER N S i) p := neutral_member N (Closure S i) hp

theorem false_familyPER_member_iff {Index : Type u} (N : NeutralPredicate)
    {S : Signature.{u,v,w} Index} {i : Index} (hi : ¬ Closure S i) (p : Value) :
    Member (FamilyPER N S i) p ↔ N p := member_of_false_truth_iff N hi p

/-- `Dext` and `Cext` are the chosen extended relations.  The function
relation tests only their admitted arguments, using the inherited theorem. -/
def FunctionPER (app : Value → Value → Value) (Dext : Relation)
    (Cext : Value → Relation) : Relation := TypedPER.FunctionPER app Dext Cext

theorem functionPER_laws (app : Value → Value → Value) (Dext : Relation)
    (Cext : Value → Relation) (hDext : Laws Dext)
    (hCext : ∀ x, Member Dext x → Laws (Cext x))
    (hcExt : FamilyCoherent Dext Cext) : Laws (FunctionPER app Dext Cext) :=
  TypedPER.functionPER_laws app hDext hCext hcExt

/-- A concrete specialization extends both the domain and each codomain. -/
def ProofFunctionPER (app : Value → Value → Value)
    (domainNeutral : NeutralPredicate) (domainTruth : Prop)
    (codomainNeutral : Value → NeutralPredicate) (codomainTruth : Value → Prop) : Relation :=
  FunctionPER app (ProofPER domainNeutral domainTruth)
    (fun x => ProofPER (codomainNeutral x) (codomainTruth x))

theorem proofFunctionPER_laws (app : Value → Value → Value)
    (domainNeutral : NeutralPredicate) (domainTruth : Prop)
    (codomainNeutral : Value → NeutralPredicate) (codomainTruth : Value → Prop)
    (hcExt : FamilyCoherent (ProofPER domainNeutral domainTruth)
      (fun x => ProofPER (codomainNeutral x) (codomainTruth x))) :
    Laws (ProofFunctionPER app domainNeutral domainTruth codomainNeutral codomainTruth) :=
  functionPER_laws app (ProofPER domainNeutral domainTruth)
    (fun x => ProofPER (codomainNeutral x) (codomainTruth x))
    (proofPER_laws domainNeutral domainTruth)
    (fun x _ => proofPER_laws (codomainNeutral x) (codomainTruth x)) hcExt

theorem proofFamily_coherent {Dext : Relation}
    {N : Value → NeutralPredicate} {truth : Value → Prop}
    (ht : ∀ x y, Dext x y → (truth x ↔ truth y))
    (hN : ∀ x y, Dext x y → ∀ p, N x p ↔ N y p) :
    FamilyCoherent Dext (fun x => ProofPER (N x) (truth x)) :=
  fun x y hxy => proofPER_same (ht x y hxy) (hN x y hxy)

theorem proofFunctionPER_apply {app : Value → Value → Value}
    {domainNeutral : NeutralPredicate} {domainTruth : Prop}
    {codomainNeutral : Value → NeutralPredicate} {codomainTruth : Value → Prop}
    {f g x y : Value}
    (hfg : ProofFunctionPER app domainNeutral domainTruth codomainNeutral codomainTruth f g)
    (hx : ProofMember domainNeutral domainTruth x)
    (hy : ProofMember domainNeutral domainTruth y) :
    ProofPER (codomainNeutral x) (codomainTruth x) (app f x) (app g y) :=
  hfg x y ⟨hx, hy⟩

/-- These are the precise extra obligations for a universe-neutral value.
They are not consequences of `N x` or of extended proof membership. -/
def ExactNeutral (N : NeutralPredicate) (k : Option Nat) (x : Value) : Prop :=
  N x ∧ SortMember k x ∧ TypeDefined x

theorem exactNeutral_sort_member {N : NeutralPredicate} {k : Option Nat} {x : Value}
    (hx : ExactNeutral N k x) : Member (TypedPER.SortPER k) x :=
  (sortPER_member_iff k x).mpr ⟨hx.2.1, hx.2.2⟩

theorem insert_neutral_sort {N : NeutralPredicate} {k : Option Nat} {x : Value}
    (hn : N x) (hs : SortMember k x) (hd : TypeDefined x) :
    Member (TypedPER.SortPER k) x := exactNeutral_sort_member ⟨hn, hs, hd⟩

theorem exactNeutral_iff {N : NeutralPredicate} {k : Option Nat} {x : Value} :
    ExactNeutral N k x ↔ N x ∧ Member (TypedPER.SortPER k) x :=
  ⟨fun h => ⟨h.1, exactNeutral_sort_member h⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

theorem exactNeutral_value_congr {N : NeutralPredicate} (hN : ExtensionalNeutral N)
    {k : Option Nat} {x y : Value} (hxy : ValueEq x y) (hx : ExactNeutral N k x) :
    ExactNeutral N k y :=
  ⟨(hN hxy).mp hx.1, sortMember_congr hxy hx.2.1,
    typeDefined_congr hxy hx.2.2⟩

theorem exactNeutral_indices_unique {N : NeutralPredicate} {i j : Option Nat} {x : Value}
    (hi : ExactNeutral N i x) (hj : ExactNeutral N j x) : i = j :=
  sortPER_indices_unique (exactNeutral_sort_member hi) (exactNeutral_sort_member hj)

theorem exactNeutral_distinct_indices_impossible {N : NeutralPredicate}
    {i j : Option Nat} {x : Value} (hij : i ≠ j)
    (hi : ExactNeutral N i x) (hj : ExactNeutral N j x) : False :=
  hij (exactNeutral_indices_unique hi hj)

/-- The obstruction already holds for any value in the unchanged exact PERs. -/
theorem neutral_not_two_exact_sorts {N : NeutralPredicate} {i j : Option Nat} {x : Value}
    (_hn : N x) (hij : i ≠ j) (hi : Member (TypedPER.SortPER i) x) :
    ¬ Member (TypedPER.SortPER j) x :=
  fun hj => hij (sortPER_indices_unique hi hj)

/-- An actual target constant on the inherited carrier.  This does not
assert that every source neutral has this interpretation. -/
def neutralAtom (r : Nat) : Value := denI EnvI.bot (.const r [])

def AtomNeutral (r : Nat) (x : Value) : Prop := ValueEq x (neutralAtom r)

theorem neutralAtom_is_neutral (r : Nat) : AtomNeutral r (neutralAtom r) := ValueEq.refl _

theorem atomNeutral_inhabited (r : Nat) : ∃ x : Value, AtomNeutral r x :=
  ⟨neutralAtom r, neutralAtom_is_neutral r⟩

theorem atomNeutral_extensional (r : Nat) : ExtensionalNeutral (AtomNeutral r) :=
  fun hxy => ⟨fun hx => hxy.symm.trans hx, fun hy => hxy.trans hy⟩

theorem neutralAtom_observed (r : Nat) : neutralAtom r (.spine r []) :=
  ApproxI.const EnvI.bot r []

theorem neutralAtom_nonbottom (r : Nat) : ¬ ValueEq (neutralAtom r) bottom := by
  intro h
  have hb := (h (.spine r [])).mp (neutralAtom_observed r)
  cases hb

theorem neutralAtom_not_unit (r : Nat) :
    ¬ ValueEq (neutralAtom r) (unitValue EnvI.bot) := by
  intro h
  have hu := (h unitProbe).mpr (unit_observed EnvI.bot)
  rcases approxI_const_inv hu with hb | hs
  · cases hb
  · cases hs

theorem unit_not_atomNeutral (r : Nat) : ¬ AtomNeutral r (unitValue EnvI.bot) :=
  fun h => neutralAtom_not_unit r h.symm

theorem neutralAtom_not_sort_member (r : Nat) (k : Option Nat) :
    ¬ SortMember k (neutralAtom r) := by
  intro hs
  have ht := hs _ (neutralAtom_observed r)
  cases ht

theorem atomNeutral_not_exact_sort {r : Nat} {x : Value} (hx : AtomNeutral r x)
    (k : Option Nat) : ¬ Member (TypedPER.SortPER k) x := by
  intro hs
  exact neutralAtom_not_sort_member r k (sortMember_congr hx hs.1)

/-- A unit-only projection needs a new neutral case.  The old theorem
remains valid for its old carrier, but cannot be lifted by inclusion alone. -/
theorem proofProject_not_sound_on_false_neutrals (r : Nat) :
    ¬ (∀ x : Value, Member (ProofPER (AtomNeutral r) False) x →
      Member (ProofPER (AtomNeutral r) False) (TypedPER.proofProject x)) := by
  intro h
  have hm := h (neutralAtom r)
    (neutral_member (AtomNeutral r) False (neutralAtom_is_neutral r))
  exact unit_not_atomNeutral r ((false_member_iff (AtomNeutral r) _).mp hm)

end Rcic.Declarative.Ann.LR3.NeutralPER
