import rcic.RcicAnnLR3CandidateCompletion
import rcic.RcicAnnLR3NeutralPi
import rcic.RcicAnnLR3NeutralDataFamily
import rcic.RcicAnnLR3EnvironmentEval

/-!
# Proof-valued products over retained semantic arguments

The domain of this function PER is an explicit semantic carrier. Its
elements need not be determined by their raw realizers. In particular,
two proposition arguments with the same raw value retain different
candidate relations and hence different result fibres.

Every subsingleton candidate has a constructive completion by atoms and
actual native applications to nonempty raw arguments. Nonemptiness is
supplied for candidate-bearing type arguments by their definedness, and
for actual evaluator images by their bottom observation. The restriction
does not force bottom into candidates: these neutrals always have a
spine observation. No normalization or choice is used.

The concrete product quantifies over every candidate-bearing proposition
argument. Its neutral function membership and application law are
supplied, not fields assumed of the product. This is a proof-valued
product producer; universe-valued functions, complete source semantics,
source substitution and the full universe hierarchy remain open.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.CandidatePi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open CandidateUniverse (Candidate predicateCandidate candidate_iff_members)

universe u

def NonemptyValue (x : Value) : Prop := ∃ c : CptI, x c

theorem nonempty_of_bot {x : Value} (h : x .bot) : NonemptyValue x := ⟨.bot, h⟩

theorem typeDefined_nonempty {x : Value} (h : TypeDefined x) : NonemptyValue x := by
  obtain ⟨i, payload, hx⟩ := h
  exact ⟨.spine 10 [.spine (levelRef i) [], payload], hx⟩

theorem denI_nonempty (ρ : EnvI) (t : Expr Nat) : NonemptyValue (denI ρ t) :=
  nonempty_of_bot (.bot ρ t)

theorem environment_denote_nonempty (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (t : ExprA) :
    NonemptyValue (EnvironmentEval.denote E F ν ρ t) :=
  nonempty_of_bot (EnvironmentEval.denote_bot E F ν ρ t)

/-- Positive application closure with retained spine observations. An
empty raw argument is excluded explicitly, rather than silently adding
bottom as a proof of every proposition. -/
inductive Neutral : Value → Prop
  | atom (name : Nat) : Neutral (NeutralPER.neutralAtom name)
  | app {f : Value} (hf : Neutral f) (a : Value) (ha : NonemptyValue a) :
      Neutral (NeutralPi.applyValue f a)

theorem neutral_congr {x y : Value} (h : ValueEq x y) (hx : Neutral x) : Neutral y := by
  rw [← NeutralCodes.valueEq_eq h]
  exact hx

theorem atomNeutral_neutral {name : Nat} {x : Value}
    (h : NeutralPER.AtomNeutral name x) : Neutral x :=
  neutral_congr h.symm (.atom name)

theorem old_neutral_included {x : Value} (h : NeutralCodes.Neutral x) : Neutral x := by
  obtain ⟨name, hx⟩ := h
  exact atomNeutral_neutral hx

def SpineOnly (x : Value) : Prop :=
  ∀ c : CptI, x c → c = .bot ∨ ∃ (name : Nat) (args : List CptI), c = .spine name args

theorem neutral_spineOnly {x : Value} (hx : Neutral x) : SpineOnly x := by
  induction hx with
  | atom name =>
      intro c hc
      rcases approxI_const_inv hc with h | h
      · exact Or.inl h
      · exact Or.inr ⟨name, [], h⟩
  | @app f hf a ha ih =>
      intro c hc
      rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ | ⟨name, args, z, hc, hf, ha⟩
      · exact Or.inl hc
      · rcases ih (.lam g) hf with h | ⟨name, args, h⟩ <;> cases h
      · exact Or.inr ⟨name, args ++ [z], hc⟩

theorem neutral_spine_observed {x : Value} (hx : Neutral x) :
    ∃ (name : Nat) (args : List CptI), x (.spine name args) := by
  induction hx with
  | atom name => exact ⟨name, [], NeutralPER.neutralAtom_observed name⟩
  | @app f hf a ha ih =>
      obtain ⟨name, args, hf⟩ := ih
      obtain ⟨z, hz⟩ := ha
      exact ⟨name, args ++ [z], Or.inr (Or.inr ⟨name, args, z, rfl, hf, hz⟩)⟩

theorem neutral_nonempty {x : Value} (hx : Neutral x) : NonemptyValue x := by
  obtain ⟨name, args, h⟩ := neutral_spine_observed hx
  exact ⟨.spine name args, h⟩

theorem neutral_nonbottom {x : Value} (hx : Neutral x) : ¬ ValueEq x bottom := by
  obtain ⟨name, args, h⟩ := neutral_spine_observed hx
  intro he
  have hbot := (he _).mp h
  cases hbot

theorem bottom_not_neutral : ¬ Neutral bottom :=
  fun h => neutral_nonbottom h (ValueEq.refl bottom)

theorem unit_not_neutral (ρ : EnvI) : ¬ Neutral (unitValue ρ) := by
  intro h
  rcases neutral_spineOnly h unitProbe (unit_observed ρ) with h | ⟨name, args, h⟩ <;>
    cases h

/-- This is the actual inherited application equation. -/
theorem neutral_atom_application (name : Nat) (a : Value) :
    ValueEq (NeutralPi.applyValue (NeutralPER.neutralAtom name) a)
      (NeutralFamily.unarySpine name a) := NeutralPi.applyValue_atom name a

theorem neutral_application_spine {f a : Value} {name : Nat} {args : List CptI}
    {z : CptI} (hf : f (.spine name args)) (ha : a z) :
    NeutralPi.applyValue f a (.spine name (args ++ [z])) :=
  Or.inr (Or.inr ⟨name, args, z, rfl, hf, ha⟩)

def emptyValue : Value := fun _ => False

theorem emptyValue_not_nonempty : ¬ NonemptyValue emptyValue := by
  rintro ⟨c, hc⟩
  exact hc

theorem empty_argument_application (name : Nat) :
    ValueEq (NeutralPi.applyValue (NeutralPER.neutralAtom name) emptyValue) bottom := by
  intro c
  constructor
  · intro hc
    rcases (NeutralPi.applyValue_atom name emptyValue c).mp hc with h | ⟨z, hz, h⟩
    · exact h
    · exact hz.elim
  · intro hc
    exact Or.inl hc

theorem empty_argument_not_neutral (name : Nat) :
    ¬ Neutral (NeutralPi.applyValue (NeutralPER.neutralAtom name) emptyValue) :=
  fun h => neutral_nonbottom h (empty_argument_application name)

/-- All premises except argument nonemptiness are inhabited. Removing
that premise would force bottom into this positive neutral closure. -/
theorem unrestricted_application_boundary (name : Nat) :
    Neutral (NeutralPER.neutralAtom name) ∧
    NonemptyValue (NeutralPER.neutralAtom name) ∧
    ValueEq (NeutralPi.applyValue (NeutralPER.neutralAtom name) emptyValue) bottom ∧
    ¬ Neutral (NeutralPi.applyValue (NeutralPER.neutralAtom name) emptyValue) :=
  ⟨.atom name, neutral_nonempty (.atom name), empty_argument_application name,
    empty_argument_not_neutral name⟩

/-- Subsingleton PER with supplied support for the entire application
closure, rather than only its atom generators. -/
structure ClosedCandidate extends Candidate where
  reflect : ∀ {x : Value}, Neutral x → Member relation x

def complete (C : Candidate) : ClosedCandidate where
  toCandidate := predicateCandidate (fun x => Member C.relation x ∨ Neutral x)
  reflect := fun hx => ⟨Or.inr hx, Or.inr hx⟩

theorem complete_member_iff (C : Candidate) (x : Value) :
    Member (complete C).relation x ↔ Member C.relation x ∨ Neutral x :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem complete_includes {C : Candidate} {x y : Value} (h : C.relation x y) :
    (complete C).relation x y :=
  ⟨Or.inl (left_member C.lawful h), Or.inl (right_member C.lawful h)⟩

theorem complete_non_neutral {C : Candidate} {x : Value} (hn : ¬ Neutral x) :
    Member (complete C).relation x ↔ Member C.relation x := by
  constructor
  · intro h
    exact h.1.elim id (fun h => (hn h).elim)
  · intro h
    exact ⟨Or.inl h, Or.inl h⟩

theorem complete_same {C D : Candidate} (h : Same C.relation D.relation) :
    Same (complete C).relation (complete D).relation := by
  intro x y
  exact and_congr (or_congr (h x x) Iff.rfl) (or_congr (h y y) Iff.rfl)

theorem complete_fixed (C : ClosedCandidate) :
    Same (complete C.toCandidate).relation C.relation := by
  intro x y
  constructor
  · intro h
    exact C.irrelevant (h.1.elim id C.reflect) (h.2.elim id C.reflect)
  · exact complete_includes

theorem complete_idempotent (C : Candidate) :
    Same (complete (complete C).toCandidate).relation (complete C).relation :=
  complete_fixed (complete C)

def closedIntersection {ι : Sort u} (C : ι → ClosedCandidate) : ClosedCandidate where
  toCandidate := CandidateUniverse.intersection (fun i => (C i).toCandidate)
  reflect := fun h i => (C i).reflect h

/-- Every candidate occurs, including the empty one. -/
def allCompleted : ClosedCandidate := closedIntersection complete

theorem allCompleted_member_iff (x : Value) :
    Member allCompleted.relation x ↔ Neutral x := by
  constructor
  · intro h
    rcases (h CandidateCompletion.emptyCandidate).1 with he | hn
    · exact (CandidateCompletion.emptyCandidate_no_member x he).elim
    · exact hn
  · intro h C
    exact (complete C).reflect h

theorem complete_empty_no_bottom :
    ¬ Member (complete CandidateCompletion.emptyCandidate).relation bottom := by
  intro h
  rcases h.1 with he | hn
  · exact CandidateCompletion.emptyCandidate_no_member bottom he
  · exact bottom_not_neutral hn

/-- Both the semantic domain and its erasure are explicit. Fibres are
indexed by semantic arguments, so they need not factor through erasure. -/
def FunctionPER {α : Sort u} (erase : α → Value) (D : α → α → Prop)
    (C : α → Relation) (f g : Value) : Prop :=
  ∀ x y, D x y → C x (NeutralPi.applyValue f (erase x))
    (NeutralPi.applyValue g (erase y))

def FamilyCoherent {α : Sort u} (D : α → α → Prop) (C : α → Relation) : Prop :=
  ∀ x y, D x y → Same (C x) (C y)

theorem domain_left_member {α : Sort u} {D : α → α → Prop}
    (hD : NeutralDataFamily.RelLaws D) {x y : α} (hxy : D x y) : D x x :=
  hD.trans hxy (hD.symm hxy)

theorem domain_right_member {α : Sort u} {D : α → α → Prop}
    (hD : NeutralDataFamily.RelLaws D) {x y : α} (hxy : D x y) : D y y :=
  hD.trans (hD.symm hxy) hxy

theorem functionPER_laws {α : Sort u} (erase : α → Value) {D : α → α → Prop}
    (hD : NeutralDataFamily.RelLaws D) {C : α → Relation}
    (hC : ∀ x, D x x → Laws (C x)) (hc : FamilyCoherent D C) :
    Laws (FunctionPER erase D C) where
  symm := by
    intro f g h x y hxy
    have hyx := hD.symm hxy
    have hr := hC y (domain_right_member hD hxy)
    exact (hc y x hyx _ _).mp (hr.symm (h y x hyx))
  trans := by
    intro f g h hfg hgh x y hxy
    have hx := domain_left_member hD hxy
    have hy := domain_right_member hD hxy
    have hmid := (hc y x (hD.symm hxy) _ _).mp (hgh y y hy)
    exact (hC x hx).trans (hfg x y hxy) hmid

/-- Paired transport changes both the legal domain relation and all its
legal result fibres. No relation is recovered from an erased argument. -/
theorem functionPER_same {α : Sort u} (erase : α → Value)
    {D E : α → α → Prop} (hD : NeutralDataFamily.RelLaws D)
    (hDE : ∀ x y, D x y ↔ E x y) {C F : α → Relation}
    (hCF : ∀ x, D x x → Same (C x) (F x)) :
    Same (FunctionPER erase D C) (FunctionPER erase E F) := by
  intro f g
  constructor
  · intro h x y hxy
    have hd := (hDE x y).mpr hxy
    exact (hCF x (domain_left_member hD hd) _ _).mp (h x y hd)
  · intro h x y hxy
    exact (hCF x (domain_left_member hD hxy) _ _).mpr (h x y ((hDE x y).mp hxy))

theorem functionPER_erase_congr {α : Sort u} {erase erase' : α → Value}
    (he : ∀ x, ValueEq (erase x) (erase' x)) (D : α → α → Prop) (C : α → Relation) :
    Same (FunctionPER erase D C) (FunctionPER erase' D C) := by
  intro f g
  constructor
  · intro h x y hxy
    rw [← NeutralCodes.valueEq_eq (he x), ← NeutralCodes.valueEq_eq (he y)]
    exact h x y hxy
  · intro h x y hxy
    rw [NeutralCodes.valueEq_eq (he x), NeutralCodes.valueEq_eq (he y)]
    exact h x y hxy

theorem functionPER_result_transport {α : Sort u} {erase : α → Value}
    {D : α → α → Prop} {C : α → Relation} (hc : FamilyCoherent D C)
    {f g : Value} {x y : α} (hfg : FunctionPER erase D C f g) (hxy : D x y) :
    C y (NeutralPi.applyValue f (erase x)) (NeutralPi.applyValue g (erase y)) :=
  (hc x y hxy _ _).mp (hfg x y hxy)

/-- The function relation itself has neutral members; it is not
completed after the application obligation has been forgotten. -/
def functionCandidate {α : Sort u} (erase : α → Value) (D : α → α → Prop)
    (hD : NeutralDataFamily.RelLaws D) (C : α → ClosedCandidate)
    (coherent : FamilyCoherent D (fun x => (C x).relation))
    (nonempty : ∀ x, D x x → NonemptyValue (erase x)) : ClosedCandidate where
  relation := FunctionPER erase D (fun x => (C x).relation)
  lawful := functionPER_laws erase hD (fun x _ => (C x).lawful) coherent
  irrelevant := by
    intro f g hf hg x y hxy
    have hx := domain_left_member hD hxy
    have hy := domain_right_member hD hxy
    have hfx : Member (C x).relation (NeutralPi.applyValue f (erase x)) := hf x x hx
    have hgy : Member (C x).relation (NeutralPi.applyValue g (erase y)) :=
      (coherent x y hxy _ _).mpr (hg y y hy)
    exact (C x).irrelevant hfx hgy
  reflect := by
    intro f hf x y hxy
    have hx := nonempty x (domain_left_member hD hxy)
    have hy := nonempty y (domain_right_member hD hxy)
    exact (C x).irrelevant ((C x).reflect (.app hf _ hx))
      ((C x).reflect (.app hf _ hy))

theorem functionCandidate_apply {α : Sort u} {erase : α → Value}
    {D : α → α → Prop} {hD : NeutralDataFamily.RelLaws D}
    {C : α → ClosedCandidate}
    {hc : FamilyCoherent D (fun x => (C x).relation)}
    {hne : ∀ x, D x x → NonemptyValue (erase x)}
    {f g : Value} {x y : α}
    (hfg : (functionCandidate erase D hD C hc hne).relation f g) (hxy : D x y) :
    (C x).relation (NeutralPi.applyValue f (erase x))
      (NeutralPi.applyValue g (erase y)) := hfg x y hxy

/-- The original arbitrary candidate is retained as data. Every
candidate occurs; decoding performs the common positive completion. -/
structure Element where
  value : Value
  candidate : Candidate
  level : SortMember (some 0) value
  defined : TypeDefined value

def decode (e : Element) : Relation := (complete e.candidate).relation

def ElementRel (x y : Element) : Prop := Same (decode x) (decode y)

theorem elementRel_refl (x : Element) : ElementRel x x := fun _ _ => Iff.rfl

theorem elementRel_symm {x y : Element} (h : ElementRel x y) : ElementRel y x :=
  fun a b => (h a b).symm

theorem elementRel_trans {x y z : Element} (h : ElementRel x y)
    (g : ElementRel y z) : ElementRel x z := fun a b => (h a b).trans (g a b)

theorem elementRel_laws : NeutralDataFamily.RelLaws ElementRel :=
  ⟨elementRel_symm, elementRel_trans⟩

theorem element_nonempty (e : Element) : NonemptyValue e.value :=
  typeDefined_nonempty e.defined

theorem decode_laws (e : Element) : Laws (decode e) := (complete e.candidate).lawful

theorem decode_irrelevant (e : Element) {x y : Value}
    (hx : Member (decode e) x) (hy : Member (decode e) y) : decode e x y :=
  (complete e.candidate).irrelevant hx hy

theorem decode_transport {e f : Element} (h : ElementRel e f) :
    Same (decode e) (decode f) := h

theorem decode_reflection (e : Element) {x : Value} (hx : Neutral x) :
    Member (decode e) x := (complete e.candidate).reflect hx

def ofCandidate (C : Candidate) : Element :=
  ⟨CandidateUniverse.collisionValue, C, CandidateUniverse.collisionValue_level,
    CandidateUniverse.collisionValue_defined⟩

theorem ofCandidate_retains (C : Candidate) : (ofCandidate C).candidate = C := rfl

/-- An actual proof-valued product over all candidate-bearing
propositions, including those whose original candidate is empty. -/
def forallProp : ClosedCandidate :=
  functionCandidate Element.value ElementRel elementRel_laws
    (fun e => complete e.candidate) (fun _ _ h => h) (fun e _ => element_nonempty e)

theorem forallProp_neutral_member {f : Value} (hf : Neutral f) :
    Member forallProp.relation f := forallProp.reflect hf

theorem forallProp_atom_member (name : Nat) :
    Member forallProp.relation (NeutralPER.neutralAtom name) :=
  forallProp_neutral_member (.atom name)

theorem forallProp_apply {f g : Value} {x y : Element}
    (hfg : forallProp.relation f g) (hxy : ElementRel x y) :
    decode x (NeutralPi.applyValue f x.value) (NeutralPi.applyValue g y.value) :=
  hfg x y hxy

theorem forallProp_apply_member {f : Value} (hf : Member forallProp.relation f)
    (e : Element) : Member (decode e) (NeutralPi.applyValue f e.value) :=
  forallProp_apply hf (elementRel_refl e)

theorem forallProp_every_candidate (name : Nat) (C : Candidate) :
    Member (complete C).relation
      (NeutralPi.applyValue (NeutralPER.neutralAtom name) (ofCandidate C).value) :=
  forallProp_apply_member (forallProp_atom_member name) (ofCandidate C)

theorem forallProp_irrelevant {f g : Value}
    (hf : Member forallProp.relation f) (hg : Member forallProp.relation g) :
    forallProp.relation f g := forallProp.irrelevant hf hg

def falseElement : Element := ofCandidate (CandidateUniverse.proofCandidate False).toCandidate
def trueElement : Element := ofCandidate (CandidateUniverse.proofCandidate True).toCandidate

theorem collision_same_value : falseElement.value = trueElement.value := rfl

theorem trueElement_unit : Member (decode trueElement) (unitValue EnvI.bot) :=
  complete_includes CandidateUniverse.proofCandidate_unit

theorem falseElement_no_unit : ¬ Member (decode falseElement) (unitValue EnvI.bot) := by
  intro h
  have hbase := (complete_non_neutral (C := (CandidateUniverse.proofCandidate False).toCandidate)
    (unit_not_neutral EnvI.bot)).mp h
  exact CandidateUniverse.proofCandidate_false_no_unit hbase

theorem collision_not_related : ¬ ElementRel falseElement trueElement :=
  fun h => falseElement_no_unit ((h _ _).mpr trueElement_unit)

/-- A raw-value fibre decoder cannot recover this retained product's
codomain family. The counterinstance has actual tags, lawful inhabited
fibres and an actual neutral function member. -/
theorem no_raw_fibre_decoder (D : Value → Relation) :
    ¬ (∀ e : Element, Same (D e.value) (decode e)) := by
  intro h
  apply collision_not_related
  intro x y
  exact ((h falseElement) x y).symm.trans ((h trueElement) x y)

theorem forallProp_collision_control (name : Nat) :
    SortMember (some 0) falseElement.value ∧ TypeDefined falseElement.value ∧
    SortMember (some 0) trueElement.value ∧ TypeDefined trueElement.value ∧
    Laws (decode falseElement) ∧ Laws (decode trueElement) ∧
    Member (decode falseElement) (NeutralPER.neutralAtom name) ∧
    Member (decode trueElement) (NeutralPER.neutralAtom name) ∧
    Member forallProp.relation (NeutralPER.neutralAtom name) ∧
    Member (decode falseElement)
      (NeutralPi.applyValue (NeutralPER.neutralAtom name) falseElement.value) ∧
    Member (decode trueElement)
      (NeutralPi.applyValue (NeutralPER.neutralAtom name) trueElement.value) ∧
    Member (decode trueElement) (unitValue EnvI.bot) ∧
    ¬ Member (decode falseElement) (unitValue EnvI.bot) ∧
    falseElement.value = trueElement.value ∧ ¬ ElementRel falseElement trueElement :=
  ⟨falseElement.level, falseElement.defined, trueElement.level, trueElement.defined,
    decode_laws _, decode_laws _, decode_reflection _ (.atom name),
    decode_reflection _ (.atom name), forallProp_atom_member name,
    forallProp_apply_member (forallProp_atom_member name) falseElement,
    forallProp_apply_member (forallProp_atom_member name) trueElement,
    trueElement_unit, falseElement_no_unit, collision_same_value, collision_not_related⟩

/-- A scoped attachment to the existing constant-free raw image of
`forall P : Prop, P`. It does not supply source interpretation of all Pi
codes or source dependent substitution. -/
def forallPropCode (ν : Valuation) (ρ : EnvI) : Element :=
  ⟨UnitModel.denote ν ρ EqLargeFixture.parameter, forallProp.toCandidate,
    fixture_parameter_member ν ρ, fixture_parameter_defined ν ρ⟩

theorem forallPropCode_decode (ν : Valuation) (ρ : EnvI) :
    Same (decode (forallPropCode ν ρ)) forallProp.relation := complete_fixed forallProp

theorem forallPropCode_neutral (ν : Valuation) (ρ : EnvI) (name : Nat) :
    Member (decode (forallPropCode ν ρ)) (NeutralPER.neutralAtom name) :=
  (forallPropCode_decode ν ρ _ _).mpr (forallProp_atom_member name)

theorem forallProp_source_control (ν : Valuation) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      EqLargeFixture.parameter (.sort .zero)) ∧
    SortMember (some 0) (forallPropCode ν EnvI.bot).value ∧
    TypeDefined (forallPropCode ν EnvI.bot).value ∧
    Same (decode (forallPropCode ν EnvI.bot)) forallProp.relation ∧
    Member (decode (forallPropCode ν EnvI.bot)) (NeutralPER.neutralAtom name) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨EqLargeFixture.parameterTyped⟩,
    (forallPropCode ν EnvI.bot).level, (forallPropCode ν EnvI.bot).defined,
    forallPropCode_decode _ _, forallPropCode_neutral _ _ _⟩

end Rcic.Declarative.Ann.LR3.CandidatePi
