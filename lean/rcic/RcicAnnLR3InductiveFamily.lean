import rcic.RcicAnnLR3DependentFamily
import rcic.RcicAnnLR3NeutralCodes

/-!
# Positive represented families with explicit decoding data

`Represented` is a positive relation on the existing `Value` carrier. Its
witnesses are legal trees, their representations, and structural bisimulation.
A collision-adequate encoding supplies its PER laws and identifies this
relation with the relation on any explicitly retained representatives.
Collision adequacy is a sufficient interface proved below for Nat; it is
not assumed for all signatures, nor claimed necessary for every pushforward.

The data-valued decoder consumes `Realized`, which retains its legal tree.
It never obtains a tree from membership in `Represented` or `NeutralClosure`.
The bridge to `Paired` preserves this tree and the existing dependent quotient
eliminator. All quotient transport stays on the legal-tree quotient.

The supplied Nat package uses the existing admitted Nat constructor shape:
zero has no fields, successor has one direct recursive field, and there are
no parameters or indices. Its constructor values use the native heads 11
and 12. An exact tagged type value is supplied separately. This is a concrete
family producer and a general represented-family algebra; it is not a
decoder for every admitted source signature or a source recursor theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.InductiveFamily

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedInductive NeutralDataFamily

universe u v w l z

/-- Membership witnesses remain in Prop. They are not a data decoder. -/
inductive Represented {Index : Type u} (S : Signature.{u,v,w} Index)
    (Leaf : Index → Type l) (RN : ∀ i, Leaf i → Leaf i → Prop)
    (encode : ∀ {i}, Tree S Leaf i → Value) (i : Index) : Value → Value → Prop
  | intro (x y : LegalTree S Leaf RN i) {a b : Value}
      (left : ValueEq a (encode x.1)) (right : ValueEq b (encode y.1))
      (related : Bisim S Leaf RN x.1 y.1) : Represented S Leaf RN encode i a b

section General

variable {Index : Type u} {S : Signature.{u,v,w} Index}
  {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
  {encode : ∀ {i}, Tree S Leaf i → Value}

/-- This explicit premise allows middle witnesses to be spliced. -/
def CollisionAdequate (encode : ∀ {i}, Tree S Leaf i → Value) : Prop :=
  ∀ {i} (x y : LegalTree S Leaf RN i),
    ValueEq (encode x.1) (encode y.1) → Bisim S Leaf RN x.1 y.1

theorem represented_laws (hRN : ∀ i, RelLaws (RN i))
    (adequate : CollisionAdequate (RN := RN) encode) (i : Index) :
    TypedPER.Laws (Represented S Leaf RN encode i) where
  symm := by
    intro a b h
    cases h with
    | intro x y hx hy hxy => exact .intro y x hy hx (bisim_symm hRN hxy)
  trans := by
    intro a b c h g
    cases h with
    | intro x y hx hy hxy =>
      cases g with
      | intro t z ht hz htz =>
        exact .intro x z hx hz
          (bisim_trans hRN hxy (bisim_trans hRN (adequate y t (hy.symm.trans ht)) htz))

theorem represented_congr {i : Index} {a b c d : Value}
    (hac : ValueEq a c) (hbd : ValueEq b d) :
    Represented S Leaf RN encode i a b ↔ Represented S Leaf RN encode i c d := by
  constructor
  · intro h
    cases h with
    | intro x y hx hy hxy => exact .intro x y (hac.symm.trans hx) (hbd.symm.trans hy) hxy
  · intro h
    cases h with
    | intro x y hx hy hxy => exact .intro x y (hac.trans hx) (hbd.trans hy) hxy

/-- The representation needed by a data consumer is itself data. -/
structure Realized (S : Signature.{u,v,w} Index) (Leaf : Index → Type l)
    (RN : ∀ i, Leaf i → Leaf i → Prop)
    (encode : ∀ {i}, Tree S Leaf i → Value) (i : Index) (value : Value) where
  tree : LegalTree S Leaf RN i
  represents : ValueEq value (encode tree.1)

def realize {i : Index} (t : LegalTree S Leaf RN i) :
    Realized S Leaf RN encode i (encode t.1) := ⟨t, ValueEq.refl _⟩

def realizedTransport {i : Index} {a b : Value} (h : ValueEq a b)
    (p : Realized S Leaf RN encode i a) : Realized S Leaf RN encode i b :=
  ⟨p.tree, h.symm.trans p.represents⟩

theorem realized_member {i : Index} {a : Value}
    (p : Realized S Leaf RN encode i a) :
    TypedPER.Member (Represented S Leaf RN encode i) a :=
  .intro p.tree p.tree p.represents p.represents p.tree.2

/-- The proof of membership supplies no new representative: both are inputs. -/
theorem represented_iff_bisim (hRN : ∀ i, RelLaws (RN i))
    (adequate : CollisionAdequate (RN := RN) encode)
    {i : Index} {a b : Value} (p : Realized S Leaf RN encode i a)
    (q : Realized S Leaf RN encode i b) :
    Represented S Leaf RN encode i a b ↔ Bisim S Leaf RN p.tree.1 q.tree.1 := by
  constructor
  · intro h
    cases h with
    | intro x y hx hy hxy =>
      exact bisim_trans hRN (adequate p.tree x (p.represents.symm.trans hx))
        (bisim_trans hRN hxy (adequate y q.tree (hy.symm.trans q.represents)))
  · intro h
    exact .intro p.tree q.tree p.represents q.represents h

def decode (hRN : ∀ i, RelLaws (RN i)) {i : Index} {a : Value}
    (p : Realized S Leaf RN encode i a) :
    DependentFamily.FamilyQuotient (S := S) (Leaf := Leaf) hRN i :=
  DependentFamily.treeClass hRN p.tree

theorem decode_related (hRN : ∀ i, RelLaws (RN i))
    (adequate : CollisionAdequate (RN := RN) encode)
    {i : Index} {a b : Value} (p : Realized S Leaf RN encode i a)
    (q : Realized S Leaf RN encode i b)
    (h : Represented S Leaf RN encode i a b) : decode hRN p = decode hRN q :=
  Quotient.sound ((represented_iff_bisim hRN adequate p q).mp h)

theorem decode_transport (hRN : ∀ i, RelLaws (RN i))
    (adequate : CollisionAdequate (RN := RN) encode)
    {i : Index} {a b : Value} (p : Realized S Leaf RN encode i a)
    (q : Realized S Leaf RN encode i b)
    (h : Represented S Leaf RN encode i a b)
    (M : DependentFamily.FamilyQuotient (S := S) (Leaf := Leaf) hRN i → Type z)
    (f : ∀ t, M t) :
    DependentFamily.transport M (decode_related hRN adequate p q h) (f (decode hRN p)) =
      f (decode hRN q) := by
  have section_transport : ∀ (x y : DependentFamily.FamilyQuotient
      (S := S) (Leaf := Leaf) hRN i) (e : x = y),
      DependentFamily.transport M e (f x) = f y := by
    intro x y e
    cases e
    rfl
  exact section_transport _ _ (decode_related hRN adequate p q h)

variable (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S)

def pairedRealized {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    Realized S Leaf RN (interpret leafValue ctor) i p.value :=
  ⟨⟨p.tree, p.admitted⟩, by rw [p.value_eq]; exact ValueEq.refl _⟩

def realizedPair {i : Index} {a : Value}
    (p : Realized S Leaf RN (interpret leafValue ctor) i a) :
    Paired S Leaf RN leafValue ctor i :=
  ⟨p.tree.1, p.tree.2, a, NeutralCodes.valueEq_eq p.represents⟩

theorem represented_pair_iff (hRN : ∀ i, RelLaws (RN i))
    (adequate : CollisionAdequate (RN := RN) (interpret leafValue ctor))
    {i : Index} (p q : Paired S Leaf RN leafValue ctor i) :
    Represented S Leaf RN (interpret leafValue ctor) i p.value q.value ↔ PairPER p q :=
  represented_iff_bisim hRN adequate (pairedRealized leafValue ctor p)
    (pairedRealized leafValue ctor q)

theorem decode_realizedPair (hRN : ∀ i, RelLaws (RN i)) {i : Index} {a : Value}
    (p : Realized S Leaf RN (interpret leafValue ctor) i a) :
    pairedClass hRN (realizedPair leafValue ctor p) = decode hRN p := rfl

end General

namespace NatCode

inductive Rule
  | zero
  | succ

inductive Premise : Rule → Type
  | arg : Premise .succ

def signature : Signature Unit where
  Rule := fun _ => Rule
  Premise := fun _ r => Premise r
  child := fun _ _ _ => ()

abbrev Leaf (_ : Unit) := Nat

def leafRelation (_ : Unit) (a b : Nat) : Prop := a = b

theorem leaf_laws (i : Unit) : RelLaws (leafRelation i) where
  symm := Eq.symm
  trans := Eq.trans

def leafValue (_ : Unit) (a : Nat) : Value := NeutralPER.neutralAtom (1000 + a)

def ctor : NeutralFamily.ConstructorOp signature
  | _, .zero, _ => NeutralPER.neutralAtom 11
  | _, .succ, children => NeutralFamily.unarySpine 12 (children .arg)

def encode {i : Unit} (t : Tree signature Leaf i) : Value := interpret leafValue ctor t

theorem encode_neutral (i : Unit) (a : Nat) :
    encode (.neutral i a) = NeutralPER.neutralAtom (1000 + a) := rfl

theorem encode_zero (i : Unit) (xs : Premise .zero → Tree signature Leaf ()) :
    encode (.node i .zero xs) = NeutralPER.neutralAtom 11 := rfl

theorem encode_succ (i : Unit) (xs : Premise .succ → Tree signature Leaf ()) :
    encode (.node i .succ xs) = NeutralFamily.unarySpine 12 (encode (xs .arg)) := rfl

theorem atom_injective {a b : Nat}
    (h : ValueEq (NeutralPER.neutralAtom a) (NeutralPER.neutralAtom b)) : a = b := by
  have hb := (h (.spine a [])).mp (NeutralPER.neutralAtom_observed a)
  rcases approxI_const_inv hb with hb | hs
  · cases hb
  · exact (CptI.spine.inj hs).1

theorem atom_not_unary (a head : Nat) (x : Value) :
    ¬ ValueEq (NeutralPER.neutralAtom a) (NeutralFamily.unarySpine head x) := by
  intro h
  have ho := (h (.spine a [])).mp (NeutralPER.neutralAtom_observed a)
  rcases ho with hb | ⟨c, _, hc⟩
  · cases hb
  · have he := (CptI.spine.inj hc).2
    cases he

theorem unary_reflects (head : Nat) {x y : Value}
    (h : ValueEq (NeutralFamily.unarySpine head x) (NeutralFamily.unarySpine head y)) :
    ValueEq x y := by
  intro c
  constructor
  · intro hc
    have ho := (h (.spine head [c])).mp (Or.inr ⟨c, hc, rfl⟩)
    rcases ho with hb | ⟨d, hd, he⟩
    · cases hb
    · have hcd : c = d := (List.cons.inj (CptI.spine.inj he).2).1
      exact hcd.symm ▸ hd
  · intro hc
    have ho := (h (.spine head [c])).mpr (Or.inr ⟨c, hc, rfl⟩)
    rcases ho with hb | ⟨d, hd, he⟩
    · cases hb
    · have hcd : c = d := (List.cons.inj (CptI.spine.inj he).2).1
      exact hcd.symm ▸ hd

theorem ctor_congruent : ConstructorCongruent ctor := by
  intro i r xs ys h
  cases r with
  | zero => exact ValueEq.refl _
  | succ => exact unarySpine_congr 12 (h .arg)

theorem encode_respects {i : Unit} {x y : Tree signature Leaf i}
    (h : Bisim signature Leaf leafRelation x y) : ValueEq (encode x) (encode y) :=
  fold_respects (fun _ => ValueEq) leafValue ctor
    (fun _ _ _ h => by cases h; exact ValueEq.refl _) ctor_congruent h

/-- Reflection is proved for every explicit Nat tree, including neutrals. -/
theorem encode_reflects {i : Unit} {x y : Tree signature Leaf i}
    (h : ValueEq (encode x) (encode y)) : Bisim signature Leaf leafRelation x y := by
  induction x with
  | neutral i a =>
    cases y with
    | neutral i b =>
      have hab : a = b := Nat.add_left_cancel (atom_injective h)
      exact .neutral i a b hab
    | node i r ys =>
      cases r with
      | zero =>
        have he : 1000 + a = 11 := atom_injective h
        have hn : (1000 : Nat) ≤ 11 := he ▸ Nat.le_add_right 1000 a
        exact ((by decide : ¬ ((1000 : Nat) ≤ 11)) hn).elim
      | succ => exact (atom_not_unary (1000 + a) 12 (encode (ys .arg)) h).elim
  | node i r xs ih =>
    cases y with
    | neutral i b =>
      cases r with
      | zero =>
        have he : 1000 + b = 11 := atom_injective h.symm
        have hn : (1000 : Nat) ≤ 11 := he ▸ Nat.le_add_right 1000 b
        exact ((by decide : ¬ ((1000 : Nat) ≤ 11)) hn).elim
      | succ => exact (atom_not_unary (1000 + b) 12 (encode (xs .arg)) h.symm).elim
    | node i s ys =>
      cases r with
      | zero =>
        cases s with
        | zero =>
          exact Bisim.node (S := signature) (Leaf := Leaf) (RN := leafRelation)
            i Rule.zero xs ys (fun p => nomatch p)
        | succ => exact (atom_not_unary 11 12 (encode (ys .arg)) h).elim
      | succ =>
        cases s with
        | zero => exact (atom_not_unary 11 12 (encode (xs .arg)) h.symm).elim
        | succ =>
          exact Bisim.node (S := signature) (Leaf := Leaf) (RN := leafRelation)
            i Rule.succ xs ys (fun p => by
            cases p
            exact ih .arg (unary_reflects 12 h))

theorem encode_adequate : CollisionAdequate (RN := leafRelation) encode :=
  fun _ _ h => encode_reflects h

theorem encode_bot {i : Unit} (t : Tree signature Leaf i) : encode t .bot := by
  cases t with
  | neutral i a => exact ApproxI.bot _ _
  | node i r xs =>
    cases r with
    | zero => exact ApproxI.bot _ _
    | succ => exact Or.inl rfl

def legal {i : Unit} (t : Tree signature Leaf i) : LegalTree signature Leaf leafRelation i :=
  ⟨t, bisim_refl (fun _ _ => rfl) t⟩

def PER : TypedPER.Relation := Represented signature Leaf leafRelation encode ()

theorem per_laws : TypedPER.Laws PER := represented_laws leaf_laws encode_adequate ()

theorem per_member_bot {a : Value} (h : TypedPER.Member PER a) : a .bot := by
  cases h with
  | intro x y hx hy hxy => exact (hx .bot).mpr (encode_bot x.1)

def neutralTree (a : Nat) : Tree signature Leaf () := .neutral () a

def zeroTree : Tree signature Leaf () := .node () .zero (fun p => nomatch p)

def succTree (t : Tree signature Leaf ()) : Tree signature Leaf () :=
  .node () .succ (fun _ => t)

def reflect (a : Nat) : Realized signature Leaf leafRelation encode () (leafValue () a) :=
  realize (legal (neutralTree a))

def zero : Realized signature Leaf leafRelation encode () (NeutralPER.neutralAtom 11) :=
  realize (legal zeroTree)

def successor {a : Value} (p : Realized signature Leaf leafRelation encode () a) :
    Realized signature Leaf leafRelation encode () (NeutralFamily.unarySpine 12 a) :=
  ⟨legal (succTree p.tree.1), unarySpine_congr 12 p.represents⟩

theorem reflect_member (a : Nat) : TypedPER.Member PER (leafValue () a) :=
  realized_member (reflect a)

theorem zero_member : TypedPER.Member PER (NeutralPER.neutralAtom 11) :=
  realized_member zero

theorem successor_related {a b : Value} (h : PER a b) :
    PER (NeutralFamily.unarySpine 12 a) (NeutralFamily.unarySpine 12 b) := by
  cases h with
  | intro x y hx hy hxy =>
    exact .intro (legal (succTree x.1)) (legal (succTree y.1))
      (unarySpine_congr 12 hx) (unarySpine_congr 12 hy)
      (Bisim.node (S := signature) (Leaf := Leaf) (RN := leafRelation)
        () Rule.succ _ _ (fun _ => hxy))

/-- A fixed label for use as one base clause of a larger code relation. -/
def typeValue : Value :=
  fun c => c = .bot ∨ c = NeutralCodes.fullTag (some 1) (.spine 704 [.spine 10 []])

theorem typeValue_level : SortMember (some 1) typeValue := by
  intro c hc
  rcases hc with rfl | rfl
  · exact .bot
  · exact .tagged _ _ (Or.inr rfl)

theorem typeValue_defined : TypeDefined typeValue :=
  ⟨some 1, .spine 704 [.spine 10 []], Or.inr rfl⟩

theorem typeValue_not_old (d : NeutralCodes.Descriptor) :
    ¬ ValueEq typeValue (NeutralCodes.reify d) := by
  intro he
  cases d with
  | neutralType k name =>
    have ho := (he (NeutralCodes.fullTag (some 1) (.spine 704 [.spine 10 []]))).mp (Or.inr rfl)
    simp [NeutralCodes.reify, NeutralCodes.neutralTypeValue, NeutralCodes.fullTag,
      NeutralCodes.neutralPayload] at ho
  | proof P =>
    have ho := (he (NeutralCodes.fullTag (some 1) (.spine 704 [.spine 10 []]))).mp (Or.inr rfl)
    simp [NeutralCodes.reify, NeutralCodes.proofCodeValue, NeutralCodes.fullTag] at ho
  | univ k =>
    have ho := (he (NeutralCodes.fullTag (some 1) (.spine 704 [.spine 10 []]))).mp (Or.inr rfl)
    rcases approxI_foldApps_const_inv (r := 10) (ls := [])
      (xs := [levelTerm (k.map Nat.succ), .app (.const 11 []) (levelTerm k)]) ho
      with hb | ⟨us, hu, hs⟩
    · cases hb
    · cases hs with
      | cons ha hs =>
        cases hs with
        | cons hp hs =>
          cases hs
          cases hu
          rcases approxI_foldApps_const_inv (r := 11) (ls := [])
            (xs := [levelTerm k]) hp with hb | ⟨vs, hv, _⟩
          · cases hb
          · cases hv

/-- Actual source admission and the two inspected recursive field shapes. -/
theorem admitted_shapes :
    Nonempty (EnvWfA (iotaIfaceA pinNatBuiltEnvA) pinNatBuiltEnvA) ∧
    ctorShapesA 10 pinNatFamA.nparamsA (pinZeroA.normA.getD pinZeroA.mtypeA) = some [] ∧
    ctorShapesA 10 pinNatFamA.nparamsA (pinSuccA.normA.getD pinSuccA.mtypeA) =
      some [.recursive 0] := ⟨⟨pinNatBuilt_wf⟩, rfl, rfl⟩

theorem source_family_typed :
    Nonempty (HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
      (.const 10 []) (.sort (.succ .zero))) :=
  ⟨pinNatConstTy (by rfl)⟩

theorem supplied_control :
    TypedPER.Member PER (NeutralPER.neutralAtom 11) ∧
    TypedPER.Member PER (NeutralFamily.unarySpine 12 (NeutralPER.neutralAtom 11)) ∧
    TypedPER.Member PER (leafValue () 0) :=
  ⟨zero_member, successor_related zero_member, reflect_member 0⟩

end NatCode

end Rcic.Declarative.Ann.LR3.InductiveFamily
