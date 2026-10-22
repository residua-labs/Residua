import rcic.RcicAnnLR3NeutralExtraction
import rcic.RcicAnnLR3NeutralPER

/-!
# A decodable neutral, proof and universe code producer

This is an actual CodeSystem with a constructed decoder and neutral
reflection, on the unchanged Value carrier. Code presentations have exact
Option Nat tags. Different neutral type names at the same level are
related codes with the same element PER. Proof descriptors retain their
truth parameter while admitting neutrals independently of that truth.

Reflection is a predicate defined by the unique presentation of a type
value. It does not select a presentation from Prop or decide its shape.
The universe PER contains precisely related reified descriptors; decoding
therefore produces an actual element Code rather than only a sort tag.

The descriptor language here closes neutrals, arbitrary propositions and
universes. Pi and general-family code closure and their source operations
are separate producer obligations. No full source fundamental theorem is
asserted. No admitted environment or context is removed. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.NeutralCodes
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements

inductive Descriptor
  | neutralType (level : Option Nat) (name : Nat)
  | proof (truth : Prop)
  | univ (level : Option Nat)

def level : Descriptor → Option Nat
  | .neutralType k _ => k
  | .proof _ => some 0
  | .univ k => k.map Nat.succ

def fullTag (k : Option Nat) (payload : CptI) : CptI :=
  .spine 10 [.spine (levelRef k) [], payload]

def neutralPayload (name : Nat) : CptI := .lam [([], .spine name [])]

def neutralTypeValue (k : Option Nat) (name : Nat) : Value :=
  fun c => c = .bot ∨ c = fullTag k (neutralPayload name)

def proofCodeValue (P : Prop) : Value :=
  fun c => c = .bot ∨ c = fullTag (some 0) (.spine 24 []) ∨
    (P ∧ c = fullTag (some 0) (.spine 25 []))

def reify : Descriptor → Value
  | .neutralType k name => neutralTypeValue k name
  | .proof P => proofCodeValue P
  | .univ k => universeValue k

theorem valueEq_eq {x y : Value} (h : ValueEq x y) : x = y :=
  funext (fun c => propext (h c))

theorem reify_level (d : Descriptor) : SortMember (level d) (reify d) := by
  cases d with
  | neutralType k name =>
      intro c hc
      rcases hc with rfl | rfl
      · exact .bot
      · exact .tagged _ _ (Or.inr rfl)
  | proof P =>
      intro c hc
      rcases hc with rfl | rfl | ⟨_, rfl⟩
      · exact .bot
      · exact .tagged _ _ (Or.inr rfl)
      · exact .tagged _ _ (Or.inr rfl)
  | univ k => exact sort_member _ _

theorem reify_defined (d : Descriptor) : TypeDefined (reify d) := by
  cases d with
  | neutralType k name => exact ⟨k, neutralPayload name, Or.inr rfl⟩
  | proof P => exact ⟨some 0, .spine 24 [], Or.inr (Or.inl rfl)⟩
  | univ k => exact sort_defined _ _

theorem neutralType_not_universe (k j : Option Nat) (name : Nat) :
    ¬ ValueEq (neutralTypeValue k name) (universeValue j) := by
  intro he
  have h := (he (fullTag k (neutralPayload name))).mp (Or.inr rfl)
  rcases approxI_foldApps_const_inv (r := 10) (ls := [])
      (xs := [levelTerm (j.map Nat.succ), .app (.const 11 []) (levelTerm j)]) h
    with hb | ⟨us, hu, hs⟩
  · cases hb
  · cases hs with
    | cons ha hs =>
      cases hs with
      | cons hp hs =>
        cases hs
        cases hu
        rcases approxI_foldApps_const_inv (r := 11) (ls := [])
          (xs := [levelTerm j]) hp with hb | ⟨vs, hv, _⟩
        · cases hb
        · cases hv

theorem proofCode_not_universe (P : Prop) (k : Option Nat) :
    ¬ ValueEq (proofCodeValue P) (universeValue k) := by
  intro he
  have hk := sortMember_unique (reify_level (.proof P))
    (sortMember_congr he.symm (sort_member EnvI.bot k)) (reify_defined (.proof P))
  cases k with
  | none => cases hk
  | some n => exact Nat.noConfusion (Option.some.inj hk)

theorem neutralType_not_proof (k : Option Nat) (name : Nat) (P : Prop) :
    ¬ ValueEq (neutralTypeValue k name) (proofCodeValue P) := by
  intro he
  have h := (he (fullTag k (neutralPayload name))).mp (Or.inr rfl)
  simp [proofCodeValue, fullTag, neutralPayload] at h

theorem reify_injective {d e : Descriptor} (h : ValueEq (reify d) (reify e)) : d = e := by
  cases d with
  | neutralType k name =>
      cases e with
      | neutralType l other =>
          have hl : k = l := sortMember_unique (reify_level (.neutralType k name))
            (sortMember_congr h.symm (reify_level (.neutralType l other)))
            (reify_defined (.neutralType k name))
          subst l
          have ho := (h (fullTag k (neutralPayload name))).mp (Or.inr rfl)
          have hn : name = other := by
            simpa [reify, neutralTypeValue, fullTag, neutralPayload] using ho
          subst other
          rfl
      | proof P => exact (neutralType_not_proof k name P h).elim
      | univ j => exact (neutralType_not_universe k j name h).elim
  | proof P =>
      cases e with
      | neutralType k name => exact (neutralType_not_proof k name P h.symm).elim
      | proof Q =>
          have hpq : P ↔ Q := by
            simpa [reify, proofCodeValue, fullTag] using
              h (fullTag (some 0) (.spine 25 []))
          exact congrArg Descriptor.proof (propext hpq)
      | univ k => exact (proofCode_not_universe P k h).elim
  | univ k =>
      cases e with
      | neutralType l name => exact (neutralType_not_universe l k name h.symm).elim
      | proof P => exact (proofCode_not_universe P k h.symm).elim
      | univ j => exact congrArg Descriptor.univ (sort_code_injective h)

/-- The relation can identify different type values. Neutral names are
retained as observations, while their element carriers agree. -/
def Related : Descriptor → Descriptor → Prop
  | .neutralType k _, .neutralType l _ => k = l
  | .proof P, .proof Q => P ↔ Q
  | .univ k, .univ l => k = l
  | _, _ => False

theorem related_refl (d : Descriptor) : Related d d := by
  cases d <;> simp [Related]

theorem related_symm {d e : Descriptor} (h : Related d e) : Related e d := by
  cases d <;> cases e <;> simp_all [Related]

theorem related_trans {d e f : Descriptor} (h : Related d e) (g : Related e f) :
    Related d f := by
  cases d <;> cases e <;> cases f <;> simp_all [Related]

theorem related_level {d e : Descriptor} (h : Related d e) : level d = level e := by
  cases d <;> cases e <;> simp_all [Related, level]

def UniversePER (k : Option Nat) (x y : Value) : Prop :=
  ∃ d e : Descriptor, level d = k ∧ Related d e ∧
    ValueEq x (reify d) ∧ ValueEq y (reify e)

theorem universePER_laws (k : Option Nat) : Laws (UniversePER k) where
  symm := by
    rintro x y ⟨d, e, hd, hde, hx, hy⟩
    exact ⟨e, d, (related_level hde).symm.trans hd, related_symm hde, hy, hx⟩
  trans := by
    rintro x y z ⟨d, e, hd, hde, hx, hy⟩ ⟨f, g, _, hfg, hy', hz⟩
    have hef : e = f := reify_injective (hy.symm.trans hy')
    subst f
    exact ⟨d, g, hd, related_trans hde hfg, hx, hz⟩

def Neutral (x : Value) : Prop := ∃ name : Nat, NeutralPER.AtomNeutral name x

def El : Descriptor → Relation
  | .neutralType _ _ => NeutralPER.ProofPER Neutral False
  | .proof P => NeutralPER.ProofPER Neutral P
  | .univ k => UniversePER k

theorem el_laws (d : Descriptor) : Laws (El d) := by
  cases d with
  | neutralType k name => exact NeutralPER.proofPER_laws _ _
  | proof P => exact NeutralPER.proofPER_laws _ _
  | univ k => exact universePER_laws k

theorem related_el {d e : Descriptor} (h : Related d e) : Same (El d) (El e) := by
  cases d with
  | neutralType k name =>
      cases e with
      | neutralType l other => exact fun _ _ => Iff.rfl
      | proof Q => exact h.elim
      | univ j => exact h.elim
  | proof P =>
      cases e with
      | neutralType l other => exact h.elim
      | proof Q => exact NeutralPER.proofPER_same h (fun _ => Iff.rfl)
      | univ j => exact h.elim
  | univ k =>
      cases e with
      | neutralType l other => exact h.elim
      | proof Q => exact h.elim
      | univ j =>
          change k = j at h
          subst j
          exact fun _ _ => Iff.rfl

def Code (k : Option Nat) (V : Value) (R : Relation) : Prop :=
  ∃ d : Descriptor, level d = k ∧ ValueEq V (reify d) ∧ Same R (El d)

theorem code (d : Descriptor) : Code (level d) (reify d) (El d) :=
  ⟨d, rfl, ValueEq.refl _, fun _ _ => Iff.rfl⟩

theorem code_lawful {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) : Laws R := by
  obtain ⟨d, _, _, hr⟩ := h
  exact ⟨fun hxy => (hr _ _).mpr ((el_laws d).symm ((hr _ _).mp hxy)),
    fun hxy hyz => (hr _ _).mpr ((el_laws d).trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩

theorem code_defined {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) :
    TypeDefined V := by
  obtain ⟨d, _, hv, _⟩ := h
  exact typeDefined_congr hv.symm (reify_defined d)

theorem code_level {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) :
    SortMember k V := by
  obtain ⟨d, hd, hv, _⟩ := h
  subst k
  exact sortMember_congr hv.symm (reify_level d)

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : Code k V R) (g : Code l V S) : Same R S := by
  obtain ⟨d, _, hv, hr⟩ := h
  obtain ⟨e, _, hv', hs⟩ := g
  have he := reify_injective (hv.symm.trans hv')
  subst e
  exact fun x y => (hr x y).trans (hs x y).symm

theorem code_member_universe {k : Option Nat} {V : Value} {R : Relation}
    (h : Code k V R) : Member (UniversePER k) V := by
  obtain ⟨d, hd, hv, _⟩ := h
  exact ⟨d, d, hd, related_refl d, hv, hv⟩

theorem code_prop_irrelevant {V : Value} {R : Relation} {x y : Value}
    (h : Code (some 0) V R) (hx : Member R x) (hy : Member R y) : R x y := by
  obtain ⟨d, hd, _, hr⟩ := h
  apply (hr x y).mpr
  cases d with
  | neutralType k name =>
      exact NeutralPER.proofPER_irrelevant ((hr x x).mp hx) ((hr y y).mp hy)
  | proof P =>
      exact NeutralPER.proofPER_irrelevant ((hr x x).mp hx) ((hr y y).mp hy)
  | univ k => cases k <;> simp [level] at hd

theorem code_universe (k : Option Nat) :
    Code (k.map Nat.succ) (universeValue k) (UniversePER k) := code (.univ k)

theorem universe_member (k : Option Nat) :
    Member (UniversePER (k.map Nat.succ)) (universeValue k) :=
  ⟨.univ k, .univ k, rfl, related_refl _, ValueEq.refl _, ValueEq.refl _⟩

theorem universe_carrier {k l : Option Nat} {R : Relation}
    (h : Code l (universeValue k) R) : Same R (UniversePER k) :=
  code_coherent h (code_universe k)

theorem decode {k l : Option Nat} {R : Relation} {x : Value}
    (h : Code l (universeValue k) R) (hx : Member R x) :
    ∃ S : Relation, Code k x S := by
  obtain ⟨d, e, hd, _, hxd, _⟩ := (universe_carrier h x x).mp hx
  exact ⟨El d, d, hd, hxd, fun _ _ => Iff.rfl⟩

theorem universe_elim {k l : Option Nat} {R : Relation} {x : Value}
    (h : Code l (universeValue k) R) (hx : Member R x) :
    SortMember k x ∧ TypeDefined x := by
  obtain ⟨S, hs⟩ := decode h hx
  exact ⟨code_level hs, code_defined hs⟩

def codeSystem : CodeSystem where
  Code := Code
  universePER := UniversePER
  lawful := code_lawful
  defined := code_defined
  level := code_level
  coherent := code_coherent
  universe_code := code_universe
  universe_member := universe_member
  universe_elim := universe_elim

def reflectDescriptor : Descriptor → Nat → Value
  | .neutralType _ _, name => NeutralPER.neutralAtom name
  | .proof _, name => NeutralPER.neutralAtom name
  | .univ k, name => reify (.neutralType k name)

theorem reflectDescriptor_member (d : Descriptor) (name : Nat) :
    Member (El d) (reflectDescriptor d name) := by
  cases d with
  | neutralType k other =>
      exact NeutralPER.neutral_member Neutral False ⟨name, ValueEq.refl _⟩
  | proof P => exact NeutralPER.neutral_member Neutral P ⟨name, ValueEq.refl _⟩
  | univ k =>
      exact ⟨.neutralType k name, .neutralType k name, rfl, related_refl _,
        ValueEq.refl _, ValueEq.refl _⟩

/-- A total raw value operation. The existential is inside a value's Prop
of observations, not a choice of data from an existential proof. -/
def reflect (V : Value) (name : Nat) : Value :=
  fun c => ∃ d : Descriptor, ValueEq V (reify d) ∧ reflectDescriptor d name c

theorem reflect_at {V : Value} {d : Descriptor} (h : ValueEq V (reify d)) (name : Nat) :
    ValueEq (reflect V name) (reflectDescriptor d name) := by
  intro c
  constructor
  · rintro ⟨e, he, hc⟩
    have hed : e = d := reify_injective (he.symm.trans h)
    subst e
    exact hc
  · intro hc
    exact ⟨d, h, hc⟩

theorem reflectDescriptor_related_of_same {d e : Descriptor}
    (h : Same (El d) (El e)) (name : Nat) :
    El d (reflectDescriptor d name) (reflectDescriptor e name) := by
  cases d with
  | neutralType k other =>
      exact NeutralPER.proofPER_irrelevant
        (reflectDescriptor_member (.neutralType k other) name)
        ((h _ _).mpr (reflectDescriptor_member e name))
  | proof P =>
      exact NeutralPER.proofPER_irrelevant (reflectDescriptor_member (.proof P) name)
        ((h _ _).mpr (reflectDescriptor_member e name))
  | univ k =>
      cases e with
      | neutralType j other =>
          have hu : Member (UniversePER k) (NeutralPER.neutralAtom name) :=
            (h _ _).mpr (reflectDescriptor_member (.neutralType j other) name)
          exact (NeutralPER.neutralAtom_not_sort_member name k
            (universe_elim (code_universe k) hu).1).elim
      | proof P =>
          have hu : Member (UniversePER k) (NeutralPER.neutralAtom name) :=
            (h _ _).mpr (reflectDescriptor_member (.proof P) name)
          exact (NeutralPER.neutralAtom_not_sort_member name k
            (universe_elim (code_universe k) hu).1).elim
      | univ j =>
          have hj : SortMember j (reify (.neutralType k name)) :=
            (universe_elim (code_universe j)
              ((h _ _).mp (reflectDescriptor_member (.univ k) name))).1
          have hkj : k = j := sortMember_unique
            (reify_level (.neutralType k name)) hj (reify_defined (.neutralType k name))
          subst j
          exact reflectDescriptor_member (.univ k) name

theorem reflect_member {k : Option Nat} {V : Value} {R : Relation}
    (h : Code k V R) (name : Nat) : Member R (reflect V name) := by
  obtain ⟨d, _, hv, hr⟩ := h
  rw [valueEq_eq (reflect_at hv name)]
  exact (hr _ _).mpr (reflectDescriptor_member d name)

/-- Reflection respects any coherent pair of element-code presentations,
including presentations whose type values are different observations. -/
theorem reflect_relation {k l : Option Nat} {V W : Value} {R S : Relation}
    (hv : Code k V R) (hw : Code l W S) (h : Same R S) (name : Nat) :
    R (reflect V name) (reflect W name) := by
  obtain ⟨d, _, hV, hR⟩ := hv
  obtain ⟨e, _, hW, hS⟩ := hw
  have hde : Same (El d) (El e) :=
    fun x y => (hR x y).symm.trans ((h x y).trans (hS x y))
  rw [valueEq_eq (reflect_at hV name), valueEq_eq (reflect_at hW name)]
  exact (hR _ _).mpr (reflectDescriptor_related_of_same hde name)

/-- Decoding related universe members supplies both element codes and
their transport; raw equality of the two type images is not required. -/
theorem universe_transport {k : Option Nat} {V W : Value}
    (h : UniversePER k V W) :
    ∃ R S : Relation, Code k V R ∧ Code k W S ∧ Same R S := by
  obtain ⟨d, e, hd, hde, hv, hw⟩ := h
  exact ⟨El d, El e,
    ⟨d, hd, hv, fun _ _ => Iff.rfl⟩,
    ⟨e, (related_level hde).symm.trans hd, hw, fun _ _ => Iff.rfl⟩,
    related_el hde⟩

theorem el_transport {k l m : Option Nat} {V W : Value} {R S : Relation}
    (hv : Code l V R) (hw : Code m W S) (h : UniversePER k V W) : Same R S := by
  obtain ⟨T, U, ht, hu, htu⟩ := universe_transport h
  exact fun x y => (code_coherent hv ht x y).trans
    ((htu x y).trans (code_coherent hu hw x y))

theorem reflection_related {k : Option Nat} {V W : Value}
    (h : UniversePER k V W) (name : Nat) :
    ∃ R S : Relation, Code k V R ∧ Code k W S ∧ Same R S ∧
      R (reflect V name) (reflect W name) := by
  obtain ⟨d, e, hd, hde, hv, hw⟩ := h
  refine ⟨El d, El e, ⟨d, hd, hv, fun _ _ => Iff.rfl⟩,
    ⟨e, (related_level hde).symm.trans hd, hw, fun _ _ => Iff.rfl⟩,
    related_el hde, ?_⟩
  rw [valueEq_eq (reflect_at hv name), valueEq_eq (reflect_at hw name)]
  cases d <;> cases e <;> simp only [Related] at hde
  all_goals try exact hde.elim
  · exact reflectDescriptor_member (.neutralType _ _) name
  · exact reflectDescriptor_member (.proof _) name
  · subst_vars
    exact reflectDescriptor_member (.univ _) name

def annSemantics (image : Valuation → LCtxA → EnvI → ExprA → Value)
    (sort_image : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l)) :
    AnnSemantics where
  toCodeSystem := codeSystem
  image := image
  sort_image := sort_image

/-- An actual NeutralSupport supplier for the constructed code system,
uniform in the attached source image. No fundamental statement is used. -/
def neutralSupport (image : Valuation → LCtxA → EnvI → ExprA → Value)
    (sort_image : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l)) :
    NeutralExtraction.NeutralSupport (annSemantics image sort_image) where
  decode := decode
  reflect := reflect
  reflect_member := reflect_member

def nativeSemantics (image : Valuation → LCtx → EnvI → Expr Nat → Value)
    (sort_image : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l)) :
    NativeSemantics where
  toCodeSystem := codeSystem
  image := image
  sort_image := sort_image

def nativeNeutralSupport (image : Valuation → LCtx → EnvI → Expr Nat → Value)
    (sort_image : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l)) :
    NeutralExtraction.NativeNeutralSupport (nativeSemantics image sort_image) where
  decode := decode
  reflect := reflect
  reflect_member := reflect_member

/-- Distinct observed neutral type names are related codes. This tests
transport across different values rather than only same-value coherence. -/
theorem distinct_related_neutral_codes (k : Option Nat) :
    (¬ ValueEq (reify (.neutralType k 0)) (reify (.neutralType k 1))) ∧
    UniversePER k (reify (.neutralType k 0)) (reify (.neutralType k 1)) ∧
    Same (El (.neutralType k 0)) (El (.neutralType k 1)) := by
  refine ⟨?_, ⟨.neutralType k 0, .neutralType k 1, rfl, rfl,
    ValueEq.refl _, ValueEq.refl _⟩, fun _ _ => Iff.rfl⟩
  intro h
  have hd := reify_injective h
  cases hd

end Rcic.Declarative.Ann.LR3.NeutralCodes
