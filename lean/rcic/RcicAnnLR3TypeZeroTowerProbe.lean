import rcic.RcicAnnLR3InductiveCodes
import rcic.RcicAnnLR3UnifiedPi
import rcic.RcicAnnLR3RCodeSoundPiControl

/-!
# Probe: a level-indexed code tower with dependent Pi in Type 0

The design rule under test: codes are data, an inductive family
`Code : Nat → Type` indexed by the object level, and all semantics are PERs
on raw values, `Value → Value → Prop`. There is no Type-valued
interpretation of codes.

**(i) Size.** `Code k : Type` for every object level `k`, so the type of all
codes at all levels, `Σ k, Code k`, is again in `Type 0` (`AllCodes`). The
raw image and the interpretation are structural recursions into `Value` and
`Prop`; neither depends on the object level, and no host universe is raised.
The Pi constructor quantifies over raw values, `B : Value → Code b`, which is
strictly positive. It also records the raw fibre-image function `F`; its
image is the evaluator's graph of `F`, and well-formedness asks `F` to agree
with the fibre images on domain members.

**(ii) Definability.** The level `k+1` universe code's PER relates the raw
images of level-`k` codes. The Pi code's PER is the pointwise function
relation of its domain and fibres. Decoding a universe element as a type is
also defined from the level-`k` interpretation (`ElU`). Every interpretation
satisfies the PER laws (`el_laws`), by structural recursion on codes. A
dependent function relates its applications in the fibres at both related
arguments, so no respect premise is needed, and well-formedness is a
condition on raw images only. Neither interpretation uses a Type-valued El.

**(iii) Unfolding.** The interpretation unfolds by `rfl` on closed universe
and Pi codes. A closed neutral function is proved a member by `simp only [El]`.

**Answer: yes for (i)–(iii).** Coherence of `ElU` is also proved for the
generators. Well-formed Pi codes require their raw fibre-image function to
have finite demand in the raw argument, which the evaluator's bodies satisfy
through `body_legalFiniteDemand`, and to agree with the fibre images on
domain members. Every image is tagged with its object level and a
payload. Universe, native neutral and Pi payloads are pairwise separated by
concrete compacts. `piValue_injective` together with `applyValue_legalGraph`
recovers the domain image and every fibre image. Hence `coherent`: equal raw
images of well-formed codes give the same PER, at any two levels. Then
`elU_laws` holds: decoding universe elements is a PER.

**Neutral types (R5).** `ntype k v` codes have a level-tagged neutral payload.
The universe relation also relates all neutral type images of its level, and
neutral and `ntype` codes share one relation (all neutrals related). This is
coarse but enough for sort membership. It lets reflected neutral type
families be members of their products (see `NeutralReflectionProbe`).
Coherence covers the new cases. `ntype` payloads are required to be
head-11-free, so they are never sort payloads. Function relations require
the bottom observation, so every member of every code is nonempty.

Still outside this probe are readings that depend on retained, non-raw
bindings, where the open-Eq retained separation shows raw-image keying is
insufficient, and the remaining code formers (guarded, inductive, Eq).
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.TypeZeroTowerProbe

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- The object-level product index: impredicative at zero. -/
def imaxN (a b : Nat) : Nat := if b = 0 then 0 else max a b

/-- Codes are data, indexed by the object level. -/
inductive Code : Nat → Type
  | univ (k : Nat) : Code (k + 1)
  | neutral (k name : Nat) : Code k
  | ntype (k : Nat) (v : Value) : Code k
  | pi {a b : Nat} (A : Code a) (F : Value → Value) (B : Value → Code b) : Code (imaxN a b)

/-- (i) All codes at all object levels form one Type-0 type. -/
abbrev AllCodes : Type := (k : Nat) × Code k

def bigUniverse : AllCodes := ⟨1001, .univ 1000⟩

/-- A value with the bottom observation added. -/
def withBot (v : Value) : Value := fun c => c = .bot ∨ v c

/-- The tag payload of `Sort j`. -/
def sortPayload (j : Option Nat) : Value := denI EnvI.bot (.app (.const 11 []) (levelTerm j))

/-- The raw type image, by structural recursion. -/
def image : {k : Nat} → Code k → Value
  | _, .univ k => universeValue (some k)
  | _, .neutral k name => NativeMemberValues.value (some k) name
  | _, .ntype k v => InductiveCodes.taggedValue (some k) (withBot v)
  | _, @Code.pi a b A F _ => InductiveCodes.piValue (some (imaxN a b)) (image A)
      (UnifiedPi.legalGraph (fun _ _ => True) F)

/-- No observation of the payload is headed by the sort tag 11. -/
def Head11Free (v : Value) : Prop := ∀ args, ¬ v (.spine 11 args)

/-- A level-tagged neutral type image with a head-11-free neutral payload. -/
def NeutralImage (k : Nat) (V : Value) : Prop :=
  ∃ v, CandidatePi.Neutral v ∧ Head11Free v ∧ ValueEq V (image (Code.ntype k v))

/-- Well-formedness is a condition on raw images only: the raw fibre-image
function has finite demand and bottom and agrees with every fibre image, and
neutral payloads are neutral and not sort payloads. It does not mention the
interpretation, so universes can range over well-formed codes. -/
inductive WF : {k : Nat} → Code k → Prop
  | univ (k : Nat) : WF (.univ k)
  | neutral (k name : Nat) : WF (.neutral k name)
  | ntype (k : Nat) (v : Value) (hv : CandidatePi.Neutral v)
      (hfree : Head11Free v) : WF (.ntype k v)
  | pi {a b : Nat} {A : Code a} {F : Value → Value} {B : Value → Code b}
      (hA : WF A) (hB : ∀ x, WF (B x))
      (finite : UnifiedPi.LegalFiniteDemand (fun _ _ => True) F)
      (bot : ∀ x, F x .bot)
      (fibre : ∀ x, ValueEq (image (B x)) (F x)) :
      WF (.pi A F B)

/-- (ii) The interpretation: a PER on raw values for every code. The universe
relates images of one well-formed code, and relates all neutral type images of
its level (neutral types share one relation). A dependent function relates
its applications in the fibres at both related arguments, so it is a PER
without a respect premise. -/
def El : {k : Nat} → Code k → Value → Value → Prop
  | _, .univ k, V, W => (∃ c : Code k, WF c ∧ ValueEq V (image c) ∧ ValueEq W (image c)) ∨
      (NeutralImage k V ∧ NeutralImage k W)
  | _, .neutral _ _, x, y => CandidatePi.Neutral x ∧ CandidatePi.Neutral y
  | _, .ntype _ _, x, y => CandidatePi.Neutral x ∧ CandidatePi.Neutral y
  | _, .pi A _ B, f, g => f .bot ∧ g .bot ∧ ∀ x y, El A x y →
      El (B x) (NeutralPi.applyValue f x) (NeutralPi.applyValue g y) ∧
      El (B y) (NeutralPi.applyValue f x) (NeutralPi.applyValue g y)

/-! ## (iii) Unfolding on closed examples -/

theorem el_univ_unfold (V W : Value) :
    El (Code.univ 0) V W = ((∃ c : Code 0, WF c ∧ ValueEq V (image c) ∧ ValueEq W (image c)) ∨
      (NeutralImage 0 V ∧ NeutralImage 0 W)) := rfl

theorem el_pi_unfold (f g : Value) :
    El (Code.pi (Code.neutral 1 5) (fun _ => universeValue (some 0)) (fun _ => Code.univ 0)) f g =
      (f .bot ∧ g .bot ∧ ∀ x y, El (Code.neutral 1 5) x y →
        El (Code.univ 0) (NeutralPi.applyValue f x) (NeutralPi.applyValue g y) ∧
        El (Code.univ 0) (NeutralPi.applyValue f x) (NeutralPi.applyValue g y)) := rfl

theorem image_univ_unfold : image (Code.univ 1000) = universeValue (some 1000) := rfl

theorem pi_level_unfold : imaxN 3 0 = 0 ∧ imaxN 3 2 = 3 := ⟨rfl, rfl⟩

/-- The universe at level 2 contains the code of Sort 0. -/
theorem universe_contains_lower :
    El (Code.univ 1) (image (Code.univ 0)) (image (Code.univ 0)) :=
  Or.inl ⟨Code.univ 0, WF.univ 0, ValueEq.refl _, ValueEq.refl _⟩

/-- A closed dependent-Pi membership proved by unfolding: a neutral function
between neutral types at level zero. -/
theorem neutral_function_member (head : Nat) :
    El (Code.pi (Code.neutral 0 1) (fun _ => NativeMemberValues.value (some 0) 2)
      (fun _ => Code.neutral 0 2))
      (NeutralPER.neutralAtom head) (NeutralPER.neutralAtom head) := by
  refine ⟨.bot _ _, .bot _ _, ?_⟩
  rintro x y ⟨hx, hy⟩
  have h : CandidatePi.Neutral (NeutralPi.applyValue (NeutralPER.neutralAtom head) x) ∧
      CandidatePi.Neutral (NeutralPi.applyValue (NeutralPER.neutralAtom head) y) :=
    ⟨.app (.atom head) x (CandidatePi.neutral_nonempty hx),
      .app (.atom head) y (CandidatePi.neutral_nonempty hy)⟩
  exact ⟨h, h⟩

/-! ## (ii) PER laws for every code -/

theorem neutralImage_congr {k : Nat} {V W : Value} (h : ValueEq V W)
    (hW : NeutralImage k W) : NeutralImage k V := by
  obtain ⟨v, hv, hns, hW⟩ := hW
  exact ⟨v, hv, hns, h.trans hW⟩

/-- Every interpretation is a PER; no well-formedness is needed. -/
theorem el_laws : {k : Nat} → (c : Code k) → Laws (El c)
  | _, .univ k => by
      refine ⟨?_, ?_⟩
      · rintro V W (⟨c, hc, hv, hw⟩ | ⟨hV, hW⟩)
        · exact Or.inl ⟨c, hc, hw, hv⟩
        · exact Or.inr ⟨hW, hV⟩
      · rintro V W Z (⟨c, hc, hv, hw⟩ | ⟨hV, hW⟩) (⟨d, hd, hw', hz⟩ | ⟨hW', hZ⟩)
        · exact Or.inl ⟨c, hc, hv, hz.trans (hw'.symm.trans hw)⟩
        · exact Or.inr ⟨neutralImage_congr (hv.trans hw.symm) hW', hZ⟩
        · exact Or.inr ⟨hV, neutralImage_congr (hz.trans hw'.symm) hW⟩
        · exact Or.inr ⟨hV, hZ⟩
  | _, .neutral _ _ => ⟨fun ⟨hx, hy⟩ => ⟨hy, hx⟩, fun ⟨hx, _⟩ ⟨_, hz⟩ => ⟨hx, hz⟩⟩
  | _, .ntype _ _ => ⟨fun ⟨hx, hy⟩ => ⟨hy, hx⟩, fun ⟨hx, _⟩ ⟨_, hz⟩ => ⟨hx, hz⟩⟩
  | _, .pi A _ B => by
      have lA := el_laws A
      refine ⟨?_, ?_⟩
      · rintro f g ⟨hf, hg, hfg⟩
        refine ⟨hg, hf, fun x y hxy => ?_⟩
        obtain ⟨h1, h2⟩ := hfg y x (lA.symm hxy)
        exact ⟨(el_laws (B x)).symm h2, (el_laws (B y)).symm h1⟩
      · rintro f g h ⟨hf, _, hfg⟩ ⟨_, hh, hgh⟩
        refine ⟨hf, hh, fun x y hxy => ?_⟩
        have hxx := lA.trans hxy (lA.symm hxy)
        have hyy := lA.trans (lA.symm hxy) hxy
        exact ⟨(el_laws (B x)).trans (hfg x x hxx).1 (hgh x y hxy).1,
          (el_laws (B y)).trans (hfg x y hxy).2 (hgh y y hyy).2⟩

/-! ## Image coherence for the generators -/

/-- The tag payload of each code's raw image. -/
def payload : {k : Nat} → Code k → Value
  | _, .univ k => denI EnvI.bot (.app (.const 11 []) (levelTerm (some k)))
  | _, .neutral _ name => NeutralPER.neutralAtom name
  | _, .ntype _ v => withBot v
  | _, @Code.pi a b A F _ => InductiveCodes.piPayload (image A)
      (UnifiedPi.legalGraph (fun _ _ => True) F)

theorem image_tagged : {k : Nat} → (c : Code k) →
    ValueEq (image c) (InductiveCodes.taggedValue (some k) (payload c))
  | _, .univ k => (InductiveCodes.taggedValue_denI EnvI.bot (some (k+1)) _).symm
  | _, .neutral k name => (InductiveCodes.taggedValue_denI EnvI.bot (some k) (.const name [])).symm
  | _, .ntype _ _ => ValueEq.refl _
  | _, .pi _ _ _ => ValueEq.refl _

theorem image_bot {k : Nat} (c : Code k) : image c .bot :=
  ((image_tagged c) .bot).mpr (Or.inl rfl)

theorem tagged_level (k : Option Nat) (P : Value) :
    SortMember k (InductiveCodes.taggedValue k P) := by
  rintro c (rfl | ⟨a, p, rfl, ha, _⟩)
  · exact .bot
  · exact .tagged a p ha

theorem image_level : {k : Nat} → (c : Code k) → SortMember (some k) (image c)
  | _, .univ k => sort_member _ (some k)
  | _, .neutral k name => NativeMemberValues.value_level (some k) name
  | _, .ntype k _ => tagged_level _ _
  | _, .pi _ _ _ => InductiveCodes.piValue_level _ _ _

theorem image_defined : {k : Nat} → (c : Code k) → TypeDefined (image c)
  | _, .univ k => sort_defined _ (some k)
  | _, .neutral k name => NativeMemberValues.value_defined (some k) name
  | _, .ntype k _ => ⟨some k, .bot, (InductiveCodes.taggedValue_full _ _ _).mpr (Or.inl rfl)⟩
  | _, .pi _ _ _ => InductiveCodes.piValue_defined _ _ _

theorem level_eq {k l : Nat} {c : Code k} {d : Code l} (h : ValueEq (image c) (image d)) :
    k = l :=
  Option.some.inj (sortMember_unique (image_level c) (sortMember_congr h.symm (image_level d))
    (image_defined c))

/-- Equal images have equal tag payloads. -/
theorem payload_eq {k l : Nat} {c : Code k} {d : Code l} (h : ValueEq (image c) (image d))
    (p : CptI) : payload c p ↔ payload d p := by
  have hkl := level_eq h
  subst hkl
  have he := ((image_tagged c).symm.trans (h.trans (image_tagged d))) (NeutralCodes.fullTag (some k) p)
  exact (InductiveCodes.taggedValue_full _ _ _).symm.trans (he.trans (InductiveCodes.taggedValue_full _ _ _))

theorem univ_payload_inv {k : Nat} {p : CptI}
    (h : payload (Code.univ k) p) : p = .bot ∨ ∃ u, p = .spine 11 [u] := by
  rcases approxI_app_inv h with hb | ⟨g, _, _, hf, _, _⟩ | ⟨r, args, u, he, hf, _⟩
  · exact Or.inl hb
  · rcases approxI_const_inv hf with h | h <;> cases h
  · rcases approxI_const_inv hf with h | h
    · cases h
    · cases h
      exact Or.inr ⟨u, he⟩

theorem neutral_payload_inv {k name : Nat} {p : CptI}
    (h : payload (Code.neutral k name) p) : p = .bot ∨ p = .spine name [] :=
  approxI_const_inv h

theorem pi_payload_obs {a b : Nat} (A : Code a) (F : Value → Value) (B : Value → Code b) :
    payload (Code.pi A F B) (.pi .bot []) :=
  Or.inr ⟨.bot, [], rfl, image_bot A, by simp⟩

theorem not_univ_neutral {k l name : Nat} :
    ¬ ValueEq (image (Code.univ k)) (image (Code.neutral l name)) := by
  intro h
  rcases univ_payload_inv ((payload_eq h (.spine name [])).mpr (.const _ _ _)) with h | ⟨_, h⟩
    <;> cases h

theorem not_pi_other {a b l : Nat} {A : Code a} {F : Value → Value} {B : Value → Code b}
    {d : Code l}
    (hd : ∀ p, payload d p → p = .bot ∨ ∃ r args, p = .spine r args)
    (h : ValueEq (image (Code.pi A F B)) (image d)) : False := by
  rcases hd _ ((payload_eq h _).mp (pi_payload_obs A F B)) with h | ⟨_, _, h⟩ <;> cases h

theorem univ_spine {k : Nat} (p : CptI) (h : payload (Code.univ k) p) :
    p = .bot ∨ ∃ r args, p = .spine r args := by
  rcases univ_payload_inv h with h | ⟨u, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨11, [u], h⟩

theorem neutral_spine {k name : Nat} (p : CptI) (h : payload (Code.neutral k name) p) :
    p = .bot ∨ ∃ r args, p = .spine r args := by
  rcases neutral_payload_inv h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨name, [], h⟩

theorem ntype_spine {k : Nat} {v : Value} (hv : CandidatePi.Neutral v) (p : CptI)
    (h : payload (Code.ntype k v) p) : p = .bot ∨ ∃ r args, p = .spine r args := by
  rcases h with h | h
  · exact Or.inl h
  · rcases CandidatePi.neutral_spineOnly hv p h with h | ⟨r, args, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, args, h⟩

theorem not_univ_ntype {k l : Nat} {v : Value} (hfree : Head11Free v)
    (h : ValueEq (image (Code.univ k)) (image (Code.ntype l v))) : False := by
  have hs : payload (Code.univ k) (.spine 11 [.bot]) :=
    .appSpine (args := []) (.const _ _ _) (.bot _ _)
  rcases (payload_eq h _).mp hs with hb | hv
  · cases hb
  · exact hfree _ hv

/-- Image coherence: on well-formed codes, equal raw images give the same
PER, at any two object levels. -/
theorem coherent : {k : Nat} → {c : Code k} → WF c →
    {l : Nat} → (d : Code l) → WF d → ValueEq (image c) (image d) → Same (El c) (El d) := by
  intro k c hc
  induction hc with
  | univ k =>
      intro l d hd h
      cases d with
      | univ j =>
          have hj : some k = some j := sort_code_injective h
          cases hj
          exact fun _ _ => Iff.rfl
      | neutral _ name => exact (not_univ_neutral h).elim
      | ntype _ v =>
          cases hd with
          | ntype _ _ _ hfree => exact (not_univ_ntype hfree h).elim
      | pi A F B => exact (not_pi_other (fun p hp => univ_spine p hp) h.symm).elim
  | neutral k name =>
      intro l d hd h
      cases d with
      | univ j => exact (not_univ_neutral h.symm).elim
      | neutral _ _ => exact fun _ _ => Iff.rfl
      | ntype _ _ => exact fun _ _ => Iff.rfl
      | pi A F B => exact (not_pi_other (fun p hp => neutral_spine p hp) h.symm).elim
  | ntype k v hv hfree =>
      intro l d hd h
      cases d with
      | univ j => exact (not_univ_ntype hfree h.symm).elim
      | neutral _ _ => exact fun _ _ => Iff.rfl
      | ntype _ _ => exact fun _ _ => Iff.rfl
      | pi A F B => exact (not_pi_other (fun p hp => ntype_spine hv p hp) h.symm).elim
  | @pi a b A F B hA hB finite bot fibre ihA ihB =>
      intro l d hd h
      cases hd with
      | univ j => exact (not_pi_other (fun p hp => univ_spine p hp) h).elim
      | neutral _ name => exact (not_pi_other (fun p hp => neutral_spine p hp) h).elim
      | ntype _ _ hv _ => exact (not_pi_other (fun p hp => ntype_spine hv p hp) h).elim
      | @pi a' b' A' F' B' hA' hB' finite' bot' fibre' =>
          obtain ⟨_, hdom, hcod⟩ := InductiveCodes.piValue_injective (image_bot A) (image_bot A') h
          have hF : ∀ x, ValueEq (F x) (F' x) := fun x =>
            (UnifiedPi.applyValue_legalGraph (fun y _ => bot y) finite
              (x := x) True.intro).symm.trans ((hcod x).trans
              (UnifiedPi.applyValue_legalGraph (fun y _ => bot' y) finite'
                (x := x) True.intro))
          have sA := ihA A' hA' hdom
          have sB : ∀ x, Same (El (B x)) (El (B' x)) := fun x =>
            ihB x (B' x) (hB' x) ((fibre x).trans ((hF x).trans (fibre' x).symm))
          intro f g
          constructor
          · rintro ⟨hf, hg, hfg⟩
            refine ⟨hf, hg, fun x y hxy => ?_⟩
            obtain ⟨h1, h2⟩ := hfg x y ((sA x y).mpr hxy)
            exact ⟨(sB x _ _).mp h1, (sB y _ _).mp h2⟩
          · rintro ⟨hf, hg, hfg⟩
            refine ⟨hf, hg, fun x y hxy => ?_⟩
            obtain ⟨h1, h2⟩ := hfg x y ((sA x y).mp hxy)
            exact ⟨(sB x _ _).mpr h1, (sB y _ _).mpr h2⟩

/-- Decoding a universe element as a well-formed type, from the level-`k`
interpretation. -/
def ElU (k : Nat) (V x y : Value) : Prop :=
  ∃ c : Code k, WF c ∧ ValueEq V (image c) ∧ El c x y

/-- With coherence proved, decoding is a PER for every type value. -/
theorem elU_laws (k : Nat) (V : Value) : Laws (ElU k V) := by
  refine ⟨?_, ?_⟩
  · rintro x y ⟨c, hc, hv, hxy⟩
    exact ⟨c, hc, hv, (el_laws c).symm hxy⟩
  · rintro x y z ⟨c, hc, hv, hxy⟩ ⟨d, hd, hw, hyz⟩
    have hs := coherent hd c hc (hw.symm.trans hv)
    exact ⟨c, hc, hv, (el_laws c).trans hxy ((hs y z).mp hyz)⟩

end Rcic.Declarative.Ann.LR3.TypeZeroTowerProbe
