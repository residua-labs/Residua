import rcic.RcicAnnLR3TypeZeroTowerProbe
import rcic.RcicAnnLR3OptionSoundUniverse

/-!
# The Type-0 tower as an Option-indexed raw code system

This module puts the level-indexed data tower of `TypeZeroTowerProbe` and
the ordinary none algebra of `OptionSoundUniverse` together into one
`CodeSystem` over all Option levels.

At a finite level `k`, the raw value `V` has the relation of every
well-formed level-`k` code with image `V`, namely the decoded relation
`ElU k V`. `TowerCode` records this together with the existence of some code
with image `V`. Image coherence makes this one relation, so the system is
image-coherent by construction and contains dependent products and universes
at every Nat level. The universe relation at `k` is the actual universe
code's relation (images of level-`k` codes). At `none`, the system is the
ordinary none algebra: the self-containing universe plus chaotic ordinary
none types.

Supplied: every `CodeSystem` field, `UniverseTransport` (actual codes for
both sides of every universe edge), `PropIrrelevance` (well-formed level-zero
codes are proof-irrelevant), and the original `Ty_sort` over the attached
`EnvironmentEval` semantics for any environment pair. Everything lives in
`Type 0`/`Prop`. No source evaluator, reader, or remaining arm is claimed.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.TowerCodeSystem

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open TypeZeroTowerProbe

/-! ## Decoding agrees with every well-formed code -/

theorem elU_of_wf {k : Nat} {c : Code k} (hc : WF c) {V : Value}
    (hV : ValueEq V (image c)) : Same (ElU k V) (El c) := by
  intro x y
  constructor
  · rintro ⟨d, hd, hVd, hxy⟩
    exact (coherent hd c hc (hVd.symm.trans hV) x y).mp hxy
  · intro h
    exact ⟨c, hc, hV, h⟩

theorem elU_congr {k : Nat} {V W : Value} (h : ValueEq V W) : Same (ElU k V) (ElU k W) := by
  rw [NeutralCodes.valueEq_eq h]
  exact fun _ _ => Iff.rfl

theorem imaxN_zero {a b : Nat} (h : imaxN a b = 0) : b = 0 := by
  by_cases hb : b = 0
  · exact hb
  · unfold imaxN at h
    rw [if_neg hb] at h
    have hle := Nat.le_max_right a b
    omega

/-- Well-formed level-zero codes are proof-irrelevant. -/
theorem el_irrelevant {k : Nat} {c : Code k} (hc : WF c) (hk : k = 0) {x y : Value}
    (hx : El c x x) (hy : El c y y) : El c x y := by
  induction hc generalizing x y with
  | univ j => exact (Nat.succ_ne_zero j hk).elim
  | neutral j name => exact ⟨hx.1, hy.1⟩
  | ntype j v _ _ => exact ⟨hx.1, hy.1⟩
  | @pi a b A F B hA hB _ _ _ _ ihB =>
      have hb : b = 0 := imaxN_zero hk
      obtain ⟨hxb, _, hx⟩ := hx
      obtain ⟨_, hyb, hy⟩ := hy
      refine ⟨hxb, hyb, fun u v huv => ?_⟩
      have lA := el_laws A
      have hvu := lA.symm huv
      -- left members of each fibre
      have hxu : El (B u) (NeutralPi.applyValue x u) (NeutralPi.applyValue x u) :=
        (hx u u (lA.trans huv hvu)).1
      have hxv : El (B v) (NeutralPi.applyValue x u) (NeutralPi.applyValue x u) := by
        have h := (hx u v huv).2
        exact (el_laws (B v)).trans h ((el_laws (B v)).symm h)
      have hyu : El (B u) (NeutralPi.applyValue y v) (NeutralPi.applyValue y v) := by
        have h := (hy v u hvu).2
        exact (el_laws (B u)).trans h ((el_laws (B u)).symm h)
      have hyv : El (B v) (NeutralPi.applyValue y v) (NeutralPi.applyValue y v) :=
        (hy v v (lA.trans hvu huv)).1
      exact ⟨ihB u hb hxu hyu, ihB v hb hxv hyv⟩

/-! ## The Option-indexed system -/

def TowerCode (k : Nat) (V : Value) (R : Relation) : Prop :=
  (∃ c : Code k, WF c ∧ ValueEq V (image c)) ∧ Same R (ElU k V)

def Code' : Option Nat → Value → Relation → Prop
  | none, V, R => OptionSoundUniverse.NoneRawCode V R
  | some k, V, R => TowerCode k V R

def UniversePER : Option Nat → Relation
  | none => OptionSoundUniverse.NoneUniversePER
  | some k => El (Code.univ k)

theorem code_lawful {k : Option Nat} {V : Value} {R : Relation} (h : Code' k V R) : Laws R := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_lawful.{0} (k := none) h
  | some k => exact NeutralControls.laws_of_same h.2 (elU_laws k V)

theorem code_level {k : Option Nat} {V : Value} {R : Relation} (h : Code' k V R) :
    SortMember k V := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_level.{0} (k := none) h
  | some k =>
      obtain ⟨⟨c, _, hV⟩, _⟩ := h
      exact sortMember_congr hV.symm (image_level c)

theorem code_defined {k : Option Nat} {V : Value} {R : Relation} (h : Code' k V R) :
    TypeDefined V := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_defined.{0} (k := none) h
  | some k =>
      obtain ⟨⟨c, _, hV⟩, _⟩ := h
      exact typeDefined_congr hV.symm (image_defined c)

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : Code' k V R) (g : Code' l V S) : Same R S := by
  have hkl := sortMember_unique (code_level h) (code_level g) (code_defined h)
  cases hkl
  cases k with
  | none => exact OptionSoundUniverse.rawCode_coherent.{0} (k := none) (l := none) h g
  | some k => exact fun x y => (h.2 x y).trans (g.2 x y).symm

theorem universe_code (k : Option Nat) :
    Code' (k.map Nat.succ) (universeValue k) (UniversePER k) := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_universe.{0} none
  | some k =>
      exact ⟨⟨Code.univ k, WF.univ k, ValueEq.refl _⟩,
        fun x y => ((elU_of_wf (WF.univ k) (ValueEq.refl _)) x y).symm⟩

theorem universe_member (k : Option Nat) :
    Member (UniversePER (k.map Nat.succ)) (universeValue k) := by
  cases k with
  | none => exact OptionSoundUniverse.rawUniverse_member.{0} none
  | some k => exact Or.inl ⟨Code.univ k, WF.univ k, ValueEq.refl _, ValueEq.refl _⟩

theorem universe_elim {k l : Option Nat} {R : Relation} {x : Value}
    (h : Code' l (universeValue k) R) (hx : Member R x) : SortMember k x ∧ TypeDefined x := by
  have hu : Member (UniversePER k) x := (code_coherent h (universe_code k) x x).mp hx
  cases k with
  | none =>
      obtain ⟨a, hx, _⟩ := hu
      exact ⟨sortMember_congr hx.symm (OptionSoundUniverse.noneImage_level a),
        typeDefined_congr hx.symm (OptionSoundUniverse.noneImage_defined a)⟩
  | some k =>
      rcases hu with ⟨c, _, hx, _⟩ | ⟨⟨v, _, _, hx⟩, _⟩
      · exact ⟨sortMember_congr hx.symm (image_level c),
          typeDefined_congr hx.symm (image_defined c)⟩
      · exact ⟨sortMember_congr hx.symm (image_level (Code.ntype k v)),
          typeDefined_congr hx.symm (image_defined (Code.ntype k v))⟩

def codeSystem : CodeSystem where
  Code := Code'
  universePER := UniversePER
  lawful := code_lawful
  defined := code_defined
  level := code_level
  coherent := code_coherent
  universe_code := universe_code
  universe_member := universe_member
  universe_elim := universe_elim

/-- Every universe edge has actual codes on both sides. -/
theorem universeTransport : UniverseTransport codeSystem where
  relate := by
    intro k V W h
    cases k with
    | none =>
        obtain ⟨a, hv, hw⟩ := h
        exact ⟨OptionSoundUniverse.noneElementPER a, OptionSoundUniverse.noneElementPER a,
          ⟨a, hv, fun _ _ => Iff.rfl⟩, ⟨a, hw, fun _ _ => Iff.rfl⟩, fun _ _ => Iff.rfl⟩
    | some k =>
        rcases h with ⟨c, hc, hv, hw⟩ | ⟨⟨v, hv, hnv, hV⟩, ⟨w, hw, hnw, hW⟩⟩
        · exact ⟨ElU k V, ElU k W, ⟨⟨c, hc, hv⟩, fun _ _ => Iff.rfl⟩, ⟨⟨c, hc, hw⟩, fun _ _ => Iff.rfl⟩,
            elU_congr (hv.trans hw.symm)⟩
        · refine ⟨ElU k V, ElU k W, ⟨⟨_, WF.ntype k v hv hnv, hV⟩, fun _ _ => Iff.rfl⟩,
            ⟨⟨_, WF.ntype k w hw hnw, hW⟩, fun _ _ => Iff.rfl⟩, ?_⟩
          intro x y
          exact ((elU_of_wf (WF.ntype k v hv hnv) hV) x y).trans
            ((elU_of_wf (WF.ntype k w hw hnw) hW) x y).symm

/-- Level-zero codes are proof-irrelevant. -/
theorem propIrrelevance : PropIrrelevance codeSystem where
  relate := by
    intro V R x y h hx hy
    obtain ⟨_, hR⟩ := (h : TowerCode 0 V R)
    obtain ⟨c, hc, hV, hxx⟩ := (hR x x).mp hx
    obtain ⟨d, hd, hV', hyy⟩ := (hR y y).mp hy
    have hs := coherent hd c hc (hV'.symm.trans hV)
    exact (hR x y).mpr ⟨c, hc, hV, el_irrelevant hc rfl hxx ((hs y y).mp hyy)⟩

/-- A dependent product at a positive level is a code of the system. -/
theorem pi_code {a b : Nat} {A : Code a} {F : Value → Value} {B : Value → Code b}
    (h : WF (Code.pi A F B)) :
    codeSystem.Code (some (imaxN a b)) (image (Code.pi A F B)) (El (Code.pi A F B)) :=
  ⟨⟨Code.pi A F B, h, ValueEq.refl _⟩, fun x y => ((elU_of_wf h (ValueEq.refl _)) x y).symm⟩

/-! ## The original sort arm over any attached environment -/

theorem ty_sort_supplied (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort (EnvironmentEval.annSemantics codeSystem E F) E I n :=
  fun Γ l => PairedArms.paired_sort_goal _ E I n Γ l

end Rcic.Declarative.Ann.LR3.TowerCodeSystem
