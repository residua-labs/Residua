import rcic.RcicAnnLR3ContentJ

/-!
# Boundary: exact-image universes reject families over non-discrete indices

In the content model (`ContentCodes`), a universe relates two raw values
exactly when both are the image of one closed code. Eq codes retain their
indices in their images, which content needs: image-keyed coherence would
otherwise force `Eq A a a` and `Eq A a b` to have the same reading.

**`exact_universe_rejects_family` (all premises constructed).** Let `P` be
the opaque proposition `neutral 0 0`; its reading relates any two neutral
values, so the distinct atoms `0` and `1` are related (`atoms_related`).
The family `λ (x : P). Eq P x x` has, at each argument, the image of a
closed, kinded Eq code (`fam_fibre_type`), so each fibre is a type. Yet its
raw value is not related to itself by the reading of `P → Prop`: at the
related atoms the two fibres are `Eq P 0 0` and `Eq P 1 1`, whose images
differ, so no single code has both images.

The same happens for every index type whose reading relates raw-distinct
values: proofs (irrelevance), functions (extensionality), opaque types. In
particular the motive of J at a large codomain may mention the proof `h`.

**What this rules out.** A Fundamental theorem for the content model in which
type-valued terms are related by the universe's reading. Making the universe
relate types "up to related indices" needs the reading of the index types
inside the universe's reading, which is circular through impredicative
`Prop` (a level-zero product over a universe, an Eq over a kind). A universe
reading that relates any two types (Girard's guard) makes Eq over a universe
contentless (`Eq Prop P Q` inhabited for all `P Q`), which is unsound for J
at a large motive. The standard repair is two-level: an index interpretation
in which related values are equal (proof-irrelevant and extensional, as in
Werner's set-theoretic model), with candidates indexed by it. The raw
evaluator image is not such an interpretation. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ContentUniverseBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open TypeZeroTowerProbe (withBot)
open CandidateTowerProbe (REnv rcons)
open CandidateTowerCoherence (applyValue_legalGraph_at)
open ContentCodes ContentJ

/-- The fibre `Eq P x x` of the family, with `x` bound at slot zero. -/
def famBody (r : Nat) : DCode 0 := .eq r (.neutral 0 0) (wb 0) (wb 0)

/-- The raw value of `λ (x : P). Eq P x x`. -/
def famVal (r : Nat) (σ : REnv) : Value :=
  UnifiedPi.legalGraph (fun _ _ => True) (fun x => image (rcons x σ) (famBody r))

theorem famBody_kinded (r : Nat) (κ : List (Option (Nat × Nat))) : Kinded κ (famBody r) :=
  ⟨(by decide : (0 : Nat) ≠ 11), wb_tok 0, wb_tok 0⟩

theorem fam_fibre (r : Nat) (σ : REnv) {x : Value} (hx : x .bot) :
    ValueEq (NeutralPi.applyValue (famVal r σ) x)
      (eqImage r (image σ (DCode.neutral 0 0)) x x) := by
  have h := applyValue_legalGraph_at (codomain_finite (famBody r) [] (famBody_kinded r []) σ)
    (x := x) (image_bot _ (famBody r))
  refine h.trans ?_
  show ValueEq (eqImage r (image (rcons x σ) (DCode.neutral 0 0)) (withBot x) (withBot x)) _
  rw [withBot_id hx]
  exact ValueEq.refl _

/-- Every fibre is the image of a closed, kinded content code. -/
theorem fam_fibre_type (r : Nat) (σ : REnv) {x : Value} (hx : x .bot) :
    ∃ c : DCode 0, WFc c ∧ ValueEq (NeutralPi.applyValue (famVal r σ) x) (image σ c) :=
  ⟨.eq r (.neutral 0 0) (fun _ => x) (fun _ => x),
    ⟨⟨(by decide : (0 : Nat) ≠ 11), const_tok hx, const_tok hx⟩,
      ⟨trivial, fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩,
    fam_fibre r σ hx⟩

/-- The opaque proposition relates two distinct atoms. -/
theorem atoms_related (σ : REnv) (ρ : FEnv) :
    El σ ρ (DCode.neutral 0 0) (NeutralPER.neutralAtom 0) (NeutralPER.neutralAtom 1) :=
  ⟨.atom 0, .atom 1⟩

theorem atoms_distinct : NeutralPER.neutralAtom 0 ≠ NeutralPER.neutralAtom 1 := by
  intro h
  rw [atom_spineVal, atom_spineVal] at h
  have h' : ValueEq (spineVal 0 []) (spineVal 1 []) := by
    rw [h]
    exact ValueEq.refl _
  have := (spineVal_inj (xs := []) (ys := []) (fun _ hx => by cases hx)
    (fun _ hx => by cases hx) h').1
  cases this

/-- **Boundary.** The family `λ (x : P). Eq P x x`, each of whose fibres is a
type, is not related to itself by the reading of `P → Prop`. -/
theorem exact_universe_rejects_family (r : Nat) (σ : REnv) (ρ : FEnv) :
    ¬ El σ ρ (DCode.pi (.neutral 0 0) (.univ 0)) (famVal r σ) (famVal r σ) := by
  rintro ⟨_, _, h⟩
  obtain ⟨⟨c, _, h1, h2⟩, _⟩ := h _ _ (atoms_related σ ρ) emptyFam emptyFam_sat trivial
  have e := (fam_fibre r σ (atom_bot 0)).symm.trans
    (h1.trans (h2.symm.trans (fam_fibre r σ (atom_bot 1))))
  unfold eqImage at e
  rw [applyAll_atom, applyAll_atom] at e
  have hb : ∀ (n : Nat), ∀ x ∈ [image σ (DCode.neutral 0 0), NeutralPER.neutralAtom n,
      NeutralPER.neutralAtom n], x .bot := by
    intro n x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact image_bot _ _
    · exact atom_bot n
    · exact atom_bot n
  have hl := (spineVal_inj (hb 0) (hb 1) (tagged_inj (Or.inl rfl) e).2).2
  injection hl with _ hl
  injection hl with hl _
  exact atoms_distinct hl

end Rcic.Declarative.Ann.LR3.ContentUniverseBoundary
