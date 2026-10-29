import rcic.RcicAnnLR3TypeZeroTowerProbe

/-!
# Probe R5: reflected neutral type families need a coarse universe relation

A context variable `P : A → Sort k` must be realized by its reflection. At a
universe the reflection of a neutral `s` is the level-tagged neutral type
`taggedNeutral k s`; at a product it is the legal graph of the reflected
applications. For `P` this is `famReflect k s`, the graph of
`x ↦ taggedNeutral k (s · x)`.

**(a) Continuity.** `x ↦ taggedNeutral k (s · x)` has finite demand and
bottom. So `famReflect k s` applied to any argument is exactly the tagged
neutral application (`famReflect_apply`).

**(b) Boundary for the exact-image universe (the mutant).** The level-zero
neutral code relates the two distinct neutral proofs `atom 1` and `atom 2`,
by irrelevance. The exact-image universe relation `ExactUniverse` (one code
image on both sides) does not relate the two reflected applications, because
their payloads differ. All premises are constructed.
(`exact_universe_rejects_reflection`)

**(c) The coarse relation repairs it.** Relating all level-tagged neutral
types of one level, with one shared element relation, makes the reflected
family a member of the product over every domain whose related elements are
nonempty (`coarse_accepts_reflection`). This coarsening identifies neutral
types only, which is sufficient for sort membership, and decoding stays
coherent because they share one relation. Building it into the tower,
**(d) Integrated.** The tower now carries neutral-payload type codes and the
coarse universe relation; the reflected family is a member of its product
(`tower_accepts_reflection`). Type-directed reflection for every code and
`NeutralSupport` remain the next step. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NeutralReflectionProbe

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

def taggedNeutral (k : Nat) (s : Value) : Value := InductiveCodes.taggedValue (some k) s

def famFibre (k : Nat) (s : Value) : Value → Value :=
  fun x => taggedNeutral k (NeutralPi.applyValue s x)

def famReflect (k : Nat) (s : Value) : Value :=
  UnifiedPi.legalGraph (fun _ _ => True) (famFibre k s)

/-! ## (a) Continuity -/

theorem applyValue_finite (s x : Value) (c : CptI) (h : NeutralPi.applyValue s x c) :
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ y, (∀ u ∈ us, y u) → NeutralPi.applyValue s y c := by
  rcases h with hc | ⟨g, r, hc, hf, hr, ha⟩ | ⟨head, args, u, hc, hf, ha⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hc⟩
  · exact ⟨r.1, ha, fun y hy => Or.inr (Or.inl ⟨g, r, hc, hf, hr, hy⟩)⟩
  · exact ⟨[u], by simpa using ha, fun y hy => Or.inr (Or.inr ⟨head, args, u, hc, hf,
      hy u (by simp)⟩)⟩

theorem famFibre_finite (k : Nat) (s : Value) :
    UnifiedPi.LegalFiniteDemand (fun _ _ => True) (famFibre k s) := by
  intro x _ c hc
  rcases hc with hc | ⟨a, p, he, ha, hp⟩
  · exact ⟨[], by simp, fun y _ _ => Or.inl hc⟩
  · obtain ⟨us, hus, hfin⟩ := applyValue_finite s x p hp
    exact ⟨us, hus, fun y _ hy => Or.inr ⟨a, p, he, ha, hfin y hy⟩⟩

theorem famFibre_bot (k : Nat) (s x : Value) : famFibre k s x .bot := Or.inl rfl

theorem famReflect_apply (k : Nat) (s x : Value) :
    ValueEq (NeutralPi.applyValue (famReflect k s) x) (famFibre k s x) :=
  UnifiedPi.applyValue_legalGraph (fun y _ => famFibre_bot k s y) (famFibre_finite k s) True.intro

/-! ## (b) The exact-image universe rejects the reflection -/

theorem atom_app_distinct :
    ¬ ValueEq (NeutralPi.applyValue (NeutralPER.neutralAtom 7) (NeutralPER.neutralAtom 1))
      (NeutralPi.applyValue (NeutralPER.neutralAtom 7) (NeutralPER.neutralAtom 2)) := by
  intro h
  have h1 : NeutralPi.applyValue (NeutralPER.neutralAtom 7) (NeutralPER.neutralAtom 1)
      (.spine 7 [.spine 1 []]) :=
    Or.inr (Or.inr ⟨7, [], .spine 1 [], rfl, .const _ _ _, .const _ _ _⟩)
  rcases (h _).mp h1 with h2 | ⟨_, _, _, hf, _, _⟩ | ⟨r, args, u, he, hf, hu⟩
  · cases h2
  · rcases approxI_const_inv hf with h | h <;> cases h
  · rcases approxI_const_inv hf with h | h
    · cases h
    · cases h
      have hargs := (CptI.spine.inj he).2
      have hu' : u = .spine 1 [] := by
        simp only [List.nil_append, List.cons.injEq, and_true] at hargs
        exact hargs.1.symm
      subst hu'
      rcases approxI_const_inv hu with h | h
      · cases h
      · -- the heads 1 and 2 differ
        exact absurd (CptI.spine.inj h).1 (by decide)

theorem tagged_payload_eq {k : Nat} {v w : Value}
    (h : ValueEq (taggedNeutral k v) (taggedNeutral k w)) : ValueEq v w := fun _ =>
  (InductiveCodes.taggedValue_full _ _ _).symm.trans
    ((h _).trans (InductiveCodes.taggedValue_full _ _ _))

open TypeZeroTowerProbe in
/-- The exact-image universe relation: the mutant without the neutral
coarsening. -/
def ExactUniverse (k : Nat) (V W : Value) : Prop :=
  ∃ c : Code k, ValueEq V (image c) ∧ ValueEq W (image c)

open TypeZeroTowerProbe in
/-- All premises constructed: the level-zero neutral code relates the two
distinct neutral proofs, but the exact-image relation does not relate their
reflected applications. -/
theorem exact_universe_rejects_reflection :
    El (Code.neutral 0 0) (NeutralPER.neutralAtom 1) (NeutralPER.neutralAtom 2) ∧
    ¬ ExactUniverse 0
      (NeutralPi.applyValue (famReflect 0 (NeutralPER.neutralAtom 7)) (NeutralPER.neutralAtom 1))
      (NeutralPi.applyValue (famReflect 0 (NeutralPER.neutralAtom 7)) (NeutralPER.neutralAtom 2)) := by
  refine ⟨⟨.atom 1, .atom 2⟩, ?_⟩
  rintro ⟨c, h1, h2⟩
  have he := (famReflect_apply 0 _ _).symm.trans (h1.trans (h2.symm.trans (famReflect_apply 0 _ _)))
  exact atom_app_distinct (tagged_payload_eq he)

/-! ## (c) The coarse relation accepts the reflection -/

/-- Level-tagged neutral types of one level, all related. -/
def CoarseNeutral (k : Nat) (V W : Value) : Prop :=
  (∃ v, CandidatePi.Neutral v ∧ ValueEq V (taggedNeutral k v)) ∧
  (∃ w, CandidatePi.Neutral w ∧ ValueEq W (taggedNeutral k w))

theorem coarseNeutral_laws (k : Nat) : Laws (CoarseNeutral k) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h g => ⟨h.1, g.2⟩⟩

theorem coarse_accepts_reflection (k : Nat) {s : Value} (hs : CandidatePi.Neutral s)
    {D : Relation} (hne : ∀ x y, D x y → CandidatePi.NonemptyValue x ∧ CandidatePi.NonemptyValue y)
    {x y : Value} (hxy : D x y) :
    CoarseNeutral k (NeutralPi.applyValue (famReflect k s) x)
      (NeutralPi.applyValue (famReflect k s) y) :=
  ⟨⟨_, .app hs x (hne x y hxy).1, famReflect_apply k s x⟩,
    ⟨_, .app hs y (hne x y hxy).2, famReflect_apply k s y⟩⟩

theorem coarse_reflection_level (k : Nat) {s : Value} (x : Value) :
    SortMember (some k) (NeutralPi.applyValue (famReflect k s) x) := by
  refine sortMember_congr (famReflect_apply k s x).symm ?_
  rintro c (rfl | ⟨a, p, rfl, ha, _⟩)
  · exact .bot
  · exact .tagged a p ha

/-! ## (d) The coarse tower accepts the reflected family -/

open TypeZeroTowerProbe in
theorem withBot_applyValue (s x : Value) :
    ValueEq (withBot (NeutralPi.applyValue s x)) (NeutralPi.applyValue s x) := fun _ =>
  ⟨fun h => h.elim (fun h => Or.inl h) id, Or.inr⟩

open TypeZeroTowerProbe in
theorem atom_app_head11Free (x : Value) :
    Head11Free (NeutralPi.applyValue (NeutralPER.neutralAtom 7) x) := by
  intro args h
  rcases h with hb | ⟨_, _, _, hf, _, _⟩ | ⟨r, args', u, he, hf, _⟩
  · cases hb
  · rcases approxI_const_inv hf with h | h <;> cases h
  · rcases approxI_const_inv hf with h | h
    · cases h
    · cases h
      -- the heads 11 and 7 differ
      exact absurd (CptI.spine.inj he).1 (by decide)

open TypeZeroTowerProbe in
/-- In the tower with the coarse universe, the reflected family is a member
of the product `A → Sort 0` over the level-zero neutral code. -/
theorem tower_accepts_reflection :
    El (Code.pi (Code.neutral 0 0) (famFibre 0 (NeutralPER.neutralAtom 7)) (fun _ => Code.univ 0))
      (famReflect 0 (NeutralPER.neutralAtom 7)) (famReflect 0 (NeutralPER.neutralAtom 7)) := by
  refine ⟨Or.inl rfl, Or.inl rfl, fun x y hxy => ?_⟩
  have himg : ∀ z, CandidatePi.Neutral z → NeutralImage 0
      (NeutralPi.applyValue (famReflect 0 (NeutralPER.neutralAtom 7)) z) := fun z hz =>
    ⟨_, .app (.atom 7) z (CandidatePi.neutral_nonempty hz), atom_app_head11Free z,
      (famReflect_apply 0 _ z).trans (by
        show ValueEq (InductiveCodes.taggedValue (some 0) _) (InductiveCodes.taggedValue (some 0) _)
        rw [NeutralCodes.valueEq_eq (withBot_applyValue (NeutralPER.neutralAtom 7) z)]
        exact ValueEq.refl _)⟩
  exact ⟨Or.inr ⟨himg x hxy.1, himg y hxy.2⟩, Or.inr ⟨himg x hxy.1, himg y hxy.2⟩⟩

end Rcic.Declarative.Ann.LR3.NeutralReflectionProbe
