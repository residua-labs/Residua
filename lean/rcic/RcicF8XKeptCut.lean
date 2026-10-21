import rcic.RcicF8XEdgeLex

/-!
# A0: kept cuts in the original DM order

Implements ChatGPT (J line), #7301, `S0_W_X_SUBST_JOIN_MEASURE.md` §4.
The cut fills the existing `DMStep` witnesses. The exact count criterion
counts finite lists of Nat weights, including every duplicate. Its reverse
direction keeps all weights above the pivot and the shared pivot copies;
one remaining pivot pays for every added lower weight.

`Jd.wt`, `DMStep`, and `OM3_edgeLex` are unchanged. The lexicographic
right branch requires literal equality of weight lists, not a permutation
or equal counts. This module supplies ordering evidence only; provenance,
actual JOIN execution, and availability belong to later slices.
`closure_claim = 0`.
-/

namespace Rcic.Syn

private theorem keptCut_greatest {X : List Nat} (hne : X ≠ []) :
    ∃ r ∈ X, ∀ x ∈ X, x ≤ r := by
  induction X with
  | nil => exact False.elim (hne rfl)
  | cons a X ih =>
    cases X with
    | nil => exact ⟨a, .head _, fun x hx => by
        have := List.mem_singleton.mp hx; omega⟩
    | cons b X =>
      obtain ⟨r, hr, hmax⟩ := ih (List.cons_ne_nil _ _)
      by_cases h : a ≤ r
      · exact ⟨r, .tail _ hr, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h
          · exact hmax x hx⟩
      · exact ⟨a, .head _, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Nat.le_refl _
          · have := hmax x hx; omega⟩

private theorem keptCut_count_filter (p : Nat → Bool) (M : List Nat) (q : Nat) :
    (M.filter p).count q = if p q then M.count q else 0 := by
  by_cases h : p q
  · simp [h, List.count_filter h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact List.count_eq_zero_of_not_mem (fun hm => h (List.mem_filter.mp hm).2)

-- Core's reverse `List.perm_iff_count` uses `Classical.choice` through
-- `perm_cons_erase`. Use the original order owner's constructive splitter.
private theorem keptCut_perm_of_count {L C : List Nat}
    (h : ∀ q, L.count q = C.count q) : L.Perm C := by
  induction L generalizing C with
  | nil =>
    cases C with
    | nil => exact .nil
    | cons c C =>
      have hc := h c
      simp only [List.count_nil, List.count_cons_self] at hc
      exact False.elim (Nat.noConfusion hc)
  | cons a L ih =>
    have ha : a ∈ C := List.count_pos_iff.mp (by
      have hh := h a; simp only [List.count_cons_self] at hh; omega)
    obtain ⟨rest, hp⟩ := perm_cons_of_mem ha
    have hrest : ∀ q, L.count q = rest.count q := by
      intro q
      have hh := (h q).trans (hp.count_eq q)
      simp only [List.count_cons] at hh
      omega
    exact ((ih hrest).cons a).trans hp.symm

/-- Forward exactness: the largest removed weight decreases, and every
    higher multiplicity is unchanged. No well-foundedness theorem is used. -/
theorem highest_count_of_dmStep {L C : List Nat} (h : DMStep C L) :
    ∃ r, C.count r < L.count r ∧ ∀ q, r < q → C.count q = L.count q := by
  obtain ⟨X, Y, Z, hne, hL, hC, hlt⟩ := h
  obtain ⟨r, hr, hmax⟩ := keptCut_greatest hne
  have hY : ∀ y ∈ Y, y < r := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hlt y hy
    exact Nat.lt_of_lt_of_le hxy (hmax x hx)
  have hYr : Y.count r = 0 := List.count_eq_zero_of_not_mem (by
    intro hm; exact Nat.lt_irrefl r (hY r hm))
  have hXr : 0 < X.count r := List.count_pos_iff.mpr hr
  refine ⟨r, ?_, ?_⟩
  · have h1 := hL.count_eq r
    have h2 := hC.count_eq r
    simp only [List.count_append, hYr] at h1 h2
    omega
  · intro q hq
    have hXq : X.count q = 0 := List.count_eq_zero_of_not_mem (by
      intro hm; have := hmax q hm; omega)
    have hYq : Y.count q = 0 := List.count_eq_zero_of_not_mem (by
      intro hm; have := hY q hm; omega)
    have h1 := hL.count_eq q
    have h2 := hC.count_eq q
    simp only [List.count_append, hXq, hYq, Nat.zero_add] at h1 h2
    exact h2.trans h1.symm

/-- Reverse exactness: construct the original `DMStep` decomposition from
    the successful count pivot. Shared pivot copies and every higher
    occurrence are retained, and all added occurrences are below the pivot. -/
theorem dmStep_of_highest_count {L C : List Nat} {r : Nat}
    (hdrop : C.count r < L.count r)
    (hhigh : ∀ q, r < q → C.count q = L.count q) : DMStep C L := by
  let removed := L.filter (fun q => q < r) ++ List.replicate (L.count r - C.count r) r
  let added := C.filter (fun q => q < r)
  let retained := L.filter (fun q => r < q) ++ List.replicate (C.count r) r
  have hr : r ∈ removed := by
    apply List.mem_append_right
    exact List.mem_replicate.mpr ⟨by omega, rfl⟩
  refine ⟨removed, added, retained, ?_, ?_, ?_, ?_⟩
  · intro hnil
    rw [hnil] at hr
    exact List.not_mem_nil _ hr
  · apply keptCut_perm_of_count
    intro q
    by_cases hqr : q = r
    · subst q
      simp [removed, retained, List.count_append, keptCut_count_filter,
        List.count_replicate]
      omega
    · by_cases hlt : q < r
      · have hgt : ¬ r < q := by omega
        simp [removed, retained, List.count_append, keptCut_count_filter,
          List.count_replicate, hqr, Ne.symm hqr, hlt, hgt]
      · have hgt : r < q := by omega
        simp [removed, retained, List.count_append, keptCut_count_filter,
          List.count_replicate, hqr, Ne.symm hqr, hlt, hgt]
  · apply keptCut_perm_of_count
    intro q
    by_cases hqr : q = r
    · subst q
      simp [added, retained, List.count_append, keptCut_count_filter,
        List.count_replicate]
    · by_cases hlt : q < r
      · have hgt : ¬ r < q := by omega
        simp [added, retained, List.count_append, keptCut_count_filter,
          List.count_replicate, hqr, Ne.symm hqr, hlt, hgt]
      · have hgt : r < q := by omega
        simpa [added, retained, List.count_append, keptCut_count_filter,
          List.count_replicate, hqr, Ne.symm hqr, hlt, hgt] using hhigh q hgt
  · intro y hy
    exact ⟨r, hr, of_decide_eq_true (List.mem_filter.mp hy).2⟩

/-- The original DM order over finite Nat-weight lists is exactly a
    decrease at the highest differing weight. -/
theorem dmStep_iff_highest_count {L C : List Nat} :
    DMStep C L ↔ ∃ r, C.count r < L.count r ∧ ∀ q, r < q → C.count q = L.count q :=
  ⟨highest_count_of_dmStep, fun ⟨_, hdrop, hhigh⟩ => dmStep_of_highest_count hdrop hhigh⟩

/-- A secondary term cannot repair a first component which neither
    DM-descends nor is literally equal. Permutation is insufficient. -/
theorem not_lex_of_not_dmStep_ne {L C : List Nat}
    (hdm : ¬ DMStep C L) (hne : C ≠ L) (sc se : Nat) :
    ¬ Prod.Lex DMStep (fun a b : Nat => a < b) (C, se) (L, sc) := by
  intro h
  cases h with
  | left _ _ h => exact hdm h
  | right _ _ => exact hne rfl

/-- Removing 6 pays for the extra copies of the retained weight 3. -/
theorem pin_kept_cut_6_3 : DMStep [3, 3, 3] [6, 3] := by
  apply dmStep_of_highest_count (r := 6)
  · decide
  · intro q hq
    have h6 : q ≠ 6 := by omega
    have h3 : q ≠ 3 := by omega
    simp [List.count_cons, h6, h3, Ne.symm h6, Ne.symm h3]

/-- The maximal kept atom cannot be duplicated when no larger payer exists. -/
theorem pin_kept_overflow (κ : Nat) (hκ : 6 < κ) : ¬ DMStep [κ, κ] [6, κ] := by
  intro h
  obtain ⟨r, hdrop, hhigh⟩ := highest_count_of_dmStep h
  have h6κ : 6 ≠ κ := by omega
  by_cases hr : r < κ
  · have hh := hhigh κ hr
    simp [List.count_cons, h6κ] at hh
  · have h6r : 6 ≠ r := by omega
    by_cases hκr : κ = r
    · subst r
      simp [List.count_cons, h6κ] at hdrop
    · simp [List.count_cons, hκr, h6r] at hdrop

/-- Even an arbitrarily small secondary size cannot repair that overflow. -/
theorem pin_kept_overflow_no_lex (κ : Nat) (hκ : 6 < κ) (sc se : Nat) :
    ¬ Prod.Lex DMStep (fun a b : Nat => a < b) ([κ, κ], se) ([6, κ], sc) :=
  not_lex_of_not_dmStep_ne (pin_kept_overflow κ hκ)
    (by intro h; have := List.cons.inj h; omega) sc se

/-- Zero is a valid pivot when the callee deletes the final occurrence. -/
theorem pin_kept_cut_zero : DMStep [] [0] := by
  exact ⟨[0], [], [], List.cons_ne_nil _ _, .refl _, .refl _,
    fun _ hy => False.elim (List.not_mem_nil _ hy)⟩

/-- Equal histograms do not enable the lexicographic right branch when
    the first lists differ in order. -/
theorem pin_kept_permutation_no_lex (sc se : Nat) :
    ¬ Prod.Lex DMStep (fun a b : Nat => a < b) ([3, 6], se) ([6, 3], sc) := by
  apply not_lex_of_not_dmStep_ne (hne := by decide)
  intro h
  obtain ⟨r, hdrop, _⟩ := highest_count_of_dmStep h
  have hh := (List.Perm.swap 3 6 []).count_eq r
  exact (Nat.ne_of_lt hdrop) hh.symm

/-- Literal equality does enable secondary descent in the existing order. -/
theorem pin_kept_equal_secondary :
    Prod.Lex DMStep (fun a b : Nat => a < b) ([6, 3], 0) ([6, 3], 1) :=
  .right _ (by decide)

end Rcic.Syn

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

/-- Constructive keep-some/replace-the-rest edge, with an untouched outer
    frame. These are witnesses for the original `DMStep`, not a new order. -/
theorem om3_edge_of_cut_kept {L C Z removed retained added : List (Jd E n)}
    (hL : L.Perm (removed ++ retained))
    (hC : C.Perm (added ++ retained)) (hne : removed ≠ [])
    (hlt : ∀ y ∈ added, ∃ x ∈ removed, y.wt < x.wt) :
    OM3_edge (L ++ Z) (C ++ Z) := by
  refine ⟨removed.map Jd.wt, added.map Jd.wt, (retained ++ Z).map Jd.wt,
    ?_, ?_, ?_, ?_⟩
  · cases removed with
    | nil => exact False.elim (hne rfl)
    | cons x xs => exact List.cons_ne_nil _ _
  · simpa only [List.map_append, List.append_assoc] using (hL.append_right Z).map Jd.wt
  · simpa only [List.map_append, List.append_assoc] using (hC.append_right Z).map Jd.wt
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    obtain ⟨x, hx, hax⟩ := hlt a ha
    exact ⟨x.wt, List.mem_map.mpr ⟨x, hx, rfl⟩, hax⟩

/-- Multiplicity at a weight, computed without deciding equality on `Jd`. -/
def weightCount (L : List (Jd E n)) (r : Nat) : Nat := (L.map Jd.wt).count r

/-- Exact count criterion for the existing `OM3_edge`, in caller/callee order. -/
theorem om3_edge_iff_highest_count {L C : List (Jd E n)} :
    OM3_edge L C ↔ ∃ r, weightCount C r < weightCount L r ∧
      ∀ q, r < q → weightCount C q = weightCount L q :=
  dmStep_iff_highest_count

/-- Reverse no-lex-repair: the equality premise is literal equality of
    the mapped lists, exactly what the existing `Prod.Lex.right` requires. -/
theorem not_om3_edgeLex_of_not_edge_ne {L C : List (Jd E n)}
    (hdm : ¬ OM3_edge L C) (hne : C.map Jd.wt ≠ L.map Jd.wt) (sc se : Nat) :
    ¬ OM3_edgeLex (L, sc) (C, se) :=
  not_lex_of_not_dmStep_ne hdm hne sc se

/-- The kept-cut API handles caller permutation, duplicate added atoms,
    and an arbitrary common outer frame using weights alone. -/
theorem pin_om3_kept_cut_frame {b k : Jd E n} (hlt : k.wt < b.wt)
    (Z : List (Jd E n)) : OM3_edge ([k, b] ++ Z) ([k, k, k] ++ Z) := by
  apply om3_edge_of_cut_kept (removed := [b]) (retained := [k]) (added := [k, k])
    (List.Perm.swap b k []) (.refl _) (List.cons_ne_nil _ _)
  intro y hy
  have hyk : y = k := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hy
  subst y
  exact ⟨b, .head _, hlt⟩

end Rcic.Declarative.F8Measure

#print axioms Rcic.Syn.highest_count_of_dmStep
#print axioms Rcic.Syn.dmStep_of_highest_count
#print axioms Rcic.Syn.dmStep_iff_highest_count
#print axioms Rcic.Syn.not_lex_of_not_dmStep_ne
#print axioms Rcic.Syn.pin_kept_cut_6_3
#print axioms Rcic.Syn.pin_kept_overflow
#print axioms Rcic.Syn.pin_kept_overflow_no_lex
#print axioms Rcic.Syn.pin_kept_cut_zero
#print axioms Rcic.Syn.pin_kept_permutation_no_lex
#print axioms Rcic.Syn.pin_kept_equal_secondary
#print axioms Rcic.Declarative.F8Measure.om3_edge_of_cut_kept
#print axioms Rcic.Declarative.F8Measure.weightCount
#print axioms Rcic.Declarative.F8Measure.om3_edge_iff_highest_count
#print axioms Rcic.Declarative.F8Measure.not_om3_edgeLex_of_not_edge_ne
#print axioms Rcic.Declarative.F8Measure.pin_om3_kept_cut_frame
