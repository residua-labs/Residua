import rcic.RcicAnnCtorSem
import rcic.RcicAnnIotaGroup

/-!
# M2-f (5b) — the recursor's telescope: syntax, neutrality, the major's chain

The laws the recursors' clause (`RcicAnnRecSem`) reads off the recursor type built from the views
(`RcicAnnRecView`):

* a recursor type at a zero motive level is a proposition (`recTypeA_propTy`);
* the minor builder under substitution, level instantiation and the two instantiation steps of a
  field (`substA_minorFieldsA`, `instantiate0A_minorFieldsA_plain`, `substA_minorFieldsA_drec`);
* level instantiation through the whole builder (`instDomsA_recDomsA`), the canonical vector at a
  longer list (`canonLevelsA_instLevel_take`), bounded expressions read only a prefix
  (`instantiateLevelsA_take`);
* the walk along the recursor's telescope, both ways: related arguments split into the motive, the
  minors, the indices and the major (`recArgsSplitA`), and join back (`recArgsJoinA`);
* a recursor spine at its arity on a stuck major, or of a group without a constructor (O1-a), is an
  extended neutral (`neutKA_recApp`);
* an application at the major expands along the major's chain (`LRRelA_expand_majorChain`), each step
  a typed major step (R-MajorStep), ι refusing at a stepping major (`iotaFnA_app_none_of_step`);
* iterated elimination (`LRRelA_apps`, in `RcicAnnTelIntro`), the converse of the telescope lemma.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) a recursor type whose motive level is zero is a proposition -/

theorem recDomsA_ne_nil (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) : recDomsA f ls params indices wF wM cds ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [recDomsA_length] at this
  simp at this

/-- at a zero motive level the instantiated recursor type is a Π whose codomain annotation is
    zero: a proposition, weak-head normal. -/
theorem recTypeA_propTy {E : ResolvedEnvA} {I : IotaIfaceA} (ms : List Level) (f : Nat) (ls : List Level)
    (params indices : List (ExprA × Level)) (wF wM : Level) (cds : List MinorDataA)
    (hz : isZero (instLevel ms wM) = true) (Γ : LCtxA) :
    hStepFnA E I.fn Γ (instantiateLevelsA ms (recTypeA f ls params indices wF wM cds)) = none ∧
      IsPropTy E I Γ (instantiateLevelsA ms (recTypeA f ls params indices wF wM cds)) := by
  rw [instantiateLevelsA_recTypeA]
  cases h : instDomsA ms (recDomsA f ls params indices wF wM cds) with
  | nil =>
      have := congrArg List.length h
      simp only [instDomsA, List.length_map, List.length_nil, recDomsA_length] at this
      exfalso
      omega
  | cons d ds =>
      obtain ⟨D, u⟩ := d
      simp only [piTelA]
      refine ⟨hStepFnA_pi _ _ _ _ _ _ _, (isPropTy_pi_iff _ _ _ _ _ _ _).mpr ?_⟩
      rw [piTelA_snd_isZero]
      exact hz


/-! ## (2) the minor's builder laws: substitution, levels, the walk's two steps -/

theorem liftA_two (e : ExprA) : liftA 0 2 e = liftA 0 1 (liftA 0 1 e) :=
  (liftA_liftA_merge 1 1 0 0 (Nat.le_refl 0) (Nat.zero_le _) e).symm

theorem substA_up_up_liftA2 (τ : SubstA) (e : ExprA) :
    substA τ.up.up (liftA 0 2 e) = liftA 0 2 (substA τ e) := by
  rw [liftA_two, liftA_two, substA_up_liftA, substA_up_liftA]

theorem map_substA_up_up_liftA2 (τ : SubstA) :
    (pl : List ExprA) → (pl.map (liftA 0 2)).map (substA τ.up.up) = (pl.map (substA τ)).map (liftA 0 2)
  | [] => rfl
  | p :: pl => by simp only [List.map, substA_up_up_liftA2, map_substA_up_up_liftA2 τ pl]

/-- substitution passes through a function-recursive field's induction hypothesis when it fixes the
    variables up to the field's (`x` at `j`, the inner ones below it at the body). -/
theorem substA_frecIHA (wM : Level) (idx : List ExprA) (m : Nat) :
    (ds : List (ExprA × Level)) → (mot : ExprA) → (j : Nat) → (σ τ : SubstA) → m ≤ j + ds.length →
    (∀ i, i ≤ j → τ i = .bvar i) →
    substA τ (frecIHA wM mot j σ ds idx m).1 =
      (frecIHA wM (substA τ mot) j (fun i => substA τ (σ i)) ds idx m).1
  | [], mot, j, σ, τ, hm, hτ => by
      simp only [List.length_nil, Nat.add_zero] at hm
      simp only [frecIHA, substA_foldAppsA, List.map_append, List.map_map, List.map]
      have hidx : (substA τ ∘ substA σ) = substA (fun i => substA τ (σ i)) :=
        funext fun e => substA_substA τ σ e
      have hxs : (List.range m).reverse.map (substA τ ∘ ExprA.bvar) = (List.range m).reverse.map ExprA.bvar := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_reverse, List.mem_range] at hi
        simp only [Function.comp, substA_bvar]
        exact hτ i (by omega)
      rw [hidx, substA_bvar, hτ j (Nat.le_refl j), hxs]
  | (D, u) :: ds, mot, j, σ, τ, hm, hτ => by
      simp only [List.length_cons] at hm
      simp only [frecIHA, substA_pi]
      rw [substA_frecIHA wM idx m ds (liftA 0 1 mot) (j + 1) σ.up τ.up (by omega) (fun i hi => by
          cases i with
          | zero => rfl
          | succ i =>
              rw [SubstA.up_succ, hτ i (by omega), liftA_bvar]
              simp [shiftIdx]),
        substA_up_liftA, substA_substA τ σ D]
      have hσ : (fun i => substA τ.up (σ.up i)) = SubstA.up (fun i => substA τ (σ i)) :=
        funext (substA_substA.comp_up τ σ)
      rw [hσ]
      simp only [frecIHA_snd]

/-- level instantiation passes through a function-recursive field's induction hypothesis. -/
theorem instantiateLevelsA_frecIHA (ms : List Level) (wM : Level) (idx : List ExprA) (m : Nat) :
    (ds : List (ExprA × Level)) → (mot : ExprA) → (j : Nat) → (σ : SubstA) →
    instantiateLevelsA ms (frecIHA wM mot j σ ds idx m).1 =
      (frecIHA (instLevel ms wM) (instantiateLevelsA ms mot) j (fun i => instantiateLevelsA ms (σ i))
        (instDomsA ms ds) (idx.map (instantiateLevelsA ms)) m).1
  | [], mot, j, σ => by
      simp only [frecIHA, instDomsA, List.map, instantiateLevelsA_foldAppsA, List.map_append, List.map_map]
      have hidx : (instantiateLevelsA ms ∘ substA σ) =
          (substA (fun i => instantiateLevelsA ms (σ i)) ∘ instantiateLevelsA ms) :=
        funext fun e => instantiateLevelsA_substA ms e σ
      have hxs : (instantiateLevelsA ms ∘ ExprA.bvar) = ExprA.bvar := funext fun _ => rfl
      rw [hidx, hxs]
      rfl
  | (D, u) :: ds, mot, j, σ => by
      simp only [frecIHA, instantiateLevelsA, instDomsA, List.map]
      have ih := instantiateLevelsA_frecIHA ms wM idx m ds (liftA 0 1 mot) (j + 1) σ.up
      simp only [instDomsA] at ih
      rw [ih, instantiateLevelsA_liftA, instantiateLevelsA_substA ms D σ,
        instantiateLevelsA_substA.upLevels ms σ, frecIHA_snd, frecIHA_snd]
      have h := frecLevelA_instLevel ms wM ds
      simp only [instDomsA] at h
      rw [h]

/-- substitution passes through the minor builder: on the parameter locals, the motive and the field
    locals, and composed onto the plain substitution. -/
theorem substA_minorFieldsA (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ τ : SubstA) →
    substA τ (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 =
      (minorFieldsA f c ls wF wM (pl.map (substA τ)) (substA τ mot) (fl.map (substA τ))
        (fun i => substA τ (σ i)) fs res).1
  | [], pl, mot, fl, σ, τ => by
      simp only [minorFieldsA, substA_foldAppsA, substA_const, List.map_append, List.map_map, List.map]
      congr 3
      exact funext fun e => substA_substA τ σ e
  | .plain D u :: fs, pl, mot, fl, σ, τ => by
      simp only [minorFieldsA, substA_pi]
      rw [substA_minorFieldsA f c ls wF wM res fs _ _ _ σ.up τ.up, map_substA_up_liftA,
        substA_up_liftA, List.map_append, map_substA_up_liftA, substA_substA τ σ D]
      have hσ : (fun i => substA τ.up (σ.up i)) = SubstA.up (fun i => substA τ (σ i)) :=
        funext (substA_substA.comp_up τ σ)
      simp only [List.map, substA_bvar, SubstA.up_zero, hσ, minorFieldsA_snd]
  | .drec idx :: fs, pl, mot, fl, σ, τ => by
      simp only [minorFieldsA, substA_pi]
      rw [substA_minorFieldsA f c ls wF wM res fs _ _ _ σ.shift1.shift1 τ.up.up, map_substA_up_up_liftA2,
        substA_up_up_liftA2, List.map_append, map_substA_up_up_liftA2, substA_foldAppsA, substA_foldAppsA,
        substA_const, substA_up_liftA, List.map_append, List.map_append, map_substA_up_liftA, List.map_map]
      have hσ : (fun i => substA τ.up.up (σ.shift1.shift1 i)) =
          SubstA.shift1 (SubstA.shift1 (fun i => substA τ (σ i))) :=
        funext fun i => by
          show substA τ.up.up (liftA 0 1 (liftA 0 1 (σ i))) = liftA 0 1 (liftA 0 1 (substA τ (σ i)))
          rw [substA_up_liftA, substA_up_liftA]
      have hidx : (substA τ ∘ substA σ) = substA (fun i => substA τ (σ i)) :=
        funext fun e => substA_substA τ σ e
      have hb1 : substA τ.up.up (.bvar 1) = .bvar 1 := rfl
      simp only [List.map, substA_bvar, SubstA.up_zero, hσ, hidx, hb1, minorFieldsA_snd]
  | .drecD D idx :: fs, pl, mot, fl, σ, τ => by
      simp only [minorFieldsA, substA_pi]
      rw [substA_minorFieldsA f c ls wF wM res fs _ _ _ σ.shift1.shift1 τ.up.up, map_substA_up_up_liftA2,
        substA_up_up_liftA2, List.map_append, map_substA_up_up_liftA2, substA_substA τ σ D,
        substA_foldAppsA, substA_up_liftA, List.map_append, map_substA_up_liftA,
        List.map_map]
      have hσ : (fun i => substA τ.up.up (σ.shift1.shift1 i)) =
          SubstA.shift1 (SubstA.shift1 (fun i => substA τ (σ i))) :=
        funext fun i => by
          show substA τ.up.up (liftA 0 1 (liftA 0 1 (σ i))) = liftA 0 1 (liftA 0 1 (substA τ (σ i)))
          rw [substA_up_liftA, substA_up_liftA]
      have hidx : (substA τ ∘ substA σ) = substA (fun i => substA τ (σ i)) :=
        funext fun e => substA_substA τ σ e
      have hb1 : substA τ.up.up (.bvar 1) = .bvar 1 := rfl
      simp only [List.map, substA_bvar, SubstA.up_zero, hσ, hidx, hb1, minorFieldsA_snd]
      have hl : List.map (liftA 0 1 ∘ substA τ) (List.map (substA σ) idx) =
          List.map (liftA 0 1) (List.map (substA fun i => substA τ (σ i)) idx) := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left (fun e _ => by simp only [Function.comp, substA_substA τ σ e])
      rw [hl]
  | .frec B uB Bs idx :: fs, pl, mot, fl, σ, τ => by
      simp only [minorFieldsA, substA_pi]
      rw [substA_minorFieldsA f c ls wF wM res fs _ _ _ σ.shift1.shift1 τ.up.up, map_substA_up_up_liftA2,
        substA_up_up_liftA2, List.map_append, map_substA_up_up_liftA2, substA_frecDomA,
        substA_frecIHA wM idx (Bs.length + 1) ((B, uB) :: Bs) (liftA 0 1 mot) 0 σ.shift1 τ.up (by simp)
          (fun i hi => by obtain rfl : i = 0 := by omega
                          rfl),
        substA_up_liftA]
      have hσ : (fun i => substA τ.up.up (σ.shift1.shift1 i)) =
          SubstA.shift1 (SubstA.shift1 (fun i => substA τ (σ i))) :=
        funext fun i => by
          show substA τ.up.up (liftA 0 1 (liftA 0 1 (σ i))) = liftA 0 1 (liftA 0 1 (substA τ (σ i)))
          rw [substA_up_liftA, substA_up_liftA]
      have hσ1 : (fun i => substA τ.up (σ.shift1 i)) = SubstA.shift1 (fun i => substA τ (σ i)) :=
        funext fun i => substA_up_liftA τ (σ i)
      have hb1 : substA τ.up.up (.bvar 1) = .bvar 1 := rfl
      simp only [List.map, hσ, hσ1, hb1, minorFieldsA_snd, frecDomA_snd, frecIHA_snd]

/-- a plain field's argument: the field local is the argument, the plain substitution extends. -/
theorem instantiate0A_minorFieldsA_plain (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA)
    (fs : List FieldA) (pl : List ExprA) (mot : ExprA) (fl : List ExprA) (σ : SubstA) (a : ExprA) :
    instantiate0A a (minorFieldsA f c ls wF wM (pl.map (liftA 0 1)) (liftA 0 1 mot)
      (fl.map (liftA 0 1) ++ [.bvar 0]) σ.up fs res).1 =
      (minorFieldsA f c ls wF wM pl mot (fl ++ [a]) (SubstA.cons a σ) fs res).1 := by
  rw [instantiate0A_eq_substA_cons, substA_minorFieldsA, map_substA_cons_liftA, map_substA_id,
    substA_cons_liftA, substA_id, List.map_append, map_substA_cons_liftA, map_substA_id]
  have hσ : (fun i => substA (SubstA.cons a SubstA.id) (σ.up i)) = SubstA.cons a σ := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [SubstA.up_succ, substA_cons_liftA, substA_id, SubstA.cons_succ]
  rw [hσ]
  rfl

/-- the substitution of a recursive field's two binders: the field `a` innermost-but-one, its
    induction hypothesis `h` innermost. -/
theorem substA_cons_cons_liftA2 (h a : ExprA) (σ : SubstA) (e : ExprA) :
    substA (SubstA.cons h (SubstA.cons a σ)) (liftA 0 2 e) = substA σ e := by
  rw [liftA_two, substA_cons_liftA, substA_cons_liftA]

theorem map_substA_cons_cons_liftA2 (h a : ExprA) (σ : SubstA) :
    (pl : List ExprA) → (pl.map (liftA 0 2)).map (substA (SubstA.cons h (SubstA.cons a σ))) =
      pl.map (substA σ)
  | [] => rfl
  | p :: pl => by simp only [List.map, substA_cons_cons_liftA2, map_substA_cons_cons_liftA2 h a σ pl]

/-- a recursive field's argument and its induction hypothesis: both binders consumed, the field local
    is the argument, the plain substitution unchanged. -/
theorem substA_minorFieldsA_drec (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA)
    (fs : List FieldA) (pl : List ExprA) (mot : ExprA) (fl : List ExprA) (σ : SubstA) (a h : ExprA) :
    substA (SubstA.cons h (SubstA.cons a SubstA.id)) (minorFieldsA f c ls wF wM (pl.map (liftA 0 2))
      (liftA 0 2 mot) (fl.map (liftA 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res).1 =
      (minorFieldsA f c ls wF wM pl mot (fl ++ [a]) σ fs res).1 := by
  rw [substA_minorFieldsA, map_substA_cons_cons_liftA2, map_substA_id, substA_cons_cons_liftA2, substA_id,
    List.map_append, map_substA_cons_cons_liftA2, map_substA_id]
  have hσ : (fun i => substA (SubstA.cons h (SubstA.cons a SubstA.id)) (σ.shift1.shift1 i)) = σ := by
    funext i
    show substA _ (liftA 0 1 (liftA 0 1 (σ i))) = σ i
    rw [substA_cons_liftA, substA_cons_liftA, substA_id]
  rw [hσ]
  rfl

/-- the two binders of a recursive field instantiated in turn. -/
theorem instantiate0A_instantiate0A_up (h a e : ExprA) :
    instantiate0A h (substA (SubstA.cons a SubstA.id).up e) =
      substA (SubstA.cons h (SubstA.cons a SubstA.id)) e := by
  rw [instantiate0A_eq_substA_cons, substA_substA]
  apply substA_ext
  intro i
  cases i with
  | zero => rfl
  | succ i => simp only [SubstA.up_succ, substA_cons_liftA, substA_id, SubstA.cons_succ]

/-! ## (3) level instantiation through the recursor builder -/

/-- a constructor's minor data at instantiated levels. -/
def MinorDataA.inst (ms : List Level) (cd : MinorDataA) : MinorDataA :=
  (cd.1, cd.2.1.map (FieldA.instLevels ms), cd.2.2.map (instantiateLevelsA ms))

theorem minorLevelA_instLevel (ms : List Level) (wF wM : Level) :
    (fs : List FieldA) → instLevel ms (minorLevelA wF wM fs) =
      minorLevelA (instLevel ms wF) (instLevel ms wM) (fs.map (FieldA.instLevels ms))
  | [] => rfl
  | .plain _ _ :: fs => by
      simp only [minorLevelA, List.map, FieldA.instLevels, instLevel_imax, minorLevelA_instLevel ms wF wM fs]
  | .drec _ :: fs => by
      simp only [minorLevelA, List.map, FieldA.instLevels, instLevel_imax, minorLevelA_instLevel ms wF wM fs]
  | .drecD _ _ :: fs => by
      simp only [minorLevelA, List.map, FieldA.instLevels, instLevel_imax, minorLevelA_instLevel ms wF wM fs]
  | .frec B uB Bs _ :: fs => by
      have hF := frecLevelA_instLevel ms wF ((B, uB) :: Bs)
      have hM := frecLevelA_instLevel ms wM ((B, uB) :: Bs)
      simp only [instDomsA, List.map] at hF hM
      simp only [minorLevelA, List.map, FieldA.instLevels, instLevel_imax, minorLevelA_instLevel ms wF wM fs,
        hF, hM]
      rfl

theorem map_instantiateLevelsA_liftA2 (ms : List Level) :
    (pl : List ExprA) →
    (pl.map (liftA 0 2)).map (instantiateLevelsA ms) = (pl.map (instantiateLevelsA ms)).map (liftA 0 2)
  | [] => rfl
  | p :: pl => by
      simp only [List.map, instantiateLevelsA_liftA, map_instantiateLevelsA_liftA2 ms pl]

theorem instantiateLevelsA_minorFieldsA (ms : List Level) (f c : Nat) (ls : List Level) (wF wM : Level)
    (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    instantiateLevelsA ms (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 =
      (minorFieldsA f c (ls.map (instLevel ms)) (instLevel ms wF) (instLevel ms wM)
        (pl.map (instantiateLevelsA ms)) (instantiateLevelsA ms mot) (fl.map (instantiateLevelsA ms))
        (fun i => instantiateLevelsA ms (σ i)) (fs.map (FieldA.instLevels ms))
        (res.map (instantiateLevelsA ms))).1
  | [], pl, mot, fl, σ => by
      simp only [minorFieldsA, instantiateLevelsA_foldAppsA, instantiateLevelsA, List.map_append,
        List.map_map, List.map]
      congr 3
      exact funext fun e => instantiateLevelsA_substA ms e σ
  | .plain D u :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, instantiateLevelsA, List.map, FieldA.instLevels]
      rw [instantiateLevelsA_minorFieldsA ms f c ls wF wM res fs _ _ _ σ.up, map_instantiateLevelsA_liftA,
        instantiateLevelsA_liftA, List.map_append, map_instantiateLevelsA_liftA, instantiateLevelsA_substA ms D σ,
        instantiateLevelsA_substA.upLevels ms σ, minorFieldsA_snd, minorFieldsA_snd, minorLevelA_instLevel]
      rfl
  | .drec idx :: fs, pl, mot, fl, σ => by
      have hσ : (fun i => instantiateLevelsA ms (σ.shift1.shift1 i)) =
          SubstA.shift1 (SubstA.shift1 (fun i => instantiateLevelsA ms (σ i))) :=
        funext fun i => by
          show instantiateLevelsA ms (liftA 0 1 (liftA 0 1 (σ i))) = liftA 0 1 (liftA 0 1 (instantiateLevelsA ms (σ i)))
          rw [instantiateLevelsA_liftA, instantiateLevelsA_liftA]
      have hidx : (idx.map (substA σ)).map (instantiateLevelsA ms) =
          (idx.map (instantiateLevelsA ms)).map (substA (fun i => instantiateLevelsA ms (σ i))) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro e _
        exact instantiateLevelsA_substA ms e σ
      have hidxL : ((idx.map (substA σ)).map (liftA 0 1)).map (instantiateLevelsA ms) =
          ((idx.map (instantiateLevelsA ms)).map (substA (fun i => instantiateLevelsA ms (σ i)))).map (liftA 0 1) := by
        rw [map_instantiateLevelsA_liftA, hidx]
      simp only [minorFieldsA, instantiateLevelsA, List.map, FieldA.instLevels]
      rw [instantiateLevelsA_minorFieldsA ms f c ls wF wM res fs _ _ _ σ.shift1.shift1,
        map_instantiateLevelsA_liftA2, instantiateLevelsA_liftA, List.map_append, map_instantiateLevelsA_liftA2,
        instantiateLevelsA_foldAppsA, instantiateLevelsA_foldAppsA, instantiateLevelsA_liftA, List.map_append,
        List.map_append, hidx, hidxL, hσ, minorFieldsA_snd, minorFieldsA_snd, instLevel_imax, minorLevelA_instLevel]
      rfl
  | .drecD D idx :: fs, pl, mot, fl, σ => by
      have hσ : (fun i => instantiateLevelsA ms (σ.shift1.shift1 i)) =
          SubstA.shift1 (SubstA.shift1 (fun i => instantiateLevelsA ms (σ i))) :=
        funext fun i => by
          show instantiateLevelsA ms (liftA 0 1 (liftA 0 1 (σ i))) = liftA 0 1 (liftA 0 1 (instantiateLevelsA ms (σ i)))
          rw [instantiateLevelsA_liftA, instantiateLevelsA_liftA]
      have hidx : (idx.map (substA σ)).map (instantiateLevelsA ms) =
          (idx.map (instantiateLevelsA ms)).map (substA (fun i => instantiateLevelsA ms (σ i))) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro e _
        exact instantiateLevelsA_substA ms e σ
      have hidxL : ((idx.map (substA σ)).map (liftA 0 1)).map (instantiateLevelsA ms) =
          ((idx.map (instantiateLevelsA ms)).map (substA (fun i => instantiateLevelsA ms (σ i)))).map (liftA 0 1) := by
        rw [map_instantiateLevelsA_liftA, hidx]
      simp only [minorFieldsA, instantiateLevelsA, List.map, FieldA.instLevels]
      rw [instantiateLevelsA_minorFieldsA ms f c ls wF wM res fs _ _ _ σ.shift1.shift1,
        map_instantiateLevelsA_liftA2, instantiateLevelsA_liftA, List.map_append, map_instantiateLevelsA_liftA2,
        instantiateLevelsA_substA ms D σ, instantiateLevelsA_foldAppsA, instantiateLevelsA_liftA,
        List.map_append, hidxL, hσ, minorFieldsA_snd, minorFieldsA_snd, instLevel_imax, minorLevelA_instLevel]
      rfl
  | .frec B uB Bs idx :: fs, pl, mot, fl, σ => by
      have hσ2 : (fun i => instantiateLevelsA ms (σ.shift1.shift1 i)) =
          SubstA.shift1 (SubstA.shift1 (fun i => instantiateLevelsA ms (σ i))) :=
        funext fun i => by
          show instantiateLevelsA ms (liftA 0 1 (liftA 0 1 (σ i))) = liftA 0 1 (liftA 0 1 (instantiateLevelsA ms (σ i)))
          rw [instantiateLevelsA_liftA, instantiateLevelsA_liftA]
      have hσ1 : (fun i => instantiateLevelsA ms (σ.shift1 i)) =
          SubstA.shift1 (fun i => instantiateLevelsA ms (σ i)) :=
        funext fun i => instantiateLevelsA_liftA ms 0 1 (σ i)
      have hd := instantiateLevelsA_frecDomA ms f ls wF idx Bs (pl.map (liftA 0 1)) σ.up
      have hih := instantiateLevelsA_frecIHA ms wM idx (Bs.length + 1) Bs (liftA 0 1 (liftA 0 1 mot)) (0 + 1)
        σ.shift1.up
      have hlF := frecLevelA_instLevel ms wF Bs
      have hlM := frecLevelA_instLevel ms wM Bs
      have hlen : (instDomsA ms Bs).length = Bs.length := by simp [instDomsA]
      rw [instantiateLevelsA_liftA, instantiateLevelsA_liftA, instantiateLevelsA_substA.upLevels ms σ.shift1,
        hσ1] at hih
      rw [map_instantiateLevelsA_liftA, instantiateLevelsA_substA.upLevels ms σ] at hd
      simp only [instDomsA] at hd hih hlF hlM hlen
      simp only [minorFieldsA, frecDomA, frecIHA, instantiateLevelsA, List.map, FieldA.instLevels, instDomsA,
        hlen, instLevel_imax]
      rw [instantiateLevelsA_minorFieldsA ms f c ls wF wM res fs _ _ _ σ.shift1.shift1,
        map_instantiateLevelsA_liftA2, instantiateLevelsA_liftA, List.map_append, map_instantiateLevelsA_liftA2,
        hd, hih, instantiateLevelsA_substA ms B σ, instantiateLevelsA_substA ms B σ.shift1, hσ1, hσ2]
      simp only [minorFieldsA_snd, frecDomA_snd, frecIHA_snd, minorLevelA_instLevel, hlF, hlM]
      rfl

theorem instantiateLevelsA_famLocalsA (ms : List Level) (f : Nat) (ls : List Level) (np ni : Nat) :
    instantiateLevelsA ms (famLocalsA f ls np ni) = famLocalsA f (ls.map (instLevel ms)) np ni := by
  simp only [famLocalsA, instantiateLevelsA_foldAppsA, List.map_append, List.map_map]
  have h1 : (instantiateLevelsA ms ∘ liftA 0 ni) = (liftA 0 ni ∘ instantiateLevelsA ms) :=
    funext fun e => instantiateLevelsA_liftA ms 0 ni e
  rw [h1, ← List.map_map, map_instantiateLevelsA_paramLocalsA, map_instantiateLevelsA_paramLocalsA]
  rfl

theorem instDomsA_length (ms : List Level) (ds : List (ExprA × Level)) : (instDomsA ms ds).length = ds.length := by
  simp [instDomsA]

theorem instDomsA_append (ms : List Level) (xs ys : List (ExprA × Level)) :
    instDomsA ms (xs ++ ys) = instDomsA ms xs ++ instDomsA ms ys := by
  simp [instDomsA]

theorem instDomsA_liftDomsA (ms : List Level) :
    (c a : Nat) → (ds : List (ExprA × Level)) → instDomsA ms (liftDomsA c a ds) = liftDomsA c a (instDomsA ms ds)
  | _, _, [] => rfl
  | c, a, (D, u) :: ds => by
      have ih := instDomsA_liftDomsA ms (c + 1) a ds
      simp only [instDomsA, List.map, liftDomsA] at ih ⊢
      rw [instantiateLevelsA_liftA, ih]

theorem instantiateLevelsA_motTyA (ms : List Level) (f : Nat) (ls : List Level)
    (params indices : List (ExprA × Level)) (wF wM : Level) :
    (instantiateLevelsA ms (motTyA f ls params indices wF wM).1, instLevel ms (motTyA f ls params indices wF wM).2) =
      motTyA f (ls.map (instLevel ms)) (instDomsA ms params) (instDomsA ms indices) (instLevel ms wF)
        (instLevel ms wM) := by
  simp only [motTyA]
  rw [instantiateLevelsA_piTelA]
  simp only [instantiateLevelsA, instantiateLevelsA_famLocalsA, instLevel_imax, instLevel_succ,
    instDomsA_length]

theorem instantiateLevelsA_minorTyA (ms : List Level) (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (cd : MinorDataA) :
    (instantiateLevelsA ms (minorTyA f ls wF wM np cd).1, instLevel ms (minorTyA f ls wF wM np cd).2) =
      minorTyA f (ls.map (instLevel ms)) (instLevel ms wF) (instLevel ms wM) np (cd.inst ms) := by
  apply Prod.ext
  · show instantiateLevelsA ms (minorTyA f ls wF wM np cd).1 =
      (minorTyA f (ls.map (instLevel ms)) (instLevel ms wF) (instLevel ms wM) np (cd.inst ms)).1
    simp only [minorTyA, MinorDataA.inst]
    rw [instantiateLevelsA_minorFieldsA, map_instantiateLevelsA_liftA_paramLocalsA]
    have hid : (fun i => instantiateLevelsA ms (SubstA.id.shift1 i)) = SubstA.id.shift1 :=
      funext fun i => by simp [SubstA.shift1, liftA, instantiateLevelsA]
    rw [hid]
    rfl
  · show instLevel ms (minorTyA f ls wF wM np cd).2 =
      (minorTyA f (ls.map (instLevel ms)) (instLevel ms wF) (instLevel ms wM) np (cd.inst ms)).2
    simp only [minorTyA, MinorDataA.inst]
    rw [minorFieldsA_snd, minorFieldsA_snd, minorLevelA_instLevel]

theorem instDomsA_minorDomsA (ms : List Level) (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat) :
    (j : Nat) → (cds : List MinorDataA) →
    instDomsA ms (minorDomsA f ls wF wM np j cds) =
      minorDomsA f (ls.map (instLevel ms)) (instLevel ms wF) (instLevel ms wM) np j (cds.map (MinorDataA.inst ms))
  | _, [] => rfl
  | j, cd :: cds => by
      have ih := instDomsA_minorDomsA ms f ls wF wM np (j + 1) cds
      have hm := instantiateLevelsA_minorTyA ms f ls wF wM np cd
      simp only [instDomsA, List.map, minorDomsA] at ih ⊢
      rw [instantiateLevelsA_liftA, ih]
      rw [Prod.mk.injEq] at hm
      rw [hm.1, hm.2]

/-- LEVEL INSTANTIATION OF THE RECURSOR'S BINDERS is the binders built from the instantiated views. -/
theorem instDomsA_recDomsA (ms : List Level) (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    instDomsA ms (recDomsA f ls params indices wF wM cds) =
      recDomsA f (ls.map (instLevel ms)) (instDomsA ms params) (instDomsA ms indices) (instLevel ms wF)
        (instLevel ms wM) (cds.map (MinorDataA.inst ms)) := by
  simp only [recDomsA, instDomsA_append, instDomsA_length, instDomsA_minorDomsA, instDomsA_liftDomsA,
    List.length_map]
  have hm := instantiateLevelsA_motTyA ms f ls params indices wF wM
  have hmaj : instDomsA ms [(liftA indices.length (cds.length + 1) (famLocalsA f ls params.length indices.length), wF)] =
      [(liftA indices.length (cds.length + 1)
        (famLocalsA f (ls.map (instLevel ms)) params.length indices.length), instLevel ms wF)] := by
    simp only [instDomsA, List.map, instantiateLevelsA_liftA, instantiateLevelsA_famLocalsA]
  have hmot : instDomsA ms [motTyA f ls params indices wF wM] =
      [motTyA f (ls.map (instLevel ms)) (instDomsA ms params) (instDomsA ms indices) (instLevel ms wF)
        (instLevel ms wM)] := by
    show [(instantiateLevelsA ms (motTyA f ls params indices wF wM).1,
      instLevel ms (motTyA f ls params indices wF wM).2)] = _
    rw [hm]
  rw [hmaj, hmot]

/-- the canonical level vector at a longer list: its prefix. -/
theorem canonLevelsA_instLevel_take (ls : List Level) (a : Nat) (h : a ≤ ls.length) :
    (canonLevelsA a).map (instLevel ls) = ls.take a := by
  apply List.ext_getElem
  · simp [canonLevelsA, List.length_take, Nat.min_eq_left h]
  · intro i h1 h2
    simp only [canonLevelsA, List.getElem_map, List.getElem_range, List.getElem_take]
    have hi : i < ls.length := by
      simp [canonLevelsA] at h1; omega
    rw [instLevel_param, List.getElem?_eq_getElem hi]
    rfl

/-- an expression bounded at `k` reads only the first `k` levels. -/
theorem instantiateLevelsA_take (k : Nat) (ls : List Level) :
    (e : ExprA) → exprLevelsBoundedA k e = true → instantiateLevelsA ls e = instantiateLevelsA (ls.take k) e
  | .bvar _, _ => rfl
  | .sort l, h => by simp only [instantiateLevelsA, instLevel_take k ls l h]
  | .const _ ns, h => by simp only [instantiateLevelsA, instLevel_take_map k ls ns h]
  | .app f x, h => by
      simp only [instantiateLevelsA, instantiateLevelsA_take k ls f (boolAnd_left h),
        instantiateLevelsA_take k ls x (boolAnd_right h)]
  | .lam a u b, h => by
      simp only [instantiateLevelsA, instantiateLevelsA_take k ls a (boolAnd_left (boolAnd_left h)),
        instLevel_take k ls u (boolAnd_right (boolAnd_left h)),
        instantiateLevelsA_take k ls b (boolAnd_right h)]
  | .pi a u b v, h => by
      simp only [instantiateLevelsA,
        instantiateLevelsA_take k ls a (boolAnd_left (boolAnd_left (boolAnd_left h))),
        instLevel_take k ls u (boolAnd_right (boolAnd_left (boolAnd_left h))),
        instantiateLevelsA_take k ls b (boolAnd_right (boolAnd_left h)),
        instLevel_take k ls v (boolAnd_right h)]
  | .letE a w b, h => by
      simp only [instantiateLevelsA, instantiateLevelsA_take k ls a (boolAnd_left (boolAnd_left h)),
        instantiateLevelsA_take k ls w (boolAnd_right (boolAnd_left h)),
        instantiateLevelsA_take k ls b (boolAnd_right h)]
  | .lit _, _ => rfl

/-! ## (4) the walk along the recursor's telescope -/

theorem consListA_lt : (ys : List ExprA) → (σ σ' : SubstA) → (i : Nat) → i < ys.length →
    consListA ys σ i = consListA ys σ' i
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | y :: ys, σ, σ', i, h => by
      show consListA ys (SubstA.cons y σ) i = consListA ys (SubstA.cons y σ') i
      by_cases hi : i < ys.length
      · exact consListA_lt ys _ _ i hi
      · have e : i = 0 + ys.length := by simp at h; omega
        rw [e, consListA_add, consListA_add]
        rfl

/-- a lift by `a` at cutoff `c` read through a substitution: the substitution skips `a` slots at `c`. -/
theorem substA_liftA_gen (c : Nat) : (a : Nat) → (σ : SubstA) → (e : ExprA) →
    substA σ (liftA c a e) = substA (fun i => if c ≤ i then σ (i + a) else σ i) e
  | 0, σ, e => by
      rw [liftA_zero]
      exact substA_ext (fun i => by by_cases h : c ≤ i <;> simp [h]) e
  | a + 1, σ, e => by
      rw [← liftA_liftA_merge 1 a c c (Nat.le_refl c) (by omega) e, substA_liftA, substA_liftA_gen c a]
      apply substA_ext
      intro i
      by_cases h : c ≤ i
      · simp only [SubstA.shiftAt, if_pos h, if_pos (show c ≤ i + a by omega)]
        rfl
      · simp only [SubstA.shiftAt, if_neg h]

/-- THE CUTOFF CANCELLATION: values for the `ys` binders over values for `xs` binders the expression
    was lifted past at the cutoff `ys.length`: the `xs` are skipped. -/
theorem substA_consListA_liftA_cut (ys xs : List ExprA) (τ : SubstA) (e : ExprA) :
    substA (consListA ys (consListA xs τ)) (liftA ys.length xs.length e) = substA (consListA ys τ) e := by
  rw [substA_liftA_gen]
  apply substA_ext
  intro i
  by_cases h : ys.length ≤ i
  · rw [if_pos h]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + ys.length := ⟨i - ys.length, by omega⟩
    rw [show j + ys.length + xs.length = (j + xs.length) + ys.length by omega]
    simp only [consListA_add]
  · rw [if_neg h]
    exact consListA_lt ys _ _ i (by omega)

section RecWalk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a related list along a built telescope does not read the body. -/
theorem argsRelKA_piTelA_body {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level) :
    (ds : List (ExprA × Level)) → (σ : SubstA) → {as as' : List ExprA} →
    ArgsRelKA E I n ρ₀ k Γ (substA σ (piTelA ds B w).1) as as' → as.length = ds.length →
    ArgsRelKA E I n ρ₀ k Γ (substA σ (piTelA ds B' w').1) as as'
  | [], _, [], as', h, _ => by
      have hl := argsRelKA_length h
      cases as' with
      | nil => exact .nil _
      | cons _ _ => exact nomatch hl
  | [], _, _ :: _, _, _, hl => nomatch hl
  | (_, _) :: _, _, [], _, _, hl => nomatch hl
  | (D, u) :: ds, σ, a :: as, _, h, hl => by
      simp only [piTelA, substA_pi] at h ⊢
      cases h with
      | cons _ _ _ _ _ a' _ as' hr hs =>
          rw [instantiate0A_substA_up] at hs
          refine .cons _ _ _ _ a a' as as' hr ?_
          rw [instantiate0A_substA_up]
          exact argsRelKA_piTelA_body B B' w w' ds _ hs (Nat.succ.inj hl)

/-- a related list along a built telescope splits at a prefix of the binders: the prefix along the
    prefix's telescope (any body), the rest along the rest under the prefix's values. -/
theorem argsRelKA_piTelA_append_inv {k : Nat} {Γ : LCtxA} (B : ExprA) (w : Level)
    (xs ys : List (ExprA × Level)) (σ : SubstA) {as₁ as₁' as₂ as₂' : List ExprA}
    (h : ArgsRelKA E I n ρ₀ k Γ (substA σ (piTelA (xs ++ ys) B w).1) (as₁ ++ as₂) (as₁' ++ as₂'))
    (hl : as₁.length = xs.length) (hl' : as₁'.length = xs.length) :
    (∀ (B' : ExprA) (w' : Level), ArgsRelKA E I n ρ₀ k Γ (substA σ (piTelA xs B' w').1) as₁ as₁') ∧
      ArgsRelKA E I n ρ₀ k Γ (substA (consListA as₁ σ) (piTelA ys B w).1) as₂ as₂' := by
  rw [piTelA_append] at h
  obtain ⟨T', hT', h1, h2⟩ := argsRelKA_append_inv (hl.trans hl'.symm) h
  rw [applyTelA_piTelA _ _ xs as₁ hl σ] at hT'
  injection hT' with hT'
  subst hT'
  exact ⟨fun B' w' => argsRelKA_piTelA_body _ B' _ w' xs σ h1 hl, h2⟩

/-- the minors' block: each minor related at its type under the values before the block. -/
theorem argsRelKA_minorDomsA {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (B : ExprA) (w : Level) (σ₀ : SubstA) :
    (cds : List MinorDataA) → (j0 : Nat) → (pre : List ExprA) → pre.length = j0 →
    {ms ms' : List ExprA} →
    ArgsRelKA E I n ρ₀ k Γ (substA (consListA pre σ₀) (piTelA (minorDomsA f ls wF wM np j0 cds) B w).1) ms ms' →
    ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelA E I n ρ₀ k Γ (substA σ₀ (minorTyA f ls wF wM np cds[i]).1) ms[i] ms'[i]
  | [], _, _, _, _, _, _, _, _, _, hc => absurd hc (Nat.not_lt_zero _)
  | cd :: cds, j0, pre, hpre, ms, ms', h, i, hi, hi', hc => by
      simp only [minorDomsA, piTelA, substA_pi] at h
      cases h with
      | nil => exact absurd hi (Nat.not_lt_zero _)
      | cons _ _ _ _ m m' ms₀ ms₀' hr hs =>
          cases i with
          | zero =>
              rw [← hpre, substA_consListA_liftA] at hr
              exact hr
          | succ i =>
              rw [instantiate0A_substA_up, ← consListA_snoc] at hs
              exact argsRelKA_minorDomsA f ls wF wM np B w σ₀ cds (j0 + 1) (pre ++ [m])
                (by rw [List.length_append, hpre]; rfl) hs i (Nat.lt_of_succ_lt_succ hi)
                (Nat.lt_of_succ_lt_succ hi') (Nat.lt_of_succ_lt_succ hc)

/-- the indices' block: a telescope lifted past `xs` binders at its cutoff reads as the telescope
    itself once the `xs` values are skipped. -/
theorem argsRelKA_liftDomsA {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level) (xs : List ExprA) (τ : SubstA) :
    (ds : List (ExprA × Level)) → (pre : List ExprA) → {as as' : List ExprA} →
    ArgsRelKA E I n ρ₀ k Γ (substA (consListA pre (consListA xs τ)) (piTelA (liftDomsA pre.length xs.length ds) B w).1)
      as as' → as.length = ds.length →
    ArgsRelKA E I n ρ₀ k Γ (substA (consListA pre τ) (piTelA ds B' w').1) as as'
  | [], _, [], as', h, _ => by
      have hl := argsRelKA_length h
      cases as' with
      | nil => exact .nil _
      | cons _ _ => exact nomatch hl
  | [], _, _ :: _, _, _, hl => nomatch hl
  | (_, _) :: _, _, [], _, _, hl => nomatch hl
  | (D, u) :: ds, pre, a :: as, _, h, hl => by
      simp only [liftDomsA, piTelA, substA_pi] at h ⊢
      cases h with
      | cons _ _ _ _ _ a' _ as' hr hs =>
          rw [substA_consListA_liftA_cut] at hr
          rw [instantiate0A_substA_up, ← consListA_snoc] at hs
          refine .cons _ _ _ _ a a' as as' hr ?_
          rw [instantiate0A_substA_up, ← consListA_snoc]
          have hs' : ArgsRelKA E I n ρ₀ k Γ (substA (consListA (pre ++ [a]) (consListA xs τ))
              (piTelA (liftDomsA (pre ++ [a]).length xs.length ds) B w).1) as as' := by
            rw [List.length_append, List.length_singleton]; exact hs
          exact argsRelKA_liftDomsA B B' w w' xs τ ds (pre ++ [a]) hs' (Nat.succ.inj hl)

/-- the recursor body under all its values: the motive at the indices and the major, whatever the
    values below the motive (the parameters'). -/
theorem substA_recBodyA (mot x : ExprA) (ms is : List ExprA) {τ : SubstA} :
    substA (consListA ([mot] ++ ms ++ is ++ [x]) τ) (recBodyA is.length ms.length) =
      foldAppsA mot (is ++ [x]) := by
  rw [consListA_snoc, recBodyA, substA_foldAppsA, List.map_append, List.map_map]
  have hl : (substA (SubstA.cons x (consListA ([mot] ++ ms ++ is) τ)) ∘ liftA 0 1) =
      substA (consListA ([mot] ++ ms ++ is) τ) := funext fun e => substA_cons_liftA _ _ e
  rw [hl, consListA_append, paramLocalsA_consListA]
  simp only [List.map, substA_bvar, SubstA.cons_zero]
  congr 1
  show SubstA.cons x (consListA is (consListA ([mot] ++ ms) τ)) (is.length + ms.length + 1) = mot
  rw [SubstA.cons_succ, show is.length + ms.length = ms.length + is.length by omega, consListA_add,
    consListA_append]
  have h0 := consListA_add ms (SubstA.cons mot τ) 0
  rw [Nat.zero_add] at h0
  exact h0

/-- THE RECURSOR'S ARGUMENTS SPLIT (M2-f (6c)): related arguments along the recursor's telescope are
    related parameters along the parameter telescope and then, under the parameters' values, a related
    motive, the minors each related at its type under the left motive, related indices along the index
    telescope, and a related major at the family application at the parameters and the indices; the
    codomain is the motive at the indices and the major. -/
theorem recArgsSplitPA {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {as as' : List ExprA}
    (h : ArgsRelKA E I n ρ₀ K Γ
      (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 as as')
    (hlen : as.length = params.length + (1 + cds.length + idxs.length + 1)) :
    ∃ (qs qs' : List ExprA) (mot mot' x x' : ExprA) (ms ms' is is' : List ExprA),
      as = qs ++ ([mot] ++ ms ++ is ++ [x]) ∧ as' = qs' ++ ([mot'] ++ ms' ++ is' ++ [x']) ∧
      qs.length = params.length ∧ qs'.length = params.length ∧
      ms.length = cds.length ∧ ms'.length = cds.length ∧ is.length = idxs.length ∧
      is'.length = idxs.length ∧
      (∀ (B : ExprA) (v : Level), ArgsRelKA E I n ρ₀ K Γ (piTelA params B v).1 qs qs') ∧
      LRRelA E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) mot mot' ∧
      (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
        LRRelA E I n ρ₀ K Γ (substA (SubstA.cons mot (consListA qs SubstA.id))
          (minorTyA f ls wF wM params.length cds[i]).1) ms[i] ms'[i]) ∧
      (∀ (B : ExprA) (v : Level),
        ArgsRelKA E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (piTelA idxs B v).1) is is') ∧
      LRRelA E I n ρ₀ K Γ (foldAppsA (.const f ls) (qs ++ is)) x x' ∧
      applyTelA as (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
        some (foldAppsA mot (is ++ [x])) := by
  have hlen' : as'.length = params.length + (1 + cds.length + idxs.length + 1) :=
    (argsRelKA_length h).symm.trans hlen
  -- the parameters
  obtain ⟨qs, rs, rfl, hqs⟩ : ∃ qs rs, as = qs ++ rs ∧ qs.length = params.length :=
    ⟨as.take params.length, as.drop params.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨qs', rs', rfl, hqs'⟩ : ∃ qs rs, as' = qs ++ rs ∧ qs.length = params.length :=
    ⟨as'.take params.length, as'.drop params.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  have hrl : rs.length = 1 + cds.length + idxs.length + 1 := by
    rw [List.length_append, hqs] at hlen; omega
  have hrl' : rs'.length = 1 + cds.length + idxs.length + 1 := by
    rw [List.length_append, hqs'] at hlen'; omega
  have hT : (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      substA SubstA.id (piTelA (params ++ ([motTyA f ls params idxs wF wM] ++ (minorDomsA f ls wF wM
        params.length 0 cds ++ (liftDomsA 0 (cds.length + 1) idxs ++
          [(liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length), wF)]))))
        (recBodyA idxs.length cds.length) w).1 := by
    rw [substA_id, recDomsA]
    simp only [List.append_assoc]
  have hPh := h
  rw [hT] at hPh
  obtain ⟨hP, h⟩ := argsRelKA_piTelA_append_inv _ _ _ _ _ hPh hqs hqs'
  have hpar : ∀ (B : ExprA) (v : Level), ArgsRelKA E I n ρ₀ K Γ (piTelA params B v).1 qs qs' := by
    intro B v
    have := hP B v
    rwa [substA_id] at this
  generalize hτ : consListA qs SubstA.id = τ at h
  -- the four blocks of the rest
  obtain ⟨mot, r1, rfl⟩ : ∃ mot r1, rs = mot :: r1 := by
    cases rs with
    | nil => exact nomatch hrl
    | cons a r => exact ⟨a, r, rfl⟩
  obtain ⟨mot', r1', rfl⟩ : ∃ mot r1, rs' = mot :: r1 := by
    cases rs' with
    | nil => exact nomatch hrl'
    | cons a r => exact ⟨a, r, rfl⟩
  have hr1 : r1.length = cds.length + idxs.length + 1 := by rw [List.length_cons] at hrl; omega
  have hr1' : r1'.length = cds.length + idxs.length + 1 := by rw [List.length_cons] at hrl'; omega
  obtain ⟨ms, r2, rfl, hms⟩ : ∃ ms r2, r1 = ms ++ r2 ∧ ms.length = cds.length :=
    ⟨r1.take cds.length, r1.drop cds.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨ms', r2', rfl, hms'⟩ : ∃ ms r2, r1' = ms ++ r2 ∧ ms.length = cds.length :=
    ⟨r1'.take cds.length, r1'.drop cds.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  have hr2 : r2.length = idxs.length + 1 := by rw [List.length_append] at hr1; omega
  have hr2' : r2'.length = idxs.length + 1 := by rw [List.length_append] at hr1'; omega
  obtain ⟨is, xl, rfl, his⟩ : ∃ is xl, r2 = is ++ xl ∧ is.length = idxs.length :=
    ⟨r2.take idxs.length, r2.drop idxs.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨is', xl', rfl, his'⟩ : ∃ is xl, r2' = is ++ xl ∧ is.length = idxs.length :=
    ⟨r2'.take idxs.length, r2'.drop idxs.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  have hxl : xl.length = 1 := by rw [List.length_append] at hr2; omega
  have hxl' : xl'.length = 1 := by rw [List.length_append] at hr2'; omega
  obtain ⟨x, rfl⟩ : ∃ x, xl = [x] := by
    match xl, hxl with
    | [x], _ => exact ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ : ∃ x, xl' = [x] := by
    match xl', hxl' with
    | [x], _ => exact ⟨x, rfl⟩
  -- the motive
  have h₀ := h
  rw [show mot :: (ms ++ (is ++ [x])) = [mot] ++ (ms ++ (is ++ [x])) from rfl,
    show mot' :: (ms' ++ (is' ++ [x'])) = [mot'] ++ (ms' ++ (is' ++ [x'])) from rfl] at h₀
  obtain ⟨hM, h₁⟩ := argsRelKA_piTelA_append_inv _ _ _ _ _ h₀ rfl rfl
  have hmot : LRRelA E I n ρ₀ K Γ (substA τ (motTyA f ls params idxs wF wM).1) mot mot' := by
    have h := hM (.sort .zero) .zero
    simp only [piTelA, substA_pi] at h
    cases h with
    | cons _ _ _ _ _ _ _ _ hr _ => exact hr
  -- the minors
  obtain ⟨hMin, h₂⟩ := argsRelKA_piTelA_append_inv _ _ _ _ _ h₁ (hms.trans (minorDomsA_length _ _ _ _ _ _ _).symm)
    (hms'.trans (minorDomsA_length _ _ _ _ _ _ _).symm)
  have hmin := fun i hi hi' hc => argsRelKA_minorDomsA (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := K) (Γ := Γ)
    f ls wF wM params.length (.sort .zero) .zero (consListA [mot] τ) cds 0 [] rfl (hMin (.sort .zero) .zero) i hi hi'
    hc
  -- the indices and the major
  obtain ⟨hIdx, h₃⟩ := argsRelKA_piTelA_append_inv _ _ _ _ _ h₂
    (his.trans (liftDomsA_length _ _ _).symm) (his'.trans (liftDomsA_length _ _ _).symm)
  have hidx : ∀ (B : ExprA) (v : Level), ArgsRelKA E I n ρ₀ K Γ (substA τ (piTelA idxs B v).1) is is' := by
    intro B v
    have h := hIdx (.sort .zero) .zero
    rw [← consListA_append] at h
    have h' : ArgsRelKA E I n ρ₀ K Γ (substA (consListA [] (consListA ([mot] ++ ms) τ))
        (piTelA (liftDomsA ([] : List ExprA).length ([mot] ++ ms).length idxs) (.sort .zero) .zero).1) is is' := by
      have e : ([mot] ++ ms).length = cds.length + 1 := by
        rw [List.length_append, hms, List.length_singleton]; omega
      rw [e]; exact h
    exact argsRelKA_liftDomsA (.sort .zero) B .zero v ([mot] ++ ms) τ idxs [] h' his
  have hmaj : LRRelA E I n ρ₀ K Γ (foldAppsA (.const f ls) (qs ++ is)) x x' := by
    simp only [piTelA, substA_pi] at h₃
    cases h₃ with
    | cons _ _ _ _ _ _ _ _ hr _ =>
        have e : cds.length + 1 = ([mot] ++ ms).length := by
          rw [List.length_append, hms, List.length_singleton]; omega
        have hfun : (substA (consListA is τ) ∘ liftA 0 is.length) = substA τ :=
          funext fun e => substA_consListA_liftA is τ e
        rw [← consListA_append [mot] ms τ, e, ← his, substA_consListA_liftA_cut, famLocalsA,
          substA_foldAppsA, substA_const, List.map_append, paramLocalsA_consListA, List.map_map, hfun, ← hτ,
          ← hqs, paramLocalsA_consListA] at hr
        exact hr
  subst hτ
  refine ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', by simp, by simp, hqs, hqs', hms, hms', his, his', hpar,
    hmot, hmin, hidx, hmaj, ?_⟩
  rw [hT, applyTelA_piTelA _ _ _ _ (by
    simp only [List.length_append, List.length_singleton, minorDomsA_length, liftDomsA_length, hms, his, hqs,
      List.length_cons, List.length_nil]; omega) SubstA.id]
  congr 1
  rw [consListA_append, ← hms, ← his, show mot :: (ms ++ (is ++ [x])) = [mot] ++ ms ++ is ++ [x] by simp]
  exact substA_recBodyA mot x ms is

/-- THE RECURSOR'S ARGUMENTS SPLIT, no parameters: `recArgsSplitPA` at the empty parameter list. -/
theorem recArgsSplitA {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {as as' : List ExprA}
    (h : ArgsRelKA E I n ρ₀ K Γ
      (piTelA (recDomsA f ls [] idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 as as')
    (hlen : as.length = 1 + cds.length + idxs.length + 1) :
    ∃ (mot mot' x x' : ExprA) (ms ms' is is' : List ExprA),
      as = [mot] ++ ms ++ is ++ [x] ∧ as' = [mot'] ++ ms' ++ is' ++ [x'] ∧
      ms.length = cds.length ∧ ms'.length = cds.length ∧ is.length = idxs.length ∧
      is'.length = idxs.length ∧
      LRRelA E I n ρ₀ K Γ (motTyA f ls [] idxs wF wM).1 mot mot' ∧
      (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
        LRRelA E I n ρ₀ K Γ (substA (SubstA.cons mot SubstA.id) (minorTyA f ls wF wM 0 cds[i]).1) ms[i] ms'[i]) ∧
      (∀ (B : ExprA) (v : Level), ArgsRelKA E I n ρ₀ K Γ (piTelA idxs B v).1 is is') ∧
      LRRelA E I n ρ₀ K Γ (foldAppsA (.const f ls) is) x x' ∧
      applyTelA as (piTelA (recDomsA f ls [] idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
        some (foldAppsA mot (is ++ [x])) := by
  obtain ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', e, e', hq, hq', hms, hms', his, his', -, hmot, hmin,
    hidx, hmaj, happ⟩ := recArgsSplitPA f ls [] idxs wF wM w cds h (by rw [hlen, List.length_nil, Nat.zero_add])
  obtain rfl : qs = [] := List.eq_nil_of_length_eq_zero hq
  obtain rfl : qs' = [] := List.eq_nil_of_length_eq_zero hq'
  rw [List.nil_append] at e e'
  rw [show consListA ([] : List ExprA) SubstA.id = SubstA.id from rfl, substA_id] at hmot
  rw [List.nil_append] at hmaj
  refine ⟨mot, mot', x, x', ms, ms', is, is', e, e', hms, hms', his, his', hmot, hmin, fun B v => ?_, hmaj, happ⟩
  have := hidx B v
  rwa [show consListA ([] : List ExprA) SubstA.id = SubstA.id from rfl, substA_id] at this

end RecWalk

/-! ## (5) a recursor spine on a stuck major is an extended neutral -/

section RecNeut
variable {E : ResolvedEnvA}

theorem foldAppsA_snoc (h : ExprA) (xs : List ExprA) (x : ExprA) :
    foldAppsA h (xs ++ [x]) = .app (foldAppsA h xs) x := by
  rw [foldAppsA_append]; rfl

theorem foldAppsA_const_not_lam (r : Nat) (ls : List Level) (xs : List ExprA) :
    ∀ A u b, foldAppsA (.const r ls) xs ≠ .lam A u b := by
  intro A u b h
  have := congrArg (fun e => (appsSpineA e).1) h
  simp only [foldAppsA_const_head] at this
  exact ExprA.noConfusion this

/-- the concrete ι reads a recursor spine at its telescope arity. -/
theorem iotaFnA_len {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m) {ls : List Level}
    {args : List ExprA} {e' : ExprA} (h : iotaFnA E (foldAppsA (.const r ls) args) = some e') :
    args.length = piCountA m.mtypeA := by
  obtain ⟨r', ls', m', hsp, hres', _, hlen⟩ := iotaFnA_recHead E _ _ h
  rw [foldAppsA_const_head] at hsp hlen
  injection hsp with e1 _
  subst e1
  rw [hres] at hres'
  cases hres'
  exact hlen

/-- the concrete ι fires only at a recursor whose group has a constructor (O1-a). -/
theorem recHasCtorA_of_iotaFnA {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    {ls : List Level} {args : List ExprA} {e' : ExprA}
    (h : iotaFnA E (foldAppsA (.const r ls) args) = some e') : recHasCtorA r m = true := by
  obtain ⟨s, c, g, hs, _, hg, _⟩ := iotaFnA_some h
  have hsp := recSpineA_some hs
  rw [foldAppsA_const_head] at hsp
  injection hsp with e1 _
  injection e1 with e1 _
  subst e1
  obtain ⟨hrec, _⟩ := iotaGroupA_some hg
  rw [hres] at hrec
  cases hrec
  exact recHasCtorA_of_iotaGroupA hg

/-- below its major a recursor spine never head-steps. -/
theorem hStepFnA_recSpine_below (Γ : LCtxA) {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hcls : m.mclass = .recursorM) (ls : List Level) (args : List ExprA)
    (hlen : args.length < piCountA m.mtypeA) :
    hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) args) = none := by
  revert hlen
  refine snocInduction (P := fun args => args.length < piCountA m.mtypeA →
    hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) args) = none) ?_ ?_ args
  · intro _
    show (match E.members r with
      | some m => if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls) else none
      | none => none) = none
    rw [hres]
    show (if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls) else none) = none
    rw [hcls]
    rfl
  · intro as a ih hlen
    show hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) (as ++ [a])) = none
    rw [foldAppsA_snoc]
    have has : as.length < piCountA m.mtypeA := by simp at hlen; omega
    refine hStepFnA_app_none E (iotaFnA E) Γ (foldAppsA_const_not_lam r ls as) (ih has) ?_ ?_
    · cases hi : iotaFnA E (.app (foldAppsA (.const r ls) as) a) with
      | none => rfl
      | some e' =>
          rw [← foldAppsA_snoc] at hi
          have := iotaFnA_len hres hi
          simp at this hlen
          omega
    · cases hrec : recAtMajorA E (foldAppsA (.const r ls) as) with
      | false => rfl
      | true =>
          exfalso
          obtain ⟨r', ls', m', hsp, hres', _, hk⟩ := recAtMajorA_true hrec
          rw [foldAppsA_const_head] at hsp hk
          dsimp only at hk
          injection hsp with e1 _
          subst e1
          rw [hres] at hres'
          cases hres'
          simp at hlen
          omega

/-- at a recursor whose group has no constructor the major arm is off (O1-a). -/
theorem recAtMajorA_noCtor {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hno : recHasCtorA r m = false) (ls : List Level) (xs : List ExprA) :
    recAtMajorA E (foldAppsA (.const r ls) xs) = false := by
  unfold recAtMajorA
  rw [foldAppsA_const_head]
  show recAtMajorA' E (.const r ls) xs.length = false
  cases h : recAtMajorA' E (.const r ls) xs.length with
  | false => rfl
  | true =>
      obtain ⟨m', hm', _, _, hh⟩ := (recAtMajorA'_const E r ls _).1 h
      rw [hres] at hm'
      cases hm'
      rw [hno] at hh
      exact Bool.noConfusion hh

/-- O1-b-1: at a recursor that is not a unit group the K-unit arm reads nothing, at any spine. -/
theorem unitMinorA_foldAppsA_none {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hu : unitGroupA r m = false) (ls : List Level) (pre : List ExprA) :
    unitMinorA E (foldAppsA (.const r ls) pre) = none := by
  refine snocInduction (P := fun pre => unitMinorA E (foldAppsA (.const r ls) pre) = none) rfl ?_ pre
  intro xs x _
  rw [foldAppsA_snoc]
  show (if unitHeadA E (appsSpineA (foldAppsA (.const r ls) xs)).1 then some x else none) = none
  rw [foldAppsA_const_head]
  show (if (match E.members r with
    | some m => unitGroupA r m
    | none => false) then some x else none) = none
  rw [hres]
  dsimp only
  rw [hu]
  rfl

/-- W-1 (a): at a recursor that is no struct group's the struct arm reads nothing, at any spine. -/
theorem structArmA_foldAppsA_none {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hs : structGroupA r m = false) (ls : List Level) (pre : List ExprA) (x : ExprA) :
    structArmA E (foldAppsA (.const r ls) pre) x = none := by
  refine snocInduction (P := fun pre => structArmA E (foldAppsA (.const r ls) pre) x = none) rfl ?_ pre
  intro xs y _
  rw [foldAppsA_snoc]
  exact structArmA_of_not_struct (by rw [foldAppsA_const_head]) hres hs y x

/-- W-1 (e): a recursor spine's struct head is its member's struct test, at any spine. -/
theorem structHeadA_foldAppsA {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (ls : List Level) (pre : List ExprA) :
    structHeadA E (foldAppsA (.const r ls) pre) = structGroupA r m :=
  structHeadA_of_spine (by rw [foldAppsA_const_head]) hres

/-- O1-b-1: at a unit group's recursor the K-unit arm reads the last argument, at any spine. -/
theorem unitMinorA_foldAppsA_snoc {r : Nat} {m : CheckedMemberA}
    (hres : E.members r = some m) (hu : unitGroupA r m = true) (ls : List Level) (pre : List ExprA)
    (mn : ExprA) : unitMinorA E (foldAppsA (.const r ls) (pre ++ [mn])) = some mn := by
  rw [foldAppsA_snoc]
  show (if unitHeadA E (appsSpineA (foldAppsA (.const r ls) pre)).1 then some mn else none) = some mn
  rw [foldAppsA_const_head]
  show (if (match E.members r with
    | some m => unitGroupA r m
    | none => false) then some mn else none) = some mn
  rw [hres]
  dsimp only
  rw [hu]
  rfl

/-- at its major a recursor spine never head-steps when the major is stuck, or when the recursor's
    group has no constructor (O1-a): ι needs a constructor-headed major of the group, the major arm
    a stepping major of a group with a constructor. -/
theorem hStepFnA_recSpine_at (Γ : LCtxA) {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hcls : m.mclass = .recursorM) (ls : List Level) {pre : List ExprA} {N : ExprA}
    (hpre : pre.length + 1 = piCountA m.mtypeA)
    (hN : (StuckTmA E (iotaIfaceA E) Γ N ∧ unitGroupA r m = false ∧ structGroupA r m = false) ∨
      recHasCtorA r m = false) :
    hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) (pre ++ [N])) = none := by
  rw [foldAppsA_snoc, hStepFnA_app_nonlam E (iotaFnA E) Γ N (foldAppsA_const_not_lam r ls pre),
    hStepFnA_recSpine_below Γ hres hcls ls pre (by omega)]
  have hi : iotaFnA E (.app (foldAppsA (.const r ls) pre) N) = none := by
    cases hi : iotaFnA E (.app (foldAppsA (.const r ls) pre) N) with
    | none => rfl
    | some e' =>
        exfalso
        rw [← foldAppsA_snoc] at hi
        obtain ⟨s, c, g, hs, hc, hg, _⟩ := iotaFnA_some hi
        rw [recSpineA_of_spine (foldAppsA_const_head r ls (pre ++ [N]))] at hs
        injection hs with hs
        subst hs
        rcases hN with ⟨hN, _⟩ | hno
        · obtain ⟨lsN, hsp⟩ := spineHeadRefA_some hc
          obtain ⟨_, _, hcm, hcc, _⟩ := iotaGroupA_some hg
          exact hN.2 ⟨c, lsN, g.ctorM, hsp, hcm, hcc⟩
        · have hg' : iotaGroupA E r c = some g := hg
          rw [iotaGroupA_none_of_noCtor hres hno c] at hg'
          exact Option.noConfusion hg'
  have hp : structPosA E (foldAppsA (.const r ls) pre) = false := by
    rcases hN with ⟨_, _, hst⟩ | hno
    · exact structPosA_of_head (by rw [structHeadA_foldAppsA hres]; exact hst)
    · exact structPosA_of_not_rec (recAtMajorA_noCtor hres hno ls pre)
  dsimp only
  rw [hp, if_neg Bool.false_ne_true]
  simp only [hi]
  rcases hN with ⟨hN, hu, hst⟩ | hno
  · have hNs : hStepFnA E (iotaFnA E) Γ N = none := hN.1
    rw [unitMinorA_foldAppsA_none hres hu ls pre, hNs]
    cases recAtMajorA E (foldAppsA (.const r ls) pre) <;> rfl
  · rw [recAtMajorA_noCtor hres hno ls pre]
    rfl

/-- past its major a recursor spine never head-steps, on a stuck major or at a group without a
    constructor. -/
theorem hStepFnA_recSpine_above (Γ : LCtxA) {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hcls : m.mclass = .recursorM) (ls : List Level) {pre : List ExprA} {N : ExprA}
    (hpre : pre.length + 1 = piCountA m.mtypeA)
    (hN : (StuckTmA E (iotaIfaceA E) Γ N ∧ unitGroupA r m = false ∧ structGroupA r m = false) ∨
      recHasCtorA r m = false) (xs : List ExprA) :
    hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) (pre ++ [N] ++ xs)) = none := by
  refine snocInduction (P := fun xs =>
    hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) (pre ++ [N] ++ xs)) = none) ?_ ?_ xs
  · show hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) (pre ++ [N] ++ [])) = none
    rw [List.append_nil]; exact hStepFnA_recSpine_at Γ hres hcls ls hpre hN
  · intro xs x ih
    show hStepFnA E (iotaFnA E) Γ (foldAppsA (.const r ls) (pre ++ [N] ++ (xs ++ [x]))) = none
    rw [← List.append_assoc, foldAppsA_snoc]
    refine hStepFnA_app_none E (iotaFnA E) Γ (foldAppsA_const_not_lam r ls _) ih ?_ ?_
    · cases hi : iotaFnA E (.app (foldAppsA (.const r ls) (pre ++ [N] ++ xs)) x) with
      | none => rfl
      | some e' =>
          rw [← foldAppsA_snoc] at hi
          have := iotaFnA_len hres hi
          simp at this
          omega
    · cases hrec : recAtMajorA E (foldAppsA (.const r ls) (pre ++ [N] ++ xs)) with
      | false => rfl
      | true =>
          exfalso
          obtain ⟨r', ls', m', hsp, hres', _, hk⟩ := recAtMajorA_true hrec
          rw [foldAppsA_const_head] at hsp hk
          dsimp only at hk
          injection hsp with e1 _
          subst e1
          rw [hres] at hres'
          cases hres'
          simp at hk
          omega

/-- A RECURSOR SPINE AT ITS ARITY ON A STUCK MAJOR, OR OF A GROUP WITHOUT A CONSTRUCTOR (O1-a), IS
    AN EXTENDED NEUTRAL: under every world and every further application it never head-steps (the
    major stays stuck under weakening; a group without a constructor has no ι and no major arm), its
    head is a recursor (not a shape, not a constructor). -/
theorem neutKA_recApp (hE : EnvClosedA E) (hI : IotaLiftA (iotaIfaceA E)) {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} (hres : E.members r = some m) (hcls : m.mclass = .recursorM) {ls : List Level}
    {pre : List ExprA} {N : ExprA} (hpre : pre.length + 1 = piCountA m.mtypeA)
    (hN : (StuckTmA E (iotaIfaceA E) Γ N ∧ unitGroupA r m = false ∧ structGroupA r m = false) ∨
      recHasCtorA r m = false) :
    NeutKA E (iotaIfaceA E) Γ (foldAppsA (.const r ls) (pre ++ [N])) := by
  refine ⟨fun ρ hρ xs => ?_, ?_, ?_⟩
  · rw [wkExprA_foldAppsA, wkExprA_const, List.map_append, List.map_singleton, ← foldAppsA_append]
    exact hStepFnA_recSpine_above (wkCtxA ρ Γ) hres hcls ls (by rw [List.length_map]; exact hpre)
      (hN.imp (fun h => ⟨stuckTmA_wk hE hI ρ hρ h.1, h.2⟩) id) xs
  · rw [foldAppsA_const_head]
    rintro ⟨m', hm', hk⟩
    rw [hres] at hm'
    cases hm'
    rw [hcls] at hk
    exact MemberClass.noConfusion hk
  · rintro ⟨c, lsc, m', hsp, hm', hk⟩
    rw [foldAppsA_const_head] at hsp
    injection hsp with e1 _
    subst e1
    rw [hres] at hm'
    cases hm'
    rw [hcls] at hk
    exact MemberClass.noConfusion hk

end RecNeut

/-! ## (6) the converse walk, and iterated elimination -/

section RecJoin
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the minors' block, built from the minors each related at its type. -/
theorem argsRelKA_minorDomsA_join {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (B : ExprA) (w : Level) (σ₀ : SubstA) :
    (cds : List MinorDataA) → (j0 : Nat) → (pre : List ExprA) → pre.length = j0 → (ms ms' : List ExprA) →
    ms.length = cds.length → ms'.length = cds.length →
    (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelA E I n ρ₀ k Γ (substA σ₀ (minorTyA f ls wF wM np cds[i]).1) ms[i] ms'[i]) →
    ArgsRelKA E I n ρ₀ k Γ (substA (consListA pre σ₀) (piTelA (minorDomsA f ls wF wM np j0 cds) B w).1) ms ms'
  | [], _, _, _, [], [], _, _, _ => .nil _
  | [], _, _, _, _ :: _, _, hl, _, _ => nomatch hl
  | [], _, _, _, [], _ :: _, _, hl', _ => nomatch hl'
  | _ :: _, _, _, _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _, _, _, _ :: _, [], _, hl', _ => nomatch hl'
  | cd :: cds, j0, pre, hpre, m :: ms, m' :: ms', hl, hl', h => by
      simp only [minorDomsA, piTelA, substA_pi]
      refine .cons _ _ _ _ m m' ms ms' ?_ ?_
      · rw [← hpre, substA_consListA_liftA]
        exact h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      · rw [instantiate0A_substA_up, ← consListA_snoc]
        exact argsRelKA_minorDomsA_join f ls wF wM np B w σ₀ cds (j0 + 1) (pre ++ [m])
          (by rw [List.length_append, hpre]; rfl) ms ms' (Nat.succ.inj hl) (Nat.succ.inj hl')
          (fun i hi hi' hc => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hc))

/-- the indices' block, built from the index telescope itself. -/
theorem argsRelKA_liftDomsA_join {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level) (xs : List ExprA)
    (τ : SubstA) :
    (ds : List (ExprA × Level)) → (pre : List ExprA) → {as as' : List ExprA} →
    ArgsRelKA E I n ρ₀ k Γ (substA (consListA pre τ) (piTelA ds B' w').1) as as' → as.length = ds.length →
    ArgsRelKA E I n ρ₀ k Γ
      (substA (consListA pre (consListA xs τ)) (piTelA (liftDomsA pre.length xs.length ds) B w).1) as as'
  | [], _, [], as', h, _ => by
      have hl := argsRelKA_length h
      cases as' with
      | nil => exact .nil _
      | cons _ _ => exact nomatch hl
  | [], _, _ :: _, _, _, hl => nomatch hl
  | (_, _) :: _, _, [], _, _, hl => nomatch hl
  | (D, u) :: ds, pre, a :: as, _, h, hl => by
      simp only [liftDomsA, piTelA, substA_pi] at h ⊢
      cases h with
      | cons _ _ _ _ _ a' _ as' hr hs =>
          rw [instantiate0A_substA_up, ← consListA_snoc] at hs
          refine .cons _ _ _ _ a a' as as' ?_ ?_
          · rw [substA_consListA_liftA_cut]; exact hr
          · rw [instantiate0A_substA_up, ← consListA_snoc]
            have ih := argsRelKA_liftDomsA_join B B' w w' xs τ ds (pre ++ [a]) hs (Nat.succ.inj hl)
            rw [List.length_append, List.length_singleton] at ih
            exact ih

/-- the converse of `argsRelKA_piTelA_append_inv`. -/
theorem argsRelKA_piTelA_append {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level)
    (xs ys : List (ExprA × Level)) (σ : SubstA) {as₁ as₁' as₂ as₂' : List ExprA}
    (h₁ : ArgsRelKA E I n ρ₀ k Γ (substA σ (piTelA xs B' w').1) as₁ as₁') (hl : as₁.length = xs.length)
    (h₂ : ArgsRelKA E I n ρ₀ k Γ (substA (consListA as₁ σ) (piTelA ys B w).1) as₂ as₂') :
    ArgsRelKA E I n ρ₀ k Γ (substA σ (piTelA (xs ++ ys) B w).1) (as₁ ++ as₂) (as₁' ++ as₂') := by
  rw [piTelA_append]
  exact argsRelKA_append (argsRelKA_piTelA_body B' _ w' _ xs σ h₁ hl) (applyTelA_piTelA _ _ xs as₁ hl σ) h₂

/-- THE RECURSOR'S ARGUMENTS JOIN (M2-f (6c)): the converse of `recArgsSplitPA`. -/
theorem recArgsJoinPA {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {qs qs' : List ExprA} {mot mot' x x' : ExprA}
    {ms ms' is is' : List ExprA} (hqs : qs.length = params.length)
    (hms : ms.length = cds.length) (hms' : ms'.length = cds.length) (his : is.length = idxs.length)
    (hpar : ArgsRelKA E I n ρ₀ K Γ (piTelA params (.sort .zero) .zero).1 qs qs')
    (hmot : LRRelA E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) mot mot')
    (hmin : ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelA E I n ρ₀ K Γ (substA (SubstA.cons mot (consListA qs SubstA.id))
        (minorTyA f ls wF wM params.length cds[i]).1) ms[i] ms'[i])
    (hidx : ArgsRelKA E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (piTelA idxs (.sort .zero) .zero).1) is is')
    (hmaj : LRRelA E I n ρ₀ K Γ (foldAppsA (.const f ls) (qs ++ is)) x x') :
    ArgsRelKA E I n ρ₀ K Γ (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1
      (qs ++ ([mot] ++ ms ++ is ++ [x])) (qs' ++ ([mot'] ++ ms' ++ is' ++ [x'])) := by
  have hT : (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      substA SubstA.id (piTelA (params ++ ([motTyA f ls params idxs wF wM] ++ (minorDomsA f ls wF wM
        params.length 0 cds ++ (liftDomsA 0 (cds.length + 1) idxs ++
          [(liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length), wF)]))))
        (recBodyA idxs.length cds.length) w).1 := by
    rw [substA_id, recDomsA]
    simp only [List.append_assoc]
  rw [hT]
  refine argsRelKA_piTelA_append _ (.sort .zero) _ .zero _ _ _ (by rw [substA_id]; exact hpar) hqs ?_
  generalize hτ : consListA qs SubstA.id = τ at hmot hmin hidx ⊢
  rw [show [mot] ++ ms ++ is ++ [x] = [mot] ++ (ms ++ (is ++ [x])) by simp,
    show [mot'] ++ ms' ++ is' ++ [x'] = [mot'] ++ (ms' ++ (is' ++ [x'])) by simp]
  refine argsRelKA_piTelA_append _ (.sort .zero) _ .zero _ _ _ ?_ rfl ?_
  · simp only [piTelA, substA_pi]
    exact .cons _ _ _ _ mot mot' [] [] hmot (.nil _)
  refine argsRelKA_piTelA_append _ (.sort .zero) _ .zero _ _ _ ?_
    (hms.trans (minorDomsA_length _ _ _ _ _ _ _).symm) ?_
  · exact argsRelKA_minorDomsA_join f ls wF wM params.length (.sort .zero) .zero (SubstA.cons mot τ) cds 0 [] rfl
      ms ms' hms hms' hmin
  have e2 : ([mot] ++ ms).length = cds.length + 1 := by
    rw [List.length_append, hms, List.length_singleton]; omega
  have ec : consListA ms (consListA [mot] τ) = consListA ([mot] ++ ms) τ := by
    rw [consListA_append]
  refine argsRelKA_piTelA_append _ (.sort .zero) _ .zero _ _ _ ?_
    (his.trans (liftDomsA_length _ _ _).symm) ?_
  · have hIdx := argsRelKA_liftDomsA_join (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := K) (Γ := Γ)
      (.sort .zero) (.sort .zero) .zero .zero ([mot] ++ ms) τ idxs [] hidx his
    rw [show ([] : List ExprA).length = 0 from rfl, e2,
      show consListA ([] : List ExprA) (consListA ([mot] ++ ms) τ) = consListA ([mot] ++ ms) τ from rfl] at hIdx
    rw [ec]
    exact hIdx
  -- the major
  rw [ec]
  have hfun : (substA (consListA is τ) ∘ liftA 0 is.length) = substA τ :=
    funext fun e => substA_consListA_liftA is τ e
  have hd : substA (consListA is (consListA ([mot] ++ ms) τ))
      (liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length)) =
      foldAppsA (.const f ls) (qs ++ is) := by
    rw [← e2, ← his, substA_consListA_liftA_cut, famLocalsA, substA_foldAppsA, substA_const, List.map_append,
      paramLocalsA_consListA, List.map_map, hfun, ← hτ, ← hqs, paramLocalsA_consListA]
  simp only [piTelA, substA_pi]
  rw [hd]
  exact .cons _ _ _ _ x x' [] [] hmaj (.nil _)

/-- THE RECURSOR'S ARGUMENTS JOIN, no parameters: `recArgsJoinPA` at the empty parameter list. -/
theorem recArgsJoinA {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {mot mot' x x' : ExprA} {ms ms' is is' : List ExprA}
    (hms : ms.length = cds.length) (hms' : ms'.length = cds.length) (his : is.length = idxs.length)
    (hmot : LRRelA E I n ρ₀ K Γ (motTyA f ls [] idxs wF wM).1 mot mot')
    (hmin : ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelA E I n ρ₀ K Γ (substA (SubstA.cons mot SubstA.id) (minorTyA f ls wF wM 0 cds[i]).1) ms[i] ms'[i])
    (hidx : ArgsRelKA E I n ρ₀ K Γ (piTelA idxs (.sort .zero) .zero).1 is is')
    (hmaj : LRRelA E I n ρ₀ K Γ (foldAppsA (.const f ls) is) x x') :
    ArgsRelKA E I n ρ₀ K Γ (piTelA (recDomsA f ls [] idxs wF wM cds) (recBodyA idxs.length cds.length) w).1
      ([mot] ++ ms ++ is ++ [x]) ([mot'] ++ ms' ++ is' ++ [x']) := by
  have h := recArgsJoinPA (qs := []) (qs' := []) f ls [] idxs wF wM w cds rfl hms hms' his (.nil _)
    (by rw [show consListA ([] : List ExprA) SubstA.id = SubstA.id from rfl, substA_id]; exact hmot) hmin
    (by rw [show consListA ([] : List ExprA) SubstA.id = SubstA.id from rfl, substA_id]; exact hidx)
    (by rw [List.nil_append]; exact hmaj)
  rwa [List.nil_append, List.nil_append] at h

end RecJoin

/-! ## (7) the major's chain, expanded -/

section MajorChain
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the one-step chain. -/
theorem tyHRedStarA_step {Γ : LCtxA} {A z z' : ExprA} (hz : HasTyA E I n Γ z A) (hs : TyHRedA E I n Γ z z' A) :
    TyHRedStarA E I n Γ z z' A :=
  ⟨.cons z z' z' hz hs (.refl z' (tyHRedA_hasTy_right hs))⟩

/-- THE MAJOR'S CHAIN, EXPANDED: an application of a recursor spine at its major (`h`, of type
    `Π (x : Dm), B`) to a major that reduces along a chain at `D` (convertible to `Dm`) is related at `A`
    wherever its application to the chain's end is, provided each instance `B[w]` along the chain is a
    type convertible to `A`. Each step is a typed major step (`TyHRedA.major`, ι refusing at a stepping
    major) at the step's own instance, moved to `A`. -/
theorem LRRelA_expand_majorChain (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA}
    {h Dm B D A : ExprA} {u v : Level} (hrec : recAtMajorA E h = true) (hu : unitMinorA E h = none)
    (hst : structHeadA E h = false) (hhs : hStepFnA E I.fn Γ h = none)
    (hhT : HasTyA E I n Γ h (.pi Dm u B v)) (hBty : HasTyA E I n (.assumption Dm :: Γ) B (.sort v))
    (hDc : TyConvA E I n Γ D Dm)
    (hiota : ∀ z z', TyHRedA E I n Γ z z' D → I.fn (.app h z) = none) :
    {z N : ExprA} → TmChainA E I n Γ D z N →
    (∀ w, TyHRedStarA E I n Γ z w D → (∃ s, Nonempty (HasTyA E I n Γ (instantiate0A w B) (.sort s))) ∧
      Nonempty (TyConvA E I n Γ (instantiate0A w B) A)) →
    ∀ {b : ExprA}, LRRelA E I n ρ₀ k Γ A (.app h N) b → LRRelA E I n ρ₀ k Γ A (.app h z) b
  | _, _, .refl _ _, _, _, hb => hb
  | z, _, .cons _ z' _ hzD hs t, hw, _, hb => by
      have hzz' := tyHRedStarA_step hzD hs
      have ih := LRRelA_expand_majorChain hE hI hrec hu hst hhs hhT hBty hDc hiota t
        (fun w hw' => hw w (tyHRedStarA_trans hzz' hw')) hb
      obtain ⟨⟨s₁, ⟨hT₁⟩⟩, ⟨hc₁⟩⟩ := hw z (tyHRedStarA_refl hzD)
      obtain ⟨⟨s₂, ⟨hT₂⟩⟩, ⟨hc₂⟩⟩ := hw z' hzz'
      have hzDm : HasTyA E I n Γ z Dm := hasTyA_of_tyConvA hzD hDc
      have hz'Dm : HasTyA E I n Γ z' Dm := hasTyA_of_tyConvA (tyHRedA_hasTy_right hs) hDc
      have happ : HasTyA E I n Γ (.app h z) (instantiate0A z B) := .app Γ h z Dm B u v s₁ hBty hT₁ hhT hzDm
      have happ' : HasTyA E I n Γ (.app h z') (instantiate0A z' B) :=
        .app Γ h z' Dm B u v s₂ hBty hT₂ hhT hz'Dm
      have hrt : HasTyA E I n Γ (.app h z') (instantiate0A z B) :=
        hasTyA_of_tyConvA happ' (.trans _ _ _ _ hc₂ hc₁.symm)
      have hstep : TyHRedA E I n Γ (.app h z) (.app h z') (instantiate0A z B) :=
        .major Γ h z z' Dm B D u v hrec hu hst hhs (hiota z z' hs) hs hDc hhT hBty hrt
      exact LRRelA_expand_left hE hI ⟨⟨hasTyA_of_tyConvA happ hc₁⟩, ⟨.conv _ _ _ _ _ hstep hc₁⟩⟩ ih

/-- the right-hand form. -/
theorem LRRelA_expand_majorChain_right (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA}
    {h Dm B D A : ExprA} {u v : Level} (hrec : recAtMajorA E h = true) (hu : unitMinorA E h = none)
    (hst : structHeadA E h = false) (hhs : hStepFnA E I.fn Γ h = none)
    (hhT : HasTyA E I n Γ h (.pi Dm u B v)) (hBty : HasTyA E I n (.assumption Dm :: Γ) B (.sort v))
    (hDc : TyConvA E I n Γ D Dm)
    (hiota : ∀ z z', TyHRedA E I n Γ z z' D → I.fn (.app h z) = none) :
    {z N : ExprA} → TmChainA E I n Γ D z N →
    (∀ w, TyHRedStarA E I n Γ z w D → (∃ s, Nonempty (HasTyA E I n Γ (instantiate0A w B) (.sort s))) ∧
      Nonempty (TyConvA E I n Γ (instantiate0A w B) A)) →
    ∀ {a : ExprA}, LRRelA E I n ρ₀ k Γ A a (.app h N) → LRRelA E I n ρ₀ k Γ A a (.app h z)
  | _, _, .refl _ _, _, _, hb => hb
  | z, _, .cons _ z' _ hzD hs t, hw, _, hb => by
      have hzz' := tyHRedStarA_step hzD hs
      have ih := LRRelA_expand_majorChain_right hE hI hrec hu hst hhs hhT hBty hDc hiota t
        (fun w hw' => hw w (tyHRedStarA_trans hzz' hw')) hb
      obtain ⟨⟨s₁, ⟨hT₁⟩⟩, ⟨hc₁⟩⟩ := hw z (tyHRedStarA_refl hzD)
      obtain ⟨⟨s₂, ⟨hT₂⟩⟩, ⟨hc₂⟩⟩ := hw z' hzz'
      have hzDm : HasTyA E I n Γ z Dm := hasTyA_of_tyConvA hzD hDc
      have hz'Dm : HasTyA E I n Γ z' Dm := hasTyA_of_tyConvA (tyHRedA_hasTy_right hs) hDc
      have happ : HasTyA E I n Γ (.app h z) (instantiate0A z B) := .app Γ h z Dm B u v s₁ hBty hT₁ hhT hzDm
      have happ' : HasTyA E I n Γ (.app h z') (instantiate0A z' B) :=
        .app Γ h z' Dm B u v s₂ hBty hT₂ hhT hz'Dm
      have hrt : HasTyA E I n Γ (.app h z') (instantiate0A z B) :=
        hasTyA_of_tyConvA happ' (.trans _ _ _ _ hc₂ hc₁.symm)
      have hstep : TyHRedA E I n Γ (.app h z) (.app h z') (instantiate0A z B) :=
        .major Γ h z z' Dm B D u v hrec hu hst hhs (hiota z z' hs) hs hDc hhT hBty hrt
      exact LRRelA_expand_right hE hI ⟨⟨hasTyA_of_tyConvA happ hc₁⟩, ⟨.conv _ _ _ _ _ hstep hc₁⟩⟩ ih

end MajorChain

/-- the concrete ι reads a constructor-headed major. -/
theorem ctorHeadA_of_iotaFnA {E : ResolvedEnvA} {f z e' : ExprA} (h : iotaFnA E (.app f z) = some e') :
    CtorHeadA E z := by
  obtain ⟨s, c, g, hs, hc, hg, _⟩ := iotaFnA_some h
  have hsp := recSpineA_some hs
  have h2 := congrArg Prod.snd hsp
  rw [appsSpineA_app_snd] at h2
  have hz : z = s.major := by
    have h3 := (List.append_inj' h2 rfl).2
    injection h3
  subst hz
  obtain ⟨lsN, hspN⟩ := spineHeadRefA_some hc
  obtain ⟨_, _, hcm, hcc, _⟩ := iotaGroupA_some hg
  exact ⟨c, lsN, g.ctorM, hspN, hcm, hcc⟩

/-- at a stepping major the concrete ι refuses: a constructor-headed spine never steps. -/
theorem iotaFnA_app_none_of_step {E : ResolvedEnvA} {Γ : LCtxA} {f z z' : ExprA}
    (hs : hStepFnA E (iotaFnA E) Γ z = some z') : iotaFnA E (.app f z) = none := by
  cases hi : iotaFnA E (.app f z) with
  | none => rfl
  | some e' =>
      exfalso
      obtain ⟨c, ls, m, hsp, hm, hk⟩ := ctorHeadA_of_iotaFnA hi
      have hn := hStepFnA_constSpine_none (I := iotaIfaceA E) (iotaFnA_recHead E) hm (Or.inl (by rw [hk]; rfl))
        (by rw [hk]; exact fun h => MemberClass.noConfusion h) Γ z hsp
      have hn' : hStepFnA E (iotaFnA E) Γ z = none := hn
      rw [hn'] at hs
      exact Option.noConfusion hs

/-! ## (8) bounded views read only the family's levels -/

theorem exprLevelsBoundedA_substA_rev (k : Nat) :
    (e : ExprA) → (σ : SubstA) → exprLevelsBoundedA k (substA σ e) = true → exprLevelsBoundedA k e = true
  | .bvar _, _, _ => rfl
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .app f x, σ, h => by
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA_rev k f σ (boolAnd_left h), exprLevelsBoundedA_substA_rev k x σ (boolAnd_right h)]
      rfl
  | .lam a u b, σ, h => by
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA_rev k a σ (boolAnd_left (boolAnd_left h)), boolAnd_right (boolAnd_left h),
        exprLevelsBoundedA_substA_rev k b σ.up (boolAnd_right h)]
      rfl
  | .pi a u b v, σ, h => by
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA_rev k a σ (boolAnd_left (boolAnd_left (boolAnd_left h))),
        boolAnd_right (boolAnd_left (boolAnd_left h)),
        exprLevelsBoundedA_substA_rev k b σ.up (boolAnd_right (boolAnd_left h)), boolAnd_right h]
      rfl
  | .letE a w b, σ, h => by
      simp only [substA, exprLevelsBoundedA] at h ⊢
      rw [exprLevelsBoundedA_substA_rev k a σ (boolAnd_left (boolAnd_left h)),
        exprLevelsBoundedA_substA_rev k w σ (boolAnd_right (boolAnd_left h)),
        exprLevelsBoundedA_substA_rev k b σ.up (boolAnd_right h)]
      rfl
  | .lit _, _, _ => rfl

theorem exprLevelsBoundedA_foldAppsA_rev (k : Nat) :
    (h : ExprA) → (xs : List ExprA) → exprLevelsBoundedA k (foldAppsA h xs) = true →
    exprLevelsBoundedA k h = true ∧ ∀ x ∈ xs, exprLevelsBoundedA k x = true
  | _, [], hb => ⟨hb, fun _ hx => absurd hx (List.not_mem_nil _)⟩
  | h, x :: xs, hb => by
      obtain ⟨hhx, hxs⟩ := exprLevelsBoundedA_foldAppsA_rev k (.app h x) xs hb
      simp only [exprLevelsBoundedA] at hhx
      refine ⟨boolAnd_left hhx, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact boolAnd_right hhx
      · exact hxs y hy

/-- a field bounded at `k`. -/
def FieldA.BoundedA (k : Nat) : FieldA → Prop
  | .plain D u => exprLevelsBoundedA k D = true ∧ levelBounded k u = true
  | .drec idx => ∀ x ∈ idx, exprLevelsBoundedA k x = true
  | .drecD D idx => exprLevelsBoundedA k D = true ∧ ∀ x ∈ idx, exprLevelsBoundedA k x = true
  | .frec B uB Bs idx => (∀ d ∈ (B, uB) :: Bs, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true) ∧
      ∀ x ∈ idx, exprLevelsBoundedA k x = true

/-- a field's bound survives `norm`: `drecD`'s domain bound is dropped with the domain, its
    index bound is the `drec` arm's (R-NoDeltaRec-4d-iii). -/
theorem FieldA.BoundedA_norm {k : Nat} : ∀ F : FieldA, F.BoundedA k → F.norm.BoundedA k
  | .plain _ _, h => h
  | .drec _, h => h
  | .frec _ _ _ _, h => h
  | .drecD _ _, h => h.2

/-- a bounded function-recursive domain has bounded inner binders and indices. -/
theorem frecDomA_bounded (k f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    exprLevelsBoundedA k (frecDomA f ls w pl σ ds idx).1 = true →
    (∀ d ∈ ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true) ∧
      ∀ x ∈ idx, exprLevelsBoundedA k x = true
  | [], pl, σ, hb => by
      simp only [frecDomA] at hb
      obtain ⟨_, hxs⟩ := exprLevelsBoundedA_foldAppsA_rev k _ _ hb
      refine ⟨fun _ hd => absurd hd (List.not_mem_nil _), fun x hx => ?_⟩
      exact exprLevelsBoundedA_substA_rev k x σ (hxs _ (List.mem_append_right _ (List.mem_map_of_mem _ hx)))
  | (D, u) :: ds, pl, σ, hb => by
      simp only [frecDomA, exprLevelsBoundedA] at hb
      obtain ⟨hds, hidx⟩ := frecDomA_bounded k f ls w idx ds _ _ (boolAnd_right (boolAnd_left hb))
      refine ⟨fun d hd => ?_, hidx⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨exprLevelsBoundedA_substA_rev k D σ (boolAnd_left (boolAnd_left (boolAnd_left hb))),
          boolAnd_right (boolAnd_left (boolAnd_left hb))⟩
      · exact hds d hd

/-- a bounded field builder has bounded fields and result indices. A `drecD` field's domain reads
    its bound off the Π it wraps in; its indices occur in no stored type, so their bound is
    evidence — `hix`, which the view's `drecD_typed` supplies (R-NoDeltaRec-4d-i). -/
theorem ctorFieldsA_bounded (k f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    (∀ D idx, FieldA.drecD D idx ∈ fs → ∀ x ∈ idx, exprLevelsBoundedA k x = true) →
    exprLevelsBoundedA k (ctorFieldsA f ls w pl σ fs res).1 = true →
    (∀ F ∈ fs, F.BoundedA k) ∧ ∀ x ∈ res, exprLevelsBoundedA k x = true
  | [], pl, σ, _, hb => by
      simp only [ctorFieldsA] at hb
      obtain ⟨_, hxs⟩ := exprLevelsBoundedA_foldAppsA_rev k _ _ hb
      refine ⟨fun _ hF => absurd hF (List.not_mem_nil _), fun x hx => ?_⟩
      exact exprLevelsBoundedA_substA_rev k x σ (hxs _ (List.mem_append_right _ (List.mem_map_of_mem _ hx)))
  | .drecD D idx :: fs, pl, σ, hix, hb => by
      simp only [ctorFieldsA, exprLevelsBoundedA] at hb
      obtain ⟨hfs, hres⟩ := ctorFieldsA_bounded k f ls w res fs _ _
        (fun D' idx' hd => hix D' idx' (List.mem_cons_of_mem _ hd))
        (boolAnd_right (boolAnd_left hb))
      refine ⟨fun F hF => ?_, hres⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨exprLevelsBoundedA_substA_rev k D σ (boolAnd_left (boolAnd_left (boolAnd_left hb))),
          hix D idx (List.mem_cons_self _ _)⟩
      · exact hfs F hF
  | .plain D u :: fs, pl, σ, hix, hb => by
      simp only [ctorFieldsA, exprLevelsBoundedA] at hb
      obtain ⟨hfs, hres⟩ := ctorFieldsA_bounded k f ls w res fs _ _
        (fun D' idx' hd => hix D' idx' (List.mem_cons_of_mem _ hd)) (boolAnd_right (boolAnd_left hb))
      refine ⟨fun F hF => ?_, hres⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨exprLevelsBoundedA_substA_rev k D σ (boolAnd_left (boolAnd_left (boolAnd_left hb))),
          boolAnd_right (boolAnd_left (boolAnd_left hb))⟩
      · exact hfs F hF
  | .drec idx :: fs, pl, σ, hix, hb => by
      simp only [ctorFieldsA, exprLevelsBoundedA] at hb
      obtain ⟨hfs, hres⟩ := ctorFieldsA_bounded k f ls w res fs _ _
        (fun D' idx' hd => hix D' idx' (List.mem_cons_of_mem _ hd)) (boolAnd_right (boolAnd_left hb))
      refine ⟨fun F hF => ?_, hres⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · intro x hx
        obtain ⟨_, hxs⟩ := exprLevelsBoundedA_foldAppsA_rev k _ _ (boolAnd_left (boolAnd_left (boolAnd_left hb)))
        exact exprLevelsBoundedA_substA_rev k x σ (hxs _ (List.mem_append_right _ (List.mem_map_of_mem _ hx)))
      · exact hfs F hF
  | .frec B uB Bs idx :: fs, pl, σ, hix, hb => by
      simp only [ctorFieldsA, exprLevelsBoundedA] at hb
      obtain ⟨hfs, hres⟩ := ctorFieldsA_bounded k f ls w res fs _ _
        (fun D' idx' hd => hix D' idx' (List.mem_cons_of_mem _ hd)) (boolAnd_right (boolAnd_left hb))
      refine ⟨fun F hF => ?_, hres⟩
      rcases List.mem_cons.mp hF with rfl | hF
      · exact frecDomA_bounded k f ls w idx _ pl σ (boolAnd_left (boolAnd_left (boolAnd_left hb)))
      · exact hfs F hF

/-- a bounded telescope has bounded domains and body. -/
theorem piTelA_bounded (k : Nat) (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → exprLevelsBoundedA k (piTelA ds B w).1 = true →
    (∀ d ∈ ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true) ∧ exprLevelsBoundedA k B = true
  | [], hb => ⟨fun _ hd => absurd hd (List.not_mem_nil _), hb⟩
  | (D, u) :: ds, hb => by
      simp only [piTelA, exprLevelsBoundedA] at hb
      obtain ⟨hds, hB⟩ := piTelA_bounded k B w ds (boolAnd_right (boolAnd_left hb))
      refine ⟨fun d hd => ?_, hB⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨boolAnd_left (boolAnd_left (boolAnd_left hb)), boolAnd_right (boolAnd_left (boolAnd_left hb))⟩
      · exact hds d hd

theorem instDomsA_take (k : Nat) (ls : List Level) (ds : List (ExprA × Level))
    (h : ∀ d ∈ ds, exprLevelsBoundedA k d.1 = true ∧ levelBounded k d.2 = true) :
    instDomsA ls ds = instDomsA (ls.take k) ds := by
  simp only [instDomsA]
  apply List.map_congr_left
  intro d hd
  rw [instantiateLevelsA_take k ls d.1 (h d hd).1, instLevel_take k ls d.2 (h d hd).2]

theorem FieldA.instLevels_take (k : Nat) (ls : List Level) :
    (F : FieldA) → F.BoundedA k → F.instLevels ls = F.instLevels (ls.take k)
  | .plain D u, ⟨hD, hu⟩ => by
      simp only [FieldA.instLevels, instantiateLevelsA_take k ls D hD, instLevel_take k ls u hu]
  | .drec idx, h => by
      simp only [FieldA.instLevels]
      congr 1
      exact List.map_congr_left (fun x hx => instantiateLevelsA_take k ls x (h x hx))
  | .drecD D idx, ⟨hD, hidx⟩ => by
      simp only [FieldA.instLevels, instantiateLevelsA_take k ls D hD]
      congr 1
      exact List.map_congr_left (fun x hx => instantiateLevelsA_take k ls x (hidx x hx))
  | .frec B uB Bs idx, ⟨hds, hidx⟩ => by
      have hB := hds (B, uB) (List.mem_cons.mpr (Or.inl rfl))
      simp only [FieldA.instLevels, instantiateLevelsA_take k ls B hB.1, instLevel_take k ls uB hB.2,
        instDomsA_take k ls Bs (fun d hd => hds d (List.mem_cons_of_mem _ hd))]
      congr 1
      exact List.map_congr_left (fun x hx => instantiateLevelsA_take k ls x (hidx x hx))

/-- a constructor's minor data at a longer list is its data at the family's prefix. -/
theorem MinorDataA.inst_take {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (gc : GroupCtorA I E f fm fv) (ls : List Level) :
    gc.minorData.inst ls = gc.minorData.inst (ls.take fm.arity) := by
  have hb := gc.hlvl
  rw [gc.view.stored, gc.harity] at hb
  simp only [ctorTypeA] at hb
  obtain ⟨_, hbody⟩ := piTelA_bounded _ _ _ _ hb
  obtain ⟨hfs, hres⟩ := ctorFieldsA_bounded _ _ _ _ _ _ _ _
      (fun D idx hd => drecDTypedA_idxBounded gc.view.drecD_typed hd) hbody
  simp only [MinorDataA.inst, GroupCtorA.minorData]
  congr 2
  · exact List.map_congr_left (fun F hF => FieldA.instLevels_take _ ls F (hfs F hF))
  · exact List.map_congr_left (fun x hx => instantiateLevelsA_take _ ls x (hres x hx))

/-- THE GROUP'S RECURSOR TYPE AT A LONGER LIST: the binders built from the views at the family's
    prefix `ls.take a`, the motive's universe at the full list. -/
theorem instantiateLevelsA_groupRecTypeA {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (cs : List (GroupCtorA I E f fm fv)) (elim : RecElimA) (ls : List Level)
    (hlen : fm.arity ≤ ls.length) (hfm : exprLevelsBoundedA fm.arity fm.mtypeA = true) :
    instantiateLevelsA ls (groupRecTypeA fv cs elim) =
      (piTelA (recDomsA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
          (instDomsA (ls.take fm.arity) fv.indices) (instLevel (ls.take fm.arity) fv.sort)
          (instLevel ls (elim.motiveLevel fm.arity))
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))))
        (recBodyA fv.indices.length cs.length) (instLevel ls (elim.motiveLevel fm.arity))).1 := by
  rw [groupRecTypeA, instantiateLevelsA_recTypeA, instDomsA_recDomsA, canonLevelsA_instLevel_take ls _ hlen]
  rw [fv.stored] at hfm
  obtain ⟨hds, hB⟩ := piTelA_bounded _ _ _ _ hfm
  have hp : instDomsA ls fv.params = instDomsA (ls.take fm.arity) fv.params :=
    instDomsA_take _ ls _ (fun d hd => hds d (List.mem_append_left _ hd))
  have hi : instDomsA ls fv.indices = instDomsA (ls.take fm.arity) fv.indices :=
    instDomsA_take _ ls _ (fun d hd => hds d (List.mem_append_right _ hd))
  have hs : instLevel ls fv.sort = instLevel (ls.take fm.arity) fv.sort := instLevel_take _ ls _ hB
  have hc : (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst ls) =
      (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun gc _ => MinorDataA.inst_take gc ls)
  rw [hp, hi, hs, hc]
  simp only [List.length_map, List.length_reverse]

/-! ## (9) walks along a telescope, pointwise: split and join (moved from `RcicAnnIotaSR` for W-1 (c)) -/

section Walk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

/-- a pointwise list splits at a prefix: the prefix along the telescope, the rest along the
    telescope the prefix reaches. -/
theorem convArgsA_append_inv :
    {T : ExprA} → {xs xs' ys ys' : List ExprA} → xs.length = xs'.length →
    ConvArgsA E I n Γ T (xs ++ ys) (xs' ++ ys') →
    ∃ T', applyTelA xs T = some T' ∧ ConvArgsA E I n Γ T xs xs' ∧ ConvArgsA E I n Γ T' ys ys'
  | T, [], [], _, _, _, h => ⟨T, rfl, .nil _, h⟩
  | _, x :: xs, x' :: xs', ys, ys', hl, .cons A u B v _ _ _ _ hr hs => by
      obtain ⟨T', hT', h1, h2⟩ := convArgsA_append_inv (Nat.succ.inj hl) hs
      exact ⟨T', hT', .cons A u B v x x' xs xs' hr h1, h2⟩
  | _, [], _ :: _, _, _, hl, _ => nomatch hl
  | _, _ :: _, [], _, _, hl, _ => nomatch hl

/-- a pointwise list along a built telescope does not read the body. -/
theorem convArgsA_piTelA_body (B B' : ExprA) (w w' : Level) :
    (ds : List (ExprA × Level)) → (σ : SubstA) → {as as' : List ExprA} →
    ConvArgsA E I n Γ (substA σ (piTelA ds B w).1) as as' → as.length = ds.length →
    ConvArgsA E I n Γ (substA σ (piTelA ds B' w').1) as as'
  | [], _, [], as', h, _ => by
      have hl := convArgsA_length h
      cases as' with
      | nil => exact .nil _
      | cons _ _ => exact nomatch hl
  | [], _, _ :: _, _, _, hl => nomatch hl
  | (_, _) :: _, _, [], _, _, hl => nomatch hl
  | (D, u) :: ds, σ, a :: as, _, h, hl => by
      simp only [piTelA, substA_pi] at h ⊢
      cases h with
      | cons _ _ _ _ _ a' _ as' hr hs =>
          rw [instantiate0A_substA_up] at hs
          refine .cons _ _ _ _ a a' as as' hr ?_
          rw [instantiate0A_substA_up]
          exact convArgsA_piTelA_body B B' w w' ds _ hs (Nat.succ.inj hl)

/-- a pointwise list along a built telescope splits at a prefix of the binders. -/
theorem convArgsA_piTelA_append_inv (B : ExprA) (w : Level)
    (xs ys : List (ExprA × Level)) (σ : SubstA) {as₁ as₁' as₂ as₂' : List ExprA}
    (h : ConvArgsA E I n Γ (substA σ (piTelA (xs ++ ys) B w).1) (as₁ ++ as₂) (as₁' ++ as₂'))
    (hl : as₁.length = xs.length) (hl' : as₁'.length = xs.length) :
    (∀ (B' : ExprA) (w' : Level), ConvArgsA E I n Γ (substA σ (piTelA xs B' w').1) as₁ as₁') ∧
      ConvArgsA E I n Γ (substA (consListA as₁ σ) (piTelA ys B w).1) as₂ as₂' := by
  rw [piTelA_append] at h
  obtain ⟨T', hT', h1, h2⟩ := convArgsA_append_inv (hl.trans hl'.symm) h
  rw [applyTelA_piTelA _ _ xs as₁ hl σ] at hT'
  injection hT' with hT'
  subst hT'
  exact ⟨fun B' w' => convArgsA_piTelA_body _ B' _ w' xs σ h1 hl, h2⟩

/-- the converse of `convArgsA_piTelA_append_inv`. -/
theorem convArgsA_piTelA_append (B B' : ExprA) (w w' : Level)
    (xs ys : List (ExprA × Level)) (σ : SubstA) {as₁ as₁' as₂ as₂' : List ExprA}
    (h₁ : ConvArgsA E I n Γ (substA σ (piTelA xs B' w').1) as₁ as₁') (hl : as₁.length = xs.length)
    (h₂ : ConvArgsA E I n Γ (substA (consListA as₁ σ) (piTelA ys B w).1) as₂ as₂') :
    ConvArgsA E I n Γ (substA σ (piTelA (xs ++ ys) B w).1) (as₁ ++ as₂) (as₁' ++ as₂') := by
  rw [piTelA_append]
  exact convArgsA_append (convArgsA_piTelA_body B' _ w' _ xs σ h₁ hl) (applyTelA_piTelA _ _ xs as₁ hl σ) h₂

/-- the minors' block, split. -/
theorem convArgsA_minorDomsA (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (B : ExprA) (w : Level) (σ₀ : SubstA) :
    (cds : List MinorDataA) → (j0 : Nat) → (pre : List ExprA) → pre.length = j0 →
    {ms ms' : List ExprA} →
    ConvArgsA E I n Γ (substA (consListA pre σ₀) (piTelA (minorDomsA f ls wF wM np j0 cds) B w).1) ms ms' →
    ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      Nonempty (ConvA E I n Γ ms[i] ms'[i] (substA σ₀ (minorTyA f ls wF wM np cds[i]).1))
  | [], _, _, _, _, _, _, _, _, _, hc => absurd hc (Nat.not_lt_zero _)
  | cd :: cds, j0, pre, hpre, ms, ms', h, i, hi, hi', hc => by
      simp only [minorDomsA, piTelA, substA_pi] at h
      cases h with
      | nil => exact absurd hi (Nat.not_lt_zero _)
      | cons _ _ _ _ m m' ms₀ ms₀' hr hs =>
          cases i with
          | zero =>
              rw [← hpre, substA_consListA_liftA] at hr
              exact hr
          | succ i =>
              rw [instantiate0A_substA_up, ← consListA_snoc] at hs
              exact convArgsA_minorDomsA f ls wF wM np B w σ₀ cds (j0 + 1) (pre ++ [m])
                (by rw [List.length_append, hpre]; rfl) hs i (Nat.lt_of_succ_lt_succ hi)
                (Nat.lt_of_succ_lt_succ hi') (Nat.lt_of_succ_lt_succ hc)

/-- the minors' block, joined. -/
theorem convArgsA_minorDomsA_join (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (B : ExprA) (w : Level) (σ₀ : SubstA) :
    (cds : List MinorDataA) → (j0 : Nat) → (pre : List ExprA) → pre.length = j0 → (ms ms' : List ExprA) →
    ms.length = cds.length → ms'.length = cds.length →
    (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      Nonempty (ConvA E I n Γ ms[i] ms'[i] (substA σ₀ (minorTyA f ls wF wM np cds[i]).1))) →
    ConvArgsA E I n Γ (substA (consListA pre σ₀) (piTelA (minorDomsA f ls wF wM np j0 cds) B w).1) ms ms'
  | [], _, _, _, [], [], _, _, _ => .nil _
  | [], _, _, _, _ :: _, _, hl, _, _ => nomatch hl
  | [], _, _, _, [], _ :: _, _, hl', _ => nomatch hl'
  | _ :: _, _, _, _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _, _, _, _ :: _, [], _, hl', _ => nomatch hl'
  | cd :: cds, j0, pre, hpre, m :: ms, m' :: ms', hl, hl', h => by
      simp only [minorDomsA, piTelA, substA_pi]
      refine .cons _ _ _ _ m m' ms ms' ?_ ?_
      · rw [← hpre, substA_consListA_liftA]
        exact h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      · rw [instantiate0A_substA_up, ← consListA_snoc]
        exact convArgsA_minorDomsA_join f ls wF wM np B w σ₀ cds (j0 + 1) (pre ++ [m])
          (by rw [List.length_append, hpre]; rfl) ms ms' (Nat.succ.inj hl) (Nat.succ.inj hl')
          (fun i hi hi' hc => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hc))

/-- the indices' block, split: a telescope lifted past `xs` binders reads as itself once the `xs`
    values are skipped. -/
theorem convArgsA_liftDomsA (B B' : ExprA) (w w' : Level) (xs : List ExprA) (τ : SubstA) :
    (ds : List (ExprA × Level)) → (pre : List ExprA) → {as as' : List ExprA} →
    ConvArgsA E I n Γ (substA (consListA pre (consListA xs τ)) (piTelA (liftDomsA pre.length xs.length ds) B w).1)
      as as' → as.length = ds.length →
    ConvArgsA E I n Γ (substA (consListA pre τ) (piTelA ds B' w').1) as as'
  | [], _, [], as', h, _ => by
      have hl := convArgsA_length h
      cases as' with
      | nil => exact .nil _
      | cons _ _ => exact nomatch hl
  | [], _, _ :: _, _, _, hl => nomatch hl
  | (_, _) :: _, _, [], _, _, hl => nomatch hl
  | (D, u) :: ds, pre, a :: as, _, h, hl => by
      simp only [liftDomsA, piTelA, substA_pi] at h ⊢
      cases h with
      | cons _ _ _ _ _ a' _ as' hr hs =>
          rw [substA_consListA_liftA_cut] at hr
          rw [instantiate0A_substA_up, ← consListA_snoc] at hs
          refine .cons _ _ _ _ a a' as as' hr ?_
          rw [instantiate0A_substA_up, ← consListA_snoc]
          have hs' : ConvArgsA E I n Γ (substA (consListA (pre ++ [a]) (consListA xs τ))
              (piTelA (liftDomsA (pre ++ [a]).length xs.length ds) B w).1) as as' := by
            rw [List.length_append, List.length_singleton]; exact hs
          exact convArgsA_liftDomsA B B' w w' xs τ ds (pre ++ [a]) hs' (Nat.succ.inj hl)

/-- the indices' block, joined. -/
theorem convArgsA_liftDomsA_join (B B' : ExprA) (w w' : Level) (xs : List ExprA) (τ : SubstA) :
    (ds : List (ExprA × Level)) → (pre : List ExprA) → {as as' : List ExprA} →
    ConvArgsA E I n Γ (substA (consListA pre τ) (piTelA ds B' w').1) as as' → as.length = ds.length →
    ConvArgsA E I n Γ
      (substA (consListA pre (consListA xs τ)) (piTelA (liftDomsA pre.length xs.length ds) B w).1) as as'
  | [], _, [], as', h, _ => by
      have hl := convArgsA_length h
      cases as' with
      | nil => exact .nil _
      | cons _ _ => exact nomatch hl
  | [], _, _ :: _, _, _, hl => nomatch hl
  | (_, _) :: _, _, [], _, _, hl => nomatch hl
  | (D, u) :: ds, pre, a :: as, _, h, hl => by
      simp only [liftDomsA, piTelA, substA_pi] at h ⊢
      cases h with
      | cons _ _ _ _ _ a' _ as' hr hs =>
          rw [instantiate0A_substA_up, ← consListA_snoc] at hs
          refine .cons _ _ _ _ a a' as as' ?_ ?_
          · rw [substA_consListA_liftA_cut]; exact hr
          · rw [instantiate0A_substA_up, ← consListA_snoc]
            have ih := convArgsA_liftDomsA_join B B' w w' xs τ ds (pre ++ [a]) hs (Nat.succ.inj hl)
            rw [List.length_append, List.length_singleton] at ih
            exact ih

/-- the recursor's telescope, as one substituted telescope over its blocks. -/
theorem recTel_blocks (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM w : Level)
    (cds : List MinorDataA) :
    (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      substA SubstA.id (piTelA (params ++ ([motTyA f ls params idxs wF wM] ++ (minorDomsA f ls wF wM
        params.length 0 cds ++ (liftDomsA 0 (cds.length + 1) idxs ++
          [(liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length), wF)]))))
        (recBodyA idxs.length cds.length) w).1 := by
  rw [substA_id, recDomsA]
  simp only [List.append_assoc]

/-- the major's domain under the recursor's values: the family at the parameters and the indices. -/
theorem substA_majorDom (f : Nat) (ls : List Level) (np : Nat) (idxs : List (ExprA × Level))
    (cds : List MinorDataA) (qs : List ExprA) (mot : ExprA) (ms is : List ExprA)
    (hqs : qs.length = np) (hms : ms.length = cds.length) (his : is.length = idxs.length) :
    substA (consListA is (consListA ([mot] ++ ms) (consListA qs SubstA.id)))
      (liftA idxs.length (cds.length + 1) (famLocalsA f ls np idxs.length)) =
      foldAppsA (.const f ls) (qs ++ is) := by
  have e2 : ([mot] ++ ms).length = cds.length + 1 := by
    rw [List.length_append, hms, List.length_singleton]; omega
  have hfun : (substA (consListA is (consListA qs SubstA.id)) ∘ liftA 0 is.length) =
      substA (consListA qs SubstA.id) :=
    funext fun e => substA_consListA_liftA is _ e
  rw [← e2, ← his, substA_consListA_liftA_cut, famLocalsA, substA_foldAppsA, substA_const, List.map_append,
    paramLocalsA_consListA, List.map_map, hfun, ← hqs, paramLocalsA_consListA]

/-- THE RECURSOR'S ARGUMENTS SPLIT, pointwise: parameters along the parameter telescope; then, under
    the parameters' values, the motive at its type, each minor at its type under the left motive, the
    indices along the index telescope, and the major at the family application; the type reached is the
    motive at the indices and the major. -/
theorem recArgsSplitC (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {as as' : List ExprA}
    (h : ConvArgsA E I n Γ
      (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 as as')
    (hlen : as.length = params.length + (1 + cds.length + idxs.length + 1)) :
    ∃ (qs qs' : List ExprA) (mot mot' x x' : ExprA) (ms ms' is is' : List ExprA),
      as = qs ++ ([mot] ++ ms ++ is ++ [x]) ∧ as' = qs' ++ ([mot'] ++ ms' ++ is' ++ [x']) ∧
      qs.length = params.length ∧ qs'.length = params.length ∧
      ms.length = cds.length ∧ ms'.length = cds.length ∧ is.length = idxs.length ∧
      is'.length = idxs.length ∧
      (∀ (B : ExprA) (v : Level), ConvArgsA E I n Γ (piTelA params B v).1 qs qs') ∧
      Nonempty (ConvA E I n Γ mot mot' (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1)) ∧
      (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
        Nonempty (ConvA E I n Γ ms[i] ms'[i] (substA (SubstA.cons mot (consListA qs SubstA.id))
          (minorTyA f ls wF wM params.length cds[i]).1))) ∧
      (∀ (B : ExprA) (v : Level),
        ConvArgsA E I n Γ (substA (consListA qs SubstA.id) (piTelA idxs B v).1) is is') ∧
      Nonempty (ConvA E I n Γ x x' (foldAppsA (.const f ls) (qs ++ is))) ∧
      applyTelA as (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
        some (foldAppsA mot (is ++ [x])) := by
  have hlen' : as'.length = params.length + (1 + cds.length + idxs.length + 1) :=
    (convArgsA_length h).symm.trans hlen
  obtain ⟨qs, rs, rfl, hqs⟩ : ∃ qs rs, as = qs ++ rs ∧ qs.length = params.length :=
    ⟨as.take params.length, as.drop params.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨qs', rs', rfl, hqs'⟩ : ∃ qs rs, as' = qs ++ rs ∧ qs.length = params.length :=
    ⟨as'.take params.length, as'.drop params.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  have hrl : rs.length = 1 + cds.length + idxs.length + 1 := by
    rw [List.length_append, hqs] at hlen; omega
  have hrl' : rs'.length = 1 + cds.length + idxs.length + 1 := by
    rw [List.length_append, hqs'] at hlen'; omega
  have hPh := h
  rw [recTel_blocks] at hPh
  obtain ⟨hP, h⟩ := convArgsA_piTelA_append_inv _ _ _ _ _ hPh hqs hqs'
  have hpar : ∀ (B : ExprA) (v : Level), ConvArgsA E I n Γ (piTelA params B v).1 qs qs' := by
    intro B v
    have := hP B v
    rwa [substA_id] at this
  generalize hτ : consListA qs SubstA.id = τ at h
  obtain ⟨mot, r1, rfl⟩ : ∃ mot r1, rs = mot :: r1 := by
    cases rs with
    | nil => exact nomatch hrl
    | cons a r => exact ⟨a, r, rfl⟩
  obtain ⟨mot', r1', rfl⟩ : ∃ mot r1, rs' = mot :: r1 := by
    cases rs' with
    | nil => exact nomatch hrl'
    | cons a r => exact ⟨a, r, rfl⟩
  have hr1 : r1.length = cds.length + idxs.length + 1 := by rw [List.length_cons] at hrl; omega
  have hr1' : r1'.length = cds.length + idxs.length + 1 := by rw [List.length_cons] at hrl'; omega
  obtain ⟨ms, r2, rfl, hms⟩ : ∃ ms r2, r1 = ms ++ r2 ∧ ms.length = cds.length :=
    ⟨r1.take cds.length, r1.drop cds.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨ms', r2', rfl, hms'⟩ : ∃ ms r2, r1' = ms ++ r2 ∧ ms.length = cds.length :=
    ⟨r1'.take cds.length, r1'.drop cds.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  have hr2 : r2.length = idxs.length + 1 := by rw [List.length_append] at hr1; omega
  have hr2' : r2'.length = idxs.length + 1 := by rw [List.length_append] at hr1'; omega
  obtain ⟨is, xl, rfl, his⟩ : ∃ is xl, r2 = is ++ xl ∧ is.length = idxs.length :=
    ⟨r2.take idxs.length, r2.drop idxs.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨is', xl', rfl, his'⟩ : ∃ is xl, r2' = is ++ xl ∧ is.length = idxs.length :=
    ⟨r2'.take idxs.length, r2'.drop idxs.length, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega⟩
  have hxl : xl.length = 1 := by rw [List.length_append] at hr2; omega
  have hxl' : xl'.length = 1 := by rw [List.length_append] at hr2'; omega
  obtain ⟨x, rfl⟩ : ∃ x, xl = [x] := by
    match xl, hxl with
    | [x], _ => exact ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ : ∃ x, xl' = [x] := by
    match xl', hxl' with
    | [x], _ => exact ⟨x, rfl⟩
  -- the motive
  have h₀ := h
  rw [show mot :: (ms ++ (is ++ [x])) = [mot] ++ (ms ++ (is ++ [x])) from rfl,
    show mot' :: (ms' ++ (is' ++ [x'])) = [mot'] ++ (ms' ++ (is' ++ [x'])) from rfl] at h₀
  obtain ⟨hM, h₁⟩ := convArgsA_piTelA_append_inv _ _ _ _ _ h₀ rfl rfl
  have hmot : Nonempty (ConvA E I n Γ mot mot' (substA τ (motTyA f ls params idxs wF wM).1)) := by
    have h := hM (.sort .zero) .zero
    simp only [piTelA, substA_pi] at h
    cases h with
    | cons _ _ _ _ _ _ _ _ hr _ => exact hr
  -- the minors
  obtain ⟨hMin, h₂⟩ := convArgsA_piTelA_append_inv _ _ _ _ _ h₁
    (hms.trans (minorDomsA_length _ _ _ _ _ _ _).symm) (hms'.trans (minorDomsA_length _ _ _ _ _ _ _).symm)
  have hmin := fun i hi hi' hc => convArgsA_minorDomsA (E := E) (I := I) (n := n) (Γ := Γ)
    f ls wF wM params.length (.sort .zero) .zero (consListA [mot] τ) cds 0 [] rfl (hMin (.sort .zero) .zero) i hi hi'
    hc
  -- the indices and the major
  obtain ⟨hIdx, h₃⟩ := convArgsA_piTelA_append_inv _ _ _ _ _ h₂
    (his.trans (liftDomsA_length _ _ _).symm) (his'.trans (liftDomsA_length _ _ _).symm)
  have hidx : ∀ (B : ExprA) (v : Level), ConvArgsA E I n Γ (substA τ (piTelA idxs B v).1) is is' := by
    intro B v
    have h := hIdx (.sort .zero) .zero
    rw [← consListA_append] at h
    have h' : ConvArgsA E I n Γ (substA (consListA [] (consListA ([mot] ++ ms) τ))
        (piTelA (liftDomsA ([] : List ExprA).length ([mot] ++ ms).length idxs) (.sort .zero) .zero).1) is is' := by
      have e : ([mot] ++ ms).length = cds.length + 1 := by
        rw [List.length_append, hms, List.length_singleton]; omega
      rw [e]; exact h
    exact convArgsA_liftDomsA (.sort .zero) B .zero v ([mot] ++ ms) τ idxs [] h' his
  have hmaj : Nonempty (ConvA E I n Γ x x' (foldAppsA (.const f ls) (qs ++ is))) := by
    simp only [piTelA, substA_pi] at h₃
    cases h₃ with
    | cons _ _ _ _ _ _ _ _ hr _ =>
        rw [← consListA_append [mot] ms τ, ← hτ, substA_majorDom f ls params.length idxs cds qs mot ms is
          hqs hms his] at hr
        exact hr
  subst hτ
  refine ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', by simp, by simp, hqs, hqs', hms, hms', his, his', hpar,
    hmot, hmin, hidx, hmaj, ?_⟩
  rw [recTel_blocks, applyTelA_piTelA _ _ _ _ (by
    simp only [List.length_append, List.length_singleton, minorDomsA_length, liftDomsA_length, hms, his, hqs,
      List.length_cons, List.length_nil]; omega) SubstA.id]
  congr 1
  rw [consListA_append, ← hms, ← his, show mot :: (ms ++ (is ++ [x])) = [mot] ++ ms ++ is ++ [x] by simp]
  exact substA_recBodyA mot x ms is

/-- THE RECURSOR'S ARGUMENTS JOIN, pointwise: the converse of `recArgsSplitC`. -/
theorem recArgsJoinC (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {qs qs' : List ExprA} {mot mot' x x' : ExprA}
    {ms ms' is is' : List ExprA} (hqs : qs.length = params.length)
    (hms : ms.length = cds.length) (hms' : ms'.length = cds.length) (his : is.length = idxs.length)
    (hpar : ConvArgsA E I n Γ (piTelA params (.sort .zero) .zero).1 qs qs')
    (hmot : Nonempty (ConvA E I n Γ mot mot' (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1)))
    (hmin : ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      Nonempty (ConvA E I n Γ ms[i] ms'[i] (substA (SubstA.cons mot (consListA qs SubstA.id))
        (minorTyA f ls wF wM params.length cds[i]).1)))
    (hidx : ConvArgsA E I n Γ (substA (consListA qs SubstA.id) (piTelA idxs (.sort .zero) .zero).1) is is')
    (hmaj : Nonempty (ConvA E I n Γ x x' (foldAppsA (.const f ls) (qs ++ is)))) :
    ConvArgsA E I n Γ (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1
      (qs ++ ([mot] ++ ms ++ is ++ [x])) (qs' ++ ([mot'] ++ ms' ++ is' ++ [x'])) := by
  rw [recTel_blocks]
  refine convArgsA_piTelA_append _ (.sort .zero) _ .zero _ _ _ (by rw [substA_id]; exact hpar) hqs ?_
  generalize hτ : consListA qs SubstA.id = τ at hmot hmin hidx ⊢
  rw [show [mot] ++ ms ++ is ++ [x] = [mot] ++ (ms ++ (is ++ [x])) by simp,
    show [mot'] ++ ms' ++ is' ++ [x'] = [mot'] ++ (ms' ++ (is' ++ [x'])) by simp]
  refine convArgsA_piTelA_append _ (.sort .zero) _ .zero _ _ _ ?_ rfl ?_
  · simp only [piTelA, substA_pi]
    exact .cons _ _ _ _ mot mot' [] [] hmot (.nil _)
  refine convArgsA_piTelA_append _ (.sort .zero) _ .zero _ _ _ ?_
    (hms.trans (minorDomsA_length _ _ _ _ _ _ _).symm) ?_
  · exact convArgsA_minorDomsA_join f ls wF wM params.length (.sort .zero) .zero (SubstA.cons mot τ) cds 0 []
      rfl ms ms' hms hms' hmin
  have e2 : ([mot] ++ ms).length = cds.length + 1 := by
    rw [List.length_append, hms, List.length_singleton]; omega
  have ec : consListA ms (consListA [mot] τ) = consListA ([mot] ++ ms) τ := by
    rw [consListA_append]
  refine convArgsA_piTelA_append _ (.sort .zero) _ .zero _ _ _ ?_
    (his.trans (liftDomsA_length _ _ _).symm) ?_
  · have hIdx := convArgsA_liftDomsA_join (E := E) (I := I) (n := n) (Γ := Γ)
      (.sort .zero) (.sort .zero) .zero .zero ([mot] ++ ms) τ idxs [] hidx his
    rw [show ([] : List ExprA).length = 0 from rfl, e2,
      show consListA ([] : List ExprA) (consListA ([mot] ++ ms) τ) = consListA ([mot] ++ ms) τ from rfl] at hIdx
    rw [ec]
    exact hIdx
  -- the major
  rw [ec]
  have hd := substA_majorDom f ls params.length idxs cds qs mot ms is hqs hms his
  rw [hτ] at hd
  simp only [piTelA, substA_pi]
  rw [hd]
  exact .cons _ _ _ _ x x' [] [] hmaj (.nil _)

end Walk

#print axioms recTypeA_propTy
#print axioms substA_minorFieldsA
#print axioms instantiate0A_minorFieldsA_plain
#print axioms substA_minorFieldsA_drec
#print axioms instantiateLevelsA_minorFieldsA
#print axioms instantiateLevelsA_motTyA
#print axioms instantiateLevelsA_minorTyA
#print axioms instDomsA_recDomsA
#print axioms canonLevelsA_instLevel_take
#print axioms instantiateLevelsA_take
#print axioms substA_consListA_liftA_cut
#print axioms argsRelKA_piTelA_body
#print axioms argsRelKA_piTelA_append_inv
#print axioms recArgsSplitPA
#print axioms recArgsSplitA
#print axioms recHasCtorA_of_iotaFnA
#print axioms hStepFnA_recSpine_below
#print axioms recAtMajorA_noCtor
#print axioms hStepFnA_recSpine_at
#print axioms hStepFnA_recSpine_above
#print axioms neutKA_recApp
#print axioms argsRelKA_piTelA_append
#print axioms recArgsJoinPA
#print axioms recArgsJoinA
#print axioms LRRelA_expand_majorChain
#print axioms LRRelA_expand_majorChain_right
#print axioms ctorHeadA_of_iotaFnA
#print axioms iotaFnA_app_none_of_step
#print axioms MinorDataA.inst_take
#print axioms instantiateLevelsA_groupRecTypeA
#print axioms structArmA_foldAppsA_none
#print axioms recArgsSplitC
#print axioms recArgsJoinC

end Rcic.Declarative.Ann
