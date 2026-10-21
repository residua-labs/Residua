import rcic.RcicAnnRecTel
import rcic.RcicAnnLREnvG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnFamSemG
import rcic.RcicAnnCtorSemG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnFrecDomSynG
import rcic.RcicAnnIotaWfG
import rcic.RcicAnnLRRowsG
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
  minors, the indices and the major (`recArgsSplitAg`), and join back (`recArgsJoinAg`);
* a recursor spine at its arity on a stuck major, or of a group without a constructor (O1-a), is an
  extended neutral (`neutKA_recApp`);
* an application at the major expands along the major's chain (`LRRelA_expand_majorChaing`), each step
  a typed major step (R-MajorStep), ι refusing at a stepping major (`iotaFnA_app_none_of_step`);
* iterated elimination (`LRRelA_appsg`, in `RcicAnnTelIntro`), the converse of the telescope lemma.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) a recursor type whose motive level is zero is a proposition -/

/-! ## (2) the minor's builder laws: substitution, levels, the walk's two steps -/

/-! ## (3) level instantiation through the recursor builder -/

/-! ## (4) the walk along the recursor's telescope -/

section RecWalk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a related list along a built telescope does not read the body. -/
theorem argsRelKA_piTelA_bodyg {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level) :
    (ds : List (ExprA × Level)) → (σ : SubstA) → {as as' : List ExprA} →
    ArgsRelKAg E I n ρ₀ k Γ (substA σ (piTelA ds B w).1) as as' → as.length = ds.length →
    ArgsRelKAg E I n ρ₀ k Γ (substA σ (piTelA ds B' w').1) as as'
  | [], _, [], as', h, _ => by
      have hl := argsRelKA_lengthg h
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
          exact argsRelKA_piTelA_bodyg B B' w w' ds _ hs (Nat.succ.inj hl)

/-- a related list along a built telescope splits at a prefix of the binders: the prefix along the
    prefix's telescope (any body), the rest along the rest under the prefix's values. -/
theorem argsRelKA_piTelA_append_invg {k : Nat} {Γ : LCtxA} (B : ExprA) (w : Level)
    (xs ys : List (ExprA × Level)) (σ : SubstA) {as₁ as₁' as₂ as₂' : List ExprA}
    (h : ArgsRelKAg E I n ρ₀ k Γ (substA σ (piTelA (xs ++ ys) B w).1) (as₁ ++ as₂) (as₁' ++ as₂'))
    (hl : as₁.length = xs.length) (hl' : as₁'.length = xs.length) :
    (∀ (B' : ExprA) (w' : Level), ArgsRelKAg E I n ρ₀ k Γ (substA σ (piTelA xs B' w').1) as₁ as₁') ∧
      ArgsRelKAg E I n ρ₀ k Γ (substA (consListA as₁ σ) (piTelA ys B w).1) as₂ as₂' := by
  rw [piTelA_append] at h
  obtain ⟨T', hT', h1, h2⟩ := argsRelKA_append_invg (hl.trans hl'.symm) h
  rw [applyTelA_piTelA _ _ xs as₁ hl σ] at hT'
  injection hT' with hT'
  subst hT'
  exact ⟨fun B' w' => argsRelKA_piTelA_bodyg _ B' _ w' xs σ h1 hl, h2⟩

/-- the minors' block: each minor related at its type under the values before the block. -/
theorem argsRelKA_minorDomsAg {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (B : ExprA) (w : Level) (σ₀ : SubstA) :
    (cds : List MinorDataA) → (j0 : Nat) → (pre : List ExprA) → pre.length = j0 →
    {ms ms' : List ExprA} →
    ArgsRelKAg E I n ρ₀ k Γ (substA (consListA pre σ₀) (piTelA (minorDomsA f ls wF wM np j0 cds) B w).1) ms ms' →
    ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelAg E I n ρ₀ k Γ (substA σ₀ (minorTyA f ls wF wM np cds[i]).1) ms[i] ms'[i]
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
              exact argsRelKA_minorDomsAg f ls wF wM np B w σ₀ cds (j0 + 1) (pre ++ [m])
                (by rw [List.length_append, hpre]; rfl) hs i (Nat.lt_of_succ_lt_succ hi)
                (Nat.lt_of_succ_lt_succ hi') (Nat.lt_of_succ_lt_succ hc)

/-- the indices' block: a telescope lifted past `xs` binders at its cutoff reads as the telescope
    itself once the `xs` values are skipped. -/
theorem argsRelKA_liftDomsAg {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level) (xs : List ExprA) (τ : SubstA) :
    (ds : List (ExprA × Level)) → (pre : List ExprA) → {as as' : List ExprA} →
    ArgsRelKAg E I n ρ₀ k Γ (substA (consListA pre (consListA xs τ)) (piTelA (liftDomsA pre.length xs.length ds) B w).1)
      as as' → as.length = ds.length →
    ArgsRelKAg E I n ρ₀ k Γ (substA (consListA pre τ) (piTelA ds B' w').1) as as'
  | [], _, [], as', h, _ => by
      have hl := argsRelKA_lengthg h
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
          have hs' : ArgsRelKAg E I n ρ₀ k Γ (substA (consListA (pre ++ [a]) (consListA xs τ))
              (piTelA (liftDomsA (pre ++ [a]).length xs.length ds) B w).1) as as' := by
            rw [List.length_append, List.length_singleton]; exact hs
          exact argsRelKA_liftDomsAg B B' w w' xs τ ds (pre ++ [a]) hs' (Nat.succ.inj hl)

/-- THE RECURSOR'S ARGUMENTS SPLIT (M2-f (6c)): related arguments along the recursor's telescope are
    related parameters along the parameter telescope and then, under the parameters' values, a related
    motive, the minors each related at its type under the left motive, related indices along the index
    telescope, and a related major at the family application at the parameters and the indices; the
    codomain is the motive at the indices and the major. -/
theorem recArgsSplitPAg {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {as as' : List ExprA}
    (h : ArgsRelKAg E I n ρ₀ K Γ
      (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 as as')
    (hlen : as.length = params.length + (1 + cds.length + idxs.length + 1)) :
    ∃ (qs qs' : List ExprA) (mot mot' x x' : ExprA) (ms ms' is is' : List ExprA),
      as = qs ++ ([mot] ++ ms ++ is ++ [x]) ∧ as' = qs' ++ ([mot'] ++ ms' ++ is' ++ [x']) ∧
      qs.length = params.length ∧ qs'.length = params.length ∧
      ms.length = cds.length ∧ ms'.length = cds.length ∧ is.length = idxs.length ∧
      is'.length = idxs.length ∧
      (∀ (B : ExprA) (v : Level), ArgsRelKAg E I n ρ₀ K Γ (piTelA params B v).1 qs qs') ∧
      LRRelAg E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) mot mot' ∧
      (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
        LRRelAg E I n ρ₀ K Γ (substA (SubstA.cons mot (consListA qs SubstA.id))
          (minorTyA f ls wF wM params.length cds[i]).1) ms[i] ms'[i]) ∧
      (∀ (B : ExprA) (v : Level),
        ArgsRelKAg E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (piTelA idxs B v).1) is is') ∧
      LRRelAg E I n ρ₀ K Γ (foldAppsA (.const f ls) (qs ++ is)) x x' ∧
      applyTelA as (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
        some (foldAppsA mot (is ++ [x])) := by
  have hlen' : as'.length = params.length + (1 + cds.length + idxs.length + 1) :=
    (argsRelKA_lengthg h).symm.trans hlen
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
  obtain ⟨hP, h⟩ := argsRelKA_piTelA_append_invg _ _ _ _ _ hPh hqs hqs'
  have hpar : ∀ (B : ExprA) (v : Level), ArgsRelKAg E I n ρ₀ K Γ (piTelA params B v).1 qs qs' := by
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
  obtain ⟨hM, h₁⟩ := argsRelKA_piTelA_append_invg _ _ _ _ _ h₀ rfl rfl
  have hmot : LRRelAg E I n ρ₀ K Γ (substA τ (motTyA f ls params idxs wF wM).1) mot mot' := by
    have h := hM (.sort .zero) .zero
    simp only [piTelA, substA_pi] at h
    cases h with
    | cons _ _ _ _ _ _ _ _ hr _ => exact hr
  -- the minors
  obtain ⟨hMin, h₂⟩ := argsRelKA_piTelA_append_invg _ _ _ _ _ h₁ (hms.trans (minorDomsA_length _ _ _ _ _ _ _).symm)
    (hms'.trans (minorDomsA_length _ _ _ _ _ _ _).symm)
  have hmin := fun i hi hi' hc => argsRelKA_minorDomsAg (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := K) (Γ := Γ)
    f ls wF wM params.length (.sort .zero) .zero (consListA [mot] τ) cds 0 [] rfl (hMin (.sort .zero) .zero) i hi hi'
    hc
  -- the indices and the major
  obtain ⟨hIdx, h₃⟩ := argsRelKA_piTelA_append_invg _ _ _ _ _ h₂
    (his.trans (liftDomsA_length _ _ _).symm) (his'.trans (liftDomsA_length _ _ _).symm)
  have hidx : ∀ (B : ExprA) (v : Level), ArgsRelKAg E I n ρ₀ K Γ (substA τ (piTelA idxs B v).1) is is' := by
    intro B v
    have h := hIdx (.sort .zero) .zero
    rw [← consListA_append] at h
    have h' : ArgsRelKAg E I n ρ₀ K Γ (substA (consListA [] (consListA ([mot] ++ ms) τ))
        (piTelA (liftDomsA ([] : List ExprA).length ([mot] ++ ms).length idxs) (.sort .zero) .zero).1) is is' := by
      have e : ([mot] ++ ms).length = cds.length + 1 := by
        rw [List.length_append, hms, List.length_singleton]; omega
      rw [e]; exact h
    exact argsRelKA_liftDomsAg (.sort .zero) B .zero v ([mot] ++ ms) τ idxs [] h' his
  have hmaj : LRRelAg E I n ρ₀ K Γ (foldAppsA (.const f ls) (qs ++ is)) x x' := by
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

/-- THE RECURSOR'S ARGUMENTS SPLIT, no parameters: `recArgsSplitPAg` at the empty parameter list. -/
theorem recArgsSplitAg {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {as as' : List ExprA}
    (h : ArgsRelKAg E I n ρ₀ K Γ
      (piTelA (recDomsA f ls [] idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 as as')
    (hlen : as.length = 1 + cds.length + idxs.length + 1) :
    ∃ (mot mot' x x' : ExprA) (ms ms' is is' : List ExprA),
      as = [mot] ++ ms ++ is ++ [x] ∧ as' = [mot'] ++ ms' ++ is' ++ [x'] ∧
      ms.length = cds.length ∧ ms'.length = cds.length ∧ is.length = idxs.length ∧
      is'.length = idxs.length ∧
      LRRelAg E I n ρ₀ K Γ (motTyA f ls [] idxs wF wM).1 mot mot' ∧
      (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
        LRRelAg E I n ρ₀ K Γ (substA (SubstA.cons mot SubstA.id) (minorTyA f ls wF wM 0 cds[i]).1) ms[i] ms'[i]) ∧
      (∀ (B : ExprA) (v : Level), ArgsRelKAg E I n ρ₀ K Γ (piTelA idxs B v).1 is is') ∧
      LRRelAg E I n ρ₀ K Γ (foldAppsA (.const f ls) is) x x' ∧
      applyTelA as (piTelA (recDomsA f ls [] idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
        some (foldAppsA mot (is ++ [x])) := by
  obtain ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', e, e', hq, hq', hms, hms', his, his', -, hmot, hmin,
    hidx, hmaj, happ⟩ := recArgsSplitPAg f ls [] idxs wF wM w cds h (by rw [hlen, List.length_nil, Nat.zero_add])
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

end RecNeut

/-! ## (6) the converse walk, and iterated elimination -/

section RecJoin
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the minors' block, built from the minors each related at its type. -/
theorem argsRelKA_minorDomsA_joing {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (B : ExprA) (w : Level) (σ₀ : SubstA) :
    (cds : List MinorDataA) → (j0 : Nat) → (pre : List ExprA) → pre.length = j0 → (ms ms' : List ExprA) →
    ms.length = cds.length → ms'.length = cds.length →
    (∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelAg E I n ρ₀ k Γ (substA σ₀ (minorTyA f ls wF wM np cds[i]).1) ms[i] ms'[i]) →
    ArgsRelKAg E I n ρ₀ k Γ (substA (consListA pre σ₀) (piTelA (minorDomsA f ls wF wM np j0 cds) B w).1) ms ms'
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
        exact argsRelKA_minorDomsA_joing f ls wF wM np B w σ₀ cds (j0 + 1) (pre ++ [m])
          (by rw [List.length_append, hpre]; rfl) ms ms' (Nat.succ.inj hl) (Nat.succ.inj hl')
          (fun i hi hi' hc => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hc))

/-- the indices' block, built from the index telescope itself. -/
theorem argsRelKA_liftDomsA_joing {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level) (xs : List ExprA)
    (τ : SubstA) :
    (ds : List (ExprA × Level)) → (pre : List ExprA) → {as as' : List ExprA} →
    ArgsRelKAg E I n ρ₀ k Γ (substA (consListA pre τ) (piTelA ds B' w').1) as as' → as.length = ds.length →
    ArgsRelKAg E I n ρ₀ k Γ
      (substA (consListA pre (consListA xs τ)) (piTelA (liftDomsA pre.length xs.length ds) B w).1) as as'
  | [], _, [], as', h, _ => by
      have hl := argsRelKA_lengthg h
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
            have ih := argsRelKA_liftDomsA_joing B B' w w' xs τ ds (pre ++ [a]) hs (Nat.succ.inj hl)
            rw [List.length_append, List.length_singleton] at ih
            exact ih

/-- the converse of `argsRelKA_piTelA_append_invg`. -/
theorem argsRelKA_piTelA_appendg {k : Nat} {Γ : LCtxA} (B B' : ExprA) (w w' : Level)
    (xs ys : List (ExprA × Level)) (σ : SubstA) {as₁ as₁' as₂ as₂' : List ExprA}
    (h₁ : ArgsRelKAg E I n ρ₀ k Γ (substA σ (piTelA xs B' w').1) as₁ as₁') (hl : as₁.length = xs.length)
    (h₂ : ArgsRelKAg E I n ρ₀ k Γ (substA (consListA as₁ σ) (piTelA ys B w).1) as₂ as₂') :
    ArgsRelKAg E I n ρ₀ k Γ (substA σ (piTelA (xs ++ ys) B w).1) (as₁ ++ as₂) (as₁' ++ as₂') := by
  rw [piTelA_append]
  exact argsRelKA_appendg (argsRelKA_piTelA_bodyg B' _ w' _ xs σ h₁ hl) (applyTelA_piTelA _ _ xs as₁ hl σ) h₂

/-- THE RECURSOR'S ARGUMENTS JOIN (M2-f (6c)): the converse of `recArgsSplitPAg`. -/
theorem recArgsJoinPAg {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {qs qs' : List ExprA} {mot mot' x x' : ExprA}
    {ms ms' is is' : List ExprA} (hqs : qs.length = params.length)
    (hms : ms.length = cds.length) (hms' : ms'.length = cds.length) (his : is.length = idxs.length)
    (hpar : ArgsRelKAg E I n ρ₀ K Γ (piTelA params (.sort .zero) .zero).1 qs qs')
    (hmot : LRRelAg E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) mot mot')
    (hmin : ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelAg E I n ρ₀ K Γ (substA (SubstA.cons mot (consListA qs SubstA.id))
        (minorTyA f ls wF wM params.length cds[i]).1) ms[i] ms'[i])
    (hidx : ArgsRelKAg E I n ρ₀ K Γ (substA (consListA qs SubstA.id) (piTelA idxs (.sort .zero) .zero).1) is is')
    (hmaj : LRRelAg E I n ρ₀ K Γ (foldAppsA (.const f ls) (qs ++ is)) x x') :
    ArgsRelKAg E I n ρ₀ K Γ (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1
      (qs ++ ([mot] ++ ms ++ is ++ [x])) (qs' ++ ([mot'] ++ ms' ++ is' ++ [x'])) := by
  have hT : (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      substA SubstA.id (piTelA (params ++ ([motTyA f ls params idxs wF wM] ++ (minorDomsA f ls wF wM
        params.length 0 cds ++ (liftDomsA 0 (cds.length + 1) idxs ++
          [(liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length), wF)]))))
        (recBodyA idxs.length cds.length) w).1 := by
    rw [substA_id, recDomsA]
    simp only [List.append_assoc]
  rw [hT]
  refine argsRelKA_piTelA_appendg _ (.sort .zero) _ .zero _ _ _ (by rw [substA_id]; exact hpar) hqs ?_
  generalize hτ : consListA qs SubstA.id = τ at hmot hmin hidx ⊢
  rw [show [mot] ++ ms ++ is ++ [x] = [mot] ++ (ms ++ (is ++ [x])) by simp,
    show [mot'] ++ ms' ++ is' ++ [x'] = [mot'] ++ (ms' ++ (is' ++ [x'])) by simp]
  refine argsRelKA_piTelA_appendg _ (.sort .zero) _ .zero _ _ _ ?_ rfl ?_
  · simp only [piTelA, substA_pi]
    exact .cons _ _ _ _ mot mot' [] [] hmot (.nil _)
  refine argsRelKA_piTelA_appendg _ (.sort .zero) _ .zero _ _ _ ?_
    (hms.trans (minorDomsA_length _ _ _ _ _ _ _).symm) ?_
  · exact argsRelKA_minorDomsA_joing f ls wF wM params.length (.sort .zero) .zero (SubstA.cons mot τ) cds 0 [] rfl
      ms ms' hms hms' hmin
  have e2 : ([mot] ++ ms).length = cds.length + 1 := by
    rw [List.length_append, hms, List.length_singleton]; omega
  have ec : consListA ms (consListA [mot] τ) = consListA ([mot] ++ ms) τ := by
    rw [consListA_append]
  refine argsRelKA_piTelA_appendg _ (.sort .zero) _ .zero _ _ _ ?_
    (his.trans (liftDomsA_length _ _ _).symm) ?_
  · have hIdx := argsRelKA_liftDomsA_joing (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := K) (Γ := Γ)
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

/-- THE RECURSOR'S ARGUMENTS JOIN, no parameters: `recArgsJoinPAg` at the empty parameter list. -/
theorem recArgsJoinAg {K : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) {mot mot' x x' : ExprA} {ms ms' is is' : List ExprA}
    (hms : ms.length = cds.length) (hms' : ms'.length = cds.length) (his : is.length = idxs.length)
    (hmot : LRRelAg E I n ρ₀ K Γ (motTyA f ls [] idxs wF wM).1 mot mot')
    (hmin : ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length) (hc : i < cds.length),
      LRRelAg E I n ρ₀ K Γ (substA (SubstA.cons mot SubstA.id) (minorTyA f ls wF wM 0 cds[i]).1) ms[i] ms'[i])
    (hidx : ArgsRelKAg E I n ρ₀ K Γ (piTelA idxs (.sort .zero) .zero).1 is is')
    (hmaj : LRRelAg E I n ρ₀ K Γ (foldAppsA (.const f ls) is) x x') :
    ArgsRelKAg E I n ρ₀ K Γ (piTelA (recDomsA f ls [] idxs wF wM cds) (recBodyA idxs.length cds.length) w).1
      ([mot] ++ ms ++ is ++ [x]) ([mot'] ++ ms' ++ is' ++ [x']) := by
  have h := recArgsJoinPAg (qs := []) (qs' := []) f ls [] idxs wF wM w cds rfl hms hms' his (.nil _)
    (by rw [show consListA ([] : List ExprA) SubstA.id = SubstA.id from rfl, substA_id]; exact hmot) hmin
    (by rw [show consListA ([] : List ExprA) SubstA.id = SubstA.id from rfl, substA_id]; exact hidx)
    (by rw [List.nil_append]; exact hmaj)
  rwa [List.nil_append, List.nil_append] at h

end RecJoin

/-! ## (7) the major's chain, expanded -/

section MajorChain
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE MAJOR'S CHAIN, EXPANDED: an application of a recursor spine at its major (`h`, of type
    `Π (x : Dm), B`) to a major that reduces along a chain at `D` (convertible to `Dm`) is related at `A`
    wherever its application to the chain's end is, provided each instance `B[w]` along the chain is a
    type convertible to `A`. Each step is a typed major step (`TyHRedA.major`, ι refusing at a stepping
    major) at the step's own instance, moved to `A`. -/
theorem LRRelA_expand_majorChaing (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA}
    {h Dm B D A : ExprA} {u v : Level} (hrec : recAtMajorA E h = true) (hu : unitMinorA E h = none)
    (hst : structHeadA E h = false) (hhs : hStepFnA E I.fn Γ h = none)
    (hhT : HasTyA E I n Γ h (.pi Dm u B v)) (hBty : HasTyA E I n (.assumption Dm :: Γ) B (.sort v))
    (hDc : TyConvA E I n Γ D Dm)
    (hiota : ∀ z z', TyHRedA E I n Γ z z' D → I.fn (.app h z) = none) :
    {z N : ExprA} → TmChainA E I n Γ D z N →
    (∀ w, TyHRedStarA E I n Γ z w D → (∃ s, Nonempty (HasTyA E I n Γ (instantiate0A w B) (.sort s))) ∧
      Nonempty (TyConvA E I n Γ (instantiate0A w B) A)) →
    ∀ {b : ExprA}, LRRelAg E I n ρ₀ k Γ A (.app h N) b → LRRelAg E I n ρ₀ k Γ A (.app h z) b
  | _, _, .refl _ _, _, _, hb => hb
  | z, _, .cons _ z' _ hzD hs t, hw, _, hb => by
      have hzz' := tyHRedStarA_step hzD hs
      have ih := LRRelA_expand_majorChaing hE hI hrec hu hst hhs hhT hBty hDc hiota t
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
      exact LRRelA_expand_leftg hE hI ⟨⟨hasTyA_of_tyConvA happ hc₁⟩, ⟨.conv _ _ _ _ _ hstep hc₁⟩⟩ ih

/-- the right-hand form. -/
theorem LRRelA_expand_majorChain_rightg (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA}
    {h Dm B D A : ExprA} {u v : Level} (hrec : recAtMajorA E h = true) (hu : unitMinorA E h = none)
    (hst : structHeadA E h = false) (hhs : hStepFnA E I.fn Γ h = none)
    (hhT : HasTyA E I n Γ h (.pi Dm u B v)) (hBty : HasTyA E I n (.assumption Dm :: Γ) B (.sort v))
    (hDc : TyConvA E I n Γ D Dm)
    (hiota : ∀ z z', TyHRedA E I n Γ z z' D → I.fn (.app h z) = none) :
    {z N : ExprA} → TmChainA E I n Γ D z N →
    (∀ w, TyHRedStarA E I n Γ z w D → (∃ s, Nonempty (HasTyA E I n Γ (instantiate0A w B) (.sort s))) ∧
      Nonempty (TyConvA E I n Γ (instantiate0A w B) A)) →
    ∀ {a : ExprA}, LRRelAg E I n ρ₀ k Γ A a (.app h N) → LRRelAg E I n ρ₀ k Γ A a (.app h z)
  | _, _, .refl _ _, _, _, hb => hb
  | z, _, .cons _ z' _ hzD hs t, hw, _, hb => by
      have hzz' := tyHRedStarA_step hzD hs
      have ih := LRRelA_expand_majorChain_rightg hE hI hrec hu hst hhs hhT hBty hDc hiota t
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
      exact LRRelA_expand_rightg hE hI ⟨⟨hasTyA_of_tyConvA happ hc₁⟩, ⟨.conv _ _ _ _ _ hstep hc₁⟩⟩ ih

end MajorChain

/-! ## (8) bounded views read only the family's levels -/

/-! ## (9) walks along a telescope, pointwise: split and join (moved from `RcicAnnIotaSR` for W-1 (c)) -/

section Walk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

end Walk

#print axioms argsRelKA_piTelA_bodyg
#print axioms argsRelKA_piTelA_append_invg
#print axioms recArgsSplitPAg
#print axioms recArgsSplitAg
#print axioms argsRelKA_piTelA_appendg
#print axioms recArgsJoinPAg
#print axioms recArgsJoinAg
#print axioms LRRelA_expand_majorChaing
#print axioms LRRelA_expand_majorChain_rightg

end Rcic.Declarative.Ann
