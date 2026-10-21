import rcic.RcicSynLetTrace

/-!
# Wall 2 (changed-declaration letRight), step 2b — the trace under a binder

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Strengthened trace":
"Under binders: `shiftAll`, `runL_shift`, `steps_shiftAll`."

`tyAtLet` passes a binder with `packLUnder`: the stack becomes `shiftAll dL dF ss`, the
slot moves to `k + 1`, every stored payload is weakened at cutoff `0`. The trace follows:

* `sitesShift` mirrors `shiftAll` on the site data; `walkSite` of the shifted stack is
  `none` at `0` and the original `walkSite` at `i + 1`.
* `bwalkAtL_shift_zero`: the binder's own variable survives every shifted step as `keep 0`.
* `bwalkAtL_shift_succ`: the walk of `i + 1` through the shifted stack is the walk of `i`
  through the original stack, with every survivor index shifted by one, every replacement
  erasure lifted when the binder is kept (`eps_wk_zero_liftIfKeep`), and every bridge
  chain's levels unchanged (`BHitShift`).
* `traceInv_under`: the invariant is pushed under a binder whose two display entries are
  `BinderRel`-related (`keep`/`keep`, `drop`/`drop`, or two inlined values related by `Rel`
  through the pending actions — the introduced-let pre-action head of Part III).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 sites under a binder -/

/-- `Sites` of the shifted stack: every site's gate is unchanged. -/
def sitesShift {E : ResolvedEnv} {n : Nat} (dF : LocalDecl) :
    (dL : LocalDecl) → {ss : List (PStep E n)} → Sites ss → Sites (shiftAll dL dF ss)
  | _, _, .nil => .nil
  | dL, _, .wk c d s => .wk (c + 1) d (sitesShift dF (liftDecl c dL) s)
  | dL, _, .esub j v t Γe Γr hget repl replT hv σ u s =>
      .esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_assumption (d := dL) hget)
        (lift 0 1 repl) (lift 0 1 replT) (TyP.wk E n Γr repl replT dF 0 hv) σ u
        (sitesShift dF (instDecl j v dL) s)
  | dL, _, .lsub j v t Γe Γr hget repl replT hv σ u s =>
      .lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_let (d := dL) hget)
        (lift 0 1 repl) (lift 0 1 replT) (TyP.wk E n Γr repl replT dF 0 hv) σ u
        (sitesShift dF (instDecl j v dL) s)
  | dL, _, .linst ls a nStep hls hlen s =>
      .linst ls a nStep hls hlen (sitesShift dF (instLvlsDecl ls dL) s)
  | dL, _, .cctx p Askel newTy oldTy u Γr hc s =>
      .cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dF 0 Γr)
        (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
          (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc))
        (sitesShift dF dL s)

theorem walkSite_shift_zero {E : ResolvedEnv} {n : Nat} (dF : LocalDecl) :
    (dL : LocalDecl) → {ss : List (PStep E n)} → (s : Sites ss) →
      walkSite (sitesShift dF dL s) 0 = none
  | _, _, .nil => rfl
  | dL, _, .wk c d s => by
      simp only [sitesShift, walkSite]
      rw [if_pos (Nat.zero_lt_succ c)]
      exact walkSite_shift_zero dF _ s
  | dL, _, .esub j v t Γe Γr hget repl replT hv σ u s => by
      simp only [sitesShift, walkSite]
      rw [if_pos (Nat.zero_lt_succ j)]
      exact walkSite_shift_zero dF _ s
  | dL, _, .lsub j v t Γe Γr hget repl replT hv σ u s => by
      simp only [sitesShift, walkSite]
      rw [if_pos (Nat.zero_lt_succ j)]
      exact walkSite_shift_zero dF _ s
  | dL, _, .linst ls a nStep hls hlen s => by
      simp only [sitesShift, walkSite]
      exact walkSite_shift_zero dF _ s
  | dL, _, .cctx p Askel newTy oldTy u Γr hc s => by
      simp only [sitesShift, walkSite]
      rw [if_neg (Nat.succ_ne_zero p).symm]
      exact walkSite_shift_zero dF _ s

theorem walkSite_shift_succ {E : ResolvedEnv} {n : Nat} (dF : LocalDecl) :
    (dL : LocalDecl) → {ss : List (PStep E n)} → (s : Sites ss) → (i : Nat) →
      walkSite (sitesShift dF dL s) (i + 1) = walkSite s i
  | _, _, .nil, _ => rfl
  | dL, _, .wk c d s, i => by
      simp only [sitesShift, walkSite]
      by_cases h : i < c
      · rw [if_pos (Nat.succ_lt_succ h), if_pos h]
        exact walkSite_shift_succ dF _ s i
      · rw [if_neg (fun h' => h (Nat.lt_of_succ_lt_succ h')), if_neg h]
        exact walkSite_shift_succ dF _ s (i + 1)
  | dL, _, .esub j v t Γe Γr hget repl replT hv σ u s, i => by
      simp only [sitesShift, walkSite]
      by_cases h1 : i < j
      · rw [if_pos (Nat.succ_lt_succ h1), if_pos h1]
        exact walkSite_shift_succ dF _ s i
      · rw [if_neg (fun h' => h1 (Nat.lt_of_succ_lt_succ h')), if_neg h1]
        by_cases h2 : j < i
        · rw [if_pos (Nat.succ_lt_succ h2), if_pos h2]
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          exact walkSite_shift_succ dF _ s i'
        · rw [if_neg (fun h' => h2 (Nat.lt_of_succ_lt_succ h')), if_neg h2]
  | dL, _, .lsub j v t Γe Γr hget repl replT hv σ u s, i => by
      simp only [sitesShift, walkSite]
      by_cases h1 : i < j
      · rw [if_pos (Nat.succ_lt_succ h1), if_pos h1]
        exact walkSite_shift_succ dF _ s i
      · rw [if_neg (fun h' => h1 (Nat.lt_of_succ_lt_succ h')), if_neg h1]
        by_cases h2 : j < i
        · rw [if_pos (Nat.succ_lt_succ h2), if_pos h2]
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          exact walkSite_shift_succ dF _ s i'
        · rw [if_neg (fun h' => h2 (Nat.lt_of_succ_lt_succ h')), if_neg h2]
  | dL, _, .linst ls a nStep hls hlen s, i => by
      simp only [sitesShift, walkSite]
      exact walkSite_shift_succ dF _ s i
  | dL, _, .cctx p Askel newTy oldTy u Γr hc s, i => by
      simp only [sitesShift, walkSite]
      by_cases h : i = p
      · subst h
        rw [if_pos rfl, if_pos rfl]
        exact walkSite_shift_succ dF _ s i
      · rw [if_neg (fun h' => h (Nat.add_right_cancel h')), if_neg h]
        exact walkSite_shift_succ dF _ s i

/-! ## §2 the binder's own variable -/

def IsKeepZero {E : ResolvedEnv} {n : Nat} {pre fin : LCtx} {term ty : Expr Nat} :
    BHit E n pre fin term ty → Prop
  | .keep j _ _ => j = 0
  | .repl _ => False
  | .retype _ _ _ _ _ => False

theorem isKeepZero_castTerm {E : ResolvedEnv} {n : Nat} {pre fin : LCtx} {term ty term' : Expr Nat}
    (h : term' = term) (w : BHit E n pre fin term ty) (hw : IsKeepZero w) :
    IsKeepZero (BHit.castTerm h w) := by
  cases w with
  | keep j ht hl => exact hw
  | repl hv => exact hw
  | retype j B ht hl hc => exact hw

/-- The walk of index `0` through a shifted stack is `keep 0`. -/
theorem bwalkAtL_shift_zero {E : ResolvedEnv} {n : Nat} (k : Nat) (Dom' Val' : Expr Nat)
    (dF : LocalDecl) :
    ∀ (ss : List (PStep E n)) (dL : LocalDecl) (A : Expr Nat) (Γ : LCtx)
      (hlu : lookupType (dL :: Γ) 0 = some A)
      (hinv : EsInv (shiftAll dL dF ss)) (hrun : RunL k Dom' Val' (shiftAll dL dF ss) (dL :: Γ)),
      IsKeepZero (bwalkAtL k Dom' Val' (shiftAll dL dF ss) 0 A (dL :: Γ) hlu hinv hrun)
  | [], dL, A, Γ, hlu, hinv, hrun => by
      show IsKeepZero (bwalkAtL k Dom' Val' [] 0 A (dL :: Γ) hlu hinv hrun)
      unfold bwalkAtL
      exact rfl
  | .wk c d :: ss, dL, A, Γ, hlu, hinv, hrun => by
      change EsInv (.wk (c + 1) d :: shiftAll (liftDecl c dL) dF ss) at hinv
      change RunL k Dom' Val' (.wk (c + 1) d :: shiftAll (liftDecl c dL) dF ss) (dL :: Γ) at hrun
      cases hinv with
      | wk _ _ hinv' =>
      cases hrun with
      | wk _ _ hrun' =>
        show IsKeepZero (bwalkAtL k Dom' Val' (.wk (c + 1) d :: shiftAll (liftDecl c dL) dF ss) 0 A
          (dL :: Γ) hlu (.wk _ _ hinv') (.wk _ _ hrun'))
        unfold bwalkAtL
        rw [dif_pos (Nat.zero_lt_succ c)]
        exact isKeepZero_castTerm _ _
          (bwalkAtL_shift_zero k Dom' Val' dF ss (liftDecl c dL) _ (insertAt d c Γ) _ hinv' hrun')
  | .esub j v t Γe Γr hget repl replT hv :: ss, dL, A, Γ, hlu, hinv, hrun => by
      change EsInv (.esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_assumption (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) at hinv
      change RunL k Dom' Val' (.esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_assumption (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) (dL :: Γ) at hrun
      cases hinv with
      | esub _ _ _ _ _ hget' _ _ _ hinv' hr hT =>
      cases hrun with
      | esub hΓ hctx hrun' =>
        show IsKeepZero (bwalkAtL k Dom' Val' (.esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
          hget' (lift 0 1 repl) (lift 0 1 replT) (TyP.wk E n Γr repl replT dF 0 hv) ::
            shiftAll (instDecl j v dL) dF ss) 0 A (dL :: Γ) hlu
          (.esub _ _ _ _ _ _ _ _ _ hinv' hr hT) (.esub hΓ hctx hrun'))
        unfold bwalkAtL
        rw [dif_pos (Nat.zero_lt_succ j)]
        exact isKeepZero_castTerm _ _
          (bwalkAtL_shift_zero k Dom' Val' dF ss (instDecl j v dL) _ (substRemove v j Γ) _ hinv' hrun')
  | .lsub j v t Γe Γr hget repl replT hv :: ss, dL, A, Γ, hlu, hinv, hrun => by
      change EsInv (.lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_let (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) at hinv
      change RunL k Dom' Val' (.lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_let (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) (dL :: Γ) at hrun
      cases hinv with
      | lsub _ _ _ _ _ hget' _ _ _ hinv' hr hT =>
      cases hrun with
      | lsub hΓ hctx hrun' =>
        show IsKeepZero (bwalkAtL k Dom' Val' (.lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
          hget' (lift 0 1 repl) (lift 0 1 replT) (TyP.wk E n Γr repl replT dF 0 hv) ::
            shiftAll (instDecl j v dL) dF ss) 0 A (dL :: Γ) hlu
          (.lsub _ _ _ _ _ _ _ _ _ hinv' hr hT) (.lsub hΓ hctx hrun'))
        unfold bwalkAtL
        rw [dif_pos (Nat.zero_lt_succ j)]
        exact isKeepZero_castTerm _ _
          (bwalkAtL_shift_zero k Dom' Val' dF ss (instDecl j v dL) _ (substRemove v j Γ) _ hinv' hrun')
  | .linst ls a nStep hls hlen :: ss, dL, A, Γ, hlu, hinv, hrun => by
      change EsInv (.linst ls a nStep hls hlen :: shiftAll (instLvlsDecl ls dL) dF ss) at hinv
      change RunL k Dom' Val' (.linst ls a nStep hls hlen :: shiftAll (instLvlsDecl ls dL) dF ss)
        (dL :: Γ) at hrun
      cases hinv with
      | linst _ _ _ _ _ hinv' =>
      cases hrun with
      | linst _ _ _ _ _ hrun' =>
        show IsKeepZero (bwalkAtL k Dom' Val' (.linst ls a nStep hls hlen ::
          shiftAll (instLvlsDecl ls dL) dF ss) 0 A (dL :: Γ) hlu
          (.linst _ _ _ _ _ hinv') (.linst _ _ _ _ _ hrun'))
        unfold bwalkAtL
        exact bwalkAtL_shift_zero k Dom' Val' dF ss (instLvlsDecl ls dL) _ (instLvlsCtx ls Γ) _ hinv' hrun'
  | .cctx p Askel newTy oldTy u Γr hc :: ss, dL, A, Γ, hlu, hinv, hrun => by
      change EsInv (.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dF 0 Γr)
        (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
          (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc)) :: shiftAll dL dF ss) at hinv
      change RunL k Dom' Val' (.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u
        (insertAt dF 0 Γr)
        (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
          (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc)) :: shiftAll dL dF ss) (dL :: Γ) at hrun
      cases hinv with
      | cctx _ _ _ _ _ _ _ hinv' =>
      cases hrun with
      | cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun' =>
        show IsKeepZero (bwalkAtL k Dom' Val' (.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u
          (insertAt dF 0 Γr) (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
            (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc)) :: shiftAll dL dF ss) 0 A (dL :: Γ) hlu
          (.cctx _ _ _ _ _ _ _ hinv') (.cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun'))
        unfold bwalkAtL
        rw [dif_neg (Nat.succ_ne_zero p).symm]
        exact bwalkAtL_shift_zero k Dom' Val' dF ss dL _ (setAssump p Askel Γ) _ hinv' hrun'

/-! ## §3 the walk of a shifted index -/

/-- The binder's lift of a right-side erasure: kept binders occupy an erased slot. -/
def liftIfKeep : Disp → ETm → ETm
  | .keep, t => t.lift 0 1
  | _, t => t

/-- Shifted walk result against the original: survivor indices shift by one, replacement
    erasures are lifted at a kept binder, bridge levels are unchanged. -/
def BHitShift (μ' : Level → Level) (ρ' : List Disp) (d' : Disp) {E : ResolvedEnv} {n : Nat}
    {pre fin pre' fin' : LCtx} {term ty term' ty' : Expr Nat} :
    BHit E n pre fin term ty → BHit E n pre' fin' term' ty' → Prop
  | .keep j _ _, .keep j' _ _ => j' = j + 1
  | .repl hv, .repl hv' => hv'.eps μ' (d' :: ρ') = liftIfKeep d' (hv.eps μ' ρ')
  | .retype j _ _ _ hc, .retype j' _ _ _ hc' =>
      j' = j + 1 ∧ convChainLevels hc' = convChainLevels hc
  | .keep _ _ _, .repl _ => False
  | .keep _ _ _, .retype _ _ _ _ _ => False
  | .repl _, .keep _ _ _ => False
  | .repl _, .retype _ _ _ _ _ => False
  | .retype _ _ _ _ _, .keep _ _ _ => False
  | .retype _ _ _ _ _, .repl _ => False

theorem bHitShift_castTerm {μ' : Level → Level} {ρ' : List Disp} {d' : Disp}
    {E : ResolvedEnv} {n : Nat} {pre fin pre' fin' : LCtx} {term ty term' ty' t1 t2 : Expr Nat}
    (h1 : t1 = term) (h2 : t2 = term')
    (w : BHit E n pre fin term ty) (w' : BHit E n pre' fin' term' ty')
    (hw : BHitShift μ' ρ' d' w w') :
    BHitShift μ' ρ' d' (BHit.castTerm h1 w) (BHit.castTerm h2 w') := by
  cases w with
  | keep j ht hl =>
      cases w' with
      | keep j' ht' hl' => exact hw
      | repl hv' => exact hw.elim
      | retype j' B' ht' hl' hc' => exact hw.elim
  | repl hv =>
      cases w' with
      | keep j' ht' hl' => exact hw.elim
      | repl hv' =>
          simp only [BHit.castTerm, BHitShift] at hw ⊢
          rw [eps_tyCast, eps_tyCast]
          exact hw
      | retype j' B' ht' hl' hc' => exact hw.elim
  | retype j B ht hl hc =>
      cases w' with
      | keep j' ht' hl' => exact hw.elim
      | repl hv' => exact hw.elim
      | retype j' B' ht' hl' hc' => exact hw

/-- A cutoff-`0` weakening of a stored replacement erases to the lifted erasure at a kept
    binder, and to the same erasure otherwise. -/
theorem eps_wk_zero_liftIfKeep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (dF : LocalDecl) (hv : TyP E n Γ e A) (μ' : Level → Level) (d' : Disp) (ρ' : List Disp) :
    (TyP.wk E n Γ e A dF 0 hv).eps μ' (d' :: ρ') = liftIfKeep d' (hv.eps μ' ρ') := by
  cases d' with
  | keep =>
      rw [eps_wk_keep (hk := (by simp : ((.keep : Disp) :: ρ')[0]? = some .keep))]
      rfl
  | drop =>
      rw [eps_wk_not_keep (hk := Or.inr (Or.inl (by simp)))]
      rfl
  | inline v =>
      rw [eps_wk_not_keep (hk := Or.inr (Or.inr ⟨v, by simp⟩))]
      rfl

theorem lift_instantiate_succ (j : Nat) (v A : Expr Nat) :
    instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 A) = lift 0 1 (instantiate j (lift 0 j v) A) := by
  rw [lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) A, Nat.add_comm 1 j,
    lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v]

theorem lift_lift_succ_comm (c : Nat) (A : Expr Nat) :
    lift (c + 1) 1 (lift 0 1 A) = lift 0 1 (lift c 1 A) := by
  rw [lift_lift_permute 1 1 c 0 (Nat.zero_le c) A, Nat.add_comm 1 c]

/-- The walk of `i + 1` through the shifted stack against the walk of `i` through the
    original stack. -/
theorem bwalkAtL_shift_succ {E : ResolvedEnv} {n : Nat} (μ' : Level → Level) (ρ' : List Disp)
    (d' : Disp) (k : Nat) (Dom' Val' : Expr Nat) (dF : LocalDecl) :
    ∀ (ss : List (PStep E n)) (dL : LocalDecl) (i : Nat) (A : Expr Nat) (Γ : LCtx)
      (hlu : lookupType Γ i = some A) (hinv : EsInv ss) (hrun : RunL k Dom' Val' ss Γ)
      (A' : Expr Nat) (hA' : A' = lift 0 1 A)
      (hlu' : lookupType (dL :: Γ) (i + 1) = some A')
      (hinv' : EsInv (shiftAll dL dF ss))
      (hrun' : RunL (k + 1) Dom' Val' (shiftAll dL dF ss) (dL :: Γ)),
      BHitShift μ' ρ' d' (bwalkAtL k Dom' Val' ss i A Γ hlu hinv hrun)
        (bwalkAtL (k + 1) Dom' Val' (shiftAll dL dF ss) (i + 1) A' (dL :: Γ) hlu' hinv' hrun')
  | [], dL, i, A, Γ, hlu, hinv, hrun, A', hA', hlu', hinv', hrun' => by
      subst hA'
      show BHitShift μ' ρ' d' (bwalkAtL k Dom' Val' [] i A Γ hlu hinv hrun)
        (bwalkAtL (k + 1) Dom' Val' [] (i + 1) (lift 0 1 A) (dL :: Γ) hlu' hinv' hrun')
      unfold bwalkAtL
      exact rfl
  | .wk c d :: ss, dL, i, A, Γ, hlu, hinv, hrun, A', hA', hlu', hinv', hrun' => by
      subst hA'
      change EsInv (.wk (c + 1) d :: shiftAll (liftDecl c dL) dF ss) at hinv'
      change RunL (k + 1) Dom' Val' (.wk (c + 1) d :: shiftAll (liftDecl c dL) dF ss) (dL :: Γ)
        at hrun'
      cases hinv with
      | wk _ _ hinv₀ =>
      cases hrun with
      | wk _ _ hrun₀ =>
      cases hinv' with
      | wk _ _ hinv₁ =>
      cases hrun' with
      | wk _ _ hrun₁ =>
        show BHitShift μ' ρ' d' _ (bwalkAtL (k + 1) Dom' Val'
          (.wk (c + 1) d :: shiftAll (liftDecl c dL) dF ss) (i + 1) (lift 0 1 A) (dL :: Γ) hlu'
          (.wk _ _ hinv₁) (.wk _ _ hrun₁))
        unfold bwalkAtL
        by_cases hi : i < c
        · have hi' : i + 1 < c + 1 := Nat.succ_lt_succ hi
          rw [dif_pos hi, dif_pos hi']
          exact bHitShift_castTerm _ _ _ _
            (bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (liftDecl c dL) i (lift c 1 A)
              (insertAt d c Γ) _ hinv₀ hrun₀ _ (lift_lift_succ_comm c A) _ hinv₁ hrun₁)
        · have hi' : ¬ i + 1 < c + 1 := fun h => hi (Nat.lt_of_succ_lt_succ h)
          rw [dif_neg hi, dif_neg hi']
          exact bHitShift_castTerm _ _ _ _
            (bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (liftDecl c dL) (i + 1) (lift c 1 A)
              (insertAt d c Γ) _ hinv₀ hrun₀ _ (lift_lift_succ_comm c A) _ hinv₁ hrun₁)
  | .esub j v t Γe Γr hget repl replT hv :: ss, dL, i, A, Γ, hlu, hinv, hrun, A', hA', hlu',
      hinv', hrun' => by
      subst hA'
      change EsInv (.esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_assumption (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) at hinv'
      change RunL (k + 1) Dom' Val' (.esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_assumption (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) (dL :: Γ) at hrun'
      cases hinv with
      | esub _ _ _ _ _ _ _ _ _ hinv₀ hr hT =>
      cases hrun with
      | esub hΓ hctx hrun₀ =>
      cases hinv' with
      | esub _ _ _ _ _ hget' _ _ _ hinv₁ hr' hT' =>
      cases hrun' with
      | esub hΓ' hctx' hrun₁ =>
        show BHitShift μ' ρ' d' _ (bwalkAtL (k + 1) Dom' Val'
          (.esub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr) hget' (lift 0 1 repl) (lift 0 1 replT)
            (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) (i + 1)
          (lift 0 1 A) (dL :: Γ) hlu' (.esub _ _ _ _ _ _ _ _ _ hinv₁ hr' hT') (.esub hΓ' hctx' hrun₁))
        unfold bwalkAtL
        by_cases hi : i < j
        · have hi' : i + 1 < j + 1 := Nat.succ_lt_succ hi
          rw [dif_pos hi, dif_pos hi']
          exact bHitShift_castTerm _ _ _ _
            (bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (instDecl j v dL) i _
              (substRemove v j Γ) _ hinv₀ hrun₀ _ (lift_instantiate_succ j v A) _ hinv₁ hrun₁)
        · have hi' : ¬ i + 1 < j + 1 := fun h => hi (Nat.lt_of_succ_lt_succ h)
          rw [dif_neg hi, dif_neg hi']
          by_cases hj : j < i
          · have hj' : j + 1 < i + 1 := Nat.succ_lt_succ hj
            rw [dif_pos hj, dif_pos hj']
            obtain ⟨i₀, rfl⟩ : ∃ i₀, i = i₀ + 1 := ⟨i - 1, by omega⟩
            exact bHitShift_castTerm _ _ _ _
              (bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (instDecl j v dL) i₀ _
                (substRemove v j Γ) _ hinv₀ hrun₀ _ (lift_instantiate_succ j v A) _ hinv₁ hrun₁)
          · have hj' : ¬ j + 1 < i + 1 := fun h => hj (Nat.lt_of_succ_lt_succ h)
            rw [dif_neg hj, dif_neg hj']
            generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
            cases e
            generalize hg' : Nat.le_antisymm (Nat.le_of_not_lt hj') (Nat.le_of_not_lt hi') = e'
            cases e'
            simp only [BHitShift, eps_tyCastCtx, eps_tyCast]
            exact eps_wk_zero_liftIfKeep dF hv μ' d' ρ'
  | .lsub j v t Γe Γr hget repl replT hv :: ss, dL, i, A, Γ, hlu, hinv, hrun, A', hA', hlu',
      hinv', hrun' => by
      subst hA'
      change EsInv (.lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_let (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) at hinv'
      change RunL (k + 1) Dom' Val' (.lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr)
        (get?_cons_succ_let (d := dL) hget) (lift 0 1 repl) (lift 0 1 replT)
        (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) (dL :: Γ) at hrun'
      cases hinv with
      | lsub _ _ _ _ _ _ _ _ _ hinv₀ hr hT =>
      cases hrun with
      | lsub hΓ hctx hrun₀ =>
      cases hinv' with
      | lsub _ _ _ _ _ hget' _ _ _ hinv₁ hr' hT' =>
      cases hrun' with
      | lsub hΓ' hctx' hrun₁ =>
        show BHitShift μ' ρ' d' _ (bwalkAtL (k + 1) Dom' Val'
          (.lsub (j + 1) v t (dL :: Γe) (insertAt dF 0 Γr) hget' (lift 0 1 repl) (lift 0 1 replT)
            (TyP.wk E n Γr repl replT dF 0 hv) :: shiftAll (instDecl j v dL) dF ss) (i + 1)
          (lift 0 1 A) (dL :: Γ) hlu' (.lsub _ _ _ _ _ _ _ _ _ hinv₁ hr' hT') (.lsub hΓ' hctx' hrun₁))
        unfold bwalkAtL
        by_cases hi : i < j
        · have hi' : i + 1 < j + 1 := Nat.succ_lt_succ hi
          rw [dif_pos hi, dif_pos hi']
          exact bHitShift_castTerm _ _ _ _
            (bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (instDecl j v dL) i _
              (substRemove v j Γ) _ hinv₀ hrun₀ _ (lift_instantiate_succ j v A) _ hinv₁ hrun₁)
        · have hi' : ¬ i + 1 < j + 1 := fun h => hi (Nat.lt_of_succ_lt_succ h)
          rw [dif_neg hi, dif_neg hi']
          by_cases hj : j < i
          · have hj' : j + 1 < i + 1 := Nat.succ_lt_succ hj
            rw [dif_pos hj, dif_pos hj']
            obtain ⟨i₀, rfl⟩ : ∃ i₀, i = i₀ + 1 := ⟨i - 1, by omega⟩
            exact bHitShift_castTerm _ _ _ _
              (bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (instDecl j v dL) i₀ _
                (substRemove v j Γ) _ hinv₀ hrun₀ _ (lift_instantiate_succ j v A) _ hinv₁ hrun₁)
          · have hj' : ¬ j + 1 < i + 1 := fun h => hj (Nat.lt_of_succ_lt_succ h)
            rw [dif_neg hj, dif_neg hj']
            generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
            cases e
            generalize hg' : Nat.le_antisymm (Nat.le_of_not_lt hj') (Nat.le_of_not_lt hi') = e'
            cases e'
            simp only [BHitShift, eps_tyCastCtx, eps_tyCast]
            exact eps_wk_zero_liftIfKeep dF hv μ' d' ρ'
  | .linst ls a nStep hls hlen :: ss, dL, i, A, Γ, hlu, hinv, hrun, A', hA', hlu', hinv',
      hrun' => by
      subst hA'
      change EsInv (.linst ls a nStep hls hlen :: shiftAll (instLvlsDecl ls dL) dF ss) at hinv'
      change RunL (k + 1) Dom' Val' (.linst ls a nStep hls hlen ::
        shiftAll (instLvlsDecl ls dL) dF ss) (dL :: Γ) at hrun'
      cases hinv with
      | linst _ _ _ _ _ hinv₀ =>
      cases hrun with
      | linst _ _ _ _ _ hrun₀ =>
      cases hinv' with
      | linst _ _ _ _ _ hinv₁ =>
      cases hrun' with
      | linst _ _ _ _ _ hrun₁ =>
        show BHitShift μ' ρ' d' _ (bwalkAtL (k + 1) Dom' Val'
          (.linst ls a nStep hls hlen :: shiftAll (instLvlsDecl ls dL) dF ss) (i + 1)
          (lift 0 1 A) (dL :: Γ) hlu' (.linst _ _ _ _ _ hinv₁) (.linst _ _ _ _ _ hrun₁))
        unfold bwalkAtL
        exact bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss (instLvlsDecl ls dL) i _
          (instLvlsCtx ls Γ) _ hinv₀ hrun₀ _ (lift_instantiateLevels ls 1 A 0).symm _ hinv₁ hrun₁
  | .cctx p Askel newTy oldTy u Γr hc :: ss, dL, i, A, Γ, hlu, hinv, hrun, A', hA', hlu',
      hinv', hrun' => by
      subst hA'
      change EsInv (.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dF 0 Γr)
        (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
          (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc)) :: shiftAll dL dF ss) at hinv'
      change RunL (k + 1) Dom' Val' (.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u
        (insertAt dF 0 Γr)
        (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
          (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc)) :: shiftAll dL dF ss) (dL :: Γ) at hrun'
      cases hinv with
      | cctx _ _ _ _ _ _ _ hinv₀ =>
      cases hrun with
      | cctx _ _ _ _ _ Aold hdec hnew hold hctx hrun₀ =>
      cases hinv' with
      | cctx _ _ _ _ _ _ _ hinv₁ =>
      cases hrun' with
      | cctx _ _ _ _ _ Aold' hdec' hnew' hold' hctx' hrun₁ =>
        show BHitShift μ' ρ' d' _ (bwalkAtL (k + 1) Dom' Val'
          (.cctx (p + 1) Askel (lift 0 1 newTy) (lift 0 1 oldTy) u (insertAt dF 0 Γr)
            (cvCast rfl rfl (rfl : lift 0 1 (.sort u) = .sort u)
              (CvP.wk E n Γr newTy oldTy (.sort u) dF 0 hc)) :: shiftAll dL dF ss) (i + 1)
          (lift 0 1 A) (dL :: Γ) hlu' (.cctx _ _ _ _ _ _ _ hinv₁)
          (.cctx _ _ _ _ _ Aold' hdec' hnew' hold' hctx' hrun₁))
        unfold bwalkAtL
        by_cases hip : i = p
        · have hip' : i + 1 = p + 1 := congrArg Nat.succ hip
          rw [dif_pos hip, dif_pos hip']
          have hw := bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss dL p _ (setAssump p Askel Γ)
            (lookupType_setAssump_at Askel Γ p (hip ▸ hlu)) hinv₀ hrun₀ _
            (lift_lift_merge 1 (p + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) Askel).symm
            (lookupType_setAssump_at Askel (dL :: Γ) (p + 1) (hip' ▸ hlu')) hinv₁ hrun₁
          change BHitShift μ' ρ' d'
            (bwalkAtL k Dom' Val' ss p (lift 0 (p + 1) Askel) (setAssump p Askel Γ) _ hinv₀ hrun₀)
            (bwalkAtL (k + 1) Dom' Val' (shiftAll dL dF ss) (p + 1) (lift 0 (p + 1 + 1) Askel)
              (setAssump (p + 1) Askel (dL :: Γ)) _ hinv₁ hrun₁) at hw
          dsimp only
          split
          · rename_i j hterm hlook heq
            split
            · rename_i j' hterm' hlook' heq'
              rw [heq, heq'] at hw
              exact ⟨hw, rfl⟩
            · rename_i hv' heq'
              rw [heq, heq'] at hw
              exact hw.elim
            · rename_i j' B' hterm' hlook' hc' heq'
              rw [heq, heq'] at hw
              exact hw.elim
          · rename_i hv₀ heq
            split
            · rename_i j' hterm' hlook' heq'
              rw [heq, heq'] at hw
              exact hw.elim
            · rename_i hv' heq'
              rw [heq, heq'] at hw
              simp only [BHitShift, eps_tyCast, eps_conv] at hw ⊢
              exact hw
            · rename_i j' B' hterm' hlook' hc' heq'
              rw [heq, heq'] at hw
              exact hw.elim
          · rename_i j B hterm hlook hc₀ heq
            split
            · rename_i j' hterm' hlook' heq'
              rw [heq, heq'] at hw
              exact hw.elim
            · rename_i hv' heq'
              rw [heq, heq'] at hw
              exact hw.elim
            · rename_i j' B' hterm' hlook' hc' heq'
              rw [heq, heq'] at hw
              simp only [BHitShift] at hw ⊢
              rw [convChainLevels_snoc, convChainLevels_snoc, hw.2]
              exact ⟨hw.1, rfl⟩
        · have hip' : ¬ i + 1 = p + 1 := fun h => hip (Nat.add_right_cancel h)
          rw [dif_neg hip, dif_neg hip']
          exact bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss dL i A (setAssump p Askel Γ) _
            hinv₀ hrun₀ _ rfl _ hinv₁ hrun₁

/-! ## §4 the binder push -/

/-- The two display entries of one binder: keep to keep, drop to drop, or two inlined
    values related by `Rel` through the pending actions (the pre-action left head). -/
inductive BinderRel (tbl : List CRule) (acts : List EAct) : Disp → Disp → Prop where
  | keep : BinderRel tbl acts .keep .keep
  | drop : BinderRel tbl acts .drop .drop
  | inline {x x' : ETm} (h : Rel tbl (applyActs acts x) x') :
      BinderRel tbl acts (.inline x) (.inline x')

/-- The pending actions under a binder: shifted at a kept binder, unchanged otherwise. -/
def binderActs : Disp → List EAct → List EAct
  | .keep, acts => shiftActs acts
  | .drop, acts => acts
  | .inline _, acts => acts

theorem eActsNonStar_binderActs (dd : Disp) {acts : List EAct} (h : EActsNonStar acts) :
    EActsNonStar (binderActs dd acts) := by
  cases dd with
  | keep => exact eActsNonStar_shift acts h
  | drop => exact h
  | inline _ => exact h

/-- The introduced-let heads: the left head holds the pre-action value, the right head the
    transported value; their relation through the actions synchronizes the branch. -/
theorem binderRel_letDisp {tbl : List CRule} {acts : List EAct} (hns : EActsNonStar acts)
    {a a' : ETm} (h : Rel tbl (applyActs acts a) a') :
    BinderRel tbl acts (letDisp a) (letDisp a') := by
  by_cases hs : a = .star
  · subst hs
    have ha' : a' = .star := h.eq_star (applyActs_star acts)
    subst ha'
    exact .drop
  · have hs' : a' ≠ .star := h.ne_star (fun h' => hs ((applyActs_eq_star_iff acts hns a).mp h'))
    rw [letDisp_of_ne_star hs, letDisp_of_ne_star hs']
    exact .inline h

theorem bHitRel_shift {tbl : List CRule} (hcl : TableClosed tbl) {μ' : Level → Level}
    {ρ' : List Disp} {acts : List EAct} {dd d' : Disp} (hb : BinderRel tbl acts dd d')
    {L : ETm} {site : Option ((Level → Level) × Level)} {E : ResolvedEnv} {n : Nat}
    {pre fin pre' fin' : LCtx} {term ty term' ty' : Expr Nat}
    {w : BHit E n pre fin term ty} {w' : BHit E n pre' fin' term' ty'}
    (hw : BHitRel tbl μ' ρ' L site w) (hs : BHitShift μ' ρ' d' w w') :
    BHitRel tbl μ' (d' :: ρ') (liftIfKeep dd L) site w' := by
  cases w with
  | keep j ht hl =>
      cases w' with
      | keep j' ht' hl' =>
          obtain ⟨hsite, hr⟩ := hw
          simp only [BHitShift] at hs
          subst hs
          refine ⟨hsite, ?_⟩
          cases hb with
          | keep => rw [resolve_keep_succ]; exact rel_lift hcl hr 0 1
          | drop => rw [resolve_drop_succ]; exact hr
          | inline _ => rw [resolve_inline_succ]; exact hr
      | repl hv' => exact hs.elim
      | retype j' B' ht' hl' hc' => exact hs.elim
  | repl hv =>
      cases w' with
      | keep j' ht' hl' => exact hs.elim
      | repl hv' =>
          obtain ⟨σo, uo, hsite, hst, hr⟩ := hw
          simp only [BHitShift] at hs
          refine ⟨σo, uo, hsite, ?_, ?_⟩
          · rw [hs]
            cases hb with
            | keep => simp only [liftIfKeep]; rw [etm_lift_eq_star_iff]; exact hst
            | drop => exact hst
            | inline _ => exact hst
          · rw [hs]
            cases hb with
            | keep => simp only [liftIfKeep]; exact rel_lift hcl hr 0 1
            | drop => exact hr
            | inline _ => exact hr
      | retype j' B' ht' hl' hc' => exact hs.elim
  | retype j B ht hl hc =>
      cases w' with
      | keep j' ht' hl' => exact hs.elim
      | repl hv' => exact hs.elim
      | retype j' B' ht' hl' hc' =>
          obtain ⟨hsite, hr⟩ := hw
          simp only [BHitShift] at hs
          obtain ⟨hj, -⟩ := hs
          subst hj
          refine ⟨hsite, ?_⟩
          cases hb with
          | keep => rw [resolve_keep_succ]; exact rel_lift hcl hr 0 1
          | drop => rw [resolve_drop_succ]; exact hr
          | inline _ => rw [resolve_inline_succ]; exact hr

/-- The trace invariant under one binder. -/
theorem traceInv_under {tbl : List CRule} (hcl : TableClosed tbl) {μ' : Level → Level}
    {ρ' : List Disp} {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat}
    {ss : List (PStep E n)} {Γ : LCtx} {δ : List Disp} {acts : List EAct}
    {hinv : EsInv ss} {hrun : RunL k Dom' Val' ss Γ} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss Γ δ acts hinv hrun s)
    (dL dF : LocalDecl) (hd : dF = Skels.onDecl (steps ss) dL)
    (dd d' : Disp) (hb : BinderRel tbl acts dd d') :
    TraceInv tbl μ' (d' :: ρ') (k + 1) Dom' Val' (shiftAll dL dF ss) (dL :: Γ) (dd :: δ)
      (binderActs dd acts) (esInv_shiftAll dL dF ss hinv)
      (runL_shift k Dom' Val' dL dF ss Γ hd hrun) (sitesShift dF dL s) := by
  intro i' A' hlu'
  cases i' with
  | zero =>
      have hz := bwalkAtL_shift_zero (k + 1) Dom' Val' dF ss dL A' Γ hlu'
        (esInv_shiftAll dL dF ss hinv) (runL_shift k Dom' Val' dL dF ss Γ hd hrun)
      rw [walkSite_shift_zero]
      revert hz
      generalize bwalkAtL (k + 1) Dom' Val' (shiftAll dL dF ss) 0 A' (dL :: Γ) hlu'
        (esInv_shiftAll dL dF ss hinv) (runL_shift k Dom' Val' dL dF ss Γ hd hrun) = w
      intro hz
      cases w with
      | keep j ht hl =>
          simp only [IsKeepZero] at hz
          subst hz
          refine ⟨rfl, ?_⟩
          cases hb with
          | keep =>
              simp only [binderActs, resolve_keep_zero, applyActs_shift_bvar_zero]
              exact Rel.refl tbl _
          | drop =>
              simp only [binderActs, resolve_drop_zero, applyActs_star]
              exact Rel.star tbl
          | inline hx =>
              simp only [binderActs, resolve_inline_zero]
              exact hx
      | repl hv => exact hz.elim
      | retype j B ht hl hc => exact hz.elim
  | succ i =>
      obtain ⟨A, hlu, hA⟩ := lookupType_cons_succ_inv hlu'
      have hw := h i A hlu
      have hs := bwalkAtL_shift_succ μ' ρ' d' k Dom' Val' dF ss dL i A Γ hlu hinv hrun A' hA.symm
        hlu' (esInv_shiftAll dL dF ss hinv) (runL_shift k Dom' Val' dL dF ss Γ hd hrun)
      rw [walkSite_shift_succ]
      refine bHitRel_of_eq ?_ (bHitRel_shift hcl hb hw hs)
      cases hb with
      | keep =>
          simp only [binderActs, resolve_keep_succ, liftIfKeep, applyActs_shift_lift]
      | drop => rfl
      | inline _ => rfl

end Rcic.Syn

#print axioms Rcic.Syn.sitesShift
#print axioms Rcic.Syn.walkSite_shift_zero
#print axioms Rcic.Syn.walkSite_shift_succ
#print axioms Rcic.Syn.bwalkAtL_shift_zero
#print axioms Rcic.Syn.bHitShift_castTerm
#print axioms Rcic.Syn.eps_wk_zero_liftIfKeep
#print axioms Rcic.Syn.bwalkAtL_shift_succ
#print axioms Rcic.Syn.binderRel_letDisp
#print axioms Rcic.Syn.bHitRel_shift
#print axioms Rcic.Syn.traceInv_under
