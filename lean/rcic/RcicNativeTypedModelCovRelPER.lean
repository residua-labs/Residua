import rcic.RcicNativeTypedModelCovRelCore

/-!
# The typed PER of the typing-parametric covariant core

The induction uses a combined operation: reverse the term endpoints while
moving the index along a related type. This operation consumes the selected
covering row directly. It yields ordinary symmetry and, by applying it twice,
index irrelevance. Thus no universal cross-row output typing, compact re-entry,
or imported old-relation PER is needed.

The rigid-spine Pi branch uses the imported spine algebra and the fact that a
Pi readback cannot also be a sort readback. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Reversal and index transport together form the smaller induction motive. -/
def TurnAtCov (C : CovTyping E) (R : Readback) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {w : Level},
    LRSCoreCov C R n Γ A B (.sort w) a → C.ty u a →
    ∀ {x y : Expr Nat}, LRSCoreCov C R n Γ x y A u → LRSCoreCov C R n Γ y x B u

private theorem cov_dom_demand_lt {a : CptT}
    {f : List (List CptT × CptT)} {s : List CptT × CptT}
    (hs : s ∈ f) {u : CptT} (hu : u ∈ s.1) :
    sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
  have := List.sizeOf_lt_of_mem hs
  have := List.sizeOf_lt_of_mem hu
  have := sizeOfT_fst_lt s
  simp
  omega

private theorem cov_pair_demand_lt {a : CptT}
    {g f : List (List CptT × CptT)} {s : List CptT × CptT}
    (hs : s ∈ f) {u : CptT} (hu : u ∈ s.1) :
    sizeOf a + sizeOf u < sizeOf (CptT.pi a g) + sizeOf (CptT.lam f) := by
  have := sizeOf_dom_lt_pi a g
  have := sizeOf_dem_lt_lam hs hu
  omega

private theorem cov_pair_output_lt {a : CptT}
    {g f : List (List CptT × CptT)} {s t : List CptT × CptT}
    (hs : s ∈ f) (ht : t ∈ g) :
    sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a g) + sizeOf (CptT.lam f) := by
  have := sizeOf_out_lt_pi (a := a) ht
  have := sizeOf_out_lt_lam hs
  omega

private theorem cov_sort_change (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {A B : Expr Nat}
    {u v : Level} {c : CptT} (h : LRSCoreCov C R n Γ A B (.sort u) c) :
    LRSCoreCov C R n Γ A B (.sort v) c :=
  lrSCoreCov_sortIdx_irrel C hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ c h

private theorem cov_edge_left (C : CovTyping E) {a u : CptT}
    (hturn : TurnAtCov C R n a u) (htrans : TransTmAtCov C R n a u)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A x y : Expr Nat} {w : Level}
    (hA : LRSCoreCov C R n Γ A A (.sort w) a) (hu : C.ty u a)
    (h : LRSCoreCov C R n Γ x y A u) : LRSCoreCov C R n Γ x x A u :=
  htrans hΓ hA hu h (hturn hΓ hA hu h)

private theorem cov_move (C : CovTyping E) {a u : CptT}
    (hturn : TurnAtCov C R n a u) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B x y : Expr Nat} {w : Level}
    (hA : LRSCoreCov C R n Γ A A (.sort w) a)
    (hAB : LRSCoreCov C R n Γ A B (.sort w) a) (hu : C.ty u a)
    (h : LRSCoreCov C R n Γ x y A u) : LRSCoreCov C R n Γ x y B u :=
  hturn hΓ hAB hu (hturn hΓ hA hu h)

private theorem cov_type_symm_step (C : CovTyping E) (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hS : ConvArgsSymmS E n) (c : CptT)
    (q : ∀ d, sizeOf d < sizeOf c → SymmTyAtCov C R n d ∧ TransTyAtCov C R n d)
    (p : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      TurnAtCov C R n a u ∧ TransTmAtCov C R n a u) :
    SymmTyAtCov C R n c := by
  intro Γ hΓ A B w h
  cases c with
  | bot => exact lrSCoreCov_bot C _ _ _ _
  | prop | sort =>
      rw [LRSCoreCov.eq_def] at h ⊢
      obtain ⟨hi, u, v, hA, hB⟩ := h
      exact ⟨hi, v, u, hB, hA⟩
  | lam f =>
      rw [LRSCoreCov.eq_def] at h
      obtain ⟨D, F, hbad, _⟩ := h
      exact Expr.noConfusion (redR_sort_eq hL hbad)
  | spine r args =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact spineClauseS_symm hS hΓ (fun _ => ⟨_, .refl _⟩) h
  | pi a f =>
      rw [LRSCoreCov.eq_def] at h ⊢
      obtain ⟨hi, D, F, D', F', hA, hB, ⟨hDctx⟩, ⟨hDD⟩, ⟨hFF⟩, ⟨v, hd⟩, rows⟩ := h
      have hd' := (q a (sizeOf_dom_lt_pi a f)).1 hΓ hd
      cases hDctx with
      | assumption _ _ l _ hD =>
          obtain ⟨l', hD'⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hDD hD
          refine ⟨hi, D', F', D, F, hB, hA,
            ⟨.assumption Γ D' l' hΓ hD'⟩, ⟨hDD.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hDD.symmT hFF.symmT⟩, ⟨v, hd'⟩, ?_⟩
          intro s hs hty x y hx hy hxy hdemand
          obtain ⟨hxy⟩ := hxy
          have hxD := hasTyT_of_tyConvT hx hDD.symmT
          have hyD := hasTyT_of_tyConvT hy hDD.symmT
          have hyxD := convT_of_tyConv (ConvT.symm _ _ _ _ hxy) hDD.symmT
          have reversed : ∀ u ∈ s.1, LRSCoreCov C R n Γ y x D u := by
            intro u hu
            exact (p a u (cov_dom_demand_lt hs hu)).1 hΓ hd' (hty u hu) (hdemand u hu)
          obtain ⟨z, hz⟩ := rows s hs hty y x hyD hxD ⟨hyxD⟩ reversed
          exact ⟨z, (q s.2 (sizeOf_out_lt_pi hs)).1 hΓ hz⟩

private theorem cov_type_trans_step (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hT : ConvArgsTransS E n) (c : CptT)
    (q : ∀ d, sizeOf d < sizeOf c → SymmTyAtCov C R n d ∧ TransTyAtCov C R n d)
    (p : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      TurnAtCov C R n a u ∧ TransTmAtCov C R n a u) :
    TransTyAtCov C R n c := by
  intro Γ hΓ A B D w hab hbd
  cases c with
  | bot => exact lrSCoreCov_bot C _ _ _ _
  | prop | sort =>
      rw [LRSCoreCov.eq_def] at hab hbd ⊢
      obtain ⟨hi, u, _, hA, _⟩ := hab
      obtain ⟨_, _, v, _, hD⟩ := hbd
      exact ⟨hi, u, v, hA, hD⟩
  | lam f =>
      rw [LRSCoreCov.eq_def] at hab
      obtain ⟨X, Y, hbad, _⟩ := hab
      exact Expr.noConfusion (redR_sort_eq hL hbad)
  | spine r args =>
      rw [LRSCoreCov.eq_def] at hab hbd ⊢
      exact spineClauseS_trans hNU hT hΓ hab hbd
  | pi a f =>
      rw [LRSCoreCov.eq_def] at hab hbd ⊢
      obtain ⟨hi, X, Y, X', Y', hA, hB, hctx, ⟨hX⟩, ⟨hY⟩, ⟨v, hd⟩, rows⟩ := hab
      obtain ⟨_, X'', Y'', X₃, Y₃, hB', hD, _, ⟨hX'⟩, ⟨hY'⟩, ⟨v', hd'⟩, rows'⟩ := hbd
      obtain ⟨ex, ey⟩ := redR_pi_unique hL hNU hB hB'
      subst ex
      subst ey
      obtain ⟨sd, td⟩ := q a (sizeOf_dom_lt_pi a f)
      have hdAligned : LRSCoreCov C R n Γ X' X₃ (.sort v) a := cov_sort_change C hL hNU hd'
      have hdSelf := td hΓ hd (sd hΓ hd)
      refine ⟨hi, X, Y, X₃, Y₃, hA, hD, hctx,
        ⟨TyConvT.trans _ _ _ _ hX hX'⟩,
        ⟨TyConvT.trans _ _ _ _ hY (tyConvT_assump_dom hW hΓ hX hY')⟩,
        ⟨v, td hΓ hd hdAligned⟩, ?_⟩
      intro s hs hty x y hx hy hxy hdemand
      obtain ⟨hxy⟩ := hxy
      have reflexive : ∀ u ∈ s.1, LRSCoreCov C R n Γ x x X u := by
        intro u hu
        obtain ⟨turn, trans⟩ := p a u (cov_dom_demand_lt hs hu)
        exact cov_edge_left C turn trans hΓ hdSelf (hty u hu) (hdemand u hu)
      have moved : ∀ u ∈ s.1, LRSCoreCov C R n Γ x y X' u := by
        intro u hu
        exact cov_move C (p a u (cov_dom_demand_lt hs hu)).1 hΓ hdSelf hd
          (hty u hu) (hdemand u hu)
      obtain ⟨z, hz⟩ := rows s hs hty x x hx hx ⟨.refl _ _ _ hx⟩ reflexive
      obtain ⟨z', hz'⟩ := rows' s hs hty x y
        (hasTyT_of_tyConvT hx hX) (hasTyT_of_tyConvT hy hX)
        ⟨convT_of_tyConv hxy hX⟩ moved
      exact ⟨z, (q s.2 (sizeOf_out_lt_pi hs)).2 hΓ hz (cov_sort_change C hL hNU hz')⟩

private theorem cov_turn_step (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hS : ConvArgsSymmS E n) (a u : CptT)
    (q : ∀ d, sizeOf d < sizeOf a + sizeOf u →
      SymmTyAtCov C R n d ∧ TransTyAtCov C R n d)
    (p : ∀ b v, sizeOf b + sizeOf v < sizeOf a + sizeOf u →
      TurnAtCov C R n b v ∧ TransTmAtCov C R n b v) :
    TurnAtCov C R n a u := by
  intro Γ hΓ A B w hAB hty F G hFG
  cases a with
  | bot =>
      rw [C.bot_inv hty]
      exact lrSCoreCov_bot C _ _ _ _
  | lam g =>
      rw [C.lam_inv hty]
      exact lrSCoreCov_bot C _ _ _ _
  | prop | sort =>
      rw [LRSCoreCov.eq_def] at hAB
      obtain ⟨_, l, l', hA, hB⟩ := hAB
      have atSort := lrSCoreCov_sortIdx_irrel C hL hNU ⟨_, hA⟩ ⟨w, .refl _⟩ u hFG
      exact lrSCoreCov_sortIdx_irrel C hL hNU ⟨w, .refl _⟩ ⟨_, hB⟩ u
        ((q u (by simp)).1 hΓ atSort)
  | spine r args =>
      rcases C.spine_inv hty with rfl | ⟨r', args', rfl⟩
      · exact lrSCoreCov_bot C _ _ _ _
      · rw [LRSCoreCov.eq_def] at hAB hFG ⊢
        have noSort := (spineClauseS_not_sort hL hNU hAB).2
        exact spineClauseS_symm hS hΓ (fun ⟨l, hl⟩ => (noSort l hl).elim) hFG
  | pi d g =>
      rcases C.pi_inv hty with rfl | ⟨f, rfl, hdom, hcover⟩ | ⟨r, args, rfl⟩
      · exact lrSCoreCov_bot C _ _ _ _
      · rw [LRSCoreCov.eq_def] at hFG hAB ⊢
        obtain ⟨X, Y, hA, ⟨hctx⟩, appRows⟩ := hFG
        obtain ⟨_, X', Y', X₂, Y₂, hA', hB, _, ⟨hX⟩, _, ⟨v, hd⟩, typeRows⟩ := hAB
        obtain ⟨ex, ey⟩ := redR_pi_unique hL hNU hA hA'
        subst ex
        subst ey
        have smallDom : sizeOf d < sizeOf (CptT.pi d g) + sizeOf (CptT.lam f) := by
          have := sizeOf_dom_lt_pi d g
          omega
        have hdBack := (q d smallDom).1 hΓ hd
        cases hctx with
        | assumption _ _ l _ hXty =>
            obtain ⟨l₂, hX₂ty⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hX hXty
            refine ⟨X₂, Y₂, hB, ⟨.assumption Γ X₂ l₂ hΓ hX₂ty⟩, ?_⟩
            intro s hs x y hx hy hxy hdemand
            obtain ⟨hxy⟩ := hxy
            have hx₁ := hasTyT_of_tyConvT hx hX.symmT
            have hy₁ := hasTyT_of_tyConvT hy hX.symmT
            have hyx₁ := convT_of_tyConv (ConvT.symm _ _ _ _ hxy) hX.symmT
            have backwards : ∀ z ∈ s.1, LRSCoreCov C R n Γ y x X z := by
              intro z hz
              exact (p d z (cov_pair_demand_lt hs hz)).1 hΓ hdBack
                (hdom s hs z hz) (hdemand z hz)
            have appEdge := appRows s hs y x hy₁ hx₁ ⟨hyx₁⟩ backwards
            rcases hcover s hs with hb | ⟨t, ht, hsub, hout⟩
            · rw [hb]
              exact lrSCoreCov_bot C _ _ _ _
            · obtain ⟨lout, typeEdge⟩ := typeRows t ht
                (fun z hz => hdom s hs z (hsub z hz)) y x hy₁ hx₁ ⟨hyx₁⟩
                (fun z hz => backwards z (hsub z hz))
              exact (p t.2 s.2 (cov_pair_output_lt hs ht)).1 hΓ typeEdge hout appEdge
      · apply lrSCoreCov_spine_irrel_pi C hL hNU hAB
        rw [LRSCoreCov.eq_def] at hFG ⊢
        exact spineClauseS_symm hS hΓ (fun h => h) hFG

private theorem cov_term_trans_step (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hT : ConvArgsTransS E n) (a u : CptT)
    (q : ∀ d, sizeOf d < sizeOf a + sizeOf u →
      SymmTyAtCov C R n d ∧ TransTyAtCov C R n d)
    (p : ∀ b v, sizeOf b + sizeOf v < sizeOf a + sizeOf u →
      TurnAtCov C R n b v ∧ TransTmAtCov C R n b v) :
    TransTmAtCov C R n a u := by
  intro Γ hΓ A w hAA hty F G H hFG hGH
  cases a with
  | bot =>
      rw [C.bot_inv hty]
      exact lrSCoreCov_bot C _ _ _ _
  | lam g =>
      rw [C.lam_inv hty]
      exact lrSCoreCov_bot C _ _ _ _
  | prop | sort =>
      rw [LRSCoreCov.eq_def] at hAA
      obtain ⟨_, l, _, hA, _⟩ := hAA
      have first := lrSCoreCov_sortIdx_irrel C hL hNU ⟨_, hA⟩ ⟨w, .refl _⟩ u hFG
      have second := lrSCoreCov_sortIdx_irrel C hL hNU ⟨_, hA⟩ ⟨w, .refl _⟩ u hGH
      exact lrSCoreCov_sortIdx_irrel C hL hNU ⟨w, .refl _⟩ ⟨_, hA⟩ u
        ((q u (by simp)).2 hΓ first second)
  | spine r args =>
      rcases C.spine_inv hty with rfl | ⟨r', args', rfl⟩
      · exact lrSCoreCov_bot C _ _ _ _
      · rw [LRSCoreCov.eq_def] at hFG hGH ⊢
        exact spineClauseS_trans hNU hT hΓ hFG hGH
  | pi d g =>
      rcases C.pi_inv hty with rfl | ⟨f, rfl, hdom, hcover⟩ | ⟨r, args, rfl⟩
      · exact lrSCoreCov_bot C _ _ _ _
      · rw [LRSCoreCov.eq_def] at hFG hGH hAA ⊢
        obtain ⟨X, Y, hA, hctx, firstRows⟩ := hFG
        obtain ⟨X', Y', hA', _, secondRows⟩ := hGH
        obtain ⟨ex, ey⟩ := redR_pi_unique hL hNU hA hA'
        subst ex
        subst ey
        obtain ⟨_, X', Y', X'', Y'', hA', hA'', _, _, _, ⟨v, hd⟩, typeRows⟩ := hAA
        obtain ⟨ex, ey⟩ := redR_pi_unique hL hNU hA hA'
        subst ex
        subst ey
        obtain ⟨ex, ey⟩ := redR_pi_unique hL hNU hA hA''
        subst ex
        subst ey
        refine ⟨X, Y, hA, hctx, ?_⟩
        intro s hs x y hx hy hxy hdemand
        have reflexive : ∀ z ∈ s.1, LRSCoreCov C R n Γ x x X z := by
          intro z hz
          obtain ⟨turn, trans⟩ := p d z (cov_pair_demand_lt hs hz)
          exact cov_edge_left C turn trans hΓ hd (hdom s hs z hz) (hdemand z hz)
        have firstEdge := firstRows s hs x x hx hx ⟨.refl _ _ _ hx⟩ reflexive
        have secondEdge := secondRows s hs x y hx hy hxy hdemand
        rcases hcover s hs with hb | ⟨t, ht, hsub, hout⟩
        · rw [hb]
          exact lrSCoreCov_bot C _ _ _ _
        · obtain ⟨lout, typeEdge⟩ := typeRows t ht
            (fun z hz => hdom s hs z (hsub z hz)) x x hx hx ⟨.refl _ _ _ hx⟩
            (fun z hz => reflexive z (hsub z hz))
          exact (p t.2 s.2 (cov_pair_output_lt hs ht)).2 hΓ typeEdge hout firstEdge secondEdge
      · rw [LRSCoreCov.eq_def] at hFG hGH ⊢
        exact spineClauseS_trans hNU hT hΓ hFG hGH

/-- The kernel induction proves type PER, combined term reversal/transport,
and term transitivity together. -/
theorem covPERKernel (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (k : Nat) :
    (∀ c, sizeOf c ≤ k → SymmTyAtCov C R n c ∧ TransTyAtCov C R n c) ∧
    (∀ a u, sizeOf a + sizeOf u ≤ k → TurnAtCov C R n a u ∧ TransTmAtCov C R n a u) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      refine ⟨?_, ?_⟩
      · intro c hc
        have q : ∀ d, sizeOf d < sizeOf c →
            SymmTyAtCov C R n d ∧ TransTyAtCov C R n d := by
          intro d hd
          exact (ih (sizeOf d) (Nat.lt_of_lt_of_le hd hc)).1 d (Nat.le_refl _)
        have p : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
            TurnAtCov C R n a u ∧ TransTmAtCov C R n a u := by
          intro a u hau
          exact (ih (sizeOf a + sizeOf u) (Nat.lt_of_lt_of_le hau hc)).2 a u (Nat.le_refl _)
        exact ⟨cov_type_symm_step C hL hW hS c q p,
          cov_type_trans_step C hL hNU hW hT c q p⟩
      · intro a u hau
        have q : ∀ d, sizeOf d < sizeOf a + sizeOf u →
            SymmTyAtCov C R n d ∧ TransTyAtCov C R n d := by
          intro d hd
          exact (ih (sizeOf d) (Nat.lt_of_lt_of_le hd hau)).1 d (Nat.le_refl _)
        have p : ∀ b v, sizeOf b + sizeOf v < sizeOf a + sizeOf u →
            TurnAtCov C R n b v ∧ TransTmAtCov C R n b v := by
          intro b v hbv
          exact (ih (sizeOf b + sizeOf v) (Nat.lt_of_lt_of_le hbv hau)).2 b v (Nat.le_refl _)
        exact ⟨cov_turn_step C hL hNU hW hS a u q p,
          cov_term_trans_step C hL hNU hT a u q p⟩

/-- The requested irrelevance, symmetry and transitivity motives follow from
the kernel induction, uniformly in the compact typing implementation. -/
theorem typedPERCov (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (k : Nat) :
    (∀ c, sizeOf c ≤ k → SymmTyAtCov C R n c ∧ TransTyAtCov C R n c) ∧
    (∀ a u, sizeOf a + sizeOf u ≤ k →
      IrrelAtCov C R n a u ∧ SymmTmAtCov C R n a u ∧ TransTmAtCov C R n a u) := by
  obtain ⟨q, p⟩ := covPERKernel C hL hNU hW hS hT k
  refine ⟨q, ?_⟩
  intro a u hau
  obtain ⟨turn, trans⟩ := p a u hau
  refine ⟨?_, ?_, trans⟩
  · intro Γ hΓ A B w hab hty x y hxy
    obtain ⟨sym, tran⟩ := q a (by omega)
    exact cov_move C turn hΓ (tran hΓ hab (sym hΓ hab)) hab hty hxy
  · intro Γ hΓ A w haa hty x y hxy
    exact turn hΓ haa hty hxy

theorem lrSCoreCov_irrel (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (a u : CptT) :
    IrrelAtCov C R n a u :=
  ((typedPERCov C hL hNU hW hS hT _).2 a u (Nat.le_refl _)).1

theorem lrSCoreCov_symm (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (c : CptT) :
    SymmTyAtCov C R n c :=
  ((typedPERCov C hL hNU hW hS hT _).1 c (Nat.le_refl _)).1

theorem lrSCoreCov_trans (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (c : CptT) :
    TransTyAtCov C R n c :=
  ((typedPERCov C hL hNU hW hS hT _).1 c (Nat.le_refl _)).2

theorem lrSCoreCov_symm_tm (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (a u : CptT) :
    SymmTmAtCov C R n a u :=
  ((typedPERCov C hL hNU hW hS hT _).2 a u (Nat.le_refl _)).2.1

theorem lrSCoreCov_trans_tm (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (a u : CptT) :
    TransTmAtCov C R n a u :=
  ((typedPERCov C hL hNU hW hS hT _).2 a u (Nat.le_refl _)).2.2

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_PER_ROOTS
#print axioms TurnAtCov
#print axioms covPERKernel
#print axioms typedPERCov
#print axioms lrSCoreCov_irrel
#print axioms lrSCoreCov_symm
#print axioms lrSCoreCov_trans
#print axioms lrSCoreCov_symm_tm
#print axioms lrSCoreCov_trans_tm
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_PER_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
