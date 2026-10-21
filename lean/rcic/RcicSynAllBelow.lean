import rcic.RcicSynSepUnique

/-!
# Syntactic sortRow, build step 4d — Global `AllBelow` Pack Consequences: Automatic `ESChain` & `SortChainCoh` Discharge, Multi-Step Conjecture 2.9 Item 3, and End-to-End `sortRow` / `SortUnique` / `sepContract`

`research/rcic/semantic/S3_ES_ARMS.md` §53 and `S0_SORTROW_SYNTACTIC.md` §2.4, §4.

1. **§1 `AllBelow` and Well-Founded Induction (`lexDM_wf`)**:
   - `AllBelow Aw tbl`: `∀ bound, Below Aw tbl bound`.
   - `allBelow_of_lexDM_step`: derives `AllBelow Aw tbl` from the inductive step
     `∀ bound, (∀ m, LexDM m bound → Below Aw tbl m) → Below Aw tbl bound` via `lexDM_wf.fix`.
   - `es_of_allBelow`, `cl_of_allBelow`, `eut_of_allBelow`, `cts_of_allBelow`,
     `pbit_of_allBelow`, `bitCoh_of_allBelow`, and `sortCoh_of_allBelow`: extract every pack
     claim at any derivation from `AllBelow Aw tbl` via `Prod.Lex.right _ (Nat.lt_succ_self _)`.

2. **§2 Automatic `TyCvP.ESChain` and `TyCvP.SortChainCoh` Discharge**:
   - `esChain_of_allBelow`: for **any** `c : TyCvP E n Γ A B`, `dA : TyP E n Γ A T₁`, and
     `dB : TyP E n Γ B T₂`, `AllBelow Aw tbl → DispFor σ E n Γ ρ → c.ESChain tbl σ ρ dA dB`
     (using `c₁.endpoints` at `.trans` to obtain `dM : TyP E n Γ B Tₘ` either as `e₁ ▸ dA`
     when `c₁` is a `.refl` chain or as `dR₁` when `c₁` contains an `.of` step — requiring
     **zero external middle typings** and **zero `hUniq` / `DT012T`**).
   - `sortCoh_tyCvP_of_allBelow` and `sortChainCoh_of_allBelow`: for **any** `c : TyCvP E n Γ A B`,
     `dA : TyP E n Γ A (.sort u)`, and `dB : TyP E n Γ B (.sort v)`,
     `AllBelow Aw tbl → TableWF tbl → DispFor σ E n Γ ρ → c.SortChainCoh σ dA dB`.

3. **§3 Multi-Step Conjecture 2.9 Item 3 (`sort u ≢ Π x : A, B`, zero `.pi` typing premise)**:
   - `canonPiOfTyP`: constructs a canonical `TyP.pi` node from any `D : TyP E n Γ (.pi A B) T`
     via `piInvP_here D`.
   - `not_tyCvP_sort_pi_of_allBelow` and `not_tyCvP_pi_sort_of_allBelow`: for any
     `c : TyCvP E n Γ (.sort u) (.pi A B)` (or symmetric), `c.endpoints` either equates
     `.sort u = .pi A B` (`Expr.noConfusion`) or extracts `dR : TyP E n Γ (.pi A B) (.sort uR)`,
     from which `canonPiOfTyP dR` and `esChain_of_allBelow` + `not_convE_sort_pi_wf` refute `c`
     with **zero external `.pi A B` typing premise**.
   - `not_tyConvT_sort_pi_of_allBelow`, `not_tyConvT_pi_sort_of_allBelow`, and
     `not_convT_sort_pi_of_allBelow`: plain `TyConvT` and `ConvT` forms under `EnvWfT` and `CtxWfT`.

4. **§4 End-to-End `sortRow`, `SortUnique`, and `sepContract` from `AllBelow` + `TableWF`**:
   - `sortRow_tyCvP_of_allBelow`, `sortRow_of_allBelow`, and `sortRow_convT_of_allBelow`:
     `EnvWfT E → CtxWfT E n Γ → TyConvT E n Γ (.sort u) (.sort v) → eqN u v`.
   - `sortUnique_tyP_of_allBelow` and `sortUnique_of_allBelow`:
     `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ T (.sort u) → HasTyT E n Γ T (.sort v) → eqN u v`.
   - `sepContract_tyCvP_of_allBelow`, `sepContract_of_allBelow`,
     `sepContract_symm_of_allBelow`, and `sepContract_convT_of_allBelow`:
     `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `AllBelow` and Well-Founded Induction (`lexDM_wf`) -/

/-- Global mutual-pack validity at all `LexDM` bounds for `(Aw, tbl)`. -/
def AllBelow (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ bound : List Nat × Nat, Below Aw tbl bound

/-- Well-founded induction principle for `AllBelow Aw tbl` along `lexDM_wf`. -/
theorem allBelow_of_lexDM_step {Aw : Nat → Nat} {tbl : List CRule}
    (step : ∀ bound : List Nat × Nat,
      (∀ m : List Nat × Nat, LexDM m bound → Below Aw tbl m) → Below Aw tbl bound) :
    AllBelow Aw tbl :=
  fun bound => lexDM_wf.fix step bound

/-- Pointwise `LexDM` step `(m.1, m.2) < (m.1, m.2 + 1)`. -/
theorem lexDM_succ_snd (m : List Nat × Nat) : LexDM m (m.1, m.2 + 1) := by
  rcases m with ⟨atoms, wt⟩
  exact Prod.Lex.right atoms (Nat.lt_succ_self wt)

/-- Extract `ES tbl σ ρ h` for any `h : CvP E n Γ a b T` from `AllBelow Aw tbl`. -/
theorem es_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) {σ : Level → Level} {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ) :
    ES tbl σ ρ h :=
  (hBel (h.atoms Aw, h.wt Aw + 1)).es h σ ρ hρ (lexDM_succ_snd (cvMeas Aw h))

/-- Extract `CL tbl σ ρ D₁ D₂` for any `D₁ : TyP E n Γ e T₁`, `D₂ : TyP E n Γ e T₂`
    from `AllBelow Aw tbl`. -/
theorem cl_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    {σ : Level → Level} {ρ : List Disp} (hρ : DispFor σ E n Γ ρ) :
    CL tbl σ ρ D₁ D₂ :=
  (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).cl D₁ D₂ σ ρ hρ
    (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))

/-- Extract `EUT tbl σ ρ D₁ D₂` for any `D₁ : TyP E n Γ e T`, `D₂ : TyP E n Γ e T'`
    from `AllBelow Aw tbl`. -/
theorem eut_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    (D₁ : TyP E n Γ e T) (D₂ : TyP E n Γ e T')
    {σ : Level → Level} {ρ : List Disp} (hρ : DispFor σ E n Γ ρ) :
    EUT tbl σ ρ D₁ D₂ :=
  (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).eut D₁ D₂ σ ρ hρ
    (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))

/-- Extract `CTS h DX` for any `h : CvP E n Γ X Y (.sort w)`, `DX : TyP E n Γ X (.sort s)`
    from `AllBelow Aw tbl`. -/
theorem cts_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s)) :
    CTS h DX :=
  (hBel ((cvTyMeas Aw h DX).1, (cvTyMeas Aw h DX).2 + 1)).cts h DX
    (lexDM_succ_snd (cvTyMeas Aw h DX))

/-- Extract `PBit σ ρ D DT` for any `D : TyP E n Γ e T`, `DT : TyP E n Γ T (.sort s)`
    from `AllBelow Aw tbl`. -/
theorem pbit_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    {σ : Level → Level} {ρ : List Disp} (hρ : DispFor σ E n Γ ρ) :
    PBit σ ρ D DT :=
  (hBel ((tyPairMeas Aw D DT).1, (tyPairMeas Aw D DT).2 + 1)).pb D DT σ ρ hρ
    (lexDM_succ_snd (tyPairMeas Aw D DT))

/-- Extract `BitCoh σ D₁ D₂` (`levelIsZero (σ u) = levelIsZero (σ v)`) for any
    `D₁ : TyP E n Γ T (.sort u)`, `D₂ : TyP E n Γ T (.sort v)` from `AllBelow Aw tbl`. -/
theorem bitCoh_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    {σ : Level → Level} {ρ : List Disp} (hρ : DispFor σ E n Γ ρ) :
    BitCoh σ D₁ D₂ :=
  (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).bitCoh D₁ D₂ σ ρ hρ
    (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))

/-- Extract `SortCoh σ D₁ D₂` (`eqN (σ u) (σ v)`) for any `D₁ : TyP E n Γ T (.sort u)` and
    `D₂ : TyP E n Γ T (.sort v)` from `AllBelow Aw tbl` and `TableWF tbl`. -/
theorem sortCoh_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    {σ : Level → Level} {ρ : List Disp} (hρ : DispFor σ E n Γ ρ) :
    SortCoh σ D₁ D₂ :=
  sortCoh_of_below_pair Aw hW D₁ D₂ σ ρ hρ (hBel (cvMeas Aw (sortPairNode D₁ D₂)))

/-! ## §2 Automatic `TyCvP.ESChain` and `TyCvP.SortChainCoh` Discharge -/

/-- Under `AllBelow Aw tbl` and `DispFor σ E n Γ ρ`, **every** heterogeneous `TyCvP` chain
    `c : TyCvP E n Γ A B` satisfies `c.ESChain tbl σ ρ dA dB` for any endpoint typings
    `dA : TyP E n Γ A T₁` and `dB : TyP E n Γ B T₂`, using `c₁.endpoints` to supply the
    intermediate typing at `.trans` with zero external middle typings and zero `hUniq`. -/
theorem esChain_of_allBelow {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelow Aw tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ) :
    ∀ {A B T₁ T₂ : Expr Nat} (c : TyCvP E n Γ A B)
      (dA : TyP E n Γ A T₁) (dB : TyP E n Γ B T₂),
      c.ESChain tbl σ ρ dA dB
  | _, _, _, _, .refl _ _, dA, dB =>
      .refl dA dB (cl_of_allBelow hBel dA dB hρ)
  | _, _, _, _, .of _ _ _ _ h, dA, dB =>
      .of h dA dB
        (cl_of_allBelow hBel dA h.dl hρ)
        (es_of_allBelow hBel h hρ)
        (cl_of_allBelow hBel h.dr dB hρ)
  | _, _, _, _, .trans _ _ _ _ c₁ c₂, dA, dB => by
      cases c₁.endpoints with
      | inl h₁ =>
          let dM := h₁ ▸ dA
          exact .trans c₁ c₂ dA dM dB
            (esChain_of_allBelow hBel hρ c₁ dA dM)
            (esChain_of_allBelow hBel hρ c₂ dM dB)
      | inr p₁ =>
          rcases p₁ with ⟨_, _, _, dR₁⟩
          exact .trans c₁ c₂ dA dR₁ dB
            (esChain_of_allBelow hBel hρ c₁ dA dR₁)
            (esChain_of_allBelow hBel hρ c₂ dR₁ dB)

/-- Under `AllBelow Aw tbl`, `TableWF tbl`, and `DispFor σ E n Γ ρ`, **every** `c : TyCvP E n Γ A B`
    satisfies `c.SortCoh σ` at all internal `.trans` junctions. -/
theorem sortCoh_tyCvP_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ) :
    ∀ {A B : Expr Nat} (c : TyCvP E n Γ A B), c.SortCoh σ
  | _, _, .refl _ _ => trivial
  | _, _, .of _ _ _ _ _ => trivial
  | _, _, .trans _ _ _ _ c₁ c₂ => by
      refine ⟨sortCoh_tyCvP_of_allBelow hBel hW hρ c₁,
        sortCoh_tyCvP_of_allBelow hBel hW hρ c₂, ?_⟩
      cases c₁.endpoints with
      | inl _ =>
          cases c₂.endpoints <;> exact trivial
      | inr p₁ =>
          rcases p₁ with ⟨_, _, _, dR₁⟩
          cases c₂.endpoints with
          | inl _ => exact trivial
          | inr p₂ =>
              rcases p₂ with ⟨_, _, dL₂, _⟩
              exact sortCoh_of_allBelow hBel hW dR₁ dL₂ hρ

/-- Under `AllBelow Aw tbl`, `TableWF tbl`, and `DispFor σ E n Γ ρ`, **every** `c : TyCvP E n Γ A B`
    and endpoint sort typings `dA : TyP E n Γ A (.sort u)`, `dB : TyP E n Γ B (.sort v)`
    satisfy `c.SortChainCoh σ dA dB`. -/
theorem sortChainCoh_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ)
    {A B : Expr Nat} {u v : Level}
    (c : TyCvP E n Γ A B)
    (dA : TyP E n Γ A (.sort u)) (dB : TyP E n Γ B (.sort v)) :
    c.SortChainCoh σ dA dB := by
  refine ⟨sortCoh_tyCvP_of_allBelow hBel hW hρ c, ?_⟩
  cases c.endpoints with
  | inl h =>
      exact sortCoh_of_allBelow hBel hW (h ▸ dA) dB hρ
  | inr p =>
      rcases p with ⟨_, _, dL, dR⟩
      exact ⟨sortCoh_of_allBelow hBel hW dA dL hρ, sortCoh_of_allBelow hBel hW dR dB hρ⟩

/-! ## §3 Multi-Step Conjecture 2.9 Item 3 (`sort u ≢ Π x : A, B`, zero `.pi` typing premise) -/

/-- Canonical `TyP.pi` node extracted from any `D : TyP E n Γ (.pi A B) T` via `piInvP_here`. -/
def canonPiOfTyP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B T : Expr Nat}
    (D : TyP E n Γ (.pi A B) T) :
    TyP E n Γ (.pi A B) (.sort (.imax (piInvP_here D).u (piInvP_here D).v)) :=
  let P := piInvP_here D
  TyP.pi E n Γ A P.u B P.v P.hA P.hB

/-- Multi-step Conjecture 2.9 item 3 on `TyCvP`: under `AllBelow Aw tbl`, `TableWF tbl`,
    and `DispFor σ E n Γ ρ`, no `TyCvP E n Γ (.sort u) (.pi A B)` exists (requiring **zero**
    external typing premise on `.pi A B`). -/
theorem not_tyCvP_sort_pi_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ)
    {u : Level} {A B : Expr Nat}
    (c : TyCvP E n Γ (.sort u) (.pi A B)) :
    False := by
  cases he : c.endpoints with
  | inl h => exact Expr.noConfusion h
  | inr p =>
      rcases p with ⟨_, _, _, dR⟩
      let dSort := TyP.sort E n Γ u (.succ u) (eqN_refl _)
      let P := piInvP_here dR
      let dPi := canonPiOfTyP dR
      have hchain := esChain_of_allBelow hBel hρ c dSort dPi
      have hconv : ConvMod (EStep tbl) LvlEq (.sort (σ u))
          (.pi (P.hA.eps σ ρ) (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: ρ)))) := by
        simpa only [dSort, dPi, canonPiOfTyP, eps_sort, eps_pi_clause] using
          convMod_of_tyCvP_esChain hchain
      exact not_convE_sort_pi_wf hW (σ u) (P.hA.eps σ ρ)
        (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: ρ))) hconv

/-- Symmetric multi-step Conjecture 2.9 item 3 on `TyCvP` (`TyCvP E n Γ (.pi A B) (.sort u) → False`). -/
theorem not_tyCvP_pi_sort_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (hρ : DispFor σ E n Γ ρ)
    {u : Level} {A B : Expr Nat}
    (c : TyCvP E n Γ (.pi A B) (.sort u)) :
    False := by
  cases he : c.endpoints with
  | inl h => exact Expr.noConfusion h
  | inr p =>
      rcases p with ⟨_, _, dL, _⟩
      let P := piInvP_here dL
      let dPi := canonPiOfTyP dL
      let dSort := TyP.sort E n Γ u (.succ u) (eqN_refl _)
      have hchain := esChain_of_allBelow hBel hρ c dPi dSort
      have hconv : ConvMod (EStep tbl) LvlEq
          (.pi (P.hA.eps σ ρ) (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: ρ))))
          (.sort (σ u)) := by
        simpa only [dPi, dSort, canonPiOfTyP, eps_pi_clause, eps_sort] using
          convMod_of_tyCvP_esChain hchain
      exact not_convE_pi_sort_wf hW (P.hA.eps σ ρ)
        (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: ρ))) (σ u) hconv

/-- Plain `TyConvT` Conjecture 2.9 item 3 (`EnvWfT E → CtxWfT E n Γ → TyConvT E n Γ (.sort u) (.pi A B) → False`). -/
theorem not_tyConvT_sort_pi_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u : Level} {A B : Expr Nat}
    (hc : TyConvT E n Γ (.sort u) (.pi A B)) :
    False :=
  not_tyCvP_sort_pi_of_allBelow hBel hW
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    (enrichTyConvT_of_envWfT hEnv hΓ hc)

/-- Symmetric plain `TyConvT` Conjecture 2.9 item 3 (`TyConvT E n Γ (.pi A B) (.sort u) → False`). -/
theorem not_tyConvT_pi_sort_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u : Level} {A B : Expr Nat}
    (hc : TyConvT E n Γ (.pi A B) (.sort u)) :
    False :=
  not_tyCvP_pi_sort_of_allBelow hBel hW
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    (enrichTyConvT_of_envWfT hEnv hΓ hc)

/-- Single-step plain `ConvT` Conjecture 2.9 item 3 (`ConvT E n Γ (.sort u) (.pi A B) (.sort w) → False`). -/
theorem not_convT_sort_pi_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u w : Level} {A B : Expr Nat}
    (h : ConvT E n Γ (.sort u) (.pi A B) (.sort w)) :
    False :=
  not_tyConvT_sort_pi_of_allBelow hBel hW hEnv hΓ (.of Γ (.sort u) (.pi A B) w h)

/-! ## §4 End-to-End `sortRow`, `SortUnique`, and `sepContract` from `AllBelow` + `TableWF` -/

/-- `sortRow` on `TyCvP` from `AllBelow Aw tbl` and `TableWF tbl` (with zero chain-specific hypotheses). -/
theorem sortRow_tyCvP_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
    (hρ : DispFor id E n Γ ρ)
    {u v : Level} (c : TyCvP E n Γ (.sort u) (.sort v)) :
    eqN u v :=
  sortRow_of_tyCvP_esChain_id hW c ρ
    (esChain_of_allBelow hBel hρ c
      (TyP.sort E n Γ u (.succ u) (eqN_refl _))
      (TyP.sort E n Γ v (.succ v) (eqN_refl _)))

/-- End-to-end `sortRow` on plain `TyConvT` from `AllBelow Aw tbl` and `TableWF tbl`:
    `EnvWfT E → CtxWfT E n Γ → TyConvT E n Γ (.sort u) (.sort v) → eqN u v`. -/
theorem sortRow_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} (hc : TyConvT E n Γ (.sort u) (.sort v)) :
    eqN u v :=
  sortRow_tyCvP_of_allBelow hBel hW
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    (enrichTyConvT_of_envWfT hEnv hΓ hc)

/-- Single-step plain `ConvT` `sortRow` from `AllBelow Aw tbl` and `TableWF tbl`:
    `EnvWfT E → CtxWfT E n Γ → ConvT E n Γ (.sort u) (.sort v) (.sort w) → eqN u v`. -/
theorem sortRow_convT_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v w : Level} (h : ConvT E n Γ (.sort u) (.sort v) (.sort w)) :
    eqN u v :=
  sortRow_of_allBelow hBel hW hEnv hΓ (.of Γ (.sort u) (.sort v) w h)

/-- `SortUnique` on `TyP` from `AllBelow Aw tbl` and `TableWF tbl`. -/
theorem sortUnique_tyP_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
    (hρ : DispFor id E n Γ ρ)
    {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)) :
    eqN u v :=
  sortCoh_of_allBelow hBel hW D₁ D₂ hρ

/-- End-to-end `SortUnique` on plain `HasTyT` from `AllBelow Aw tbl` and `TableWF tbl`:
    `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ T (.sort u) → HasTyT E n Γ T (.sort v) → eqN u v`. -/
theorem sortUnique_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {u v : Level}
    (h₁ : HasTyT E n Γ T (.sort u)) (h₂ : HasTyT E n Γ T (.sort v)) :
    eqN u v :=
  sortUnique_tyP_of_allBelow hBel hW
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    (enrichHasTyT_of_envWfT hEnv hΓ h₁)
    (enrichHasTyT_of_envWfT hEnv hΓ h₂)

/-- Prop/Sort Separation Contract on `TyCvP` from `AllBelow Aw tbl` and `TableWF tbl`. -/
theorem sepContract_tyCvP_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
    (hρ : DispFor id E n Γ ρ)
    {P : Expr Nat} {l : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (c : TyCvP E n Γ (.sort l) P) :
    False :=
  not_tyCvP_sort_prop_of_sortChainCoh dP c
    (sortChainCoh_of_allBelow hBel hW hρ c (TyP.sort E n Γ l (.succ l) (eqN_refl _)) dP)

/-- End-to-end Prop/Sort Separation Contract on plain `HasTyT` / `TyConvT` from `AllBelow Aw tbl`
    and `TableWF tbl`:
    `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False`. -/
theorem sepContract_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hc : TyConvT E n Γ (.sort l) P) :
    False :=
  sepContract_tyCvP_of_allBelow hBel hW
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    (enrichHasTyT_of_envWfT hEnv hΓ hP)
    (enrichTyConvT_of_envWfT hEnv hΓ hc)

/-- Symmetric end-to-end Prop/Sort Separation Contract on plain `HasTyT` / `TyConvT`
    (`TyConvT E n Γ P (.sort l) → False`). -/
theorem sepContract_symm_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hc : TyConvT E n Γ P (.sort l)) :
    False :=
  not_tyCvP_prop_sort_of_sortChainCoh
    (enrichHasTyT_of_envWfT hEnv hΓ hP)
    (enrichTyConvT_of_envWfT hEnv hΓ hc)
    (sortChainCoh_of_allBelow hBel hW
      (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
      (enrichTyConvT_of_envWfT hEnv hΓ hc)
      (enrichHasTyT_of_envWfT hEnv hΓ hP)
      (TyP.sort E n Γ l (.succ l) (eqN_refl _)))

/-- Single-step plain `ConvT` Prop/Sort Separation Contract from `AllBelow Aw tbl` and `TableWF tbl`. -/
theorem sepContract_convT_of_allBelow {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelow Aw tbl) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l w : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (h : ConvT E n Γ (.sort l) P (.sort w)) :
    False :=
  sepContract_of_allBelow hBel hW hEnv hΓ hP (.of Γ (.sort l) P w h)

end Rcic.Syn
