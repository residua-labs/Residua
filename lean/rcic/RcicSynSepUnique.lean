import rcic.RcicSynEnrich

/-!
# Syntactic sortRow, build step 4c — Uniqueness of the Sort of a Type (`SortUnique`), the Prop/Sort Separation Contract (`sepContract`), and Sealed Ill-Formed Context Refutations

`research/rcic/semantic/S3_ES_ARMS.md` §52 and `S0_SORTROW_SYNTACTIC.md` §2.4, §4.
Addresses `cc`'s Step 4 requests (13:40Z, 01:30Z, and 08:55Z from #7026):

1. **§1 Uniqueness of the Sort of a Type (`SortUnique`, `cc` 01:30Z + 08:55Z requests)**:
   - On `TyP`: `sortUnique_of_tyP_eut_cl`, `sortPairNode`, `sortCoh_of_below_pair`,
     `sortUnique_of_tyP_below`, `sortUnique_of_tyP_below_nil`,
     `not_tyP_sort_zero_succ_of_sortCoh`, and `not_tyP_sort_zero_succ_of_below`.
   - On plain `HasTyT`: `sortUnique_of_hasTyT_sortCoh`, `sortUnique_of_hasTyT_eut_cl`,
     `sortUnique_of_hasTyT_envWfT`, and `sortUnique_of_hasTyT_envWfT_below`:
     `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ T (.sort u) → HasTyT E n Γ T (.sort v) → eqN u v`,
     where `sortUnique_of_hasTyT_envWfT` additionally takes the coherence premise
     `hcoh : SortCoh id (enrich h₁) (enrich h₂)` (its discharge is the `AllBelow`
     fixpoint, codex-4c #7140) and `sortUnique_of_hasTyT_envWfT_below` takes `Below`
     at the canonical `ρ = (enrichCtxWfT_of_envWfT hEnv hΓ).disp id`.

2. **§2 Heterogeneous `TyCvP` Sort-Agreement (`TyCvP.endpoints`, `TyCvP.SortCoh`, `eqN_of_tyCvP_sortChainCoh`)**:
   - `TyCvP.endpoints`: extracts `PSum (A = B) ((uL : Level) × (uR : Level) × TyP E n Γ A (.sort uL) × TyP E n Γ B (.sort uR))`
     from any `c : TyCvP E n Γ A B` with zero external middle typings at `.trans`.
   - `TyCvP.SortCoh`, `eqN_of_tyCvP_endpoints`, `TyCvP.SortChainCoh`,
     `eqN_of_tyCvP_sortChainCoh`, and `eqN_of_tyCvP_sortChainCoh_id`: every `.of` step
     carries `h.dl` and `h.dr` at the **same** sort `w` (`eqN (σ w) (σ w)` by `eqN_refl`),
     so `SortCoh` is required only at junctions between consecutive steps, yielding
     `eqN (σ u) (σ v)` across any `TyCvP` chain between `A : .sort u` and `B : .sort v`.

3. **§3 The Prop/Sort Separation Contract (`cc` 13:40Z + 08:55Z requests)**:
   - On `TyCvP` and `CvP`: `not_tyCvP_sort_prop_of_sortChainCoh`,
     `not_tyCvP_prop_sort_of_sortChainCoh`, `not_cvp_sort_prop_of_sortCoh`,
     `not_cvp_prop_sort_of_sortCoh`, `not_cvp_sort_prop_of_below`, and
     `not_cvp_prop_sort_of_below` (since `.sort l : .sort (.succ l)` and `P : .sort .zero`
     yield `eqN (.succ l) .zero`, refuted by `not_eqN_zero_succ l`).
   - On plain `HasTyT` / `TyConvT` / `ConvT`: `sepContract_of_tyConvT`,
     `sepContract_of_tyConvT_envWfT`, `sepContract_symm_of_tyConvT_envWfT`,
     `sepContract_of_convT_envWfT`, and `sepContract_of_convT_envWfT_below`:
     `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False`,
     where the `_envWfT` variants additionally take the chain-coherence premise
     `hchain : (enrichTyConvT_of_envWfT hEnv hΓ hc).SortChainCoh id … …`
     (`sepContract_of_convT_envWfT_below` takes `Below` at the canonical `ρ`).

4. **§4 Why `CtxWfT E n Γ` is required by `O6` (`cc` 08:55Z note on `SepAll` at ill-formed `Γ`)**:
   - Exact lemmas in `O6` (`RcicSynEnrich.lean`) that consume `hΓ : CtxWfT E n Γ`:
     (a) `enrichCtxWfT` (`RcicSynEnrich.lean:1162`), which builds the spine `C : CtxP E n Γ`;
     (b) `ctxP_lookupType_sort` (`RcicSynEnrich.lean:458`), called by `enrichHasTyT` on
         `HasTyT.bvar` (`:843`) and `enrichConvT` on `ConvT.zetaLocal` (`:907`) to supply the
         sort witness `hA : TyP E n Γ A (.sort u)` stored in `TyP.bvar`;
     (c) `dispFor_ctxP_id` (`RcicSynPack.lean:188`), which builds `DispFor id E n Γ (C.disp id)`
         from `C : CtxP E n Γ`.
   - Sealed refutation theorems proving that without `CtxWfT E n Γ`, the invariants of `TyP`/`CvP`
     fail unconditionally at every `(E, n)`:
     - `not_hasTyT_regularity_illCtx`: in `illCtxReg = [.assumption (.bvar 0)]`,
       `HasTyT E n illCtxReg (.bvar 0) (.bvar 1)` holds (`hasTyT_illCtxReg_bvar0`), while
       `∀ S, HasTyT E n illCtxReg (.bvar 1) S → False` (`not_hasTyT_illCtxReg_bvar1`),
       refuting `HasTyT` regularity (`TyP.reg`).
     - `not_convT_lhs_typed_illCtx`: in `illCtxEta = [.assumption (.pi (.bvar 0) (.sort .zero))]`,
       `ConvT.eta` derives `ConvT E n illCtxEta (.lam (.bvar 1) (.app (.bvar 1) (.bvar 0))) (.bvar 0) (.pi (.bvar 1) (.sort .zero))`
       (`convT_illCtxEta_eta`), while its left-hand side `.lam (.bvar 1) (.app (.bvar 1) (.bvar 0))`
       has no `HasTyT` typing at any `S` (`not_hasTyT_illCtxEta_lam`), refuting `ConvT`
       endpoint well-typedness (`CvP.dl` / `etaLeftP`).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Uniqueness of the Sort of a Type (`SortUnique`, `cc` 01:30Z + 08:55Z requests) -/

/-- `SortUnique` on `TyP` from `EUT` + `CL` (`sortCoh_of_eut_cl` at `σ = id`):
    for any `D₁ : TyP E n Γ T (.sort u)` and `D₂ : TyP E n Γ T (.sort v)` under a
    `TableWF` table, `EUT tbl id ρ D₁ D₂` and `CL` of `D₁.reg.2`, `D₂.reg.2` against
    canonical `TyP.sort` nodes prove `eqN u v`. -/
theorem sortUnique_of_tyP_eut_cl {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (ρ : List Disp)
    (heut : EUT tbl id ρ D₁ D₂)
    (hL : CL tbl id ρ D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl id ρ D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  sortCoh_of_eut_cl hW D₁ D₂ id ρ heut hL hR

/-- Non-transport `CvP.refl` wrapper around `TyP.pi E n Γ T u (lift 0 1 T) v D₁ (wkAtZero D₂)`,
    whose weight strictly bounds both `D₁` and `D₂`. -/
def sortPairNode {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)) :
    CvP E n Γ (.pi T (lift 0 1 T)) (.pi T (lift 0 1 T)) (.sort (.imax u v)) :=
  let Dpi := TyP.pi E n Γ T u (lift 0 1 T) v D₁ (wkAtZero (A := T) D₂)
  CvP.refl E n Γ (.pi T (lift 0 1 T)) (.sort (.imax u v)) Dpi Dpi Dpi

/-- `SortCoh σ D₁ D₂` (`eqN (σ u) (σ v)`) from `Below` on `sortPairNode D₁ D₂`. -/
theorem sortCoh_of_below_pair (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (sortPairNode D₁ D₂))) :
    SortCoh σ D₁ D₂ := by
  let hnode := sortPairNode D₁ D₂
  have ht : hnode.isTransport = false := rfl
  have h1 : D₁.wt Aw < hnode.wt Aw := by
    simp only [hnode, sortPairNode, wkAtZero, CvP.wt, TyP.wt]
    omega
  have h2 : D₂.wt Aw < hnode.wt Aw := by
    simp only [hnode, sortPairNode, wkAtZero, CvP.wt, TyP.wt]
    omega
  exact const_reg_levels Aw tbl hnode ht Bel hW D₁ D₂ σ ρ hρ h1 h2

/-- `SortUnique` on `TyP` from `Below` (`σ = id`): `D₁ : TyP E n Γ T (.sort u)` and
    `D₂ : TyP E n Γ T (.sort v)` yield `eqN u v`. -/
theorem sortUnique_of_tyP_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (sortPairNode D₁ D₂))) :
    eqN u v :=
  sortCoh_of_below_pair Aw hW D₁ D₂ id ρ hρ Bel

/-- Closed-context corollary of `sortUnique_of_tyP_below` in `Γ = []` at `ρ = []`. -/
theorem sortUnique_of_tyP_below_nil (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n [] T (.sort u)) (D₂ : TyP E n [] T (.sort v))
    (Bel : Below Aw tbl (cvMeas Aw (sortPairNode D₁ D₂))) :
    eqN u v :=
  sortUnique_of_tyP_below Aw hW D₁ D₂ [] (.nil levelSub_id) Bel

/-- Non-vacuity of `SortUnique` on `TyP`: no type `T` can simultaneously have sort `.zero`
    and sort `.succ l` under `SortCoh id`. -/
theorem not_tyP_sort_zero_succ_of_sortCoh
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {l : Level}
    (D₁ : TyP E n Γ T (.sort .zero)) (D₂ : TyP E n Γ T (.sort (.succ l)))
    (hcoh : SortCoh id D₁ D₂) :
    False :=
  not_eqN_zero_succ l hcoh

/-- Non-vacuity of `SortUnique` on `TyP` under `Below`: no type `T` can simultaneously have
    sort `.zero` and sort `.succ l`. -/
theorem not_tyP_sort_zero_succ_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {l : Level}
    (D₁ : TyP E n Γ T (.sort .zero)) (D₂ : TyP E n Γ T (.sort (.succ l)))
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (sortPairNode D₁ D₂))) :
    False :=
  not_eqN_zero_succ l (sortUnique_of_tyP_below Aw hW D₁ D₂ ρ hρ Bel)

/-- Plain `HasTyT` `SortUnique` bridge via `enrichHasTyT` and `SortCoh id`. -/
theorem sortUnique_of_hasTyT_sortCoh
    {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {Γ : LCtx} (C : CtxP E n Γ) {T : Expr Nat} {u v : Level}
    (h₁ : HasTyT E₁ n Γ T (.sort u)) (h₂ : HasTyT E₁ n Γ T (.sort v))
    (hcoh : SortCoh id
      (enrichHasTyT hcl hext hm hlet C h₁)
      (enrichHasTyT hcl hext hm hlet C h₂)) :
    eqN u v :=
  hcoh

/-- Plain `HasTyT` `SortUnique` bridge via `enrichHasTyT` and `EUT` + `CL`. -/
theorem sortUnique_of_hasTyT_eut_cl {tbl : List CRule} (hW : TableWF tbl)
    {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {Γ : LCtx} (C : CtxP E n Γ) {T : Expr Nat} {u v : Level}
    (h₁ : HasTyT E₁ n Γ T (.sort u)) (h₂ : HasTyT E₁ n Γ T (.sort v))
    (ρ : List Disp)
    (heut : EUT tbl id ρ
      (enrichHasTyT hcl hext hm hlet C h₁)
      (enrichHasTyT hcl hext hm hlet C h₂))
    (hL : CL tbl id ρ
      (enrichHasTyT hcl hext hm hlet C h₁).reg.2
      (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl id ρ
      (enrichHasTyT hcl hext hm hlet C h₂).reg.2
      (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  sortUnique_of_tyP_eut_cl hW
    (enrichHasTyT hcl hext hm hlet C h₁)
    (enrichHasTyT hcl hext hm hlet C h₂)
    ρ heut hL hR

/-- `EnvWfT`-fronted `SortUnique` (`cc` 01:30Z + 08:55Z requests):
    `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ T (.sort u) → HasTyT E n Γ T (.sort v) →
    SortCoh id (enrichHasTyT_of_envWfT hEnv hΓ h₁) (enrichHasTyT_of_envWfT hEnv hΓ h₂) → eqN u v`.
    The `hcoh` premise is the remaining discharge (unconditional `AllBelow`, codex-4c
    #7140); the body is exactly `hcoh`. -/
theorem sortUnique_of_hasTyT_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {u v : Level}
    (h₁ : HasTyT E n Γ T (.sort u)) (h₂ : HasTyT E n Γ T (.sort v))
    (hcoh : SortCoh id
      (enrichHasTyT_of_envWfT hEnv hΓ h₁)
      (enrichHasTyT_of_envWfT hEnv hΓ h₂)) :
    eqN u v :=
  hcoh

/-- `EnvWfT`-fronted `SortUnique` from `Below` at the canonical context disposition
    `ρ = (enrichCtxWfT_of_envWfT hEnv hΓ).disp id` (`dispFor_ctxP_id`). -/
theorem sortUnique_of_hasTyT_envWfT_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T : Expr Nat} {u v : Level}
    (h₁ : HasTyT E n Γ T (.sort u)) (h₂ : HasTyT E n Γ T (.sort v))
    (Bel : Below Aw tbl (cvMeas Aw
      (sortPairNode
        (enrichHasTyT_of_envWfT hEnv hΓ h₁)
        (enrichHasTyT_of_envWfT hEnv hΓ h₂)))) :
    eqN u v :=
  sortUnique_of_tyP_below Aw hW
    (enrichHasTyT_of_envWfT hEnv hΓ h₁)
    (enrichHasTyT_of_envWfT hEnv hΓ h₂)
    ((enrichCtxWfT_of_envWfT hEnv hΓ).disp id)
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    Bel

/-! ## §2 Heterogeneous `TyCvP` Sort-Agreement (`TyCvP.endpoints`, `TyCvP.SortCoh`, `eqN_of_tyCvP_sortChainCoh`) -/

/-- Extracts either `A = B` (when `c` consists solely of `.refl` steps) or the outermost
    left and right endpoint sort typings `(uL, uR, dL, dR)` from the `.of` steps of
    `c : TyCvP E n Γ A B`, requiring **zero** external middle typings at `.trans`. -/
def TyCvP.endpoints {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B : Expr Nat} → TyCvP E n Γ A B →
    PSum (A = B) ((uL : Level) × (uR : Level) × TyP E n Γ A (.sort uL) × TyP E n Γ B (.sort uR))
  | _, _, .refl _ _ => .inl rfl
  | _, _, .of _ _ _ u h => .inr ⟨u, u, h.dl, h.dr⟩
  | _, _, .trans _ _ _ _ c₁ c₂ =>
      match c₁.endpoints, c₂.endpoints with
      | .inl h₁, .inl h₂ => .inl (h₁.trans h₂)
      | .inl h₁, .inr ⟨uL, uR, dL, dR⟩ => .inr ⟨uL, uR, h₁ ▸ dL, dR⟩
      | .inr ⟨uL, uR, dL, dR⟩, .inl h₂ => .inr ⟨uL, uR, dL, h₂ ▸ dR⟩
      | .inr ⟨uL₁, _, dL₁, _⟩, .inr ⟨_, uR₂, _, dR₂⟩ => .inr ⟨uL₁, uR₂, dL₁, dR₂⟩

/-- Internal junction `SortCoh` predicate on a heterogeneous `TyCvP` chain `c`:
    - `.refl` and `.of` require `True` (every `.of` step already shares a single sort `u`
      between `h.dl` and `h.dr`);
    - `.trans c₁ c₂` requires `SortCoh σ dR₁ dL₂` at the shared middle type `B` when both
      `c₁` and `c₂` contain `.of` steps. -/
def TyCvP.SortCoh (σ : Level → Level) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B : Expr Nat} → TyCvP E n Γ A B → Prop
  | _, _, .refl _ _ => True
  | _, _, .of _ _ _ _ _ => True
  | _, _, .trans _ _ _ _ c₁ c₂ =>
      c₁.SortCoh σ ∧ c₂.SortCoh σ ∧
      match c₁.endpoints, c₂.endpoints with
      | .inr ⟨_, _, _, dR₁⟩, .inr ⟨_, _, dL₂, _⟩ => Rcic.Syn.SortCoh σ dR₁ dL₂
      | _, _ => True

/-- For any `c : TyCvP E n Γ A B` satisfying `c.SortCoh σ`, if `c.endpoints = .inr ⟨uL, uR, dL, dR⟩`,
    then `eqN (σ uL) (σ uR)` holds. -/
theorem eqN_of_tyCvP_endpoints {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {A B : Expr Nat} (c : TyCvP E n Γ A B),
      c.SortCoh σ →
      ∀ {uL uR : Level} {dL : TyP E n Γ A (.sort uL)} {dR : TyP E n Γ B (.sort uR)},
        c.endpoints = .inr ⟨uL, uR, dL, dR⟩ →
        eqN (σ uL) (σ uR)
  | _, _, .refl _ _, _, _, _, _, _, he => PSum.noConfusion he
  | _, _, .of _ _ _ u _, _, _, _, _, _, he => by
      injection he with hsig
      cases hsig
      exact eqN_refl (σ u)
  | _, _, .trans _ _ _ _ c₁ c₂, hcoh, _, _, _, _, he => by
      rcases hcoh with ⟨hc₁, hc₂, hmid⟩
      unfold TyCvP.endpoints at he
      revert hmid he
      cases he₁ : c₁.endpoints with
      | inl h₁ =>
          cases he₂ : c₂.endpoints with
          | inl h₂ =>
              intro _ he
              exact PSum.noConfusion he
          | inr p₂ =>
              rcases p₂ with ⟨uL₂, uR₂, dL₂, dR₂⟩
              intro _ he
              injection he with hsig
              cases hsig
              exact eqN_of_tyCvP_endpoints c₂ hc₂ he₂
      | inr p₁ =>
          rcases p₁ with ⟨uL₁, uR₁, dL₁, dR₁⟩
          cases he₂ : c₂.endpoints with
          | inl h₂ =>
              intro _ he
              injection he with hsig
              cases hsig
              exact eqN_of_tyCvP_endpoints c₁ hc₁ he₁
          | inr p₂ =>
              rcases p₂ with ⟨uL₂, uR₂, dL₂, dR₂⟩
              intro hmid he
              injection he with hsig
              cases hsig
              have h1 := eqN_of_tyCvP_endpoints c₁ hc₁ he₁
              have h2 := eqN_of_tyCvP_endpoints c₂ hc₂ he₂
              exact eqN_trans h1 (eqN_trans hmid h2)

/-- Full `SortCoh` obligation for a heterogeneous `TyCvP` chain `c : TyCvP E n Γ A B`
    between endpoint sort typings `dA : TyP E n Γ A (.sort u)` and `dB : TyP E n Γ B (.sort v)`. -/
def TyCvP.SortChainCoh (σ : Level → Level)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (c : TyCvP E n Γ A B)
    (dA : TyP E n Γ A (.sort u)) (dB : TyP E n Γ B (.sort v)) : Prop :=
  c.SortCoh σ ∧
  match c.endpoints with
  | .inl h => Rcic.Syn.SortCoh σ (h ▸ dA) dB
  | .inr ⟨_, _, dL, dR⟩ => Rcic.Syn.SortCoh σ dA dL ∧ Rcic.Syn.SortCoh σ dR dB

/-- Every `TyCvP.SortChainCoh σ c dA dB` yields `eqN (σ u) (σ v)`. -/
theorem eqN_of_tyCvP_sortChainCoh {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    {c : TyCvP E n Γ A B}
    {dA : TyP E n Γ A (.sort u)} {dB : TyP E n Γ B (.sort v)}
    (hc : c.SortChainCoh σ dA dB) :
    eqN (σ u) (σ v) := by
  rcases hc with ⟨hc_int, hc_bd⟩
  revert hc_bd
  cases he : c.endpoints with
  | inl h =>
      cases h
      intro hcoh
      exact hcoh
  | inr p =>
      rcases p with ⟨uL, uR, dL, dR⟩
      intro ⟨hL, hR⟩
      have hmid := eqN_of_tyCvP_endpoints c hc_int he
      exact eqN_trans hL (eqN_trans hmid hR)

/-- At `σ = id`, `eqN_of_tyCvP_sortChainCoh` yields `eqN u v`. -/
theorem eqN_of_tyCvP_sortChainCoh_id
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    {c : TyCvP E n Γ A B}
    {dA : TyP E n Γ A (.sort u)} {dB : TyP E n Γ B (.sort v)}
    (hc : c.SortChainCoh id dA dB) :
    eqN u v :=
  eqN_of_tyCvP_sortChainCoh hc

/-! ## §3 The Prop/Sort Separation Contract (`cc` 13:40Z + 08:55Z requests) -/

/-- Enriched Prop/Sort Separation Contract on `TyCvP`:
    given `dP : TyP E n Γ P (.sort .zero)` and `c : TyCvP E n Γ (.sort l) P` satisfying
    `c.SortChainCoh id (TyP.sort E n Γ l (.succ l) (eqN_refl _)) dP`, `False` follows from
    `eqN (.succ l) .zero` (`not_eqN_zero_succ l`). -/
theorem not_tyCvP_sort_prop_of_sortChainCoh
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat} {l : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (c : TyCvP E n Γ (.sort l) P)
    (hc : c.SortChainCoh id (TyP.sort E n Γ l (.succ l) (eqN_refl _)) dP) :
    False :=
  not_eqN_zero_succ l (eqN_symm (eqN_of_tyCvP_sortChainCoh_id hc))

/-- Symmetric enriched Prop/Sort Separation Contract on `TyCvP` (`TyCvP E n Γ P (.sort l) → False`). -/
theorem not_tyCvP_prop_sort_of_sortChainCoh
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat} {l : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (c : TyCvP E n Γ P (.sort l))
    (hc : c.SortChainCoh id dP (TyP.sort E n Γ l (.succ l) (eqN_refl _))) :
    False :=
  not_eqN_zero_succ l (eqN_of_tyCvP_sortChainCoh_id hc)

/-- Single-step `CvP` Prop/Sort Separation from `SortCoh id`:
    no `h : CvP E n Γ (.sort l) P (.sort w)` can coexist with `dP : TyP E n Γ P (.sort .zero)`. -/
theorem not_cvp_sort_prop_of_sortCoh
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat} {l w : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (h : CvP E n Γ (.sort l) P (.sort w))
    (hL : SortCoh id (TyP.sort E n Γ l (.succ l) (eqN_refl _)) h.dl)
    (hR : SortCoh id h.dr dP) :
    False :=
  not_tyCvP_sort_prop_of_sortChainCoh dP (.of Γ (.sort l) P w h) ⟨trivial, hL, hR⟩

/-- Symmetric single-step `CvP` Prop/Sort Separation from `SortCoh id`. -/
theorem not_cvp_prop_sort_of_sortCoh
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat} {l w : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (h : CvP E n Γ P (.sort l) (.sort w))
    (hL : SortCoh id dP h.dl)
    (hR : SortCoh id h.dr (TyP.sort E n Γ l (.succ l) (eqN_refl _))) :
    False :=
  not_tyCvP_prop_sort_of_sortChainCoh dP (.of Γ P (.sort l) w h) ⟨trivial, hL, hR⟩

/-- Single-step `CvP` Prop/Sort Separation from `Below` on the endpoint `sortPairNode` pairs. -/
theorem not_cvp_sort_prop_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat} {l w : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (h : CvP E n Γ (.sort l) P (.sort w))
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (BelL : Below Aw tbl
      (cvMeas Aw (sortPairNode (TyP.sort E n Γ l (.succ l) (eqN_refl _)) h.dl)))
    (BelR : Below Aw tbl (cvMeas Aw (sortPairNode h.dr dP))) :
    False :=
  not_cvp_sort_prop_of_sortCoh dP h
    (sortUnique_of_tyP_below Aw hW (TyP.sort E n Γ l (.succ l) (eqN_refl _)) h.dl ρ hρ BelL)
    (sortUnique_of_tyP_below Aw hW h.dr dP ρ hρ BelR)

/-- Symmetric single-step `CvP` Prop/Sort Separation from `Below`. -/
theorem not_cvp_prop_sort_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat} {l w : Level}
    (dP : TyP E n Γ P (.sort .zero))
    (h : CvP E n Γ P (.sort l) (.sort w))
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (BelL : Below Aw tbl (cvMeas Aw (sortPairNode dP h.dl)))
    (BelR : Below Aw tbl
      (cvMeas Aw (sortPairNode h.dr (TyP.sort E n Γ l (.succ l) (eqN_refl _))))) :
    False :=
  not_cvp_prop_sort_of_sortCoh dP h
    (sortUnique_of_tyP_below Aw hW dP h.dl ρ hρ BelL)
    (sortUnique_of_tyP_below Aw hW h.dr (TyP.sort E n Γ l (.succ l) (eqN_refl _)) ρ hρ BelR)

/-- Plain `HasTyT` / `TyConvT` Separation Contract bridge via `enrichHasTyT` and `enrichTyConvT`. -/
theorem sepContract_of_tyConvT
    {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {Γ : LCtx} (C : CtxP E n Γ) {P : Expr Nat} {l : Level}
    (hP : HasTyT E₁ n Γ P (.sort .zero))
    (hc : TyConvT E₁ n Γ (.sort l) P)
    (hchain : (enrichTyConvT hcl hext hm hlet C hc).SortChainCoh id
      (TyP.sort E n Γ l (.succ l) (eqN_refl _))
      (enrichHasTyT hcl hext hm hlet C hP)) :
    False :=
  not_tyCvP_sort_prop_of_sortChainCoh
    (enrichHasTyT hcl hext hm hlet C hP)
    (enrichTyConvT hcl hext hm hlet C hc)
    hchain

/-- `EnvWfT`-fronted Prop/Sort SEPARATION CONTRACT (`cc` 13:40Z + 08:55Z requests):
    `EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P →
    (enrichTyConvT_of_envWfT hEnv hΓ hc).SortChainCoh id (TyP.sort E n Γ l (.succ l) (eqN_refl _))
      (enrichHasTyT_of_envWfT hEnv hΓ hP) → False`.
    The `hchain` premise is sort-agreement along the enriched chain's junctions. -/
theorem sepContract_of_tyConvT_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hc : TyConvT E n Γ (.sort l) P)
    (hchain : (enrichTyConvT_of_envWfT hEnv hΓ hc).SortChainCoh id
      (TyP.sort E n Γ l (.succ l) (eqN_refl _))
      (enrichHasTyT_of_envWfT hEnv hΓ hP)) :
    False :=
  not_tyCvP_sort_prop_of_sortChainCoh
    (enrichHasTyT_of_envWfT hEnv hΓ hP)
    (enrichTyConvT_of_envWfT hEnv hΓ hc)
    hchain

/-- Symmetric `EnvWfT`-fronted Prop/Sort Separation Contract (`TyConvT E n Γ P (.sort l) → False`). -/
theorem sepContract_symm_of_tyConvT_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hc : TyConvT E n Γ P (.sort l))
    (hchain : (enrichTyConvT_of_envWfT hEnv hΓ hc).SortChainCoh id
      (enrichHasTyT_of_envWfT hEnv hΓ hP)
      (TyP.sort E n Γ l (.succ l) (eqN_refl _))) :
    False :=
  not_tyCvP_prop_sort_of_sortChainCoh
    (enrichHasTyT_of_envWfT hEnv hΓ hP)
    (enrichTyConvT_of_envWfT hEnv hΓ hc)
    hchain

/-- Single-step plain `ConvT` Prop/Sort Separation Contract under `EnvWfT` and `CtxWfT`. -/
theorem sepContract_of_convT_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l w : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (h : ConvT E n Γ (.sort l) P (.sort w))
    (hL : SortCoh id
      (TyP.sort E n Γ l (.succ l) (eqN_refl _))
      (enrichConvT_of_envWfT hEnv hΓ h).dl)
    (hR : SortCoh id
      (enrichConvT_of_envWfT hEnv hΓ h).dr
      (enrichHasTyT_of_envWfT hEnv hΓ hP)) :
    False :=
  not_cvp_sort_prop_of_sortCoh
    (enrichHasTyT_of_envWfT hEnv hΓ hP)
    (enrichConvT_of_envWfT hEnv hΓ h)
    hL hR

/-- Single-step plain `ConvT` Prop/Sort Separation Contract under `EnvWfT`, `CtxWfT`, and `Below`
    at the canonical context disposition `ρ = (enrichCtxWfT_of_envWfT hEnv hΓ).disp id`. -/
theorem sepContract_of_convT_envWfT_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P : Expr Nat} {l w : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (h : ConvT E n Γ (.sort l) P (.sort w))
    (BelL : Below Aw tbl
      (cvMeas Aw (sortPairNode
        (TyP.sort E n Γ l (.succ l) (eqN_refl _))
        (enrichConvT_of_envWfT hEnv hΓ h).dl)))
    (BelR : Below Aw tbl
      (cvMeas Aw (sortPairNode
        (enrichConvT_of_envWfT hEnv hΓ h).dr
        (enrichHasTyT_of_envWfT hEnv hΓ hP)))) :
    False :=
  not_cvp_sort_prop_of_below Aw hW
    (enrichHasTyT_of_envWfT hEnv hΓ hP)
    (enrichConvT_of_envWfT hEnv hΓ h)
    ((enrichCtxWfT_of_envWfT hEnv hΓ).disp id)
    (dispFor_ctxP_id (enrichCtxWfT_of_envWfT hEnv hΓ))
    BelL BelR

/-! ## §4 Why `CtxWfT E n Γ` is required by `O6` (`cc` 08:55Z note on `SepAll` at ill-formed `Γ`):
    Sealed Refutations of `HasTyT` Regularity and `ConvT` Endpoint Typing without `CtxWfT` -/

/-- Ill-formed context `[x₀ : x₁]` (`x₁` is dangling out of bounds), violating `CtxWfT`. -/
def illCtxReg : LCtx := [.assumption (.bvar 0)]

/-- In `illCtxReg`, `.bvar 0` has type `.bvar 1` by `HasTyT.bvar` at index `0`. -/
def hasTyT_illCtxReg_bvar0 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n illCtxReg (.bvar 0) (.bvar 1) :=
  .bvar illCtxReg 0 (.bvar 1) rfl

/-- In `illCtxReg`, `.bvar 1` has no `HasTyT` typing at any `S` (`lookupType illCtxReg 1 = none`). -/
theorem not_hasTyT_illCtxReg_bvar1 (E : ResolvedEnv) (n : Nat) :
    ∀ {e S : Expr Nat}, HasTyT E n illCtxReg e S → e = .bvar 1 → False
  | _, _, .sort .., he => Expr.noConfusion he
  | _, _, .bvar _ i _ hlook, he => by
      injection he with hi
      subst hi
      exact Option.noConfusion hlook
  | _, _, .const .., he => Expr.noConfusion he
  | _, _, .pi .., he => Expr.noConfusion he
  | _, _, .lam .., he => Expr.noConfusion he
  | _, _, .app .., he => Expr.noConfusion he
  | _, _, .letE .., he => Expr.noConfusion he
  | _, _, .lit .., he => Expr.noConfusion he
  | _, _, .conv _ _ _ _ _ h _, he => not_hasTyT_illCtxReg_bvar1 E n h he

/-- **Sealed Refutation 1 (`cc` 08:55Z note)**: Without `CtxWfT E n Γ`, `HasTyT` regularity
    (`TyP.reg` in `O6`, `DT008T_regularity`) is **false** at every `(E, n)`:
    `HasTyT E n illCtxReg (.bvar 0) (.bvar 1)` holds, while `.bvar 1` has no sort typing. -/
theorem not_hasTyT_regularity_illCtx (E : ResolvedEnv) (n : Nat) :
    ¬ (∀ (Γ : LCtx) (e T : Expr Nat),
        Nonempty (HasTyT E n Γ e T) → ∃ u : Level, Nonempty (HasTyT E n Γ T (.sort u))) := by
  intro hreg
  obtain ⟨u, ⟨hT⟩⟩ := hreg illCtxReg (.bvar 0) (.bvar 1) ⟨hasTyT_illCtxReg_bvar0 E n⟩
  exact not_hasTyT_illCtxReg_bvar1 E n hT rfl

/-- Ill-formed context `[f : Π (_ : x₁), Prop]` (`x₁` is dangling out of bounds), violating `CtxWfT`. -/
def illCtxEta : LCtx := [.assumption (.pi (.bvar 0) (.sort .zero))]

/-- In `illCtxEta`, `.bvar 0` has type `.pi (.bvar 1) (.sort .zero)` by `HasTyT.bvar` at index `0`. -/
def hasTyT_illCtxEta_bvar0 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n illCtxEta (.bvar 0) (.pi (.bvar 1) (.sort .zero)) :=
  .bvar illCtxEta 0 (.pi (.bvar 1) (.sort .zero)) rfl

/-- In `illCtxEta`, `ConvT.eta` derives `(λ x : x₁, f x) ≡ f : Π (_ : x₁), Prop`. -/
def convT_illCtxEta_eta (E : ResolvedEnv) (n : Nat) :
    ConvT E n illCtxEta
      (.lam (.bvar 1) (.app (.bvar 1) (.bvar 0)))
      (.bvar 0)
      (.pi (.bvar 1) (.sort .zero)) :=
  .eta illCtxEta (.bvar 0) (.bvar 1) (.sort .zero) (hasTyT_illCtxEta_bvar0 E n)

/-- In `illCtxEta`, `.bvar 1` has no `HasTyT` typing at any `S` (`lookupType illCtxEta 1 = none`). -/
theorem not_hasTyT_illCtxEta_bvar1 (E : ResolvedEnv) (n : Nat) :
    ∀ {e S : Expr Nat}, HasTyT E n illCtxEta e S → e = .bvar 1 → False
  | _, _, .sort .., he => Expr.noConfusion he
  | _, _, .bvar _ i _ hlook, he => by
      injection he with hi
      subst hi
      exact Option.noConfusion hlook
  | _, _, .const .., he => Expr.noConfusion he
  | _, _, .pi .., he => Expr.noConfusion he
  | _, _, .lam .., he => Expr.noConfusion he
  | _, _, .app .., he => Expr.noConfusion he
  | _, _, .letE .., he => Expr.noConfusion he
  | _, _, .lit .., he => Expr.noConfusion he
  | _, _, .conv _ _ _ _ _ h _, he => not_hasTyT_illCtxEta_bvar1 E n h he

/-- In `illCtxEta`, the left-hand side `.lam (.bvar 1) (.app (.bvar 1) (.bvar 0))` of
    `convT_illCtxEta_eta` has no `HasTyT` typing at any `S`, because `HasTyT.lam` requires
    `hA : HasTyT E n illCtxEta (.bvar 1) (.sort u)`. -/
theorem not_hasTyT_illCtxEta_lam (E : ResolvedEnv) (n : Nat) :
    ∀ {e S : Expr Nat},
      HasTyT E n illCtxEta e S →
      e = .lam (.bvar 1) (.app (.bvar 1) (.bvar 0)) →
      False
  | _, _, .sort .., he => Expr.noConfusion he
  | _, _, .bvar .., he => Expr.noConfusion he
  | _, _, .const .., he => Expr.noConfusion he
  | _, _, .pi .., he => Expr.noConfusion he
  | _, _, .lam _ _ _ _ _ hA _, he => by
      injection he with hdom _
      exact not_hasTyT_illCtxEta_bvar1 E n hA hdom
  | _, _, .app .., he => Expr.noConfusion he
  | _, _, .letE .., he => Expr.noConfusion he
  | _, _, .lit .., he => Expr.noConfusion he
  | _, _, .conv _ _ _ _ _ h _, he => not_hasTyT_illCtxEta_lam E n h he

/-- **Sealed Refutation 2 (`cc` 08:55Z note)**: Without `CtxWfT E n Γ`, `ConvT` left-endpoint
    well-typedness (`CvP.dl` and `etaLeftP` in `O6`, `DT009T_endpoints`) is **false** at
    every `(E, n)`: `ConvT.eta` produces a valid `ConvT` derivation in `illCtxEta` whose
    left endpoint `.lam (.bvar 1) (.app (.bvar 1) (.bvar 0))` is completely untypable. -/
theorem not_convT_lhs_typed_illCtx (E : ResolvedEnv) (n : Nat) :
    ¬ (∀ (Γ : LCtx) (a b T : Expr Nat),
        Nonempty (ConvT E n Γ a b T) → Nonempty (HasTyT E n Γ a T)) := by
  intro hend
  obtain ⟨hL⟩ := hend illCtxEta
    (.lam (.bvar 1) (.app (.bvar 1) (.bvar 0)))
    (.bvar 0)
    (.pi (.bvar 1) (.sort .zero))
    ⟨convT_illCtxEta_eta E n⟩
  exact not_hasTyT_illCtxEta_lam E n hL rfl

end Rcic.Syn
