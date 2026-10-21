import rcic.RcicSynCLFromBelow
import rcic.RcicSynLetInline
import rcic.RcicSynCtsLocal

/-!
# Syntactic sortRow, build step 10 — `EUT` pair dispatch over local call interfaces

`research/rcic/sortrow/S10_EUT_PAIR_DISPATCH.md` (S10, ChatGPT, PR #7352) §3–5.
The `.eut` case of the sortRow induction is dispatched over the two root pairs'
typing-rule heads. This module turns the composable rows into *conditional*
lemmas: each takes exactly the strict sub-rank requests it needs as named
interfaces, never a rebuilt unconditional `Below`.

1. **§1 The four local bounded call interfaces** (`CLBelowHere`, `EUTBelowHere`,
   `ESBelowHere`, `BITBelowHere`): `CL` / `EUT` / `ES` / `BitCoh` at every
   same-scope derivation (pair) strictly `LexDM`-below `bound`, gated on
   `AssumpPref`. `CLBelowHere`/`EUTBelowHere`/`sortNode` are the S9
   interfaces of `RcicSynCtsLocal` (#7347, landed) — imported, not
   re-declared here. The `AssumpPref` premises are
   not consulted by the `Below` projections (`*_of_below`), so every existing
   supplier already implements these interfaces.

2. **§2 `conv` on either side** (`eut_conv_left_of_local_calls`,
   `eut_conv_right_of_local_calls`): three strict requests in the fixed
   direction — left: `ES[c]`, `CL[c.dl, d.reg.2]`, `EUT[d, D₂]`, closing by
   `eut_conv_left`; right: `EUT[D₁, d]`, `CL[d.reg.2, c.dl]`, `ES[c]`, closing
   by `eut_conv_right`. The `CvP` is paid by `Dᵢ`'s own atom
   (`cvp_atoms_lt_of_wt_lt`), the pair edges by `lexDM_both_wt_lt_*` and a plain
   append over the untouched other side.

3. **§3 The zero- and one-request rows**: `eut_sort_sort_of_local_calls` (no
   recursive request — `DispFor` gives `LevelSub` and `eut_sort_nodes` closes),
   `eut_bvar_bvar_of_local_calls` (`CL[hA₁, hA₂]`, both real lookups at one
   index force `A₁ = A₂`), `eut_lit_lit_of_local_calls` (`EUT` of the original
   expansion pair).

4. **§4 `pi/pi`**: `sortCoh_of_local_calls` is the named in-case composition the
   S10 §4 table prescribes — the strictly smaller pair's `EUT` request plus the
   two reg-`CL` requests against `sortNode`, *with the `isSortOrPiHead` head
   closing for free* (the reg-`CL` edges are passed as conditional functions of
   the false hypothesis, so a sort/Π head issues no request at all).
   `eut_pi_pi_of_local_calls` runs it on the domain pair at `(Γ, ρ)` and on the
   codomain pair at the real binder view `(Γ⁺, ρ⁺)`, then closes with
   `hσ.imax_eqN` and `eut_pi_nodes` — the full `SortCoh`, never just bit
   equality, and never the current Π pair's own `EUT`.

5. **§5 `lam/lam` with different codomains**
   (`eut_lam_lam_of_local_calls`): exactly the five S10 §5.1 requests —
   `BIT[hA₁, hA₂]`, `CL[hA₁, hA₂]` at `(Γ, ρ)` and `CL[hB₁, hb₁.reg.2]`,
   `EUT[hb₁, hb₂]`, `CL[hb₂.reg.2, hB₂]` at `(Γ⁺, ρ⁺)` — composed as
   `hLeft.trans (hBodyEUT.trans hRight)` into `eut_lam_nodes`. `B₁ ≠ B₂` needs
   nothing extra; the current λ's `TagCoh` is never requested (§7 control).

6. **§6 `letE/letE` via the real `letSub`**
   (`eut_letE_letE_of_local_calls`): `Lᵢ := letSub hbᵢ hvᵢ hAᵢ` is the actual
   lazy let substitution in the *same* `Γ`; `Lᵢ.wt < Dᵢ.wt` because `Dᵢ` carries
   its own `hTᵢ` atom. Requests: `CL[hT₁, L₁.reg.2]`, `EUT[L₁, L₂]`,
   `CL[L₂.reg.2, hT₂]`, composed by trans into `eut_letE_nodes`.

7. **§7 Controls**:
   - `LinstSameView` / `EsubSameView` name the same-view premise the
     same-transport adapters consume (same source context, subject, and actual
     parameters); `linst_sameTag_diff_source_refused` and
     `esub_sameTag_diff_source_refused` refuse it when the sources differ —
     equal tags are never enough.
   - `eut_lam_sameRank_no_self_call`: a current-pair `TagCoh`-style request on
     the λ/λ pair would carry the identical `tyPairMeas` rank; `LexDM` is
     irreflexive, so no such IH edge exists.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Local bounded call interfaces -/

/-- Local projection of the pack IH for `ES`: every same-scope conversion
    `h : CvP E n Γ a b T` with `AssumpPref` at a strictly smaller `cvMeas`
    yields `ES tbl σ ρ h`. -/
def ESBelowHere (Aw : Nat → Nat) (tbl : List CRule) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (σ : Level → Level) (ρ : List Disp) (bound : List Nat × Nat) : Prop :=
  ∀ {a b T : Expr Nat} (h : CvP E n Γ a b T),
    h.AssumpPref → LexDM (cvMeas Aw h) bound → ES tbl σ ρ h

/-- Local projection of the pack IH for `BitCoh`: every same-scope sort-typing
    pair `D₁ D₂ : TyP E n Γ T (.sort _)`, both `AssumpPref`, at a strictly
    smaller `tyPairMeas`, yields `BitCoh σ D₁ D₂`. -/
def BITBelowHere (Aw : Nat → Nat) (tbl : List CRule) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (σ : Level → Level) (ρ : List Disp) (bound : List Nat × Nat) : Prop :=
  ∀ {T : Expr Nat} {u v : Level} (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)),
    D₁.AssumpPref → D₂.AssumpPref → LexDM (tyPairMeas Aw D₁ D₂) bound → BitCoh σ D₁ D₂

/-- Any `Below Aw tbl bound` supplier implements `ESBelowHere` at a
    `DispFor`-reachable `ρ`. -/
theorem esBelowHere_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {bound : List Nat × Nat} (hρ : DispFor σ E n Γ ρ) (Bel : Below Aw tbl bound) :
    ESBelowHere Aw tbl E n Γ σ ρ bound :=
  fun h _ hlex => Bel.es h σ ρ hρ hlex

/-- Any `Below Aw tbl bound` supplier implements `BITBelowHere` at a
    `DispFor`-reachable `ρ`. -/
theorem bitBelowHere_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {bound : List Nat × Nat} (hρ : DispFor σ E n Γ ρ) (Bel : Below Aw tbl bound) :
    BITBelowHere Aw tbl E n Γ σ ρ bound :=
  fun D₁ D₂ _ _ hlex => Bel.bitCoh D₁ D₂ σ ρ hρ hlex

/-! ## §2 `conv` on either side (S10 §3) -/

/-- `EUT` on `TyP.conv` on the left against any `D₂`, from three strict local
    requests: `ES[hc]` (paid by the conv node's own atom),
    `CL[hc.dl, h.reg.2]` (both strictly lighter than `D₁`), and
    `EUT[h, D₂]` (`h` replaces `D₁`). Composed by `eut_conv_left`. -/
theorem eut_conv_left_of_local_calls (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B T₂ : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (hh : h.AssumpPref) (hhc : hc.AssumpPref) (hD₂ : D₂.AssumpPref)
    (σ : Level → Level) (ρ : List Disp)
    (esBelow : ESBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂))
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂))
    (eutBelow : EUTBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂)) :
    EUT tbl σ ρ (TyP.conv E n Γ e A B u h hc) D₂ := by
  let D₁ := TyP.conv E n Γ e A B u h hc
  have hwh : h.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwc : hc.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwdl : hc.dl.wt Aw < D₁.wt Aw :=
    Nat.lt_of_lt_of_le (CvP.wt_dl_lt Aw hc) (Nat.le_of_lt hwc)
  have hwreg : h.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw h) hwh
  have hstep_c : DMStep (hc.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) := by
    refine dmStep_drop_right ?_ (D₂.atoms Aw)
    change DMStep (hc.atoms Aw) [D₁.wt Aw]
    rw [← List.append_nil (hc.atoms Aw)]
    exact dmStep_of_below (cvp_atoms_lt_of_wt_lt Aw hc hwc)
  have hes : ES tbl σ ρ hc := esBelow hc hhc (lex_of_dm hstep_c)
  have hcl : CL tbl σ ρ hc.dl h.reg.2 :=
    clBelow hc.dl h.reg.2 (assumpPref_dl hhc) (assumpPref_reg hh)
      (lexDM_both_wt_lt_left Aw hc.dl h.reg.2 D₁ D₂ rfl hwdl hwreg)
  have hstep_h : DMStep (h.atoms Aw ++ D₂.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
    dmStep_append_right (dmStep_wt_lt_singleton Aw h D₁ rfl hwh) (D₂.atoms Aw)
  have heut : EUT tbl σ ρ h D₂ := eutBelow h D₂ hh hD₂ (lex_of_dm hstep_h)
  exact eut_conv_left tbl σ ρ h hc D₂ hes hcl heut

/-- `EUT` on `TyP.conv` on the right against any `D₁`, the fixed direction:
    `EUT[D₁, h]`, `CL[h.reg.2, hc.dl]`, `ES[hc]` — composed by
    `eut_conv_right`. -/
theorem eut_conv_right_of_local_calls (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ A B : Expr Nat} {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (hD₁ : D₁.AssumpPref) (hh : h.AssumpPref) (hhc : hc.AssumpPref)
    (σ : Level → Level) (ρ : List Disp)
    (esBelow : ESBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc)))
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc)))
    (eutBelow : EUTBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc))) :
    EUT tbl σ ρ D₁ (TyP.conv E n Γ e A B u h hc) := by
  let D₂ := TyP.conv E n Γ e A B u h hc
  have hwh : h.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwc : hc.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwdl : hc.dl.wt Aw < D₂.wt Aw :=
    Nat.lt_of_lt_of_le (CvP.wt_dl_lt Aw hc) (Nat.le_of_lt hwc)
  have hwreg : h.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw h) hwh
  have hstep_c : DMStep (hc.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) := by
    refine dmStep_drop_left ?_ (D₁.atoms Aw)
    change DMStep (hc.atoms Aw) [D₂.wt Aw]
    rw [← List.append_nil (hc.atoms Aw)]
    exact dmStep_of_below (cvp_atoms_lt_of_wt_lt Aw hc hwc)
  have hes : ES tbl σ ρ hc := esBelow hc hhc (lex_of_dm hstep_c)
  have hcl : CL tbl σ ρ h.reg.2 hc.dl :=
    clBelow h.reg.2 hc.dl (assumpPref_reg hh) (assumpPref_dl hhc)
      (lexDM_both_wt_lt_right Aw h.reg.2 hc.dl D₁ D₂ rfl hwreg hwdl)
  have hstep_h : DMStep (D₁.atoms Aw ++ h.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
    dmStep_append_left (dmStep_wt_lt_singleton Aw h D₂ rfl hwh) (D₁.atoms Aw)
  have heut : EUT tbl σ ρ D₁ h := eutBelow D₁ h hD₁ hh (lex_of_dm hstep_h)
  exact eut_conv_right tbl σ ρ D₁ h hc heut hcl hes

/-! ## §3 The zero- and one-request rows -/

/-- `EUT` on two `TyP.sort` nodes at the same `l`: zero recursive requests —
    `DispFor` already gives the `LevelSub` that `eut_sort_nodes` consumes. -/
theorem eut_sort_sort_of_local_calls (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l))
    (hρ : DispFor σ E n Γ ρ) :
    EUT tbl σ ρ (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) :=
  eut_sort_nodes tbl hρ.levelSub ρ h₁ h₂

/-- `EUT` on two `TyP.bvar` nodes at the same `i`: both real lookups resolve to
    one `A`, and the single request is `CL[hA₁, hA₂]` paid by the two bvar
    atoms. -/
theorem eut_bvar_bvar_of_local_calls (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (hAP₁ : hA₁.AssumpPref) (hAP₂ : hA₂.AssumpPref)
    (σ : Level → Level) (ρ : List Disp)
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁)
        (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂))) :
    EUT tbl σ ρ (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁)
      (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) := by
  have hAeq : A₁ = A₂ := Option.some.inj (hlook₁.symm.trans hlook₂)
  subst hAeq
  have hw₁ : hA₁.wt Aw < (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hcl : CL tbl σ ρ hA₁ hA₂ :=
    clBelow hA₁ hA₂ hAP₁ hAP₂
      (lexDM_wt_lt_pair Aw hA₁ hA₂
        (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂)
        rfl rfl hw₁ hw₂)
  exact eut_bvar_nodes tbl σ ρ hlook₁ hA₁ hlook₂ hA₂ hcl

/-- `EUT` on two `TyP.lit` nodes: the single request is `EUT` of the original
    expansion pair, paid by the two literal atoms. -/
theorem eut_lit_lit_of_local_calls (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂)
    (hAP₁ : hexp₁.AssumpPref) (hAP₂ : hexp₂.AssumpPref)
    (σ : Level → Level) (ρ : List Disp)
    (eutBelow : EUTBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂))) :
    EUT tbl σ ρ (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) := by
  let D₁ := TyP.lit E n Γ t T₁ hexp₁
  let D₂ := TyP.lit E n Γ t T₂ hexp₂
  have hw₁ : hexp₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hw₂ : hexp₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  exact (eut_lit_nodes tbl σ ρ hexp₁ hexp₂).mpr
    (eutBelow hexp₁ hexp₂ hAP₁ hAP₂
      (lexDM_wt_lt_pair Aw hexp₁ hexp₂ D₁ D₂ rfl rfl hw₁ hw₂))

/-! ## §4 `pi/pi`: `SortCoh` composed inside the case (S10 §4) -/

/-- The named in-case composition of S10 §4: `SortCoh σ D₁ D₂` of a strictly
    smaller pair from its `EUT` result plus the two reg-`CL` requests against
    `sortNode`. The reg-`CL` edges are *conditional* on
    `isSortOrPiHead = false`: a sort/Π head closes for free by
    `cl_reg_sort_of_isSortOrPiHead` and issues no request. -/
theorem sortCoh_of_local_calls (Aw : Nat → Nat) {tbl : List CRule} (hTbl : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    {bound : List Nat × Nat}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) (σ : Level → Level) (ρ : List Disp)
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ bound)
    (heut : EUT tbl σ ρ D₁ D₂)
    (hEdgeL : D₁.isSortOrPiHead = false →
      LexDM (tyPairMeas Aw D₁.reg.2 (sortNode E n Γ u)) bound)
    (hEdgeR : D₂.isSortOrPiHead = false →
      LexDM (tyPairMeas Aw D₂.reg.2 (sortNode E n Γ v)) bound) :
    SortCoh σ D₁ D₂ := by
  have hL : CL tbl σ ρ D₁.reg.2 (sortNode E n Γ u) := by
    cases hs : D₁.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₁ hs σ ρ
    | false =>
        exact clBelow D₁.reg.2 (sortNode E n Γ u) (assumpPref_reg h₁)
          sortNode_assumpPref (hEdgeL hs)
  have hR : CL tbl σ ρ D₂.reg.2 (sortNode E n Γ v) := by
    cases hs : D₂.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₂ hs σ ρ
    | false =>
        exact clBelow D₂.reg.2 (sortNode E n Γ v) (assumpPref_reg h₂)
          sortNode_assumpPref (hEdgeR hs)
  exact sortCoh_of_eut_cl hTbl D₁ D₂ σ ρ heut hL hR

/-- `EUT` on two `TyP.pi` nodes on `(A, B)`: full `SortCoh` on the domain pair
    at `(Γ, ρ)` and on the codomain pair at the real binder view
    `(Γ⁺, ρ⁺)` — each built *inside* this case from the smaller pair's `EUT`
    request and its two reg-`CL`s — then `hσ.imax_eqN` and `eut_pi_nodes`. The
    current Π pair's `EUT` is never a premise. -/
theorem eut_pi_pi_of_local_calls (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (hAPA₁ : hA₁.AssumpPref) (hAPB₁ : hB₁.AssumpPref)
    (hAPA₂ : hA₂.AssumpPref) (hAPB₂ : hB₂.AssumpPref)
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp)
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)))
    (eutBelow : EUTBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)))
    (clBelowB : CLBelowHere Aw tbl E n (.assumption A :: Γ) σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ)
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)))
    (eutBelowB : EUTBelowHere Aw tbl E n (.assumption A :: Γ) σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ)
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂))) :
    EUT tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  let D₁ := TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁
  let D₂ := TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂
  have hwA₁ : hA₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwregA₁ : hA₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hA₁) hwA₁
  have hwregA₂ : hA₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hA₂) hwA₂
  have hwregB₁ : hB₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hB₁) hwB₁
  have hwregB₂ : hB₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hB₂) hwB₂
  have hwSN₁ : (sortNode E n Γ u₁).wt Aw < D₁.wt Aw := by
    have pA := TyP.wt_pos Aw hA₁; have pB := TyP.wt_pos Aw hB₁
    simp only [D₁, TyP.wt, sortNode]; omega
  have hwSN₂ : (sortNode E n Γ u₂).wt Aw < D₂.wt Aw := by
    have pA := TyP.wt_pos Aw hA₂; have pB := TyP.wt_pos Aw hB₂
    simp only [D₂, TyP.wt, sortNode]; omega
  have hwSNB₁ : (sortNode E n (.assumption A :: Γ) v₁).wt Aw < D₁.wt Aw := by
    have pA := TyP.wt_pos Aw hA₁; have pB := TyP.wt_pos Aw hB₁
    simp only [D₁, TyP.wt, sortNode]; omega
  have hwSNB₂ : (sortNode E n (.assumption A :: Γ) v₂).wt Aw < D₂.wt Aw := by
    have pA := TyP.wt_pos Aw hA₂; have pB := TyP.wt_pos Aw hB₂
    simp only [D₂, TyP.wt, sortNode]; omega
  have hlexA : LexDM (tyPairMeas Aw hA₁ hA₂) (tyPairMeas Aw D₁ D₂) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ D₁ D₂ rfl rfl hwA₁ hwA₂
  have hlexB : LexDM (tyPairMeas Aw hB₁ hB₂) (tyPairMeas Aw D₁ D₂) :=
    lexDM_wt_lt_pair Aw hB₁ hB₂ D₁ D₂ rfl rfl hwB₁ hwB₂
  have hcohA : SortCoh σ hA₁ hA₂ :=
    sortCoh_of_local_calls Aw hW hA₁ hA₂ hAPA₁ hAPA₂ σ ρ clBelow
      (eutBelow hA₁ hA₂ hAPA₁ hAPA₂ hlexA)
      (fun _ => lexDM_both_wt_lt_left Aw hA₁.reg.2 (sortNode E n Γ u₁) D₁ D₂ rfl
        hwregA₁ hwSN₁)
      (fun _ => lexDM_both_wt_lt_right Aw hA₂.reg.2 (sortNode E n Γ u₂) D₁ D₂ rfl
        hwregA₂ hwSN₂)
  have hcohB : SortCoh σ hB₁ hB₂ :=
    sortCoh_of_local_calls Aw hW hB₁ hB₂ hAPB₁ hAPB₂ σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ) clBelowB
      (eutBelowB hB₁ hB₂ hAPB₁ hAPB₂ hlexB)
      (fun _ => lexDM_both_wt_lt_left Aw hB₁.reg.2 (sortNode E n (.assumption A :: Γ) v₁)
        D₁ D₂ rfl hwregB₁ hwSNB₁)
      (fun _ => lexDM_both_wt_lt_right Aw hB₂.reg.2 (sortNode E n (.assumption A :: Γ) v₂)
        D₁ D₂ rfl hwregB₂ hwSNB₂)
  exact eut_pi_nodes tbl σ ρ hA₁ hB₁ hA₂ hB₂ (hσ.imax_eqN hcohA hcohB)

/-! ## §5 `lam/lam` with different codomains (S10 §5.1) -/

/-- `EUT` on any two `TyP.lam` nodes on `(A, body)` — different codomains
    `B₁, B₂` included — from exactly five strict requests: `BIT[hA₁, hA₂]` and
    `CL[hA₁, hA₂]` at `(Γ, ρ)`, then `CL[hB₁, hb₁.reg.2]`, `EUT[hb₁, hb₂]`, and
    `CL[hb₂.reg.2, hB₂]` at the real binder view `(Γ⁺, ρ⁺)`, the last three
    chaining `hB₁.eps ↔ hb₁.reg.eps ↔ hb₂.reg.eps ↔ hB₂.eps`. No `TagCoh` of the
    current λ pair is ever requested. -/
theorem eut_lam_lam_of_local_calls (Aw : Nat → Nat) (tbl : List CRule)
    (hTC : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (hAPA₁ : hA₁.AssumpPref) (hAPb₁ : hb₁.AssumpPref) (hAPB₁ : hB₁.AssumpPref)
    (hAPA₂ : hA₂.AssumpPref) (hAPb₂ : hb₂.AssumpPref) (hAPB₂ : hB₂.AssumpPref)
    (σ : Level → Level) (ρ : List Disp)
    (bitBelow : BITBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)))
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)))
    (clBelowB : CLBelowHere Aw tbl E n (.assumption A :: Γ) σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ)
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)))
    (eutBelowB : EUTBelowHere Aw tbl E n (.assumption A :: Γ) σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ)
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂))) :
    EUT tbl σ ρ (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  let D₁ := TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁
  let D₂ := TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂
  have hwA₁ : hA₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwb₁ : hb₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwb₂ : hb₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwreg₁ : hb₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb₁) hwb₁
  have hwreg₂ : hb₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb₂) hwb₂
  have hlexA := lexDM_wt_lt_pair Aw hA₁ hA₂ D₁ D₂ rfl rfl hwA₁ hwA₂
  have hlexb := lexDM_wt_lt_pair Aw hb₁ hb₂ D₁ D₂ rfl rfl hwb₁ hwb₂
  have hcl₁ : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB₁ hb₁.reg.2 :=
    clBelowB hB₁ hb₁.reg.2 hAPB₁ (assumpPref_reg hAPb₁)
      (lexDM_both_wt_lt_left Aw hB₁ hb₁.reg.2 D₁ D₂ rfl hwB₁ hwreg₁)
  have heut_b : EUT tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₁ hb₂ :=
    eutBelowB hb₁ hb₂ hAPb₁ hAPb₂ hlexb
  have hcl₂ : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₂.reg.2 hB₂ :=
    clBelowB hb₂.reg.2 hB₂ (assumpPref_reg hAPb₂) hAPB₂
      (lexDM_both_wt_lt_right Aw hb₂.reg.2 hB₂ D₁ D₂ rfl hwreg₂ hwB₂)
  exact eut_lam_nodes tbl hTC σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂
    (bitBelow hA₁ hA₂ hAPA₁ hAPA₂ hlexA)
    (clBelow hA₁ hA₂ hAPA₁ hAPA₂ hlexA)
    (hcl₁.trans (heut_b.trans hcl₂))

/-! ## §6 `letE/letE` via the real `letSub` (S10 §5.2) -/

/-- `EUT` on any two `TyP.letE` nodes on `.letE A v b` — different body types
    `B₁, B₂` included — staying in the original `Γ` with the actual lazy let
    substitution `Lᵢ := letSub hbᵢ hvᵢ hAᵢ` (`Lᵢ.wt < Dᵢ.wt` because `Dᵢ` also
    carries `hTᵢ`). Requests: `CL[hT₁, L₁.reg.2]`, `EUT[L₁, L₂]`,
    `CL[L₂.reg.2, hT₂]`, composed by trans into `eut_letE_nodes`. -/
theorem eut_letE_letE_of_local_calls (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (hAPA₁ : hA₁.AssumpPref) (hAPv₁ : hv₁.AssumpPref) (hAPb₁ : hb₁.AssumpPref)
    (hAPT₁ : hT₁.AssumpPref)
    (hAPA₂ : hA₂.AssumpPref) (hAPv₂ : hv₂.AssumpPref) (hAPb₂ : hb₂.AssumpPref)
    (hAPT₂ : hT₂.AssumpPref)
    (σ : Level → Level) (ρ : List Disp)
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂)))
    (eutBelow : EUTBelowHere Aw tbl E n Γ σ ρ
      (tyPairMeas Aw (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂))) :
    EUT tbl σ ρ (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) := by
  let D₁ := TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁
  let D₂ := TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂
  let L₁ := letSub hb₁ hv₁ hA₁
  let L₂ := letSub hb₂ hv₂ hA₂
  have hwL₁ : L₁.wt Aw < D₁.wt Aw := by
    have := TyP.wt_pos Aw hT₁
    simp only [L₁, letSub_wt, D₁, TyP.wt]; omega
  have hwL₂ : L₂.wt Aw < D₂.wt Aw := by
    have := TyP.wt_pos Aw hT₂
    simp only [L₂, letSub_wt, D₂, TyP.wt]; omega
  have hwT₁ : hT₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwT₂ : hT₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwreg₁ : L₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw L₁) hwL₁
  have hwreg₂ : L₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw L₂) hwL₂
  have hAPL₁ : L₁.AssumpPref := assumpPref_letSub hAPb₁ hAPv₁ hAPA₁
  have hAPL₂ : L₂.AssumpPref := assumpPref_letSub hAPb₂ hAPv₂ hAPA₂
  have hcl₁ : CL tbl σ ρ hT₁ L₁.reg.2 :=
    clBelow hT₁ L₁.reg.2 hAPT₁ (assumpPref_reg hAPL₁)
      (lexDM_both_wt_lt_left Aw hT₁ L₁.reg.2 D₁ D₂ rfl hwT₁ hwreg₁)
  have heut_L : EUT tbl σ ρ L₁ L₂ :=
    eutBelow L₁ L₂ hAPL₁ hAPL₂ (lexDM_wt_lt_pair Aw L₁ L₂ D₁ D₂ rfl rfl hwL₁ hwL₂)
  have hcl₂ : CL tbl σ ρ L₂.reg.2 hT₂ :=
    clBelow L₂.reg.2 hT₂ (assumpPref_reg hAPL₂) hAPT₂
      (lexDM_both_wt_lt_right Aw L₂.reg.2 hT₂ D₁ D₂ rfl hwreg₂ hwT₂)
  exact eut_letE_nodes tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂
    (hcl₁.trans (heut_L.trans hcl₂))

/-! ## §7 Controls -/

/-- The same-view premise the same-transport `linst/linst` adapters consume
    (S10 §1, §8): one source context bound `a'`, one source subject `e`, and one
    actual parameter list `ls`. Equal transport tags — and even equal displayed
    terms — never give it. -/
def LinstSameView (a₁ a₂ : Nat) (e₁ e₂ : Expr Nat) (ls₁ ls₂ : List Level) : Prop :=
  a₁ = a₂ ∧ e₁ = e₂ ∧ ls₁ = ls₂

/-- Control (S10 §1): a same-tag `linst` pair whose *sources* differ is refused
    as a same-view pair, regardless of what it displays. -/
theorem linst_diff_source_no_sameview {a₁ a₂ : Nat} {e₁ e₂ : Expr Nat}
    {ls₁ ls₂ : List Level} (hne : e₁ ≠ e₂) :
    ¬ LinstSameView a₁ a₂ e₁ e₂ ls₁ ls₂ :=
  fun h => hne h.2.1

/-- Concrete tooth (S10 §1): `linst [zero] (sort (param 0))` and
    `linst [zero] (sort zero)` display the same term at the same level list,
    but the sources differ — the same-view premise fails. -/
theorem linst_sameTag_diff_source_refused :
    ¬ LinstSameView 0 0 (Expr.sort (.param 0)) (Expr.sort .zero) [.zero] [.zero] := by
  have hne : (Expr.sort (Level.param 0) : Expr Nat) ≠ Expr.sort Level.zero := by decide
  exact linst_diff_source_no_sameview hne

/-- The same-view premise the same-transport `esub/esub` adapters consume
    (S10 §1, §8): one source subject `e` and the same actual substitution
    parameters `(t, v, j)`. -/
def EsubSameView (e₁ e₂ t₁ t₂ v₁ v₂ : Expr Nat) (j₁ j₂ : Nat) : Prop :=
  e₁ = e₂ ∧ t₁ = t₂ ∧ v₁ = v₂ ∧ j₁ = j₂

/-- Control (S10 §1): a same-tag `esub` pair whose sources differ is refused as
    a same-view pair. -/
theorem esub_diff_source_no_sameview {e₁ e₂ t₁ t₂ v₁ v₂ : Expr Nat} {j₁ j₂ : Nat}
    (hne : e₁ ≠ e₂) :
    ¬ EsubSameView e₁ e₂ t₁ t₂ v₁ v₂ j₁ j₂ :=
  fun h => hne h.1

/-- Concrete tooth: two `esub`s on the same parameters but different subjects
    are not a same-view pair. -/
theorem esub_sameTag_diff_source_refused :
    ¬ EsubSameView (Expr.sort (.param 0)) (Expr.sort .zero)
      (.sort .zero) (.sort .zero) (.bvar 0) (.bvar 0) 0 0 := by
  have hne : (Expr.sort (Level.param 0) : Expr Nat) ≠ Expr.sort Level.zero := by decide
  exact esub_diff_source_no_sameview hne

/-- λ-row same-rank negative control (S10 §5.1): the `EUT` case of a λ/λ pair
    issues five requests at strictly smaller `tyPairMeas` ranks and *never* a
    request on the current pair itself. A current-pair `TagCoh`-style query
    would carry the identical `tyPairMeas` on both sides of the edge, and
    `LexDM` is irreflexive — so no such IH edge exists, whether or not the
    propositional tag differs. -/
theorem eut_lam_sameRank_no_self_call (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂)) :
    ¬ LexDM
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂))
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)) :=
  lexDM_irrefl

end Rcic.Syn

#print axioms Rcic.Syn.CLBelowHere
#print axioms Rcic.Syn.EUTBelowHere
#print axioms Rcic.Syn.ESBelowHere
#print axioms Rcic.Syn.BITBelowHere
#print axioms Rcic.Syn.sortNode
#print axioms Rcic.Syn.sortNode_assumpPref
#print axioms Rcic.Syn.clBelowHere_of_below
#print axioms Rcic.Syn.eutBelowHere_of_below
#print axioms Rcic.Syn.esBelowHere_of_below
#print axioms Rcic.Syn.bitBelowHere_of_below
#print axioms Rcic.Syn.eut_conv_left_of_local_calls
#print axioms Rcic.Syn.eut_conv_right_of_local_calls
#print axioms Rcic.Syn.eut_sort_sort_of_local_calls
#print axioms Rcic.Syn.eut_bvar_bvar_of_local_calls
#print axioms Rcic.Syn.eut_lit_lit_of_local_calls
#print axioms Rcic.Syn.sortCoh_of_local_calls
#print axioms Rcic.Syn.eut_pi_pi_of_local_calls
#print axioms Rcic.Syn.eut_lam_lam_of_local_calls
#print axioms Rcic.Syn.eut_letE_letE_of_local_calls
#print axioms Rcic.Syn.dmStep_irrefl_aux
#print axioms Rcic.Syn.dmStep_irrefl
#print axioms Rcic.Syn.lexDM_irrefl
#print axioms Rcic.Syn.LinstSameView
#print axioms Rcic.Syn.linst_diff_source_no_sameview
#print axioms Rcic.Syn.linst_sameTag_diff_source_refused
#print axioms Rcic.Syn.EsubSameView
#print axioms Rcic.Syn.esub_diff_source_no_sameview
#print axioms Rcic.Syn.esub_sameTag_diff_source_refused
#print axioms Rcic.Syn.eut_lam_sameRank_no_self_call
