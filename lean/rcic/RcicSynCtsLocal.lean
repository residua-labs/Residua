import rcic.RcicSynRegStep
import rcic.RcicSynLetInline

/-!
# Syntactic sortRow, build step 9 — `CTS` and the derived `BitCoh` from local call interfaces

`research/rcic/sortrow/S9_CTS_BITCOH_ASSEMBLY.md` (#7345). The `.cts` and `.bitCoh`
cases of the sortRow mutual induction take only this call's real requests from the
induction hypothesis at the same bound — no rebuilt unconditional `Below` supplier.

1. **§1 The two local bounded call interfaces** (`CLBelowHere`, `EUTBelowHere`):
   `CL` / `EUT` at every same-scope pair of `TyP`s strictly `LexDM`-below `bound`,
   gated on both derivations' `AssumpPref`. `sortNode` is the canonical `TyP.sort`
   target a reg-`CL` request is paired against. These are local projection
   interfaces of the pack IH, not new full-domain suppliers.

2. **§2 Non-vacuity of the interfaces** (`clBelowHere_of_below`,
   `eutBelowHere_of_below`): any `Below Aw tbl bound` supplier at a
   `DispFor`-reachable `ρ` already implements both interfaces — the `AssumpPref`
   premises are not consulted by this projection.

3. **§3 `cts_from_local_calls`**: the three real `CTS` requests — the `h.dl`/`DX`
   `EUT` (`lexDM_cts_pair`), the left reg-`CL` (`dmStep_cvp_dl_reg` then
   `dmStep_drop_right` over `DX`'s atoms), and the right reg-`CL`
   (`dmStep_reg_sort_pair` then `dmStep_drop_left` over `h`'s atoms) — descend
   strictly at `cvTyMeas Aw h DX`; a `DX.isSortOrPiHead = true` takes the zero-call
   branch `cl_reg_sort_of_isSortOrPiHead`. The conclusion is `CTS h DX`
   (`eqN s w`) via `cts_of_eut_cl`: `EUT` + sort separation produces `eqN w s`
   first and the composition performs the symmetry — a `BitCoh` cannot stand in
   for `CTS`.

4. **§4 `bitCoh_from_current_eut`**: `BitCoh σ D₁ D₂` from the *current pair's*
   `EUT` (built inside the step, never re-requested — see §5) plus the two
   reg-`CL` descents `lexDM_reg_sort_of_pair_left` / `_right` at
   `tyPairMeas Aw D₁ D₂`.

5. **§5 The same-rank negative control**: `dmStep_irrefl` and `lexDM_irrefl` make
   the `LexDM` order irreflexive; `eut_bitCoh_sameRank_no_ih` pins that an
   `.eut`-tagged request and a `.bitCoh`-tagged request on the same pair of sort
   typings carry the *identical* `tyPairMeas` rank, so an IH edge between them is
   refused. A same-rank local data dependency (the `.bitCoh` case reusing the
   result of the `.eut` body) is never a recursive call.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Local bounded call interfaces -/

/-- Local projection of the pack IH for `CL`: every same-scope pair
    `D₁ D₂ : TyP E n Γ e _`, both `AssumpPref`, at a strictly smaller
    `tyPairMeas`, yields `CL tbl σ ρ D₁ D₂`. -/
def CLBelowHere (Aw : Nat → Nat) (tbl : List CRule) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (σ : Level → Level) (ρ : List Disp) (bound : List Nat × Nat) : Prop :=
  ∀ {e A B : Expr Nat} (D₁ : TyP E n Γ e A) (D₂ : TyP E n Γ e B),
    D₁.AssumpPref → D₂.AssumpPref → LexDM (tyPairMeas Aw D₁ D₂) bound → CL tbl σ ρ D₁ D₂

/-- Local projection of the pack IH for `EUT`: every same-scope pair
    `D₁ D₂ : TyP E n Γ e _`, both `AssumpPref`, at a strictly smaller
    `tyPairMeas`, yields `EUT tbl σ ρ D₁ D₂`. -/
def EUTBelowHere (Aw : Nat → Nat) (tbl : List CRule) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (σ : Level → Level) (ρ : List Disp) (bound : List Nat × Nat) : Prop :=
  ∀ {e A B : Expr Nat} (D₁ : TyP E n Γ e A) (D₂ : TyP E n Γ e B),
    D₁.AssumpPref → D₂.AssumpPref → LexDM (tyPairMeas Aw D₁ D₂) bound → EUT tbl σ ρ D₁ D₂

/-- The canonical `TyP.sort` node a reg-`CL` request is paired against. -/
def sortNode (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    TyP E n Γ (.sort l) (.sort (.succ l)) :=
  TyP.sort E n Γ l (.succ l) (eqN_refl _)

/-- `sortNode` satisfies `AssumpPref` unconditionally (a `.sort` leaf carries no
    transport). -/
theorem sortNode_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (sortNode E n Γ l).AssumpPref :=
  trivial

/-! ## §2 The interfaces are projections of `Below` (non-vacuity) -/

/-- Any `Below Aw tbl bound` supplier implements `CLBelowHere` at a
    `DispFor`-reachable `ρ`; the `AssumpPref` premises are unused by this
    projection. -/
theorem clBelowHere_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {bound : List Nat × Nat} (hρ : DispFor σ E n Γ ρ) (Bel : Below Aw tbl bound) :
    CLBelowHere Aw tbl E n Γ σ ρ bound :=
  fun D₁ D₂ _ _ hlex => Bel.cl D₁ D₂ σ ρ hρ hlex

/-- Any `Below Aw tbl bound` supplier implements `EUTBelowHere` at a
    `DispFor`-reachable `ρ`. -/
theorem eutBelowHere_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {bound : List Nat × Nat} (hρ : DispFor σ E n Γ ρ) (Bel : Below Aw tbl bound) :
    EUTBelowHere Aw tbl E n Γ σ ρ bound :=
  fun D₁ D₂ _ _ hlex => Bel.eut D₁ D₂ σ ρ hρ hlex

/-! ## §3 `CTS` from the three real local requests -/

/-- `CTS h DX` (`eqN s w`) at the pack measure `cvTyMeas Aw h DX`, from the two
    local interfaces only: the `EUT` on `(h.dl, DX)`, the `CL` on
    `(h.dl.reg.2, sortNode w)`, and — unless `DX.isSortOrPiHead` makes it free —
    the `CL` on `(DX.reg.2, sortNode s)`. -/
theorem cts_from_local_calls (Aw : Nat → Nat) {tbl : List CRule} (hTbl : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (hAP : h.AssumpPref) (hDX : DX.AssumpPref) (ρ : List Disp)
    (clBelow : CLBelowHere Aw tbl E n Γ id ρ (cvTyMeas Aw h DX))
    (eutBelow : EUTBelowHere Aw tbl E n Γ id ρ (cvTyMeas Aw h DX)) : CTS h DX := by
  have heut : EUT tbl id ρ h.dl DX :=
    eutBelow h.dl DX (assumpPref_dl hAP) hDX (lexDM_cts_pair Aw h DX)
  have hL : CL tbl id ρ h.dl.reg.2 (sortNode E n Γ w) := by
    have hd : DMStep (h.dl.reg.2.atoms Aw ++ (sortNode E n Γ w).atoms Aw) (h.atoms Aw) := by
      refine dmStep_cvp_dl_reg Aw h ?_
      intro y hy
      simp only [sortNode, TyP.atoms, List.mem_singleton] at hy
      subst y
      exact Nat.le_refl 1
    exact clBelow h.dl.reg.2 (sortNode E n Γ w) (assumpPref_reg (assumpPref_dl hAP))
      sortNode_assumpPref (lex_of_dm (dmStep_drop_right hd (DX.atoms Aw)))
  have hR : CL tbl id ρ DX.reg.2 (sortNode E n Γ s) := by
    cases hs : DX.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl DX hs id ρ
    | false =>
        exact clBelow DX.reg.2 (sortNode E n Γ s) (assumpPref_reg hDX)
          sortNode_assumpPref
          (lex_of_dm (dmStep_drop_left (dmStep_reg_sort_pair Aw DX hs) (h.atoms Aw)))
  exact cts_of_eut_cl hTbl h DX ρ heut hL hR

/-! ## §4 The derived `BitCoh` from the current pair's `EUT` -/

/-- `BitCoh σ D₁ D₂` at the pack measure `tyPairMeas Aw D₁ D₂`, from the current
    pair's already-produced `EUT` and the two reg-`CL` descents. The `EUT` is an
    argument of this step, not a recursive request: `Q.eut D₁ D₂` and
    `Q.bitCoh D₁ D₂` have the same rank (§5). -/
theorem bitCoh_from_current_eut (Aw : Nat → Nat) {tbl : List CRule} (hTbl : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) (σ : Level → Level) (ρ : List Disp)
    (heut : EUT tbl σ ρ D₁ D₂)
    (clBelow : CLBelowHere Aw tbl E n Γ σ ρ (tyPairMeas Aw D₁ D₂)) :
    BitCoh σ D₁ D₂ := by
  have hL : CL tbl σ ρ D₁.reg.2 (sortNode E n Γ u) := by
    cases hs : D₁.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₁ hs σ ρ
    | false =>
        exact clBelow D₁.reg.2 (sortNode E n Γ u) (assumpPref_reg h₁)
          sortNode_assumpPref (lexDM_reg_sort_of_pair_left Aw D₁ hs D₂)
  have hR : CL tbl σ ρ D₂.reg.2 (sortNode E n Γ v) := by
    cases hs : D₂.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₂ hs σ ρ
    | false =>
        exact clBelow D₂.reg.2 (sortNode E n Γ v) (assumpPref_reg h₂)
          sortNode_assumpPref (lexDM_reg_sort_of_pair_right Aw D₁ D₂ hs)
  exact bitCoh_of_eut_cl hTbl D₁ D₂ σ ρ heut hL hR

/-! ## §5 The same-rank negative control -/

/-- `DMStep` is irreflexive (it is well-founded by `dmStep_wf`): a multiset is
    never a strict step of itself. -/
theorem dmStep_irrefl_aux {M : List Nat} (hacc : Acc DMStep M) : DMStep M M → False := by
  induction hacc with
  | intro x _ ih => exact fun h => ih x h h

theorem dmStep_irrefl {M : List Nat} : ¬ DMStep M M :=
  dmStep_irrefl_aux (dmStep_wf.apply M)

/-- `LexDM` is irreflexive: the multiset component never steps to itself and the
    weight component is a strict `<`. -/
theorem lexDM_irrefl {m : List Nat × Nat} : ¬ LexDM m m := by
  intro h
  cases h with
  | left _ _ h => exact dmStep_irrefl h
  | right _ h => exact Nat.lt_irrefl _ h

/-- Same-rank negative control (S9 §4): the `EUT` request and the `BitCoh`
    request on one pair of sort typings have the *identical* `tyPairMeas` rank —
    `tyPairMeas Aw D₁ D₂` on both sides — so a strict-descent IH edge between
    them does not exist. -/
theorem eut_bitCoh_sameRank_no_ih (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)) :
    ¬ LexDM (tyPairMeas Aw D₁ D₂) (tyPairMeas Aw D₁ D₂) :=
  lexDM_irrefl

end Rcic.Syn

#print axioms Rcic.Syn.CLBelowHere
#print axioms Rcic.Syn.EUTBelowHere
#print axioms Rcic.Syn.sortNode
#print axioms Rcic.Syn.sortNode_assumpPref
#print axioms Rcic.Syn.clBelowHere_of_below
#print axioms Rcic.Syn.eutBelowHere_of_below
#print axioms Rcic.Syn.cts_from_local_calls
#print axioms Rcic.Syn.bitCoh_from_current_eut
#print axioms Rcic.Syn.dmStep_irrefl_aux
#print axioms Rcic.Syn.dmStep_irrefl
#print axioms Rcic.Syn.lexDM_irrefl
#print axioms Rcic.Syn.eut_bitCoh_sameRank_no_ih
