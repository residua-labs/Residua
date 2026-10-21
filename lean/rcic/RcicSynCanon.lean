import rcic.RcicSynCR
import rcic.RcicSynPack

/-!
# Syntactic sortRow, build step 3t — canonical endpoints

`research/rcic/semantic/S3_ES_ARMS.md` §19. `sorts`, `lit` and `consts` do not
walk the stored endpoint. Each one builds the one-node typing whose `eps` is
the clause equation (`eps_sort`, `eps_lit`, `eps_const_proof` / `eps_const_rel`)
and calls `CL` below the rule node.

`CL` concludes `↔*`, not definitional equality. A typing of `.sort l` need not
erase to `sort (σ l)`: `SortHead.esub_var` on the `drop` path can erase the
variable to `★` or, when the erased context is shorter than the index, to a
`bvar`. That case is a `CL` obligation of the fix (`PB` / `CTS`), not a
structural lemma, and it is not discharged here.

`consts` has a second obligation the one node does not see. The two endpoints
carry their own regularity levels. Both proof-bits agree because the
regularity derivations of the common type erase to `sort (σ u)` and
`sort (σ u')`, `EUT` makes those convertible, and `eqN_of_convE_sort_wf`
separates them. That is why this arm takes `TableWF`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 calls under a rule node -/

/-- `CL` of two typings whose weights sit under one non-transport node. -/
theorem cl_under (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (B : Below Aw tbl (cvMeas Aw hnode))
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E' n' Γ' e T₁) (D₂ : TyP E' n' Γ' e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E' n' Γ' ρ)
    (h₁ : D₁.wt Aw < hnode.wt Aw) (h₂ : D₂.wt Aw < hnode.wt Aw) :
    CL tbl σ ρ D₁ D₂ :=
  B.cl D₁ D₂ σ ρ hρ (lex_of_dm (dmStep_pair_below Aw hnode ht D₁ D₂ h₁ h₂))

/-- `EUT` of two typings of one term, under the same weight bound. -/
theorem eut_under (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (B : Below Aw tbl (cvMeas Aw hnode))
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E' n' Γ' e T₁) (D₂ : TyP E' n' Γ' e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E' n' Γ' ρ)
    (h₁ : D₁.wt Aw < hnode.wt Aw) (h₂ : D₂.wt Aw < hnode.wt Aw) :
    EUT tbl σ ρ D₁ D₂ :=
  B.eut D₁ D₂ σ ρ hρ (lex_of_dm (dmStep_pair_below Aw hnode ht D₁ D₂ h₁ h₂))

/-- `BitCoh` of two sort typings of one type, under the same weight bound (Q10). -/
theorem bitCoh_under (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (B : Below Aw tbl (cvMeas Aw hnode))
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {T' : Expr Nat} {u v : Level}
    (D₁ : TyP E' n' Γ' T' (.sort u)) (D₂ : TyP E' n' Γ' T' (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E' n' Γ' ρ)
    (h₁ : D₁.wt Aw < hnode.wt Aw) (h₂ : D₂.wt Aw < hnode.wt Aw) :
    BitCoh σ D₁ D₂ :=
  B.bitCoh D₁ D₂ σ ρ hρ (lex_of_dm (dmStep_pair_below Aw hnode ht D₁ D₂ h₁ h₂))

/-! ## §2 `sorts` -/

/-- Both endpoints are `CL` to a `sort` node. `DispFor.levelSub` supplies
    `eqN_map`, which sends the two erased sorts across `≈`. The right node is
    typed at `sort (succ l₂)`; `CL` does not ask it to share `dr`'s slack
    `sort (succ l₁)`. -/
theorem es_of_below_sorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l₁ l₂ : Level}
    (σ : Level → Level)
    (h : eqN l₁ l₂)
    (dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁)))
    (dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁)))
    (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.sorts E n Γ l₁ l₂ h dl dr))) :
    ES tbl σ ρ (CvP.sorts E n Γ l₁ l₂ h dl dr) := by
  let hnode := CvP.sorts E n Γ l₁ l₂ h dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canonL := TyP.sort E n Γ l₁ (.succ l₁) (eqN_refl _)
  let canonR := TyP.sort E n Γ l₂ (.succ l₂) (eqN_refl _)
  have hwcL : canonL.wt Aw < hnode.wt Aw := by
    have hpos := TyP.wt_pos Aw dl
    simp only [TyP.wt, CvP.wt]
    omega
  have hwcR : canonR.wt Aw < hnode.wt Aw := by
    have hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.sort (σ l₁)) := by
    simpa only [CL, eps_sort] using cl_under Aw tbl hnode ht B dl canonL σ ρ hρ hwl hwcL
  have hR : ConvMod (EStep tbl) LvlEq (dr.eps σ ρ) (.sort (σ l₂)) := by
    simpa only [CL, eps_sort] using cl_under Aw tbl hnode ht B dr canonR σ ρ hρ hwr hwcR
  have hmid : ConvMod (EStep tbl) LvlEq (.sort (σ l₁)) (.sort (σ l₂)) :=
    .eqv (.sort (hρ.levelSub.eqN_map h))
  simpa only [ES, CvP.dl, CvP.dr] using
    (hL.trans (hmid.trans (ConvMod.symm' LvlEq.symm' hR)))

/-! ## §3 `lit` -/

/-- The literal node erases to its expansion (`eps_lit`). `CL` moves that to
    the stored literal endpoint, and `CL` of the two typings of the expansion
    moves it to `dr`. -/
theorem es_of_below_lit (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (h : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.lit E n Γ t exp T h hexp dl dr))) :
    ES tbl σ ρ (CvP.lit E n Γ t exp T h hexp dl dr) := by
  cases h with
  | of =>
    let hnode := CvP.lit E n Γ t (natExpand t) T (.of t) hexp dl dr
    have ht : hnode.isTransport = false := rfl
    have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
    have hwe : hexp.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
    have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
    let canon := TyP.lit E n Γ t T hexp
    have hwc : canon.wt Aw < hnode.wt Aw := by
      have hpos := TyP.wt_pos Aw dl
      simp only [TyP.wt, CvP.wt]
      omega
    have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hexp.eps σ ρ) := by
      simpa only [CL, eps_lit] using cl_under Aw tbl hnode ht B dl canon σ ρ hρ hwl hwc
    have hR : ConvMod (EStep tbl) LvlEq (hexp.eps σ ρ) (dr.eps σ ρ) := by
      simpa only [CL] using cl_under Aw tbl hnode ht B hexp dr σ ρ hρ hwe hwr
    simpa only [ES, CvP.dl, CvP.dr] using (hL.trans hR)

/-! ## §4 `consts` -/

/-- The two regularity levels of the common ascribed type agree after `σ`
    (`SortCoh`). `EUT` compares the typings of that type; each regularity
    derivation types a sort, and `CL` against a `sort` node puts `sort (σ u)`
    on both sides. -/
theorem const_reg_levels (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b Tnode : Expr Nat}
    (hnode : CvP E n Γ a b Tnode) (ht : hnode.isTransport = false)
    (B : Below Aw tbl (cvMeas Aw hnode))
    (hW : TableWF tbl)
    {T : Expr Nat} {u u' : Level}
    (hTu : TyP E n Γ T (.sort u)) (hTu' : TyP E n Γ T (.sort u'))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : hTu.wt Aw < hnode.wt Aw) (hu' : hTu'.wt Aw < hnode.wt Aw) :
    SortCoh σ hTu hTu' := by
  have hSu : hTu.reg.2.wt Aw < hnode.wt Aw := by
    have hle := TyP.wt_reg_le Aw hTu
    omega
  have hSu' : hTu'.reg.2.wt Aw < hnode.wt Aw := by
    have hle := TyP.wt_reg_le Aw hTu'
    omega
  let canonU := TyP.sort E n Γ u (.succ u) (eqN_refl _)
  let canonU' := TyP.sort E n Γ u' (.succ u') (eqN_refl _)
  have hwc : canonU.wt Aw < hnode.wt Aw := by
    simp only [TyP.wt]
    have hpos := TyP.wt_pos Aw hTu
    omega
  have hwc' : canonU'.wt Aw < hnode.wt Aw := by
    simp only [TyP.wt]
    have hpos := TyP.wt_pos Aw hTu'
    omega
  have hLU : ConvMod (EStep tbl) LvlEq (hTu.reg.2.eps σ ρ) (.sort (σ u)) := by
    simpa only [CL, eps_sort] using
      cl_under Aw tbl hnode ht B hTu.reg.2 canonU σ ρ hρ hSu hwc
  have hLU' : ConvMod (EStep tbl) LvlEq (hTu'.reg.2.eps σ ρ) (.sort (σ u')) := by
    simpa only [CL, eps_sort] using
      cl_under Aw tbl hnode ht B hTu'.reg.2 canonU' σ ρ hρ hSu' hwc'
  have hE : ConvMod (EStep tbl) LvlEq (hTu.reg.2.eps σ ρ) (hTu'.reg.2.eps σ ρ) := by
    simpa only [EUT] using eut_under Aw tbl hnode ht B hTu hTu' σ ρ hρ hu hu'
  exact eqN_of_convE_sort_wf hW
    ((ConvMod.symm' LvlEq.symm' hLU).trans (hE.trans hLU'))

/-- Both endpoints are `CL` to a `const` node built from that endpoint's own
    regularity. The nodes erase to `★` together or to `const r (ls.map σ)` and
    `const r (ls'.map σ)`, which `≈` identifies. `TableWF` is the separator
    that keeps the two proof-bits from disagreeing. -/
theorem es_of_below_consts (Aw : Nat → Nat) (tbl : List CRule)
    (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (σ : Level → Level)
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw
      (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr))) :
    ES tbl σ ρ (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) := by
  let hnode := CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hu : dl.reg.2.wt Aw < hnode.wt Aw := by
    have hle := TyP.wt_reg_le Aw dl
    omega
  have hu' : dr.reg.2.wt Aw < hnode.wt Aw := by
    have hle := TyP.wt_reg_le Aw dr
    omega
  have hlevels : eqN (σ dl.reg.1) (σ dr.reg.1) :=
    const_reg_levels Aw tbl hnode ht B hW dl.reg.2 dr.reg.2 σ ρ hρ hu hu'
  have hsame : levelIsZero (σ dl.reg.1) = levelIsZero (σ dr.reg.1) :=
    levelIsZero_congr hlevels
  have hlen' : ls'.length = m.arity := by
    rw [← eqNList_length ls ls' h]
    exact hlen
  let canonL := TyP.const E n Γ r ls ls m dl.reg.1 hres hlen hwf (eqNList_refl ls) dl.reg.2
  let canonR := TyP.const E n Γ r ls' ls m dr.reg.1 hres hlen' hwf' (eqNList_symm h) dr.reg.2
  have hwcL : canonL.wt Aw < hnode.wt Aw := by
    have hreg := TyP.wt_reg_le Aw dl
    have hAw : Aw r < dr.wt Aw := TyP.admW_lt_of_const Aw dr ⟨ls', rfl⟩
    simp only [TyP.wt, CvP.wt]
    omega
  have hwcR : canonR.wt Aw < hnode.wt Aw := by
    have hreg := TyP.wt_reg_le Aw dr
    have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
    simp only [TyP.wt, CvP.wt]
    omega
  have hLraw := cl_under Aw tbl hnode ht B dl canonL σ ρ hρ hwl hwcL
  have hRraw := cl_under Aw tbl hnode ht B dr canonR σ ρ hρ hwr hwcR
  cases hzu : levelIsZero (σ dl.reg.1)
  · have hzu' : levelIsZero (σ dr.reg.1) = false := by rw [← hsame]; exact hzu
    have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.const r (ls.map σ)) := by
      simpa only [CL, eps_const_rel hzu] using hLraw
    have hR : ConvMod (EStep tbl) LvlEq (dr.eps σ ρ) (.const r (ls'.map σ)) := by
      simpa only [CL, eps_const_rel hzu'] using hRraw
    have hmid : ConvMod (EStep tbl) LvlEq
        (.const r (ls.map σ)) (.const r (ls'.map σ)) :=
      .eqv (.const r (eqNList_map_congr hρ.levelSub.eqN_map h))
    simpa only [ES, CvP.dl, CvP.dr] using
      (hL.trans (hmid.trans (ConvMod.symm' LvlEq.symm' hR)))
  · have hzu' : levelIsZero (σ dr.reg.1) = true := by rw [← hsame]; exact hzu
    have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) .star := by
      simpa only [CL, eps_const_proof hzu] using hLraw
    have hR : ConvMod (EStep tbl) LvlEq (dr.eps σ ρ) .star := by
      simpa only [CL, eps_const_proof hzu'] using hRraw
    simpa only [ES, CvP.dl, CvP.dr] using
      (hL.trans (ConvMod.symm' LvlEq.symm' hR))

end Rcic.Syn

#print axioms Rcic.Syn.cl_under
#print axioms Rcic.Syn.eut_under
#print axioms Rcic.Syn.bitCoh_under
#print axioms Rcic.Syn.es_of_below_sorts
#print axioms Rcic.Syn.es_of_below_lit
#print axioms Rcic.Syn.const_reg_levels
#print axioms Rcic.Syn.es_of_below_consts
