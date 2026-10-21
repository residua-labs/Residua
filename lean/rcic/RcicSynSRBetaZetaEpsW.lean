import rcic.RcicSynSRBetaZetaBeta

/-!
# sortRow inline wedge — repair candidate `epsW` (display-aware erasure)

cc 2026-10-20 16:45Z, after #7798's audit pinned `beta_body_cl`'s defect to
the erasure: `TyP.wk`'s eps clause lifts the inner erasure by one at
`countKeep (ρ.take c)` whenever the inserted entry is a `keep`, but a bvar
that resolved through an `.inline v` entry at `j < c` already carries that
slot in `v`'s frame (the display value is computed in the context *outside*
the let). The lift is applied a second time — the same wedge as the landed
`not_es_wk_inline`.

The repair, new names only (`RcicSynRead`/`RcicSynRedex`/`eps` untouched):
at a `wk` over a `keep`, first re-frame every inline value at `j < c` by
removing the inserted keep's slot (`ETm.inst s .star`, the arbitrary-slot
sibling of the landed R2 `localize` repair at slot 0), run the inner erasure
at that display, then apply the unchanged keep-lift. Net effect: `wk` shifts
an inline display value exactly once. Deliverables:

* (a) `epsW_eq_eps_noInline` — conservativity: `epsW = eps` whenever the
  display has no inline entry and the derivation pushes none (`letE`/`lsub`).
* (b) `es_wkZetaNode_epsW` — the `not_es_wk_inline` wedge vanishes under
  `epsW` (`ESW` holds at the canonical disposition).
* (c) `clw_beta_body_epsW` / `clw_beta_reduct_epsW` — at the #7780 fixture,
  the `beta_body_cl` and `beta_reduct_cl` goals restated with `epsW` (`CLW`)
  hold. closure_claim = 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `wk`'s inner display, prefix pass: position `c` is dropped (as
    `removeAt`); every inline entry at a position `j < c` has its value
    unlifted at the slot the inserted keep occupies in that value's frame
    (`r` counts the keeps still before `c`, below the ones already passed). -/
def wkInnerGo (r : Nat) : Nat → List Disp → List Disp
  | _, [] => []
  | 0, _ :: ρ => ρ
  | k + 1, d :: ρ =>
      let d' := match d with
        | .inline v => .inline (ETm.inst r .star v)
        | _ => d
      let r' := match d with
        | .keep => r - 1
        | _ => r
      d' :: wkInnerGo r' k ρ

/-- The inner display of a `wk` at cutoff `c`: when the inserted entry is a
    `keep`, `removeAt ρ c` with every inline value at `j < c` re-framed
    (unlifted at the inserted keep's slot in that value's frame); otherwise
    exactly `removeAt ρ c` (no slot is inserted, frames already agree). -/
def wkInnerDisp (ρ : List Disp) (c : Nat) : List Disp :=
  match ρ[c]? with
  | some .keep => wkInnerGo (countKeep (ρ.take c)) c ρ
  | _ => removeAt ρ c

end Rcic.Syn

namespace Rcic.Syn

open Rcic.Declarative

/-- Display-aware erasure: `TyP.eps` verbatim, except the `wk` arm runs the
    inner erasure at `wkInnerDisp ρ c` (inline values re-framed past the
    inserted keep) before the unchanged keep-lift. -/
def TyP.epsW (σ : Level → Level) (ρ : List Disp) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → ETm
  | _, _, _, _, _, .sort _ _ _ l _ _ => ETm.sort (σ l)
  | _, _, _, _, _, .bvar _ _ _ i _ u _ _ =>
      match levelIsZero (σ u) with
      | true => ETm.star
      | false => resolve ρ i
  | _, _, _, _, _, .const _ _ _ r ls _ _ u _ _ _ _ _ =>
      match levelIsZero (σ u) with
      | true => ETm.star
      | false => ETm.const r (ls.map σ)
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB =>
      match levelIsZero (σ u) with
      | true => ETm.pi (hA.epsW σ ρ) (piSlot true (hB.epsW σ (.drop :: ρ)))
      | false => ETm.pi (hA.epsW σ ρ) (hB.epsW σ (.keep :: ρ))
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ _ hbody _ =>
      match levelIsZero (σ u) with
      | true => hbody.epsW σ (.drop :: ρ)
      | false =>
          match hbody.epsW σ (.keep :: ρ) with
          | .star => ETm.star
          | eb => ETm.lam eb
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ =>
      match hf.epsW σ ρ with
      | .star => ETm.star
      | ef =>
          match ha.epsW σ ρ with
          | .star => ef
          | ea => ETm.app ef ea
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ =>
      match hv.epsW σ ρ with
      | .star => hb.epsW σ (.drop :: ρ)
      | ev => hb.epsW σ (.inline ev :: ρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.epsW σ ρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.epsW σ ρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D =>
      let inner := D.epsW σ (wkInnerDisp ρ c)
      match ρ[c]? with
      | some .keep => inner.lift (countKeep (ρ.take c)) 1
      | _ => inner
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _ =>
      match levelIsZero (σ u) with
      | true => D.epsW σ (insertDisp .drop j ρ)
      | false =>
          ETm.inst (countKeep (ρ.take j)) (hv.epsW σ ρ) (D.epsW σ (insertDisp .keep j ρ))
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D _ hv _ =>
      let r := hv.epsW σ ρ
      match r with
      | .star => D.epsW σ (insertDisp .drop j ρ)
      | r => D.epsW σ (insertDisp (.inline (localize (countKeep (ρ.take j)) r)) j ρ)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D =>
      D.epsW (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.epsW σ ρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.epsW σ ρ

/-! ## (b) the `not_es_wk_inline` wedge vanishes under `epsW` -/

/-- `ES` restated with the display-aware erasure. -/
def ESW (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) : Prop :=
  ConvMod (EStep tbl) LvlEq (h.dl.epsW σ ρ) (h.dr.epsW σ ρ)

/-- Under `epsW` the wedge's left endpoint erases to `.bvar 1`: the inline
    display value is unlifted at the inserted keep's slot (`wkInnerDisp`)
    and the keep-lift restores it — shifted exactly once, net honest. -/
theorem epsW_wkZetaNode_dl :
    (wkZetaNode emptyEnv 0).dl.epsW id ((wkZetaCtxP emptyEnv 0).disp id) = .bvar 1 := rfl

theorem epsW_wkZetaNode_dr :
    (wkZetaNode emptyEnv 0).dr.epsW id ((wkZetaCtxP emptyEnv 0).disp id) = .bvar 1 := rfl

/-- The landed `not_es_wk_inline` refutation is exactly repaired: `ESW`
    holds at the canonical disposition, for every rule table. -/
theorem es_wkZetaNode_epsW (tbl : List CRule) :
    ESW tbl id ((wkZetaCtxP emptyEnv 0).disp id) (wkZetaNode emptyEnv 0) := by
  unfold ESW
  rw [epsW_wkZetaNode_dl, epsW_wkZetaNode_dr]
  exact ConvMod.refl _

/-! ## (c) the #7780 `beta_body_cl` / `beta_reduct_cl` goals under `epsW` -/

/-- `CL` restated with the display-aware erasure. -/
def CLW (tbl : List CRule) (σ : Level → Level) (ρ : List Disp) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) : Prop :=
  ConvMod (EStep tbl) LvlEq (D₁.epsW σ ρ) (D₂.epsW σ ρ)

/-- Under `epsW` the read's body erases to the honest `.bvar 2`: the inline
    value `.bvar 1` is unlifted at the inserted keep's slot by `wkInnerDisp`
    (slot 1 of the value's frame), the resolve keep-walk re-frames it, and
    the single keep-lift restores it — the `.bvar 3` double-lift is gone. -/
theorem epsW_bGot_hbody :
    bGot.hbody.epsW id
      (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho) = .bvar 2 := rfl

theorem epsW_bHBody :
    bHBody.epsW id
      (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho) = .bvar 2 := rfl

/-- The `beta_body_cl` goal of #7780, restated with `epsW`, holds at the
    refutation's own fixture (same binders, same canonical disposition). -/
theorem clw_beta_body_epsW :
    CLW (tableOfI EnvWfT.empty) id
      (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho)
      bGot.hbody bHBody := by
  unfold CLW
  rw [epsW_bGot_hbody, epsW_bHBody]
  exact ConvMod.refl _

/-- Under `epsW` the reduct surface `bDr = zlWkDl` erases to `.bvar 1`
    (the honest inline value, not the double-lifted `.bvar 2`). -/
theorem epsW_bDr : bDr.epsW id zlRho = .bvar 1 := rfl

theorem epsW_instEnd_bEnd :
    (instEnd bHBody bHArg bHA).epsW id zlRho = .bvar 1 := rfl

/-- The `beta_reduct_cl` goal of #7780, restated with `epsW`, holds at the
    refutation's own fixture. -/
theorem clw_beta_reduct_epsW :
    CLW (tableOfI EnvWfT.empty) id zlRho (instEnd bHBody bHArg bHA) bDr := by
  unfold CLW
  rw [epsW_instEnd_bEnd, epsW_bDr]
  exact ConvMod.refl _

/-! ## (a) conservativity: `epsW = eps` with no inline entries -/

/-- A display with no `.inline` entry. -/
inductive NoInlineEntry : List Disp → Prop
  | nil : NoInlineEntry []
  | keep {ρ : List Disp} (h : NoInlineEntry ρ) : NoInlineEntry (.keep :: ρ)
  | drop {ρ : List Disp} (h : NoInlineEntry ρ) : NoInlineEntry (.drop :: ρ)

theorem NoInlineEntry.ne_inline {ρ : List Disp} (h : NoInlineEntry ρ) :
    ∀ (c : Nat) (v : ETm), ρ[c]? ≠ some (.inline v) := by
  induction h with
  | nil => intro c v; cases c <;> simp
  | keep _ ih => intro c v; cases c with
    | zero => simp
    | succ c => simpa only [List.getElem?_cons_succ] using ih c v
  | drop _ ih => intro c v; cases c with
    | zero => simp
    | succ c => simpa only [List.getElem?_cons_succ] using ih c v

theorem noInlineEntry_removeAt {ρ : List Disp} (h : NoInlineEntry ρ) :
    ∀ (c : Nat), NoInlineEntry (removeAt ρ c) := by
  induction h with
  | nil => intro c; exact NoInlineEntry.nil
  | keep h' ih => intro c; cases c with
    | zero => simp only [removeAt]; exact h'
    | succ c => exact NoInlineEntry.keep (ih c)
  | drop h' ih => intro c; cases c with
    | zero => simp only [removeAt]; exact h'
    | succ c => exact NoInlineEntry.drop (ih c)

theorem noInlineEntry_insertDisp {d : Disp} (hd : d = .keep ∨ d = .drop) {ρ : List Disp}
    (h : NoInlineEntry ρ) : ∀ (j : Nat), NoInlineEntry (insertDisp d j ρ) := by
  induction h with
  | nil => intro j; cases j with
    | zero => cases hd with
      | inl hd => simp only [hd, insertDisp]; exact NoInlineEntry.keep NoInlineEntry.nil
      | inr hd => simp only [hd, insertDisp]; exact NoInlineEntry.drop NoInlineEntry.nil
    | succ j => cases hd with
      | inl hd => simp only [hd, insertDisp]; exact NoInlineEntry.keep NoInlineEntry.nil
      | inr hd => simp only [hd, insertDisp]; exact NoInlineEntry.drop NoInlineEntry.nil
  | keep h' ih => intro j; cases j with
    | zero => cases hd with
      | inl hd => simp only [hd, insertDisp]; exact NoInlineEntry.keep (NoInlineEntry.keep h')
      | inr hd => simp only [hd, insertDisp]; exact NoInlineEntry.drop (NoInlineEntry.keep h')
    | succ j => simp only [insertDisp]; exact NoInlineEntry.keep (ih j)
  | drop h' ih => intro j; cases j with
    | zero => cases hd with
      | inl hd => simp only [hd, insertDisp]; exact NoInlineEntry.keep (NoInlineEntry.drop h')
      | inr hd => simp only [hd, insertDisp]; exact NoInlineEntry.drop (NoInlineEntry.drop h')
    | succ j => simp only [insertDisp]; exact NoInlineEntry.drop (ih j)

/-- With no inline entries in `ρ`, the `wk` prefix pass changes nothing:
    `wkInnerDisp` is exactly `removeAt`. -/
theorem wkInnerGo_eq_removeAt {ρ : List Disp} (h : NoInlineEntry ρ) :
    ∀ (r c : Nat), wkInnerGo r c ρ = removeAt ρ c := by
  induction h with
  | nil => intro r c; cases c <;> rfl
  | keep _ ih => intro r c; cases c with
    | zero => rfl
    | succ c => simp only [wkInnerGo, removeAt]; rw [ih (r - 1) c]
  | drop _ ih => intro r c; cases c with
    | zero => rfl
    | succ c => simp only [wkInnerGo, removeAt]; rw [ih r c]

theorem wkInnerDisp_eq_removeAt {ρ : List Disp} (h : NoInlineEntry ρ) (c : Nat) :
    wkInnerDisp ρ c = removeAt ρ c := by
  unfold wkInnerDisp
  cases hc : ρ[c]? with
  | none => rfl
  | some d => cases d with
    | keep => exact wkInnerGo_eq_removeAt h _ c
    | drop => rfl
    | inline v => exact absurd hc (NoInlineEntry.ne_inline h c v)

/-- A derivation that pushes no `.inline` display of its own: every
    constructor except `letE` and `lsub` (those inline their payload). -/
inductive HasNoInlinePush : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Prop
  | sort {E n Γ l k h} : HasNoInlinePush (.sort E n Γ l k h)
  | bvar {E n Γ i A u h hA} : HasNoInlinePush (.bvar E n Γ i A u h hA)
  | const {E n Γ r ls ls₀ m u hres hlen hwf hls hT} (hT' : HasNoInlinePush hT) :
      HasNoInlinePush (.const E n Γ r ls ls₀ m u hres hlen hwf hls hT)
  | pi {E n Γ A u B v hA hB} (h1 : HasNoInlinePush hA) (h2 : HasNoInlinePush hB) :
      HasNoInlinePush (.pi E n Γ A u B v hA hB)
  | lam {E n Γ A u body B v hA hbody hB} (h1 : HasNoInlinePush hA)
      (h2 : HasNoInlinePush hbody) (h3 : HasNoInlinePush hB) :
      HasNoInlinePush (.lam E n Γ A u body B v hA hbody hB)
  | app {E n Γ f a A B w hf ha hT} (h1 : HasNoInlinePush hf) (h2 : HasNoInlinePush ha)
      (h3 : HasNoInlinePush hT) : HasNoInlinePush (.app E n Γ f a A B w hf ha hT)
  | lit {E n Γ t T hexp} (h : HasNoInlinePush hexp) : HasNoInlinePush (.lit E n Γ t T hexp)
  | conv {E n Γ e A B u h hc} (h' : HasNoInlinePush h) : HasNoInlinePush (.conv E n Γ e A B u h hc)
  | wk {E n Γ e A d c D} (h : HasNoInlinePush D) : HasNoInlinePush (.wk E n Γ e A d c D)
  | esub {E n Γ e A t v j u D hget hv hvT} (h1 : HasNoInlinePush D) (h2 : HasNoInlinePush hv)
      (h3 : HasNoInlinePush hvT) : HasNoInlinePush (.esub E n Γ e A t v j u D hget hv hvT)
  | linst {E a n Γ e A ls hls hlen D} (h : HasNoInlinePush D) :
      HasNoInlinePush (.linst E a n Γ e A ls hls hlen D)
  | ewk {E₀ E n Γ e A hext D} (h : HasNoInlinePush D) :
      HasNoInlinePush (.ewk E₀ E n Γ e A hext D)
  | cctx {E n Γ e T A A' u D hA} (h1 : HasNoInlinePush D) :
      HasNoInlinePush (.cctx E n Γ e T A A' u D hA)

/-- (a) Conservativity: on a display with no inline entry, and a derivation
    that pushes none of its own, `epsW` is exactly `eps`. -/
theorem epsW_eq_eps_noInline {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D : TyP E n Γ e T} (hD : HasNoInlinePush D) :
    ∀ (σ : Level → Level) (ρ : List Disp), NoInlineEntry ρ → D.epsW σ ρ = D.eps σ ρ := by
  induction hD with
  | sort => intro σ ρ _; rfl
  | bvar => intro σ ρ _; rfl
  | const => intro σ ρ _; rfl
  | lit _ ih => intro σ ρ hρ; exact ih σ ρ hρ
  | conv _ ih => intro σ ρ hρ; exact ih σ ρ hρ
  | ewk _ ih => intro σ ρ hρ; exact ih σ ρ hρ
  | cctx _ ih => intro σ ρ hρ; exact ih σ ρ hρ
  | linst _ ih => intro σ ρ hρ; exact ih _ ρ hρ
  | @pi E n Γ A u B v hA hB _ _ ihA ihB =>
      intro σ ρ hρ
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihA σ ρ hρ, ihB σ (.drop :: ρ) (NoInlineEntry.drop hρ)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihA σ ρ hρ, ihB σ (.keep :: ρ) (NoInlineEntry.keep hρ)]
  | @lam E n Γ A u body B v hA hbody hB _ _ _ ihA ihBody ihB =>
      intro σ ρ hρ
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihBody σ (.drop :: ρ) (NoInlineEntry.drop hρ)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihBody σ (.keep :: ρ) (NoInlineEntry.keep hρ)]
          rfl
  | @app E n Γ f a A B w hf ha hT _ _ _ ihf iha ihT =>
      intro σ ρ hρ
      simp only [TyP.epsW, TyP.eps, ihf σ ρ hρ, iha σ ρ hρ]
      rfl
  | @esub E n Γ e A t v j u D hget hv hvT _ _ _ ihD ihv ihvT =>
      intro σ ρ hρ
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihD σ (insertDisp .drop j ρ) (noInlineEntry_insertDisp (Or.inr rfl) hρ j)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihv σ ρ hρ,
            ihD σ (insertDisp .keep j ρ) (noInlineEntry_insertDisp (Or.inl rfl) hρ j)]
  | @wk E n Γ e A d c D _ ihD =>
      intro σ ρ hρ
      have hd : wkInnerDisp ρ c = removeAt ρ c := wkInnerDisp_eq_removeAt hρ c
      cases hc : ρ[c]? with
      | none =>
          simp only [TyP.epsW, TyP.eps, hc, hd]
          rw [ihD σ (removeAt ρ c) (noInlineEntry_removeAt hρ c)]
      | some dv => cases dv with
        | keep =>
            simp only [TyP.epsW, TyP.eps, hc, hd]
            rw [ihD σ (removeAt ρ c) (noInlineEntry_removeAt hρ c)]
        | drop =>
            simp only [TyP.epsW, TyP.eps, hc, hd]
            rw [ihD σ (removeAt ρ c) (noInlineEntry_removeAt hρ c)]
        | inline v => exact absurd hc (NoInlineEntry.ne_inline hρ c v)

end Rcic.Syn

#print axioms Rcic.Syn.wkInnerGo
#print axioms Rcic.Syn.wkInnerDisp
#print axioms Rcic.Syn.TyP.epsW
#print axioms Rcic.Syn.ESW
#print axioms Rcic.Syn.epsW_wkZetaNode_dl
#print axioms Rcic.Syn.epsW_wkZetaNode_dr
#print axioms Rcic.Syn.es_wkZetaNode_epsW
#print axioms Rcic.Syn.CLW
#print axioms Rcic.Syn.epsW_bGot_hbody
#print axioms Rcic.Syn.epsW_bHBody
#print axioms Rcic.Syn.clw_beta_body_epsW
#print axioms Rcic.Syn.epsW_bDr
#print axioms Rcic.Syn.epsW_instEnd_bEnd
#print axioms Rcic.Syn.clw_beta_reduct_epsW
#print axioms Rcic.Syn.NoInlineEntry
#print axioms Rcic.Syn.noInlineEntry_removeAt
#print axioms Rcic.Syn.noInlineEntry_insertDisp
#print axioms Rcic.Syn.wkInnerGo_eq_removeAt
#print axioms Rcic.Syn.wkInnerDisp_eq_removeAt
#print axioms Rcic.Syn.HasNoInlinePush
#print axioms Rcic.Syn.epsW_eq_eps_noInline
