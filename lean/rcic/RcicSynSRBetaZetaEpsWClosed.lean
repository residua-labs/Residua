import rcic.RcicSynSRBetaZetaEpsWLvl

/-!
# epsW under the closed regime: conservativity + the lift/inst commutation

`TyP.ClosedWf` demands `AssumpCut Γ c` of every `wk`, and the
`AssumpCut` bridge (`wkInnerDisp_eq_removeAt_of_shape`) then makes the
re-frame pass the identity at every `wk` node of a closed-well-formed
derivation. Hence:

* `epsW_eq_eps_closed` — for every `D.ClosedWf` derivation at every shaped
  display, `epsW` **is** `eps`. The whole closed-regime eps corpus
  (`closedAt_eps`, `eps_nil_lift(_zero)`, `eps_nil_inst`) transfers verbatim;
  we register the epsW-named mirrors below.
* `closedAt_epsW(_nil)`, `epsW_nil_lift(_zero)`, `epsW_nil_inst` — the
  subst/lift/inst commutation mirrors, each a one-line consequence.
  `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `removeAt ρ c` is shaped for the `wk`'s child context whenever `ρ` is
    shaped for the parent and `AssumpCut Γ c` holds. -/
theorem assumpCut_dispShape_removeAt {Γ : LCtx} {c : Nat} (ha : AssumpCut Γ c) (d : LocalDecl)
    {ρ : List Disp} (hs : DispShape (insertAt d c Γ) ρ) :
    DispShape Γ (removeAt ρ c) := by
  induction ha generalizing ρ with
  | zero Γ =>
      cases hs with
      | assumptionKeep hs₀ => exact hs₀
      | assumptionDrop hs₀ => exact hs₀
      | letDrop hs₀ => exact hs₀
      | letInline hs₀ => exact hs₀
  | succ A _ ih =>
      rw [insertAt_succ_cons] at hs
      cases hs with
      | assumptionKeep hs₀ => exact .assumptionKeep (ih hs₀)
      | assumptionDrop hs₀ => exact .assumptionDrop (ih hs₀)
      | _ => nomatch hs

/-! ## conservativity under `ClosedWf` -/

/-- **The closed-regime transfer:** for every `ClosedWf` derivation at every
    shaped display, `epsW` **is** `eps` — `ClosedWf`'s `AssumpCut` makes the
    re-frame pass the identity at every `wk` node. The re-frame only bites at
    displays the closed regime never supplies (canonical Entry dispositions
    of let-binding contexts, where the wedge lives). -/
theorem epsW_eq_eps_closed :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.ClosedWf →
    ∀ (σ : Level → Level) (ρ : List Disp), DispShape Γ ρ →
    D.epsW σ ρ = D.eps σ ρ
  | _, _, _, _, _, .sort .., _, _, _, _ => rfl
  | _, _, _, _, _, .bvar .., _, _, _, _ => rfl
  | _, _, _, _, _, .const .., _, _, _, _ => rfl
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, hW, σ, ρ, hs =>
      epsW_eq_eps_closed hexp hW σ ρ hs
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, hW, σ, ρ, hs => epsW_eq_eps_closed h hW σ ρ hs
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, hW, σ, ρ, hs => epsW_eq_eps_closed D hW σ ρ hs
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, hW, σ, ρ, hs =>
      epsW_eq_eps_closed D hW σ ρ (dispShape_cctx hs)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, hW, σ, ρ, hs =>
      epsW_eq_eps_closed D hW _ ρ (dispShape_of_instLvlsCtx ls hs)
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB, hW, σ, ρ, hs => by
      have ihA := epsW_eq_eps_closed hA hW.1 σ ρ hs
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihA, epsW_eq_eps_closed hB hW.2 σ (.drop :: ρ) (.assumptionDrop hs)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihA, epsW_eq_eps_closed hB hW.2 σ (.keep :: ρ) (.assumptionKeep hs)]
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ _ hbody _, hW, σ, ρ, hs => by
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [epsW_eq_eps_closed hbody hW σ (.drop :: ρ) (.assumptionDrop hs)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [epsW_eq_eps_closed hbody hW σ (.keep :: ρ) (.assumptionKeep hs)]
          rfl

  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _, hW, σ, ρ, hs => by
      simp only [TyP.epsW, TyP.eps,
        epsW_eq_eps_closed hf hW.1 σ ρ hs, epsW_eq_eps_closed ha hW.2 σ ρ hs]
      rfl
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, hW, σ, ρ, hs => by
      have e1 : hv.epsW σ ρ = hv.eps σ ρ := epsW_eq_eps_closed hv hW.1 σ ρ hs
      simp only [TyP.epsW, TyP.eps, e1]
      cases hr : hv.eps σ ρ with
      | star =>
          rw [epsW_eq_eps_closed hb hW.2 σ (.drop :: ρ) (.letDrop hs)]
      | _ =>
          exact epsW_eq_eps_closed hb hW.2 σ _ (.letInline hs)
  | _, _, _, _, _, .esub _ _ _ _ _ _ v j u D hget hv _, hW, σ, ρ, hs => by
      have ihv := epsW_eq_eps_closed hv hW.2 σ ρ hs
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [epsW_eq_eps_closed D hW.1 σ (insertDisp .drop j ρ)
            (dispShape_insertDisp_drop v hget hs)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu, ihv]
          rw [epsW_eq_eps_closed D hW.1 σ (insertDisp .keep j ρ)
            (dispShape_insertDisp_keep v hget hs)]
  | _, _, _, _, _, .lsub _ _ _ _ _ _ v j u D hget hv hvT, hW, σ, ρ, hs => by
      rw [lsub_epsW_eq D hget hv hvT, lsub_eps_eq D hget hv hvT]
      rw [epsW_eq_eps_closed hv hW.2.2 σ ρ hs]
      exact epsW_eq_eps_closed D hW.2.1 σ _
        (dispShape_insertDisp_lsub v hW.1 hget hs _ (hv.eps σ ρ))
  | _, _, _, _, _, .wk _ _ _ _ _ d c D, hW, σ, ρ, hs => by
      have hd : wkInnerDisp ρ c = removeAt ρ c :=
        wkInnerDisp_eq_removeAt_of_shape hW.1 d hs
      have ih := epsW_eq_eps_closed D hW.2 σ (removeAt ρ c)
        (assumpCut_dispShape_removeAt hW.1 d hs)
      cases hc : ρ[c]? with
      | none => simp only [TyP.epsW, TyP.eps, hc, hd]; exact ih
      | some dv =>
          cases dv with
          | keep => simp only [TyP.epsW, TyP.eps, hc, hd]; rw [ih]
          | drop => simp only [TyP.epsW, TyP.eps, hc, hd]; exact ih
          | inline v => simp only [TyP.epsW, TyP.eps, hc, hd]; exact ih

/-! ## the closed-regime commutation mirrors -/

/-- `closedAt_eps` at `epsW` (the `epsW` mirror of `closedAt_eps`). -/
theorem closedAt_epsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (hD : D.ClosedWf) (σ : Level → Level)
    {ρ : List Disp} (hs : DispShape Γ ρ) (hc : DispClosed ρ) :
    ETm.ClosedAt (countKeep ρ) (D.epsW σ ρ) := by
  rw [epsW_eq_eps_closed D hD σ ρ hs]
  exact closedAt_eps D hD σ hs hc

/-- Every closed derivation `D : TyP E n [] e T` with `D.ClosedWf` erases at
    `ρ = []` to a closed erased term (`closedAt_eps_nil` mirror). -/
theorem closedAt_epsW_nil {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) :
    ETm.ClosedAt 0 (D.epsW σ []) := by
  rw [epsW_eq_eps_closed D hD σ [] .nil]
  exact closedAt_eps_nil hD σ

/-- The closed erasure is fixed by `ETm.lift c k` (`eps_nil_lift` mirror —
    the **lift** commutation). -/
theorem epsW_nil_lift {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) (c k : Nat) :
    (D.epsW σ []).lift c k = D.epsW σ [] := by
  rw [epsW_eq_eps_closed D hD σ [] .nil]
  exact eps_nil_lift hD σ c k

/-- `c = 0, k = 1` specialization (`eps_nil_lift_zero` mirror). -/
theorem epsW_nil_lift_zero {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) :
    (D.epsW σ []).lift 0 1 = D.epsW σ [] :=
  epsW_nil_lift hD σ 0 1

/-- The closed erasure is fixed by `ETm.inst j r` (`eps_nil_inst` mirror —
    the **inst** commutation). -/
theorem epsW_nil_inst {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) (j : Nat) (r : ETm) :
    ETm.inst j r (D.epsW σ []) = D.epsW σ [] := by
  rw [epsW_eq_eps_closed D hD σ [] .nil]
  exact eps_nil_inst hD σ j r

end Rcic.Syn

#print axioms Rcic.Syn.assumpCut_dispShape_removeAt
#print axioms Rcic.Syn.epsW_eq_eps_closed
#print axioms Rcic.Syn.closedAt_epsW
#print axioms Rcic.Syn.closedAt_epsW_nil
#print axioms Rcic.Syn.epsW_nil_lift
#print axioms Rcic.Syn.epsW_nil_lift_zero
#print axioms Rcic.Syn.epsW_nil_inst
