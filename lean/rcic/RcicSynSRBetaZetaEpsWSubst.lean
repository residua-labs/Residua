import rcic.RcicSynSRBetaZetaEpsWClosed
import rcic.RcicSynES

/-!
# epsW subst commutation + the `ESW` transport layer

Part A (**subst** commutation): `epsW_tyCast`, `epsW_castLift0`,
`epsW_esub_keep/drop`, and `instEnd_epsW_drop/keep` — the mirrors of the
landed `instEnd_eps_drop/keep` (β-substitution at the end), which is what
the sortRow `es_beta`/`es_fsub` rows consume.

Part B (the `ESW` transports — the CL/ConvMod lemmas `step_of_suppliers`
closes its five transport cases by): `esW_ewk/cctx/linst/esub_drop/
esub_keep/wk_not_keep/wk_keep` and the recursion `esW_transports`. The
`wk` transport reads its child at `wkInnerDisp ρ c` — the honest display
under `epsW`. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## Part A: subst commutation at `instEnd` -/

theorem epsW_tyCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T') (D : TyP E n Γ e T)
    (σ : Level → Level) (ρ : List Disp) :
    (tyCast he hT D).epsW σ ρ = D.epsW σ ρ := by
  cases he
  cases hT
  rfl

theorem epsW_castLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {v t : Expr Nat}
    (D : TyP E n Γ v t) (σ : Level → Level) (ρ : List Disp) :
    (castLift0 D).epsW σ ρ = D.epsW σ ρ :=
  epsW_tyCast _ _ D σ ρ

theorem epsW_esub_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = false) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).epsW σ ρ =
      ETm.inst (countKeep (ρ.take j)) (hv.epsW σ ρ) (D.epsW σ (insertDisp .keep j ρ)) := by
  simp only [TyP.epsW, hu]

theorem epsW_esub_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).epsW σ ρ =
      D.epsW σ (insertDisp .drop j ρ) := by
  simp only [TyP.epsW, hu]

/-- The `instEnd_eps_drop` mirror: β-substitution at the end, proof-sort
    domain (`instEnd_epsW_drop`). -/
theorem instEnd_epsW_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) :
    (instEnd hB hv hA).epsW σ ρ = hB.epsW σ (.drop :: ρ) := by
  rw [instEnd, epsW_tyCast]
  rw [epsW_esub_drop (hu := hu), insertDisp_zero]

/-- The `instEnd_eps_keep` mirror: relevant-sort domain
    (`instEnd_epsW_keep`). -/
theorem instEnd_epsW_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) :
    (instEnd hB hv hA).epsW σ ρ =
      ETm.inst 0 (hv.epsW σ ρ) (hB.epsW σ (.keep :: ρ)) := by
  rw [instEnd, epsW_tyCast]
  rw [epsW_esub_keep (hu := hu), insertDisp_zero, List.take_zero, epsW_castLift0]
  rfl

/-! ## Part B: the `ESW` transports -/

/-- `es_ewk` mirror at `ESW`. -/
theorem esW_ewk {tbl : List CRule} {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {hext : EnvExt E₀ E} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E₀ n Γ a b T) (ih : ESW tbl σ ρ h) :
    ESW tbl σ ρ (CvP.ewk E₀ E n Γ a b T hext h) := by
  simpa [ESW, CvP.dl, CvP.dr] using ih

/-- `es_cctx` mirror at `ESW`. -/
theorem esW_cctx {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T A A' : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n (.assumption A :: Γ) a b T) (hA : CvP E n Γ A A' (.sort u))
    (ih : ESW tbl σ ρ h) :
    ESW tbl σ ρ (CvP.cctx E n Γ a b T A A' u h hA) := by
  simpa [ESW, CvP.dl, CvP.dr] using ih

/-- `es_linst` mirror at `ESW`. -/
theorem esW_linst {tbl : List CRule} {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {ls : List Level} {hls : levelsBounded n ls = true}
    {hlen : ls.length = a'} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E a' Γ a b T)
    (ih : ESW tbl (fun l => σ (instLevel ls l)) ρ h) :
    ESW tbl σ ρ (CvP.linst E a' n Γ a b T ls hls hlen h) := by
  simpa [ESW, CvP.dl, CvP.dr] using ih

/-- `es_esub_drop` mirror at `ESW`. -/
theorem esW_esub_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T t v : Expr Nat} {j : Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hu : levelIsZero (σ u) = true)
    (ih : ESW tbl σ (insertDisp .drop j ρ) h) :
    ESW tbl σ ρ (CvP.esub E n Γ a b T t v j u h hget hv hvT) := by
  simpa [ESW, CvP.dl, CvP.dr, epsW_esub_drop (D := h.dl) hu, epsW_esub_drop (D := h.dr) hu]
    using ih

/-- `es_esub_keep` mirror at `ESW`. -/
theorem esW_esub_keep {tbl : List CRule} (hcl : TableClosed tbl) {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {a b T t v : Expr Nat} {j : Nat} {u : Level}
    {σ : Level → Level} {ρ : List Disp} (h : CvP E n Γ a b T)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hu : levelIsZero (σ u) = false)
    (ih : ESW tbl σ (insertDisp .keep j ρ) h) :
    ESW tbl σ ρ (CvP.esub E n Γ a b T t v j u h hget hv hvT) := by
  have ih' : ConvMod (EStep tbl) LvlEq
      (h.dl.epsW σ (insertDisp .keep j ρ)) (h.dr.epsW σ (insertDisp .keep j ρ)) := ih
  simpa [ESW, CvP.dl, CvP.dr, epsW_esub_keep (D := h.dl) hu, epsW_esub_keep (D := h.dr) hu]
    using convMod_inst_body hcl ih' (countKeep (ρ.take j)) (hv.epsW σ ρ)

/-- `es_wk_not_keep` mirror at `ESW`. -/
theorem esW_wk_not_keep {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b T)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (ih : ESW tbl σ (removeAt ρ c) h) :
    ESW tbl σ ρ (CvP.wk E n Γ a b T d c h) := by
  simpa [ESW, CvP.dl, CvP.dr, epsW_wk_not_keep (D := h.dl) hk, epsW_wk_not_keep (D := h.dr) hk]
    using ih

/-- `es_wk_keep` mirror at `ESW`: the keep case lifts the child's `ESW` —
    read at `wkInnerDisp ρ c`, the honest display under `epsW`. -/
theorem esW_wk_keep {tbl : List CRule} (hcl : TableClosed tbl) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level}
    {ρ : List Disp} (h : CvP E n Γ a b T) (hk : ρ[c]? = some .keep)
    (ih : ESW tbl σ (wkInnerDisp ρ c) h) :
    ESW tbl σ ρ (CvP.wk E n Γ a b T d c h) := by
  have ih' : ConvMod (EStep tbl) LvlEq
      (h.dl.epsW σ (wkInnerDisp ρ c)) (h.dr.epsW σ (wkInnerDisp ρ c)) := ih
  simpa [ESW, CvP.dl, CvP.dr, epsW_wk_keep (D := h.dl) hk, epsW_wk_keep (D := h.dr) hk]
    using convMod_lift hcl ih' (countKeep (ρ.take c)) 1

/-- `es_transports` mirror at `ESW`: `ESW` of any derivation follows from
    `ESW` of its rule nodes, at the `(σ, ρ)` the transports compute — with
    the `wk` child read at `wkInnerDisp ρ c`. -/
theorem esW_transports (tbl : List CRule) (hcl : TableClosed tbl)
    (k : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (h : CvP E n Γ a b T), h.isTransport = false →
        ∀ (σ : Level → Level) (ρ : List Disp), ESW tbl σ ρ h) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
      (h : CvP E n Γ a b T) → (σ : Level → Level) → (ρ : List Disp) →
        ESW tbl σ ρ h
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ c h, σ, ρ =>
      match hρ : ρ[c]? with
      | none => esW_wk_not_keep h (Or.inl hρ)
          (esW_transports tbl hcl k h σ (removeAt ρ c))
      | some .keep =>
          esW_wk_keep hcl h hρ (esW_transports tbl hcl k h σ (wkInnerDisp ρ c))
      | some .drop =>
          esW_wk_not_keep h (Or.inr (Or.inl hρ))
            (esW_transports tbl hcl k h σ (removeAt ρ c))
      | some (.inline v) =>
          esW_wk_not_keep h (Or.inr (Or.inr ⟨v, hρ⟩))
            (esW_transports tbl hcl k h σ (removeAt ρ c))
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ j u h hget hv hvT, σ, ρ =>
      match hu : levelIsZero (σ u) with
      | true => esW_esub_drop h hget hv hvT hu
          (esW_transports tbl hcl k h σ (insertDisp .drop j ρ))
      | false => esW_esub_keep hcl h hget hv hvT hu
          (esW_transports tbl hcl k h σ (insertDisp .keep j ρ))
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ ls _ _ h, σ, ρ =>
      esW_linst h (esW_transports tbl hcl k h (fun l => σ (instLevel ls l)) ρ)
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h, σ, ρ =>
      esW_ewk h (esW_transports tbl hcl k h σ ρ)
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA, σ, ρ =>
      esW_cctx h hA (esW_transports tbl hcl k h σ ρ)
  | _, _, _, _, _, _, .refl E n Γ a A ht dl dr, σ, ρ =>
      k (CvP.refl E n Γ a A ht dl dr) rfl σ ρ
  | _, _, _, _, _, _, .symm E n Γ a b A h dl dr, σ, ρ =>
      k (CvP.symm E n Γ a b A h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .trans E n Γ a b c A h1 h2 dl dr, σ, ρ =>
      k (CvP.trans E n Γ a b c A h1 h2 dl dr) rfl σ ρ
  | _, _, _, _, _, _, .beta E n Γ A body arg B u hA hbody harg dl dr, σ, ρ =>
      k (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl σ ρ
  | _, _, _, _, _, _, .zeta E n Γ A value body B u hA hv hb dl dr, σ, ρ =>
      k (CvP.zeta E n Γ A value body B u hA hv hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .zetaLocal E n Γ i A v hval hty hv dl dr, σ, ρ =>
      k (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) rfl σ ρ
  | _, _, _, _, _, _, .delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr, σ, ρ =>
      k (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .iota E n Γ lhs rhs T h hlhs hrhs dl dr, σ, ρ =>
      k (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) rfl σ ρ
  | _, _, _, _, _, _, .lit E n Γ t exp T h hexp dl dr, σ, ρ =>
      k (CvP.lit E n Γ t exp T h hexp dl dr) rfl σ ρ
  | _, _, _, _, _, _, .app E n Γ f g a b A B h1 h2 dl dr, σ, ρ =>
      k (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl σ ρ
  | _, _, _, _, _, _, .lam E n Γ A A' b b' B u hA hb dl dr, σ, ρ =>
      k (CvP.lam E n Γ A A' b b' B u hA hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .pi E n Γ A A' B B' u v hA hB dl dr, σ, ρ =>
      k (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl σ ρ
  | _, _, _, _, _, _, .letE E n Γ A A' v v' b b' B u hA hv hb dl dr, σ, ρ =>
      k (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .sorts E n Γ l₁ l₂ h dl dr, σ, ρ =>
      k (CvP.sorts E n Γ l₁ l₂ h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr, σ, ρ =>
      k (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .eta E n Γ f A B h dl dr, σ, ρ =>
      k (CvP.eta E n Γ f A B h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .irr E n Γ P p q hP hp hq dl dr, σ, ρ =>
      k (CvP.irr E n Γ P p q hP hp hq dl dr) rfl σ ρ
  | _, _, _, _, _, _, .tyConv E n Γ a b A A' u h hA dl dr, σ, ρ =>
      k (CvP.tyConv E n Γ a b A A' u h hA dl dr) rfl σ ρ
  | _, _, _, _, _, _, .fsub E n Γ A B S a b u hB hA hab dl dr, σ, ρ =>
      k (CvP.fsub E n Γ A B S a b u hB hA hab dl dr) rfl σ ρ

end Rcic.Syn

#print axioms Rcic.Syn.epsW_tyCast
#print axioms Rcic.Syn.epsW_castLift0
#print axioms Rcic.Syn.epsW_esub_keep
#print axioms Rcic.Syn.epsW_esub_drop
#print axioms Rcic.Syn.instEnd_epsW_drop
#print axioms Rcic.Syn.instEnd_epsW_keep
#print axioms Rcic.Syn.esW_ewk
#print axioms Rcic.Syn.esW_cctx
#print axioms Rcic.Syn.esW_linst
#print axioms Rcic.Syn.esW_esub_drop
#print axioms Rcic.Syn.esW_esub_keep
#print axioms Rcic.Syn.esW_wk_not_keep
#print axioms Rcic.Syn.esW_wk_keep
#print axioms Rcic.Syn.esW_transports
