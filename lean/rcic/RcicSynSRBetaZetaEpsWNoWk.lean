import rcic.RcicSynSRBetaZetaEpsW

/-!
# epsW blast radius, transfer 2: derivations with no `wk` node

`epsW` differs from `TyP.eps` in exactly one arm: `wk` over an inserted
`keep` runs the inner erasure at `wkInnerDisp ρ c` (inline values re-framed)
instead of `removeAt ρ c`. A derivation that contains no `TyP.wk`
constructor at all therefore erases identically under both — no condition on
the display, `letE`/`lsub` pushes included. This is the transfer lemma the
blast-radius table applies to the landed iota/`lsub`/`esub` fixture pins
(`RcicSynVecConsIota`, `RcicSynNatSuccIota`, `RcicSynListConsIota`,
`RcicSynStepFieldsDeltaIota`, `RcicERLsubInlineScope`: all `TyP.wk`-free),
complementing `epsW_eq_eps_noInline` (display-side transfer). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A derivation with no `TyP.wk` constructor. -/
inductive NoWk : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Prop
  | sort {E n Γ l k h} : NoWk (.sort E n Γ l k h)
  | bvar {E n Γ i A u h hA} : NoWk (.bvar E n Γ i A u h hA)
  | const {E n Γ r ls ls₀ m u hres hlen hwf hls hT} (hT' : NoWk hT) :
      NoWk (.const E n Γ r ls ls₀ m u hres hlen hwf hls hT)
  | pi {E n Γ A u B v hA hB} (h1 : NoWk hA) (h2 : NoWk hB) :
      NoWk (.pi E n Γ A u B v hA hB)
  | lam {E n Γ A u body B v hA hbody hB} (h1 : NoWk hA) (h2 : NoWk hbody)
      (h3 : NoWk hB) : NoWk (.lam E n Γ A u body B v hA hbody hB)
  | app {E n Γ f a A B w hf ha hT} (h1 : NoWk hf) (h2 : NoWk ha) (h3 : NoWk hT) :
      NoWk (.app E n Γ f a A B w hf ha hT)
  | letE {E n Γ A u value B body w hA hv hb hT} (h1 : NoWk hA) (h2 : NoWk hv)
      (h3 : NoWk hb) (h4 : NoWk hT) :
      NoWk (.letE E n Γ A u value B body w hA hv hb hT)
  | lit {E n Γ t T hexp} (h : NoWk hexp) : NoWk (.lit E n Γ t T hexp)
  | conv {E n Γ e A B u h hc} (h' : NoWk h) : NoWk (.conv E n Γ e A B u h hc)
  | esub {E n Γ e A t v j u D hget hv hvT} (h1 : NoWk D) (h2 : NoWk hv)
      (h3 : NoWk hvT) : NoWk (.esub E n Γ e A t v j u D hget hv hvT)
  | lsub {E n Γ e A t v j u D hget hv hvT} (h1 : NoWk D) (h2 : NoWk hv)
      (h3 : NoWk hvT) : NoWk (.lsub E n Γ e A t v j u D hget hv hvT)
  | linst {E a n Γ e A ls hls hlen D} (h : NoWk D) :
      NoWk (.linst E a n Γ e A ls hls hlen D)
  | ewk {E₀ E n Γ e A hext D} (h : NoWk D) : NoWk (.ewk E₀ E n Γ e A hext D)
  | cctx {E n Γ e T A A' u D hA} (h1 : NoWk D) :
      NoWk (.cctx E n Γ e T A A' u D hA)

/-- Transfer 2: on a derivation with no `wk` node, `epsW` is exactly `eps`
    at every display (`letE`/`lsub` inline pushes included). -/
theorem epsW_eq_eps_noWk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D : TyP E n Γ e T} (hD : NoWk D) :
    ∀ (σ : Level → Level) (ρ : List Disp), D.epsW σ ρ = D.eps σ ρ := by
  induction hD with
  | sort => intro σ ρ; rfl
  | bvar => intro σ ρ; rfl
  | const _ ih => intro σ ρ; simp only [TyP.epsW, TyP.eps, ih σ ρ]; rfl
  | @pi E n Γ A u B v hA hB _ _ ihA ihB =>
      intro σ ρ
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihA σ ρ, ihB σ (.drop :: ρ)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihA σ ρ, ihB σ (.keep :: ρ)]
  | @lam E n Γ A u body B v hA hbody hB _ _ _ ihA ihBody ihB =>
      intro σ ρ
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihBody σ (.drop :: ρ)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihBody σ (.keep :: ρ)]
          rfl
  | app _ _ _ ihf iha ihT =>
      intro σ ρ
      simp only [TyP.epsW, TyP.eps, ihf σ ρ, iha σ ρ]
      rfl
  | @letE E n Γ A u value B body w hA hv hb hT _ _ _ _ ihA ihv ihb ihT =>
      intro σ ρ
      have e1 : hv.epsW σ ρ = hv.eps σ ρ := ihv σ ρ
      cases hr : hv.eps σ ρ with
      | star =>
          simp only [TyP.epsW, TyP.eps, e1.trans hr, hr]
          exact ihb σ (.drop :: ρ)
      | _ =>
          simp only [TyP.epsW, TyP.eps, e1.trans hr, hr]
          exact ihb σ (.inline _ :: ρ)
  | lit _ ih => intro σ ρ; exact ih σ ρ
  | conv _ ih => intro σ ρ; exact ih σ ρ
  | ewk _ ih => intro σ ρ; exact ih σ ρ
  | cctx _ ih => intro σ ρ; exact ih σ ρ
  | linst _ ih => intro σ ρ; simp only [TyP.epsW, TyP.eps, ih _ ρ]
  | @esub E n Γ e A t v j u D hget hv hvT _ _ _ ihD ihv ihvT =>
      intro σ ρ
      cases hu : levelIsZero (σ u) with
      | true =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihD σ (insertDisp .drop j ρ)]
      | false =>
          simp only [TyP.epsW, TyP.eps, hu]
          rw [ihv σ ρ, ihD σ (insertDisp .keep j ρ)]
  | @lsub E n Γ e A t v j u D hget hv hvT _ _ _ ihD ihv ihvT =>
      intro σ ρ
      have e1 : hv.epsW σ ρ = hv.eps σ ρ := ihv σ ρ
      cases hr : hv.eps σ ρ with
      | star =>
          simp only [TyP.epsW, TyP.eps, e1.trans hr, hr]
          exact ihD σ (insertDisp .drop j ρ)
      | _ =>
          simp only [TyP.epsW, TyP.eps, e1.trans hr, hr]
          exact ihD σ _

end Rcic.Syn

#print axioms Rcic.Syn.NoWk
#print axioms Rcic.Syn.epsW_eq_eps_noWk
