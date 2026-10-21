import rcic.RcicSynBelowScoped
import rcic.RcicHostPropTransfer

/-!
# piRow wall, piece A — zero-sort coherence from the scoped BelowC pack (§3.1)

Spec: `research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §3.1 (J line, #7515). Zero-sort
coherence has a direct scoped BIT projection: for `S : ScopedCtx Eₐ E n Γ` and two sortings
`A : sort u`, `A : sort 0`, the enriched derivations' `BitCoh id` (from
`bitCoh_of_allBelowScoped`, `RcicSynBelowScoped`) is definitionally
`levelIsZero u = levelIsZero .zero`, and `levelIsZero_iff` reads `eqN u .zero` off it.
No `TableWF`; the two AP proofs stay visible (`zeroSort_of_allBelowScoped`).

The enrichment's AP theorem (`assumpPref_enrichHasTyT`, `RcicSynEnrich`) keeps its member,
let-context and context AP premises; no `EnvWfT`-fronted AP lemma for
`enrichHasTyT_of_envWfT` is on the tree (`RcicSynP2Shared` records the same). The completed
global `ZeroSortCoherence E n` therefore names those admission adapters
(`EnrichAPAdapters`, quantified over the environment witness that `ZeroSortCoherence` binds
inside) and applies the landed AP theorems to every auxiliary query
(`zeroSortCoherence_of_allBelowScoped`). Nothing here constructs `AllBelowScoped` or the
adapters. `closure_claim = 0`.
-/
set_option autoImplicit false

namespace Rcic.Syn

open Rcic.Declarative Rcic.Declarative.HostProp

/-- §3.1 the scoped BIT projection at one pair of sortings, the two AP proofs explicit:
    `BitCoh id Du D0` is definitionally `levelIsZero u = levelIsZero .zero`. No `TableWF`. -/
theorem zeroSort_of_allBelowScoped {Eₐ E : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) {n : Nat} {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ)
    {A : Expr Nat} {u : Level}
    (hAu : HasTyT E n Γ A (.sort u)) (hA0 : HasTyT E n Γ A (.sort .zero))
    (hAPu : (enrichHasTyT_of_envWfT S.env S.ctx hAu).AssumpPref)
    (hAP0 : (enrichHasTyT_of_envWfT S.env S.ctx hA0).AssumpPref) : eqN u .zero := by
  have hbit : BitCoh id (enrichHasTyT_of_envWfT S.env S.ctx hAu)
      (enrichHasTyT_of_envWfT S.env S.ctx hA0) :=
    bitCoh_of_allBelowScoped hBel S levelHom_id _ _ hAPu hAP0
  exact (levelIsZero_iff u).mp hbit

/-- the admission adapters the enrichment's AP theorem keeps as premises, quantified over the
    environment witness (which `ZeroSortCoherence`'s `EnvWfT E → …` binds inside). -/
structure EnrichAPAdapters (E : ResolvedEnv) (n : Nat) : Prop where
  member : ∀ hW : EnvWfT E, MemberSortP.AssumpPref (memberSortP_of_envWfT hW)
  letCtx : ∀ hW : EnvWfT E, LetCtxConvP.AssumpPref (letCtxConvP_of_envWfT hW (n := n))

/-- AP of every `EnvWfT`-fronted typing enrichment from the adapters: the landed
    `assumpPref_enrichHasTyT` at the landed `assumpPref_enrichCtxWfT` context spine. -/
theorem assumpPref_enrichHasTyT_of_adapters {E : ResolvedEnv} {n : Nat}
    (hAd : EnrichAPAdapters E n) (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (D : HasTyT E n Γ e T) :
    (enrichHasTyT_of_envWfT hW hΓ D).AssumpPref :=
  assumpPref_enrichHasTyT (envClosed_of_envWfT hW) (envExt_refl E)
    (hAd.member hW) (hAd.letCtx hW) _ D
    (assumpPref_enrichCtxWfT (envClosed_of_envWfT hW) (envExt_refl E)
      (hAd.member hW) (hAd.letCtx hW) hΓ)

/-- §3.1 completed global zero-sort coherence from the scoped pack: the ambient environment
    `Eₐ` extends `E`, and every auxiliary query's AP comes from the adapters. -/
theorem zeroSortCoherence_of_allBelowScoped {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl) (hext : EnvExt E Eₐ) {n : Nat}
    (hAd : EnrichAPAdapters E n) : ZeroSortCoherence E n := by
  intro hW Γ A u hΓ hAu hA0
  exact zeroSort_of_allBelowScoped hBel ⟨hW, hext, hΓ⟩ hAu hA0
    (assumpPref_enrichHasTyT_of_adapters hAd hW hΓ hAu)
    (assumpPref_enrichHasTyT_of_adapters hAd hW hΓ hA0)

end Rcic.Syn

#print axioms Rcic.Syn.zeroSort_of_allBelowScoped
#print axioms Rcic.Syn.assumpPref_enrichHasTyT_of_adapters
#print axioms Rcic.Syn.zeroSortCoherence_of_allBelowScoped
