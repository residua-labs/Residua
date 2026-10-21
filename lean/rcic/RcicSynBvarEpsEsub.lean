import rcic.RcicSynBvarEsub

/-!
# Syntactic sortRow, build step 3ai — the `esub` equations of a bvar

`research/rcic/semantic/S3_ES_ARMS.md` §34. `bvarEpsEsub` consumes
these equations.

A `★` is preserved on both paths: `drop` returns the body, and `keep`
instantiates it (`ETm.inst` fixes `★`). A relevant variable below an
in-range `drop` stays. One at or above an in-range `drop` is the
shifted index. One at or above an in-range `keep` is that index after
`ETm.inst_lift_id` cancels the lift. The hole on `drop` is `★`. The
hole on `keep` is `hv.eps`.

A `keep` strictly above the index is not one of these: `inst` may
change an inlined value. A short list is not either.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

theorem eps_esub_star_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true)
    (h : D.eps σ (insertDisp .drop j ρ) = .star) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_drop hu, h]

theorem eps_esub_star_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false)
    (h : D.eps σ (insertDisp .keep j ρ) = .star) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_keep hu, h]
  rfl

theorem eps_esub_rel_drop_lo {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) (hij : i < j) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .drop j ρ) = resolve (insertDisp .drop j ρ) i) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_esub_drop hu, h, resolve_insertDisp_lo .drop ρ j i hij hlen]

theorem eps_esub_rel_drop_hi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) (hj : j ≤ i) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .drop j ρ) =
      resolve (insertDisp .drop j ρ) (i + 1)) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_esub_drop hu, h, resolve_insertDisp_hi_drop ρ j i hj hlen]

theorem eps_esub_rel_keep_hi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) (hj : j ≤ i) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .keep j ρ) =
      resolve (insertDisp .keep j ρ) (i + 1)) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_esub_keep hu, h, resolve_insertDisp_hi_keep ρ j i hj hlen]
  exact ETm.inst_lift_id (countKeep (ρ.take j)) (hv.eps σ ρ) (resolve ρ i)

theorem eps_esub_hole_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .drop j ρ) = resolve (insertDisp .drop j ρ) j) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_esub_drop hu, h, resolve_insertDisp_drop j ρ hlen]

theorem eps_esub_hole_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .keep j ρ) = resolve (insertDisp .keep j ρ) j) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = hv.eps σ ρ := by
  rw [eps_esub_keep hu, h, resolve_insertDisp_keep j ρ hlen, inst_bvar_hit]

end Rcic.Syn

#print axioms Rcic.Syn.eps_esub_star_drop
#print axioms Rcic.Syn.eps_esub_star_keep
#print axioms Rcic.Syn.eps_esub_rel_drop_lo
#print axioms Rcic.Syn.eps_esub_rel_drop_hi
#print axioms Rcic.Syn.eps_esub_rel_keep_hi
#print axioms Rcic.Syn.eps_esub_hole_drop
#print axioms Rcic.Syn.eps_esub_hole_keep
