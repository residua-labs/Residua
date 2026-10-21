import rcic.RcicSynBvarEsub
import rcic.RcicERScope0

/-!
# Syntactic sortRow, build step 3aj — the `lsub` equations of a bvar

`research/rcic/semantic/S3_ES_ARMS.md` §35. `bvarEpsLsub` consumes
these equations.

`lsub` inserts `drop` when the value erases to `★`, and
`inline (hv.eps)` otherwise. A `★` body is preserved on both paths.
A relevant variable below an in-range hole stays. One at or above an
in-range `drop` or `inline` is the shifted index. The hole on `drop`
is `★`. The hole on `inline` is the value lifted at cutoff 0 by the
newer `keep`s, which is not `resolve ρ i`.

A short list is not one of these. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

theorem eps_lsub_ne_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : ¬ hv.eps σ ρ = .star) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) := by
  rw [eps_lsub]
  split
  · rename_i hEq
    exact absurd hEq hne
  · rfl

theorem eps_lsub_star_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hve : hv.eps σ ρ = .star)
    (h : D.eps σ (insertDisp .drop j ρ) = .star) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_lsub, hve, h]

theorem eps_lsub_star_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : ¬ hv.eps σ ρ = .star)
    (h : D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) = .star) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_lsub_ne_star hne, h]

theorem eps_lsub_rel_drop_lo {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hve : hv.eps σ ρ = .star) (hlo : i < j) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .drop j ρ) = resolve (insertDisp .drop j ρ) i) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_lsub, hve, h, resolve_insertDisp_lo .drop ρ j i hlo hlen]

theorem eps_lsub_rel_inline_lo {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : ¬ hv.eps σ ρ = .star) (hlo : i < j) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) =
      resolve (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) i) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_lsub_ne_star hne, h,
    resolve_insertDisp_lo (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) ρ j i hlo hlen]

theorem eps_lsub_rel_drop_hi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hve : hv.eps σ ρ = .star) (hj : j ≤ i) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .drop j ρ) =
      resolve (insertDisp .drop j ρ) (i + 1)) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_lsub, hve, h, resolve_insertDisp_hi_drop ρ j i hj hlen]

theorem eps_lsub_rel_inline_hi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j i : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : ¬ hv.eps σ ρ = .star) (hj : j ≤ i) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) =
      resolve (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) (i + 1)) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = resolve ρ i := by
  rw [eps_lsub_ne_star hne, h,
    resolve_insertDisp_hi_inline ρ j i (localize (countKeep (ρ.take j)) (hv.eps σ ρ)) hj hlen]

theorem eps_lsub_hole_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hve : hv.eps σ ρ = .star) (hlen : j ≤ ρ.length)
    (h : D.eps σ (insertDisp .drop j ρ) = resolve (insertDisp .drop j ρ) j) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star := by
  rw [eps_lsub, hve, h, resolve_insertDisp_drop j ρ hlen]

theorem eps_lsub_hole_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : ¬ hv.eps σ ρ = .star) (hlen : j ≤ ρ.length)
    (hscope : AvoidPrefix (countKeep (ρ.take j)) 0 (hv.eps σ ρ))
    (h : D.eps σ (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) =
      resolve (insertDisp (.inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ))) j ρ) j) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      hv.eps σ ρ := by
  rw [eps_lsub_ne_star hne, h,
    resolve_insertDisp_inline j (localize (countKeep (ρ.take j)) (hv.eps σ ρ)) ρ hlen]
  exact restore_eq _ _ hscope

end Rcic.Syn

#print axioms Rcic.Syn.eps_lsub_ne_star
#print axioms Rcic.Syn.eps_lsub_star_drop
#print axioms Rcic.Syn.eps_lsub_star_inline
#print axioms Rcic.Syn.eps_lsub_rel_drop_lo
#print axioms Rcic.Syn.eps_lsub_rel_drop_hi
#print axioms Rcic.Syn.eps_lsub_rel_inline_lo
#print axioms Rcic.Syn.eps_lsub_rel_inline_hi
#print axioms Rcic.Syn.eps_lsub_hole_drop
#print axioms Rcic.Syn.eps_lsub_hole_inline
