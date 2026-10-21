import rcic.RcicSynBvarWk

/-!
# Syntactic sortRow, build step 3ag — the `wk` equations of a bvar

`research/rcic/semantic/S3_ES_ARMS.md` §32. `eps_wk_star` already sends a
`★` through `TyP.wk`. These four equations are the relevant case.

`removeAt ρ c` is the inner disposition list (`RcicSynBvarWk`). Below the
cutoff the index is unchanged, and a non-`keep` does not lift, so the
outer erasure is `resolve ρ i`. At or above the cutoff a `drop` or an
`inline` leaves the erased index, and a `keep` is one `ETm.lift` at
`countKeep (ρ.take c)`.

A `keep` strictly above the index is not one of these: the lift moves an
inlined value, and that is not `resolve ρ i`. A missing entry at or above
the cutoff is not either. `bvarEpsWk` returns `other` on both.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A relevant variable below the cutoff. The inserted disposition is not
    a `keep`, so `wk` does not lift, and `resolve` is unchanged. -/
theorem eps_wk_rel_lo {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c i : Nat} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp}
    (hlo : i < c)
    (hnk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (h : D.eps σ (removeAt ρ c) = resolve (removeAt ρ c) i) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = resolve ρ i := by
  rw [eps_wk_not_keep hnk, h, resolve_removeAt_lo ρ c i hlo]

/-- A relevant variable at or above a `drop`. The outer index is one
    larger, and the erased index is the inner one. -/
theorem eps_wk_rel_hi_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c i₀ : Nat} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp}
    (hc : c ≤ i₀) (hk : ρ[c]? = some .drop)
    (h : D.eps σ (removeAt ρ c) = resolve (removeAt ρ c) i₀) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = resolve ρ (i₀ + 1) := by
  rw [eps_wk_not_keep (Or.inr (Or.inl hk)), h,
    resolve_removeAt_hi_drop ρ c i₀ hc hk]

/-- A relevant variable at or above an `inline`. Same index as `drop`. -/
theorem eps_wk_rel_hi_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c i₀ : Nat} {v : ETm} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp}
    (hc : c ≤ i₀) (hk : ρ[c]? = some (.inline v))
    (h : D.eps σ (removeAt ρ c) = resolve (removeAt ρ c) i₀) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = resolve ρ (i₀ + 1) := by
  rw [eps_wk_not_keep (Or.inr (Or.inr ⟨v, hk⟩)), h,
    resolve_removeAt_hi_inline ρ c i₀ v hc hk]

/-- A relevant variable at or above a `keep`. The outer erasure is the
    inner erasure lifted at `countKeep` of the prefix. -/
theorem eps_wk_rel_hi_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c i₀ : Nat} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp}
    (hc : c ≤ i₀) (hk : ρ[c]? = some .keep)
    (h : D.eps σ (removeAt ρ c) = resolve (removeAt ρ c) i₀) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = resolve ρ (i₀ + 1) := by
  rw [eps_wk_keep hk, h, resolve_removeAt_hi_keep ρ c i₀ hc hk]

end Rcic.Syn

#print axioms Rcic.Syn.eps_wk_rel_lo
#print axioms Rcic.Syn.eps_wk_rel_hi_drop
#print axioms Rcic.Syn.eps_wk_rel_hi_inline
#print axioms Rcic.Syn.eps_wk_rel_hi_keep
