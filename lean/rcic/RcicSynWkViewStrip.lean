import rcic.RcicSynTable
import rcic.RcicSynPack

/-!
# S6 §5 — the `wk` view-strip adapter (the payable fragment)

For the original `H = TyP.wk E n Γ e A d c D` (target context `insertAt d c Γ`) the
source erased context is computed directly, `ρs = removeAt ρ c`, and the original
post-operation is kept: `keep` lifts the source erasure at the original cutoff,
any other disposition keeps it. That view step is `eps_wk_keep` /
`eps_wk_not_keep(_of_ne)` on main, re-exported here as the single-clause
`eps_wk_view`.

The measure side is payable by the lex's right branch: `wk` contributes no atom
(`H.atoms = D.atoms`, transport flattening), and the current unprocessed judgment
weight drops `1 + D.wt → D.wt`, so `LexDM (tyMeas Aw D) (tyMeas Aw H)` — and, with
the kept occurrence table `K` unchanged in order,
`LexDM (K ++ at(D), wt(D)) (K ++ at(H), wt(H))` — are `Prod.Lex.right` steps.

**Unpaid boundary (§5, decided).** `ρs = removeAt ρ c` is handed to the callee as
a plain display list; the adapter never claims it is a rebuilt source canonical
spine (`CtxP`/`DispFor` for the source context stays unsupplied). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `wk` contributes no atom — the occurrence table is unchanged. -/
theorem atoms_wk_eq (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (d : LocalDecl) (c : Nat) (D : TyP E n Γ e A) :
    (TyP.wk E n Γ e A d c D).atoms Aw = D.atoms Aw := rfl

/-- `wk` adds exactly one to the unprocessed judgment weight. -/
theorem wt_wk_eq (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (d : LocalDecl) (c : Nat) (D : TyP E n Γ e A) :
    (TyP.wk E n Γ e A d c D).wt Aw = 1 + D.wt Aw := by
  simp only [TyP.wt]

/-- §5's payable edge at `tyMeas`: same atoms, weight drops `1 + D.wt → D.wt` —
    the lex's right branch. -/
theorem lexDM_wk_view_strip (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP E n Γ e A) :
    LexDM (tyMeas Aw D) (tyMeas Aw (TyP.wk E n Γ e A d c D)) := by
  exact Prod.Lex.right _ (by simp only [TyP.wt]; omega)

/-- The same edge in the §5 occurrence-table shape: `K` kept, unchanged in order. -/
theorem lexDM_wk_view_strip_tbl (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP E n Γ e A)
    (K : List Nat) :
    LexDM (K ++ D.atoms Aw, D.wt Aw)
      (K ++ (TyP.wk E n Γ e A d c D).atoms Aw, (TyP.wk E n Γ e A d c D).wt Aw) := by
  exact Prod.Lex.right _ (by simp only [TyP.wt]; omega)

/-- §5's view step in one clause — `ρs = removeAt ρ c` computed directly: `keep`
    lifts the source erasure at the original cutoff, any other disposition keeps it. -/
theorem eps_wk_view {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp} :
    (TyP.wk E n Γ e A d c D).eps σ ρ =
      (match ρ[c]? with
      | some .keep => (D.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1
      | _ => D.eps σ (removeAt ρ c)) := by
  cases hget : ρ[c]? with
  | none => exact eps_wk_not_keep (.inl hget)
  | some disp =>
      cases disp with
      | keep => exact eps_wk_keep hget
      | drop => exact eps_wk_not_keep (.inr (.inl hget))
      | inline v => exact eps_wk_not_keep (.inr (.inr ⟨v, hget⟩))

/-- §5's adapter: the `wk` view node hands the callee the original `D` under the
    directly-computed source erased context `removeAt ρ c`, a strict `LexDM`
    descent by the right branch, and the original post-operation on the erasure.
    No `DispFor`/canonical-spine claim about `removeAt ρ c` — the unpaid boundary. -/
structure WkViewStrip (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP E n Γ e A)
    {σ : Level → Level} {ρ : List Disp} (K : List Nat) : Prop where
  /-- the measure edge: atoms unchanged, `1 + D.wt → D.wt`. -/
  edge : LexDM (K ++ D.atoms Aw, D.wt Aw)
      (K ++ (TyP.wk E n Γ e A d c D).atoms Aw, (TyP.wk E n Γ e A d c D).wt Aw)
  /-- `keep`: the source erasure is lifted at the original cutoff. -/
  eps_keep : ρ[c]? = some .keep →
      (TyP.wk E n Γ e A d c D).eps σ ρ =
        (D.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1
  /-- any other disposition: the source erasure is kept. -/
  eps_not_keep : ρ[c]? ≠ some .keep →
      (TyP.wk E n Γ e A d c D).eps σ ρ = D.eps σ (removeAt ρ c)

/-- §5's payable adapter holds at every `wk` view node. -/
theorem wkViewStrip (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {d : LocalDecl} {c : Nat} (D : TyP E n Γ e A)
    {σ : Level → Level} {ρ : List Disp} (K : List Nat) :
    WkViewStrip Aw (d := d) (c := c) D (σ := σ) (ρ := ρ) K :=
  ⟨lexDM_wk_view_strip_tbl Aw D K, eps_wk_keep, eps_wk_not_keep_of_ne⟩

#print axioms Rcic.Syn.lexDM_wk_view_strip
#print axioms Rcic.Syn.lexDM_wk_view_strip_tbl
#print axioms Rcic.Syn.eps_wk_view
#print axioms Rcic.Syn.wkViewStrip

end Rcic.Syn
