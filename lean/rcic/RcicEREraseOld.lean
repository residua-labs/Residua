import rcic.RcicSynErase

/-!
# R2 audit: frozen copy of the pre-R2 `TyP.eps` (`RcicEREraseOld`)

S12 option (a) + S13_R2_SCOPE_AMENDMENT §6 require the ER1/ER2 kernel pins to be
kept **frozen against the old erasure** after the in-place `TyP.eps` switch, so
the counterexample values remain kernel-checkable on the same head as the fix.

`TyP.epsOld` is the pre-switch erasure verbatim, with exactly two differences
from current `TyP.eps`:

* **proof-domain Π codomain** (`levelIsZero (σ u) = true`): the codomain is
  erased at `.drop :: ρ` *without* the `piSlot` pad — `Dw`/`Dd`'s
  `W-ERASURE-PI-DROP-WK` mismatch (`pi (bvar 1) (bvar 0)` vs `pi (bvar 1) (bvar 1)`).
* **`lsub` non-star payload**: the erased value `r` is inlined raw — `W-ERASURE-LSUB-INLINE-SCOPE`'s
  double lift (`bvar 2`) — instead of `localize (countKeep (ρ.take j)) r`.

`CLold` is `CL` with `epsOld` on both sides. Nothing here is used by
production: it exists so the frozen pins and the new positive pins
(`*_eps_fixed`, `cl_pi_drop_wk`, `cl_lsub_inline_scope`) live under one root.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Frozen pre-R2 erasure — identical to `TyP.eps` except the proof-domain
    Π codomain is **not** `piSlot`-padded and the `lsub` non-star payload is
    **not** `localize`d. Audit-only. -/
def TyP.epsOld (σ : Level → Level) (ρ : List Disp) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
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
      | true => ETm.pi (hA.epsOld σ ρ) (hB.epsOld σ (.drop :: ρ))
      | false => ETm.pi (hA.epsOld σ ρ) (hB.epsOld σ (.keep :: ρ))
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ _ hbody _ =>
      match levelIsZero (σ u) with
      | true => hbody.epsOld σ (.drop :: ρ)
      | false =>
          match hbody.epsOld σ (.keep :: ρ) with
          | .star => ETm.star
          | eb => ETm.lam eb
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ =>
      match hf.epsOld σ ρ with
      | .star => ETm.star
      | ef =>
          match ha.epsOld σ ρ with
          | .star => ef
          | ea => ETm.app ef ea
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ =>
      match hv.epsOld σ ρ with
      | .star => hb.epsOld σ (.drop :: ρ)
      | ev => hb.epsOld σ (.inline ev :: ρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.epsOld σ ρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.epsOld σ ρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D =>
      let inner := D.epsOld σ (removeAt ρ c)
      match ρ[c]? with
      | some .keep => inner.lift (countKeep (ρ.take c)) 1
      | _ => inner
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _ =>
      match levelIsZero (σ u) with
      | true => D.epsOld σ (insertDisp .drop j ρ)
      | false =>
          ETm.inst (countKeep (ρ.take j)) (hv.epsOld σ ρ) (D.epsOld σ (insertDisp .keep j ρ))
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D _ hv _ =>
      match hv.epsOld σ ρ with
      | .star => D.epsOld σ (insertDisp .drop j ρ)
      | r => D.epsOld σ (insertDisp (.inline r) j ρ)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D =>
      D.epsOld (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.epsOld σ ρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.epsOld σ ρ

/-- `CL` against the frozen erasure: `ConvMod (EStep tbl) LvlEq` of the two
    `epsOld`s — same demand shape as `CL`, audit-only. -/
def CLold (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D₁ D₂ : TyP E n Γ e T) : Prop :=
  ConvMod (EStep tbl) LvlEq (D₁.epsOld σ ρ) (D₂.epsOld σ ρ)

end Rcic.Syn

#print axioms Rcic.Syn.TyP.epsOld
#print axioms Rcic.Syn.CLold
