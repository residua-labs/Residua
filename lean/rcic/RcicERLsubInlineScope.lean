import rcic.RcicSynInlineRefute
import rcic.RcicEREraseOld
import rcic.RcicSynSpineComb
import rcic.RcicSynLetInline
import rcic.RcicSynCLFromBelow

/-!
# Kernel check — ER2 counterexample W-ERASURE-LSUB-INLINE-SCOPE (ChatGPT S13)

Kernel-check of the ER2 counterexample
(`research/rcic/sortrow/S13_ERASURE_TRANSPORT_AUDIT.md` §ER2, PR #7367).
A nonzero-cutoff `TyP.lsub` inlines `hv.eps` — which already lives in the
*target* context `Δ` — at source position `j`, and `resolve` then lifts it
again by the keeps in the prefix (`eps_lsub_hole_inline`'s
`countKeep (ρ.take j)`). The actual replacement value is `bvar 1`; the
lsub erases to `bvar 2`.

Objects (`E = emptyEnv`, `n = 0`, `S = sort zero`, all indices newest-first):
- `Γ = [.assumption S, .letBinding S (.bvar 0), .assumption S]`
  (`[X : S, z : S := P, P : S]`, canonical display
  `[keep, inline (bvar 0), keep]`),
- `Δ = [.assumption S, .assumption S]` (`[X : S, P : S]`, display
  `[keep, keep]`),
- `D : Γ ⊢ bvar 1 : S` (the let-bound slot `z`, direct `bvar`),
- `hv : Δ ⊢ bvar 1 : S` (the actual replacement `lift 0 1 v`, direct `bvar`),
- `hvT : Δ ⊢ S : sort (succ zero)` (direct `sort`),
- `L := TyP.lsub … (.bvar 1) S S (.bvar 0) 1 (.succ .zero) D rfl hv hvT`.

Sealed:
1. Native `CtxWfT` of `Γ` and `Δ` (the let entry really carries `P : S`).
2. `AssumpPref` of `D`, `hv`, `L` — `Γ.take 1 = [.assumption S]`, so the
   `j = 1` lsub is a *legal* public AP input; no `j = 0` anywhere.
3. `CtxP.disp id` of the canonical enriched contexts gives
   `ρΓ = [.keep, .inline (.bvar 0), .keep]`, `ρΔ = [.keep, .keep]`.
4. `D.eps id ρΓ = bvar 1`, `hv.eps id ρΔ = bvar 1`, `L.eps id ρΔ = bvar 2`
   (by `decide`).
5. `no_cl_lsub_inline_scope`: `¬ CL tbl id [.keep,.keep] L hv` for every
   `TableWF tbl` — directly `not_convMod_bvar_ne`, no Π-injectivity.

`closure_claim` stays 0. Any kernel deviation from these values is reported
verbatim, never adjusted.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `S`: every entry's type — `sort zero`. -/
abbrev er2S : Expr Nat := .sort .zero

/-- `Γ = [.assumption S, .letBinding S (.bvar 0), .assumption S]`
    (`[X : S, z : S := P, P : S]`, newest-first). -/
abbrev er2Γ : LCtx := [.assumption er2S, .letBinding er2S (.bvar 0), .assumption er2S]

/-- `Δ = [.assumption S, .assumption S]` (`[X : S, P : S]`) —
    `substRemove (.bvar 0) 1 er2Γ` reduces to this. -/
abbrev er2Δ : LCtx := [.assumption er2S, .assumption er2S]

/-! ## §1 native context well-formedness -/

/-- `Δ` is natively well formed. -/
def er2Δ_wf : CtxWfT emptyEnv 0 er2Δ :=
  .assumption _ _ _ (.assumption _ _ _ .nil (.sort _ _)) (.sort _ _)

/-- `Γ` is natively well formed; the let entry's value `bvar 0 : S` is the
    innermost assumption. -/
def er2Γ_wf : CtxWfT emptyEnv 0 er2Γ :=
  .assumption _ _ _
    (.letBinding _ _ _ _
      (.assumption _ _ _ .nil (.sort _ _))
      (.sort _ _)
      (.bvar _ _ _ rfl))
    (.sort _ _)

/-! ## §2 enriched contexts and canonical displays -/

/-- `P : S` as `.bvar 0` in the innermost prefix — the let's value typing. -/
def er2P_ty : TyP emptyEnv 0 [.assumption er2S] (.bvar 0) er2S :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- Canonical enriched context over `Γ`. -/
def er2ΓP : CtxP emptyEnv 0 er2Γ :=
  .assumption _ _ _ _ _
    (.letBinding _ _ _ _ _ _
      (.assumption _ _ _ _ _ (.nil _ _)
        (.sort _ _ _ _ _ (eqN_refl _)))
      (.sort _ _ _ _ _ (eqN_refl _))
      er2P_ty)
    (.sort _ _ _ _ _ (eqN_refl _))

/-- Canonical enriched context over `Δ`. -/
def er2ΔP : CtxP emptyEnv 0 er2Δ :=
  .assumption _ _ _ _ _
    (.assumption _ _ _ _ _ (.nil _ _)
      (.sort _ _ _ _ _ (eqN_refl _)))
    (.sort _ _ _ _ _ (eqN_refl _))

/-- `Γ`'s canonical display: keep, inline the erased let value, keep. -/
theorem er2Γ_disp : er2ΓP.disp id = [.keep, .inline (.bvar 0), .keep] := by decide

/-- `Δ`'s canonical display: two keeps. -/
theorem er2Δ_disp : er2ΔP.disp id = [.keep, .keep] := by decide

/-! ## §3 the derivations -/

/-- `D : Γ ⊢ bvar 1 : S` — the let-bound slot `z`, direct `bvar`. -/
def er2D : TyP emptyEnv 0 er2Γ (.bvar 1) er2S :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- `hv : Δ ⊢ bvar 1 : S` — the actual replacement `lift 0 1 (bvar 0)`. -/
def er2Hv : TyP emptyEnv 0 er2Δ (.bvar 1) er2S :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- `hvT : Δ ⊢ S : sort (succ zero)` — the removed entry's type, direct `sort`. -/
def er2HvT : TyP emptyEnv 0 er2Δ er2S (.sort (.succ .zero)) :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- `Γ[1]` is the let slot `z : S := P`. -/
theorem er2Γ_get_one : er2Γ[1]? = some (.letBinding er2S (.bvar 0)) := rfl

/-- `L`: remove the let slot `j = 1` with `v = bvar 0`, `u = succ zero`.
    `substRemove` and both `instantiate`s reduce, so the result judgment is
    `Δ ⊢ bvar 1 : S` — the *same* judgment as `hv`, derived differently. -/
def er2L : TyP emptyEnv 0 er2Δ (.bvar 1) er2S :=
  .lsub emptyEnv 0 er2Γ (.bvar 1) er2S er2S (.bvar 0) 1 (.succ .zero)
    er2D rfl er2Hv er2HvT

/-! ## §4 admissibility -/

/-- `Γ.take 1 = [.assumption S]` — the `j = 1` cutoff prefix is all
    assumptions, so `L` is a legal public `AssumpPref` input. -/
theorem er2Γ_assumptionPrefix_one : AssumptionPrefix er2Γ 1 := by
  intro d hd
  simp only [er2Γ, List.take_succ_cons, List.take_zero, List.mem_singleton] at hd
  exact ⟨er2S, hd⟩

/-- `D` carries no transport nodes. -/
theorem er2D_assumpPref : er2D.AssumpPref := trivial

/-- `hv` carries no transport nodes. -/
theorem er2Hv_assumpPref : er2Hv.AssumpPref := trivial

/-- `hvT` carries no transport nodes. -/
theorem er2HvT_assumpPref : er2HvT.AssumpPref := trivial

/-- `L`: the `j = 1` `AssumptionPrefix` plus its three children's. -/
theorem er2L_assumpPref : er2L.AssumpPref :=
  ⟨er2Γ_assumptionPrefix_one, er2D_assumpPref, er2Hv_assumpPref, er2HvT_assumpPref⟩

/-! ## §5 erasures -/

/-- `D.eps` at `ρΓ`: `resolve [keep, inline (bvar 0), keep] 1` returns the
    inline payload `bvar 0` lifted once for the prefix keep — `bvar 1`. -/
theorem er2D_eps : er2D.eps id [.keep, .inline (.bvar 0), .keep] = .bvar 1 := by decide

/-- `hv.eps` at `ρΔ`: `resolve [keep, keep] 1` — `bvar 1`. -/
theorem er2Hv_eps : er2Hv.eps id [.keep, .keep] = .bvar 1 := by decide

/-- `L.epsOld` at `ρΔ` under the **frozen** pre-R2 erasure: `hv.eps` is
    `bvar 1 ≠ star`, so `D` is erased at
    `insertDisp (inline (bvar 1)) 1 ρΔ = [keep, inline (bvar 1), keep]`, and
    `resolve` lifts the inline payload across the prefix keep *again* —
    `bvar 2`. The payload `hv.eps` already lives in `Δ`; the lsub treats it
    as suffix-local. -/
theorem er2L_eps : er2L.epsOld id [.keep, .keep] = .bvar 2 := by decide

/-- `L.eps` under the fixed erasure: the gate still reads `hv.eps = bvar 1`,
    but the inserted payload is `localize (countKeep (ρ.take 1)) (bvar 1)
    = localize 1 (bvar 1) = inst 0 star (bvar 1) = bvar 0`; `resolve` then
    lifts it across the prefix keep back to `bvar 1` — the double lift is
    gone. -/
theorem er2L_eps_fixed : er2L.eps id [.keep, .keep] = .bvar 1 := by decide

/-- The frozen and fixed erasures of `L` diverge — `bvar 2 ≠ bvar 1`. -/
theorem er2L_eps_ne_epsOld :
    er2L.eps id [.keep, .keep] ≠ er2L.epsOld id [.keep, .keep] := by decide

/-! ## §6 `CL` refusal (frozen) and agreement (fixed) -/

/-- The lsub-transported and the directly-built derivations of the same
    judgment `Δ ⊢ bvar 1 : S` are NOT `CLold`-related at `ρΔ` under the
    frozen erasure: `L.epsOld` is `bvar 2`, `hv.eps` is `bvar 1`, and
    `bvar` rigidity refuses. No Π-injectivity needed. -/
theorem no_cl_lsub_inline_scope {tbl : List CRule} (hW : TableWF tbl) :
    ¬ CLold tbl id [.keep, .keep] er2L er2Hv := by
  intro h
  have h' : ConvMod (EStep tbl) LvlEq (.bvar 2) (.bvar 1) := h
  exact not_convMod_bvar_ne hW (by decide : (2 : Nat) ≠ 1) h'

/-- Under the fixed erasure they ARE `CL`-related — both erase to
    `bvar 1`. The R2 positive pin: the `localize`d inline payload lands in
    the right scope. -/
theorem cl_lsub_inline_scope {tbl : List CRule} (hW : TableWF tbl) :
    CL tbl id [.keep, .keep] er2L er2Hv := by
  unfold CL
  rw [er2L_eps_fixed, er2Hv_eps]
  exact .refl _

end Rcic.Syn

#print axioms Rcic.Syn.er2S
#print axioms Rcic.Syn.er2Γ
#print axioms Rcic.Syn.er2Δ
#print axioms Rcic.Syn.er2Δ_wf
#print axioms Rcic.Syn.er2Γ_wf
#print axioms Rcic.Syn.er2P_ty
#print axioms Rcic.Syn.er2ΓP
#print axioms Rcic.Syn.er2ΔP
#print axioms Rcic.Syn.er2Γ_disp
#print axioms Rcic.Syn.er2Δ_disp
#print axioms Rcic.Syn.er2D
#print axioms Rcic.Syn.er2Hv
#print axioms Rcic.Syn.er2HvT
#print axioms Rcic.Syn.er2Γ_get_one
#print axioms Rcic.Syn.er2L
#print axioms Rcic.Syn.er2Γ_assumptionPrefix_one
#print axioms Rcic.Syn.er2D_assumpPref
#print axioms Rcic.Syn.er2Hv_assumpPref
#print axioms Rcic.Syn.er2HvT_assumpPref
#print axioms Rcic.Syn.er2L_assumpPref
#print axioms Rcic.Syn.er2D_eps
#print axioms Rcic.Syn.er2Hv_eps
#print axioms Rcic.Syn.er2L_eps
#print axioms Rcic.Syn.no_cl_lsub_inline_scope
