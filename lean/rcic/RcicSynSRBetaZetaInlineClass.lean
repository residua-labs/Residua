import rcic.RcicSynSRClEutClCase
import rcic.RcicSynSRLitPiLit
import rcic.RcicSynSRBetaZetaField
import rcic.RcicSynSRBetaZetaEpsW

/-!
# sortRow refutation teeth — classification (kernel-checked)

cc 2026-10-20 16:45Z task (1): for each same-subject CL refutation in hand,
decide whether its tooth IS the inline double-lift behind the landed
`not_es_wk_inline` (the `wk` eps clause keep-lifting an inline-resolved
display value that already carries the inserted slot), or something else.

`InlineWkLift ρ c j v w u` is the tooth's exact shape, as pure display
arithmetic: a `wk` at cutoff `c` over a `keep` (`ρ[c]? = some .keep`),
whose inner resolution of the bvar at `j` passes through the inline entry
`v` (`ρ[j]? = some (.inline v)`, `j < c`), giving the honest `w =
resolve (removeAt ρ c) j` and the offending `u = w.lift κ 1` at
`κ = countKeep (ρ.take c)` — the same eps computation `not_es_wk_inline`
exhibits. A fixture is SAME-tooth when its discriminating pair is
(`u`, `w`) for concrete witnesses (kernel-checked here), DIFFERENT-tooth
when no display participates (`ρ = []`), or the pair is not a
lift-of-the-other at all. closure_claim = 0.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins (one two)

/-- The inline double-lift tooth: the offending erasure is the honest one
    (the inner resolution through the inline entry) lifted once more at the
    `wk` keep slot. -/
structure InlineWkLift (ρ : List Disp) (c j : Nat) (v w u : ETm) : Prop where
  keepAt : ρ[c]? = some .keep
  inlineAt : ρ[j]? = some (.inline v)
  below : j < c
  honest : w = resolve (removeAt ρ c) j
  lifted : u = w.lift (countKeep (ρ.take c)) 1

/-! ## The canonical tooth (`not_es_wk_inline` itself) -/

/-- The canonical disposition of `wkZetaCtx`, as a concrete list. -/
theorem zlRho_eq : zlRho = [.inline (.bvar 1), .keep, .keep] := rfl

/-- `not_es_wk_inline`'s own discriminating pair is an `InlineWkLift`: the
    offending `.bvar 2` is the honest inline value `.bvar 1` (the inner
    resolution through `.inline (.bvar 1)` at `removeAt zlRho 1`) lifted
    once more at the `wk` keep slot `κ = 0`. -/
theorem tooth_canonical : InlineWkLift zlRho 1 0 (.bvar 1) (.bvar 1) (.bvar 2) :=
  ⟨rfl, rfl, by decide, rfl, rfl⟩

/-- The canonical tooth's values are exactly `wkZetaNode`'s erasures (the
    landed refutation's `hl`/`hr`). -/
theorem canonical_pair_is_wkZetaNode :
    (wkZetaNode emptyEnv 0).dl.eps id zlRho = .bvar 2 ∧
      (wkZetaNode emptyEnv 0).dr.eps id zlRho = .bvar 1 :=
  ⟨rfl, rfl⟩

/-! ## Row 2 `es_beta` (#7780): `beta_body_cl`, `beta_reduct_cl` — SAME -/

/-- `beta_body_cl`'s pair is an `InlineWkLift` at the read's body: the
    offending `.bvar 3` is the honest `.bvar 2` (resolve of the lam-body
    bvar through `.inline (.bvar 1)` with its keep-walk) lifted once more
    at the `wk`-at-2 keep slot `κ = 1`. -/
theorem tooth_beta_body :
    InlineWkLift (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho)
      2 1 (.bvar 1) (.bvar 2) (.bvar 3) :=
  ⟨by simp [zlRho_eq], by simp [zlRho_eq], by decide, rfl, rfl⟩

theorem beta_body_pair :
    bGot.hbody.eps id
        (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho) = .bvar 3 ∧
      bHBody.eps id
        (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho) = .bvar 2 :=
  ⟨rfl, rfl⟩

/-- `beta_reduct_cl`'s offending side is `bDr = zlWkDl` at the canonical
    tooth (`c = 1`, `j = 0`): `.bvar 2` vs the honest `instEnd` `.bvar 1`. -/
theorem beta_reduct_offending : bDr.eps id zlRho = .bvar 2 := rfl

theorem beta_reduct_honest : (instEnd bHBody bHArg bHA).eps id zlRho = .bvar 1 := by
  rw [instEnd_eps_keep bHBody bHArg bHA
    (hu := (show levelIsZero (id (.succ (.succ .zero))) = false from rfl))]
  rfl

/-! ## Row 3 `es_zeta` (#7780): `zeta_surface_cl`, `zeta_reduct_cl` — SAME -/

theorem zeta_surface_offending : zzWkDl.eps id zlRho = .bvar 2 := rfl

theorem zeta_surface_honest :
    (TyP.letE emptyEnv 0 wkZetaCtx (.sort (.succ .zero)) (.succ (.succ .zero))
      (.bvar 0) (.sort (.succ .zero)) (.bvar 0) zzWkDl.reg.1 zzHA zzHV zzHB
      zzWkDl.reg.2).eps id zlRho = .bvar 1 := rfl

theorem zeta_reduct_offending : zzDr.eps id zlRho = .bvar 2 := rfl

theorem zeta_reduct_honest : (letSub zzHB zzHV zzHA).eps id zlRho = .bvar 1 := by
  rw [letSub_eps]
  rfl

/-! ## Row 4 `es_zetaLocal` (#7780) — surface SAME, `res_conv` DIFFERENT -/

theorem zetaLocal_surface_offending : zlWkDl.eps id zlRho = .bvar 2 := rfl

theorem zetaLocal_surface_honest :
    (zetaLocalBvarSurface (rfl : lookupType wkZetaCtx 0 = some (.sort (.succ .zero)))
      zlWkDl).eps id zlRho = .bvar 1 := rfl

/-- `zetaLocal_res_conv` is NOT the inline double-lift tooth: its display
    `[.keep]` has no inline entry at all, and the discriminating pair
    (`.bvar 0` vs `.sort .zero`) is not a lift of the other — the value's
    erasure is a sort, the kept variable a bvar. -/
theorem zetaLocal_res_conv_value : zrHv.eps id [.keep] = .sort .zero := rfl

theorem res_conv_no_inline_entry (v : ETm) :
    ([.keep] : List Disp)[0]? ≠ some (.inline v) := by simp

theorem res_conv_pair_not_lift (κ : Nat) :
    ETm.sort .zero ≠ ETm.lift κ 1 (.bvar 0) := by
  intro h
  cases κ with
  | zero => exact ETm.noConfusion (by simpa only [ETm.lift] using h)
  | succ κ => exact ETm.noConfusion (by simpa only [ETm.lift] using h)

/-! ## Row 14 `cl_case` (#7781) — DIFFERENT: the `eqN`-slack port bit -/

/-- Row 14's wall dies on `ports.hbit sr3hne : (true : Bool) = false` — a
    level-list disequality feeding a port bit — not on an erasure pair:
    its display is `[]` (no inline entry can participate) and both endpoint
    erasures are sorts of the same shape. -/
theorem cl_case_eps_values :
    sr3hT₁.eps sr3σ [] = .sort (sr3σ one) ∧
      sr3hT₂.eps sr3σ [] = .sort (sr3σ (.max one one)) :=
  ⟨by simp only [sr3hT₁, TyP.eps], by simp only [sr3hT₂, TyP.eps]⟩

theorem cl_case_no_display (j : Nat) (v : ETm) :
    ([] : List Disp)[j]? ≠ some (.inline v) := by simp

/-! ## `TransportHeadSortAt` lit tooth (#7799, sr2) — DIFFERENT -/

/-- #7799's discriminating pair is `.const 1 []` vs `.star` at `ρ = []` —
    a `levelIsZero`/max-vs-succ cutoff mismatch behind `.ewk`, not an
    inline double-lift: no display participates, and a lift never turns a
    `.const` into a `.star`. -/
theorem sr2_pair_values :
    sr2_litTooth.eps sr2_σ [] = .const 1 [] ∧
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy).eps sr2_σ [] = .star :=
  ⟨rfl, rfl⟩

theorem sr2_no_display (j : Nat) (v : ETm) :
    ([] : List Disp)[j]? ≠ some (.inline v) := by simp

theorem sr2_pair_not_lift (κ : Nat) :
    ETm.star ≠ ETm.lift κ 1 (.const 1 []) := by
  intro h
  exact ETm.noConfusion (by simpa only [ETm.lift] using h)

/-! ## The table (see PROGRESS.md and the PR body for prose)

| refutation                | display        | pair                  | tooth      |
|---------------------------|----------------|-----------------------|------------|
| not_es_wk_inline (landed) | zlRho          | .bvar 2 / .bvar 1     | SAME (canon) |
| beta_body_cl      (#7780) | keep :: zlRho  | .bvar 3 / .bvar 2     | SAME (c=2,j=1) |
| beta_reduct_cl    (#7780) | zlRho          | .bvar 2 / .bvar 1     | SAME (c=1,j=0) |
| zeta_surface_cl   (#7780) | zlRho          | .bvar 2 / .bvar 1     | SAME (c=1,j=0) |
| zeta_reduct_cl    (#7780) | zlRho          | .bvar 2 / .bvar 1     | SAME (c=1,j=0) |
| zetaLocal_surface (#7780) | zlRho          | .bvar 2 / .bvar 1     | SAME (c=1,j=0) |
| zetaLocal_res_conv(#7780) | [.keep]        | .sort 0 / .bvar 0     | DIFFERENT (value-is-a-sort; no inline) |
| cl_case           (#7781) | []             | hbit sr3hne (Bool)    | DIFFERENT (eqN-slack bit; no display) |
| sr2 litTooth      (#7799) | []             | .const 1 [] / .star   | DIFFERENT (levelIsZero cutoff; no display) |
-/

end Rcic.Syn

#print axioms Rcic.Syn.InlineWkLift
#print axioms Rcic.Syn.zlRho_eq
#print axioms Rcic.Syn.tooth_canonical
#print axioms Rcic.Syn.canonical_pair_is_wkZetaNode
#print axioms Rcic.Syn.tooth_beta_body
#print axioms Rcic.Syn.beta_body_pair
#print axioms Rcic.Syn.beta_reduct_offending
#print axioms Rcic.Syn.beta_reduct_honest
#print axioms Rcic.Syn.zeta_surface_offending
#print axioms Rcic.Syn.zeta_surface_honest
#print axioms Rcic.Syn.zeta_reduct_offending
#print axioms Rcic.Syn.zeta_reduct_honest
#print axioms Rcic.Syn.zetaLocal_surface_offending
#print axioms Rcic.Syn.zetaLocal_surface_honest
#print axioms Rcic.Syn.zetaLocal_res_conv_value
#print axioms Rcic.Syn.res_conv_no_inline_entry
#print axioms Rcic.Syn.res_conv_pair_not_lift
#print axioms Rcic.Syn.cl_case_eps_values
#print axioms Rcic.Syn.cl_case_no_display
#print axioms Rcic.Syn.sr2_pair_values
#print axioms Rcic.Syn.sr2_no_display
#print axioms Rcic.Syn.sr2_pair_not_lift
