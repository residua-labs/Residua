import rcic.RcicDTRowFields
import rcic.RcicSynAllBelow

/-!
# DT-021 on full `EnvWfT` — the sort-only row composed with the BelowC
`sortRow` producer

`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §9.4/§9.5; brief
`~/.residua-lean/briefs/dt021-envwft.md`. `closure_claim = 0`.

`DT021T_no_cumulativity_of_sortRow` consumes exactly one
`TypedRowsWf` field — `sortRow`. `Rcic.Syn.sortRow_of_allBelow` produces
that field end-to-end on plain `TyConvT` from the BelowC pack. The
composition:

  `AllBelow Aw tbl` + `TableWF tbl` + `EnvWfT E` ⊢
    `ConvT E n Γ (.sort u) (.sort v) T → eqN u v`

**Premise measure** (what the BelowC `sortRow` still carries on full
`EnvWfT`): exactly `AllBelow Aw tbl` and `TableWF tbl`. Both are
statements about the BelowC rule table `tbl` — mutual-pack validity at
all `LexDM` bounds, and rule congruence/closedness/rigidity — not about
`E`'s members, so neither is dischargeable from `EnvWfT E` on main; they
remain named premises. No `ScopedCtx`/`AssumpPref`/level-homomorphism
adapters are needed at this interface: the unscoped `AllBelow` route
enriches the native judgments internally (`enrichTyConvT_of_envWfT`,
`dispFor_ctxP_id`, `sortRow_of_tyCvP_esChain_id`).
-/

namespace Rcic.Declarative

/-- DT-021 at full `EnvWfT`: a typed conversion between two sorts
    collapses their levels. Pure composition —
    `Rcic.Syn.sortRow_of_allBelow` (premises `AllBelow Aw tbl`,
    `TableWF tbl`) feeds the `sortRow` slot of
    `DT021T_no_cumulativity_of_sortRow`, whose own body is the landed
    DT-009 → sort-inversion → `succ`-cancellation route. Neither BelowC
    premise is derivable from `EnvWfT E` on main: `AllBelow`/`TableWF`
    constrain the rewrite table `tbl`, which `EnvWfT` does not mention. -/
theorem DT021T_of_envWfT {Aw : Nat → Nat} {tbl : List Rcic.Syn.CRule}
    (hBel : Rcic.Syn.AllBelow Aw tbl) (hT : Rcic.Syn.TableWF tbl)
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {u v : Level} {T : Expr Nat}
    (hc : ConvT E n Γ (.sort u) (.sort v) T) : eqN u v :=
  DT021T_no_cumulativity_of_sortRow hW
    (Rcic.Syn.sortRow_of_allBelow hBel hT hW) hΓ hc

end Rcic.Declarative

#print axioms Rcic.Declarative.DT021T_of_envWfT
