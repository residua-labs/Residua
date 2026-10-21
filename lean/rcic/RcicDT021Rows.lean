import rcic.RcicDT008Equiv
import rcic.RcicAnnSemPrefixRows
import rcic.RcicTypedGroupPinsList
import rcic.RcicA2SortSupport

namespace Rcic.Declarative

/-!
# DT-021 modulo the rows (r6 census leg)

cc's r6 directive: the DT chapter's `PARTIAL` rows are re-measured per named
open, and the missing legs built where the discharge is honest. DT-021's
sealed front is `DT021T_no_cumulativity` (`RcicDTMetaTypedSR.lean`), which
takes `hP : hW.InScope`. This module states the same row with
`hrows : TypedRowsWf E n` instead — the `_of_typedRowsWf` convention of
`DT012T_type_uniqueness_of_typedRowsWf` (`RcicDT008Equiv.lean:192`).

The unconditional leg is FALSE — `bEnv_typedRowsWf_false` refutes
`TypedRowsWf bEnv n`, and `not_envWfT_bEnv` refutes `EnvWfT bEnv`, so row 1 is
not derivable from the environment alone; `TypedRowsWf` stays a named premise.
Note the counterexample is *inadmissible for the conditioned theorem*: `bEnv`
falsifies the premise members (`EnvWfT bEnv`, `TypedRowsWf bEnv n`), which
cannot falsify the `EnvWfT`-conditioned statement — that would require an
environment satisfying `EnvWfT` (and supplying the row) where the conclusion
fails (`PIROW_FAMAPPROW_FULL_ENVWFT.md` §9.4).

The route (no AnnEnvA round-trip needed):

| step | fact |
|---|---|
| endpoint typing | `DT009T_endpoints_envWfT` (unconditional, all seven supplies) |
| sort inversion | `hasTyTInv_sortT` — `HasTyT Γ (sort l) T` ⇒ `TyConvT Γ (sort (l+1)) T` |
| chain | `TyConvT.trans` on `(sort (u+1)) ≡ T ≡ (sort (v+1))` (right leg `symmT`) |
| row 1 | `hrows.sortRow hΓ` ⇒ `eqN (u+1) (v+1)` |
| succ-cancel | `eqN_succ_inj` — `eval ρ (l+1) = (eval ρ l).map (·+1)`, `Option.map` injective |

This is exactly the consumption `sortConvCharT_inScope` performs at the
`InScope` cone, replayed at the `TypedRowsWf` interface.
-/

/-- level `succ` cancellation in `eqN`: `⟦.succ l⟧ρ = (⟦l⟧ρ).map (·+1)`, and
    `Option.map (·+1)` collapses `none`/`some` mismatches to `noConfusion`
    while `some`/`some` injects at `+1`. -/
theorem eqN_succ_inj {u v : Level} (h : eqN (.succ u) (.succ v)) : eqN u v := by
  intro ρ
  have hρ : Option.map (· + 1) (eval ρ u) = Option.map (· + 1) (eval ρ v) := h ρ
  cases hu : eval ρ u with
  | none =>
      cases hv : eval ρ v with
      | none => rfl
      | some b => rw [hu, hv] at hρ; exact Option.noConfusion hρ
  | some a =>
      cases hv : eval ρ v with
      | none => rw [hu, hv] at hρ; exact Option.noConfusion hρ
      | some b =>
          rw [hu, hv] at hρ
          exact congrArg Option.some (Nat.succ.inj (Option.some.inj hρ))

/-- DT-021 modulo the rows conjecture: a typed conversion between two sorts
    collapses their levels, `TypedRowsWf` premise in place of `hW.InScope`.
    `DT009T_endpoints_envWfT` types both ends unconditionally; sort-inversion
    reads each as a `TyConvT` from the successor sort; `sortRow` collapses
    the chained `TyConvT (sort (u+1)) (sort (v+1))` to `eqN`. -/
theorem DT021T_no_cumulativity_of_typedRowsWf {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} (hrows : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} {T : Expr Nat} (hc : ConvT E n Γ (.sort u) (.sort v) T) :
    eqN u v := by
  obtain ⟨⟨h1⟩, ⟨h2⟩⟩ := DT009T_endpoints_envWfT hW hΓ hc
  exact eqN_succ_inj (hrows.sortRow hΓ
    (.trans _ _ _ _ (hasTyTInv_sortT h1 rfl) (hasTyTInv_sortT h2 rfl).symmT))

/-- PIN (non-vacuity tooth): DT-021 modulo the rows consumed at `listEnvUT`'s
    `TypedRowsWf` supply (the `InScope` lane witnesses the premise is
    inhabitable where the conjecture holds). The conversion is `.max 0 0 ≡ 0`
    at `Sort 1` — distinct syntax, equal denotation — so the pin exercises
    the row's actual content, not a `refl` degenerate. -/
theorem pin_DT021T_rows_listU {n : Nat} : eqN (.max .zero .zero) .zero :=
  DT021T_no_cumulativity_of_typedRowsWf listEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix listEnvUWfT listEnvUWfT_inScope n)
    CtxWfT.nil (ConvT.sorts [] (.max .zero .zero) .zero (fun _ => rfl))

/-- DT-021 with only the sortRow leg paid: the additive `SortUnique`
    anchor of `CENSUS_WALLS_MAINLINE_AUTHORITY_RECOVERY.md` §I.6 —
    the body replays `DT021T_no_cumulativity_of_typedRowsWf` step for
    step, with `F8A2Support.sort_chain_eq` in place of the whole
    `TypedRowsWf` premise. Π and family rows are not silently imported:
    `sort_chain_eq` transports `sort u : sort (succ u)` along the
    original chain and `su` compares the two canonical typings. -/
theorem DT021T_no_cumulativity_of_sortUnique {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level} {T : Expr Nat}
    (hc : ConvT E n Γ (.sort u) (.sort v) T) : eqN u v := by
  obtain ⟨⟨h1⟩, ⟨h2⟩⟩ := DT009T_endpoints_envWfT hW hΓ hc
  exact eqN_succ_inj (F8A2Support.sort_chain_eq su hW hΓ
    (.trans _ _ _ _ (hasTyTInv_sortT h1 rfl) (hasTyTInv_sortT h2 rfl).symmT))

#print axioms Rcic.Declarative.eqN_succ_inj
#print axioms Rcic.Declarative.DT021T_no_cumulativity_of_typedRowsWf
#print axioms Rcic.Declarative.DT021T_no_cumulativity_of_sortUnique
#print axioms Rcic.Declarative.pin_DT021T_rows_listU

end Rcic.Declarative
