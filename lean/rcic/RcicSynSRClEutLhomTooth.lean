import rcic.RcicSynSRClEutLhomEut
import rcic.RcicSynSRBetaZetaInlineClass
import rcic.RcicSynCR
import rcic.RcicSynPiLamRight

/-!
# RcicSynSRClEutLhomTooth — row 15 `lamP` gated refutation: tooth class

cc 17:30Z task (2): classify the tooth of `eutLamP_lhom_tableOfI_empty_refuted`
(row 15 `lamP`, field-level, `σ := id`) against #7801's `InlineWkLift` — the
inline wk double-lift behind `not_es_wk_inline` — kernel-checked, as #7801
did. VERDICT: **DIFFERENT defect**. The gated refutation dies on SORT-LEVEL
DISTINCTNESS: the raw `EutLamPorts` binds INDEPENDENT subjects `B₁ B₂`, and
its `convB` demands `ConvMod` between their erasures; at the closed fixtures
`hs0s`/`hs1s` those are `.sort .zero / .sort one`, and sort separation
(`eqN_of_convE_sort_wf` at any `TableWF` table) forces `eqN .zero one`,
refuted by `not_eqN_zero_succ`. No inline entry participates (the whole
display is one `.keep`), the pair is not a lift of the other (lift is the
identity on sorts), and — the on-cone strengthening — the tooth is uniform
over every `LevelHom σ`, so the `LevelHom` gate cannot dodge it.
closure_claim = 0.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins (one two hs0s hs1s)

/-! ## The display and the discriminating pair -/

/-- The display the refuted instance's `convB` erases at: the `lamP` binder
    slot of `u₁ := two` (never zero: `two` is a succ) prepended to `ρ := []`.
    Kernel-checked: it is a single `.keep`. -/
def lamPDisp : List Disp := binderDisp (levelIsZero two) :: []

theorem lamPDisp_eq : lamPDisp = [.keep] := rfl

/-- The pair `convB` demands convertible, kernel-checked: the two INDEPENDENT
    subjects erase to distinct sorts at `σ := id` (`TyP.eps` on the `.sort`
    arm ignores the display: `rfl` at `RcicSynErase.lean:227`). -/
theorem lamP_eps_values :
    hs0s.eps id lamPDisp = .sort .zero ∧ hs1s.eps id lamPDisp = .sort one :=
  ⟨rfl, rfl⟩

/-! ## Not the inline wk double-lift -/

/-- No inline entry participates: the whole display is one `.keep` (#7801's
    `res_conv_no_inline_entry` covers slot 0; every other slot is `none`). -/
theorem lamP_no_inline_entry (j : Nat) (v : ETm) :
    lamPDisp[j]? ≠ some (.inline v) := by
  cases j with
  | zero => exact res_conv_no_inline_entry v
  | succ j => simp [lamPDisp_eq]

/-- Hence no `InlineWkLift` witness exists at this display — the tooth shape
    of #7801's SAME family cannot even be stated here (its `inlineAt`
    precondition is unsatisfiable), whatever `c`/`w`/`u` are. -/
theorem lamP_not_InlineWkLift (c j : Nat) (v w u : ETm) :
    ¬ InlineWkLift lamPDisp c j v w u :=
  fun h => lamP_no_inline_entry j v h.inlineAt

/-- The pair is not a lift of the other: `ETm.lift` is the identity on
    sorts, and `.zero`/`one` are distinct level constructors. -/
theorem lamP_pair_not_lift (κ : Nat) :
    ETm.sort .zero ≠ ETm.lift κ 1 (ETm.sort one) := by
  intro h
  exact ETm.noConfusion (show ETm.sort .zero = ETm.sort one from h) Level.noConfusion

/-! ## The tooth: sort-level distinctness (kernel content) -/

/-- The actual contradiction source, restated: at every `TableWF` table the
    two sorts of the pair are convertible only if `eqN .zero one` — which
    `not_eqN_zero_succ` refutes. This is SORT SEPARATION, not display
    arithmetic. -/
theorem lamP_sort_zero_one_not_convMod {tbl : List CRule} (hW : TableWF tbl) :
    ¬ ConvMod (EStep tbl) LvlEq (.sort .zero) (.sort one) :=
  fun h => not_eqN_zero_succ .zero (eqN_of_convE_sort_wf hW h)

/-- On-cone strengthening: the distinctness is uniform over the whole demand
    cone — at EVERY `LevelHom σ` (not just `id`) the gated pair stays
    distinct, because `map_zero`/`map_succ` pin `σ .zero = .zero` and
    `σ one = one`. The `LevelHom` gate cannot dodge the tooth. -/
theorem lamP_sort_distinct_at_levelHom {σ : Level → Level} (hσ : LevelHom σ) :
    ¬ eqN (σ .zero) (σ one) := by
  have h1 : σ one = .succ .zero := by
    rw [show one = Level.succ .zero from rfl, hσ.map_succ, hσ.map_zero]
  rw [hσ.map_zero, h1]
  exact not_eqN_zero_succ .zero

/-- Field-level statement of the same: the gated `lamP` supply is refuted at
    the closed fixtures for EVERY `LevelHom σ` — the `σ := id` instance of
    `eutLamP_lhom_tableOfI_empty_refuted` is one point of this family, not
    an artifact of the chosen σ. -/
theorem eutLamPorts_lhom_fixtures_refuted (hW : EnvWfT emptyEnv)
    {σ : Level → Level} (hσ : LevelHom σ) :
    ¬ EutLamPorts (tableOfI hW) σ [] two hs0s hs1s := by
  intro ports
  have hconv := ports.convB
  have h0 : hs0s.eps σ
      (binderDisp (levelIsZero (σ two)) :: []) = .sort (σ .zero) := rfl
  have h1 : hs1s.eps σ
      (binderDisp (levelIsZero (σ two)) :: []) = .sort (σ one) := rfl
  rw [h0, h1] at hconv
  exact lamP_sort_distinct_at_levelHom hσ
    (eqN_of_convE_sort_wf (tableWF_tableOfI_full hW) hconv)

/-! ## The verdict row (see #7801's table)

| refutation | display | pair | tooth |
|---|---|---|---|
| eutLamP_lhom_tableOfI_empty_refuted (this PR) | [.keep] | .sort 0 / .sort 1 | **DIFFERENT** — sort-level distinctness under independent subjects: no inline entry participates (`lamP_no_inline_entry`), no `InlineWkLift` witness exists (`lamP_not_InlineWkLift`), the pair is not lift-related (`lamP_pair_not_lift`), and the distinctness is uniform over every `LevelHom σ` (`lamP_sort_distinct_at_levelHom`). -/

#print axioms Rcic.Syn.lamPDisp
#print axioms Rcic.Syn.lamPDisp_eq
#print axioms Rcic.Syn.lamP_eps_values
#print axioms Rcic.Syn.lamP_no_inline_entry
#print axioms Rcic.Syn.lamP_not_InlineWkLift
#print axioms Rcic.Syn.lamP_pair_not_lift
#print axioms Rcic.Syn.lamP_sort_zero_one_not_convMod
#print axioms Rcic.Syn.lamP_sort_distinct_at_levelHom
#print axioms Rcic.Syn.eutLamPorts_lhom_fixtures_refuted

end Rcic.Syn
