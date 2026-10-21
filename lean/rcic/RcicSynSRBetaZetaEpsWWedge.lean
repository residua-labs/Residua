import rcic.RcicSynSRBetaZetaEpsWSubst
import rcic.RcicSynInlineRefute

/-!
# The landed `not_es_wk_inline` becomes FALSE at `epsW` — that is the point

The landed refutation `not_es_wk_inline` (RcicSynInlineRefute) says: at the
canonical Entry disposition of `wkZetaCtx`, `ES tbl id … (wkZetaNode E n)`
is FALSE for every `TableWF tbl` — the double-lift wedge. Restated at the
display-aware erasure, the same statement is FALSE, for **every** `E`, `n`
and **every** table (no `TableWF` needed): under `epsW` both endpoints
erase to `.bvar 1` (`es_wkZetaNode_epsW_general`), so the negated
`ESW` is refuted — kernel-checked, not by the author's own gate
(`ConvMod.refl` carries the content). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `wkZetaNode`'s left endpoint erases to `.bvar 1` under `epsW`, at every
    `E` and `n` (the re-frame un-lifts the inline value at the inserted
    keep's slot; the keep-lift restores it — shifted exactly once). -/
theorem epsW_wkZetaNode_dl_general (E : ResolvedEnv) (n : Nat) :
    (wkZetaNode E n).dl.epsW id ((wkZetaCtxP E n).disp id) = .bvar 1 := rfl

theorem epsW_wkZetaNode_dr_general (E : ResolvedEnv) (n : Nat) :
    (wkZetaNode E n).dr.epsW id ((wkZetaCtxP E n).disp id) = .bvar 1 := rfl

/-- Under `epsW` the wedge vanishes at the canonical disposition, for every
    `E`, `n` and every rule table. -/
theorem es_wkZetaNode_epsW_general (tbl : List CRule) (E : ResolvedEnv) (n : Nat) :
    ESW tbl id ((wkZetaCtxP E n).disp id) (wkZetaNode E n) := by
  unfold ESW
  rw [epsW_wkZetaNode_dl_general, epsW_wkZetaNode_dr_general]
  exact ConvMod.refl _

/-- **The landed refutation's `epsW`-restatement is FALSE**: the exact shape
    of `not_es_wk_inline` with `ES`→`ESW` (its `TableWF` premise kept
    verbatim) has a kernel-checked refutation of its own negation — the
    wedge the landed theorem pins does not survive the display-aware
    erasure. -/
theorem not_es_wk_inline_epsW_false (tbl : List CRule) (hW : TableWF tbl)
    (E : ResolvedEnv) (n : Nat) :
    ¬ (¬ ESW tbl id ((wkZetaCtxP E n).disp id) (wkZetaNode E n)) :=
  fun h => h (es_wkZetaNode_epsW_general tbl E n)

end Rcic.Syn

#print axioms Rcic.Syn.epsW_wkZetaNode_dl_general
#print axioms Rcic.Syn.epsW_wkZetaNode_dr_general
#print axioms Rcic.Syn.es_wkZetaNode_epsW_general
#print axioms Rcic.Syn.not_es_wk_inline_epsW_false
