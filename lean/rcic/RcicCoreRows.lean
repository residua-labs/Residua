import rcic.RcicAnnTypedRows
import rcic.RcicDT1011Rows
import rcic.RcicDTMetaTypedScope
import rcic.RcicDTRowFields
import rcic.RcicTypedScopeCheckPins

/-!
# RcicCoreRows — core layer 6: the three rows and their consumers

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

The three rows are the consumable interfaces the core results are discharged
against: sort uniqueness (DT-021), one-step subject reduction (DT-010) and
multi-step subject reduction (DT-011).

Key definitions and theorems of the layer:

* `Rcic.Declarative.TypedRowsWf` — the rows as a consumable interface
* `Rcic.Declarative.PiRowField` / `Rcic.Declarative.PiRowInjT` — the Π-row field
* `Rcic.Declarative.EnvWfT.ScopeCheck` / `Rcic.Declarative.typedRowsWf_of_scopeCheck` — the scope-check supply
* `Rcic.Declarative.Ann.typedRowsWf_of_envWfT_semPrefix` — the semantic-prefix supply
* `Rcic.Declarative.Ann.sortConvCharT` / `Rcic.Declarative.Ann.piConvInjT` / `Rcic.Declarative.Ann.famAppConvInjT` — the three rows on the typed judgment
* `Rcic.Declarative.DT021T_no_cumulativity_of_typedRowsWf` — sort uniqueness (DT-021) modulo the rows
* `Rcic.Declarative.DT010T_one_step_subject_reduction_of_typedRowsWf` / `Rcic.Declarative.DT011T_multi_step_subject_reduction_of_typedRowsWf` — subject reduction (DT-010/011) modulo the rows
* `Rcic.Declarative.DT012T_type_uniqueness_of_sortRow_piRow` / `Rcic.Declarative.DT021T_no_cumulativity_of_sortRow` — the two-field DT-012 and sort-only DT-021 row fields
* `Rcic.Declarative.F8A2Support.SortUnique` / `Rcic.Declarative.F8A2Support.sort_transport` — the conditional sorting support
* `Rcic.Declarative.DT009T_endpoints_inScope` — the scope supply's endpoints

Layer members: `RcicTypedRowsWf`, `RcicTypedScopeCheck`,
`RcicTypedScopeCheckPins`, `RcicAnnRowsSupply`, `RcicAnnSemPrefixRows`,
`RcicAnnTypedRows`, `RcicDTRowFields`, `RcicDT1011Rows`, `RcicDT021Rows`,
`RcicDTMetaTypedScope`, `RcicA2SortSupport`.
-/
