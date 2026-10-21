import rcic.RcicSynTableBuild

/-!
# `TableWF` of the derived table — field-by-field audit

`~/.residua-lean/briefs/tablewf.md` (sortRow gap): `TableWF` (`RcicSynE.lean:525`) is a
named hypothesis of `step_of_suppliers` / `allBelowScoped_of_suppliers` /
`sortCoh_of_suppliers` (`RcicSynStepSkeleton`), and the measurement recorded no
inhabitant for the table built from an admitted environment. The inhabitant is the
landed `tableWF_build` (`RcicSynTableBuild`), proved by induction over the
`EnvWfT` builder (L222–240) through `tableWF_cons_deltaRule`; this module exposes
each field under a named projection so supplier call-sites can cite the field they
consume, and fixes the field-by-field audit the brief asks for:

| field | discharge | kind |
|---|---|---|
| `congr` | `tableCongr_cons_deltaRule hW.congr r D_b` — `deltaRule` rhs is `LvlEq`-congruent for every `D_b` (`deltaRule_lvlEq_rhs`) | proved |
| `closed` | `deltaRule_closed r hDb` with `hDb := closedWf_enrichHasTyT … hv` — the enriched body's `ClosedWf` at the node's own admission derivation | reduced to an exact admission fact (the `.definition` node's `hv`) |
| `rigid` | `cases hm` on the new rule (bare: `major = none`); tail majors refuted by `major_none_tableOf` | vacuous — the δ half emits no major rule |
| `bare_unique` | `hfresh_head`: `head_mem_build` gives `E.members σ.head = some m`; the node's `hfresh : E.members r = none` contradicts `σ.head = r` | proved (real freshness, never a label) |
| `ctor_disjoint` | `cases hm_ρ` / `cases hm_σ` — no rule in `tableOf` carries a major | vacuous |
| `bare_nullary` | `rfl` — `(deltaRule r D_b).nargs ls = 0` | proved |

No field is false; none is left as open admission debt. `closure_claim = 0`.

The `TableWF` hypothesis stays a hypothesis of the supplier theorems — this module
does not rewire `StepSuppliers`; it names the discharge they instantiate with
`tbl := tableOf hEnv`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `TableWF.congr` of the derived table. -/
theorem tableOf_congr {E : ResolvedEnv} (hEnv : EnvWfT E) :
    TableCongr (tableOf hEnv) :=
  (tableWF_build hEnv).congr

/-- `TableWF.closed` of the derived table: every rule rhs is `ClosedAt 0` — the
emitted `deltaRule` bodies are closed by `ClosedWf` of the enriched admission
derivation. -/
theorem tableOf_closed {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOf hEnv, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms) :=
  (tableWF_build hEnv).closed

/-- `TableWF.rigid` of the derived table — vacuous: `major_none_tableOf` shows no
emitted rule has a major, so the antecedent is uninhabited. -/
theorem tableOf_rigid {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOf hEnv, ∀ {d : Nat} {m : List Level → Nat},
      ρ.major = some (d, m) → ∀ σ ∈ tableOf hEnv, σ.head ≠ d :=
  (tableWF_build hEnv).rigid

/-- `TableWF.bare_unique` of the derived table: a bare rule's head is unique —
each emitted `deltaRule` head is fresh in the prefix env by the node's own
`hfresh`, via `head_mem_build`. -/
theorem tableOf_bare_unique {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOf hEnv, ρ.major = none →
      ∀ σ ∈ tableOf hEnv, σ.head = ρ.head → σ = ρ :=
  (tableWF_build hEnv).bare_unique

/-- `TableWF.ctor_disjoint` of the derived table — vacuous: no emitted rule has a
major (`major_none_tableOf`). -/
theorem tableOf_ctor_disjoint {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOf hEnv, ∀ σ ∈ tableOf hEnv, ρ.head = σ.head →
      ∀ {d e : Nat} {m n : List Level → Nat},
        ρ.major = some (d, m) → σ.major = some (e, n) →
        ρ.nargs = σ.nargs ∧ (d = e → σ = ρ) :=
  (tableWF_build hEnv).ctor_disjoint

/-- `TableWF.bare_nullary` of the derived table: `(deltaRule r D_b).nargs ls = 0`. -/
theorem tableOf_bare_nullary {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOf hEnv, ρ.major = none → ∀ ls, ρ.nargs ls = 0 :=
  (tableWF_build hEnv).bare_nullary

#print axioms tableOf_congr
#print axioms tableOf_closed
#print axioms tableOf_rigid
#print axioms tableOf_bare_unique
#print axioms tableOf_ctor_disjoint
#print axioms tableOf_bare_nullary

end Rcic.Syn
