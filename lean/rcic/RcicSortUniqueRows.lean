import rcic.RcicA2SortSupport
import rcic.RcicDT008Equiv
import rcic.RcicAnnSemPrefixRows

/-!
# `SortUnique` from the rows — the rows-route supplier (S0 #7068, cc ruling)

`F8A2Support.SortUnique E n` (`RcicA2SortSupport`: two sort typings of one type in a
well-formed context have `=ₙ` sorts) is a corollary of two sealed theorems:
`DT012T_type_uniqueness_of_typedRowsWf` (`RcicDT008Equiv`) composed with
`TypedRowsWf.sortRow`. So it depends on exactly `EnvWfT + TypedRowsWf`, and holds
unconditionally at `InScope` (`typedRowsWf_of_envWfT_semPrefix`).

## CIRCULARITY GUARD (binding, cc ruling on #7068)

`TypedRowsWf` contains `piRow`, and the construction of `piRow` itself CONSUMES
`SortUnique`: the X tile (via StructPi / SP-1's separation entries), F8-OCC-POSITION's
sort hosts, and A-2 inside the ηK repair's diamond all take `SortUnique` as a named
hypothesis. **These theorems must NOT be imported into, or used by, any module that
participates in building `piRow` / `TypedRowsWf`** — the U/X/D/J mutual, StructPi, the
ηK diamond. Supplying `SortUnique` from `TypedRowsWf` inside that construction would
make `TypedRowsWf` depend on a proof that assumes it. Those modules keep `SortUnique`
as a hypothesis; the `piRow`-free discharge is the sortRow lane's step 4c (#6938,
`sortUnique_of_hasTyT_envWfT`, sortRow + the O6 enrichment), which is on the critical
path for closing the mutual. Legitimate consumers of this file are the ones OUTSIDE
that construction: census rows that only consume `SortUnique` (A-2's conditional,
DT-012), and any `InScope` client.

Names are distinct from #6938's. `closure_claim` 0.
-/

namespace Rcic.Declarative

/-- `SortUnique` from the rows: two sort typings of one type have `=ₙ` sorts, by
    rows-conditional type uniqueness (DT-012) collapsed at `sortRow`. Depends on
    `TypedRowsWf` (hence on `piRow`): see the circularity guard in the module doc. -/
theorem sortUnique_of_typedRowsWf {E : ResolvedEnv} {n : Nat} (hrows : TypedRowsWf E n) :
    F8A2Support.SortUnique E n := by
  intro hW Γ T u v hΓ hu hv
  exact (DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ hu hv).elim fun c =>
    hrows.sortRow hΓ c

/-- `SortUnique` at `InScope`, unconditionally: the rows are supplied by the semantic
    prefix bridge. Same guard applies. -/
theorem sortUnique_of_inScope {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope) (n : Nat) :
    F8A2Support.SortUnique E n :=
  sortUnique_of_typedRowsWf (Ann.typedRowsWf_of_envWfT_semPrefix hW hP n)

end Rcic.Declarative

#print axioms Rcic.Declarative.sortUnique_of_typedRowsWf
#print axioms Rcic.Declarative.sortUnique_of_inScope
