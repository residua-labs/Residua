/-
CONVERSION BASE — THIS FILE'S `RowsT` IS BUILT ON MAIN'S THREE-
ARGUMENT UNTYPED `Conv` (`RcicDeclarative.lean`, `Conv E n Γ a b`),
which `RcicUntypedConvCollapse` measures TOTAL (cc-verified #6099;
ruling `d768d1a494`, #6102): `totalConv : ∀ Γ a b, Conv E n Γ a b`,
`sortConvChar_empty_false`, `sortsConv` axiom-free. Consequences for
the bundled fields:

  * `sortConvChar : SortConvChar` — REFUTED statement: `totalConv`
    inhabits `Conv Γ (sort u) (sort v)` at `u ≢ v`, so the `eqN`
    conclusion fails (`sortConvChar_empty_false` at `emptyEnv`);
  * `famAppConvInj : FamAppConvInj` — REFUTED the same way
    (`eqNList`/`ConvArgs` conclusions against totality);
  * `piConvInj : PiConvInj` — DEGENERATE: its `×' Conv` conclusion is
    trivially inhabited by `totalConv`.

`RowsT` over this `Conv` is REFUTED — uninhabitable at every
well-formed environment (`rowsT_false_of_envWf`, [propext]; the
`sortConvChar`/`famAppConvInj` fields are refuted statements and
`piConvInj` is degenerate), and every consumer citing it is vacuously
true — including each of the 80 hypothesis slots the #78 migration
reroutes here, and the 152 branch's 68-cell conditioned core if read
over this Conv. The assumption class `R-TheRowsAreOpenInTheLiterature`,
`E-RingCircle`, and this file's docking role apply to the TYPED rows
ONLY (ruling, `d768d1a494`/`c7bb4fd22b`; "open"/"never discharged"
understates the state — on this Conv the rows are REFUTED, not open).
The file is kept on main as the bookkeeping marker #78's migration
cites; no consumer on main should be scheduled as if the rows could
be supplied — they cannot, on this Conv.

THE LIVE INTERFACE is on `minustwo/rcic-d152b`: `RowsT`/`RowsTWf`
built on the typed face's four-argument `Conv E n Γ a b A` —
`RcicDeclarative.lean:1216`, landed by `8fc19d1f10` ("rcic knife 2a:
the declarative theory D-RCIC-0 transcribed", #3681); derived
`TyConv E n Γ A B` at `:1356`, added by `1119f9fe63` ("wip: I-3a
RcicDeclarative"). Every constructor of that `Conv` carries typing
evidence (`refl` needs `HasTy a A`; `beta`/`zeta`/`delta`/`iota`/
`lit` carry component typings; `app`/`lam`/`pi`/`letE` are typed
congruences; `irr` needs `P : sort 0` plus `p,q : P`; `tyConv` needs
a sort-indexed retype) — `totalConv`'s three mechanisms (untyped
`irr`/`app`/`beta`) are not expressible there — and
`irrRetypeDeadD152by` is the compiled `irr`-confinement to Prop
indices. When I-2's typed root edit lands on main (RCIC first
priority per `d768d1a494`), THIS file's fields re-key to the
`TyConv`-primary statements and `RowsT` becomes the honest single
interface; until then its legs carry the statuses above.
closure_claim stays 0. -/

import rcic.RcicInvertFamily

namespace Rcic.Declarative

/-- THE ROW POSITION — the three §19.2 rows as one named hypothesis,
    on main's untyped `Conv` — REFUTED on this `Conv`
    (`rowsT_false_of_envWf`; `RcicUntypedConvCollapse`/
    `sortConvChar_empty_false`, `d768d1a494`): `sortConvChar` and
    `famAppConvInj` are refuted statements, `piConvInj` is degenerate,
    so `RowsT` is uninhabitable at every `EnvWf` and every citing
    consumer is vacuous — pending I-2's typed-face landing. -/
structure RowsT (E : ResolvedEnv) (n : Nat) : Type where
  sortConvChar : SortConvChar E n
  piConvInj : PiConvInj E n
  famAppConvInj : FamAppConvInj E n

#print axioms RowsT

end Rcic.Declarative
