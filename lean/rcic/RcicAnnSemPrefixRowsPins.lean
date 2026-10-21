import rcic.RcicAnnSemPrefixRows
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec
import rcic.RcicRefutations

/-!
# M3-b GLM-3 — consumption pins on the two-group environments

End-to-end pins through the REGISTERED integration
(`typedRowsWf_of_envWfT_semPrefix`, itself `annEnvA_of_envWfT_semPrefix` ∘
`typedRowsWf_of_annEnvA`): a real two-group environment → the semantic-prefix
entry → `TypedRowsWf` → a row CONSUMED → `False`. Each pin ends in `False`,
so each actually uses what a row concludes; no `True`-valued stubs.

This module is the minimal real core (row 1 on both group environments). The
full four-pin set described on the #6165 side (rows 2+1 at `[N]`, row 3 at
List, rows 3+1 at Vec) awaits that side's re-delivery or lands as its own
slice; nothing here pre-claims it. Multi-group (Nat→List→Vec) regression stays
arc D's per the round-3 responsibilities table.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- Nat→List group environment: `Sort 0` and `Sort 1` are not type-convertible
    — row 1 through the semantic-prefix entry on a REAL two-group environment. -/
theorem pin_listEnv_sorts_notTotal {n : Nat}
    (h : TyConvT listEnvUT n [] (.sort .zero) (.sort (.succ .zero))) : False :=
  refutEqN_zero_succ_false
    ((typedRowsWf_of_envWfT_semPrefix listEnvUWfT listEnvUWfT_inScope n).sortRow
      CtxWfT.nil h)

/-- Nat→Vec group environment (base already containing the Nat group): same
    row-1 consumption, the strict-prefix entry path. -/
theorem pin_vecEnv_sorts_notTotal {n : Nat}
    (h : TyConvT vecEnvUT n [] (.sort .zero) (.sort (.succ .zero))) : False :=
  refutEqN_zero_succ_false
    ((typedRowsWf_of_envWfT_semPrefix vecEnvUWfT vecEnvUWfT_inScope n).sortRow
      CtxWfT.nil h)

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.pin_listEnv_sorts_notTotal
#print axioms Rcic.Declarative.Ann.pin_vecEnv_sorts_notTotal
