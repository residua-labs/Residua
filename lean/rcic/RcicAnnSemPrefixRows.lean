import rcic.RcicAnnRowsSupply
import rcic.RcicAnnViewTySem

/-!
# M3-b GLM-3 — the bounded integration: `EnvWfT` (semantic-prefix entry) gives
the typed chain rows

The one-line composition the architect's work order named: #6165's
`annEnvA_of_envWfT_semPrefix` (an `AnnEnvA` over any `EnvWfT E` with `hW.InScope`,
the group bridge's semantic-prefix entry) composed with GLM-1's
`typedRowsWf_of_annEnvA` (the chain adapter + the three rows). No third bridge,
no new transport — both interfaces already exist and are reviewed.

The group-environment consumption pins (Nat→List; Nat→Vec over a base that already
contains the Nat→List group) are NOT in this file yet: their ready-made module
(`RcicAnnSemPrefixRowsPins`, four False-ending pins on the rows' conclusions over
the two-group environments) was authored on the #6165 side and has not landed in
any ref visible here — re-delivery requested (see GLM_M3B_MIGRATION_MAP.md §14).
This file claims only the composition above.

closure_claim 0; axioms within {propext, Quot.sound}; no row premises, no
`RowsT`/`EnvSemA`/`IotaSRA` demanded of the caller.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- THE INTEGRATION: any `EnvWfT` environment in the bridge's scope bears the
    three typed chain rows. -/
theorem typedRowsWf_of_envWfT_semPrefix
    {E : ResolvedEnv}
    (hW : EnvWfT E)
    (hP : hW.InScope)
    (n : Nat) :
    TypedRowsWf E n := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact typedRowsWf_of_annEnvA C hn n

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.typedRowsWf_of_envWfT_semPrefix
