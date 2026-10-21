import rcic.RcicTypedGroupPins
import rcic.RcicDTMetaTypedSR

/-!
# DT typed counterparts, segment 2 — DT-003 / DT-023 (+ finding on DT-007)

O2S-pattern typed counterparts (erratum E-O2SCounterparts) for two more
02 §14 rows, over the typed root (`HasTyT`/`ConvT`/`CtxWfT`/`EnvWfT`),
BESIDE the legacy theorems — no legacy statement touched — each with a
consumption pin at `natEnvU` (in scope through `natEnvUWfT_inScope`).

- DT-003 — context regularity: a well-formed context's head assumption is
  sort-typed, read straight off the `CtxWfT.assumption` constructor (the
  `letBinding` arm is recorded too — same inversion, the other cell).
- DT-023 — `bvar 0` in the empty context is untypable on the typed root:
  `hasTyTInv_bvar` reads the lookup, which is `none`.

## Finding `[DT007T_seal_collision]` (named residue, not a patch)

DT-007 (typing regularity) *holds* on the typed root — R-2 is landed as
`hasTyT_type_sort_exists_scope` in `RcicParRedSRTyped` — but the counterpart
cannot be registered in `RcicFoundationSeal`: `RcicParRedSRTyped` cannot be
co-imported with `RcicParRedSR` (already in the seal environment) because
six helper declarations are duplicated between the two files under the
same `Rcic.Declarative` names — `get?_lt_length`
(`RcicParRedSR.lean:79` / `RcicParRedSRTyped.lean:764`),
`lookupType_getQ_letBinding` (`:91` / `:775`),
`lookupType_replace_let_ne` (`:204` / `:788`),
`lookupType_replace_let_zero` (`:209` / `:793`),
`lookupValue_replace_let_ne` (`:220` / `:800`),
`lookupValue_replace_let_zero` (`:225` / `:805`); the first reported
collision is `get?_lt_length.match_1`). The unsealed SRTyped copies exist
only because SRTyped sits outside SR's import chain — the unblock is a
separate PR: rename the six `SRTyped` copies, or move them into a lower
module both files import (e.g. `RcicConvChar`). That unblocks not just
DT-007 but the sealability of the whole parRedSRT segment. Reported here
rather than patched silently; the row's theorem itself,
`hasTyT_type_sort_exists_scope` (`RcicParRedSRTyped.lean:471`), is
unaffected — only its seal registration is blocked.

`dtTypedCensus` lives in `RcicDTMetaTypedLiftSubst` (seg 1); this file adds
the two counterparts it names.
-/

namespace Rcic.Declarative

/-- DT-003 typed: context regularity — a well-formed context whose head is
    an `assumption` cell carries that cell's domain sort-typing. -/
theorem DT003T_context_regularity {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A : Expr Nat}
    (hΓ : CtxWfT E n (LocalDecl.assumption A :: Γ)) :
    ∃ u, Nonempty (HasTyT E n Γ A (.sort u)) := by
  cases hΓ with
  | assumption _ _ u _ hA' => exact ⟨u, ⟨hA'⟩⟩

/-- DT-003 typed, the let arm: a `letBinding` cell's stored domain is
    sort-typed the same way. -/
theorem DT003T_context_regularity_let {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A v : Expr Nat}
    (hΓ : CtxWfT E n (LocalDecl.letBinding A v :: Γ)) :
    ∃ u, Nonempty (HasTyT E n Γ A (.sort u)) := by
  cases hΓ with
  | letBinding _ _ u _ _ hA _ => exact ⟨u, ⟨hA⟩⟩

/-- DT-023 typed: not every raw expression is typable — `bvar 0` in the
    empty context. `hasTyTInv_bvar` reads off the lookup, which is `none`. -/
theorem DT023T_not_everything_typable {E : ResolvedEnv} {n : Nat} :
    ¬ ∃ A, Nonempty (HasTyT E n [] (.bvar 0) A) :=
  fun ⟨_, ⟨h⟩⟩ =>
    let ⟨_, hlk, _⟩ := hasTyTInv_bvar h rfl
    Option.noConfusion hlk

/-! ## consumption pins at `natEnvU` -/

/-- PIN (DT-003T): the head-`Sort 1` context over `natEnvU` — regularity
    recovers its domain's sort-typing (`u = 2`). -/
theorem pin_DT003T_natU {n : Nat} :
    ∃ u, Nonempty (HasTyT natEnvU n [] (.sort (.succ .zero)) (.sort u)) :=
  DT003T_context_regularity
    (CtxWfT.assumption [] (.sort (.succ .zero)) (.succ (.succ .zero))
      CtxWfT.nil (HasTyT.sort [] (.succ .zero)))

/-- PIN (DT-023T): consumed at `natEnvU` — `bvar 0` stays untypable in the
    empty context on the real environment. -/
theorem pin_DT023T_natU {n : Nat} :
    ¬ ∃ A, Nonempty (HasTyT natEnvU n [] (.bvar 0) A) :=
  DT023T_not_everything_typable

end Rcic.Declarative

#print axioms Rcic.Declarative.DT003T_context_regularity
#print axioms Rcic.Declarative.DT003T_context_regularity_let
#print axioms Rcic.Declarative.DT023T_not_everything_typable
#print axioms Rcic.Declarative.pin_DT003T_natU
#print axioms Rcic.Declarative.pin_DT023T_natU
