/-
DT-019 — the ι subject-reduction front (`IotaSRT`/`IotaSRTΓ`/
`IotaSRTN`, declared `RcicStepsSREnvWf.lean` / `RcicDT1011Rows.lean`):
the measurement and the buildable pieces, now that R6a
(`research/rcic/corr`) and the scm ι work (`ind_admit_iota*.scm`,
`RcicIATyped*`, `ScmSrcGroupsRec*`'s `admRec*`/`iotaEqTyped_of`) have
landed.

Measured on main (Lean batch 42):

- The fronts' evidence domain is `DerivedIota` — `Step.iota`'s own
  constructor (`RcicDeclarative.lean:2645`). `DerivedIotaT` /
  `DerivedIotaU` evidence (the shape/union readings the corr lanes
  produce) is consumed by OTHER routes — `iotaPreserveTT`/`TU`/`TDU`/
  `TDW`, the erasure and conv bridges. `Step.iota` never produces it,
  so the corr legs cannot widen what the fronts quantify over.
- Every ι-preservation on main returns `Nonempty` — the Ann erasure
  cannot project to `Type` (`RcicDT1011Rows.lean:42-44`). The
  `Σ'`-level output of `IotaSRT`/`IotaSRTΓ` is therefore producible
  ONLY where `DerivedIota` is uninhabited: the vacuity route.
  `noDerivedIota_emptyEnv` (`RcicDTMetaTypedEmbed.lean:229`) supplies
  it at `emptyEnv` — the sole `DerivedIota`-free env pinned on main.
- `iotaSRTN_of_inScope` (`RcicDT1011Rows.lean:139`) already feeds the
  `Nonempty`-strength front `IotaSRTN` under `InScope` via
  `iotaPreserveT`.
- The rows dispatchers' `.iota` arm is pinned at `.beta` only
  (`pin_DT010T_rows_beta`, `pin_DT011T_rows_beta`): the front is never
  consumed at a real redex. `wSuccU1` / `pinIotaLhsTy` /
  `corrCertsBelow_natEnvU` supply one at `natEnvU`.

Buildable pieces landed here:

- `iotaSRT_of_noDerivedIota`, `iotaSRTΓ_of_noDerivedIota`,
  `iotaSRTN_of_noDerivedIota` — generic vacuity adapters, the only
  `Σ'`-strength producers `EnvWfT` alone can yield.
- `pin_iotaSRT_emptyEnv` / `pin_iotaSRTΓ_emptyEnv` /
  `pin_iotaSRTN_emptyEnv` — all three fronts inhabited at `emptyEnv`.
- `iotaSRTN_of_corrCertsBelowU` — the front under the row's
  `CorrCertsBelowU` leg via `derivedIotaU_ofDerivedIota` +
  `iotaPreserveTU`. For `DerivedIota` evidence the union's `.ofU` arm
  rides `hasTyT_iota_sr` (InScope only) — `hC` is the caller's own
  leg, honestly retained, not semantically needed at `.ofU` evidence.
  (`iotaPreserveTDU`/`TDW` adapters are deliberately NOT built: their
  `hselD`/`hselW` selectors are dead premises for `.ofU` evidence —
  stating them would fake need.)
- `pin_iotaSRTN_natEnvU`, `pin_iotaSRTN_natEnvU_corrU` — the front at
  the real env under both census legs.
- `pin_DT010T_rows_iota`, `pin_DT011T_rows_iota` — the rows
  dispatchers' `.iota` arm exercised end-to-end at `wSuccU1`, the
  `N.rec.{1}` succ redex at `natEnvU`.

Not built (measured, not debt): a non-vacuous `IotaSRT`/`IotaSRTΓ`
producer — impossible at `EnvWfT` alone, `Nonempty` cannot project to
`Type`. `closure_claim` stays 0.
-/
import rcic.RcicDT1011Rows
import rcic.RcicDTMetaTypedEmbed
import rcic.RcicAnnIotaCorrU
import rcic.RcicDerivedIotaU

namespace Rcic.Declarative

/-! ## vacuity adapters — the only `Σ'`-strength route -/

/-- Any environment whose `DerivedIota` is uninhabited discharges the
    `Σ'`-level front outright. The ONLY `Σ'`-strength route `EnvWfT`
    can produce: every landed ι-preservation is `Nonempty`-valued, and
    `Nonempty` cannot eliminate into `Type`. -/
def iotaSRT_of_noDerivedIota {E : ResolvedEnv}
    (hno : ∀ lhs rhs, DerivedIota E lhs rhs → False) {n : Nat} :
    IotaSRT E n :=
  fun {_ _ _ _} hd _ => (hno _ _ hd).elim

/-- The Γ-fronted variant: same vacuity discharge, the supplied
    `CtxWfT` ignored — there is no redex to consume it on. -/
def iotaSRTΓ_of_noDerivedIota {E : ResolvedEnv}
    (hno : ∀ lhs rhs, DerivedIota E lhs rhs → False) {n : Nat} :
    IotaSRTΓ E n :=
  fun {_ _ _ _} _ hd _ => (hno _ _ hd).elim

/-- The `Nonempty`-strength front at vacuity — same route, weaker
    conclusion. -/
def iotaSRTN_of_noDerivedIota {E : ResolvedEnv}
    (hno : ∀ lhs rhs, DerivedIota E lhs rhs → False) {n : Nat} :
    IotaSRTN E n :=
  fun {_} _ {_ _ _} hd _ => (hno _ _ hd).elim

/-- PIN: `IotaSRT` at `emptyEnv` — a real `Σ'`-strength instance
    (vacuous, since `emptyEnv.members` is `none` everywhere and the
    witness's `hrec` lookup contradicts). `def`, not `theorem`:
    `IotaSRT` is `Type`-valued. -/
def pin_iotaSRT_emptyEnv (n : Nat) : IotaSRT emptyEnv n :=
  iotaSRT_of_noDerivedIota noDerivedIota_emptyEnv

/-- PIN: `IotaSRTΓ` at `emptyEnv` (`def` — `IotaSRTΓ` is `Type`-valued). -/
def pin_iotaSRTΓ_emptyEnv (n : Nat) : IotaSRTΓ emptyEnv n :=
  iotaSRTΓ_of_noDerivedIota noDerivedIota_emptyEnv

/-- PIN: `IotaSRTN` at `emptyEnv`. -/
theorem pin_iotaSRTN_emptyEnv (n : Nat) : IotaSRTN emptyEnv n :=
  iotaSRTN_of_noDerivedIota noDerivedIota_emptyEnv

/-! ## the corr-union leg -/

/-- The front under the census row's `CorrCertsBelowU` leg:
    `DerivedIota` evidence wraps into `DerivedIotaU` (`.ofU`) and rides
    `iotaPreserveTU`. For `.ofU` evidence the union consumer takes the
    premise-free `hasTyT_iota_sr` arm — `hC` is retained because it IS
    the row's leg, but is not semantically needed on `DerivedIota`
    evidence. -/
def iotaSRTN_of_corrCertsBelowU {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) (hC : CorrCertsBelowU E) {n : Nat} :
    IotaSRTN E n :=
  fun {_} hΓ {_ _ _} hd hl =>
    (iotaPreserveTU hW hP hΓ hC (derivedIotaU_ofDerivedIota hd) hl).elim
      fun h' => ⟨_, h', .refl _ _⟩

/-- PIN: `IotaSRTN` at `natEnvU` under `InScope` — the front inhabited
    at a real env with a live ι-redex (`wSuccU1`). -/
theorem pin_iotaSRTN_natEnvU {n : Nat} : IotaSRTN natEnvU n :=
  iotaSRTN_of_inScope natEnvUWfT natEnvUWfT_inScope

/-- PIN: `IotaSRTN` at `natEnvU` under the corr-union leg —
    `corrCertsBelow_natEnvU` lifts to `CorrCertsBelowU`, the
    certificate `vecEnvUT`'s countermodel shows cannot be assumed
    universally. -/
theorem pin_iotaSRTN_natEnvU_corrU {n : Nat} : IotaSRTN natEnvU n :=
  iotaSRTN_of_corrCertsBelowU natEnvUWfT natEnvUWfT_inScope
    (corrCertsBelowU_of_below corrCertsBelow_natEnvU)

/-! ## the front consumed: `.iota` through the rows dispatchers -/

/-- PIN (front consumed): `DT010T_one_step_subject_reduction_of_typedRowsWf`'s
    `.iota` arm at `wSuccU1` — the `IotaSRTN` front supplied via
    `iotaSRTN_of_inScope`, the redex `N.rec.{1}` on `succ` at `natEnvU`.
    `pin_DT010T_iota` exercises the `oneStepSRT`/InScope route; this is
    the ROWS route — the front is load-bearing data here, not inlined
    scope. -/
theorem pin_DT010T_rows_iota :
    ∃ B, Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) B) ∧
      Nonempty (TyConvT natEnvU 1 [] (.const 0 []) B) :=
  DT010T_one_step_subject_reduction_of_typedRowsWf natEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1)
    (iotaSRTN_of_inScope natEnvUWfT natEnvUWfT_inScope)
    CtxWfT.nil pinIotaLhsTy (Step.iota [] _ _ (DerivedIota.of wSuccU1))

/-- PIN (multi-step): the same redex through the `Steps.step` chain —
    `steps_srT_rows`' inductive arm at `.iota`, front consumed each
    step. -/
theorem pin_DT011T_rows_iota :
    ∃ B, Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) B) ∧
      Nonempty (TyConvT natEnvU 1 [] (.const 0 []) B) :=
  DT011T_multi_step_subject_reduction_of_typedRowsWf natEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1)
    (iotaSRTN_of_inScope natEnvUWfT natEnvUWfT_inScope)
    CtxWfT.nil pinIotaLhsTy
    (Steps.step _ _ _ _ (Step.iota [] _ _ (DerivedIota.of wSuccU1))
      (Steps.refl [] (iotaRhsOf wSuccU1)))

#print axioms Rcic.Declarative.iotaSRT_of_noDerivedIota
#print axioms Rcic.Declarative.iotaSRTΓ_of_noDerivedIota
#print axioms Rcic.Declarative.iotaSRTN_of_noDerivedIota
#print axioms Rcic.Declarative.pin_iotaSRT_emptyEnv
#print axioms Rcic.Declarative.pin_iotaSRTΓ_emptyEnv
#print axioms Rcic.Declarative.pin_iotaSRTN_emptyEnv
#print axioms Rcic.Declarative.iotaSRTN_of_corrCertsBelowU
#print axioms Rcic.Declarative.pin_iotaSRTN_natEnvU
#print axioms Rcic.Declarative.pin_iotaSRTN_natEnvU_corrU
#print axioms Rcic.Declarative.pin_DT010T_rows_iota
#print axioms Rcic.Declarative.pin_DT011T_rows_iota

end Rcic.Declarative
