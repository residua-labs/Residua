import rcic.ScmSrcGroupsFunRecEntryCheck
import rcic.RcicTypedIdxAdmitted
import rcic.RcicTypedEnv
import rcic.RcicTypedCheck
import rcic.ScmSrcGroupsFunRecTypedVA0
import rcic.ScmSrcGroupsFunRecTypedVA1
import rcic.ScmSrcGroupsFunRecTypedVA2

/-! K3c under B2: the four function-recursive constructors' typed ι.

The legacy stage-2 judgment refuses CCT 103 (`cctSum`), CCT 104 (`cctRec`),
ValueAt 139 (`vaList`) and ValueAt 142 (`vaR`) at conjunct 3, and those canaries
(`cctFunRecRefused_103`, `cctFunRecRefused_104`, `valueAtFunRecRefused_139`,
`valueAtFunRecRefused_142`) remain true and unmodified: the legacy path is
unchanged. Under R-NoFunRec-1 B2 the typed root places function-recursive ι on
`IotaWitnessS`, with field analysis and the canonical reduct sourced from
admission (`fieldShapesFuel` / `iotaOpenRhs` at `preMajorBvars`/`fieldBvars`).

This module carries the typed recursor/index obligations; the downstream
modules `ScmSrcGroupsFunRecTypedInst` and `ScmSrcGroupsFunRecTypedEq` carry the
instance-level computations:

1. `cctRecIdxAdmittedT` / `vaRecIdxAdmittedT`: the `RecursorGroupIdxAdmittedT`
   obligations for the recursors at slots 105 and 143, built through
   `ofCheck` over the real admissions' descriptor clauses (this module).
2. Canonical coverage (`…TypedInst`): for each of the four constructors the
   covered witness's `schema`/`shapes`/`preMajor`/`fields` are the
   `rhsLit`/`shapesLit` literals of `ScmSrcGroupsFunRecEntry`, and
   `iotaLhsOfS`/`iotaRhsOfS` compute at the canonical equation arguments.
3. Closed instances (`…TypedInst`): an `IotaWitnessS` per constructor at
   closed `.lit` arguments, with the expected reduct written as data (no
   `instPrefix` in the statement — the literal is the by-hand substitution of
   the closed arguments into `rhsLit`, produced as an independent literal so
   the kernel check is a real comparison) and the typed ι step
   `DerivedIotaT.of`.
4. The typed checked equation `IotaEquationTypedT` for all four, via
   `synCheck` (`…TypedEq`).
5. `RecursorGroupIdxAdmittedT.bound` instantiated at one closed witness
   (`…TypedInst`).

The `lhsLit…` literals are the equation TYPES (`iotaLhsType`/`iotaEquationType`,
motive at the result indices), not `iotaLhsOfS` redexes; the corresponding
`iotaLhsOfS` forms and the mismatch are recorded explicitly. -/

open Rcic.Declarative Rcic.Scm.SrcG Rcic.Scm.SrcG.FunRecEntry
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecTyped

/-! ### The descriptor clauses in the judgment's form -/

private theorem hresCCT' (i : Fin aRecCCT.constructors.length) :
    (aRecCCT.constructorViews i).resultIndices.map
      (lift (aRecCCT.constructorViews i).fields.length
        (1 + aRecCCT.constructors.length + aRecCCT.family.indices.length)) =
    (aRecCCT.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨k+8, h⟩ =>
      exact absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega)

/-- CCT's ι descriptor clause, judgment form (`#6160`: motive at the result
indices; parameter-free, so this is the 05 clause retyped). -/
def cctIotaClause : IotaDescriptorClause (envPre 105) aRecCCT :=
  admRecCCT05.h14.toJudgment fun i => iotaLhsType_eq_05 rfl (hresCCT' i)

-- ValueAt's ι descriptor clause `vaIotaClause` lives in
-- `ScmSrcGroupsFunRecTypedVA` (imported transitively below).

/-! ### Step 1: the typed recursor/index obligations -/

-- The decidable closure-and-canonical-witness check for the CCT recursor
-- (slot 105), including function-recursive constructors 6 and 7.
kernel_rfl_theorem cctRecIdxAdmittedB :
  recIdxAdmittedTB aRecCCT cctIotaClause = true

/-- The typed recursor/index obligation for `recCCT`. -/
def cctRecIdxAdmittedT : RecursorGroupIdxAdmittedT aRecCCT cctIotaClause :=
  .ofCheck aRecCCT cctIotaClause cctRecIdxAdmittedB


/-! ### Step 1 (ValueAt): the split `recIdxAdmittedTB` check

The whole-`recIdxAdmittedTB` evaluation for the nine-constructor ValueAt
admission exceeds the kernel's deterministic step budget in one pass — and the
budget is cumulative per source file, so the per-constructor leaves are split
across three modules:

- `ScmSrcGroupsFunRecTypedVA` : `vaIotaClause`, the `constsMemberFuel`
  `lift`/`policyPi`/telescope decomposition lemmas (`vaTel0`–`vaTel8`), the
  generic `fieldBvars`/`policyParameterLocals`/family-head sweeps, the
  freshness/closedness leaves, and `vaCtorCheckB` (`recIdxCtorB` —
  public in `RcicTypedIdxAdmitted` — at `aRecValueAt`/`vaIotaClause`).
- `ScmSrcGroupsFunRecTypedVA0`/`VA1`/`VA2` : the `kernel_rfl` leaves and the
  assembled `vaCtorB0`–`vaCtorB8` for constructors 0–3, 4–6 and 7–8
  respectively.

Each leaf is a separate `kernel_rfl_theorem` so no single kernel evaluation
crosses the deterministic step budget; each module stays under the cumulative
per-file budget. -/

-- `recIdxCtorB` is `recIdxAdmittedTB`'s per-constructor conjunct (public in
-- `RcicTypedIdxAdmitted`); `vaCtorCheckB` is its `aRecValueAt`/`vaIotaClause`
-- specialization, so each branch below is discharged by the corresponding
-- `vaCtorB…` theorem via definitional unfolding.
theorem vaRecIdxAdmittedB : recIdxAdmittedTB aRecValueAt vaIotaClause = true := by
  unfold recIdxAdmittedTB
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨rfl, rfl⟩, rfl⟩, ?_⟩
  rw [List.all_eq_true]
  intro j hj
  have hjlen : j < aRecValueAt.constructors.length := List.mem_range.mp hj
  rw [dif_pos hjlen]
  match j, hjlen with
  | 0, h => exact vaCtorB0
  | 1, h => exact vaCtorB1
  | 2, h => exact vaCtorB2
  | 3, h => exact vaCtorB3
  | 4, h => exact vaCtorB4
  | 5, h => exact vaCtorB5
  | 6, h => exact vaCtorB6
  | 7, h => exact vaCtorB7
  | 8, h => exact vaCtorB8
  | k+9, h =>
      have : aRecValueAt.constructors.length = 9 := rfl
      rw [this] at h
      exact absurd h (by omega)

/-- The typed recursor/index obligation for `recValueAt`. -/
def vaRecIdxAdmittedT : RecursorGroupIdxAdmittedT aRecValueAt vaIotaClause :=
  .ofCheck aRecValueAt vaIotaClause vaRecIdxAdmittedB

end Rcic.Scm.SrcG.FunRecTyped
