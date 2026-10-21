import rcic.RcicSynTableOfITransfer
import rcic.RcicSynTableBuildI
import rcic.RcicSynSameRankDep
import rcic.RcicSynStepPortsClEut
import rcic.RcicSynClosedEspi

/-!
# `TABLEOFI_SUPPLIER_CENSUS` — machine re-census of `StepSuppliers` at `tableOfI`

Companion to `research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md`.

For each of the 18 `StepSuppliers` fields the census pins the landed closer at
`tbl := tableOfI hW` (`tblI := tableOfI hW` for the `TableOfICompat` closer).
Each `*_tableI` def is **composition only**: it instantiates the landed theorem
with the ι-extended table and adds no premises; the def's remaining telescope is
the *exact* retained wall set for that field.

Census verdict (machine-checked here for the four rows whose instantiations are
closed terms; all 18 rows classified in the companion doc):

* **0 discharged, 18 open, 0 false.** Every closer retains at least one named
  wall — either a (d) surface-CL/occurrence port, a per-head/per-cell port
  package, `TableWF (tableOfI hW)` (PART 2/3's `tableWFI_build`, unlanded), or
  `TableOfICompat hW (tableOfI hW)` (needs `tableWFI_build` + `tableOfI_headM`
  + `tableOf_subset_tableOfI` = `mem_tableOfI_of_mem_tableOf`).
* `es_iota_retained` specifically: `iotaRetained_no_croot_tableOf` refuted the
  `croot` residual at `tableOf`; at `tableOfI` the `iotaRulesOf` rows make
  `CRoot (tableOfI hW)` inhabitable in principle, but no producer of
  `IotaRetainedSimulation`/`IotaRetainedRulePorts` over `tableOfI` exists yet
  (`iotaRetainedSimulation_tableOfI` missing → **open**, not false).

The 14 fields not pinned below (`es_consts`, `es_beta`, `es_zeta`,
`es_zetaLocal`, `es_delta`, `es_iota_retained`, `es_lit`, `es_app`, `es_lam`,
`es_letE`, `es_eta`, `es_fsub`, `pb_case`, `delta_obs`) have closers whose
telescopes interleave field-data implicit binders with explicit wall binders;
pinning them at `tableOfI hW` requires restating those telescopes (or waiting
for `tableWFI_build`, which collapses several walls at once). Their statuses
and named missing lemmas are recorded in the census doc; the four pins below
kernel-check the mechanism for the closers whose walls begin explicitly.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv} {Aw : Nat → Nat}

/-- `es_pi` at `tableOfI`: retained walls = `TableWF (tableOfI hW)`
    (`tableWFI_build`, PART 2/3), `leftCl`/`rightCl` (pi surfaces),
    `occHA`/`occHR` — visible in this def's telescope. -/
noncomputable def es_pi_tableI (hW : EnvWfT E) :=
  es_pi_field_of_tableWF (Eₐ := Eₐ) Aw (tableOfI hW)

/-- `cl_case` at `tableOfI`: retained walls = the per-cell port packages
    (`ClPiPorts`, `ClLamPorts`, `ClAppPorts`, `ClLetEPorts`, `ClConstPorts`)
    and `clOther` over `clResidualTag` (transport-headed non-conv pairs). -/
noncomputable def cl_case_tableI (hW : EnvWfT E) :=
  es_cl_field (Eₐ := Eₐ) Aw (tableOfI hW)

/-- `eut_case` at `tableOfI`: retained walls = the `Eut*Ports` packages, the
    existential `EutAppPorts`, and `eutOther` over `eutResidualTag`. -/
noncomputable def eut_case_tableI (hW : EnvWfT E) :=
  es_eut_field (Eₐ := Eₐ) Aw (tableOfI hW)

/-- `mixed_case` at `tableOfI`: derived by `mixedField_of_cl_eut` — inherits
    exactly the `cl_case`/`eut_case` retained walls. -/
noncomputable def mixed_case_tableI (hW : EnvWfT E) :=
  mixedField_of_cl_eut (Eₐ := Eₐ) Aw (tableOfI hW)

#print axioms es_pi_tableI
#print axioms cl_case_tableI
#print axioms eut_case_tableI
#print axioms mixed_case_tableI

end Rcic.Syn
