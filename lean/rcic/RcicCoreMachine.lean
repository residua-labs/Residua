import rcic.RcicMachineSoundTyped

/-!
# RcicCoreMachine — core layer 7: machine soundness

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

Key definitions and theorems of the layer:

* `Rcic.Machine.Ambient` / `Rcic.Machine.RawState` / `Rcic.Machine.StepOutcome` — the abstract machine
* `Rcic.Machine.kernelStepRaw` / `Rcic.Machine.convCert` — the raw kernel step and the conversion certifier
* `Rcic.Machine.MachineRed` — machine reduction chains
* `Rcic.Machine.machineRedSRT` — `HasTyT` preserved along `MachineRed`
* `Rcic.Machine.parRedStarSRT` / `Rcic.Machine.parRedStarConvT` — transports along `ParRedStar` chains
* `Rcic.Machine.RM014T_whnf_typed` — the whnf acceptance's reduct is typed
* `Rcic.Machine.convCert_chains` — every `convCert` acceptance carries `ParRedStar` chains to a common reduct

Layer members: `RcicMachine`, `RcicMachineSoundTyped`.
-/
