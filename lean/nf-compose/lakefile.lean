import Lake
open Lake DSL

package nfcompose where
  extraDepTargets := #[`pinSha]

/- Pin check. The bytes are the vendored copy of MST-NF@4432a34
   MSTNecessityExecModelMWE.lean. sha256 is the digest in SOURCE_PIN.md. -/
target pinSha pkg : Unit := do
  let source := pkg.dir / "pinned" / "MSTNecessityExecModelMWE.lean"
  let digest ← IO.Process.output { cmd := "shasum", args := #["-a", "256", source.toString] }
  unless digest.exitCode == 0 do
    error s!"nfcompose_pin_sha_failed: {digest.stderr}"
  let expected := "3949bccb8b940250c130f4a1ee7dc16af237d46200fd90b9fb8607663ffb0758"
  unless digest.stdout.startsWith expected do
    error s!"nfcompose_pin_mismatch: {digest.stdout}"
  return BuildJob.pure ()

lean_lib pinned where
  srcDir := "pinned"
  roots := #[`MSTNecessityExecModelMWE]

/- Existing StepExecModel and the tagged-sum theorem. Read, not copied. -/
lean_lib algorithms where
  srcDir := "../hyper"
  roots := #[`algorithms.ResiduaRCCStepExecModel,
    `algorithms.ResiduaRCCFormalCore,
    `algorithms.ResiduaConfluxMSTNFComposition]

@[default_target]
lean_lib NfCompose where
  roots := #[`NfCompose.Basic, `NfCompose.Bridge, `NfCompose.Sum,
    `NfCompose.Seq, `NfCompose.Prod, `NfCompose.AtMostOne,
    `NfCompose.Dispatch, `NfCompose.Axioms]
