import rcic.ScmSrcGroups
import rcic.ScmSrcGroupsKernelRfl

/-! Stage 3b: machine acceptance of the K3c source environment.

Every receipt is a Bool over `srcMembersG` closed by `decide`, running
`kernelStepRaw ⟨⟨xEnv (srcPrefixEnv r), 0, []⟩, task, 65536⟩` on the
literal-expanded member (`expandLits`, 00 §19.7 E-NatRef: a pure syntax
map from numerals to constructor chains, applied at emission time to
both the task and the environment).

Coverage (168 slots):
* 90  inductive/constructor mtypes infer a sort — `srcTypesOkX`
      (ScmSrcGroups.lean, re-checked with the `convCert` `.app` arm);
* 26  recursor mtypes infer a sort — `srcRecTypesOkX`;
* 29  definition bodies `.check` against their mtype —
      `srcDefBodiesOkX` (`.accepted .checked`);
* 23  theorem mtypes infer a sort — `srcThmTypesOkX`;
* 21  theorem bodies `.check` against their stored mtype —
      `srcThmBodiesOkX`.  The remaining two theorem bodies, slots 159
      (`nthBNilVa`) and 160 (`vLBNil`), are pinned individually.
* one `.convAt` receipt for a δ-under-argument conversion on a real
  member (`vb0`'s `ValueAt boundBool …` against its δ-form), the case
  the `.app` congruence arm exists for.

Named refusals (the machine's honest residues; honest typing of both
bodies is `tyThm159`/`tyThm160` in `ScmSrcGroupsConv`):
* slot 159 `nthBNilVa` — `[rcic_infer_const_levels_out_of_slice]`, at
  universe bound 0 and also at bound 1: the machine's const-level slice
  refuses `BL.rec.{1}` regardless of `n`;
* slot 160 `vLBNil` — `[rcic_conv_mismatch]` under the expanded env
  (the stored proof term differs from `cctLbPf` only by proof
  irrelevance, which the machine does not implement), and
  `[rcic_whnf_unknown_ctor]` in the unexpanded prefix env
  (`checkmVLBNil`).

No `native_decide`; axioms ⊆ `{propext, Quot.sound}`. -/

open Rcic.Declarative Rcic.Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Rcic.Scm.SrcG

/-- `infer` of the expanded type yields a sort, in the expanded prefix
env at `n = 0`. -/
def infersSortX (r : Nat) (T : Expr Nat) : Bool :=
  match kernelStepRaw
      ⟨⟨xEnv (srcPrefixEnv r), 0, []⟩, .infer (expandLits T), 65536⟩ with
  | .result (.accepted (.inferredType (.sort _))) => true
  | _ => false

/-- `check` of the expanded body against the expanded type is
`.accepted .checked`. -/
def checksX (r : Nat) (n : Nat) (e T : Expr Nat) : Bool :=
  match kernelStepRaw
      ⟨⟨xEnv (srcPrefixEnv r), n, []⟩,
        .check (expandLits e) (expandLits T), 65536⟩ with
  | .result (.accepted .checked) => true
  | _ => false

theorem srcRecTypesOkX :
    srcMembersG.all (fun p =>
      if decide (p.2.mclass = .recursorM)
      then infersSortX p.1 p.2.mtype else true) = true := by decide

theorem srcDefBodiesOkX :
    srcMembersG.all (fun p =>
      if decide (p.2.mclass = .definitionM)
      then checksX p.1 0 (p.2.body.getD (.sort .zero)) p.2.mtype
      else true) = true := by decide

theorem srcThmTypesOkX :
    srcMembersG.all (fun p =>
      if decide (p.2.mclass = .theoremM)
      then infersSortX p.1 p.2.mtype else true) = true := by decide

theorem srcThmBodiesOkX :
    srcMembersG.all (fun p =>
      if decide (p.2.mclass = .theoremM) && !decide (p.1 = 159) &&
          !decide (p.1 = 160)
      then checksX p.1 0 (p.2.body.getD (.sort .zero)) p.2.mtype
      else true) = true := by decide

theorem srcRecCount :
    (srcMembersG.filter (fun p => decide (p.2.mclass = .recursorM))).length
      = 26 := by decide

/-- Slot 159 under the expanded prefix env: refused at `n = 0` … -/
theorem checkxNthBNilVa_n0 :
    kernelStepRaw ⟨⟨xEnv (srcPrefixEnv 159), 0, []⟩,
        .check (expandLits (mNthBNilVa.body.getD (.sort .zero)))
          (expandLits mNthBNilVa.mtype), 65536⟩ =
      .result (.refused "[rcic_infer_const_levels_out_of_slice]") := by rfl

/-- … and still refused at level bound 1: `BL.rec.{1}` is outside the
machine's const-level slice, independent of `n`. -/
theorem checkxNthBNilVa_n1 :
    kernelStepRaw ⟨⟨xEnv (srcPrefixEnv 159), 1, []⟩,
        .check (expandLits (mNthBNilVa.body.getD (.sort .zero)))
          (expandLits mNthBNilVa.mtype), 65536⟩ =
      .result (.refused "[rcic_infer_const_levels_out_of_slice]") := by rfl

theorem checkxVLBNil :
    kernelStepRaw ⟨⟨xEnv (srcPrefixEnv 160), 0, []⟩,
        .check (expandLits (mVLBNil.body.getD (.sort .zero)))
          (expandLits mVLBNil.mtype), 65536⟩ =
      .result (.refused "[rcic_conv_mismatch]") := by rfl

/-- `vb0`'s stored Prop with `boundBool` δ-unfolded in the
`ValueAt` first argument. -/
def vb0Delta : Expr Nat :=
  match mVb0.mtype with
  | .app (.app h a) b => .app (.app h (mBoundBool.body.getD a)) b
  | e => e

theorem vb0Delta_ne : vb0Delta ≠ mVb0.mtype := by decide

theorem ksr_conv_vb0 :
    kernelStepRaw ⟨⟨xEnv (srcPrefixEnv 144), 0, []⟩,
        .convAt (.sort .zero) (expandLits mVb0.mtype)
          (expandLits vb0Delta), 65536⟩ =
      .result (.accepted .conversionConfirmed) := by rfl

#print axioms srcRecTypesOkX
#print axioms srcDefBodiesOkX
#print axioms srcThmTypesOkX
#print axioms srcThmBodiesOkX
#print axioms srcRecCount
#print axioms checkxNthBNilVa_n0
#print axioms checkxNthBNilVa_n1
#print axioms checkxVLBNil
#print axioms vb0Delta_ne
#print axioms ksr_conv_vb0

end Rcic.Scm.SrcG
