import rcic.ScmSrcGroupsEnvWfT17
import rcic.RcicTypedConvIotaPins

/-! `EnvWfT srcEnvG` — the whole 168-slot prefix chain, assembled.

`wft168` reaches `envPre 168`, which is `srcEnvG` as written
(`srcEnvG_eq`).  The single open premise is slot 159's body-typing
`srcNthBTyT` — a deferred composition, not a wall: `convAt?` carries an
ι arm (PR #6205's shared `iotaBetaStep?`/`iotaMid?` selector — fires on
a recursor-on-constructor redex or a λ-headed application the head
stepper could not type, falls through on `none`), so the lane does not
refuse; the measured residual is a kernel whnf recursion bound on
EXTRACTING the conversion derivation (see the
`/- DEFERRED COMPOSITION … -/` note in `ScmSrcGroupsEnvWfT17` and
`RcicTypedConvIotaPins`, KERNEL-SHAPE HONESTY).  So `wft_srcEnvG`
keeps it as a hypothesis (the `BlockedHidxAdm` precedent) and
`envWfT_srcEnvG` applies the hand-built derivation from
`RcicTypedConvIotaPins` — the unconditional statement. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/-- `EnvWfT srcEnvG`, modulo the slot-159 `srcNthBTyT` premise — a
    deferred composition discharged downstream by PR #6225's
    `envWfT_srcEnvG` (the hand-built proof is PR #6205's `srcNthBTyT`;
    the residual is a kernel whnf bound on extracting the conversion,
    not a checker refusal). -/
def wft_srcEnvG
    (srcNthBTyT : HasTyT (envPre 159) 0 []
      (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) :
    EnvWfT srcEnvG :=
  (show envPre 168 = srcEnvG from rfl) ▸ wft168 srcNthBTyT

/-- `EnvWfT srcEnvG` unconditional: the slot-159 premise is discharged by
    `srcNthBTyT` — the hand-built `HasTyT` derivation on the typed-conv
    lane (`RcicTypedConvIotaPins`, PR #6205). -/
def envWfT_srcEnvG : EnvWfT srcEnvG := wft_srcEnvG srcNthBTyT

#print axioms wft_srcEnvG
#print axioms envWfT_srcEnvG

end Rcic.Scm.SrcG
