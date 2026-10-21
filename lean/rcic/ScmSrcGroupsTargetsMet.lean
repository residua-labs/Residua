import rcic.ScmSrcGroupsTargets
import rcic.ScmSrcGroupsLK1Pin

/-! Acceptance targets met so far (statements in `ScmSrcGroupsTargets`). -/
namespace Rcic.Scm.SrcG.Targets

/-- The real slot-140 `vaPair` passes normal admission. -/
theorem vaPairBool_met : Targets.vaPairBool := vaPairAdmittedAt

end Rcic.Scm.SrcG.Targets
