import rcic.ScmSrcGroupsVaPairEntry
import rcic.ScmSrcGroupsAdm

/-! The `VaPairEntry` environments are the ones `idxValueAt_false` uses: `prefixEnv` is `envPre 143`, and `extEnv` is `ScmSrcGroupsLK1Pin`'s private `EP`, i.e. `extendEnv (envPre 143) 143 recValueAt`; both by `rfl`. Verdict-free: nothing here mentions the walk or the admission Bool. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.VaPairEntry

theorem prefixEnv_eq : prefixEnv = envPre 143 := rfl

theorem extEnv_eq : extEnv = extendEnv (envPre 143) 143 recValueAt := rfl

#print axioms prefixEnv_eq
#print axioms extEnv_eq

end Rcic.Scm.SrcG.VaPairEntry
