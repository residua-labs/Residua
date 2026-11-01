import rcic.RcicF3PiCanonicalGroup
import rcic.RcicF3PiCanonicalParamsAttack
/-! Complete-admission computation pins for canonical parameter replacement.
These check constructor order, retention of the nullary W constructor, the
higher-order field and the dependent Acc result index. They are elementary
kernel computations, not inhabitation of the whole conditional group bridge.
The imported hidden-parameter fixture separately pays constructor typing,
ordinary soundness and actual raw/beta/let tuples at every numeric label.
`closure_claim = 0`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Rcic.F3.PSet.PiCanonicalGroupAttack
open Rcic.Declarative PiCanonicalGroup

kernel_rfl_theorem w_slots :
  constructors PendAW.recA PendAW.recIota.fuelAt =
    [⟨[.plain (.sort (.succ .zero))], [.bvar 0]⟩,
     ⟨[.plain (.sort (.succ .zero)), .recursive [.bvar 0] [.bvar 1]], [.bvar 1]⟩]

kernel_rfl_theorem acc_slots :
  constructors Rcic.Declarative.Ann.accPGroupAdm Rcic.Declarative.Ann.accPIotaClause.fuelAt =
    [⟨[.plain (.sort .zero), .recursive RoleAttacks.accDomains [.bvar 1]], [.bvar 1]⟩]

end Rcic.F3.PSet.PiCanonicalGroupAttack
