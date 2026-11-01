import rcic.RcicF3PropBoolNoCompletion
import rcic.RcicF3IndexedWrapIotaAttack

/-!
# The exact Wrap attack extension has no admitted completion

This specializes the admission-origin obstruction to the same extension
used by the full Wrap `IotaAt` counterexample. It neither changes that
counterexample nor produces iota coherence in other admitted completions.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedWrapIotaAttack
open Rcic.Declarative
open Rcic.Declarative.Ann (EnvSub)

theorem no_admitted_completion {F : ResolvedEnv}
    (hF : EnvWfT F) (hsub : EnvSub extension F) : False :=
  AdmittedCompletion.no_admitted_completion lookups hF hsub

theorem no_admitted_common_completion :
    ¬ ∃ F : ResolvedEnv, Nonempty (EnvWfT F) ∧ EnvSub extension F := by
  rintro ⟨F, ⟨hF⟩, hsub⟩
  exact no_admitted_completion hF hsub

end Rcic.F3.PSet.IndexedWrapIotaAttack

#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.no_admitted_completion
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.no_admitted_common_completion
