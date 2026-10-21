import rcic.RcicNativeTypedModelCovWIrrelBoundary
import rcic.RcicTypedGroupPins

/-!
# Actual annotation scope for the admitted irrelevance fixture

The fixture extends the admitted And environment by the object-language
axioms `P : Prop`, `p : P`, `F : P -> Prop`, and `q : P`. Its annotation
scope certificate is inherited from the actual And-group certificate.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys

theorem covWIrrelEnv_inScope : covWIrrelEnv_wf.InScope :=
  andEnvUWfT_inScope

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_SCOPE_ROOTS
#print axioms covWIrrelEnv_inScope
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_SCOPE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
