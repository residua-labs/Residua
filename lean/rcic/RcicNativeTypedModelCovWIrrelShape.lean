import rcic.RcicNativeTypedModelCovWIrrelNativePositions

/-!
# Native sort/Pi typing separation in the admitted annotation scope

This is composition of the landed annotation supplier, annotation type
coherence, and annotated Pi/sort separation. No native normalization or
raw-star confluence premise is introduced. closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys

theorem covWIrrel_native_not_sort_and_pi {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hScope : hW.InScope)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e : Expr Nat} {l : Level} {D B : Expr Nat}
    (hs : HasTyT E n Γ e (.sort l)) (hp : HasTyT E n Γ e (.pi D B)) : False := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hScope
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := Ann.annCtxWfT' C hn hΓ
  obtain ⟨sA, TS, hsE, hsT, ⟨hts⟩⟩ := Ann.annHasTyT' C hn hs hΓA hctx
  obtain rfl := Ann.erase_eq_sort hsT
  obtain ⟨pA, TP, hpE, hpT, ⟨htp⟩⟩ := Ann.annHasTyT' C hn hp hΓA hctx
  obtain ⟨DA, u, BA, v, rfl, _, _⟩ := Ann.erase_eq_pi hpT
  obtain ⟨hc⟩ := Ann.annTyA C.hE C.hI C.hIS C.hENC C.hEN C.hR
    (C.hS n) Ann.posValA_one hΓA (hpE.trans hsE.symm) htp hts
  exact Ann.tyConvA_pi_sort_false C.hE C.hI C.hIS C.hENC C.hEN C.hR
    (C.hS n) Ann.posValA_one hΓA hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_SHAPE_ROOTS
#print axioms covWIrrel_native_not_sort_and_pi
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_SHAPE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
