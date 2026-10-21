import rcic.RcicNativeTypedModelCovVAligned
import rcic.RcicNativeTypedModelKIndexFree

/-!
# Native eligibility of the retained proposition-recursion environments

Every old proposition-recursion witness in Eq, True and And has a recursor
reference with an explicit legacy native K witness. Nat and the empty
environment have no proposition-recursion witnesses. These environment facts
justify transport of actual old observations; the concrete supplies are kept
in CovVControls and CovVFixtures. No arbitrary environment is classified.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKTransportAudit TypedModelKIndexFreeAudit
open ReadbackCKAudit

theorem covV_eq_native_heads : CovVPropHeadsNative eqEnvT := by
  intro w _
  by_cases hr : w.recRef = 65
  · exact Or.inl ⟨eqGapW, hr.symm, ⟨rfl, rfl, rfl⟩⟩
  · have hm := w.hrec
    by_cases h64 : w.recRef = 64
    · rw [eqEnvT_mem, if_neg hr, if_pos h64] at hm
      have he : w.recMember = eqReflT := (Option.some.inj hm).symm
      have hc := w.hrecK
      rw [he] at hc
      cases hc
    · by_cases h63 : w.recRef = 63
      · rw [eqEnvT_mem, if_neg hr, if_neg h64, if_pos h63] at hm
        have he : w.recMember = eqFamT := (Option.some.inj hm).symm
        have hc := w.hrecK
        rw [he] at hc
        cases hc
      · rw [eqEnvT_mem, if_neg hr, if_neg h64, if_neg h63] at hm
        cases hm

theorem covV_true_native_heads : CovVPropHeadsNative trueEnvU := by
  intro w _
  exact Or.inl ⟨wTrueRecU, (true_rec_metadata w).1.symm, ⟨rfl, rfl, rfl⟩⟩

theorem covV_and_native_heads : CovVPropHeadsNative andEnvU := by
  intro w _
  exact Or.inr ⟨mixAndW, (and_rec_metadata w).1.symm, kfieldW_mixAndW⟩

theorem covV_nat_native_heads : CovVPropHeadsNative natEnvU := by
  intro w hP
  have hd := natEnvU_witness_refs (fun _ _ h => h)
    w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  change piBody w.famMember.mtype = .sort .zero at hP
  rw [hd.1.2] at hP
  cases hP

theorem covV_empty_native_heads : CovVPropHeadsNative emptyEnv := by
  intro w _
  have h := w.hrec
  cases h

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_NATIVE_HEADS_ROOTS
#print axioms covV_eq_native_heads
#print axioms covV_true_native_heads
#print axioms covV_and_native_heads
#print axioms covV_nat_native_heads
#print axioms covV_empty_native_heads
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_NATIVE_HEADS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
