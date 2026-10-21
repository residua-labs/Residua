import rcic.RcicNativeTypedModelCovPStrict

/-!
# Concrete K controls for the strict compact filter

The positive guarded Eq computation keeps its universe observation, and
the existing apart-index control remains bottom-only. These compose the
landed K results; no ApproxTKR or ordinary-iota proof is reconstructed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit TypedModelKControlAudit
open ReadbackCKAudit ReadbackCK2ModelObstructionAudit

theorem approxTKStrictP_eqGap_prop (n : Nat) (ρ : EnvT) :
    ApproxTKStrictP eqEnvT n eqGapCtx ρ eqGapRedex .prop :=
  ⟨approxTK_eqGap_prop n ρ, by simp [CovPStrictCompact]⟩

theorem approxTKStrictP_apartRec_bot {n : Nat} {ρ : EnvT} {c : CptT}
    (h : ApproxTKStrictP eqEnvT n apartCtx ρ apartRec c) : c = .bot :=
  approxTK_apartRec_bot h.1

theorem covP_strict_K_positive_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    ApproxTKStrictP eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop ∧
    ApproxTKStrictP eqEnvT n eqGapCtx EnvT.bot (.sort .zero) .prop ∧
    (CptT.prop ≠ .bot) :=
  ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, approxTKStrictP_eqGap_prop n EnvT.bot,
    ⟨approxTK_sort_code eqEnvT n eqGapCtx EnvT.bot .zero, by simp [CovPStrictCompact]⟩,
    fun h => CptT.noConfusion h⟩

theorem covP_strict_K_apart_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    ApproxTKStrictP eqEnvT n apartCtx EnvT.bot apartRec .bot ∧
    (∀ c, ApproxTKStrictP eqEnvT n apartCtx EnvT.bot apartRec c → c = .bot) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨apartCtx_wf n⟩, apartRec_typed n,
    approxTKStrictP_bot _ _ _ _ _, fun _ h => approxTKStrictP_apartRec_bot h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_K_ROOTS
#print axioms approxTKStrictP_eqGap_prop
#print axioms approxTKStrictP_apartRec_bot
#print axioms covP_strict_K_positive_control
#print axioms covP_strict_K_apart_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
