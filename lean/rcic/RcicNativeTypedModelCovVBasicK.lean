import rcic.RcicNativeTypedModelCovVControls
import rcic.RcicPiModelInversion

/-!
# The concrete field-free and projection K controls

The original True and And controls have nonbottom observations under the
native-eligibility restriction. The observations below construct the exact
structured schema and use the extra native premise at proposition recursion.
The packaged controls also supply their admitted environments, native contexts,
native computation certificates and conversions.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit TypedModelAudit
open TypedModelKIndexFreeAudit ReadbackCKAudit

set_option maxRecDepth 4000

-- The landed adapter has a well-founded constsMemberFuel computation.
-- Its equation lemmas, rather than kernel reduction of the compiled
-- recursor, discharge the two finite recognizer checks.
macro "covV_basic_adapter" : tactic =>
  `(tactic| simp [iotaWitnessSB, directFragCheck, directFragOne,
    iotaWitnessStableB, constsMemberFuel, iotaSchemaS, iotaOpenRhs, iotaArgs,
    trueEnvU, truePrefix, trueFamOnly, andEnvU, andPrefix, andFamOnly,
    emptyEnv, extendEnv,
    trueFamMember, trueIntroMember, trueRecMemberU,
    andFamMember, andIntroMember, andRecMemberU, andApp,
    transparent, instantiateLevels, fieldBvars, ctorFieldTelRaw, lift,
    piTelescopeFuel, whnfFuel, transparentBody, noTransparentB, headStableB,
    piTailOf, esize, piCount, properShapeB, isFamilyApp, instPrefix,
    exprClosedAt, iotaRhsOf, rhsArgs, ctorSpine, ctorMajor, recCall, foldApps,
    recCallField, recPrefix, familyIdx, exactParamLocals, appsSpine,
    occursConst, piDomsOf, instantiate, instantiate0, instLevel,
    canonRecLevels, preMajorBvars, minorTel, shapeOfKind,
    wTrueRecU, mixAndW, mixAndSpine, mixAndMin, mixAndMot, mixAndFamApp, mixPi])

def covVTrueWitness : IotaWitnessS trueEnvU :=
  iotaWitnessSOf wTrueRecU 8 (by covV_basic_adapter)

def covVAndWitness : IotaWitnessS andEnvU :=
  iotaWitnessSOf mixAndW 16 (by covV_basic_adapter)

private theorem covV_empty_application {E : ResolvedEnv} {ρ : EnvT}
    {f x : Expr Nat} {c : CptT}
    (h : ApproxTN E ρ f (.lam [([], c)])) :
    ApproxTN E ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

private theorem covV_empty_lambda {E : ResolvedEnv} {ρ : EnvT}
    {A b : Expr Nat} {c : CptT} (hc : c ≠ .bot)
    (h : ApproxTN E (EnvT.cons (demandT []) ρ) b c) :
    ApproxTN E ρ (.lam A b) (.lam [([], c)]) := by
  refine .lam (.bot _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

/-- The major may be a local proof: the native field-free certificate
is present at the recursor, so the old empty-major-demand row survives. -/
theorem covV_trueK_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) (x : Expr Nat) :
    ApproxTKN trueEnvU n Γ ρ (kRec x) .prop := by
  apply ApproxTKN.free (kFreeT_trueEnvU _)
  have hrec : ApproxTN trueEnvU ρ (.const 2 [.succ (.succ .zero)])
      (curryStepT [[], [.prop], []] .prop) := by
    apply ApproxTN.recursorProp (w := covVTrueWitness)
      (us_pre := [[], [.prop]]) [.succ (.succ .zero)] (by rfl)
      (covV_true_native_heads covVTrueWitness (by rfl)) (by rfl)
    exact .bvar (List.mem_singleton.mpr rfl)
  have hm := covV_empty_application (x := kMot) hrec
  have hminor : ApproxTN trueEnvU ρ kRecHead (.lam [([], .prop)]) := by
    refine .app hm (List.mem_singleton.mpr rfl) ?_
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact .sort ρ .zero
  exact covV_empty_application hminor

theorem covV_trueK_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n kVarCtx) ∧
    Nonempty (NativeSpineHead.Step trueEnvU n kVarCtx
      (kRec (.bvar 0)) (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT trueEnvU n kVarCtx (.sort .zero)
      (kRec (.bvar 0)) (.sort (.succ .zero))) ∧
    ApproxTKN trueEnvU n kVarCtx EnvT.bot (kRec (.bvar 0)) .prop :=
  ⟨⟨trueEnvUWfT⟩, ⟨kVarCtx_wf n⟩, ⟨stepK_kRec_var n⟩,
    ⟨kRec_conv_sort (kVar_ty n)⟩, covV_trueK_observed n kVarCtx EnvT.bot _⟩

/-- Both plain proof fields are ignored by this minor. The surviving
recursor row is justified by the native projection K witness, not by a
field-free premise. -/
theorem covV_andK_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKN andEnvU n Γ ρ mixAndRedex (.pi .bot []) := by
  apply ApproxTKN.free (kFreeT_andEnvU _)
  let d : CptT := .lam [([], .lam [([], .pi .bot [])])]
  have hrec : ApproxTN andEnvU ρ (.const 2 [.succ (.succ .zero)])
      (curryStepT [[], [], [], [d], []] (.pi .bot [])) := by
    apply ApproxTN.recursorProp (w := covVAndWitness)
      (us_pre := [[], [], [], [d]]) [.succ (.succ .zero)] (by rfl)
      (covV_and_native_heads covVAndWitness (by rfl)) (by rfl)
    change ApproxTN andEnvU
      (EnvT.pushArgs ([[], [], [], [d], [], []].map demandT) EnvT.bot)
      (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) (.pi .bot [])
    apply covV_empty_application
    apply covV_empty_application
    exact .bvar (List.mem_singleton.mpr rfl)
  have h0 := covV_empty_application (x := .bvar 4) hrec
  have h1 := covV_empty_application (x := .bvar 3) h0
  have h2 := covV_empty_application (x := mixAndMot) h1
  have hminor : ApproxTN andEnvU ρ mixAndMin d := by
    apply covV_empty_lambda (by intro h; cases h)
    apply covV_empty_lambda (by intro h; cases h)
    exact covV_approxT_of_native_heads covV_and_native_heads
      (approxT_pi_bot_nil andEnvU _ _ _)
  have h3 : ApproxTN andEnvU ρ mixAndRec (.lam [([], .pi .bot [])]) := by
    refine .app h2 (List.mem_singleton.mpr rfl) ?_
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact hminor
  exact covV_empty_application h3

theorem covV_andK_control :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
    Nonempty (NativeSpineHead.Step andEnvU 0 mixAndCtx mixAndRedex mixAndRhs
      (.app mixAndMot mixAndMkApp)) ∧
    Nonempty (ConvT andEnvU 0 mixAndCtx mixAndRedex mixPi
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    ApproxTKN andEnvU 0 mixAndCtx EnvT.bot mixAndRedex (.pi .bot []) :=
  ⟨⟨andEnvUWfT⟩, ⟨Rcic.Domain.Model.PiInversion.mixAndCtx_wf⟩,
    ⟨stepK_mixAnd⟩, mixAnd_conv, covV_andK_observed 0 mixAndCtx EnvT.bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_BASIC_K_ROOTS
#print axioms covVTrueWitness
#print axioms covVAndWitness
#print axioms covV_trueK_observed
#print axioms covV_trueK_control
#print axioms covV_andK_observed
#print axioms covV_andK_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_BASIC_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
