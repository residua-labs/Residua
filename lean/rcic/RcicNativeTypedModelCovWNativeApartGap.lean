import rcic.RcicNativeTypedModelCovWNativeCore
import rcic.RcicNativeReadbackCK2ModelObstruction

/-!
# The exact apart-index obligation after removal of the DI guard

The earlier DI separation is not a native conversion-separation theorem.
This module names the required concrete native separation and proves that
it excludes every direct native K head at the original apart source. It
also records the requested full new-grammar bottom-only statement as an
unsupplied proposition. No theorem here asserts that proposition or counts
apart retention as checked. Native admission, context typing, source typing
and the new bottom observation remain genuinely inhabited.
`closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2ModelObstructionAudit ReadbackCK2InputsAudit
open TypedModelCovWIrrelAudit

/-- The native family conversion required by a canonical K witness at the
original apart source. The existing DI exclusion does not supply this. -/
def CovWNativeApartIndexSeparation (n : Nat) : Prop :=
  ¬ Nonempty (ConvT eqEnvT n apartCtx apartRight
    (apartEqAt apartRight) (.sort .zero))

/-- This is the full retention goal, named explicitly and left unsupplied.
In particular, it includes application and typed-eta derivations. -/
def CovWNativeApartRetention (n : Nat) : Prop :=
  ∀ (ρ : EnvWIrrel) (c : CptWIrrel),
    ApproxTKWNative eqEnvT n apartCtx ρ apartRec c → c = .bot

/-- A concrete native separation certificate would block every direct K
head at apart. This is a consumer of that certificate, not its supplier. -/
theorem covWNative_apart_direct_K_blocked (n : Nat)
    (hsep : CovWNativeApartIndexSeparation n) (e : Expr Nat) :
    ¬ KNativeHead eqEnvT n apartCtx apartRec e := by
  intro h
  generalize he : apartRec = a at h
  cases h with
  | intro hK hnc hi hc =>
      simp only [apartRec, recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      obtain ⟨hconst, hp⟩ := foldApps_const_inj hh
      have hr := (Expr.const.inj hconst).1
      obtain ⟨hcomputed, hmajor⟩ := eqKCanon_families hr.symm hp.symm hK
      obtain ⟨hi⟩ := hi
      rw [hcomputed, hmajor] at hi
      exact hsep ⟨hi⟩

/-- The unproved nonbottom exclusion must not erase the actual native and
bottom premises of the original test. -/
theorem covWNative_apart_inhabited (n : Nat) (ρ : EnvWIrrel) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    ApproxTKWNative eqEnvT n apartCtx ρ apartRec .bot :=
  ⟨⟨pinEqGroupWfT⟩, ⟨apartCtx_wf n⟩, apartRec_typed n, .bot _ _ _⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_APART_GAP_ROOTS
#print axioms CovWNativeApartIndexSeparation
#print axioms CovWNativeApartRetention
#print axioms covWNative_apart_direct_K_blocked
#print axioms covWNative_apart_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_APART_GAP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
