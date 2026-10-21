import rcic.RcicNativeReadbackCK2NativeControls

/-!
# Route C, R1: inhabited native Eq guards

These are compositions of the existing admitted Eq fixtures.  The family at
63 has two parameters and one index; its field-free constructor is at 64 and
its AnySort recursor is at 65.  The motive in both controls is the constant
`Sort 1`, the minor is `Sort 0`, and the recursor universe argument is `2`.
Thus the full calls convert at `Sort 1`, not at a proof type.

The one-assumption binder control compares the identity on propositions with
an internal-beta expansion.  The two-assumption eta control compares a neutral
function with its eta expansion.  Their computed and actual indices are not
syntactically equal, but the existing native conversions inhabit both the
family-alignment guard and the common-proposition guard.  Proof irrelevance
therefore applies to the actual proof major and the recursor-side refl canon.

This module adds no reduction rule or observation model.  It does not infer
native nonconvertibility or untypability from the old ordinary-reduction
nonjoinability pins.  No negative native guard at genuinely apart indices is
claimed.  `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.RouteCEqGuard

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit

/-- The actual admitted native Eq environment. -/
def envWf : EnvWfT eqEnvT := pinEqGroupWfT

/-- The smaller control has one local assumption, the Eq proof itself. -/
def binder_context_wf (n : Nat) : CtxWfT eqEnvT n binderEqCtx :=
  binderEqCtxWf n

/-- The eta control keeps both the neutral function and its Eq proof local. -/
def eta_context_wf (n : Nat) : CtxWfT eqEnvT n etaEqCtx :=
  etaEqCtxWf n

/-- The existing generic Eq witness, at the internal-beta control. -/
def binder_witness : IotaWitness eqEnvT :=
  eqConvW (fun _ _ h => h) indexFn indexId indexBinderBeta binderIndexMot (.sort .zero)

/-- The same witness constructor, at the neutral-function eta control. -/
def eta_witness : IotaWitness eqEnvT :=
  eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot (.sort .zero)

/-- The canon repeats the left parameter; the actual family retains its index. -/
theorem binder_families :
    computedFamily binder_witness = binderIndexFamily indexId ∧
      majorFamily binder_witness = binderIndexFamily indexBinderBeta :=
  ⟨eqConvW_computedFamily (fun _ _ h => h) indexFn indexId indexBinderBeta
    binderIndexMot (.sort .zero), rfl⟩

/-- In the eta control the computed index is the neutral function itself. -/
theorem eta_families :
    computedFamily eta_witness = etaIndexFamily (.bvar 1) ∧
      majorFamily eta_witness = etaIndexFamily etaIndex :=
  ⟨eqConvW_computedFamily (fun _ _ h => h) indexFn (.bvar 1) etaIndex
    etaIndexMot (.sort .zero), rfl⟩

/-- Native typing of the local proof at its actual, noncanonical index. -/
def binder_major_typed (n : Nat) :
    HasTyT eqEnvT n binderEqCtx (.bvar 0) (binderIndexFamily indexBinderBeta) :=
  .bvar binderEqCtx 0 _ rfl

/-- Native typing of the eta control's local proof. -/
def eta_major_typed (n : Nat) :
    HasTyT eqEnvT n etaEqCtx (.bvar 0) (etaIndexFamily etaIndex) :=
  .bvar etaEqCtx 0 _ rfl

/-- The complete binder call, including its supplied motive and minor, is typed. -/
def binder_native_typed (n : Nat) :
    HasTyT eqEnvT n binderEqCtx binderIndexRedex (.sort (.succ .zero)) :=
  binderIndexRecTy n binderEqCtx (binder_major_typed n)

/-- The complete eta call is typed at the same positive sort. -/
def eta_native_typed (n : Nat) :
    HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero)) :=
  etaIndexRecTy n (eta_major_typed n)

/-- Native conversion of the one-assumption binder call to its actual minor. -/
def binder_native_conversion (n : Nat) :
    ConvT eqEnvT n binderEqCtx binderIndexRedex (.sort .zero) (.sort (.succ .zero)) :=
  binderIndexRedexConv n

/-- Native conversion of the neutral-function eta call to its actual minor. -/
def eta_native_conversion (n : Nat) :
    ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) (.sort (.succ .zero)) :=
  etaIndexRedexConv n

/-- Internal beta pays both exact native K premises. -/
theorem binder_guards (n : Nat) :
    KIndexConvAt eqEnvT n binderEqCtx binder_witness ∧
      KCommonAt eqEnvT n binderEqCtx binder_witness (.bvar 0) :=
  eqKGate_of_indexConv (fun _ _ h => h) binderIndexMot (.sort .zero)
    (indexFnTy eqEnvT n binderEqCtx) (indexIdTy eqEnvT n binderEqCtx)
    (indexBinderBetaTy eqEnvT n binderEqCtx) (binder_major_typed n)
    (indexBinderBetaConv eqEnvT n binderEqCtx)

/-- Native eta pays both exact native K premises. -/
theorem eta_guards (n : Nat) :
    KIndexConvAt eqEnvT n etaEqCtx eta_witness ∧
      KCommonAt eqEnvT n etaEqCtx eta_witness (.bvar 0) :=
  eqKGate_of_indexConv (fun _ _ h => h) etaIndexMot (.sort .zero)
    (indexFnTy eqEnvT n etaEqCtx) (etaIndexParamTy n) (etaIndexTy n)
    (eta_major_typed n) (etaIndexConv n)

/-- The binder refl canon is actually typed at the major's proposition. -/
theorem binder_canonical_typed (n : Nat) :
    Nonempty (HasTyT eqEnvT n binderEqCtx binderIndexCtor
      (binderIndexFamily indexBinderBeta)) :=
  (binder_guards n).2.2.2

/-- The eta refl canon is actually typed at the major's proposition. -/
theorem eta_canonical_typed (n : Nat) :
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexCtor (etaIndexFamily etaIndex)) :=
  (eta_guards n).2.2.2

/-- Common typing supplies proof irrelevance in the one-assumption control. -/
theorem binder_canonical_irrelevance (n : Nat) :
    Nonempty (ConvT eqEnvT n binderEqCtx (.bvar 0) binderIndexCtor
      (binderIndexFamily indexBinderBeta)) :=
  kCommonAt_irr (binder_guards n).2

/-- Common typing supplies proof irrelevance in the neutral-function control. -/
theorem eta_canonical_irrelevance (n : Nat) :
    Nonempty (ConvT eqEnvT n etaEqCtx (.bvar 0) etaIndexCtor
      (etaIndexFamily etaIndex)) :=
  kCommonAt_irr (eta_guards n).2

/-- Literal index agreement is too strong for the inhabited binder control. -/
theorem binder_syntactic_guard_fails :
    redexIdx binder_witness ≠
      resultIdxAt binder_witness (binder_witness.preMajor.take binder_witness.nparams)
        binder_witness.fields := by
  change [indexBinderBeta] ≠ [indexId]
  decide

/-- Literal index agreement is too strong for the inhabited eta control. -/
theorem eta_syntactic_guard_fails :
    redexIdx eta_witness ≠
      resultIdxAt eta_witness (eta_witness.preMajor.take eta_witness.nparams)
        eta_witness.fields := by
  change [etaIndex] ≠ [Expr.bvar 1]
  decide

/-- Full positive binder fixture, with no semantic interpretation premise. -/
theorem binder_inhabited (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧
    Nonempty (CtxWfT eqEnvT n binderEqCtx) ∧
    Nonempty (HasTyT eqEnvT n binderEqCtx binderIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n binderEqCtx binderIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KIndexConvAt eqEnvT n binderEqCtx binder_witness ∧
    KCommonAt eqEnvT n binderEqCtx binder_witness (.bvar 0) ∧
    KNativeHead eqEnvT n binderEqCtx binderIndexRedex (.sort .zero) :=
  ⟨⟨envWf⟩, ⟨binder_context_wf n⟩, ⟨binder_native_typed n⟩,
    ⟨binder_native_conversion n⟩, (binder_guards n).1, (binder_guards n).2,
    kNativeHead_binder n⟩

/-- Full positive eta fixture, with its actual native source and target. -/
theorem eta_inhabited (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧
    Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KIndexConvAt eqEnvT n etaEqCtx eta_witness ∧
    KCommonAt eqEnvT n etaEqCtx eta_witness (.bvar 0) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) :=
  ⟨⟨envWf⟩, ⟨eta_context_wf n⟩, ⟨eta_native_typed n⟩,
    ⟨eta_native_conversion n⟩, (eta_guards n).1, (eta_guards n).2,
    kNativeHead_eta n⟩

-- BEGIN RCIC_ROUTE_C_EQ_GUARD_ROOTS
#print axioms envWf
#print axioms binder_context_wf
#print axioms eta_context_wf
#print axioms binder_witness
#print axioms eta_witness
#print axioms binder_families
#print axioms eta_families
#print axioms binder_major_typed
#print axioms eta_major_typed
#print axioms binder_native_typed
#print axioms eta_native_typed
#print axioms binder_native_conversion
#print axioms eta_native_conversion
#print axioms binder_guards
#print axioms eta_guards
#print axioms binder_canonical_typed
#print axioms eta_canonical_typed
#print axioms binder_canonical_irrelevance
#print axioms eta_canonical_irrelevance
#print axioms binder_syntactic_guard_fails
#print axioms eta_syntactic_guard_fails
#print axioms binder_inhabited
#print axioms eta_inhabited
-- END RCIC_ROUTE_C_EQ_GUARD_ROOTS

end Rcic.Declarative.RouteCEqGuard
