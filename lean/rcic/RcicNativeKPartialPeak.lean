import rcic.RcicNativeCertifiedK
import rcic.RcicStarStripUnitPeak

set_option maxRecDepth 8192

/-!
# Eta-K positive control and one more partial recursor

This module consumes Fable's additive `CertifiedK`; it does not redefine
the relation or either generic K certificate. The old admitted peak now
has a certified eta-K joining leg. The new peak leaves the minor, as well
as the major, unapplied outside the eta binder. Its inner eta-K leg is
certified by the same constructed legacy-ι certificate.

All positive data are native and use the existing admitted `trueEnvU`.
No uniqueness, sorting-coherence, Pi-row, diamond, or confluence premise
is used here. Nonjoinability, if established, belongs to the separate
negative module. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeKPartialPeakAudit

open CoherentCanonicalAudit (nativeLeafIface)
open StarStripUnitPeakAudit

private abbrev one : Level := .succ .zero
private abbrev two : Level := .succ (.succ .zero)

/-- The exact raw repair from #7606 now has a native eta-K certificate,
constructed by the legacy-arm producer from its actual witness data. -/
def unitKStep : CStepK trueEnvU 0 (ProofLeaf trueEnvU 0)
    [] unitPartialRec unitContracted unitIndex :=
  ⟨unitRawKEta, .iotaStarKEta
    (convT_iotaStarKEta (envClosed_of_envWfT trueEnvUWfT) (w := wTrueRecU) rfl
      trueEnvUF_ty unitPartialRecTy unitBoundProofTy trueEnvUtt_ty trueEnvUF_ty
      (.of wTrueRecU)
      (unitBodyPrep.rightTyped (nativeLeafIface trueEnvU 0) unitBodyContextWf)
      (.sort _ .zero))⟩

/-- The old left endpoint reaches the old centre in one enlarged step. -/
def unitKRepair : CStarK trueEnvU 0 (ProofLeaf trueEnvU 0)
    [] unitPartialRec unitContracted unitIndex :=
  .tail unitKStep (.refl [] unitContracted unitIndex unitContractedTy)

/-- The certified step contains the exact published raw eta-K repair. -/
theorem unitKStep_raw : unitKStep.step = unitRawKEta := rfl

/-- The repair uses the original endpoints' decorations verbatim. -/
theorem unitKRepair_deco :
    decoOf (unitKStep.leftTyped (nativeLeafIface trueEnvU 0) .nil) =
      decoOf (unitEtaStep.rightTyped (nativeLeafIface trueEnvU 0) .nil) ∧
    decoOf (unitKStep.rightTyped (nativeLeafIface trueEnvU 0) .nil) =
      decoOf (unitLamStep.rightTyped (nativeLeafIface trueEnvU 0) .nil) :=
  ⟨rfl, rfl⟩

/-- Only the motive is supplied: the minor and major remain unapplied. -/
def minorPartialRec : Expr Nat := .app (.const 2 [two]) unitMotive

/-- Eta expansion over the still-missing minor. -/
def minorEtaSource : Expr Nat :=
  .lam (.sort one) (.app (lift 0 1 minorPartialRec) (.bvar 0))

/-- Eta-K computes the inner partial recursor to the constant function. -/
def minorContracted : Expr Nat := .lam (.sort one) (.lam unitDomain (.bvar 1))

/-- The unchanged type of the two outer branches. -/
def minorIndex : Expr Nat := .pi (.sort one) unitIndex

/-- The literal type of the recursor after applying its motive. -/
def minorPartialRawTy {Γ : LCtx} : HasTyT trueEnvU 0 Γ minorPartialRec
    (.pi (.app unitMotive (.const 1 []))
      (.pi unitDomain (.app unitMotive (.bvar 0)))) :=
  .app _ _ _ _ _
    (.const _ 2 [two] trueRecMemberU rfl rfl rfl) trueEnvUM_ty

/-- The two displayed motive beta equations give the convenient index. -/
def minorPartialTy {Γ : LCtx} : HasTyT trueEnvU 0 Γ minorPartialRec minorIndex :=
  .conv _ _ _ _ (.imax two (.imax .zero two)) minorPartialRawTy
    (.pi _ (.app unitMotive (.const 1 [])) (.sort one)
      (.pi unitDomain (.app unitMotive (.bvar 0))) unitIndex
      two (.imax .zero two) trueEnvU_betaK
      (.pi _ unitDomain unitDomain (.app unitMotive (.bvar 0)) (.sort one)
        .zero two (.refl _ unitDomain (.sort .zero) trueEnvUF_ty) unitCodomainBeta))

/-- The outer minor binder is an actual well-formed context. -/
def minorContextWf : CtxWfT trueEnvU 0 [.assumption (.sort one)] :=
  .assumption [] (.sort one) two .nil (.sort [] one)

/-- The inner proof binder is also an actual well-formed context. -/
def minorProofContextWf : CtxWfT trueEnvU 0
    [.assumption unitDomain, .assumption (.sort one)] :=
  .assumption _ unitDomain .zero minorContextWf trueEnvUF_ty

/-- The existing True witness with the bound minor in its minor slot. -/
def minorWitness : IotaWitness trueEnvU :=
  { wTrueRecU with
    preMajor := [unitMotive, .bvar 1]
    minor := .bvar 1
    hpre := rfl
    hminor := rfl }

/-- The partially applied function under the outer eta binder. -/
def minorBodyTy : HasTyT trueEnvU 0 [.assumption (.sort one)]
    (.app (lift 0 1 minorPartialRec) (.bvar 0)) unitIndex :=
  .app _ _ _ _ _ minorPartialTy (.bvar _ 0 (.sort one) rfl)

/-- The full call at the bound proof has the constant motive's result. -/
def minorMajorCallTy : HasTyT trueEnvU 0
    [.assumption unitDomain, .assumption (.sort one)]
    (recCall (.const minorWitness.recRef minorWitness.ls)
      minorWitness.preMajor (.bvar 0)) (.sort one) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (minorPartialTy (Γ := [.assumption unitDomain, .assumption (.sort one)]))
      (.bvar [.assumption unitDomain, .assumption (.sort one)] 1 (.sort one) rfl))
    (.bvar [.assumption unitDomain, .assumption (.sort one)] 0 unitDomain rfl)

/-- The ordinary iota redex uses the same bound minor and True.intro. -/
def minorIotaCallTy : HasTyT trueEnvU 0
    [.assumption unitDomain, .assumption (.sort one)]
    (iotaLhsOf minorWitness) (.sort one) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (minorPartialTy (Γ := [.assumption unitDomain, .assumption (.sort one)]))
      (.bvar [.assumption unitDomain, .assumption (.sort one)] 1 (.sort one) rfl)) trueEnvUtt_ty

/-- Eta-K on the body, with every gate and the native certificate built. -/
def minorBodyStep : CStepK trueEnvU 0 (ProofLeaf trueEnvU 0)
    [.assumption (.sort one)]
    (.app (lift 0 1 minorPartialRec) (.bvar 0))
    (.lam unitDomain (.bvar 1)) unitIndex :=
  cstepK_iotaStarKEta_ofU (envClosed_of_envWfT trueEnvUWfT) minorWitness
    (.app (lift 0 1 minorPartialRec) (.bvar 0)) unitDomain (.sort one) unitDomain
    .zero .zero True rfl trueEnvUF_ty minorBodyTy
    rfl (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ (.bvar _ 0 unitDomain rfl) trueEnvUtt_ty trueEnvUF_ty
    minorIotaCallTy minorMajorCallTy (.bvar _ 1 (.sort one) rfl)

/-- The computed pair of lambdas has the common outer index. -/
def minorContractedTy : HasTyT trueEnvU 0 [] minorContracted minorIndex :=
  .lam [] (.sort one) two (.lam unitDomain (.bvar 1)) unitIndex (.sort [] one)
    (.lam _ unitDomain .zero (.bvar 1) (.sort one) trueEnvUF_ty
      (.bvar _ 1 (.sort one) rfl))

/-- The lambda branch contains the genuinely enlarged eta-K child. -/
def minorLamStep : CStepK trueEnvU 0 (ProofLeaf trueEnvU 0)
    [] minorEtaSource minorContracted minorIndex :=
  let hA : HasTyT trueEnvU 0 [] (.sort one) (.sort two) := .sort [] one
  let hB : HasTyT trueEnvU 0 [.assumption (.sort one)] unitIndex
      (.sort (.imax .zero two)) :=
    .pi _ unitDomain .zero (.sort one) two trueEnvUF_ty (.sort _ one)
  ⟨.lam [] (.sort one) (.sort one)
      (.app (lift 0 1 minorPartialRec) (.bvar 0)) (.lam unitDomain (.bvar 1))
      unitIndex two (.imax .zero two) (.refl _ _ _ hA) hA hB
      minorBodyStep.step minorContractedTy,
    .lam (.lam [] (.sort one) (.sort one) _ _ unitIndex two
      (.refl _ _ _ hA) minorBodyStep.toConvT) minorBodyStep.cert⟩

/-- The eta branch retains the other branch's exact source typing. -/
def minorEtaStep : CStepK trueEnvU 0 (ProofLeaf trueEnvU 0)
    [] minorEtaSource minorPartialRec minorIndex :=
  ⟨.eta [] minorPartialRec minorPartialRec (.sort one) unitIndex
      (.refl [] minorPartialRec minorIndex minorPartialTy)
      (minorLamStep.leftTyped (nativeLeafIface trueEnvU 0) .nil),
    .eta (.eta [] minorPartialRec (.sort one) unitIndex minorPartialTy)
      (.refl (.refl [] minorPartialRec minorIndex minorPartialTy))⟩

/-- The two actual enlarged steps have equal source decorations. -/
theorem minorSourceDeco :
    decoOf (minorEtaStep.leftTyped (nativeLeafIface trueEnvU 0) .nil) =
      decoOf (minorLamStep.leftTyped (nativeLeafIface trueEnvU 0) .nil) := rfl

/-- Native conversion of the endpoints is constructed from this peak. -/
def minorConversion : ConvT trueEnvU 0 [] minorPartialRec minorContracted minorIndex :=
  .trans _ _ _ _ _ (.symm _ _ _ _ minorEtaStep.toConvT) minorLamStep.toConvT

#print axioms unitKStep
#print axioms unitKRepair
#print axioms unitKStep_raw
#print axioms unitKRepair_deco
#print axioms minorPartialRec
#print axioms minorEtaSource
#print axioms minorContracted
#print axioms minorIndex
#print axioms minorPartialRawTy
#print axioms minorPartialTy
#print axioms minorContextWf
#print axioms minorProofContextWf
#print axioms minorWitness
#print axioms minorBodyTy
#print axioms minorMajorCallTy
#print axioms minorIotaCallTy
#print axioms minorBodyStep
#print axioms minorContractedTy
#print axioms minorLamStep
#print axioms minorEtaStep
#print axioms minorSourceDeco
#print axioms minorConversion

end Rcic.Declarative.NativeValleys.NativeKPartialPeakAudit
