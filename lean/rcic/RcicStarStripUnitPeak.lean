import rcic.RcicStarStripSeparation
import rcic.RcicCensusWallsForall

set_option maxRecDepth 8192

/-!
# A closed native eta/leaf/iota peak in the admitted True environment

The existing `trueEnvU` has `True`, its nullary constructor, and its
universe-polymorphic recursor at references 0, 1, and 2. Its actual
`EnvWfT` and finite `InScope` witnesses are already published.

Set `M := fun _ : True => Type`, and let `f := True.rec.{2} M Prop`.
At the common index `True -> Type`, the eta expansion of `f` has two
actual canonical certified steps: eta gives `f`; replacing the bound
proof by `True.intro`, then ordinary iota under the lambda, gives
`fun _ : True => Prop`. The source-decoration equality is definitional.

The native conversion between these endpoints is also constructed. The
global star-strip interface is used only by the explicitly conditional
consumer `unitStarStripValley`; no global confluence is asserted here.

The full-relation control uses the existing `iotaStarKEta` arm and the
existing `NativeValley` carrier to join the two endpoints. That arm has
no `Certified` witness. No reduction rule or carrier is added, and no
type-uniqueness, Pi-row, or retyping premise is used by these positive
constructions. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StarStripUnitPeakAudit

open CoherentCanonicalAudit (nativeLeafIface)
open StarStripSeparationAudit

/-- The already admitted proposition `True`. -/
def unitDomain : Expr Nat := .const 0 []

/-- The constant motive returning `Type`. -/
def unitMotive : Expr Nat := .lam unitDomain (.sort (.succ .zero))

/-- The recursor with motive and minor supplied, and its major omitted. -/
def unitPartialRec : Expr Nat :=
  .app (.app (.const 2 [.succ (.succ .zero)]) unitMotive) (.sort .zero)

/-- The eta-expanded source of both certified steps. -/
def unitExpanded : Expr Nat :=
  .lam unitDomain (.app (lift 0 1 unitPartialRec) (.bvar 0))

/-- The lambda obtained by computing under the eta binder. -/
def unitContracted : Expr Nat := .lam unitDomain (.sort .zero)

/-- Both reducts have this unchanged, positive-sort index. -/
def unitIndex : Expr Nat := .pi unitDomain (.sort (.succ .zero))

/-- The partial recursor's literal dependent type before the motive beta
conversion. All data come from the existing True fixture. -/
def unitPartialRecRawTy {Γ : LCtx} :
    HasTyT trueEnvU 0 Γ unitPartialRec
      (.pi unitDomain (.app unitMotive (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.const _ 2 [.succ (.succ .zero)] trueRecMemberU rfl rfl rfl)
      trueEnvUM_ty)
    trueEnvUS0_ty

/-- The motive computes at the bound variable by native beta. -/
def unitCodomainBeta {Γ : LCtx} :
    ConvT trueEnvU 0 (.assumption unitDomain :: Γ)
      (.app unitMotive (.bvar 0)) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  .beta _ unitDomain (.sort (.succ .zero)) (.bvar 0)
    (.sort (.succ (.succ .zero))) .zero trueEnvUF_ty
    (.sort _ (.succ .zero)) (.bvar _ 0 unitDomain rfl)

/-- Convert the literal dependent codomain by its displayed native beta
equation. This is a fixed explicit conversion, with no type exchange. -/
def unitPartialRecTy {Γ : LCtx} : HasTyT trueEnvU 0 Γ unitPartialRec unitIndex :=
  .conv _ _ _ _ (.imax .zero (.succ (.succ .zero))) unitPartialRecRawTy
    (.pi _ unitDomain unitDomain (.app unitMotive (.bvar 0))
      (.sort (.succ .zero)) .zero (.succ (.succ .zero))
      (.refl _ unitDomain (.sort .zero) trueEnvUF_ty) unitCodomainBeta)

/-- The context of the eta body is an actual well-formed context. -/
def unitBodyContextWf : CtxWfT trueEnvU 0 [.assumption unitDomain] :=
  .assumption [] unitDomain .zero .nil trueEnvUF_ty

/-- The actual bound proof has the closed proposition's type. -/
def unitBoundProofTy : HasTyT trueEnvU 0 [.assumption unitDomain]
    (.bvar 0) unitDomain := .bvar _ 0 unitDomain rfl

/-- Preparation for ordinary iota: keep the function fixed and replace
the bound proof by `True.intro`, using the canonical proof leaf. -/
def unitBodyPrep : CStep trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0)
    [.assumption unitDomain]
    (.app (lift 0 1 unitPartialRec) (.bvar 0))
    (.app (lift 0 1 unitPartialRec) (.const 1 [])) (.sort (.succ .zero)) :=
  let Δ := [LocalDecl.assumption unitDomain]
  let f := lift 0 1 unitPartialRec
  let hf : HasTyT trueEnvU 0 Δ f unitIndex := unitPartialRecTy
  let leaf := CStep.irr (nativeLeafIface trueEnvU 0)
    (trueEnvUF_ty (n := 0) (Γ := Δ)) unitBoundProofTy trueEnvUtt_ty
  ⟨.app Δ f f (.bvar 0) (.const 1 []) unitDomain (.sort (.succ .zero))
      unitIndex (.succ (.succ .zero)) (.succ (.succ .zero))
      (.refl Δ f unitIndex hf) (.refl Δ unitIndex)
      (.sort _ (.succ .zero)) (.sort Δ (.succ .zero)) leaf.step trueEnvUL_tyS1,
    .app (.app Δ f f (.bvar 0) (.const 1 []) unitDomain (.sort (.succ .zero))
      (.refl Δ f unitIndex hf) leaf.toConvT)
      (.refl (.refl Δ f unitIndex hf)) leaf.cert⟩

/-- A native proof preparation followed by the already published iota
witness. The certificate contains no K or eta-K constructor. -/
def unitBodyStep : CStep trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0)
    [.assumption unitDomain]
    (.app (lift 0 1 unitPartialRec) (.bvar 0)) (.sort .zero) (.sort (.succ .zero)) :=
  iotaAfter_step (nativeLeafIface trueEnvU 0) unitBodyContextWf
    unitBodyPrep (.of wTrueRecU) (.sort _ .zero)

/-- The certified lambda branch, computing to `fun _ => Prop`. -/
def unitLamStep : CStep trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0)
    [] unitExpanded unitContracted unitIndex :=
  lamAt_bodyStep (nativeLeafIface trueEnvU 0) .nil trueEnvUF_ty
    (.sort _ (.succ .zero)) unitBodyStep

/-- The certified eta branch, with exactly the lambda branch's source
typing stored as its own source typing. -/
def unitEtaStep : CStep trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0)
    [] unitExpanded unitPartialRec unitIndex :=
  etaAt_bodyStep (nativeLeafIface trueEnvU 0) .nil trueEnvUF_ty
    (.sort _ (.succ .zero)) unitPartialRecTy unitBodyStep

/-- The two actual certified source decorations agree definitionally. -/
theorem unitSourceDeco :
    decoOf (unitEtaStep.leftTyped (nativeLeafIface trueEnvU 0) .nil) =
      decoOf (unitLamStep.leftTyped (nativeLeafIface trueEnvU 0) .nil) := rfl

/-- The native conversion of the two endpoints is real data: reverse
the eta certificate, then use the leaf/iota lambda certificate. -/
def unitConversion : ConvT trueEnvU 0 [] unitPartialRec unitContracted unitIndex :=
  .trans _ _ _ _ _ (.symm _ _ _ _ unitEtaStep.toConvT) unitLamStep.toConvT

/-- The exact native valley any inhabitant of the canonical star-strip
interface must supply on this closed admitted peak. -/
def unitStarStripValley
    (D : CoherentStarStripAudit.StarStrip (nativeLeafIface trueEnvU 0)) :
    CValley trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0)
      [] unitPartialRec unitContracted unitIndex :=
  starStripValley_of_bodyStep (nativeLeafIface trueEnvU 0) D .nil trueEnvUF_ty
    (.sort _ (.succ .zero)) unitPartialRecTy unitBodyStep

/-- The computed lambda has the exact common index. -/
def unitContractedTy : HasTyT trueEnvU 0 [] unitContracted unitIndex :=
  .lam [] unitDomain .zero (.sort .zero) (.sort (.succ .zero))
    trueEnvUF_ty (.sort _ .zero)

/-- Full-relation control: the existing eta-K arm directly joins this
partial recursor to the computed lambda, with all typed gates supplied. -/
def unitRawKEta : PiStep trueEnvU 0 [] unitPartialRec unitContracted unitIndex :=
  .iotaStarKEta [] wTrueRecU unitPartialRec unitDomain (.sort (.succ .zero))
    unitDomain (.sort .zero) .zero .zero True
    rfl trueEnvUF_ty unitPartialRecTy
    rfl (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ unitBoundProofTy trueEnvUtt_ty trueEnvUF_ty (.ofU wTrueRecU)
    (unitBodyPrep.rightTyped (nativeLeafIface trueEnvU 0) unitBodyContextWf)
    (unitBodyPrep.leftTyped (nativeLeafIface trueEnvU 0) unitBodyContextWf)
    (.sort _ .zero)

/-- The already published unrestricted native-valley carrier is
inhabited for this exact conversion's endpoints, with one/zero steps. -/
def unitRawValley : NativeValley trueEnvU 0 [] unitPartialRec unitContracted unitIndex where
  centre := unitContracted
  left := .tail unitRawKEta (.refl [] unitContracted unitIndex unitContractedTy)
  right := .refl [] unitContracted unitIndex unitContractedTy

/-- The existing certified fragment excludes the full-relation repair. -/
theorem unitRawKEta_not_certified : ¬ Nonempty (Certified unitRawKEta) := by
  rintro ⟨h⟩
  exact h.noKEta

#print axioms unitDomain
#print axioms unitMotive
#print axioms unitPartialRec
#print axioms unitExpanded
#print axioms unitContracted
#print axioms unitIndex
#print axioms unitPartialRecRawTy
#print axioms unitCodomainBeta
#print axioms unitPartialRecTy
#print axioms unitBodyContextWf
#print axioms unitBoundProofTy
#print axioms unitBodyPrep
#print axioms unitBodyStep
#print axioms unitLamStep
#print axioms unitEtaStep
#print axioms unitSourceDeco
#print axioms unitConversion
#print axioms unitStarStripValley
#print axioms unitContractedTy
#print axioms unitRawKEta
#print axioms unitRawValley
#print axioms unitRawKEta_not_certified

end Rcic.Declarative.NativeValleys.StarStripUnitPeakAudit
