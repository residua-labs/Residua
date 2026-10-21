import rcic.RcicCoherentCanonical
import rcic.RcicCoherentConsumer
import rcic.RcicNativeValleyDecoRows

/-!
# The concrete eta/leaf peak has a coherent two-step/zero-step join

This module reuses the public `ProofLeaf`, the canonical `nativeLeafIface`,
the existing `etaLeafLamStep`/`etaLeafEtaStep` certificates, and the actual
`etaLeaf_valleyJoin` construction. The latter restores the proof argument
under the lambda with the symmetric leaf and then contracts eta:

  `d -> b -> f`, while the eta endpoint `f` takes zero steps.

The canonical leaf interface returns the supplied endpoint typings
verbatim. Consequently the valley's two internal interfaces, both peak
target/source interfaces, and the common target decoration all reduce to
the displayed existing typings. We package that construction as the
existing `DecoStarAudit.StarJoin`; no joining oracle is an input.

The lambda-left/eta-right orientation also supplies the asymmetric local
join consumed by `RcicCoherentConsumer`: its right reflexive star becomes
the existing certified reflexive step. The reversed star join is equally
coherent, but its exhibited right leg has two step nodes. No reverse
asymmetric row or global `AsymmetricDiamond` is constructed here. The
length calculation concerns this explicit valley, not every possible
valley for that peak.

No type uniqueness, Pi row, retyping, ordinary diamond, global confluence,
or `NotProof` premise is used. No new relation, certificate, star, valley,
or decoration representation is introduced. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentEtaAudit

open CoherentCanonicalAudit (nativeLeafIface)
open CoherentConsumerAudit (StarStepJoin AsymmetricStepJoin AtMostOne stepOf_short)

/-- Bundle the existing lambda-side certified peak step. -/
def lamPeakStep (E : ResolvedEnv) (n : Nat) :
    CStep E n (ProofLeaf E n) etaLeafCtx
      (.lam etaLeafP etaLeafBody) (.lam etaLeafP etaLeafBody')
      (.pi etaLeafP (.sort .zero)) :=
  ⟨etaLeafLamStep (nativeLeafIface E n), etaLeafLamCert (nativeLeafIface E n)⟩

/-- Bundle the existing eta-side certified peak step. -/
def etaPeakStep (E : ResolvedEnv) (n : Nat) :
    CStep E n (ProofLeaf E n) etaLeafCtx
      (.lam etaLeafP etaLeafBody) etaLeafF
      (.pi etaLeafP (.sort .zero)) :=
  ⟨etaLeafEtaStep, etaLeafEtaCert⟩

/-- This is an actual equal-decoration peak for the canonical native
interface; the equality is constructed, rather than supplied. -/
theorem peak_source_deco (E : ResolvedEnv) (n : Nat) :
    decoOf ((lamPeakStep E n).leftTyped (nativeLeafIface E n) etaLeafCtx_wf) =
      decoOf ((etaPeakStep E n).leftTyped (nativeLeafIface E n) etaLeafCtx_wf) := rfl

/-- Package the landed two-step/zero-step valley as the existing coherent
`StarJoin`, with all three endpoint decoration interfaces. -/
def starJoin (E : ResolvedEnv) (n : Nat) :
    StarStepJoin (nativeLeafIface E n) etaLeafCtx_wf
      (lamPeakStep E n) (etaPeakStep E n) where
  centre := (etaLeaf_valleyJoin (nativeLeafIface E n)).1
  left := (etaLeaf_valleyJoin (nativeLeafIface E n)).2.1
  right := (etaLeaf_valleyJoin (nativeLeafIface E n)).2.2
  leftCoherent := ⟨rfl, ⟨rfl, True.intro⟩⟩
  rightCoherent := True.intro
  leftSource := by
    simp only [CStar.ofStep, CStar.rightTyped, etaLeaf_valleyJoin, lamPeakStep] <;> rfl
  rightSource := by
    simp only [CStar.ofStep, CStar.rightTyped, etaLeaf_valleyJoin, etaPeakStep] <;> rfl
  target := by
    simp only [etaLeaf_valleyJoin, CStar.rightTyped]

/-- The actual lambda joining leg has two certified step nodes. -/
theorem starJoin_left_length (E : ResolvedEnv) (n : Nat) :
    CoherentConsumerAudit.length (starJoin E n).left = 2 := rfl

/-- The actual eta joining leg is reflexive. -/
theorem starJoin_right_length (E : ResolvedEnv) (n : Nat) :
    CoherentConsumerAudit.length (starJoin E n).right = 0 := rfl

/-- The exhibited eta leg meets the exact short-right consumer bound. -/
theorem starJoin_right_short (E : ResolvedEnv) (n : Nat) :
    AtMostOne (starJoin E n).right := True.intro

/-- An actual asymmetric lambda-left/eta-right row. The right certified
step is constructed from the valley's reflexive right star, preserving
both its endpoint decorations. The left leg is the landed two-step leg. -/
def asymmetricJoin (E : ResolvedEnv) (n : Nat) :
    AsymmetricStepJoin (nativeLeafIface E n) etaLeafCtx_wf
      (lamPeakStep E n) (etaPeakStep E n) := by
  let j := starJoin E n
  let r := stepOf_short (nativeLeafIface E n) etaLeafCtx_wf
    j.right (starJoin_right_short E n) j.rightCoherent
  exact
    { centre := j.centre
      left := j.left
      right := r.1
      leftCoherent := j.leftCoherent
      leftSource := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.leftSource
      rightSource := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using
          r.2.1.trans j.rightSource
      target := j.target.trans r.2.2.symm }

/-- The same actual valley supplies the reversed coherent star join.
This does not impose the short-right bound. -/
def starJoin_reverse (E : ResolvedEnv) (n : Nat) :
    StarStepJoin (nativeLeafIface E n) etaLeafCtx_wf
      (etaPeakStep E n) (lamPeakStep E n) :=
  let j := starJoin E n
  { centre := j.centre
    left := j.right
    right := j.left
    leftCoherent := j.rightCoherent
    rightCoherent := j.leftCoherent
    leftSource := j.rightSource
    rightSource := j.leftSource
    target := j.target.symm }

/-- Reversing this exhibited valley puts its two-step leg on the right. -/
theorem starJoin_reverse_right_length (E : ResolvedEnv) (n : Nat) :
    CoherentConsumerAudit.length (starJoin_reverse E n).right = 2 := rfl

/-- This particular reversed valley does not meet the consumer's right-leg
bound. No nonexistence claim about all alternative joins is made. -/
theorem starJoin_reverse_right_not_short (E : ResolvedEnv) (n : Nat) :
    ¬ AtMostOne (starJoin_reverse E n).right := fun h => h

#print axioms peak_source_deco
#print axioms starJoin
#print axioms asymmetricJoin
#print axioms starJoin_reverse
#print axioms starJoin_reverse_right_not_short

end Rcic.Declarative.NativeValleys.CoherentEtaAudit
