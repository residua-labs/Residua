import rcic.ScmSrcGroupsAdm
import rcic.RcicAdmit

/-! Acceptance targets for the K3c unlock chain, as statements (propositions, and one `Type` for the proof-relevant `EnvWf`; nothing is proved here).

Base: `devin/k3c-groups` @ `cefd14e16e`. The chain is accepted when each target below is inhabited whose axioms are within `{propext, Quot.sound}`. The proofs must use nothing from `RcicUntypedConvCollapse`. A target is not met by a witness being absent: `funRecWitnesses` and `groupWitnesses` exist so that `valueAtBool` / `cctBool` cannot be met vacuously at constructors that have no ι witness. Real objects only: the table `srcMembersG`, its prefixes `envPre`, `srcEnvG`, and the inputs packaged in `VaPairEntry` / `FunRecEntry`. -/
namespace Rcic.Scm.SrcG.Targets
open Rcic.Declarative Rcic.Scm.SrcG

/-- Slot 140 (`vaPair`) passes every conjunct of the normal admission Bool at the real recursor. -/
def vaPairBool : Prop :=
  recursorGroupAdmittedAt (envPre 143) 143 recValueAt 133 [] 0 0 9 2 6 = true

/-- ValueAt's recursor passes the normal admission Bool at all nine constructors. -/
def valueAtBool : Prop := recursorGroupAdmitted (envPre 143) 143 recValueAt = true

/-- CCT's recursor passes the normal admission Bool at all eight constructors. -/
def cctBool : Prop := recursorGroupAdmitted (envPre 105) 105 recCCT = true

/-- Main's ι has a witness at each of the four function-recursive constructors. -/
def funRecWitnesses : Prop :=
  ∀ r ∈ [103, 104, 139, 142], Nonempty {w : IotaWitness srcEnvG // w.ctorRef = r}

/-- Every constructor of the two groups has a witness, so admission there is never vacuous. -/
def groupWitnesses : Prop :=
  ∀ r ∈ (List.range 8).map (97 + ·) ++ (List.range 9).map (134 + ·),
    Nonempty {w : IotaWitness srcEnvG // w.ctorRef = r}

/-- Criterion (i) of #6029: the environment chain with no hypothesis. -/
def envWfUnconditional : Type := (n : Nat) → EnvWf srcEnvG (n + 1)

end Rcic.Scm.SrcG.Targets
