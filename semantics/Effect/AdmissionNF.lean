import Effect.MonitorLaws
import Lib.Exec9Core
import MSTNecessityExecModelMWE

namespace Effect.ABI
open MSTNecessityExecModelMWE

def monitorModel {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) : ExecModel where
  Raw := Monitor.RawInput core
  Class := Monitor.Class core
  Rep := Outcome core
  Residue := Effect.ABI.Residue
  Outcome := Outcome core
  q := Monitor.classify
  evalRaw := Monitor.run registry store context
  evalClass := Monitor.step registry store context
  admissible := Monitor.admit registry store context
  rho := Monitor.residue? registry store context
  sigma := Monitor.representative registry store context

theorem monitorQuotientFactorization {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) : quotientFactorization (monitorModel registry store context) :=
  Monitor.decision_factorization registry store context

theorem monitorAdmissibilitySound {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) : admissibilitySound (monitorModel registry store context) := by
  intro input rep selected
  change Monitor.representative registry store context input = some rep at selected
  change Monitor.admit registry store context input = true
  simp only [Monitor.admit, Monitor.representative, Monitor.residue?] at *
  cases decision : Monitor.Lambda registry store context input <;> simp_all

theorem monitorResidueTotality {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) : residueTotality (monitorModel registry store context) := by
  intro input _ refused clear
  change Monitor.admit registry store context input = false at refused
  change Monitor.residue? registry store context input = none at clear
  simp [Monitor.admit, clear] at refused

theorem monitorRepresentativePrecision {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) : representativePrecision (monitorModel registry store context) := by
  intro input _ admitted
  change Monitor.admit registry store context input = true at admitted
  change Monitor.representative registry store context input ≠ none
  simp only [Monitor.admit, Monitor.representative, Monitor.residue?] at *
  cases decision : Monitor.Lambda registry store context input <;> simp_all

theorem monitorAdmissionExact {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) (state : RuntimeState) (event : Event core) (out : Outcome core) :
    Admission registry store context (Effect.ABI.sigma state) event out ↔
      (monitorModel registry store context).evalRaw ⟨state, event⟩ = out :=
  Monitor.exact_outcome (input := Monitor.classify ⟨state, event⟩)

theorem monitorSealExact {core : Core} (registry : Registry) (store : ObjectStore)
    (context : Context core) (state : RuntimeState) (request : SealRequest core) :
    (monitorModel registry store context).evalRaw ⟨state, .seal request⟩ =
      (Monitor.sealReceipt registry store context (sigma state) request).val :=
  Monitor.complete (Monitor.sealReceipt registry store context (sigma state) request).property

namespace Exec9Admission
open Lib.Exec9

structure Input where
  digest : List Int
  state : List Int

structure NamespaceClass where
  digest : List Int
  bound : Option (List Int)

inductive NamespaceResidue where
  | invalidNamespaceDigest
  | changedNamespaceDigest

inductive Entry where
  | start (digest : List Int)
  | resume (digest : List Int)

def classify (input : Input) : NamespaceClass :=
  ⟨input.digest, if input.state.isEmpty then none else some (stNamespace input.state)⟩

def evaluate (input : NamespaceClass) : Except NamespaceResidue Entry :=
  if !validQ input.digest then .error .invalidNamespaceDigest
  else
    match input.bound with
    | none => .ok (.start input.digest)
    | some bound =>
      if bound != input.digest then .error .changedNamespaceDigest
      else .ok (.resume input.digest)

def exec9AdmissionModel : ExecModel where
  Raw := Input
  Class := NamespaceClass
  Rep := Entry
  Residue := NamespaceResidue
  Outcome := Except NamespaceResidue Entry
  q := classify
  evalRaw := evaluate ∘ classify
  evalClass := evaluate
  admissible input :=
    match evaluate input with
    | .ok _ => true
    | .error _ => false
  rho input :=
    match evaluate input with
    | .ok _ => none
    | .error cause => some cause
  sigma input :=
    match evaluate input with
    | .ok entry => some entry
    | .error _ => none

theorem exec9QuotientFactorization : quotientFactorization exec9AdmissionModel :=
  fun _ => rfl

theorem exec9AdmissibilitySound : admissibilitySound exec9AdmissionModel := by
  intro input entry selected
  simp only [exec9AdmissionModel] at *
  cases decision : evaluate input <;> simp_all

theorem exec9ResidueTotality : residueTotality exec9AdmissionModel := by
  intro input _ refused
  simp only [exec9AdmissionModel] at *
  cases decision : evaluate input <;> simp_all

theorem exec9RepresentativePrecision : representativePrecision exec9AdmissionModel := by
  intro input _ admitted
  simp only [exec9AdmissionModel] at *
  cases decision : evaluate input <;> simp_all

open Lib.Rsd.Ninep in
theorem exec9PlanAdmissionExact (plan : List Op) (digest write check state reply : List Int) :
    runPlan plan digest write check state reply =
      match exec9AdmissionModel.evalRaw ⟨digest, state⟩ with
      | .error _ => refuseQ
      | .ok (.start ns) => sendT (initState ns write check)
          (TMsg.version NOTAG DEFAULT_MSIZE W9P2000) PH_VER 0
      | .ok (.resume _) => stepR state plan reply := by
  cases valid : validQ digest <;> cases cold : state.isEmpty <;>
    cases bound : (stNamespace state != digest) <;>
    simp [runPlan, exec9AdmissionModel, classify, evaluate, valid, cold, bound]

end Exec9Admission
end Effect.ABI

set_option format.width 200
#print axioms Effect.ABI.monitorQuotientFactorization
#print axioms Effect.ABI.monitorAdmissibilitySound
#print axioms Effect.ABI.monitorResidueTotality
#print axioms Effect.ABI.monitorRepresentativePrecision
#print axioms Effect.ABI.monitorAdmissionExact
#print axioms Effect.ABI.monitorSealExact
#print axioms Effect.ABI.Exec9Admission.exec9QuotientFactorization
#print axioms Effect.ABI.Exec9Admission.exec9AdmissibilitySound
#print axioms Effect.ABI.Exec9Admission.exec9ResidueTotality
#print axioms Effect.ABI.Exec9Admission.exec9RepresentativePrecision
#print axioms Effect.ABI.Exec9Admission.exec9PlanAdmissionExact
