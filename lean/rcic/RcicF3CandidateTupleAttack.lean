import rcic.RcicF3CandidateBoundTuple
import rcic.RcicF3CandidateScopeAttack

/-!
# Actual AccR composition of admitted candidate-to-raw fields

The empty candidate is admissible and provably not closed. The actual raw
AccR frame is admissible, closed and inhabited at the empty proposition
parameter, so the candidate inclusion is proper. The actual field scan and
BoundG produce the certificate and instance bounds. The generic tuple
transport, including its typed reverse normalization, then produces the raw
field tuple at the full extra-motive universe vector [1]. This is the AccR
fixture, not an imported Acc-on-Nat.lt environment. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateTupleAttack
open Rcic.Declarative RawFamily PiIndex PlanPropEndAttack
open CandidateScopeAttack (accσ accK accμ)

abbrev X : Frame := RawFamilyCandidatePrefixAttack.emptyCandidate
noncomputable def R (P : Premises4) : Frame := frame P (installed P) fd

theorem raw_admissible (P : Premises4) : Admissible fd (R P) :=
  (RawFamilyPropAttack.acc_closed P (installed P)).1

theorem raw_closed (P : Premises4) : Closed P (installed P) fd (R P) :=
  (RawFamilyPropAttack.acc_closed P (installed P)).2

theorem frame_sub (P : Premises4) : FrameSub X (R P) := by
  intro vs i z hz
  exact (not_mem_pempty hz).elim

theorem proper_inclusion (P : Premises4) :
    pempty ∈ R P [] (key [parameter]) ∧ pempty ∉ X [] (key [parameter]) :=
  ⟨RawFamilyPropAttack.empty_parameter_inhabited P (installed P) [],
    fun h => not_mem_pempty h⟩

theorem family_all (P : Premises4) (vs : List Nat) :
    Equiv (installed P 0 vs) (ofFrame P (installed P) fd (R P) vs) := by
  have h := (PlanRole.rawTable_spec P AccEnv.accEnvWfT).1 0 accFamMember rfl vs
  rw [family_context] at h
  exact h

theorem scan :
    fieldShapesFuel PlanPropStepAttack.pNode.E0 8 0 0 1 0 1 [accField] =
      some [.recursive 1] := by
  rfl

theorem certificates :
    PiRawFieldViews.Views PlanPropStepAttack.pNode.E0 8 0 0 1 0 0
      [.recursive 1] [accField] ∧
    PropEval.FieldCertificates
      (fun _ A s => PiCleanViews.Clean PlanPropStepAttack.pNode.E0 8 0 0 1 0 A s)
      0 [.recursive 1] [accField] :=
  CandidateFieldAdmission.of_fields [accField] 0 [.recursive 1] scan

theorem instances : ∀ A ∈ [accField], InstOK accFamOnly accσ accK A := by
  exact CandidateBoundFields.original_fields_instOK accσ accK
    (E := emptyEnv) (E' := accEnv) (f := 0) (rr := 2)
    (fm := accFamMember) (rm := accRecMember) (ctors := [(1, accIntroMember)])
    .empty rfl (fun c hc => by cases List.mem_singleton.mp hc; rfl)
    rfl AccEnv.accMembersT (PlanPropStepAttack.boundG accK)
    PlanPropStepAttack.pNode rfl rfl [1] rfl
    (fun v hv => by
      have hv1 : v = 1 := List.mem_singleton.mp hv
      subst v
      exact Nat.le_refl 1)
    ⟨0, by change 0 < 1; decide⟩

theorem candidate_tuple (P : Premises4) :
    TelFits (mkM P (accμ P)) accσ [accField] (push [parameter] ρ0) [pempty] :=
  PropEvalAttack.original_field_fit P (accμ P)

/-- The produced tuple uses the generic admission-and-BoundG composition,
not a separate direct semantic proof of the already-normalized AccR field. -/
theorem raw_tuple (P : Premises4) :
    TelFits (mkM P (installed P)) accσ [accField] (push [parameter] ρ0) [pempty] := by
  have hA : AllSound P (installed P) accK emptyEnv := by
    intro r m hm
    nomatch hm
  have hI : ∀ r m, emptyEnv.members r = some m → m.mclass = .recursorM →
      IotaAt P (installed P) accK accEnv r := by
    intro r m hm
    nomatch hm
  exact CandidateBoundFields.field_tuple_raw P (installed P) accσ accK
    (E := emptyEnv) (E' := accEnv) (f := 0) (rr := 2)
    (fm := accFamMember) (rm := accRecMember) (ctors := [(1, accIntroMember)])
    .empty rfl (fun c hc => by cases List.mem_singleton.mp hc; rfl)
    rfl AccEnv.accMembersT (PlanPropStepAttack.boundG accK)
    PlanPropStepAttack.pNode hA hI rfl rfl X (R P)
    (RawFamilyCandidatePrefixAttack.admissible P) (raw_admissible P)
    (frame_sub P) (family_all P)
    (PropEvalTypedAttack.prefix_sound P accK)
    (RawFamilyCandidatePrefixAttack.prefix_sound P accK accσ 0)
    [1] rfl
    (fun v hv => by
      have hv1 : v = 1 := List.mem_singleton.mp hv
      subst v
      exact Nat.le_refl 1)
    ⟨0, by change 0 < 1; decide⟩ 8 [.recursive 1] scan
    [parameter] [pempty] (PropEvalAttack.parameters_fit P (installed P))
    (candidate_tuple P)

def Witness (P : Premises4) : Prop :=
  CandidateScopeAttack.AccWitness P ∧
  BoundG accK AccEnv.accEnvWfT ∧
  Admissible fd (R P) ∧ Closed P (installed P) fd (R P) ∧ FrameSub X (R P) ∧
  (pempty ∈ R P [] (key [parameter]) ∧ pempty ∉ X [] (key [parameter])) ∧
  fieldShapesFuel PlanPropStepAttack.pNode.E0 8 0 0 1 0 1 [accField] =
    some [.recursive 1] ∧
  PiRawFieldViews.Views PlanPropStepAttack.pNode.E0 8 0 0 1 0 0
    [.recursive 1] [accField] ∧
  PropEval.FieldCertificates
    (fun _ A s => PiCleanViews.Clean PlanPropStepAttack.pNode.E0 8 0 0 1 0 A s)
    0 [.recursive 1] [accField] ∧
  (∀ A ∈ [accField], InstOK accFamOnly accσ accK A) ∧
  TelFits (mkM P (accμ P)) accσ [accField] (push [parameter] ρ0) [pempty] ∧
  TelFits (mkM P (installed P)) accσ [accField] (push [parameter] ρ0) [pempty]

theorem component_witness (P : Premises4) : Witness P :=
  ⟨CandidateScopeAttack.acc_witness P, PlanPropStepAttack.boundG accK,
    raw_admissible P, raw_closed P, frame_sub P, proper_inclusion P,
    scan, certificates.1, certificates.2, instances, candidate_tuple P, raw_tuple P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.CandidateTupleAttack
