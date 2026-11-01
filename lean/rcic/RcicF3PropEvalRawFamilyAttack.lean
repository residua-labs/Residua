import rcic.RcicF3PropEvalRawFamily
import rcic.RcicF3PropEvalCandidateLevelsAttack

/-!
# Produced raw-family packet inputs at the admitted AccR fixture

The family equation comes from the actual canonical raw table at every
universe vector. The family abstraction and complete-application proof face
are produced at the recursor's valuation with its extra motive slot. The
application at the empty proposition parameter is inhabited, so the proof
face witness is non-vacuous. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalRawFamilyAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)

theorem installed_family_all (P : Premises4) (vs : List Nat) :
    Equiv (installed P 0 vs) (role P (installed P) fd vs) := by
  have h := (PlanRole.rawTable_spec P AccEnv.accEnvWfT).1 0 accFamMember rfl vs
  rw [family_context] at h
  exact h

def Witness (P : Premises4) : Prop :=
  (ctx P).σ 0 = 1 ∧
  ∃ endVal : (Nat → PSet.{4}) → PSet.{4},
    EnvResp endVal ∧
    Equiv (installed P 0 [])
      (piLam (ctx P).M (ctx P).σ endVal ρ0
        (policyPi (fd.params ++ fd.indices) (.sort fd.resLevel))) ∧
    (∀ ys : List PSet.{4}, ys.length = 1 → ∀ z,
      z ∈ Ed (ctx P).M (fapps (installed P 0 []) ys) → Equiv z pempty) ∧
    pempty ∈ Ed (ctx P).M (fapps (installed P 0 []) [parameter])

theorem component_witness (P : Premises4) : Witness P := by
  obtain ⟨endVal, hEnd, hFamily, hProp⟩ :=
    PropEvalCandidate.raw_family_inputs P (installed P) (ctx P) rfl
      PropEvalCandidateLevelsAttack.family_bounded (installed_family_all P)
      (RawFamilyPropAttack.acc_closed P (installed P)).1 rfl
  exact ⟨rfl, endVal, hEnd, hFamily, hProp,
    major_mem P (installed P) (installed_family P)⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalRawFamilyAttack
