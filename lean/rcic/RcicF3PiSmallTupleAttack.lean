import rcic.RcicF3PiSmallTuple
import rcic.RcicF3RawFamilyRecAtAttack

/-!
# Dependent small tuple choices retain the exact height-omega value

The second ordinary domain is the type value chosen by the first field.
Both its proof-faced and data-faced alternatives are inhabited. The third
field contains the exact admitted PendA height-omega element, which remains
outside the old finite-stage family. Choice0 suffices for these stage-one
tuples; all three result expressions and all three values are preserved.

This is a semantic tuple-compiler witness. It does not assert that this
auxiliary constant table is an admitted environment, or that recursive
outputs can already be omitted from a universal constructor signature.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PiSmallTupleAttack

open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)
open RawFamilyRecAtAttack (base omega_mem)

noncomputable def proofType : PSet.{4} := tyv (tv True)
noncomputable def dataType : PSet.{4} := tyv (singleton (tyv pempty))
noncomputable def alternatives : PSet.{4} := pair proofType dataType

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  fun r _ => if r = 3 then tyv alternatives else tyv (singleton (fxZW P))

noncomputable def model (P : Premises4) : Interp.{4} := mkM P (table P)

def σ : Nat → Nat := fun _ => 1
def fields : List (Expr Nat) := [.const 3 [], .bvar 0, .const 7 []]
def result : List (Expr Nat) := [.bvar 2, .bvar 1, .bvar 0]

noncomputable def proofTuple (P : Premises4) : List PSet.{4} :=
  [proofType, pempty, fxZW P]
noncomputable def dataTuple (P : Premises4) : List PSet.{4} :=
  [dataType, tyv pempty, fxZW P]

theorem singleton_dich {x : PSet.{4}} (hx : ¬ Equiv x pempty) :
    Dich (singleton x) := by
  apply Or.inr
  intro h
  exact hx (mem_singleton.mp h).symm

theorem alternatives_dich : Dich alternatives := by
  apply Or.inr
  intro h
  rcases mem_pair.mp h with he | he
  · exact tyv_ne_pempty _ he.symm
  · exact tyv_ne_pempty _ he.symm

theorem omega_stage_one (P : Premises4) : fxZW P ∈ W4 1 :=
  (stage4 P 0).trans
    (RawWFrame.raw_admissible P (base P) [] (key [tyv fxS])).1 (omega_mem P)

theorem omega_not_empty (P : Premises4) : ¬ Equiv (fxZW P) pempty := by
  have h := (RawWFrame.raw_admissible P (base P) [] (key [tyv fxS])).2
  have h0 : evalTotal (σOf []) fd.resLevel ≠ 0 := by decide
  rw [if_neg h0] at h
  exact h _ (omega_mem P)

theorem proofType_stage_one (P : Premises4) : proofType ∈ W4 1 :=
  (stage4 P 0).tyv_mem ((stage4 P 0).prop_mem (fun _ h => (mem_tv.mp h).2))

theorem dataType_stage_one (P : Premises4) : dataType ∈ W4 1 :=
  (stage4 P 0).tyv_mem ((stage4 P 0).singleton_mem
    ((stage4 P 0).tyv_mem (stage4 P 0).empty))

theorem proof_fits (P : Premises4) :
    TelFits (model P) σ fields ρ0 (proofTuple P) := by
  change proofType ∈ Ed (model P) (tyv alternatives) ∧
    pempty ∈ Ed (model P) proofType ∧
    fxZW P ∈ Ed (model P) (tyv (singleton (fxZW P))) ∧ True
  exact ⟨mem_congr_right (ed_tyv (model P) alternatives_dich).symm
      (mem_pair.mpr (Or.inl Equiv.rfl)),
    mem_congr_right (ed_tyv (model P) (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩),
    mem_congr_right (ed_tyv (model P) (singleton_dich (omega_not_empty P))).symm
      (mem_singleton.mpr Equiv.rfl), True.intro⟩

theorem data_fits (P : Premises4) :
    TelFits (model P) σ fields ρ0 (dataTuple P) := by
  change dataType ∈ Ed (model P) (tyv alternatives) ∧
    tyv pempty ∈ Ed (model P) dataType ∧
    fxZW P ∈ Ed (model P) (tyv (singleton (fxZW P))) ∧ True
  exact ⟨mem_congr_right (ed_tyv (model P) alternatives_dich).symm
      (mem_pair.mpr (Or.inr Equiv.rfl)),
    mem_congr_right (ed_tyv (model P) (singleton_dich (tyv_ne_pempty _))).symm
      (mem_singleton.mpr Equiv.rfl),
    mem_congr_right (ed_tyv (model P) (singleton_dich (omega_not_empty P))).symm
      (mem_singleton.mpr Equiv.rfl), True.intro⟩

theorem proof_small (P : Premises4) :
    SmallAlong (model P) σ (W4 1) fields ρ0 (proofTuple P) := by
  change Ed (model P) (tyv alternatives) ∈ W4 1 ∧
    Ed (model P) proofType ∈ W4 1 ∧
    Ed (model P) (tyv (singleton (fxZW P))) ∈ W4 1 ∧ True
  exact ⟨mem_congr_left (ed_tyv (model P) alternatives_dich).symm
      ((stage4 P 0).pair (proofType_stage_one P) (dataType_stage_one P)),
    mem_congr_left (ed_tyv (model P) (dich_tv True)).symm
      ((stage4 P 0).prop_mem (fun _ h => (mem_tv.mp h).2)),
    mem_congr_left (ed_tyv (model P) (singleton_dich (omega_not_empty P))).symm
      ((stage4 P 0).singleton_mem (omega_stage_one P)), True.intro⟩

theorem data_small (P : Premises4) :
    SmallAlong (model P) σ (W4 1) fields ρ0 (dataTuple P) := by
  change Ed (model P) (tyv alternatives) ∈ W4 1 ∧
    Ed (model P) dataType ∈ W4 1 ∧
    Ed (model P) (tyv (singleton (fxZW P))) ∈ W4 1 ∧ True
  exact ⟨mem_congr_left (ed_tyv (model P) alternatives_dich).symm
      ((stage4 P 0).pair (proofType_stage_one P) (dataType_stage_one P)),
    mem_congr_left (ed_tyv (model P) (singleton_dich (tyv_ne_pempty _))).symm
      ((stage4 P 0).singleton_mem ((stage4 P 0).tyv_mem (stage4 P 0).empty)),
    mem_congr_left (ed_tyv (model P) (singleton_dich (omega_not_empty P))).symm
      ((stage4 P 0).singleton_mem (omega_stage_one P)), True.intro⟩

def Represented (P : Premises4) (xs : List PSet.{4}) : Prop :=
  ∃ s : PiSmallTuple.Space.{0,4} (model P) P.c0 σ fields ρ0,
    LEq xs (PiSmallTuple.values (model P) P.c0 σ fields ρ0 s) ∧
    TelFits (model P) σ fields ρ0
      (PiSmallTuple.values (model P) P.c0 σ fields ρ0 s) ∧
    LEq (result.map (den (model P) σ (push xs ρ0)))
      (result.map (den (model P) σ
        (push (PiSmallTuple.values (model P) P.c0 σ fields ρ0 s) ρ0)))

theorem proof_represented (P : Premises4) : Represented P (proofTuple P) :=
  PiSmallTuple.complete_with_result (model P) P.c0 σ fields result ρ0
    (proofTuple P) (proof_fits P) (proof_small P)

theorem data_represented (P : Premises4) : Represented P (dataTuple P) :=
  PiSmallTuple.complete_with_result (model P) P.c0 σ fields result ρ0
    (dataTuple P) (data_fits P) (data_small P)

def Witness (P : Premises4) : Prop :=
  Represented P (proofTuple P) ∧ Represented P (dataTuple P) ∧
  fxZW P ∈ frame P (base P) fd [] (key [tyv fxS]) ∧
  fxZW P ∉ El (fapps (famLim P (base P) fd []) [tyv fxS])

theorem component_witness (P : Premises4) : Witness P :=
  ⟨proof_represented P, data_represented P, omega_mem P,
    (RawFamilyRecAtAttack.inhabited P).2.2.1⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) := by
  intro h
  exact h (component_witness P) P

end Rcic.F3.PSet.PiSmallTupleAttack
