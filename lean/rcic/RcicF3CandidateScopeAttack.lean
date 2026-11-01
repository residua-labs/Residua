import rcic.RcicF3CandidateBoundFields
import rcic.RcicF3PiRawIHAttack
import rcic.RcicF3RawFamilyCandidatePrefixAttack

/-!
# Hidden reader extensions and actual AccR normalization

Fresh bodyless extensions preserve the complete depth-three hidden reader
at relabelled families. The delta environments are reader fixtures only;
their stored aliases are not asserted to be typed environments. A nonfresh
bodyless overwrite is separately rejected, so freshness/preservation has
observable content. The actual admitted AccR instance below composes the
typed normalization bridge with a sound but nonclosed candidate prefix.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateScopeAttack
open Rcic.Declarative PiIndex CandidateScope
open PiRawIHAttack (field beta delta zeta ds args env)

def bodyless : CheckedMember := ⟨.constructorM, 0, .sort .zero, none⟩
noncomputable def extended (f : Nat) : ResolvedEnv := extendEnv (env f) (f + 3) bodyless
noncomputable def shadowed (f : Nat) : ResolvedEnv := extendEnv (env f) (f + 2) bodyless

/-- A genuinely fresh bodyless extension preserves every reader lookup. -/
theorem bodies_equal (f : Nat) :
    ∀ r ls, transparentBody (extended f) r ls = transparentBody (env f) r ls := by
  have hfresh : (env f).members (f + 3) = none := by
    exact members_extend_ne emptyEnv (f + 2) (PiRawIHAttack.aliasMember f)
      (f + 3) (by omega)
  apply transparentBody_eq_of_bodyless_extension
    (fun r m hm => members_extend_preserved hfresh r m hm)
  intro r m hm hn
  by_cases hr : r = f + 3
  · subst r
    change (extendEnv (env f) (f + 3) bodyless).members (f + 3) = some m at hm
    rw [members_extend_eq] at hm
    cases Option.some.inj hm
    rfl
  · change (extendEnv (env f) (f + 3) bodyless).members r = some m at hm
    rw [members_extend_ne (env f) (f + 3) bodyless r hr] at hm
    rw [hn] at hm
    cases hm

/-- The global reader theorem preserves beta/delta/zeta hidden normalized
domains and the complete terminal argument list at depth three. -/
theorem hidden_reads : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, beta f, delta f, zeta f],
      piTelescopeFuel (extended f) 32 A =
        some (ds f, foldApps (.const f []) args) := by
  have hbase : ∀ f ∈ [1, 2, 987],
      ∀ A ∈ [field f, beta f, delta f, zeta f],
        piTelescopeFuel (env f) 32 A =
          some (ds f, foldApps (.const f []) args) := by decide
  intro f hf A hA
  exact (piTelescopeFuel_of_transparentBody_eq (bodies_equal f) 32 A).trans
    (hbase f hf A hA)

/-- The actual extended reader's admission scans retain all domains and
the terminal dependent index, not merely the outer family head. -/
theorem hidden_scans : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, beta f, delta f, zeta f],
      fieldAnalyze (extended f) 32 f 0 0 1 0 A = .permitted (.recursive 3) args ∧
      domainsContainFuel (extended f) f 31 (ds f) = some false ∧
      indicesCleanFuel (extended f) f 31 args = some false := by
  decide

/-- Removing freshness changes delta lookup and the normalized telescope. -/
theorem nonfresh_rejected : ∀ f ∈ [1, 2, 987],
    piTelescopeFuel (shadowed f) 32 (delta f) ≠
      piTelescopeFuel (env f) 32 (delta f) := by
  decide

def ReaderWitness : Prop :=
  (∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, beta f, delta f, zeta f],
      piTelescopeFuel (extended f) 32 A =
        some (ds f, foldApps (.const f []) args) ∧
      fieldAnalyze (extended f) 32 f 0 0 1 0 A = .permitted (.recursive 3) args ∧
      domainsContainFuel (extended f) f 31 (ds f) = some false ∧
      indicesCleanFuel (extended f) f 31 args = some false) ∧
  (∀ f ∈ [1, 2, 987],
    piTelescopeFuel (shadowed f) 32 (delta f) ≠
      piTelescopeFuel (env f) 32 (delta f))

theorem reader_witness : ReaderWitness :=
  ⟨fun f hf A hA => ⟨hidden_reads f hf A hA, hidden_scans f hf A hA⟩,
    nonfresh_rejected⟩

theorem reader_nonrefutable (P : Premises4) :
    ¬ (ReaderWitness → (Premises4 → False)) :=
  fun h => h reader_witness P

open RawFamily PlanPropEndAttack

/-- The family has arity zero, while the full recursor vector retains the
nonzero motive slot. -/
def accσ : Nat → Nat := σOf [1]
def accK : Nat → Nat := fun _ => 1

noncomputable def accμ (P : Premises4) : Nat → List Nat → PSet.{4} :=
  table P (installed P) fd RawFamilyCandidatePrefixAttack.emptyCandidate

def accρ : Nat → PSet.{4} := push [parameter] ρ0

theorem acc_read :
    piTelescopeFuel PlanPropStepAttack.pNode.E0 8 accField =
      some ([.bvar 0], accApp (.bvar 1)) := by
  rfl

theorem acc_parameters_fit (P : Premises4) :
    TelFits (mkM P (accμ P)) accσ [.sort .zero] ρ0 [parameter] := by
  exact ⟨mem_congr_right (ed_tyv (mkM P (accμ P)) (U4_dich 0)).symm
    (parameter_mem P), True.intro⟩

/-- The same original AccR field is inhabited over the admissible empty
candidate; its Pi domain at the selected parameter is empty. -/
theorem acc_original_mem (P : Premises4) :
    pempty ∈ Ed (mkM P (accμ P)) (den (mkM P (accμ P)) accσ accρ accField) := by
  exact (PropEvalAttack.original_field_fit P (accμ P)).1

/-- This instance calls the actual BoundG producer, using its original
ordinary context and the sound nonclosed candidate family prefix. -/
theorem acc_normalized (P : Premises4) :
    Equiv
      (den (mkM P (accμ P)) accσ accρ (policyPi [.bvar 0] (accApp (.bvar 1))))
      (den (mkM P (accμ P)) accσ accρ accField) := by
  have hA : AllSound P (accμ P) accK emptyEnv := by
    intro r m hm
    nomatch hm
  have hI : ∀ r m, emptyEnv.members r = some m → m.mclass = .recursorM →
      IotaAt P (accμ P) accK accEnv r := by
    intro r m hm
    nomatch hm
  exact original_field_normalized P (accμ P) accσ accK
    (E := emptyEnv) (E' := accEnv) (f := 0) (rr := 2)
    (fm := accFamMember) (rm := accRecMember) (ctors := [(1, accIntroMember)])
    (.empty : EnvWfT emptyEnv) rfl
    (by
      intro c hc
      rcases List.mem_singleton.mp hc with rfl
      rfl)
    rfl AccEnv.accMembersT (PlanPropStepAttack.boundG accK)
    PlanPropStepAttack.pNode hA hI rfl rfl
    (RawFamilyCandidatePrefixAttack.prefix_sound P accK accσ 0)
    [1] rfl
    (by
      intro v hv
      have hv1 : v = 1 := List.mem_singleton.mp hv
      subst v
      exact Nat.le_refl 1)
    ⟨0, by change 0 < 1; decide⟩ ⟨0, by change 0 < 1; decide⟩
    [parameter] [] (acc_parameters_fit P) True.intro acc_read

theorem acc_normalized_mem (P : Premises4) :
    pempty ∈ Ed (mkM P (accμ P))
      (den (mkM P (accμ P)) accσ accρ (policyPi [.bvar 0] (accApp (.bvar 1)))) :=
  mem_congr_right (ed_congr (mkM P (accμ P)) (acc_normalized P)).symm
    (acc_original_mem P)

/-- Literal composition of the actual admitted-node normalization instance,
its member transport, and the negative candidate-closure control. -/
def AccWitness (P : Premises4) : Prop :=
  Admissible fd RawFamilyCandidatePrefixAttack.emptyCandidate ∧
  ¬ Closed P (installed P) fd RawFamilyCandidatePrefixAttack.emptyCandidate ∧
  EnvSound (mkM P (accμ P)) accσ accK accFamOnly 0 ∧
  accσ 0 = 1 ∧ PlanPropStepAttack.pNode.a.family.member.arity = 0 ∧
  piTelescopeFuel PlanPropStepAttack.pNode.E0 8 accField =
    some ([.bvar 0], accApp (.bvar 1)) ∧
  Equiv
    (den (mkM P (accμ P)) accσ accρ (policyPi [.bvar 0] (accApp (.bvar 1))))
    (den (mkM P (accμ P)) accσ accρ accField) ∧
  pempty ∈ Ed (mkM P (accμ P))
    (den (mkM P (accμ P)) accσ accρ (policyPi [.bvar 0] (accApp (.bvar 1))))

theorem acc_witness (P : Premises4) : AccWitness P :=
  ⟨RawFamilyCandidatePrefixAttack.admissible P,
    RawFamilyCandidatePrefixAttack.not_closed P,
    RawFamilyCandidatePrefixAttack.prefix_sound P accK accσ 0,
    rfl, rfl, acc_read, acc_normalized P, acc_normalized_mem P⟩

theorem acc_nonrefutable (P : Premises4) :
    ¬ (AccWitness P → (Premises4 → False)) :=
  fun h => h (acc_witness P) P

end Rcic.F3.PSet.CandidateScopeAttack
