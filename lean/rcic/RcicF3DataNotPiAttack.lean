import rcic.RcicF3DataNotPi
import rcic.RcicF3NormFreshHeadAttack

/-!
# Arbitrary-Pi head separation in the admitted W family prefix

The existing W component supplies the actual enlarged sound family prefix,
the full original local context, and its height-omega inhabitant. This
component adds the literal non-Pi spike and excludes every bounded Pi typing
or nonempty application of the auxiliary DATA local, with no family-freeness
restriction on the attempted Pi type. All former components are retained.

The local remains the explicitly auxiliary W-value declaration, not the
stored higher-order constructor field. Its valuation keeps the extra motive
slot 1. No all-universe domain mask or universal frame producer is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.DataNotPiAttack
open Rcic.Declarative RawFamily PiIndex NormFreshHeadAttack
open PendAWBridge (fd)

noncomputable abbrev spike (P : Premises4) : PSet.{4} :=
  RawFamilyEnlarge.spike (C P [] (key [parameter]))

theorem spike_mem (P : Premises4) : spike P ∈ D P [] (key [parameter]) := by
  change spike P ∈ RawFamilyEnlarge.enlarge fd (C P) [] (key [parameter])
  rw [RawFamilyEnlarge.enlarge, if_neg (by change (1 : Nat) ≠ 0; decide)]
  exact mem_insert.mpr (Or.inl Equiv.rfl)

/-- The actual enlarged W fibre contains a value that cannot be any
semantic function, including an erased proof function or empty graph. -/
theorem spike_not_pi (P : Premises4)
    (A : PSet.{4}) (B : PSet.{4} → PSet.{4})
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) :
    spike P ∉ Ed (model P (D P)) (piVal (model P (D P)) A B) :=
  DataNotPi.dataVal_not_piVal (model P (D P)) 0 [C P [] (key [parameter])] A B hB

/-- Both the attempted domain and codomain may mention the W family. -/
theorem no_pi_local (P : Premises4) (K : Nat → Nat) (A B : Expr Nat)
    (d : HasTyT PendAW.eFam 0 Γ (.bvar 0) (.pi A B))
    (hd : LOKt σ 4 K d) : False := by
  apply DataNotPi.no_variable_pi P (base P) fd (C P) (admissible_C P)
    0 σ K (prefix_sound P (D P) (admissible_D P) σ K 0) (ρ P)
    (local_fits P (D P) (admissible_D P) (omega_D P))
    [.bvar 1] A B (by intro e he; cases List.mem_singleton.mp he; rfl)
    (by change 1 ≠ 0; decide) ?_ 0 rfl d hd
  exact PendAWBridge.argsFit P (base P) pempty

/-- Nonempty attempted application spines retain all arguments and the
actual bound; no unbounded conversion or normalized typing is postulated. -/
theorem no_local_application (P : Premises4) (K : Nat → Nat)
    (a : Expr Nat) (as : List (Expr Nat)) (T : Expr Nat)
    (d : HasTyT PendAW.eFam 0 Γ (foldApps (.bvar 0) (a :: as)) T)
    (hd : LOKt σ 4 K d) : False := by
  apply DataNotPi.no_variable_application P (base P) fd (C P) (admissible_C P)
    0 σ K (prefix_sound P (D P) (admissible_D P) σ K 0) (ρ P)
    (local_fits P (D P) (admissible_D P) (omega_D P))
    [.bvar 1] (by intro e he; cases List.mem_singleton.mp he; rfl)
    (by change 1 ≠ 0; decide) ?_ 0 rfl a as T d hd
  exact PendAWBridge.argsFit P (base P) pempty

def Witness (P : Premises4) : Prop :=
  NormFreshHeadAttack.Witness P ∧
  spike P ∈ D P [] (key [parameter]) ∧
  spike P ∉ C P [] (key [parameter]) ∧
  (∀ (A : PSet.{4}) (B : PSet.{4} → PSet.{4}),
    (∀ a a', Equiv a a' → Equiv (B a) (B a')) →
    spike P ∉ Ed (model P (D P)) (piVal (model P (D P)) A B)) ∧
  (∀ K A B, ∀ d : HasTyT PendAW.eFam 0 Γ (.bvar 0) (.pi A B),
    LOKt σ 4 K d → False) ∧
  (∀ K a as T,
    ∀ d : HasTyT PendAW.eFam 0 Γ (foldApps (.bvar 0) (a :: as)) T,
    LOKt σ 4 K d → False)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormFreshHeadAttack.component_witness P, spike_mem P,
    RawFamilyEnlarge.spike_fresh _, spike_not_pi P, no_pi_local P,
    no_local_application P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.DataNotPiAttack
