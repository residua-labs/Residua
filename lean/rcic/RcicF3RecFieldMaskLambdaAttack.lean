import rcic.RcicF3RecFieldMaskLambda
import rcic.RcicF3RecFieldOriginCasesAttack

/-!
# A nonempty actual W lambda and its erased mask

The original assignment contains the actual height-omega W branch. The
mask replaces only that recursive local with pempty. An actual typed
lambda over the inhabited W parameter returns the unchanged branch;
the generic lambda case raises its Origin from depth one to depth two.
The original lambda is nonempty, whereas its masked interpretation is
empty. Both actual original family contexts fit at the supplied ord1
argument. No fit is asserted for the masked assignment.

The body relation is produced from the actual cached lookup Origin after
one binder shift; it is not a new callback in the witness. The complete
family key, hidden-type conversion and dependent-depth-three provenance
from the preceding witnesses are retained. This is the lambda induction
case, not the complete typed masking theorem. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMaskLambdaAttack
open Rcic.Declarative RawFamily PiIndex RecFieldOrigin RecFieldMask
open NormFreshHeadAttack (base C D model parameter σ)
open RecFieldOriginAttack (Γ ρ field)
open PendAWBridge (fd)

def marks : Marks := fun k => if k = 3 then some 1 else none
noncomputable def masked (P : Premises4) : Nat → PSet.{4} :=
  fun k => if k = 3 then pempty else ρ P k
def annotation : Expr Nat := .bvar 4
def bodyType : Expr Nat := .pi (.bvar 5) (.app (.const 4 []) (.bvar 6))
def term : Expr Nat := .lam annotation (.bvar 4)
def termType : Expr Nat := .pi annotation bodyType

noncomputable def body_typed : HasTyT PendAW.eFam 0
    (.assumption annotation :: Γ) (.bvar 4) bodyType :=
  .bvar _ 4 bodyType rfl

noncomputable def term_typed : HasTyT PendAW.eFam 0 Γ term termType :=
  .lam Γ annotation (.succ .zero) (.bvar 4) bodyType
    (.bvar Γ 4 (.sort (.succ .zero)) rfl) body_typed

theorem term_bound (τ K : Nat → Nat) : LOKt τ 4 K term_typed :=
  ⟨True.intro, True.intro⟩

theorem reader : piTelescopeFuel PendAW.eFam 16 termType =
    some ([.bvar 4, .bvar 5], foldApps (.const 4 (canonL 0)) [.bvar 6]) := rfl

theorem original_contexts (P : Premises4) (a : PSet.{4})
    (ha : a ∈ Ed (model P (C P)) parameter) :
    Fits (model P (C P)) σ (.assumption annotation :: Γ) (vcons a (ρ P)) ∧
    Fits (model P (D P)) σ (.assumption annotation :: Γ) (vcons a (ρ P)) :=
  ⟨⟨(RecFieldOriginAttack.contexts_fit P).1, ha⟩,
    ⟨(RecFieldOriginAttack.contexts_fit P).2, ha⟩⟩

/-- One actual lookup Origin supplies the same body case at every reached
ordinary argument. Both decoded expected types retain the shifted key. -/
theorem body_holds (P : Premises4) (K : Nat → Nat) (a : PSet.{4}) :
    Holds P (base P) fd (C P) σ (ordinary marks)
      (vcons a (ρ P)) (vcons a (masked P)) (.bvar 4) bodyType := by
  change Equiv pempty pempty ∧ Origin (mkM P (base P)) fd (C P) 1
    (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) field))
    (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) field))
    (RawFamilyIHBuilderAttack.x P)
  exact ⟨Equiv.rfl, RecFieldOriginAttack.lookup_origin P K⟩

/-- This is the generic lambda case with every body premise produced by
the previous actual lookup theorem; no semantic hypothesis is supplied. -/
theorem composed (P : Premises4) (K : Nat → Nat) :
    Holds P (base P) fd (C P) σ marks (ρ P) (masked P) term termType := by
  exact lambda_case P (base P) fd (C P) σ marks (ρ P) (masked P)
    annotation (.bvar 4) bodyType rfl Equiv.rfl (fun a _ => body_holds P K a)

theorem lambda_origin (P : Premises4) (K : Nat → Nat) :
    Origin (mkM P (base P)) fd (C P) 2
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) termType))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) termType))
      (den (model P (C P)) σ (ρ P) term) :=
  (composed P K).2

theorem masked_empty (P : Premises4) (K : Nat → Nat) :
    Equiv (den (model P (C P)) σ (masked P) term) pempty :=
  (composed P K).1

/-- The same lambda really returns the nonempty original W field at ord1;
the source side of the masking relation is not vacuously empty. -/
theorem original_nonempty (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (den (model P (C P)) σ (ρ P) term) pempty := by
  intro he
  have hbeta := beta_val (model P (C P))
    (den_resp (model P (C P)) σ (ρ P) (.bvar 4))
    (RecFieldOriginAttack.argument_mem P (C P))
  change Equiv (fapp (den (model P (C P)) σ (ρ P) term) (ord 1))
    (RawFamilyIHBuilderAttack.x P) at hbeta
  exact RecFieldOriginCasesAttack.field_nonempty P K
    (hbeta.symm.trans ((fapp_congr he Equiv.rfl).trans (fapp_pempty (ord 1))))

def Witness (P : Premises4) : Prop :=
  RecFieldOriginCasesAttack.Witness P ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ term termType) ∧
  piTelescopeFuel PendAW.eFam 16 termType =
    some ([.bvar 4, .bvar 5], foldApps (.const 4 (canonL 0)) [.bvar 6]) ∧
  ord 1 ∈ Ed (model P (C P)) parameter ∧
  Fits (model P (C P)) σ (.assumption annotation :: Γ) (vcons (ord 1) (ρ P)) ∧
  Fits (model P (D P)) σ (.assumption annotation :: Γ) (vcons (ord 1) (ρ P)) ∧
  (∀ K, LOKt σ 4 K term_typed ∧
    Holds P (base P) fd (C P) σ marks (ρ P) (masked P) term termType ∧
    Origin (mkM P (base P)) fd (C P) 2
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) termType))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) termType))
      (den (model P (C P)) σ (ρ P) term) ∧
    Equiv (den (model P (C P)) σ (masked P) term) pempty ∧
    ¬ Equiv (den (model P (C P)) σ (ρ P) term) pempty)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldOriginCasesAttack.component_witness P, ⟨term_typed⟩, reader,
    RecFieldOriginAttack.argument_mem P (C P),
    (original_contexts P (ord 1) (RecFieldOriginAttack.argument_mem P (C P))).1,
    (original_contexts P (ord 1) (RecFieldOriginAttack.argument_mem P (C P))).2,
    fun K => ⟨term_bound σ K, composed P K, lambda_origin P K,
      masked_empty P K, original_nonempty P K⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RecFieldMaskLambdaAttack
