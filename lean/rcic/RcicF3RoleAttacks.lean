import rcic.RcicF3PendARoleW
import rcic.RcicF3StepDGCheck
import rcic.RcicF3PendAWPresentation
import rcic.RcicF3PiSyntaxAttack
import rcic.RcicF3PiProducerAttack

/-!
# Self-attacks on the candidate family role

The W repair is local. In particular, the landed `famKT` reader is not
silently promoted to an arbitrary-depth normalized-syntax compiler.
The admitted AccP field below has two dependent binders; the old reader
only removes the first and consequently reads no family arguments.
These are executable/kernel pins and elementary unfolding facts, not
an assertion that the full repaired universal target has been produced.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RoleAttacks
open Rcic.Declarative Rcic.Declarative.Ann

/-- A Pi expression is not an application spine. With a nonempty
family telescope the old occurrence reader therefore rejects it. -/
theorem nestedArgs (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (A B : Expr Nat)
    (hne : fd.params ++ fd.indices ≠ []) :
    ¬ argsFitF P μ fd σ ρ (.pi A B) := by
  intro h
  unfold argsFitF at h
  change TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 [] at h
  cases he : fd.params ++ fd.indices with
  | nil => exact hne he
  | cons D Ds => rw [he] at h; exact h

kernel_rfl_theorem accField :
  fieldAt ((famDataOf StepDGCheck.accPNode.a).ctors.getD 0 ([], [])).1 1 = paFieldDom

kernel_rfl_theorem accKind : kindOf 10 paFieldDom = .fn

kernel_rfl_theorem accTelescope :
  (famDataOf StepDGCheck.accPNode.a).params ++ (famDataOf StepDGCheck.accPNode.a).indices =
    [.sort .zero]

/-- The exact admitted typed PendA fixture reaches the bad occurrence
read after just one of its two binders. -/
theorem accNestedArgs (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    ¬ argsFitF P μ (famDataOf StepDGCheck.accPNode.a) σ ρ (piCod paFieldDom) := by
  apply nestedArgs
  rw [accTelescope]
  exact List.noConfusion

/-- The failure is independent of numeric reference labels. -/
theorem relabelNestedArgs (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (f : Nat)
    (hne : fd.params ++ fd.indices ≠ []) :
    ¬ argsFitF P μ fd σ ρ
      (piCod (.pi (.sort .zero) (.pi (.sort .zero) (.app (.const f []) (.bvar 1))))) :=
  nestedArgs P μ fd σ ρ _ _ hne

/-- The finite-stage target really is refuted at the W fixture even
though the new full fixture invariant is produced. -/
theorem legacyContrast (P : Premises4) (k : Nat) :
    (¬ TierGroup.StepAG P (fun _ => k)) ∧
      RoleModel.GInv famKT P (fun _ => k) PendAWGroup.wft :=
  ⟨PendAWGroup.stepAG_false P k, PendARoleW.gInv P k⟩

/-- Admission's normalized reader sees both dependent binders, including
in the actual typed beta/delta/zeta field presentations. These pins concern
the reader, not yet the semantic extraction theorem. -/
def accDomains : List (Expr Nat) :=
  [.sort .zero, .app (.app (.const 9 []) (.bvar 0)) (.bvar 1)]

def accResult : Expr Nat := .app (.const 10 []) (.bvar 1)

kernel_rfl_theorem accRead :
  piTelescopeFuel PiSyntaxAttack.env 64 paFieldDom = some (accDomains, accResult)

kernel_rfl_theorem betaRead :
  piTelescopeFuel PiSyntaxAttack.env 64 PiSyntaxAttack.betaField =
    some (accDomains, accResult)

kernel_rfl_theorem deltaRead :
  piTelescopeFuel PiSyntaxAttack.env 64 PiSyntaxAttack.deltaField =
    some (accDomains, accResult)

kernel_rfl_theorem zetaRead :
  piTelescopeFuel PiSyntaxAttack.env 64 PiSyntaxAttack.zetaField =
    some (accDomains, accResult)

kernel_rfl_theorem accAnalyze :
  fieldAnalyze PiSyntaxAttack.env 65 10 0 0 1 1 paFieldDom =
    .permitted (.recursive 2) [.bvar 1]

kernel_rfl_theorem betaAnalyze :
  fieldAnalyze PiSyntaxAttack.env 65 10 0 0 1 1 PiSyntaxAttack.betaField =
    .permitted (.recursive 2) [.bvar 1]

kernel_rfl_theorem deltaAnalyze :
  fieldAnalyze PiSyntaxAttack.env 65 10 0 0 1 1 PiSyntaxAttack.deltaField =
    .permitted (.recursive 2) [.bvar 1]

kernel_rfl_theorem zetaAnalyze :
  fieldAnalyze PiSyntaxAttack.env 65 10 0 0 1 1 PiSyntaxAttack.zetaField =
    .permitted (.recursive 2) [.bvar 1]

end Rcic.F3.PSet.RoleAttacks
