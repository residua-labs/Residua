import rcic.RcicF3PiTypedCompile
import rcic.RcicF3RoleAttacks
/-!
# Typed Acc presentation regression

These compiler/conversion checks use the actual two-binder AccP derivation.
The bounds are elementary unfolding facts. Environment soundness and a
fitting context remain premises: no independent inductive-family model or
universal A-axis producer is claimed. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiTypedCompileAttack
open Rcic.Declarative Rcic.Declarative.Ann

theorem fieldBound (σ K : Nat → Nat) : LOKt σ 4 K PiSyntaxAttack.fieldTy := by
  simp [PiSyntaxAttack.fieldTy, accPFieldDomTyT, LOKt, LevelsOK, evalTotal]
/-- Elementary closed-level bounds of the three actual typed conversions. -/
theorem presentationBounds (σ K : Nat → Nat) :
    LOKc σ 4 K PiSyntaxAttack.betaConversion ∧
    LOKc σ 4 K PiSyntaxAttack.deltaConversion ∧
    LOKc σ 4 K PiSyntaxAttack.zetaConversion := by
  simp [PiSyntaxAttack.betaConversion, PiSyntaxAttack.deltaConversion,
    PiSyntaxAttack.zetaConversion, PiSyntaxAttack.idBodyTy,
    PiSyntaxAttack.fieldTy, accPFieldDomTyT, LOKc, LOKt, LevelsOK,
    PiSyntaxAttack.level, evalTotal]

/-- Compiled field at the current interpretation; not a fixed-point family. -/
def compiledField (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) : PSet.{4} :=
  (PiSyntaxCompile.compile (mkM P μ) σ
    (PiTypedCompile.leafIndex (mkM P μ) σ RoleAttacks.accResult)
    RoleAttacks.accDomains ρ).erasedType (mkM P μ) (fun i => i.1)

/-- The two dependent binders and hidden presentations have the same
compiled denotation, conditional on ordinary environment soundness and
context fitting. No environment inhabitant or independent family is claimed. -/
theorem presentations (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat)
    (hE : EnvSound (mkM P μ) σ K PiSyntaxAttack.env 0)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ PiSyntaxAttack.ctx ρ) :
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ paFieldDom) ∧
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ PiSyntaxAttack.betaField) ∧
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ PiSyntaxAttack.deltaField) ∧
    Equiv (compiledField P μ σ ρ) (den (mkM P μ) σ ρ PiSyntaxAttack.zetaField) := by
  have e := PiTypedCompile.compile_spec P μ σ K hE
    RoleAttacks.accDomains RoleAttacks.accResult PiSyntaxAttack.fieldTy
    (fieldBound σ K) ρ hρ
  obtain ⟨hβ, hδ, hζ⟩ := presentationBounds σ K
  exact ⟨e, e.trans (sound_conv (P.good _ rfl) hE
      PiSyntaxAttack.betaConversion hβ ρ hρ).1.symm,
    e.trans (sound_conv (P.good _ rfl) hE
      PiSyntaxAttack.deltaConversion hδ ρ hρ).1.symm,
    e.trans (sound_conv (P.good _ rfl) hE
      PiSyntaxAttack.zetaConversion hζ ρ hρ).1.symm⟩
end Rcic.F3.PSet.PiTypedCompileAttack
