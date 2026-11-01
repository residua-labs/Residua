import rcic.RcicF3PiAdmission
import rcic.RcicF3PiNormalizeAttack
/-! Independent-signature attacks, not universal production. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndependentAttack
open Rcic.Declarative
open PiIndependent

/- Literal refs 1/2 are scanned, rather than excluded by a numbering wall. -/
kernel_rfl_theorem zeroAlias : containsFamilyFuel emptyEnv 1 16 (.lit 0) = some true
kernel_rfl_theorem succAlias : containsFamilyFuel emptyEnv 2 16 (.lit 1) = some true
kernel_rfl_theorem succZeroFree : containsFamilyFuel emptyEnv 2 16 (.lit 0) = some false

/-- Dropping the literal-aware scan really changes denotation under family
replacement. This does not use an assumed environment soundness. -/
theorem literal_dependence (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    ¬ Equiv (den (mkM P (upd μ 1 (fun _ => pempty))) σ ρ (.lit 0))
      (den (mkM P (upd μ 1 (fun _ => singleton pempty))) σ ρ (.lit 0)) := by
  intro h
  change Equiv ((upd μ 1 (fun _ => pempty)) 1 [])
    ((upd μ 1 (fun _ => singleton pempty)) 1 []) at h
  rw [upd_eq, upd_eq] at h
  exact not_mem_pempty (mem_congr_right h.symm (mem_singleton.mpr Equiv.rfl))

def triDomains : List (Expr Nat) := [.bvar 0, .bvar 1, .bvar 2]
def triArgs : List (Expr Nat) := [.bvar 2, .bvar 1, .bvar 0]
def triType (f : Nat) : Expr Nat := policyPi triDomains (foldApps (.const f []) triArgs)

/- Three actual dependent indices; all numeric family references, including
literal aliases, are accepted because no domain or index reads a literal. -/
kernel_rfl_theorem triOne : fieldAnalyze emptyEnv 32 1 0 0 3 0 (triType 1) =
  .permitted (.recursive 3) triArgs
kernel_rfl_theorem triTwo : fieldAnalyze emptyEnv 32 2 0 0 3 0 (triType 2) =
  .permitted (.recursive 3) triArgs
kernel_rfl_theorem triRelabel : fieldAnalyze emptyEnv 32 987 0 0 3 0 (triType 987) =
  .permitted (.recursive 3) triArgs

/-- The complete depth-three telescope is independent at every family
reference, while retaining its three actual argument labels. -/
theorem tri_independent (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    recursiveTel P (upd μ f X₁) σ triDomains triArgs ρ =
      recursiveTel P (upd μ f X₂) σ triDomains triArgs ρ := by
  rfl


/-- Elementary index readback: three binders retain the outer-to-inner
values, rather than collapsing to a candidate-family set. -/
theorem tri_indices (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (a b c : PSet.{4}) :
    leafArgs P μ σ triArgs (vcons c (vcons b (vcons a ρ))) = [a, b, c] := by rfl

def emptyType (f : Nat) : Expr Nat := .pi (.bvar 0) (.pi (.bvar 2) (.const f []))
def emptyAssignment : Nat → PSet.{4}
  | 0 => tyv PiErasureAttack.domain
  | 1 => tyv pempty
  | _ => pempty

/-- An actual inhabited field with a nonempty outer and empty inner domain
enters the independent signature at every numeric family reference. The
literal graph product still refuses its erased proof. Field-only scope. -/
theorem empty_member (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (σ : Nat → Nat) :
    let X : List Nat → PSet.{4} := fun _ => tyv PiErasureAttack.domain
    let M := mkM P (upd μ f X)
    pempty ∈ Ed M ((PiSyntaxCompile.compile (mkM P μ) σ (leafArgs P μ σ [])
      PiNormalizeAttack.emptyDomains emptyAssignment).erasedType M
        (fun xs => Ed M (fapps (X []) xs))) ∧
      ¬ pempty ∈ PiErasureAttack.literal.{4} := by
  dsimp only
  let X : List Nat → PSet.{4} := fun _ => tyv PiErasureAttack.domain
  let M := mkM P (upd μ f X)
  have hx : pempty ∈ Ed M (den M σ emptyAssignment (emptyType f)) := by
    change pempty ∈ Ed M (piVal M (tyv PiErasureAttack.domain) (fun _ =>
      piVal M (tyv pempty) (fun _ => (upd μ f X) f [])))
    rw [upd_eq]
    exact (PiErasureAttack.nested_empty_domain.{4,4} M).1
  have hd : ∀ e ∈ PiNormalizeAttack.emptyDomains, occursConst f e = false := by
    simp [PiNormalizeAttack.emptyDomains, occursConst]
  have he := recursiveField_ed P μ f X σ [] PiNormalizeAttack.emptyDomains []
    hd (fun _ h => (List.not_mem_nil _ h).elim) emptyAssignment
  exact ⟨mem_congr_right he.symm hx, (PiErasureAttack.nested_empty_domain.{4,4} M).2⟩


/-- All actual typed Acc beta/delta/zeta presentations enter the same
independent argument-labelled field. Ordinary environment semantics remain
explicit; this does not inhabit the complete Acc group model. -/
theorem acc_fields (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ 10 X)) σ K PiSyntaxAttack.env 0)
    (hb : BodiesOK PiSyntaxAttack.env σ K) (ρ : Nat → PSet.{4}) :
    ∀ T ∈ [Rcic.Declarative.Ann.paFieldDom, PiSyntaxAttack.betaField,
      PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
    ∀ x, x ∈ Ed (mkM P (upd μ 10 X)) (den (mkM P (upd μ 10 X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 X))
        ((PiSyntaxCompile.compile (mkM P μ) σ (leafArgs P μ σ [.bvar 1])
          RoleAttacks.accDomains ρ).erasedType (mkM P (upd μ 10 X))
          (fun xs => Ed (mkM P (upd μ 10 X)) (fapps (X []) xs))) := by
  have hd : ∀ e ∈ RoleAttacks.accDomains, occursConst 10 e = false := by
    simp [RoleAttacks.accDomains, occursConst]
  have ha : ∀ e ∈ ([.bvar 1] : List (Expr Nat)), occursConst 10 e = false := by
    simp [occursConst]
  have go : ∀ T, piTelescopeFuel PiSyntaxAttack.env 64 T =
        some (RoleAttacks.accDomains, RoleAttacks.accResult) →
      InstOK PiSyntaxAttack.env σ K T → ∀ x,
      x ∈ Ed (mkM P (upd μ 10 X)) (den (mkM P (upd μ 10 X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ 10 X))
        ((PiSyntaxCompile.compile (mkM P μ) σ (leafArgs P μ σ [.bvar 1])
          RoleAttacks.accDomains ρ).erasedType (mkM P (upd μ 10 X))
          (fun xs => Ed (mkM P (upd μ 10 X)) (fapps (X []) xs))) := by
    intro T hw hI x hx
    exact normalized_mem P μ 10 X σ K hE hb 64 T [] RoleAttacks.accDomains
      [.bvar 1] hw hI hd ha ρ x hx
  have hf := PiTypedCompileAttack.fieldBound σ K
  obtain ⟨hβ, _, hζ⟩ := PiTypedCompileAttack.presentationBounds σ K
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact go _ RoleAttacks.accRead (instOK_of_lokt σ 4 K PiSyntaxAttack.fieldTy hf)
  · exact go _ RoleAttacks.betaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.betaTyped
      ⟨⟨hβ.1, hβ.2.1⟩, hβ.2.2⟩)
  · exact go _ RoleAttacks.deltaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.deltaTyped
      ⟨(fun _ h => False.elim (List.not_mem_nil _ h)), hf⟩)
  · exact go _ RoleAttacks.zetaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.zetaTyped hζ)

end Rcic.F3.PSet.PiIndependentAttack
