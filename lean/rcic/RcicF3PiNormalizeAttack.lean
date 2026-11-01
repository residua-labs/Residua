import rcic.RcicF3PiNormalize
import rcic.RcicF3PiEraseAttack
import rcic.RcicF3PiRecPlanAttack
import rcic.RcicF3PiTypedCompileAttack
/-! Normalized semantic-field regressions. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiNormalizeAttack
open Rcic.Declarative
universe u

/-- Empty environments inhabit ordinary semantic soundness, for every
interpretation; elementary impossibility of a stored constant or iota. -/
theorem emptySound (M : Interp.{u}) (σ K : Nat → Nat) : EnvSound M σ K emptyEnv 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ _ _ h
    cases h
  · intro _ _ _ _ _ _ h
    cases h
  · intro _ _ _ _ _ hi
    cases hi with
    | of w => cases w.hctor

/-- The original two-binder typed Acc field and all three hidden
presentations enter the new extraction theorem with the existing bounds.
This remains conditional on ordinary EnvSound and BodiesOK, not an
independent family interpretation. Elementary composition. -/
theorem acc_presentations (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) (hE : EnvSound (mkM P μ) σ K PiSyntaxAttack.env 0)
    (hb : BodiesOK PiSyntaxAttack.env σ K) (ρ : Nat → PSet.{4}) :
    ∀ T ∈ [Rcic.Declarative.Ann.paFieldDom, PiSyntaxAttack.betaField,
      PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
    ∀ x, x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T) →
      x ∈ Ed (mkM P μ) (PiTypedCompileAttack.compiledField P μ σ ρ) := by
  have hf := PiTypedCompileAttack.fieldBound σ K
  obtain ⟨hβ, _, hζ⟩ := PiTypedCompileAttack.presentationBounds σ K
  have go : ∀ T, piTelescopeFuel PiSyntaxAttack.env 64 T =
        some (RoleAttacks.accDomains, RoleAttacks.accResult) →
      InstOK PiSyntaxAttack.env σ K T → ∀ x,
      x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T) →
      x ∈ Ed (mkM P μ) (PiTypedCompileAttack.compiledField P μ σ ρ) := by
    intro T hw hI x hx
    exact (normalizedField_mem (mkM P μ) σ K hE hb 64 T
      RoleAttacks.accDomains RoleAttacks.accResult ρ x hw hI hx).2
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact go _ RoleAttacks.accRead (instOK_of_lokt σ 4 K PiSyntaxAttack.fieldTy hf)
  · exact go _ RoleAttacks.betaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.betaTyped
      ⟨⟨hβ.1, hβ.2.1⟩, hβ.2.2⟩)
  · exact go _ RoleAttacks.deltaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.deltaTyped
      ⟨(fun _ h => False.elim (List.not_mem_nil _ h)), hf⟩)
  · exact go _ RoleAttacks.zetaRead (instOK_of_lokt σ 4 K PiSyntaxAttack.zetaTyped hζ)

def emptyType : Expr Nat := .pi (.bvar 0) (.pi (.bvar 2) (.bvar 2))
def betaEmpty : Expr Nat := .app (.lam (.bvar 2) (.bvar 0)) emptyType
def zetaEmpty : Expr Nat := .letE (.bvar 2) emptyType (.bvar 0)
def emptyDomains : List (Expr Nat) := [.bvar 0, .bvar 2]
def emptyRaw (M : Interp.{u}) : PSet.{u} :=
  piVal M (tyv PiErasureAttack.domain) (fun _ =>
    piVal M (tyv pempty) (fun _ => tyv PiErasureAttack.domain))
def emptyAssignment (M : Interp.{u}) : Nat → PSet.{u}
  | 0 => tyv PiErasureAttack.domain
  | 1 => tyv pempty
  | _ => tyv (singleton (emptyRaw M))

/- Computation pins for the two-binder empty-domain semantic fixture. -/
kernel_rfl_theorem emptyRead :
  piTelescopeFuel emptyEnv 16 emptyType = some (emptyDomains, .bvar 2)
kernel_rfl_theorem betaEmptyRead :
  piTelescopeFuel emptyEnv 16 betaEmpty = some (emptyDomains, .bvar 2)
kernel_rfl_theorem zetaEmptyRead :
  piTelescopeFuel emptyEnv 16 zetaEmpty = some (emptyDomains, .bvar 2)

/-- The normalized compiler accepts the inhabited nested empty-domain
field and its beta/zeta presentations. Its environment soundness is
inhabited by emptySound. This is a semantic field fixture, not a typing
derivation for a new inductive group. -/
theorem empty_presentations (M : Interp.{u}) (σ K : Nat → Nat) :
    (∀ T ∈ [emptyType, betaEmpty, zetaEmpty],
      pempty ∈ Ed M (den M σ (emptyAssignment M) T)) ∧
    pempty ∈ Ed M ((PiSyntaxCompile.compile M σ
      (PiTypedCompile.leafIndex M σ (.bvar 2)) emptyDomains (emptyAssignment M)).erasedType
      M (fun i => i.1)) ∧ ¬ pempty ∈ PiErasureAttack.literal.{u} := by
  have h0 : pempty ∈ Ed M (den M σ (emptyAssignment M) emptyType) :=
    (PiErasureAttack.nested_empty_domain.{u,u} M).1
  have hd : Dich (singleton (emptyRaw M)) :=
    Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm)
  have ha : den M σ (emptyAssignment M) emptyType ∈
      Ed M (den M σ (emptyAssignment M) (.bvar 2)) :=
    mem_congr_right (ed_tyv M hd).symm (mem_singleton.mpr Equiv.rfl)
  have he : Equiv (den M σ (emptyAssignment M) betaEmpty)
      (den M σ (emptyAssignment M) emptyType) :=
    beta_val M (fun _ _ h => h) ha
  have hβ := mem_congr_right (ed_congr M he).symm h0
  have hζ : pempty ∈ Ed M (den M σ (emptyAssignment M) zetaEmpty) := h0
  have hb : BodiesOK emptyEnv σ K := by intro _ _ _ _ h; cases h
  have hI : InstOK emptyEnv σ K emptyType := by intro _ _ h; cases h
  have hc := (normalizedField_mem M σ K (emptySound M σ K) hb 16 emptyType
    emptyDomains (.bvar 2) (emptyAssignment M) pempty emptyRead hI h0).2
  refine ⟨?_, hc, (PiErasureAttack.nested_empty_domain.{u,u} M).2⟩
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact h0
  · exact hβ
  · exact hζ

end Rcic.F3.PSet.PiNormalizeAttack
