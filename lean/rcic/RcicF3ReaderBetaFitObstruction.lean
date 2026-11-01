import rcic.RcicF3ReaderNoBeta
import rcic.RcicF3DBoundDefs
import rcic.RcicF3EnvSound

/-!
# The exact missing beta-fit certificate

At a beta redex whose reduct has nonempty denotation, semantic preservation
is equivalent to membership of the actual argument in the lambda domain.
Source InstOK, soundness of the constant environment, faithful delta
equations, and an original bounded typing do not supply this membership at
a local environment that fails to fit that typing context.

The concrete counterexample below uses the empty admitted constant
environment and a one-assumption local context. It is a local reader
obstruction, not an admitted inductive-group counterexample and not a
refutation of the original soundness root. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ReaderBetaFit
open Rcic.Declarative
universe u

/-- Outside the abstraction's domain, its application denotes empty. -/
theorem application_empty_of_not_mem (M : Interp.{u})
    {A x : PSet.{u}} {b : PSet.{u} → PSet.{u}}
    (hx : ¬ x ∈ Ed M A) : Equiv (fapp (lamVal M A b) x) pempty := by
  cases hd : M.dec (LamProof M A b) with
  | isTrue hproof =>
      change Equiv (fapp (cond M.dec _ _ _) x) pempty
      rw [cond_pos hproof]
      exact fapp_pempty x
  | isFalse hproof =>
      change Equiv (fapp (cond M.dec _ _ _) x) pempty
      rw [cond_neg hproof]
      exact fapp_mkLam_out hx

/-- For a nonempty reduct, argument membership is necessary and sufficient.
This is the exact local obligation at a reverse beta-reader edge. -/
theorem beta_preserved_iff (M : Interp.{u}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) (A b a : Expr Nat)
    (hne : ¬ Equiv (den M σ ρ (instantiate0 a b)) pempty) :
    Equiv (den M σ ρ (.app (.lam A b) a))
        (den M σ ρ (instantiate0 a b)) ↔
      den M σ ρ a ∈ Ed M (den M σ ρ A) := by
  constructor
  · intro he
    apply mem_of_fapp_lamVal_ne M
    intro hz
    exact hne (he.symm.trans hz)
  · intro ha
    rw [den_inst0]
    exact beta_val M
      (fun _ _ hx => den_congr M σ b
        (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl))) ha

def context : LCtx := [.assumption (.sort .zero)]

def source : Expr Nat :=
  .app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)

noncomputable def context_wf : CtxWfT emptyEnv 0 context :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

noncomputable def source_typed :
    HasTyT emptyEnv 0 context source (.sort (.succ .zero)) :=
  .app context (.lam (.sort .zero) (.sort .zero)) (.bvar 0)
    (.sort .zero) (.sort (.succ .zero))
    (.lam context (.sort .zero) (.succ .zero) (.sort .zero)
      (.sort (.succ .zero))
      (.sort context .zero)
      (.sort (.assumption (.sort .zero) :: context) .zero))
    (.bvar context 0 (.sort .zero) rfl)

theorem source_bound (σ K : Nat → Nat) : LOKt σ 4 K source_typed := by
  change (1 ≤ 4 ∧ 1 ≤ 4) ∧ True
  exact ⟨⟨by decide, by decide⟩, True.intro⟩

theorem source_instOK (σ K : Nat → Nat) : InstOK emptyEnv σ K source :=
  instOK_of_lokt σ 4 K source_typed (source_bound σ K)

theorem source_read : piTelescopeFuel emptyEnv 3 source = some ([], .sort .zero) := rfl

theorem constant_environment_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) :
    EnvSound (mkM P μ) σ K emptyEnv 0 := by
  apply envSound_of_allSound P (E := emptyEnv) (μ := μ) (K := K) ?_ ?_ σ 0
  · intro r m hm
    change (none : Option CheckedMember) = some m at hm
    cases hm
  · intro r m hm
    change (none : Option CheckedMember) = some m at hm
    cases hm

theorem body_equations (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P μ) emptyEnv σ := by
  intro r ls b hb _ρ
  cases hb

theorem argument_not_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) :
    ¬ pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ0 (.sort .zero)) := by
  intro hp
  exact pempty_not_mem_U4 P 0
    (mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)) hp)

theorem context_not_fits (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) :
    ¬ Fits (mkM P μ) σ context ρ0 := by
  intro h
  exact argument_not_mem P μ σ h.2

theorem source_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) :
    Equiv (den (mkM P μ) σ ρ0 source) pempty :=
  application_empty_of_not_mem (mkM P μ) (argument_not_mem P μ σ)

theorem normal_member (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) :
    tyv pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ0 (.sort .zero)) :=
  tyv_pempty_mem_sort P μ σ ρ0 .zero

theorem source_has_no_member (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (x : PSet.{4}) :
    ¬ x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ0 source) := by
  intro hx
  exact not_mem_pempty (mem_congr_right
    ((ed_congr (mkM P μ) (source_empty P μ σ)).trans (ed_pempty (mkM P μ))) hx)

/-- Even with an actual bounded source typing, the proposed unguarded
reverse transport fails at this exact normalized member. -/
theorem reverse_membership_fails (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) :
    EnvSound (mkM P μ) σ K emptyEnv 0 ∧
    DeltaNormalize.BodyEquations (mkM P μ) emptyEnv σ ∧
    Nonempty (CtxWfT emptyEnv 0 context) ∧
    InstOK emptyEnv σ K source ∧ LOKt σ 4 K source_typed ∧
    piTelescopeFuel emptyEnv 3 source = some ([], .sort .zero) ∧
    tyv pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ0 (.sort .zero)) ∧
    ¬ tyv pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ0 source) :=
  ⟨constant_environment_sound P μ σ K, body_equations P μ σ, ⟨context_wf⟩,
    source_instOK σ K, source_bound σ K, source_read,
    normal_member P μ σ, source_has_no_member P μ σ _⟩

end Rcic.F3.PSet.ReaderBetaFit

#print axioms Rcic.F3.PSet.ReaderBetaFit.beta_preserved_iff
#print axioms Rcic.F3.PSet.ReaderBetaFit.reverse_membership_fails
