import rcic.RcicF3PiGraphInversion
import rcic.RcicF3RecFieldConsumerAttack

/-!
# Reached Pi conversion at the admitted W field

The actual height-omega branching function inhabits the W constructor's
stored recursive field. Its Pi domain is changed by a literal typed beta
conversion, in the same admitted family-only environment and original
parameter context. The new bounded semantic inversion then recovers the
domain and every reached codomain, at the full extra-motive valuation.

The beta mirror is an auxiliary converted view of that stored field; no
modified EnvWfT group is claimed. The earlier actual consumer-erasure and
inhabited-path separation components are retained with the same Premises4.
No normalized-domain mask or all-vector frame theorem is inferred here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiGraphInversionAttack
open Rcic.Declarative RawFamily PiIndex
open NormFreshHeadAttack (base C D model parameter σ admissible_C admissible_D prefix_sound)
open RecFieldConsumerAttack (parameterΓ)

def hiddenDomain : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.bvar 1)) (.bvar 0)
def body : Expr Nat := .app (.const 4 []) (.bvar 1)
def hiddenBody : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.app (.const 4 []) (.bvar 2))) (.bvar 1)
def hiddenField : Expr Nat := .pi hiddenDomain hiddenBody
def ρ : Nat → PSet.{4} := vcons parameter ρ0

noncomputable def domain_beta : ConvT PendAW.eFam 0 parameterΓ
    hiddenDomain (.bvar 0) (.sort (.succ .zero)) :=
  .beta parameterΓ (.sort (.succ .zero)) (.bvar 1) (.bvar 0)
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort parameterΓ (.succ .zero))
    (.bvar (.assumption (.sort (.succ .zero)) :: parameterΓ) 1 _ rfl)
    (.bvar parameterΓ 0 _ rfl)

noncomputable def body_beta : ConvT PendAW.eFam 0
    (.assumption (.bvar 0) :: parameterΓ) hiddenBody body (.sort (.succ .zero)) :=
  .beta _ (.sort (.succ .zero)) (.app (.const 4 []) (.bvar 2)) (.bvar 1)
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero))
    (.app _ (.const 4 []) (.bvar 2) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 2 _ rfl))
    (.bvar _ 1 _ rfl)

noncomputable def converted : TyConvT PendAW.eFam 0 parameterΓ
    PendAW.field hiddenField :=
  .of parameterΓ PendAW.field hiddenField
    (.imax (.succ .zero) (.succ .zero))
    (.pi parameterΓ (.bvar 0) hiddenDomain body hiddenBody (.succ .zero) (.succ .zero)
      (.symm parameterΓ hiddenDomain (.bvar 0) (.sort (.succ .zero)) domain_beta)
      (.symm (.assumption (.bvar 0) :: parameterΓ) hiddenBody body
        (.sort (.succ .zero)) body_beta))

theorem conversion_bound (K : Nat → Nat) : BoundedBVar.Bounded σ 4 K converted := by
  simp only [converted, BoundedBVar.Bounded, domain_beta, body_beta, LOKc, LOKt]
  exact ⟨by decide, by decide, ⟨by decide, True.intro, True.intro⟩,
    ⟨by decide, ⟨fun _ h => (List.not_mem_nil _ h).elim, True.intro⟩, True.intro⟩⟩

theorem parameter_fits (P : Premises4) :
    Fits (model P (C P)) σ parameterΓ ρ ∧
      Fits (model P (D P)) σ parameterΓ ρ := by
  have h := RecFieldConsumerAttack.contexts_fit P
  exact ⟨h.1.1.1.1, h.2.1.1.1⟩

theorem field_mem (P : Premises4) :
    RawFamilyIHBuilderAttack.x P ∈ Ed (model P (C P))
      (den (model P (C P)) σ ρ PendAW.field) ∧
      RawFamilyIHBuilderAttack.x P ∈ Ed (model P (D P))
        (den (model P (D P)) σ ρ PendAW.field) := by
  have h := RecFieldConsumerAttack.contexts_fit P
  exact ⟨h.1.1.1.2, h.2.1.1.2⟩

/-- The concrete domain is inhabited, so this is an actual graph case. -/
theorem argument_mem (P : Premises4) : ord 1 ∈ fxDomBig P :=
  (fx_domBig_mem P).mpr ⟨0, Equiv.rfl⟩

theorem field_nonempty (P : Premises4) :
    ¬ Equiv (RawFamilyIHBuilderAttack.x P) pempty := by
  obtain ⟨i, _⟩ := argument_mem P
  have h : ordPair ((fxDomBig P).Func i)
      (fxhW P (Quotient.mk (FSetoid (fxDomBig P)) i)) ∈ RawFamilyIHBuilderAttack.x P :=
    ⟨i, Equiv.rfl⟩
  exact fun he => not_mem_pempty (mem_congr_right he h)

/-- Apply the public bounded conversion theorem in both actually fitted
models. The type's full parameter key and the same inner argument remain. -/
theorem reached (P : Premises4) (K : Nat → Nat) :
    (Equiv (Ed (model P (C P)) (den (model P (C P)) σ ρ (.bvar 0)))
        (Ed (model P (C P)) (den (model P (C P)) σ ρ hiddenDomain)) ∧
      ∀ a, a ∈ Ed (model P (C P)) (den (model P (C P)) σ ρ (.bvar 0)) →
        Equiv (Ed (model P (C P)) (den (model P (C P)) σ (vcons a ρ) body))
          (Ed (model P (C P)) (den (model P (C P)) σ (vcons a ρ) hiddenBody))) ∧
    (Equiv (Ed (model P (D P)) (den (model P (D P)) σ ρ (.bvar 0)))
        (Ed (model P (D P)) (den (model P (D P)) σ ρ hiddenDomain)) ∧
      ∀ a, a ∈ Ed (model P (D P)) (den (model P (D P)) σ ρ (.bvar 0)) →
        Equiv (Ed (model P (D P)) (den (model P (D P)) σ (vcons a ρ) body))
          (Ed (model P (D P)) (den (model P (D P)) σ (vcons a ρ) hiddenBody))) := by
  exact ⟨PiGraphInversion.bounded_conversion P _ σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0) ρ (parameter_fits P).1
    converted (conversion_bound K) (RawFamilyIHBuilderAttack.x P)
    (field_mem P).1 (field_nonempty P),
    PiGraphInversion.bounded_conversion P _ σ K
      (prefix_sound P (D P) (admissible_D P) σ K 0) ρ (parameter_fits P).2
      converted (conversion_bound K) (RawFamilyIHBuilderAttack.x P)
      (field_mem P).2 (field_nonempty P)⟩

/-- Read the recovered codomain at an explicit inhabited argument. -/
theorem actual_argument (P : Premises4) (K : Nat → Nat) :
    ord 1 ∈ Ed (model P (C P)) (den (model P (C P)) σ ρ hiddenDomain) ∧
      fxZW P ∈ Ed (model P (C P))
        (den (model P (C P)) σ (vcons (ord 1) ρ) hiddenBody) := by
  have hdom : Equiv (Ed (model P (C P)) parameter) (fxDomBig P) := by
    rw [fx_domBig_eq P]
    exact (ed_tyv (model P (C P)) fx_dich).trans el_tyv.symm
  have ha : ord 1 ∈ Ed (model P (C P)) parameter :=
    mem_congr_right hdom.symm (argument_mem P)
  have hω : fxZW P ∈ Ed (model P (C P))
      (den (model P (C P)) σ (vcons (ord 1) ρ) body) :=
    (NormFreshHeadAttack.local_fits P (C P) (admissible_C P)
      (NormFreshHeadAttack.omega_C P)).2
  exact ⟨mem_congr_right (reached P K).1.1 ha,
    mem_congr_right ((reached P K).1.2 (ord 1) ha) hω⟩

def Witness (P : Premises4) : Prop :=
  RecFieldConsumerAttack.Witness P ∧
  Nonempty (TyConvT PendAW.eFam 0 parameterΓ PendAW.field hiddenField) ∧
  (∀ K, BoundedBVar.Bounded σ 4 K converted) ∧
  Fits (model P (C P)) σ parameterΓ ρ ∧
  Fits (model P (D P)) σ parameterΓ ρ ∧
  RawFamilyIHBuilderAttack.x P ∈ Ed (model P (C P))
    (den (model P (C P)) σ ρ PendAW.field) ∧
  RawFamilyIHBuilderAttack.x P ∈ Ed (model P (D P))
    (den (model P (D P)) σ ρ PendAW.field) ∧
  ¬ Equiv (RawFamilyIHBuilderAttack.x P) pempty ∧
  (∀ K : Nat → Nat, ord 1 ∈ Ed (model P (C P)) (den (model P (C P)) σ ρ hiddenDomain) ∧
    fxZW P ∈ Ed (model P (C P))
      (den (model P (C P)) σ (vcons (ord 1) ρ) hiddenBody)) ∧
  σ 0 = 1

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldConsumerAttack.component_witness P, ⟨converted⟩,
    conversion_bound, (parameter_fits P).1, (parameter_fits P).2,
    (field_mem P).1, (field_mem P).2, field_nonempty P, actual_argument P, rfl⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PiGraphInversionAttack
