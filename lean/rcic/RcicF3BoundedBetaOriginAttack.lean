import rcic.RcicF3BoundedBetaOrigin
import rcic.RcicF3RecFieldConsumerAttack

/-!
# Converted beta at the actual height-omega W prefix

The argument is the actual recursive W field in the original fitted local
context. The lambda's annotated domain and the application's expected
domain differ syntactically: the latter is a beta-hidden identity applied
to the former. Both the function and its argument have actual bounded
type conversions, followed by an outer conversion on the application.

The new provenance producer supplies both original body contexts in the
source and strictly enlarged W models. A genuinely inhabited dependent
three-binder telescope fits both produced contexts. This is an auxiliary
typed normalization component over the actual admitted prefix, not a new
stored constructor field or a universal domain-mask theorem.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedBetaOriginAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open NormFreshHeadAttack (base C D model σ admissible_C admissible_D prefix_sound)
open RecFieldConsumerAttack (Γ ρ lookupField truth)

def domainLevel : Level := .imax (.succ .zero) (.succ .zero)
def bodyLevel : Level :=
  .imax (.succ .zero) (.imax .zero (.imax .zero (.succ .zero)))
def ds : List (Expr Nat) := [.sort .zero, .bvar 0, .bvar 1]
def body : Expr Nat := policyPi ds (.sort .zero)
def aliasDomain : Expr Nat :=
  .app (.lam (.sort domainLevel) (.bvar 0)) lookupField
def source : Expr Nat := .app (.lam lookupField body) (.bvar 2)

noncomputable def domain_typed : HasTyT PendAW.eFam 0 Γ lookupField (.sort domainLevel) :=
  .pi Γ (.bvar 3) (.succ .zero) (.app (.const 4 []) (.bvar 4)) (.succ .zero)
    (.bvar _ 3 _ rfl)
    (.app _ (.const 4 []) (.bvar 4) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 4 _ rfl))

theorem domain_bound (τ K : Nat → Nat) : LOKt τ 4 K domain_typed := by
  change 1 ≤ 4 ∧ 1 ≤ 4 ∧ True ∧
    ((∀ l, l ∈ ([] : List Level) → evalTotal τ l ≤ K 4) ∧ True)
  exact ⟨by decide, by decide, True.intro,
    (fun l hl => (List.not_mem_nil l hl).elim), True.intro⟩

noncomputable def alias_reduct : ConvT PendAW.eFam 0 Γ aliasDomain lookupField
    (.sort domainLevel) :=
  .beta Γ (.sort domainLevel) (.bvar 0) lookupField (.sort domainLevel)
    (.succ domainLevel) (.sort Γ domainLevel) (.bvar _ 0 _ rfl) domain_typed

theorem alias_bound (τ K : Nat → Nat) : LOKc τ 4 K alias_reduct :=
  ⟨by change 2 ≤ 4; decide, True.intro, domain_bound τ K⟩

noncomputable def domain_conversion : ConvT PendAW.eFam 0 Γ lookupField aliasDomain
    (.sort domainLevel) :=
  .symm Γ aliasDomain lookupField (.sort domainLevel) alias_reduct

noncomputable def body_typed : HasTyT PendAW.eFam 0 (.assumption lookupField :: Γ)
    body (.sort bodyLevel) :=
  .pi _ (.sort .zero) (.succ .zero)
    (.pi (.bvar 0) (.pi (.bvar 1) (.sort .zero)))
    (.imax .zero (.imax .zero (.succ .zero))) (.sort _ .zero)
    (.pi _ (.bvar 0) .zero (.pi (.bvar 1) (.sort .zero))
      (.imax .zero (.succ .zero)) (.bvar _ 0 _ rfl)
      (.pi _ (.bvar 1) .zero (.sort .zero) (.succ .zero)
        (.bvar _ 1 _ rfl) (.sort _ .zero)))

theorem body_bound (τ K : Nat → Nat) : LOKt τ 4 K body_typed := by
  change 1 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4 ∧
    (0 ≤ 4 ∧ 1 ≤ 4 ∧ True ∧ (0 ≤ 4 ∧ 1 ≤ 4 ∧ True ∧ 1 ≤ 4))
  exact ⟨by decide, by decide, by decide,
    Nat.zero_le _, by decide, True.intro,
    Nat.zero_le _, by decide, True.intro, by decide⟩

noncomputable def function_conversion : ConvT PendAW.eFam 0 Γ
    (.pi lookupField (.sort bodyLevel)) (.pi aliasDomain (.sort bodyLevel))
    (.sort (.imax domainLevel (.succ bodyLevel))) :=
  .pi Γ lookupField aliasDomain (.sort bodyLevel) (.sort bodyLevel)
    domainLevel (.succ bodyLevel) domain_conversion
    (.refl _ (.sort bodyLevel) (.sort (.succ bodyLevel)) (.sort _ bodyLevel))

theorem function_conversion_bound (τ K : Nat → Nat) :
    LOKc τ 4 K function_conversion :=
  ⟨by change 1 ≤ 4; decide, by change 2 ≤ 4; decide,
    alias_bound τ K, by change 2 ≤ 4; decide⟩

noncomputable def function_typed : HasTyT PendAW.eFam 0 Γ
    (.lam lookupField body) (.pi aliasDomain (.sort bodyLevel)) :=
  .conv Γ (.lam lookupField body) (.pi lookupField (.sort bodyLevel))
    (.pi aliasDomain (.sort bodyLevel)) (.imax domainLevel (.succ bodyLevel))
    (.lam Γ lookupField domainLevel body (.sort bodyLevel) domain_typed body_typed)
    function_conversion

noncomputable def argument_typed : HasTyT PendAW.eFam 0 Γ (.bvar 2) aliasDomain :=
  .conv Γ (.bvar 2) lookupField aliasDomain domainLevel
    (.bvar Γ 2 lookupField rfl) domain_conversion

noncomputable def application_typed : HasTyT PendAW.eFam 0 Γ source (.sort bodyLevel) :=
  .app Γ (.lam lookupField body) (.bvar 2) aliasDomain (.sort bodyLevel)
    function_typed argument_typed

/-- The outer conversion changes the literal requested sort as well. -/
noncomputable def source_typed : HasTyT PendAW.eFam 0 Γ source
    (.sort (.max .zero bodyLevel)) :=
  .conv Γ source (.sort bodyLevel) (.sort (.max .zero bodyLevel)) (.succ bodyLevel)
    application_typed (.sorts Γ bodyLevel (.max .zero bodyLevel) (fun _ => rfl))

theorem source_bound (τ K : Nat → Nat) : LOKt τ 4 K source_typed :=
  ⟨⟨⟨⟨domain_bound τ K, body_bound τ K⟩, function_conversion_bound τ K⟩,
    True.intro, alias_bound τ K⟩, by change 2 ≤ 4; decide⟩

theorem domains_different : lookupField ≠ aliasDomain := by
  intro h
  cases h

theorem reader : piTelescopeFuel PendAW.eFam 16 source = some (ds, .sort .zero) := rfl

def values : List PSet.{4} := [truth, pempty, pempty]

theorem values_fit (P : Premises4) (X : Frame) (τ : Nat → Nat)
    (η : Nat → PSet.{4}) : TelFits (model P X) τ ds η values := by
  have ht : pempty ∈ Ed (model P X) truth :=
    mem_congr_right (ed_tyv (model P X) (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  refine ⟨?_, ht, ht, True.intro⟩
  exact mem_congr_right (ed_tyv (model P X) (U4_dich 0)).symm
    (RecFieldConsumerAttack.truth_mem P)

/-- The same actual converted application produces both source/enlarged
body environments and all three original dependent domain derivations. -/
theorem composition (P : Premises4) (K : Nat → Nat) :
    (∃ B,
      BoundedBetaOrigin.BodyAt (model P (C P)) σ Γ (ρ P) lookupField body (.bvar 2) B ∧
      BoundedBetaOrigin.BodyAt (model P (D P)) σ Γ (ρ P) lookupField body (.bvar 2) B) ∧
    BoundedPiSpine.Domains (E := PendAW.eFam) (n := 0) σ 4 K
      (.assumption lookupField :: Γ) ds ∧
    ∃ (T : Expr Nat)
      (dt : HasTyT PendAW.eFam 0
        (BoundedPiSpine.context (.assumption lookupField :: Γ) ds) (.sort .zero) T),
          LOKt σ 4 K dt :=
  BoundedBetaOrigin.paired_spine P
    (table P (base P) PendAWBridge.fd (C P))
    (table P (base P) PendAWBridge.fd (D P)) σ K ds (.sort .zero)
    source_typed (source_bound σ K)
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0) (ρ P) (ρ P)
    (RecFieldConsumerAttack.contexts_fit P).1 (RecFieldConsumerAttack.contexts_fit P).2

theorem contexts_fit (P : Premises4) (K : Nat → Nat) :
    Fits (model P (C P)) σ
      (BoundedPiSpine.context (.assumption lookupField :: Γ) ds)
      (push values (vcons (RawFamilyIHBuilderAttack.x P) (ρ P))) ∧
    Fits (model P (D P)) σ
      (BoundedPiSpine.context (.assumption lookupField :: Γ) ds)
      (push values (vcons (RawFamilyIHBuilderAttack.x P) (ρ P))) := by
  obtain ⟨B, hC, hD⟩ := (composition P K).1
  exact ⟨BoundedPiSpine.context_fits (model P (C P)) σ ds _ values hC.fits
      (values_fit P (C P) σ _),
    BoundedPiSpine.context_fits (model P (D P)) σ ds _ values hD.fits
      (values_fit P (D P) σ _)⟩

def Witness (P : Premises4) : Prop :=
  RecFieldConsumerAttack.Witness P ∧
  lookupField ≠ aliasDomain ∧ ds.length = 3 ∧
  piTelescopeFuel PendAW.eFam 16 source = some (ds, .sort .zero) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ source (.sort (.max .zero bodyLevel))) ∧
  (∀ K, LOKt σ 4 K source_typed ∧
    (∃ B,
      BoundedBetaOrigin.BodyAt (model P (C P)) σ Γ (ρ P) lookupField body (.bvar 2) B ∧
      BoundedBetaOrigin.BodyAt (model P (D P)) σ Γ (ρ P) lookupField body (.bvar 2) B) ∧
    BoundedPiSpine.Domains (E := PendAW.eFam) (n := 0) σ 4 K
      (.assumption lookupField :: Γ) ds ∧
    Fits (model P (C P)) σ
      (BoundedPiSpine.context (.assumption lookupField :: Γ) ds)
      (push values (vcons (RawFamilyIHBuilderAttack.x P) (ρ P))) ∧
    Fits (model P (D P)) σ
      (BoundedPiSpine.context (.assumption lookupField :: Γ) ds)
      (push values (vcons (RawFamilyIHBuilderAttack.x P) (ρ P))))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldConsumerAttack.component_witness P, domains_different, rfl, reader,
    ⟨source_typed⟩, fun K => ⟨source_bound σ K, (composition P K).1,
      (composition P K).2.1, (contexts_fit P K).1, (contexts_fit P K).2⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.BoundedBetaOriginAttack
