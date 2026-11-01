import rcic.RcicF3RecFieldMaskTyping
import rcic.RcicF3RecFieldMaskLambdaAttack

/-!
# A typed clean domain reads an actual recursive W local through consumers

The actual W local is nonempty and contains the height-omega branch from
the retained witness. A proof-valued consumer erases it; an ordinary
observer turns that proof into an inhabited proposition type. Thus the
clean domain syntax really contains the recursive local. The public
typing induction proves domain equality with that local masked to pempty.

The beta and zeta variants retain actual bounded derivations, and a literal
dependent Pi of depth three puts the same consumer at its terminal. Every
new equality calls the public typed producer. Both original environments
fit, while the masked environment is explicitly shown NOT to fit. This
is an auxiliary typed context at the admitted W prefix, not a new admitted
constructor or a universal normalized reader/domain-mask claim.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMaskTypingAttack
open Rcic.Declarative RawFamily RecFieldMask
open NormFreshHeadAttack (base C D model σ admissible_C admissible_D prefix_sound)
open RecFieldConsumerAttack (truth)
open PendAWBridge (fd)

def observerType : Expr Nat := .pi (.bvar 2) (.sort .zero)
def Γ : LCtx := .assumption observerType :: RecFieldOriginAttack.Γ
def marks : Marks := ordinary RecFieldMaskLambdaAttack.marks
noncomputable def observer (P : Premises4) : PSet.{4} :=
  lamVal (model P (C P)) truth (fun _ => truth)
noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons (observer P) (RecFieldOriginAttack.ρ P)
noncomputable def masked (P : Premises4) : Nat → PSet.{4} :=
  vcons (observer P) (RecFieldMaskLambdaAttack.masked P)

def field : Expr Nat := RecFieldConsumerAttack.fieldAt 5
def inner : Expr Nat := .app (.bvar 2) (.bvar 4)
def domain : Expr Nat := .app (.bvar 0) inner
def betaDomain : Expr Nat := .app (.lam (.sort .zero) (.bvar 0)) domain
def zetaDomain : Expr Nat := .letE (.sort .zero) domain (.bvar 0)
def deepBody : Expr Nat := .app (.bvar 3) (.app (.bvar 5) (.bvar 7))
def deepDomain : Expr Nat := policyPi [.sort .zero, .bvar 0, .bvar 1] deepBody
def deepLevel : Level := .imax (.succ .zero) (.imax .zero (.imax .zero .zero))

noncomputable def inner_typed : HasTyT PendAW.eFam 0 Γ inner (.bvar 3) :=
  .app Γ (.bvar 2) (.bvar 4) field (.bvar 4)
    (.bvar Γ 2 (.pi field (.bvar 4)) rfl) (.bvar Γ 4 field rfl)

noncomputable def domain_typed : HasTyT PendAW.eFam 0 Γ domain (.sort .zero) :=
  .app Γ (.bvar 0) inner (.bvar 3) (.sort .zero)
    (.bvar Γ 0 (.pi (.bvar 3) (.sort .zero)) rfl) inner_typed

noncomputable def beta_typed : HasTyT PendAW.eFam 0 Γ betaDomain (.sort .zero) :=
  .app Γ (.lam (.sort .zero) (.bvar 0)) domain (.sort .zero) (.sort .zero)
    (.lam Γ (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (.sort Γ .zero) (.bvar _ 0 (.sort .zero) rfl)) domain_typed

noncomputable def zeta_typed : HasTyT PendAW.eFam 0 Γ zetaDomain (.sort .zero) :=
  .letE Γ (.sort .zero) (.succ .zero) domain (.sort .zero) (.bvar 0)
    (.sort Γ .zero) domain_typed (.bvar _ 0 (.sort .zero) rfl)

noncomputable def deep_body_typed : HasTyT PendAW.eFam 0
    (.assumption (.bvar 1) :: .assumption (.bvar 0) :: .assumption (.sort .zero) :: Γ)
    deepBody (.sort .zero) :=
  .app _ (.bvar 3) (.app (.bvar 5) (.bvar 7)) (.bvar 6) (.sort .zero)
    (.bvar _ 3 (.pi (.bvar 6) (.sort .zero)) rfl)
    (.app _ (.bvar 5) (.bvar 7) (RecFieldConsumerAttack.fieldAt 8) (.bvar 7)
      (.bvar _ 5 (.pi (RecFieldConsumerAttack.fieldAt 8) (.bvar 7)) rfl)
      (.bvar _ 7 (RecFieldConsumerAttack.fieldAt 8) rfl))

noncomputable def deep_typed : HasTyT PendAW.eFam 0 Γ deepDomain (.sort deepLevel) :=
  .pi Γ (.sort .zero) (.succ .zero)
    (.pi (.bvar 0) (.pi (.bvar 1) deepBody)) (.imax .zero (.imax .zero .zero))
    (.sort Γ .zero)
    (.pi _ (.bvar 0) .zero (.pi (.bvar 1) deepBody) (.imax .zero .zero)
      (.bvar _ 0 (.sort .zero) rfl)
      (.pi _ (.bvar 1) .zero deepBody .zero
        (.bvar _ 1 (.sort .zero) rfl) deep_body_typed))

theorem bounds (K : Nat → Nat) :
    LOKt σ 4 K domain_typed ∧ LOKt σ 4 K beta_typed ∧
    LOKt σ 4 K zeta_typed ∧ LOKt σ 4 K deep_typed := by
  refine ⟨⟨True.intro, True.intro, True.intro⟩,
    ⟨⟨by change 1 ≤ 4; decide, True.intro⟩, True.intro, True.intro, True.intro⟩,
    ⟨by change 1 ≤ 4; decide, ⟨True.intro, True.intro, True.intro⟩, True.intro⟩, ?_⟩
  change 1 ≤ 4 ∧ 0 ≤ 4 ∧ 1 ≤ 4 ∧
    (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧
      (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧ (True ∧ True ∧ True)))
  exact ⟨by decide, by decide, by decide,
    by decide, by decide, True.intro, by decide, by decide,
    True.intro, True.intro, True.intro, True.intro⟩

theorem observer_mem (P : Premises4) (X : Frame) :
    observer P ∈ Ed (model P X)
      (den (model P X) σ (RecFieldOriginAttack.ρ P) observerType) := by
  apply lam_mem (model P X) (A := truth) (b := fun _ => truth)
    (B := fun _ => tyv (U W4 0))
    (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl)
  intro x _
  exact mem_congr_right (ed_tyv (model P X) (U4_dich 0)).symm
    (RecFieldConsumerAttack.truth_mem P)

theorem contexts_fit (P : Premises4) :
    Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) :=
  ⟨⟨(RecFieldOriginAttack.contexts_fit P).1, observer_mem P (C P)⟩,
    ⟨(RecFieldOriginAttack.contexts_fit P).2, observer_mem P (D P)⟩⟩

/-- All local relation facts are produced. At the recursive slot the
actual admitted reader supplies Origin; every other local is unchanged. -/
theorem original_context (P : Premises4) (K : Nat → Nat) :
    Context P (base P) fd (C P) σ RecFieldMaskLambdaAttack.marks
      RecFieldOriginAttack.Γ (RecFieldOriginAttack.ρ P)
      (RecFieldMaskLambdaAttack.masked P) := by
  intro k A hk
  by_cases h3 : k = 3
  · subst k
    change some RecFieldOriginAttack.field = some A at hk
    cases hk
    change Equiv pempty pempty ∧ RecFieldOrigin.Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) σ (RecFieldOriginAttack.ρ P)
        RecFieldOriginAttack.field))
      (Ed (model P (D P)) (den (model P (D P)) σ (RecFieldOriginAttack.ρ P)
        RecFieldOriginAttack.field)) (RawFamilyIHBuilderAttack.x P)
    exact ⟨Equiv.rfl, RecFieldOriginAttack.lookup_origin P K⟩
  · simp only [RecFieldMaskLambdaAttack.marks, if_neg h3, Value,
      RecFieldMaskLambdaAttack.masked, if_neg h3]
    exact Equiv.rfl

theorem related_context (P : Premises4) (K : Nat → Nat) :
    Context P (base P) fd (C P) σ marks Γ (ρ P) (masked P) :=
  context_ordinary P (base P) fd (C P) σ RecFieldMaskLambdaAttack.marks
    RecFieldOriginAttack.Γ (RecFieldOriginAttack.ρ P)
    (RecFieldMaskLambdaAttack.masked P) (original_context P K)
    (.assumption observerType) (observer P) (observer P) Equiv.rfl

/-- The erased recursive value is not a member of the original nonempty
DATA-returning field. The masking theorem is used without a false Fits. -/
theorem masked_not_fit (P : Premises4) (K : Nat → Nat) :
    ¬ Fits (model P (C P)) σ Γ (masked P) := by
  intro hmask
  have hz := fits_lookupType (model P (C P)) σ Γ (masked P) hmask 4 field rfl
  have hx := fits_lookupType (model P (C P)) σ RecFieldOriginAttack.Γ
    (RecFieldOriginAttack.ρ P) (RecFieldOriginAttack.contexts_fit P).1 3
    RecFieldOriginAttack.field rfl
  change pempty ∈ Ed (model P (C P))
    (den (model P (C P)) σ (RecFieldOriginAttack.ρ P) RecFieldOriginAttack.field) at hz
  rcases dich_ed (model P (C P))
      (den (model P (C P)) σ (RecFieldOriginAttack.ρ P) RecFieldOriginAttack.field)
    with hp | hn
  · exact RecFieldOriginCasesAttack.field_nonempty P K (hp _ hx)
  · exact hn hz

/-- The actual consumer applications, beta/let variants and dependent
depth-three product all invoke the complete typing induction. -/
theorem domain_masks (P : Premises4) (K : Nat → Nat) :
    ∀ e ∈ [domain, betaDomain, zetaDomain, deepDomain],
      Equiv (den (model P (C P)) σ (ρ P) e)
        (den (model P (C P)) σ (masked P) e) := by
  have hC := prefix_sound P (C P) (admissible_C P) σ K 0
  have hD := prefix_sound P (D P) (admissible_D P) σ K 0
  have hf := contexts_fit P
  have hr := related_context P K
  have hb := bounds K
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact domain_eq P (base P) fd (C P) σ K hC hD marks (ρ P) (masked P)
      hf.1 hf.2 hr rfl domain_typed hb.1
  · exact domain_eq P (base P) fd (C P) σ K hC hD marks (ρ P) (masked P)
      hf.1 hf.2 hr rfl beta_typed hb.2.1
  · exact domain_eq P (base P) fd (C P) σ K hC hD marks (ρ P) (masked P)
      hf.1 hf.2 hr rfl zeta_typed hb.2.2.1
  · exact domain_eq P (base P) fd (C P) σ K hC hD marks (ρ P) (masked P)
      hf.1 hf.2 hr rfl deep_typed hb.2.2.2

theorem domain_nonempty (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (den (model P (C P)) σ (ρ P) domain) pempty :=
  den_type_ne_pempty (model P (C P)) σ (fun k => pempty_not_mem_U4 P k) (ρ P)
    (sound_ty (P.good _ rfl) (prefix_sound P (C P) (admissible_C P) σ K 0)
      domain_typed (bounds K).1 (ρ P) (contexts_fit P).1)

def Witness (P : Premises4) : Prop :=
  RecFieldMaskLambdaAttack.Witness P ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ domain (.sort .zero)) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ betaDomain (.sort .zero)) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ zetaDomain (.sort .zero)) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ deepDomain (.sort deepLevel)) ∧
  Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) ∧
  (∀ K : Nat → Nat, Context P (base P) fd (C P) σ marks Γ (ρ P) (masked P) ∧
    ¬ Fits (model P (C P)) σ Γ (masked P) ∧
    (∀ e ∈ [domain, betaDomain, zetaDomain, deepDomain],
      Equiv (den (model P (C P)) σ (ρ P) e)
        (den (model P (C P)) σ (masked P) e)) ∧
    ¬ Equiv (den (model P (C P)) σ (ρ P) domain) pempty)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldMaskLambdaAttack.component_witness P,
    ⟨domain_typed⟩, ⟨beta_typed⟩, ⟨zeta_typed⟩, ⟨deep_typed⟩,
    (contexts_fit P).1, (contexts_fit P).2,
    fun K => ⟨related_context P K, masked_not_fit P K,
      domain_masks P K, domain_nonempty P K⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RecFieldMaskTypingAttack
