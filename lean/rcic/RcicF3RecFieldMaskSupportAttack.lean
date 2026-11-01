import rcic.RcicF3RecFieldMaskSupportTyping
import rcic.RcicF3NormFieldMaskContextAttack
import rcic.RcicF3ReaderSupportAttack

/-!
# A clean W-dependent domain after an opaque beta capture

The actual auxiliary W context already contains a nonempty recursive
field, a proof-valued consumer and an observer returning a proposition
type. An identity on the DATA family is then captured. Its source and
enlarged values are provably different, and no common identity graph can
fill both original contexts. The clean domain ignores precisely that
capture while still reading the earlier recursive field through its
actual consumer.

Both original fits, allowed-slot agreement, lookup relation, support and
bounded domain typing are produced. The new public supported typing
induction proves equality with the masked assignment, which does not fit.
An actual beta reader pin exposes the same old clean domain. This is an
auxiliary typed reader instance at the admitted W prefix, not a universal
reader-domain mask or an all-world small-frame theorem.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMaskSupportAttack
open Rcic.Declarative RawFamily RecFieldMaskSupport
open NormFreshHeadAttack (base C D model σ admissible_C admissible_D prefix_sound)
open PendAWBridge (fd)

def family : Expr Nat := .app (.const 4 []) (.bvar 5)
def familyLift : Expr Nat := .app (.const 4 []) (.bvar 6)
def captureType : Expr Nat := .pi family familyLift
def identity : Expr Nat := .lam family (.bvar 0)
def level : Level := .imax (.succ .zero) (.succ .zero)
def Γ : LCtx := .assumption captureType :: RecFieldMaskTypingAttack.Γ
def inner : Expr Nat := .app (.bvar 3) (.bvar 5)
def domain : Expr Nat := .app (.bvar 1) inner
def source : Expr Nat := .app (.lam captureType domain) identity
def marks : RecFieldMask.Marks := RecFieldMask.ordinary RecFieldMaskTypingAttack.marks
def allowed : Allowed := allowCons False (fun _ => True)
noncomputable abbrev capture (P : Premises4) (X : Frame) : PSet.{4} :=
  ReaderSupportAttack.value P X
noncomputable def originalC (P : Premises4) : Nat → PSet.{4} :=
  vcons (capture P (C P)) (RecFieldMaskTypingAttack.ρ P)
noncomputable def originalD (P : Premises4) : Nat → PSet.{4} :=
  vcons (capture P (D P)) (RecFieldMaskTypingAttack.ρ P)
noncomputable def masked (P : Premises4) : Nat → PSet.{4} :=
  vcons pempty (RecFieldMaskTypingAttack.masked P)

noncomputable def family_typed : HasTyT PendAW.eFam 0 RecFieldMaskTypingAttack.Γ
    family (.sort (.succ .zero)) :=
  .app _ (.const 4 []) (.bvar 5) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 5 _ rfl)

noncomputable def capture_typed : HasTyT PendAW.eFam 0 RecFieldMaskTypingAttack.Γ
    captureType (.sort level) :=
  .pi _ family (.succ .zero) familyLift (.succ .zero) family_typed
    (.app _ (.const 4 []) (.bvar 6) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 6 _ rfl))

noncomputable def identity_typed : HasTyT PendAW.eFam 0 RecFieldMaskTypingAttack.Γ
    identity captureType :=
  .lam _ family (.succ .zero) (.bvar 0) familyLift
    family_typed (.bvar _ 0 _ rfl)

noncomputable def inner_typed : HasTyT PendAW.eFam 0 Γ inner (.bvar 4) :=
  .app Γ (.bvar 3) (.bvar 5) (RecFieldConsumerAttack.fieldAt 6) (.bvar 5)
    (.bvar Γ 3 (.pi (RecFieldConsumerAttack.fieldAt 6) (.bvar 5)) rfl)
    (.bvar Γ 5 (RecFieldConsumerAttack.fieldAt 6) rfl)

noncomputable def domain_typed : HasTyT PendAW.eFam 0 Γ domain (.sort .zero) :=
  .app Γ (.bvar 1) inner (.bvar 4) (.sort .zero)
    (.bvar Γ 1 (.pi (.bvar 4) (.sort .zero)) rfl) inner_typed

noncomputable def source_typed : HasTyT PendAW.eFam 0 RecFieldMaskTypingAttack.Γ
    source (.sort .zero) :=
  .app _ (.lam captureType domain) identity captureType (.sort .zero)
    (.lam _ captureType level domain (.sort .zero) capture_typed domain_typed)
    identity_typed

theorem identity_bound (K : Nat → Nat) : LOKt σ 4 K identity_typed :=
  ⟨⟨fun _ h => (List.not_mem_nil _ h).elim, True.intro⟩, True.intro⟩

theorem domain_bound (K : Nat → Nat) : LOKt σ 4 K domain_typed :=
  ⟨True.intro, True.intro, True.intro⟩

theorem source_bound (K : Nat → Nat) : LOKt σ 4 K source_typed :=
  ⟨⟨⟨by change 1 ≤ 4; decide, by change 1 ≤ 4; decide,
      ⟨(fun _ h => (List.not_mem_nil _ h).elim), True.intro⟩,
      ⟨(fun _ h => (List.not_mem_nil _ h).elim), True.intro⟩⟩,
    domain_bound K⟩, identity_bound K⟩

theorem beta_reader : whnfFuel PendAW.eFam 32 source =
    some RecFieldMaskTypingAttack.domain := rfl

theorem capture_interpretation (P : Premises4) (X : Frame) :
    den (model P X) σ (RecFieldMaskTypingAttack.ρ P) identity = capture P X := rfl

/-- Each original context contains its own actual identity graph. -/
theorem original_fits (P : Premises4) (K : Nat → Nat) :
    Fits (model P (C P)) σ Γ (originalC P) ∧
    Fits (model P (D P)) σ Γ (originalD P) := by
  have hf := RecFieldMaskTypingAttack.contexts_fit P
  have hc := sound_ty (P.good _ rfl)
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    identity_typed (identity_bound K) (RecFieldMaskTypingAttack.ρ P) hf.1
  have hd := sound_ty (P.good _ rfl)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    identity_typed (identity_bound K) (RecFieldMaskTypingAttack.ρ P) hf.2
  rw [capture_interpretation] at hc hd
  exact ⟨⟨hf.1, hc⟩, ⟨hf.2, hd⟩⟩

theorem supported : Supported allowed domain := by
  intro i hi
  simp only [domain, inner, freeBvarRef, Nat.add_zero,
    Bool.or_eq_true_iff, decide_eq_true_eq] at hi
  rcases hi with h | h | h
  · cases h
    exact True.intro
  · cases h
    exact True.intro
  · cases h
    exact True.intro

theorem originals_agree (P : Premises4) : Agree allowed (originalC P) (originalD P) :=
  agree_cons (fun _ _ => Equiv.rfl) (fun h => h.elim)

/-- The opaque slot is excluded from the relation. Every earlier allowed
slot inherits the actual recursive lookup information, not an assumption. -/
theorem related (P : Premises4) (K : Nat → Nat) :
    Context P (base P) fd (C P) σ marks allowed Γ
      (originalC P) (originalD P) (masked P) :=
  context_opaque P (base P) fd (C P) σ RecFieldMaskTypingAttack.marks
    (fun _ => True) RecFieldMaskTypingAttack.Γ
    (RecFieldMaskTypingAttack.ρ P) (RecFieldMaskTypingAttack.ρ P)
    (RecFieldMaskTypingAttack.masked P)
    (context_of_same P (base P) fd (C P) σ RecFieldMaskTypingAttack.marks
      RecFieldMaskTypingAttack.Γ (RecFieldMaskTypingAttack.ρ P)
      (RecFieldMaskTypingAttack.masked P) (RecFieldMaskTypingAttack.related_context P K))
    (.assumption captureType) none (capture P (C P)) (capture P (D P)) pempty

/-- This is the new public typing recursion at DIFFERENT original
captures. The clean subject still reads its actual recursive W local. -/
theorem produced_domain_eq (P : Premises4) (K : Nat → Nat) :
    Equiv (den (model P (C P)) σ (originalC P) domain)
      (den (model P (C P)) σ (masked P) domain) :=
  domain_eq P (base P) fd (C P) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    marks allowed (originalC P) (originalD P) (masked P) (originals_agree P)
    (original_fits P K).1 (original_fits P K).2 (related P K)
    rfl supported domain_typed (domain_bound K)

theorem masked_not_fit (P : Premises4) (K : Nat → Nat) :
    ¬ Fits (model P (C P)) σ Γ (masked P) :=
  fun h => RecFieldMaskTypingAttack.masked_not_fit P K h.1

theorem domain_nonempty (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (den (model P (C P)) σ (originalC P) domain) pempty :=
  den_type_ne_pempty (model P (C P)) σ (fun k => pempty_not_mem_U4 P k) (originalC P)
    (sound_ty (P.good _ rfl) (prefix_sound P (C P) (admissible_C P) σ K 0)
      domain_typed (domain_bound K) (originalC P) (original_fits P K).1)

def Witness (P : Premises4) : Prop :=
  NormFieldMaskContextAttack.Witness P ∧ ReaderSupportAttack.Witness P ∧
  Nonempty (HasTyT PendAW.eFam 0 RecFieldMaskTypingAttack.Γ source (.sort .zero)) ∧
  whnfFuel PendAW.eFam 32 source = some RecFieldMaskTypingAttack.domain ∧
  Supported allowed domain ∧
  (∀ K, LOKt σ 4 K source_typed ∧
    Fits (model P (C P)) σ Γ (originalC P) ∧ Fits (model P (D P)) σ Γ (originalD P) ∧
    ¬ Equiv (originalC P 0) (originalD P 0) ∧
    Agree allowed (originalC P) (originalD P) ∧
    Context P (base P) fd (C P) σ marks allowed Γ (originalC P) (originalD P) (masked P) ∧
    ¬ Fits (model P (C P)) σ Γ (masked P) ∧
    Equiv (den (model P (C P)) σ (originalC P) domain)
      (den (model P (C P)) σ (masked P) domain) ∧
    ¬ Equiv (den (model P (C P)) σ (originalC P) domain) pempty)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormFieldMaskContextAttack.component_witness P, ReaderSupportAttack.component_witness P,
    ⟨source_typed⟩, beta_reader, supported,
    fun K => ⟨source_bound K, (original_fits P K).1, (original_fits P K).2,
      ReaderSupportAttack.capture_values_differ P K, originals_agree P, related P K,
      masked_not_fit P K, produced_domain_eq P K, domain_nonempty P K⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RecFieldMaskSupportAttack
