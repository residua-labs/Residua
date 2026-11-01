import rcic.RcicF3PiIndependent
import rcic.RcicF3KTWNonIR
import rcic.RcicTypedStrengthen
import rcic.RcicSubstT

/-!
# The exact local support of an emitted normalized domain

Parallel substitution preserves every explicit constant occurrence of its
source. If its result is family-free, every USED capture is family-free.
A capture containing the family is therefore unused in that source
expression. The actual instantiate operation is included by its existing
substT equation. Literal aliases and arbitrary binder depth are retained.

The semantic composition reuses den_freeAgree and the existing table
independence theorem: two original assignments need agree only at locals
actually read by the source domain. The concrete capture theorem produces
this agreement from cleanliness of the actual substituted domain, even
when unused capture values differ. Existing occursConst_instantiateLevels
supplies the level-substitution case without a duplicate declaration.

These are support producers for reader provenance. They do not produce
the original domain typing or its fitted closure contexts, and no masked
environment is asserted to fit. No scoped NonIR theorem is used.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderSupport
open Rcic.Declarative

/-- Parallel substitution cannot delete a constant already in the source. -/
theorem subst_source_clean (r : Nat) :
    (e : Expr Nat) → (s : SubstT) →
    occursConst r (substT s e) = false → occursConst r e = false
  | .bvar _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, h => h
  | .lit _, _, h => h
  | .app f a, s, h => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h ⊢
      exact ⟨subst_source_clean r f s h.1, subst_source_clean r a s h.2⟩
  | .lam A b, s, h => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h ⊢
      exact ⟨subst_source_clean r A s h.1, subst_source_clean r b s.up h.2⟩
  | .pi A B, s, h => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h ⊢
      exact ⟨subst_source_clean r A s h.1, subst_source_clean r B s.up h.2⟩
  | .letE A v b, s, h => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h ⊢
      exact ⟨⟨subst_source_clean r A s h.1.1, subst_source_clean r v s h.1.2⟩,
        subst_source_clean r b s.up h.2⟩

/-- Every used capture occurs literally in the substituted result. The
recursive proof follows the actual up/lift operation under every binder. -/
theorem subst_capture_clean (r : Nat) :
    (e : Expr Nat) → (s : SubstT) →
    occursConst r (substT s e) = false →
    ∀ i, freeBvarRef i 0 e = true → occursConst r (s i) = false
  | .bvar j, s, h, i, hu => by
      have hji : j = i := by
        simpa only [freeBvarRef, Nat.add_zero, decide_eq_true_eq] using hu
      subst j
      exact h
  | .sort _, _, _, _, hu => by cases hu
  | .const _ _, _, _, _, hu => by cases hu
  | .lit _, _, _, _, hu => by cases hu
  | .app f a, s, h, i, hu => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h
      simp only [freeBvarRef, Bool.or_eq_true_iff] at hu
      rcases hu with hf | ha
      · exact subst_capture_clean r f s h.1 i hf
      · exact subst_capture_clean r a s h.2 i ha
  | .lam A b, s, h, i, hu => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h
      simp only [freeBvarRef, Bool.or_eq_true_iff] at hu
      rcases hu with hA | hb
      · exact subst_capture_clean r A s h.1 i hA
      · have hc := subst_capture_clean r b s.up h.2 (i + 1)
          (by rw [freeBvarRef_succ i 0 b]; exact hb)
        simpa only [SubstT.up_succ, occursConst_lift] using hc
  | .pi A B, s, h, i, hu => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h
      simp only [freeBvarRef, Bool.or_eq_true_iff] at hu
      rcases hu with hA | hB
      · exact subst_capture_clean r A s h.1 i hA
      · have hc := subst_capture_clean r B s.up h.2 (i + 1)
          (by rw [freeBvarRef_succ i 0 B]; exact hB)
        simpa only [SubstT.up_succ, occursConst_lift] using hc
  | .letE A v b, s, h, i, hu => by
      simp only [substT, occursConst, Bool.or_eq_false_iff] at h
      simp only [freeBvarRef, Bool.or_eq_true_iff] at hu
      rcases hu with (hA | hv) | hb
      · exact subst_capture_clean r A s h.1.1 i hA
      · exact subst_capture_clean r v s h.1.2 i hv
      · have hc := subst_capture_clean r b s.up h.2 (i + 1)
          (by rw [freeBvarRef_succ i 0 b]; exact hb)
        simpa only [SubstT.up_succ, occursConst_lift] using hc

/-- The excluded slot is produced from the actual capture and result,
not postulated as a scope or typed-strengthening condition. -/
theorem unused_unclean_capture (r : Nat) (e : Expr Nat) (s : SubstT)
    (hc : occursConst r (substT s e) = false) (i : Nat)
    (hi : occursConst r (s i) = true) : freeBvarRef i 0 e = false := by
  cases hu : freeBvarRef i 0 e with
  | false => rfl
  | true =>
      have hf := subst_capture_clean r e s hc i hu
      rw [hi] at hf
      cases hf

/-- Literal single-variable beta/zeta substitution is covered by the
same parallel-substitution producer, including unused unclean captures. -/
theorem instantiate_support (r j : Nat) (v e : Expr Nat)
    (hc : occursConst r (instantiate j v e) = false) :
    occursConst r e = false ∧
      (freeBvarRef j 0 e = true → occursConst r v = false) := by
  rw [instantiate_eq_substT] at hc
  refine ⟨subst_source_clean r e (SubstT.single j v) hc, ?_⟩
  intro hu
  have h := subst_capture_clean r e (SubstT.single j v) hc j hu
  simpa only [SubstT.single, if_pos rfl] using h

/-- Existing local support and table independence compose. The two
assignments may differ arbitrarily outside the source domain's support. -/
theorem den_free_supported (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (r : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat) (e : Expr Nat)
    (hf : occursConst r e = false) (ρ η : Nat → PSet.{4})
    (h : ∀ i, freeBvarRef i 0 e = true → Equiv (ρ i) (η i)) :
    Equiv (den (mkM P (upd μ r X)) σ ρ e)
      (den (mkM P (upd μ r Y)) σ η e) := by
  have hv := den_freeAgree (mkM P (upd μ r X)) σ e h
  have ht := PiIndependent.den_free P μ r X Y σ e hf η
  simpa only [ht] using hv

/-- Cleanliness of the emitted syntax PRODUCES agreement for every read
capture. Unused capture values may differ between the two original models. -/
theorem captured_models_agree (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (r : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat)
    (e : Expr Nat) (s : SubstT) (hc : occursConst r (substT s e) = false)
    (ρ : Nat → PSet.{4}) :
    Equiv (den (mkM P (upd μ r X)) σ
      (fun i => den (mkM P (upd μ r X)) σ ρ (s i)) e)
      (den (mkM P (upd μ r Y)) σ
        (fun i => den (mkM P (upd μ r Y)) σ ρ (s i)) e) := by
  apply den_free_supported P μ r X Y σ e (subst_source_clean r e s hc)
  intro i hi
  have he := PiIndependent.den_free P μ r X Y σ (s i)
    (subst_capture_clean r e s hc i hi) ρ
  simpa only [he] using
    (Equiv.rfl : Equiv (den (mkM P (upd μ r Y)) σ ρ (s i))
      (den (mkM P (upd μ r Y)) σ ρ (s i)))

end Rcic.F3.PSet.ReaderSupport
