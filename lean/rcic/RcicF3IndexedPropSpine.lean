import rcic.RcicF3PropIota
import rcic.RcicF3PropEvalSafeIndex

/-!
# Recover actual fields from a nonempty typed application spine

A head in its stored telescope and a hereditarily typed application spine
determine actual field membership whenever the complete output is not
empty. The argument domains come from the two real product memberships;
no field is erased and no all-fields Prop premise is used. This is a
producer for the ordinary-field telescope part of the separate plain-iota repair.

This theorem does not identify recursor indices with constructor result
indices. That second obligation must come from the actual typed redex,
not from the legacy witness's free index or parameter fields.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedPropSpine
open Rcic.Declarative

universe T

/-- A nonempty application prevents either product containing its head
from using the proof-irrelevant branch. The graph domain then transports
the actual argument into the stored domain, at every telescope binder. -/
theorem fits_of_nonempty (M : Interp.{T}) (σ : Nat → Nat) (b : Expr Nat) :
    (Fs : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    (g : PSet.{T}) → (xs : List PSet.{T}) →
    xs.length = Fs.length →
    g ∈ Ed M (den M σ ρ (policyPi Fs b)) →
    SpineFacts M g xs → ¬ Equiv (fapps g xs) pempty →
    TelFits M σ Fs ρ xs
  | [], _, _, [], _, _, _, _ => True.intro
  | [], _, _, _ :: _, hl, _, _, _ => False.elim (Nat.noConfusion hl)
  | _ :: _, _, _, [], hl, _, _, _ => False.elim (Nat.noConfusion hl)
  | F :: Fs, ρ, g, x :: xs, hl, hg, ⟨⟨D, C, hC, hgD, hxD⟩, hsp⟩, hne => by
      have hgne : ¬ Equiv g pempty :=
        fun he => hne (fapps_of_pempty he (x :: xs))
      have hB := den_resp M σ ρ (policyPi Fs b)
      have hgF := mem_congr_right (ed_piVal M _ _ hB) hg
      haveI := M.dec
      by_cases hProp : PiProp M (den M σ ρ F)
          (fun x => den M σ (vcons x ρ) (policyPi Fs b))
      · rw [cond_pos hProp] at hgF
        exact (hgne (mem_tv.mp hgF).2).elim
      · rw [cond_neg hProp] at hgF
        have hBE : ∀ x x', Equiv x x' →
            Equiv (Ed M (den M σ (vcons x ρ) (policyPi Fs b)))
              (Ed M (den M σ (vcons x' ρ) (policyPi Fs b))) :=
          fun x x' he => ed_congr M (hB x x' he)
        have hgD' := mem_congr_right (ed_piVal M _ _ hC) hgD
        by_cases hPropD : PiProp M D C
        · rw [cond_pos hPropD] at hgD'
          exact (hgne (mem_tv.mp hgD').2).elim
        · rw [cond_neg hPropD] at hgD'
          have hx : x ∈ Ed M (den M σ ρ F) :=
            piSet_dom hBE (fun x x' he => ed_congr M (hC x x' he))
              hgF hgD' hxD
          have hgTail : fapp g x ∈ Ed M
              (den M σ (vcons x ρ) (policyPi Fs b)) :=
            fapp_mem_piSet hBE hgF hx
          exact ⟨hx, fits_of_nonempty M σ b Fs (vcons x ρ) (fapp g x) xs
            (Nat.succ.inj hl) hgTail hsp hne⟩

/-- Remove the actual inserted motive/minor prefix after reconstructing
the fitting tuple in the stored lifted minor telescope. -/
theorem fields_of_lifted_minor (M : Interp.{T}) (σ : Nat → Nat)
    (Fs : List (Expr Nat)) (ρ : Nat → PSet.{T})
    (ys : List PSet.{T}) (g : PSet.{T}) (xs : List PSet.{T}) (b : Expr Nat)
    (hl : xs.length = Fs.length)
    (hg : g ∈ Ed M (den M σ (push ys ρ)
      (policyPi (liftFields ys.length Fs 0) b)))
    (hsp : SpineFacts M g xs) (hne : ¬ Equiv (fapps g xs) pempty) :
    TelFits M σ Fs ρ xs := by
  apply (TelFits_liftFields M σ ys ρ Fs [] xs).mp
  exact fits_of_nonempty M σ b (liftFields ys.length Fs 0) (push ys ρ) g xs
    (hl.trans (liftFields_length' ys.length Fs 0).symm) hg hsp hne

/-! ## Same-P data-field witness -/

open PropEvalSafeIndex (witnessTable witnessFields falseCode trueCode)

noncomputable def identityHead (P : Premises4) (σ : Nat → Nat) : PSet.{4} :=
  piLam (mkM P witnessTable) σ (fun ρ => ρ 0) ρ0
    (.pi (.sort .zero) (.sort .zero))

theorem identity_mem (P : Premises4) (σ : Nat → Nat) :
    identityHead P σ ∈ Ed (mkM P witnessTable)
      (den (mkM P witnessTable) σ ρ0 (.pi (.sort .zero) (.sort .zero))) := by
  apply piLam_mem (mkM P witnessTable) σ (fun _ _ h => h 0) _ ρ0
  intro x hx
  exact hx

theorem identity_application (P : Premises4) (σ : Nat → Nat) :
    Equiv (fapps (identityHead P σ) [falseCode]) falseCode :=
  beta_val (mkM P witnessTable) (fun _ _ h => h) (PropEvalSafeIndex.false_fits P σ).1

theorem actual_spine (P : Premises4) (σ : Nat → Nat) :
    SpineFacts (mkM P witnessTable) (identityHead P σ) [falseCode] :=
  ⟨⟨den (mkM P witnessTable) σ ρ0 (.sort .zero),
    (fun x => den (mkM P witnessTable) σ (vcons x ρ0) (.sort .zero)),
    den_resp (mkM P witnessTable) σ ρ0 (.sort .zero),
    identity_mem P σ, (PropEvalSafeIndex.false_fits P σ).1⟩, True.intro⟩

theorem actual_nonempty (P : Premises4) (σ : Nat → Nat) :
    ¬ Equiv (fapps (identityHead P σ) [falseCode]) pempty :=
  fun he => PropEvalSafeIndex.false_code_not_proof
    ((identity_application P σ).symm.trans he)

/-- The actual data field is recovered by the new producer. -/
theorem produced_fit (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P witnessTable) σ witnessFields ρ0 [falseCode] :=
  fits_of_nonempty (mkM P witnessTable) σ (.sort .zero) witnessFields ρ0
    (identityHead P σ) [falseCode] rfl (identity_mem P σ)
    (actual_spine P σ) (actual_nonempty P σ)

/-- The same data field survives a nonempty inserted prefix. -/
theorem produced_lifted_fit (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P witnessTable) σ witnessFields ρ0 [falseCode] :=
  fields_of_lifted_minor (mkM P witnessTable) σ witnessFields ρ0 [trueCode]
    (identityHead P σ) [falseCode] (.sort .zero) rfl (identity_mem P σ)
    (actual_spine P σ) (actual_nonempty P σ)

def Witness (P : Premises4) : Prop :=
  PropEvalSafeIndex.Witness P ∧
  ∀ σ, identityHead P σ ∈ Ed (mkM P witnessTable)
      (den (mkM P witnessTable) σ ρ0 (.pi (.sort .zero) (.sort .zero))) ∧
    SpineFacts (mkM P witnessTable) (identityHead P σ) [falseCode] ∧
    ¬ Equiv (fapps (identityHead P σ) [falseCode]) pempty ∧
    TelFits (mkM P witnessTable) σ witnessFields ρ0 [falseCode]

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PropEvalSafeIndex.component_witness P, fun σ =>
    ⟨identity_mem P σ, actual_spine P σ, actual_nonempty P σ, produced_lifted_fit P σ⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedPropSpine

#print axioms Rcic.F3.PSet.IndexedPropSpine.fits_of_nonempty
#print axioms Rcic.F3.PSet.IndexedPropSpine.fields_of_lifted_minor
#print axioms Rcic.F3.PSet.IndexedPropSpine.produced_fit
#print axioms Rcic.F3.PSet.IndexedPropSpine.produced_lifted_fit
#print axioms Rcic.F3.PSet.IndexedPropSpine.component_witness
#print axioms Rcic.F3.PSet.IndexedPropSpine.component_nonrefutable
