import rcic.RcicF3RecFieldMaskSupportTyping
import rcic.RcicF3ReaderSubstitution
import rcic.RcicF3KTWTransfer

/-!
# Entering a typed beta closure without Pi injectivity

The application spine carries an actual membership of the current head
in its expected product. The literal lambda's original body derivation
supplies its membership in its annotated product. A nonempty application
forces a nonempty common graph, which determines equality of those two
decoded domains. The captured argument's already-produced value relation
can therefore be transported to the literal annotation.

The two original body assignments retain their separately evaluated
arguments. Only an allowed capture needs value agreement or a local
origin relation; an opaque capture needs neither. No masked Fits, typed
Pi-injectivity, or equality of raw and normalized family frames is used.
This is an internal reader transition, not an extra apex premise.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderCapture
open Rcic.Declarative RawFamily
open RecFieldMask (Marks Value)
open RecFieldMaskSupport (Allowed Agree Context allowCons markCons)
universe u

/-- The exact graph domain of a nonempty common function is unique. This
requires memberships only, not equality of the two whole product types. -/
theorem domains (M : Interp.{u}) (g A A' : PSet.{u})
    (B B' : PSet.{u} → PSet.{u})
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hB' : ∀ x x', Equiv x x' → Equiv (B' x) (B' x'))
    (hg : g ∈ Ed M (piVal M A B)) (hg' : g ∈ Ed M (piVal M A' B'))
    (hne : ¬ Equiv g pempty) : Equiv (Ed M A) (Ed M A') := by
  have h := mem_congr_right (ed_piVal M A B hB) hg
  have h' := mem_congr_right (ed_piVal M A' B' hB') hg'
  cases M.dec (PiProp M A B) with
  | isTrue hp =>
      rw [cond_pos hp] at h
      exact (hne (mem_tv.mp h).2).elim
  | isFalse hp =>
      rw [cond_neg hp] at h
      cases M.dec (PiProp M A' B') with
      | isTrue hp' =>
          rw [cond_pos hp'] at h'
          exact (hne (mem_tv.mp h').2).elim
      | isFalse hp' =>
          rw [cond_neg hp'] at h'
          exact ext fun x =>
            ⟨fun hx => piSet_dom (B := fun a => Ed M (B' a))
              (B' := fun a => Ed M (B a)) (fun a b e => ed_congr M (hB' a b e))
              (fun a b e => ed_congr M (hB a b e)) h' h hx,
             fun hx => piSet_dom (B := fun a => Ed M (B a))
              (B' := fun a => Ed M (B' a)) (fun a b e => ed_congr M (hB a b e))
              (fun a b e => ed_congr M (hB' a b e)) h h' hx⟩

/-- The body typing is the original lambda premise. Its annotated type
is interpreted only in the two original fitting closure environments. -/
theorem beta (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (db : HasTyT E n (.assumption A :: Γ) body B) (hb : LOKt σ 4 K db)
    (marks : Marks) (allowed : Allowed) (ρC ρD η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρD)
    (hctx : Context P μ fd C σ marks allowed Γ ρC ρD η)
    (hag : Agree allowed ρC ρD)
    (AC AD : PSet.{4}) (BC BD : PSet.{4} → PSet.{4})
    (hBC : ∀ x x', Equiv x x' → Equiv (BC x) (BC x'))
    (hBD : ∀ x x', Equiv x x' → Equiv (BD x) (BD x'))
    (hfunC : den (mkM P (table P μ fd C)) σ ρC (.lam A body) ∈
      Ed (mkM P μ) (piVal (mkM P μ) AC BC))
    (hfunD : den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      σ ρD (.lam A body) ∈ Ed (mkM P μ) (piVal (mkM P μ) AD BD))
    (xC xD y : PSet.{4}) (q : Option Nat) (a : Prop)
    (hneC : ¬ Equiv (fapp (den (mkM P (table P μ fd C)) σ ρC (.lam A body)) xC) pempty)
    (hneD : ¬ Equiv (fapp (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      σ ρD (.lam A body)) xD) pempty)
    (hx : a → Equiv xC xD)
    (hv : a → Value (mkM P μ) fd C q (Ed (mkM P μ) AC) (Ed (mkM P μ) AD) xC y) :
    Fits (mkM P (table P μ fd C)) σ (.assumption A :: Γ) (vcons xC ρC) ∧
    Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ
      (.assumption A :: Γ) (vcons xD ρD) ∧
    Agree (allowCons a allowed) (vcons xC ρC) (vcons xD ρD) ∧
    Context P μ fd C σ (markCons q marks) (allowCons a allowed)
      (.assumption A :: Γ) (vcons xC ρC) (vcons xD ρD) (vcons y η) := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  have hc : xC ∈ Ed MC (den MC σ ρC A) := mem_of_fapp_lamVal_ne MC hneC
  have hd : xD ∈ Ed MD (den MD σ ρD A) := mem_of_fapp_lamVal_ne MD hneD
  have hLC : den MC σ ρC (.lam A body) ∈ Ed MC (den MC σ ρC (.pi A B)) := by
    apply lam_mem MC (den_resp MC σ ρC body) (den_resp MC σ ρC B)
    intro x hm
    exact sound_ty (P.good MC rfl) hEC db hb (vcons x ρC) ⟨hρC, hm⟩
  have hLD : den MD σ ρD (.lam A body) ∈ Ed MD (den MD σ ρD (.pi A B)) := by
    apply lam_mem MD (den_resp MD σ ρD body) (den_resp MD σ ρD B)
    intro x hm
    exact sound_ty (P.good MD rfl) hED db hb (vcons x ρD) ⟨hρD, hm⟩
  change den MC σ ρC (.lam A body) ∈ Ed MC
    (piVal MC (den MC σ ρC A) (fun x => den MC σ (vcons x ρC) B)) at hLC
  change den MD σ ρD (.lam A body) ∈ Ed MD
    (piVal MD (den MD σ ρD A) (fun x => den MD σ (vcons x ρD) B)) at hLD
  rw [piVal_dec_eq P (table P μ fd C) μ, ed_mkM P (table P μ fd C) μ] at hLC
  rw [piVal_dec_eq P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) μ,
    ed_mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) μ] at hLD
  have hnC : ¬ Equiv (den MC σ ρC (.lam A body)) pempty :=
    fun he => hneC ((fapp_congr he Equiv.rfl).trans (fapp_pempty xC))
  have hnD : ¬ Equiv (den MD σ ρD (.lam A body)) pempty :=
    fun he => hneD ((fapp_congr he Equiv.rfl).trans (fapp_pempty xD))
  have eC := domains (mkM P μ) (den MC σ ρC (.lam A body)) AC (den MC σ ρC A)
    BC (fun x => den MC σ (vcons x ρC) B) hBC (den_resp MC σ ρC B) hfunC hLC hnC
  have eD := domains (mkM P μ) (den MD σ ρD (.lam A body)) AD (den MD σ ρD A)
    BD (fun x => den MD σ (vcons x ρD) B) hBD (den_resp MD σ ρD B) hfunD hLD hnD
  refine ⟨⟨hρC, hc⟩, ⟨hρD, hd⟩, RecFieldMaskSupport.agree_cons hag hx, ?_⟩
  apply RecFieldMaskSupport.context_capture P μ fd C σ marks allowed Γ ρC ρD η hctx
    (.assumption A) q a xC xD y
  intro ha
  change Value (mkM P μ) fd C q (Ed MC (den MC σ ρC A))
    (Ed MD (den MD σ ρD A)) xC y
  rw [ed_mkM P (table P μ fd C) μ,
    ed_mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) μ]
  exact (hv ha).transport eC eD Equiv.rfl Equiv.rfl

end Rcic.F3.PSet.ReaderCapture
