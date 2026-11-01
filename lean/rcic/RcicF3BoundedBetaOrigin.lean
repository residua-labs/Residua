import rcic.RcicF3BoundedPiSpine
import rcic.RcicF3Whnf

/-!
# Original bounded body contexts through a converted beta head

The actual application derivation may convert the lambda's function type
and may have further conversions around the application. Inversion retains
the lambda's original annotated domain and its original bounded body
derivation. At a nonempty semantic application, the actual argument belongs
to that annotated domain, so the original body context fits. No syntactic
Pi-conversion inversion is needed.

The two-model theorem produces both original body environments from the
same actual derivation. It records the exact substitution equations and
does not claim that an erased environment fits. Literal dependent domains
inside the original body retain their bounded derivations and their full
terminal expression. This is one normalization step with provenance, not a
typed fuelled reader or an admission-to-domain-mask producer.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedBetaOrigin
open Rcic.Declarative

private theorem lambda_aux (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body : Expr Nat} :
    {e T : Expr Nat} → (d : HasTyT E n Γ e T) → LOKt σ N K d →
      e = .lam A body →
      ∃ (u : Level) (B : Expr Nat)
        (dA : HasTyT E n Γ A (.sort u))
        (db : HasTyT E n (.assumption A :: Γ) body B),
          LOKt σ N K dA ∧ LOKt σ N K db
  | _, _, .lam _ A0 u body0 B dA db, hd, he => by
      injection he with hA hb
      subst hA
      subst hb
      exact ⟨u, B, dA, db, hd.1, hd.2⟩
  | _, _, .conv _ _ _ _ _ d _, hd, he => lambda_aux σ N K d hd.1 he
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .app _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

/-- Both extracted derivations are actual premises of the original
lambda, even when its type differs from the application's expected Pi. -/
theorem derivations (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg T : Expr Nat}
    (d : HasTyT E n Γ (.app (.lam A body) arg) T) (hd : LOKt σ N K d) :
    ∃ (u : Level) (B : Expr Nat)
      (dA : HasTyT E n Γ A (.sort u))
      (db : HasTyT E n (.assumption A :: Γ) body B),
        LOKt σ N K dA ∧ LOKt σ N K db := by
  obtain ⟨_A, _B, df, hf⟩ := lok_app_inv_aux σ N K d hd rfl
  exact lambda_aux σ N K df hf rfl

universe v

/-- The exact body environment is retained as data in the statement.
Its fit is an original-context fact; no erased prefix occurs. -/
structure BodyAt (M : Interp.{v}) (σ : Nat → Nat) (Γ : LCtx)
    (ρ : Nat → PSet.{v}) (A body arg B : Expr Nat) : Prop where
  argument : den M σ ρ arg ∈ Ed M (den M σ ρ A)
  fits : Fits M σ (.assumption A :: Γ) (vcons (den M σ ρ arg) ρ)
  substitute : den M σ ρ (instantiate0 arg body) =
    den M σ (vcons (den M σ ρ arg) ρ) body
  beta : Equiv (den M σ ρ (.app (.lam A body) arg))
    (den M σ (vcons (den M σ ρ arg) ρ) body)
  typed : den M σ (vcons (den M σ ρ arg) ρ) body ∈
    Ed M (den M σ (vcons (den M σ ρ arg) ρ) B)

/-- Nonemptiness supplies the lambda's annotated-domain membership;
the original body derivation supplies its soundness at that same value. -/
theorem body_at (M : Interp.{v}) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Lv : Nat → PSet.{v} → Prop} (hG : Good M N Lv)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat}
    (hE : EnvSound M σ K E n)
    (db : HasTyT E n (.assumption A :: Γ) body B) (hb : LOKt σ N K db)
    (ρ : Nat → PSet.{v}) (hρ : Fits M σ Γ ρ)
    (hne : ¬ Equiv (den M σ ρ (.app (.lam A body) arg)) pempty) :
    BodyAt M σ Γ ρ A body arg B := by
  have hx : den M σ ρ arg ∈ Ed M (den M σ ρ A) :=
    mem_of_fapp_lamVal_ne M hne
  have hf : Fits M σ (.assumption A :: Γ) (vcons (den M σ ρ arg) ρ) := ⟨hρ, hx⟩
  exact ⟨hx, hf, den_inst0 M σ ρ arg body,
    beta_val M (den_resp M σ ρ body) hx,
    sound_ty hG hE db hb _ hf⟩

/-- A single actual bounded type derivation supplies the same original
body derivation and both original fitting body environments. The two
tables and local environments may differ. Their full valuation is kept. -/
theorem paired_of_type (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg : Expr Nat} {l : Level}
    (d : HasTyT E n Γ (.app (.lam A body) arg) (.sort l)) (hd : LOKt σ 4 K d)
    (hM : EnvSound (mkM P μ) σ K E n) (hN : EnvSound (mkM P ν) σ K E n)
    (ρ η : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) (hη : Fits (mkM P ν) σ Γ η) :
    ∃ (u : Level) (B : Expr Nat)
      (dA : HasTyT E n Γ A (.sort u))
      (db : HasTyT E n (.assumption A :: Γ) body B),
        LOKt σ 4 K dA ∧ LOKt σ 4 K db ∧
        BodyAt (mkM P μ) σ Γ ρ A body arg B ∧
        BodyAt (mkM P ν) σ Γ η A body arg B := by
  obtain ⟨u, B, dA, db, hA, hb⟩ := derivations σ 4 K d hd
  have hneM := den_type_ne_pempty (mkM P μ) σ
    (fun k => pempty_not_mem_U4 P k) ρ (sound_ty (P.good _ rfl) hM d hd ρ hρ)
  have hneN := den_type_ne_pempty (mkM P ν) σ
    (fun k => pempty_not_mem_U4 P k) η (sound_ty (P.good _ rfl) hN d hd η hη)
  exact ⟨u, B, dA, db, hA, hb,
    body_at (mkM P μ) σ 4 K (P.good _ rfl) hM db hb ρ hρ hneM,
    body_at (mkM P ν) σ 4 K (P.good _ rfl) hN db hb η hη hneN⟩

/-- Literal Pi-domain inversion does not need the body's requested type
to be a sort syntactically. The terminal keeps its actual extracted type. -/
theorem literal_telescope (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (ds : List (Expr Nat)) (terminal : Expr Nat)
    {Γ : LCtx} {T : Expr Nat}
    (d : HasTyT E n Γ (policyPi ds terminal) T) (hd : LOKt σ N K d) :
    BoundedPiSpine.Domains (E := E) (n := n) σ N K Γ ds ∧
      ∃ (B : Expr Nat) (db : HasTyT E n (BoundedPiSpine.context Γ ds) terminal B),
        LOKt σ N K db := by
  induction ds generalizing Γ T with
  | nil => exact ⟨True.intro, T, d, hd⟩
  | cons A ds ih =>
      obtain ⟨u, v, dA, dB, _c, hu, _hv, hA, hB, _hc⟩ :=
        BoundedPiSpine.pi_parts σ N K d hd
      obtain ⟨hds, hb⟩ := ih dB hB
      exact ⟨⟨u, dA, hu, hA, hds⟩, hb⟩

/-- Composition retains the dependent body domains and the full terminal
in the original lambda context, together with both actual substitution
environments. There is no typing assertion in a dummy context. -/
theorem paired_spine (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A arg : Expr Nat} {l : Level}
    (ds : List (Expr Nat)) (terminal : Expr Nat)
    (d : HasTyT E n Γ (.app (.lam A (policyPi ds terminal)) arg) (.sort l))
    (hd : LOKt σ 4 K d)
    (hM : EnvSound (mkM P μ) σ K E n) (hN : EnvSound (mkM P ν) σ K E n)
    (ρ η : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) (hη : Fits (mkM P ν) σ Γ η) :
    (∃ B, BodyAt (mkM P μ) σ Γ ρ A (policyPi ds terminal) arg B ∧
      BodyAt (mkM P ν) σ Γ η A (policyPi ds terminal) arg B) ∧
    BoundedPiSpine.Domains (E := E) (n := n) σ 4 K (.assumption A :: Γ) ds ∧
      ∃ (B : Expr Nat)
        (db : HasTyT E n (BoundedPiSpine.context (.assumption A :: Γ) ds) terminal B),
          LOKt σ 4 K db := by
  obtain ⟨u, B, _dA, db, _hA, hb, hC, hD⟩ :=
    paired_of_type P μ ν σ K d hd hM hN ρ η hρ hη
  exact ⟨⟨B, hC, hD⟩, literal_telescope σ 4 K ds terminal db hb⟩

end Rcic.F3.PSet.BoundedBetaOrigin
