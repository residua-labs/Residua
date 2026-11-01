import rcic.RcicF3BoundedBVar
import rcic.RcicF3PropIota

/-!
# Bounded derivations along a literal dependent Pi spine

An actual typing of `policyPi ds body` produces bounded typings of every
domain and of the terminal body in the exact extended local context.
Conversion rules around the Pi introduction are traversed, and their
actual bounded type-conversion chain is retained by `pi_parts`.

At a terminal application, `variable_argument` extracts the derivation of
an actual argument and the bounded lookup-to-expected-type chain. The
semantic composition extends an original fitting context with an actual
fitting dependent tuple; it never evaluates at erased dummy binders.

This is the direct-syntax subcase of the missing normalized-spine theorem.
It does not turn a `piTelescopeFuel` equation into a typed reduct, remove a
local binder, identify an application's expected domain with the declared
family domain, or prove fresh-family head separation. No piRow,
SortUnique, parameter-mirror assumption, or new check is introduced.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedPiSpine
open Rcic.Declarative

variable {E : ResolvedEnv} {n : Nat}

/-- Extend by the actual outer-to-inner domains; all earlier local binders
remain present. -/
def context : LCtx → List (Expr Nat) → LCtx
  | Γ, [] => Γ
  | Γ, A :: ds => context (.assumption A :: Γ) ds

/-- The levels and derivations are those encountered at Pi introductions;
no uniqueness of the sort originally requested is inferred. -/
def Domains (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    LCtx → List (Expr Nat) → Prop
  | _, [] => True
  | Γ, A :: ds => ∃ (u : Level) (d : HasTyT E n Γ A (.sort u)),
      evalTotal σ u ≤ N ∧ LOKt σ N K d ∧
        Domains σ N K (.assumption A :: Γ) ds

private theorem pi_aux (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A B : Expr Nat} :
    {e T : Expr Nat} → (d : HasTyT E n Γ e T) → LOKt σ N K d →
      e = .pi A B →
      ∃ (u v : Level) (dA : HasTyT E n Γ A (.sort u))
        (dB : HasTyT E n (.assumption A :: Γ) B (.sort v))
        (c : TyConvT E n Γ (.sort (.imax u v)) T),
        evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧
          LOKt σ N K dA ∧ LOKt σ N K dB ∧
            BoundedBVar.Bounded σ N K c
  | _, _, .pi _ _ u _ v dA dB, hd, he => by
      injection he with hA hB
      subst hA
      subst hB
      refine ⟨u, v, dA, dB, .refl Γ _, hd.1, hd.2.1,
        hd.2.2.1, hd.2.2.2, ?_⟩
      simpa only [BoundedBVar.Bounded] using True.intro
  | _, _, .conv _ _ S T v d c, hd, he => by
      obtain ⟨u, w, dA, dB, q, hu, hw, hA, hB, hq⟩ :=
        pi_aux σ N K d hd.1 he
      refine ⟨u, w, dA, dB,
        .trans Γ (.sort (.imax u w)) S T q (.of Γ S T v c),
        hu, hw, hA, hB, ?_⟩
      simpa only [BoundedBVar.Bounded] using And.intro hq hd.2
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .app _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

/-- Pi introduction inversion, including every actual outer conversion
and the original bound on each extracted premise. -/
theorem pi_parts (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A B T : Expr Nat}
    (d : HasTyT E n Γ (.pi A B) T) (hd : LOKt σ N K d) :
    ∃ (u v : Level) (dA : HasTyT E n Γ A (.sort u))
      (dB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (c : TyConvT E n Γ (.sort (.imax u v)) T),
      evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧
        LOKt σ N K dA ∧ LOKt σ N K dB ∧
          BoundedBVar.Bounded σ N K c :=
  pi_aux σ N K d hd rfl

/-- All domains and the terminal expression are typed in their literal
contexts at the same level/constant bound, at arbitrary telescope depth. -/
theorem telescope (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ds : List (Expr Nat)) (body : Expr Nat) {Γ : LCtx} {l : Level}
    (d : HasTyT E n Γ (policyPi ds body) (.sort l)) (hd : LOKt σ N K d) :
    Domains (E := E) (n := n) σ N K Γ ds ∧
      ∃ (v : Level) (db : HasTyT E n (context Γ ds) body (.sort v)),
        LOKt σ N K db := by
  induction ds generalizing Γ l with
  | nil => exact ⟨True.intro, l, d, hd⟩
  | cons A ds ih =>
      obtain ⟨u, v, dA, dB, _c, hu, _hv, hA, hB, _hc⟩ :=
        pi_parts σ N K d hd
      obtain ⟨hds, hb⟩ := ih dB hB
      exact ⟨⟨u, dA, hu, hA, hds⟩, hb⟩

/-- The produced domain derivations extend a well-formed original context.
This constructs no typing in a shortened or erased context. -/
theorem context_wf (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} (ds : List (Expr Nat))
    (hds : Domains (E := E) (n := n) σ N K Γ ds)
    (hΓ : CtxWfT E n Γ) : Nonempty (CtxWfT E n (context Γ ds)) := by
  induction ds generalizing Γ with
  | nil => exact ⟨hΓ⟩
  | cons A ds ih =>
      obtain ⟨u, dA, _hu, _hA, ht⟩ := hds
      exact ih ht (.assumption Γ A u hΓ dA)

/-- Original fitting values plus a fitting dependent tuple fit the exact
context in which the terminal derivation was produced. -/
theorem context_fits (M : Interp.{4}) (σ : Nat → Nat)
    {Γ : LCtx} (ds : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (xs : List PSet.{4}) (hρ : Fits M σ Γ ρ)
    (hxs : TelFits M σ ds ρ xs) :
    Fits M σ (context Γ ds) (push xs ρ) := by
  induction ds generalizing Γ ρ xs with
  | nil =>
      cases xs with
      | nil => exact hρ
      | cons x xs => cases hxs
  | cons A ds ih =>
      cases xs with
      | nil => cases hxs
      | cons x xs =>
          exact ih (vcons x ρ) xs ⟨hρ, hxs.1⟩ hxs.2

private theorem app_aux (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {f a : Expr Nat} :
    {e T : Expr Nat} → (d : HasTyT E n Γ e T) → LOKt σ N K d →
      e = .app f a → ∃ (A B : Expr Nat)
        (df : HasTyT E n Γ f (.pi A B)) (da : HasTyT E n Γ a A),
        LOKt σ N K df ∧ LOKt σ N K da
  | _, _, .app _ _ _ A B df da, hd, he => by
      injection he with hf ha
      subst hf
      subst ha
      exact ⟨A, B, df, da, hd.1, hd.2⟩
  | _, _, .conv _ _ _ _ _ d _, hd, he => app_aux σ N K d hd.1 he
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

/-- Every actual argument of a bounded application spine has its actual
bounded application-rule derivation. Neither indices nor parameters are
dropped from the argument list. -/
theorem argument (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} (args : List (Expr Nat)) (head : Expr Nat) {T : Expr Nat}
    (d : HasTyT E n Γ (foldApps head args) T) (hd : LOKt σ N K d)
    (a : Expr Nat) (ha : a ∈ args) :
    ∃ (A : Expr Nat) (da : HasTyT E n Γ a A), LOKt σ N K da := by
  induction args generalizing head with
  | nil => exact (List.not_mem_nil a ha).elim
  | cons b args ih =>
      rcases List.mem_cons.mp ha with hab | ha
      · subst b
        obtain ⟨S, dh, hh⟩ := lok_head σ N K args (.app head a) d hd
        obtain ⟨A, _B, _df, da, _hf, hda⟩ := app_aux σ N K dh hh rfl
        exact ⟨A, da, hda⟩
      · exact ih (.app head b) d hd ha

/-- A variable occurring among the complete terminal arguments receives a
bounded lookup-to-expected-type chain in the exact telescope context.
The expected type is the one from the actual application derivation; no
unproved alignment with a declaration's telescope is asserted. -/
theorem variable_argument (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ds args : List (Expr Nat)) (head : Expr Nat) {Γ : LCtx} {l : Level}
    (d : HasTyT E n Γ (policyPi ds (foldApps head args)) (.sort l))
    (hd : LOKt σ N K d) (k : Nat) (hk : .bvar k ∈ args) :
    ∃ (A T : Expr Nat), lookupType (context Γ ds) k = some A ∧
      (∃ da : HasTyT E n (context Γ ds) (.bvar k) T, LOKt σ N K da) ∧
      ∃ c : TyConvT E n (context Γ ds) A T, BoundedBVar.Bounded σ N K c := by
  obtain ⟨_hds, v, db, hb⟩ := telescope σ N K ds (foldApps head args) d hd
  obtain ⟨T, da, ha⟩ := argument σ N K args head db hb (.bvar k) hk
  obtain ⟨A, hlook, c, hc⟩ := BoundedBVar.extract σ N K da ha
  exact ⟨A, T, hlook, ⟨da, ha⟩, c, hc⟩

/-- Extraction, original-context extension and bounded conversion
soundness compose. A fitting tuple is used at its actual dependent
domains; no choice of a fitting dummy completion is needed. -/
theorem variable_argument_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    (hE : EnvSound (mkM P μ) σ K E n)
    (ds args : List (Expr Nat)) (head : Expr Nat) {Γ : LCtx} {l : Level}
    (d : HasTyT E n Γ (policyPi ds (foldApps head args)) (.sort l))
    (hd : LOKt σ 4 K d) (k : Nat) (hk : .bvar k ∈ args)
    (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hρ : Fits (mkM P μ) σ Γ ρ) (hxs : TelFits (mkM P μ) σ ds ρ xs) :
    ∃ (A T : Expr Nat), lookupType (context Γ ds) k = some A ∧
      (∃ c : TyConvT E n (context Γ ds) A T, BoundedBVar.Bounded σ 4 K c) ∧
      Equiv (den (mkM P μ) σ (push xs ρ) A)
        (den (mkM P μ) σ (push xs ρ) T) := by
  obtain ⟨A, T, hlook, _ha, c, hc⟩ := variable_argument σ 4 K ds args head d hd k hk
  exact ⟨A, T, hlook, ⟨c, hc⟩,
    BoundedBVar.chain_sound P μ σ K hE (push xs ρ)
      (context_fits (mkM P μ) σ ds ρ xs hρ hxs) c hc⟩

end Rcic.F3.PSet.BoundedPiSpine
