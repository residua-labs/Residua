import rcic.RcicF3DeltaNormalize

/-!
# Actual reader traces without a beta contraction

The certificate records the original reader's fuel, source, transparent
lookups, and output. Delta and zeta preserve denotation at every local
environment. Pi descent preserves the whole dependent telescope. Therefore
these traces normalize in both directions without an original-context fit,
without a bounded mirror conversion, and without a source inhabitant.

The excluded beta edge is substantive: its argument need not belong to its
annotation when the local environment does not fit the original context.
No claim about unrestricted reader traces is made. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ReaderNoBeta
open Rcic.Declarative
universe u

/-- Exactly the heads at which the actual weak-head reader stops. -/
def Stops (E : ResolvedEnv) (e : Expr Nat) : Prop :=
  match appsSpine e with
  | (.lam _ _, _ :: _) => False
  | (.letE _ _ _, _) => False
  | (.const r ls, _) => transparentBody E r ls = none
  | _ => True

theorem Stops.read {E : ResolvedEnv} {e : Expr Nat}
    (h : Stops E e) (fuel : Nat) : whnfFuel E (fuel + 1) e = some e := by
  cases hs : appsSpine e with
  | mk hd args =>
      cases hd with
      | lam A b =>
          cases args with
          | nil => simp only [whnfFuel, hs]
          | cons a args =>
              have hf : False := by simpa only [Stops, hs] using h
              exact hf.elim
      | letE A v b =>
          have hf : False := by simpa only [Stops, hs] using h
          exact hf.elim
      | const r ls =>
          have hb : transparentBody E r ls = none := by
            simpa only [Stops, hs] using h
          simp only [whnfFuel, hs, hb]
      | bvar i => simp only [whnfFuel, hs]
      | sort l => simp only [whnfFuel, hs]
      | app f a => simp only [whnfFuel, hs]
      | pi A B => simp only [whnfFuel, hs]
      | lit n => simp only [whnfFuel, hs]

/-- A successful actual head trace containing only delta and zeta steps.
The shape equation refers to the whole original source at each step. -/
inductive Head (E : ResolvedEnv) : Nat → Expr Nat → Expr Nat → Prop where
  | stop (fuel : Nat) (e : Expr Nat) (h : Stops E e) :
      Head E (fuel + 1) e e
  | zeta {fuel : Nat} {e A v b w : Expr Nat} {args : List (Expr Nat)}
      (shape : appsSpine e = (.letE A v b, args))
      (next : Head E fuel (foldApps (instantiate0 v b) args) w) :
      Head E (fuel + 1) e w
  | delta {fuel r : Nat} {ls : List Level} {e body w : Expr Nat}
      {args : List (Expr Nat)}
      (shape : appsSpine e = (.const r ls, args))
      (lookup : transparentBody E r ls = some body)
      (next : Head E fuel (foldApps body args) w) :
      Head E (fuel + 1) e w

/-- The certificate is a refinement of the existing reader, not a second
normalization relation with different outputs or fuel. -/
theorem Head.read {E : ResolvedEnv} {fuel : Nat} {e w : Expr Nat}
    (h : Head E fuel e w) : whnfFuel E fuel e = some w := by
  induction h with
  | stop fuel e hs => exact hs.read fuel
  | zeta hs _ ih => simpa only [whnfFuel, hs] using ih
  | delta hs hb _ ih => simpa only [whnfFuel, hs, hb] using ih

/-- Faithful transparent-body equations suffice; no local membership
assumption is needed for either permitted contraction. -/
theorem Head.den (M : Interp.{u}) (σ : Nat → Nat)
    {E : ResolvedEnv} (hδ : DeltaNormalize.BodyEquations M E σ)
    {fuel : Nat} {e w : Expr Nat} (h : Head E fuel e w)
    (ρ : Nat → PSet.{u}) :
    Equiv (Rcic.F3.PSet.den M σ ρ w) (Rcic.F3.PSet.den M σ ρ e) := by
  induction h with
  | stop => exact Equiv.rfl
  | @zeta fuel e A v b w args hs _ ih =>
      have he := foldApps_appsSpine e
      rw [hs] at he
      simp only at he
      have hstep : Rcic.F3.PSet.den M σ ρ (foldApps (instantiate0 v b) args) =
          Rcic.F3.PSet.den M σ ρ e := by
        rw [← he, den_foldApps, den_foldApps, den_inst0]
        rfl
      rw [hstep] at ih
      exact ih
  | @delta fuel r ls e body w args hs hb _ ih =>
      have he := foldApps_appsSpine e
      rw [hs] at he
      simp only at he
      have hstep : Equiv (Rcic.F3.PSet.den M σ ρ (foldApps body args))
          (Rcic.F3.PSet.den M σ ρ e) := by
        rw [← he, den_foldApps, den_foldApps]
        exact fapps_congr (hδ r ls body hb ρ).symm _
      exact ih.trans hstep

/-- The same fuelled head trace is retained at every Pi codomain. Domain
expressions and the complete terminal expression are kept literally. -/
inductive Telescope (E : ResolvedEnv) :
    Nat → Expr Nat → List (Expr Nat) → Expr Nat → Prop where
  | leaf {fuel : Nat} {e b : Expr Nat}
      (head : Head E fuel e b)
      (notPi : ∀ A B, b ≠ .pi A B) : Telescope E (fuel + 1) e [] b
  | pi {fuel : Nat} {e A B b : Expr Nat} {ds : List (Expr Nat)}
      (head : Head E fuel e (.pi A B))
      (tail : Telescope E fuel B ds b) : Telescope E (fuel + 1) e (A :: ds) b

theorem Telescope.read {E : ResolvedEnv} {fuel : Nat} {e b : Expr Nat}
    {ds : List (Expr Nat)} (h : Telescope E fuel e ds b) :
    piTelescopeFuel E fuel e = some (ds, b) := by
  induction h with
  | @leaf fuel e b hh hn =>
      have hw := hh.read
      cases b with
      | pi A B => exact (hn A B rfl).elim
      | bvar i => simp only [piTelescopeFuel, hw]
      | sort l => simp only [piTelescopeFuel, hw]
      | const r ls => simp only [piTelescopeFuel, hw]
      | app f a => simp only [piTelescopeFuel, hw]
      | lam A b => simp only [piTelescopeFuel, hw]
      | letE A v b => simp only [piTelescopeFuel, hw]
      | lit n => simp only [piTelescopeFuel, hw]
  | pi hh _ ih => simp only [piTelescopeFuel, hh.read, ih]

/-- Bidirectional normalization of the certified original telescope at
arbitrary local values, including when its type has no inhabitant. -/
theorem Telescope.den (M : Interp.{u}) (σ : Nat → Nat)
    {E : ResolvedEnv} (hδ : DeltaNormalize.BodyEquations M E σ)
    {fuel : Nat} {e b : Expr Nat} {ds : List (Expr Nat)}
    (h : Telescope E fuel e ds b) (ρ : Nat → PSet.{u}) :
    Equiv (Rcic.F3.PSet.den M σ ρ (policyPi ds b))
      (Rcic.F3.PSet.den M σ ρ e) := by
  induction h generalizing ρ with
  | leaf hh _ => exact hh.den M σ hδ ρ
  | @pi fuel e A B b ds hh _ ih =>
      refine Equiv.trans (show Equiv
        (Rcic.F3.PSet.den M σ ρ (policyPi (A :: ds) b))
        (Rcic.F3.PSet.den M σ ρ (Expr.pi A B)) from ?_) (hh.den M σ hδ ρ)
      change Equiv (piVal M (Rcic.F3.PSet.den M σ ρ A)
        (fun x => Rcic.F3.PSet.den M σ (vcons x ρ) (policyPi ds b)))
        (piVal M (Rcic.F3.PSet.den M σ ρ A)
          (fun x => Rcic.F3.PSet.den M σ (vcons x ρ) B))
      apply piVal_congr_on M
        (B := fun x => Rcic.F3.PSet.den M σ (vcons x ρ) (policyPi ds b))
        (B' := fun x => Rcic.F3.PSet.den M σ (vcons x ρ) B) Equiv.rfl
        (fun _ _ hx => den_congr M σ (policyPi ds b)
          (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl)))
        (fun _ _ hx => den_congr M σ B
          (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl)))
      intro x _hx
      exact ih (vcons x ρ)

end Rcic.F3.PSet.ReaderNoBeta

#print axioms Rcic.F3.PSet.ReaderNoBeta.Head.read
#print axioms Rcic.F3.PSet.ReaderNoBeta.Head.den
#print axioms Rcic.F3.PSet.ReaderNoBeta.Telescope.read
#print axioms Rcic.F3.PSet.ReaderNoBeta.Telescope.den
