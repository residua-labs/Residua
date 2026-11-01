import rcic.RcicF3PiNormalize

/-!
# Inhabited normalization from exact transparent-body equations

The beta case needs only the nonempty denotation of the application. The
zeta case is literal substitution. Exact delta equations therefore suffice
without a numerical universe bound, an EnvSound premise, or InstOK.

The companion faithful-table producer must supply BodyEquations from actual
admission; this generic lemma is not a new apex premise. Telescope recursion
uses the given field at every fitting argument, and preserves the complete
normalized syntax. No unbounded reverse-normalization claim is made.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.DeltaNormalize
open Rcic.Declarative
universe u

/-- Literal equations at every successful transparent-body lookup. There is
no numerical bound or arity assumption hidden in this predicate. -/
def BodyEquations (M : Interp.{u}) (E : ResolvedEnv) (σ : Nat → Nat) : Prop :=
  ∀ (r : Nat) (ls : List Level) (b : Expr Nat),
    transparentBody E r ls = some b → ∀ ρ : Nat → PSet.{u},
      Equiv (M.μ r (ls.map (evalTotal σ))) (den M σ ρ b)

/-- Nonempty weak-head denotations normalize using only the literal delta
equations. An ill-typed beta redex with empty denotation is not covered. -/
theorem whnf_of_ne (M : Interp.{u}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : BodyEquations M E σ) (ρ : Nat → PSet.{u}) :
    ∀ (fuel : Nat) (e e' : Expr Nat), whnfFuel E fuel e = some e' →
      ¬ Equiv (den M σ ρ e) pempty →
      Equiv (den M σ ρ e') (den M σ ρ e)
  | 0, _, _, h, _ => by cases h
  | fuel + 1, e, e', h, hne => by
      have he : foldApps (appsSpine e).1 (appsSpine e).2 = e := foldApps_appsSpine e
      cases hs : appsSpine e with
      | mk hd args =>
        rw [hs] at he
        simp only at he
        cases hd with
        | lam A b =>
            cases args with
            | nil =>
                simp only [whnfFuel, hs] at h
                cases h
                exact Equiv.rfl
            | cons a args =>
                simp only [whnfFuel, hs] at h
                have hden : den M σ ρ e = fapps
                    (fapp (lamVal M (den M σ ρ A)
                      (fun x => den M σ (vcons x ρ) b)) (den M σ ρ a))
                    (args.map (den M σ ρ)) := by
                  rw [← he, show foldApps (Expr.lam A b) (a :: args) =
                    foldApps (.app (.lam A b) a) args from rfl, den_foldApps]
                  rfl
                have hne' : ¬ Equiv
                    (fapp (lamVal M (den M σ ρ A)
                      (fun x => den M σ (vcons x ρ) b)) (den M σ ρ a)) pempty := by
                  intro h0
                  apply hne
                  rw [hden]
                  exact (fapps_congr h0 _).trans (fapps_pempty _)
                have hx := mem_of_fapp_lamVal_ne M hne'
                have hβ := beta_val M (A := den M σ ρ A)
                  (b := fun x => den M σ (vcons x ρ) b)
                  (fun x x' hxx => den_congr M σ b
                    (vcons_congr hxx (fun _ => Equiv.rfl))) hx
                have hstep : Equiv
                    (den M σ ρ (foldApps (instantiate0 a b) args)) (den M σ ρ e) := by
                  rw [hden, den_foldApps, den_inst0]
                  exact fapps_congr hβ.symm _
                exact (whnf_of_ne M E σ hδ ρ fuel _ e' h
                  (fun h0 => hne (hstep.symm.trans h0))).trans hstep
        | letE A v b =>
            simp only [whnfFuel, hs] at h
            have hstep : den M σ ρ (foldApps (instantiate0 v b) args) = den M σ ρ e := by
              rw [← he, den_foldApps, den_foldApps, den_inst0]
              rfl
            rw [← hstep] at hne ⊢
            exact whnf_of_ne M E σ hδ ρ fuel _ e' h hne
        | const r ls =>
            cases ht : transparentBody E r ls with
            | none =>
                simp only [whnfFuel, hs, ht] at h
                cases h
                exact Equiv.rfl
            | some body =>
                simp only [whnfFuel, hs, ht] at h
                have hstep : Equiv (den M σ ρ (foldApps body args)) (den M σ ρ e) := by
                  rw [← he, den_foldApps, den_foldApps]
                  exact fapps_congr (hδ r ls body ht ρ).symm _
                exact (whnf_of_ne M E σ hδ ρ fuel _ e' h
                  (fun h0 => hne (hstep.symm.trans h0))).trans hstep
        | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | sort _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | lit _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl

/-- The actual inhabitant supplies every recursive codomain inhabitant.
Thus the exact telescope equation holds at arbitrary universe valuations
whenever the faithful transparent-body equations have been produced. -/
theorem telescope_of_mem (M : Interp.{u}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : BodyEquations M E σ) :
    ∀ (fuel : Nat) (T : Expr Nat) (ds : List (Expr Nat)) (b : Expr Nat)
      (ρ : Nat → PSet.{u}) (x : PSet.{u}),
      piTelescopeFuel E fuel T = some (ds, b) →
      x ∈ Ed M (den M σ ρ T) →
      Equiv (den M σ ρ (policyPi ds b)) (den M σ ρ T)
  | 0, _, _, _, _, _, h, _ => by cases h
  | fuel + 1, T, ds, b, ρ, x, h, hx => by
      cases hw : whnfFuel E fuel T with
      | none => simp only [piTelescopeFuel, hw] at h; cases h
      | some w =>
          have hne : ¬ Equiv (den M σ ρ T) pempty := by
            intro h0
            exact not_mem_pempty
              (mem_congr_right ((ed_congr M h0).trans (ed_pempty M)) hx)
          have he := whnf_of_ne M E σ hδ ρ fuel T w hw hne
          cases w with
          | pi A B =>
              cases ht : piTelescopeFuel E fuel B with
              | none => simp only [piTelescopeFuel, hw, ht] at h; cases h
              | some p =>
                  rcases p with ⟨as, c⟩
                  simp only [piTelescopeFuel, hw, ht] at h
                  cases h
                  have hx' : x ∈ Ed M (piVal M (den M σ ρ A)
                      (fun a => den M σ (vcons a ρ) B)) :=
                    mem_congr_right (ed_congr M he.symm) hx
                  refine Equiv.trans
                    (show Equiv (den M σ ρ (policyPi (A :: as) b))
                      (den M σ ρ (.pi A B)) from ?_) he
                  change Equiv (piVal M (den M σ ρ A)
                    (fun a => den M σ (vcons a ρ) (policyPi as b)))
                    (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) B))
                  apply piVal_congr_on M
                    (B := fun a => den M σ (vcons a ρ) (policyPi as b))
                    (B' := fun a => den M σ (vcons a ρ) B) Equiv.rfl
                    (fun _ _ ha => den_congr M σ (policyPi as b)
                      (vcons_congr (ρ := ρ) (ρ' := ρ) ha (fun _ => Equiv.rfl)))
                    (fun _ _ ha => den_congr M σ B
                      (vcons_congr (ρ := ρ) (ρ' := ρ) ha (fun _ => Equiv.rfl)))
                  intro a ha
                  have hxa : fapp x a ∈ Ed M (den M σ (vcons a ρ) B) := app_mem M
                    (fun _ _ ha => den_congr M σ B
                      (vcons_congr (ρ := ρ) (ρ' := ρ) ha (fun _ => Equiv.rfl))) hx' ha
                  exact telescope_of_mem M E σ hδ fuel B as b (vcons a ρ)
                    (fapp x a) ht hxa
          | bvar _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | sort _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | const _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | app _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | lam _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | letE _ _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | lit _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he

end Rcic.F3.PSet.DeltaNormalize
