import rcic.RcicF3Fund
import rcic.RcicF3Data
import rcic.RcicF3PiRawIH
import rcic.RcicIARecUnique

/-!
# Typed comparison of recursive IHs

Typed eta gives extensionality for proof and data functions. The telescope
comparison quantifies over actual fitting tuples. Successful reads at
different fuels are aligned by the existing monotonicity theorems.
This supplies comparison components, not general Eval functionality.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet
open Rcic.Declarative
universe u

theorem typed_pi_ext (M : Interp.{u}) {A f g : PSet.{u}} {B : PSet.{u} → PSet.{u}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hf : f ∈ Ed M (piVal M A B)) (hg : g ∈ Ed M (piVal M A B))
    (hfg : ∀ x, x ∈ Ed M A → Equiv (fapp f x) (fapp g x)) : Equiv f g :=
  (eta_val M hB hf).symm.trans
    ((lamVal_congr_on M (Equiv.refl A)
      (fun _ _ h => fapp_congr (Equiv.refl f) h) hfg).trans (eta_val M hB hg))

/-- Typed functions are determined by their results on fitting dependent tuples. -/
theorem typed_tel_ext (M : Interp.{u}) (σ : Nat → Nat)
    (ds : List (Expr Nat)) (b : Expr Nat) (ρ : Nat → PSet.{u}) {f g : PSet.{u}}
    (hf : f ∈ Ed M (den M σ ρ (policyPi ds b)))
    (hg : g ∈ Ed M (den M σ ρ (policyPi ds b)))
    (hfg : ∀ xs, TelFits M σ ds ρ xs → Equiv (fapps f xs) (fapps g xs)) : Equiv f g := by
  induction ds generalizing ρ f g with
  | nil => exact hfg [] True.intro
  | cons A ds ih =>
    have hB := den_resp M σ ρ (policyPi ds b)
    apply typed_pi_ext M hB hf hg
    intro x hx
    apply ih (ρ := vcons x ρ) (f := fapp f x) (g := fapp g x)
    · exact app_mem M hB hf hx
    · exact app_mem M hB hg hx
    · intro xs hxs
      exact hfg (x :: xs) ⟨hx, hxs⟩

namespace PiTypedExt
theorem read_unique (E : ResolvedEnv) {fuel fuel' : Nat} {A : Expr Nat}
    {ds ds' : List (Expr Nat)} {b b' : Expr Nat}
    (h : piTelescopeFuel E fuel A = some (ds, b))
    (h' : piTelescopeFuel E fuel' A = some (ds', b')) : ds = ds' ∧ b = b' := by
  have he := Option.some.inj
    ((piTelescopeFuel_mono E (Nat.le_max_left fuel fuel') h).symm.trans
      (piTelescopeFuel_mono E (Nat.le_max_right fuel fuel') h'))
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem builder_unique (E : ResolvedEnv) {fuel fuel' np inner : Nat}
    {A Mx ih ih' : Expr Nat}
    (h : funIHType E fuel np A Mx inner = some ih)
    (h' : funIHType E fuel' np A Mx inner = some ih') : ih = ih' :=
  Option.some.inj ((funIHType_mono E (Nat.le_max_left fuel fuel') h).symm.trans
    (funIHType_mono E (Nat.le_max_right fuel fuel') h'))

/-- Both actual IH memberships and all fitting branch comparisons are retained. -/
theorem builder_ext (M : Interp.{u}) (σ : Nat → Nat) (E : ResolvedEnv)
    (fuel np : Nat) (A Mx : Expr Nat) (ds args : List (Expr Nat)) (f : Nat) (ls : List Level)
    (hread : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const f ls) args))
    (ih : Expr Nat) (hih : funIHType E fuel np A Mx ds.length = some ih)
    (ρ : Nat → PSet.{u}) {x y : PSet.{u}}
    (hx : x ∈ Ed M (den M σ ρ ih)) (hy : y ∈ Ed M (den M σ ρ ih))
    (hxy : ∀ zs, TelFits M σ ds ρ zs → Equiv (fapps x zs) (fapps y zs)) : Equiv x y := by
  have he := Option.some.inj
    ((PiRawIH.funIHType_eq E fuel np A Mx ds args f ls hread).symm.trans hih)
  rw [← he] at hx hy
  exact typed_tel_ext M σ ds _ ρ hx hy hxy
end PiTypedExt

end Rcic.F3.PSet
