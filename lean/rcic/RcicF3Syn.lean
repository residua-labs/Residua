import rcic.RcicF3Rec

/-!
# F3 S5a-6: syntax of the recursor's telescope, read semantically

Generic lemmas about the admitted syntax (`lift` over telescopes and
spines, `familyIdx`, `liftFields`) and their denotations at environments
built by `push`; and `minorFromTelescope_nonrec`: for a constructor whose
fields are all non-recursive, the derived minor type is the telescope of the
(lifted) fields ending in the motive applied to the result indices and the
constructor's application, with the denotation of that end computed.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

theorem lift_policyPi (s : Nat) : (Ds : List (Expr Nat)) → (c : Nat) → (b : Expr Nat) →
    Rcic.Declarative.lift c s (policyPi Ds b) = policyPi (liftFields s Ds c) (Rcic.Declarative.lift (c + Ds.length) s b)
  | [], c, b => by simp [policyPi, liftFields]
  | A :: Ds, c, b => by
      show Expr.pi _ (Rcic.Declarative.lift (c + 1) s (policyPi Ds b)) = Expr.pi _ _
      rw [lift_policyPi s Ds (c + 1) b]
      simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem lift_foldApps (c s : Nat) : (f : Expr Nat) → (as : List (Expr Nat)) →
    Rcic.Declarative.lift c s (foldApps f as) = foldApps (Rcic.Declarative.lift c s f) (as.map (Rcic.Declarative.lift c s))
  | _, [] => rfl
  | f, a :: as => lift_foldApps c s (.app f a) as

theorem appsSpine_foldApps : (f : Expr Nat) → (as : List (Expr Nat)) →
    appsSpine (foldApps f as) = ((appsSpine f).1, (appsSpine f).2 ++ as)
  | f, [] => by simp [foldApps]
  | f, a :: as => by
      rw [show foldApps f (a :: as) = foldApps (.app f a) as from rfl, appsSpine_foldApps (.app f a) as]
      simp [appsSpine]

theorem familyIdx_foldApps_const (np r : Nat) (ls : List Level) (as : List (Expr Nat)) :
    familyIdx np (foldApps (.const r ls) as) = as.drop np := by
  simp [familyIdx, appsSpine_foldApps, appsSpine]

theorem policyPi_append : (Ds Ds' : List (Expr Nat)) → (b : Expr Nat) →
    policyPi (Ds ++ Ds') b = policyPi Ds (policyPi Ds' b)
  | [], _, _ => rfl
  | A :: Ds, Ds', b => by
      show Expr.pi A (policyPi (Ds ++ Ds') b) = Expr.pi A (policyPi Ds (policyPi Ds' b))
      rw [policyPi_append Ds Ds' b]

theorem liftρ_push (xs ys : List PSet.{T}) (R : Nat → PSet.{T}) (i : Nat) :
    liftρ xs.length ys.length (push xs (push ys R)) i = push xs R i := by
  unfold liftρ
  by_cases hi : i < xs.length
  · rw [if_pos hi, push_lt _ _ _ hi, push_lt _ _ _ hi]
  · rw [if_neg hi]
    obtain ⟨d, rfl⟩ : ∃ d, i = d + xs.length := ⟨i - xs.length, by omega⟩
    rw [show d + xs.length + ys.length = (d + ys.length) + xs.length by omega, push_ge, push_ge, push_ge]

theorem den_lift_push (M : Interp.{T}) (σ : Nat → Nat) (xs ys : List PSet.{T}) (R : Nat → PSet.{T})
    (e : Expr Nat) :
    den M σ (push xs (push ys R)) (Rcic.Declarative.lift xs.length ys.length e) = den M σ (push xs R) e := by
  rw [den_lift]
  congr 1
  exact funext (liftρ_push xs ys R)

theorem den_lift0_push (M : Interp.{T}) (σ : Nat → Nat) (ys : List PSet.{T}) (R : Nat → PSet.{T})
    (e : Expr Nat) : den M σ (push ys R) (Rcic.Declarative.lift 0 ys.length e) = den M σ R e := by
  have := den_lift_push M σ [] ys R e
  simpa [push] using this

/-- Fitting lifted fields is fitting the fields. -/
theorem TelFits_liftFields (M : Interp.{T}) (σ : Nat → Nat) (ys : List PSet.{T}) (R : Nat → PSet.{T}) :
    (Ds : List (Expr Nat)) → (zs : List PSet.{T}) → (xs : List PSet.{T}) →
    (TelFits M σ (liftFields ys.length Ds zs.length) (push zs (push ys R)) xs ↔
      TelFits M σ Ds (push zs R) xs)
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | A :: Ds, zs, x :: xs => by
      show (x ∈ Ed M (den M σ (push zs (push ys R)) (Rcic.Declarative.lift zs.length ys.length A)) ∧
          TelFits M σ (liftFields ys.length Ds (zs.length + 1)) (vcons x (push zs (push ys R))) xs) ↔
        (x ∈ Ed M (den M σ (push zs R) A) ∧ TelFits M σ Ds (vcons x (push zs R)) xs)
      rw [den_lift_push]
      have h1 : vcons x (push zs (push ys R)) = push (zs ++ [x]) (push ys R) := by rw [push_append]; rfl
      have h2 : vcons x (push zs R) = push (zs ++ [x]) R := by rw [push_append]; rfl
      have hl : zs.length + 1 = (zs ++ [x]).length := by simp
      rw [h1, h2, hl, TelFits_liftFields M σ ys R Ds (zs ++ [x]) xs]

/-- The accumulated constructor application after `n` fields. -/
def accAfter : Nat → Expr Nat → Expr Nat
  | 0, acc => acc
  | n + 1, acc => accAfter n (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0))

/-- The motive variable after `n` fields. -/
def liftIter : Nat → Expr Nat → Expr Nat
  | 0, e => e
  | n + 1, e => liftIter n (Rcic.Declarative.lift 0 1 e)

theorem den_liftIter (M : Interp.{T}) (σ : Nat → Nat) : (xs : List PSet.{T}) → (ρ : Nat → PSet.{T}) →
    (e : Expr Nat) → den M σ (push xs ρ) (liftIter xs.length e) = den M σ ρ e
  | [], _, _ => rfl
  | x :: xs, ρ, e => by
      show den M σ (push xs (vcons x ρ)) (liftIter xs.length (Rcic.Declarative.lift 0 1 e)) = _
      rw [den_liftIter M σ xs (vcons x ρ), den_lift_shift]
      rfl

theorem den_accAfter (M : Interp.{T}) (σ : Nat → Nat) : (xs : List PSet.{T}) → (ρ : Nat → PSet.{T}) →
    (acc : Expr Nat) → den M σ (push xs ρ) (accAfter xs.length acc) = fapps (den M σ ρ acc) xs
  | [], _, _ => rfl
  | x :: xs, ρ, acc => by
      show den M σ (push xs (vcons x ρ)) (accAfter xs.length (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0))) = _
      rw [den_accAfter M σ xs (vcons x ρ)]
      show fapps (fapp (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 acc)) x) xs = _
      rw [den_lift_shift]
      rfl

/-- The derived minor of a constructor with only non-recursive fields. -/
theorem minorFromTelescope_nonrec (E : ResolvedEnv) (fuel np : Nat) (Tend : Expr Nat) :
    (Ds : List (Expr Nat)) → (ss : List FieldShape) → (M acc : Expr Nat) →
    (∀ s, s ∈ ss → s = .nonrecursive) → ss.length = Ds.length →
    minorFromTelescope E fuel np M acc ss (policyPi Ds Tend) =
      some (policyPi Ds (.app (foldApps (liftIter Ds.length M) (familyIdx np Tend)) (accAfter Ds.length acc)))
  | [], [], _, _, _, _ => rfl
  | A :: Ds, s :: ss, M, acc, hs, hl => by
      have hs0 : s = .nonrecursive := hs s (List.mem_cons_self _ _)
      subst hs0
      have h := minorFromTelescope_nonrec E fuel np Tend Ds ss (Rcic.Declarative.lift 0 1 M)
        (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) (fun s h => hs s (List.mem_cons_of_mem _ h))
        (by simpa using hl)
      simp only [policyPi, minorFromTelescope, h, Option.map_some']
      rfl

end PSet

end Rcic.F3
