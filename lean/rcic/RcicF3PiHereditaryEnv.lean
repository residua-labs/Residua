import rcic.RcicF3PiHereditary
import rcic.RcicF3DEnv
/-! Transparent-body hereditary regularity from stored bounded typings,
member soundness and final-environment iota. No additional apex premise.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiHereditary
open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve)
/-- Existing member soundness and final-environment iota pay hereditary
regularity of every admitted transparent body, from its stored bound. -/
theorem transparent_regular_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {S Efin : ResolvedEnv}
    (hAS : AllSound P μ K S)
    (hIS : ∀ r m, S.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hSfin : ∀ r m, S.members r = some m → Efin.members r = some m) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → BoundG K hW →
    (∀ r m, E.members r = some m → S.members r = some m) →
    ∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true ∧ ∀ σ ρ, Regular (mkM P μ) σ b ρ
  | _, .empty, _, _, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE hfresh _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_regular_of_bound P μ K hAS hIS hSfin hE hB
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)) r m b h hb htr
  | _, .definition E r0 _ v _ hE hfresh _ hv _ _ _ hlvlv, hB, hsub, r, m, b, h, hb, htr => by
      have hpre : ∀ r' m', E.members r' = some m' → S.members r' = some m' :=
        fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
        refine ⟨hlvlv, ?_⟩
        intro σ ρ
        have hES := envSound_of P (fun r' m' hm => hSfin r' m' (hpre r' m' hm))
          (allSound_prefix hpre hAS) (fun r' m' hm hk => hIS r' m' (hpre r' m' hm) hk)
          (fun _ => 0) 0
        have hs := hsound_ty (P.good _ rfl) hES hv hB.2
        exact (Regular.levelsClosed (mkM P μ) (fun _ => 0) σ v hlvlv ρ).mp
          (of_hsound (mkM P μ) (fun _ => 0) (fun k => pempty_not_mem_U4 P k) hv hs ρ trivial)
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_regular_of_bound P μ K hAS hIS hSfin hE hB.1 hpre r m b h hb htr
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_regular_of_bound P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)) r m b h hb htr
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_regular_of_bound P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)) r m b h hb htr
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, hB, hsub, r, m, b, h, hb, htr => by
      rcases groupMembersT_cases hmem r m h with h1 | h1
      · exact transparent_regular_of_bound P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (groupMembersT_preserve hmem r' m' hm)) r m b h1 hb htr
      · rw [groupMembersT_body_none hmem r m h1] at hb
        cases hb
/-- Elementary lookup/level-closure composition: ordinary group invariant
soundness, final-environment iota, and the existing BoundG pay BodiesRegular
in an extension adding only body-less members. No A-axis wall is added. -/
theorem bodiesRegular_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : BoundG K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    (σ : Nat → Nat) : BodiesRegular (mkM P μ) σ K E₁ := by
  intro r m b ls hm hb htr _ _ ρ
  cases h1 : E.members r with
  | none =>
      rw [hnew r m hm h1] at hb
      cases hb
  | some m' =>
      have h2 := hsub r m' h1
      rw [hm] at h2
      cases h2
      obtain ⟨hb0, hR⟩ := transparent_regular_of_bound P μ K hA hI hfin hW hB
        (fun _ _ h => h) r m b h1 hb htr
      rw [Ann.instantiateLevels_closed ls b hb0]
      exact hR σ ρ

/-- Typed normalized telescopes, with all transparent-body conditions paid
from the ordinary group invariant and the existing stored-derivation bound.
Elementary composition. -/
theorem den_piTelescope_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : BoundG K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    {n : Nat} (hES : EnvSound (mkM P μ) σ K E₁ n)
    {Γ : LCtx} {T : Expr Nat} {l : Level} (d : HasTyT E₁ n Γ T (.sort l))
    (hd : LOKt σ 4 K d) {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel E₁ fuel T = some (ds, b))
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ (policyPi ds b)) (den (mkM P μ) σ ρ T) :=
  den_piTelescope_typed4 P μ σ K hES (bodiesOK_of_envWfT K hW hB hsub hnew σ)
    (bodiesRegular_of_bound P μ K hW hB hA hI hfin hsub hnew σ) d hd hw ρ hρ

/-- Both directions of field membership from the same original typed
admission; there is no original-field inhabitant premise. Elementary transport. -/
theorem normalizedField_iff_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : BoundG K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    {n : Nat} (hES : EnvSound (mkM P μ) σ K E₁ n)
    {Γ : LCtx} {T : Expr Nat} {l : Level} (d : HasTyT E₁ n Γ T (.sort l))
    (hd : LOKt σ 4 K d) {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel E₁ fuel T = some (ds, b))
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) (x : PSet.{4}) :
    x ∈ Ed (mkM P μ) ((PiSyntaxCompile.compile (mkM P μ) σ
      (PiTypedCompile.leafIndex (mkM P μ) σ b) ds ρ).erasedType (mkM P μ) (fun i => i.1)) ↔
      x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T) := by
  have he := (syntaxCompile_ed (mkM P μ) σ b ds ρ).trans
    (ed_congr (mkM P μ) (den_piTelescope_of_bound P μ σ K hW hB hA hI hfin hsub hnew hES d hd hw ρ hρ))
  exact ⟨mem_congr_right he, mem_congr_right he.symm⟩
end Rcic.F3.PSet.PiHereditary
