import rcic.RcicF3PiSized
import rcic.RcicF3PiAdmission
import rcic.RcicF3DEnv
/-! Transparent-body hereditary smallness from stored bounded typings,
member soundness and final-environment iota. No additional apex premise.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSized
open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve)
/-- Existing member soundness and final-environment iota pay hereditary
smallness of every admitted transparent body, from its stored bound. -/
theorem transparent_sized_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {S Efin : ResolvedEnv}
    (hAS : AllSound P μ K S)
    (hIS : ∀ r m, S.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hSfin : ∀ r m, S.members r = some m → Efin.members r = some m) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → BoundG K hW →
    (∀ r m, E.members r = some m → S.members r = some m) →
    ∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true ∧ ∀ σ ρ, Sized (mkM P μ) σ b ρ
  | _, .empty, _, _, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE hfresh _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_sized_of_bound P μ K hAS hIS hSfin hE hB
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
        exact (Sized.levelsClosed (mkM P μ) (fun _ => 0) σ v hlvlv ρ).mp
          (of_hsound P μ (fun _ => 0) hv hs ρ trivial)
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_sized_of_bound P μ K hAS hIS hSfin hE hB.1 hpre r m b h hb htr
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_sized_of_bound P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)) r m b h hb htr
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_sized_of_bound P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)) r m b h hb htr
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, hB, hsub, r, m, b, h, hb, htr => by
      rcases groupMembersT_cases hmem r m h with h1 | h1
      · exact transparent_sized_of_bound P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (groupMembersT_preserve hmem r' m' hm)) r m b h1 hb htr
      · rw [groupMembersT_body_none hmem r m h1] at hb
        cases hb
/-- Elementary lookup/level-closure composition: ordinary group invariant
soundness, final-environment iota, and the existing BoundG pay BodiesSized
in an extension adding only body-less members. No A-axis wall is added. -/
theorem bodiesSized_of_bound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : BoundG K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    (σ : Nat → Nat) : BodiesSized (mkM P μ) σ K E₁ := by
  intro r m b ls hm hb htr _ _ ρ
  cases h1 : E.members r with
  | none =>
      rw [hnew r m hm h1] at hb
      cases hb
  | some m' =>
      have h2 := hsub r m' h1
      rw [hm] at h2
      cases h2
      obtain ⟨hb0, hR⟩ := transparent_sized_of_bound P μ K hA hI hfin hW hB
        (fun _ _ h => h) r m b h1 hb htr
      rw [Ann.instantiateLevels_closed ls b hb0]
      exact hR σ ρ

/-- Elementary environment composition; no new domain-smallness wall. -/
theorem liveSmall_of_bound (P : Premises4)
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
    PiLive.LiveSmall (mkM P μ) σ ds ρ :=
  liveSmall_typed4 P μ σ K hES (bodiesOK_of_envWfT K hW hB hsub hnew σ)
    (PiHereditary.bodiesRegular_of_bound P μ K hW hB hA hI hfin hsub hnew σ)
    (bodiesSized_of_bound P μ K hW hB hA hI hfin hsub hnew σ) d hd hw ρ hρ

/-- Successful typed admission supplies an independent small signature,
normalized fidelity at every candidate, and raw fidelity at the sound one.
Elementary composition; no original field value or data-leaf premise. -/
theorem admitted_field_exact (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) (f : Nat) (X : List Nat → PSet.{4})
    {E Efin E₁ : ResolvedEnv} (hW : EnvWfT E) (hB : BoundG K hW)
    (hA : AllSound P (upd μ f X) K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM →
      IotaAt P (upd μ f X) K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    {n fuel nu np ni depth inner : Nat} {Γ : LCtx} {T : Expr Nat} {l : Level}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E₁ fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth)
    (hES : EnvSound (mkM P (upd μ f X)) σ K E₁ n)
    (d : HasTyT E₁ n Γ T (.sort l)) (hd : LOKt σ 4 K d) :
    ∃ ds args, ds.length = inner ∧ args.length = np + ni ∧
      piTelescopeFuel E₁ (fuel - 1) T =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      (∀ X₁ X₂ ρ, PiIndependent.recursiveTel P (upd μ f X₁) σ ds args ρ =
        PiIndependent.recursiveTel P (upd μ f X₂) σ ds args ρ) ∧
      ∀ ρ, Fits (mkM P (upd μ f X)) σ Γ ρ →
      (∀ Y : List Nat → PSet.{4},
        let M := mkM P (upd μ f Y);
        Equiv (Ed M ((PiSmallCompile.widen (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType
          M (fun xs => Ed M (fapps (Y (((List.range nu).map Level.param).map (evalTotal σ))) xs))))
          (Ed M (den M σ ρ (policyPi ds
            (foldApps (.const f ((List.range nu).map Level.param)) args))))) ∧
      (let M := mkM P (upd μ f X);
        Equiv (Ed M ((PiSmallCompile.widen (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType
          M (fun xs => Ed M (fapps (X (((List.range nu).map Level.param).map (evalTotal σ))) xs))))
          (Ed M (den M σ ρ T))) := by
  obtain ⟨ds, args, hl, ha, hr, hds, hargs⟩ := PiIndependent.admitted_shape h hscope
  refine ⟨ds, args, hl, ha, hr, ?_, ?_⟩
  · intro X₁ X₂ ρ
    exact PiIndependent.recursiveTel_free P μ f X₁ X₂ σ ds args hds hargs ρ
  · intro ρ hρ
    have hs := liveSmall_of_bound P (upd μ f X) σ K hW hB hA hI
      hfin hsub hnew hES d hd hr ρ hρ
    have he : ∀ Y : List Nat → PSet.{4},
        let M := mkM P (upd μ f Y);
        Equiv (Ed M ((PiSmallCompile.widen (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType
          M (fun xs => Ed M (fapps (Y (((List.range nu).map Level.param).map (evalTotal σ))) xs))))
          (Ed M (den M σ ρ (policyPi ds
            (foldApps (.const f ((List.range nu).map Level.param)) args)))) := by
      intro Y
      dsimp only
      have hY := (PiLive.liveSmall_free P μ f X Y σ ds ρ hds).mp hs
      have he := PiLive.compile_ed P (upd μ f Y) σ (PiIndependent.leafArgs P μ σ args)
        (fun xs => Ed (mkM P (upd μ f Y))
          (fapps (Y (((List.range nu).map Level.param).map (evalTotal σ))) xs))
        (fun _ => dich_ed _ _) (foldApps (.const f ((List.range nu).map Level.param)) args)
        (fun ρ' => by
          rw [PiIndependent.leaf_read P μ f Y σ ((List.range nu).map Level.param) args hargs ρ']
          exact Equiv.rfl) ds ρ hY
      have ht := PiIndependent.smallCompile_free P μ f Y (μ f) σ
        (PiIndependent.leafArgs P μ σ args) ds ρ hds
      rw [PiIndependent.upd_self] at ht
      rw [ht] at he
      exact he
    refine ⟨he, (he X).trans ?_⟩
    exact ed_congr (mkM P (upd μ f X))
      (PiHereditary.den_piTelescope_of_bound P (upd μ f X) σ K hW hB hA hI
        hfin hsub hnew hES d hd hr ρ hρ)
end Rcic.F3.PSet.PiSized
