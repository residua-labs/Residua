import rcic.RcicF3RawFamilyMember
import rcic.RcicF3RawFamilyPlanReads

/-!
# Candidate family-prefix soundness from the predecessor invariant

A fresh family update preserves the predecessor's actual reads and faithful
table equations. Reapplying the original predecessor GInv produces its
AllSound and extending-final IotaAt at the updated table. Admissibility
alone pays the new family member. This constructs the family-only EnvSound
needed by bounded field typing without assuming candidate closure.
It does not produce recursive evaluation existence. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative

theorem candidate_prefix_envSound
    (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hPred : PlanRole.GInv role P K hW)
    (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : PlanRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = PlanRole.envPlan hW r)
    (hFaith : PlanRole.Faithful role P μ ctx plans E)
    (hReads : ReadsClosed ctx E)
    (fd : FamData) (X : Frame) (hX : Admissible fd X)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (m : CheckedMember) (hTy : m.mtype = famType fd)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hbounded : exprLevelsBounded m.arity m.mtype = true)
    (hbody : m.body = none) (hclass : m.mclass = .inductiveM)
    (hfresh : E.members fd.fref = none)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P μ fd X)) σ K (extendEnv E fd.fref m) n := by
  let ν := table P μ fd X
  let E₁ := extendEnv E fd.fref m
  have hag : AgreeOn μ ν (Dom E) :=
    agreeOn_upd hfresh μ (ofFrame P μ fd X)
  have hFaithν : PlanRole.Faithful role P ν ctx plans E := by
    intro r m' hm vs
    have hdom : Dom E r := dom_of_members hm
    rw [← hag r hdom vs]
    exact (hFaith r m' hm vs).trans
      (PlanRole.member_agree (familyReadsCtx P ctx)
        hag r m' (hReads r m' hm) (plans r) vs)
  have hPrior := hPred ctx hctx plans hplans ν hFaithν
  have hFamily : MemberSound P ν K fd.fref m :=
    family_member_sound P μ fd X hX hf K m hTy hcl hbounded hbody
  have hsub : ∀ r m', E.members r = some m' → E₁.members r = some m' := by
    intro r m' hm
    have hne : r ≠ fd.fref := by
      intro heq
      subst r
      rw [hfresh] at hm
      cases hm
    change (extendEnv E fd.fref m).members r = some m'
    rw [members_extend_ne E fd.fref m r hne]
    exact hm
  have hAll : AllSound P ν K E₁ := by
    intro r m' hm
    by_cases heq : r = fd.fref
    · subst r
      change (extendEnv E fd.fref m).members fd.fref = some m' at hm
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      exact hFamily
    · change (extendEnv E fd.fref m).members r = some m' at hm
      rw [members_extend_ne E fd.fref m r heq] at hm
      exact hPrior.1 r m' hm
  have hI : ∀ r m', E₁.members r = some m' →
      m'.mclass = .recursorM → IotaAt P ν K E₁ r := by
    intro r m' hm hrec
    by_cases heq : r = fd.fref
    · subst r
      change (extendEnv E fd.fref m).members fd.fref = some m' at hm
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      rw [hclass] at hrec
      cases hrec
    · change (extendEnv E fd.fref m).members r = some m' at hm
      rw [members_extend_ne E fd.fref m r heq] at hm
      exact hPrior.2 E₁ hsub r m' hm hrec
  exact envSound_of P (fun _ _ hm => hm) hAll hI σ n

end Rcic.F3.PSet.RawFamily
