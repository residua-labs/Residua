import rcic.RcicF3NormRoleConsumer

/-!
# Faithful transfer at normalized roles and actual indexed plans

The read-closure certificate is produced from the admitted environment.
Changing a fresh family slot preserves every preceding normalized role
and its actual indexed endpoint. No arbitrary family-read callback or
legacy-table comparison is assumed. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormRole
open Rcic.Declarative Rcic.Model.PS

theorem readsClosed (P : Premises4) {E : ResolvedEnv} (hE : EnvWfT E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hc : ∀ r, Dom E r → ctx r = envCtx hE r)
    (hp : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r) :
    EvalRole.ReadsClosed ctx plans E :=
  (EvalRole.faithful_envTable RawFamily.role P ctx plans
    (RawFamily.familyReadsCtx P ctx) hE (planReadsOKAlong hE ctx plans hc hp)).2

theorem faithful_transfer (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {ctx : Nat → Role}
    {plans : EvalRole.Plans} {E : ResolvedEnv}
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E)
    (hR : EvalRole.ReadsClosed ctx plans E) (hag : AgreeOn ν μ (Dom E)) :
    EvalRole.Faithful RawFamily.role P ν ctx plans E := by
  intro r m hm vs
  rw [hag r (dom_of_members hm) vs]
  exact (hF r m hm vs).trans (EvalRole.member_agree
    (RawFamily.familyReadsCtx P ctx) (agreeOn_symm hag) r m (plans r) (hR r m hm) vs)

/-- Both role and plan reads are produced for the actual predecessor. -/
theorem faithful_upd_fresh (P : Premises4) {E : ResolvedEnv} (hE : EnvWfT E)
    {μ : Nat → List Nat → PSet.{4}} {ctx : Nat → Role} {plans : EvalRole.Plans}
    (hc : ∀ r, Dom E r → ctx r = envCtx hE r)
    (hp : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E)
    {f : Nat} (hf : E.members f = none) (X : List Nat → PSet.{4}) :
    EvalRole.Faithful RawFamily.role P (upd μ f X) ctx plans E := by
  refine faithful_transfer P hF (readsClosed P hE ctx plans hc hp) ?_
  intro r hr vs
  exact upd_ne μ f X (fun he => by
    subst he
    unfold Dom at hr
    rw [hf] at hr
    exact absurd hr (by decide)) vs

end Rcic.F3.PSet.NormRole
