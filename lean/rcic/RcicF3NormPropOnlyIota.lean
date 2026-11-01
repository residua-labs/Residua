import rcic.RcicF3NormPropParamRecMem
import rcic.RcicF3PropIota

/-!
# Stable iota and the complete checked PropOnly package

A uniformly Prop propOnly endpoint is the erased proof at every semantic
environment. The complete stored abstraction is therefore erased too.
The literal IotaAt clause compares two inhabitants of the same interpreted
type, so its right side equals the erased left side. This law needs no
constructor-count, recursive-depth, parameter or legacy-row restriction.

Stored member typing is independently produced from the actual bound
packages and the existing checked parameter-telescope equality, then
composed with that iota law. Unchecked arbitrary parameter mirrors and
the universal data case remain open. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropOnlyIota
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Empty endpoints erase the complete literal abstraction, including
empty binder domains; no fitting or typing input is needed for this law. -/
theorem piLam_empty (M : Interp.{4}) (σ : Nat → Nat)
    (g : (Nat → PSet.{4}) → PSet.{4})
    (hg : ∀ ρ, Equiv (g ρ) pempty) (e : Expr Nat) (ρ : Nat → PSet.{4}) :
    Equiv (piLam M σ g ρ e) pempty := by
  induction e generalizing ρ with
  | pi A B _ ih =>
    change Equiv (cond M.dec (LamProof M (den M σ ρ A)
      (fun x => piLam M σ g (vcons x ρ) B)) pempty _) pempty
    rw [cond_pos (show LamProof M (den M σ ρ A)
      (fun x => piLam M σ g (vcons x ρ) B) from fun x _ => ih _)]
    exact Equiv.rfl
  | _ => exact hg ρ

theorem endpoint_empty (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hpolicy : p.node.a.policy = .propOnly) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ p ρ = pempty := by
  rw [NormDPlanBridge.endpoint_propOnly M σ p hProp hpolicy,
    recEnd_propOnly M σ (famDataOf p.node.a) ρ (hProp σ) hpolicy]

theorem member_empty (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hpolicy : p.node.a.policy = .propOnly) (m : CheckedMember) :
    Equiv (EvalPlanValue.memberValue M σ p m) pempty :=
  piLam_empty M σ (EvalPlanValue.endValue M σ p)
    (fun ρ => by rw [endpoint_empty M σ p hProp hpolicy ρ]; exact Equiv.rfl)
    m.mtype ρ0

/-- The actual canonical plan and full faithful table supply the installed
recursor equation at every universe vector, including unused vectors. -/
theorem installed_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful role P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    ∀ vs, Equiv (μ rr vs) pempty := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hlt : f < rr := by
    have hr := p.node.a.recursorRef
    rw [p.node.fam] at hr
    change rr = f + 1 + p.node.a.constructors.length at hr
    rw [hr]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self f)
      (Nat.le_add_right (f + 1) p.node.a.constructors.length)
  intro vs
  have h := hFaithFull rr rm hrm vs
  rw [hctxFull rr (dom_of_members hrm),
    NormRole.envCtx_group hE hfam hctors hrec hmem,
    groupRoles_at_rr _ hlt] at h
  have hp : plansFull rr = some p := by
    rw [hplansFull rr (dom_of_members hrm)]
    change (if rr = rr then some p else EvalRole.envPlan hE rr) = some p
    exact if_pos rfl
  rw [hp] at h
  exact h.trans (member_empty (mkM P μ) (σOf vs) p hProp hpolicy rm)

/-- Stable literal iota on the complete uniformly Prop propOnly face.
This theorem has no no-parameter, no-PendA, field-free or singleton premise. -/
theorem iota_at (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful role P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (Efin : ResolvedEnv) : IotaAt P μ K Efin rr := by
  have hEmpty := installed_empty P μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy
  intro S _ w hwr σ n Γ T ρ hl _ _ hr _ _ _ ml mr
  apply rhs_eq_ed_pempty ml mr
  have hL : den (mkM P μ) σ ρ (iotaLhsOf w) =
      fapps (μ rr (w.ls.map (evalTotal σ)))
        (w.preMajor.map (den (mkM P μ) σ ρ) ++
          [den (mkM P μ) σ ρ (ctorMajor w)]) := by
    unfold iotaLhsOf recCall
    rw [fapps_den_append_singleton, hwr]
    rfl
  rw [hL]
  exact fapps_of_pempty (hEmpty _) _

/-- Both literal package conjuncts are produced for the actual same
PropOnly group, checked parameter telescopes and installed table. -/
theorem rec_pkg (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful role P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    RecPkg P μ K E' rr rm :=
  ⟨NormPropParamRecMem.member_sound P μ K hE hfam hctors hrec hmem
      hBound hBoundD hpar hPred ctx plans hctx hplans hFaith
      ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy,
    fun Efin _ => iota_at P μ K hE hfam hctors hrec hmem
      ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy Efin⟩

end Rcic.F3.PSet.NormPropOnlyIota
