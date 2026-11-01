import rcic.RcicF3PointwisePropParamRecMem
import rcic.RcicF3NormPropOnlyIota

/-!
# The complete PropOnly package at the new pointwise table

The unchanged proof-erased endpoint gives stable literal iota from actual
new faithfulness. Its membership is paid by the new predecessor and the
original BoundG/BoundDG plus the parameter equality supplied by the existing
D check. No new condition, masked Fits or old invariant is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropOnlyIota
open Rcic.Declarative Rcic.Model.PS RawFamily
open NormPropOnlyIota (member_empty)

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
    (α : PointwiseRole.Arities)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
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
    (α : PointwiseRole.Arities)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (Efin : ResolvedEnv) : IotaAt P μ K Efin rr := by
  have hEmpty := installed_empty P μ hE hfam hctors hrec hmem
    α ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy
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
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    RecPkg P μ K E' rr rm :=
  ⟨PointwisePropParamRecMem.member_sound P μ K hE hfam hctors hrec hmem
      hBound hBoundD hpar hPred α hα ctx plans hctx hplans hFaith
      ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy,
    fun Efin _ => iota_at P μ K hE hfam hctors hrec hmem
      α ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy Efin⟩

end Rcic.F3.PSet.PointwisePropOnlyIota
