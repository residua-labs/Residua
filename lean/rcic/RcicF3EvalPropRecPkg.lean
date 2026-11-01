import rcic.RcicF3EvalPropRecIota

/-!
# The complete literal recursor package on the Prop/anySort PendA face

The stored-type conjunct is produced by normalized indexed evaluation.
The stable IotaAt conjunct is the current production legacy-witness
property: selection gives at most one constructor, whose positive-depth
PendA row cannot admit a legacy witness. Both conjuncts are composed here
without an endpoint-typing or iota callback. Data and propOnly faces and
universal shape-schema iota are not asserted. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPropRecPkg
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The same admitted group, predecessor invariant, full faithful table
and complete bounded universe vectors supply the full literal RecPkg. -/
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
    (hPred : EvalRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful role P μ ctxFull plansFull E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hPend : ∃ node : RecNode E E' f rr rm, PendA node) :
    RecPkg P μ K E' rr rm := by
  have hmember := EvalPropRecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hPred ctx plans hctx hplans hFaith ctxFull plansFull
    hctxFull hplansFull hFaithFull hProp hpolicy
  obtain ⟨node, hA⟩ := hPend
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hsmall : node.a.constructors.length ≤ 1 := by
    have hs := (selection_prop p.node.a (fun _ => 0) (hProp _) hpolicy).2
    have hn := node.a.recursorRef
    have hp := p.node.a.recursorRef
    rw [node.fam] at hn
    rw [p.node.fam] at hp
    change rr = f + 1 + p.node.a.constructors.length at hp
    omega
  exact ⟨hmember, fun Efin hsub =>
    EvalPropRecIota.iota_at P μ K hE hmem node hA hsmall hsub⟩

end Rcic.F3.PSet.EvalPropRecPkg
