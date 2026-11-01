import rcic.RcicF3PointwisePropRecMem
import rcic.RcicF3EvalPropRecIota

/-!
# Complete Prop/anySort PendA package with the pointwise predecessor

Stored membership uses the produced new-prefix evaluation chain. The
literal legacy IotaAt clause retains its proved empty-witness scope on the
single positive-depth Prop row; no shape-schema iota is claimed. Both
conjuncts use the same actual table, full levels and original admission.
No old/new invariant equality is used. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropRecPkg
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
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hPend : ∃ node : RecNode E E' f rr rm, PendA node) :
    RecPkg P μ K E' rr rm := by
  have hmember := PointwisePropRecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hPred α hα ctx plans hctx hplans hFaith ctxFull plansFull
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

end Rcic.F3.PSet.PointwisePropRecPkg
