import rcic.RcicF3PropEvalDirectCycle
import rcic.RcicF3RecArguments
import rcic.RcicF3PointwisePropRecMem

/-!
# Original-bound Prop direct-cycle recursor package

Actual nonempty recursor arguments produce an Eval through the established
pointwise predecessor and original BoundG. Every root constructor in this
face requires a direct recursive child, so the finite Eval is impossible.
The proof-irrelevant endpoint case uses the original same-target rule.

This produces the full original RecPkg, including stable legacy IotaAt
at every arbitrary common extension. No D check, parameter equality,
field-free condition, semantic callback, or admitted-completion guard is
added. Original definitions and whole-tier root remain unchanged.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropCycleIota
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

theorem iota_eq (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (hRec : ∀ vs, Equiv (μ p.rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p p.rm))
    (hcycles : ∀ j : Fin p.node.a.constructors.length,
      FieldShape.recursive 0 ∈ p.node.h14.shapesAt j)
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (h0 : evalTotal (σOf (w.ls.map (evalTotal σ))) p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K p.rr)
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X) :
    Equiv (den (mkM P μ) σ ρ (iotaLhsOf w))
      (den (mkM P μ) σ ρ (iotaRhsOf w)) := by
  cases P.dec (Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) pempty) with
  | isTrue he => exact rhs_eq_ed_pempty ml mr he
  | isFalse hne =>
      obtain ⟨ps, mo, ms, is, ha⟩ :=
        RecArguments.of_nonempty (mkM P μ) p hRec w hwr hm σ ρ hne
      let C : Context :=
        ⟨p.E, p.E', p.f, p.rr, p.rm, p.node, mkM P μ,
          σOf (w.ls.map (evalTotal σ)), ps, mo, ms, ha.minors_length⟩
      have hmo := ha.motive_fit
      rw [hpolicy] at hmo
      have hs := PointwisePropEval.result_spec P μ K C rfl fm ctors
        hE hfam hctors hrec hmem hBound hPred α hα ctx plans hctx hplans
        hFaith hFamily (w.ls.map (evalTotal σ)) rfl hvs h0 hpolicy
        (.param p.node.a.family.member.arity) hmo ha.minors_fit is
        (den (mkM P μ) σ ρ (ctorMajor w)) ha.parameters_fit ha.indices_fit ha.major_fit
      exact (Eval.false_of_direct_cycles (C := C) hcycles hs.2.1).elim

theorem iota_at (P : Premises4)
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
    (hcycles : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      FieldShape.recursive 0 ∈ (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.h14.shapesAt j)
    (Efin : ResolvedEnv)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) :
    IotaAt P μ K Efin rr := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hFaithFull hProp
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hRec := PointwiseRoleEquations.recursor_value_of_group P α μ
    hE hfam hctors hrec hmem ctxFull plansFull hctxFull hplansFull hFaithFull
  intro S hsub w hwr σ n Γ T ρ hl hlsound hllok hr hrs hls hfit ml mr
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  have hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K rr := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact hls l hl
  exact iota_eq P μ K p fm ctors hE hfam hctors hrec hmem hBound hPred α hα
    ctx plans hctx hplans hFaith hFamily hRec hcycles w hwr hm σ ρ
    (hProp _) hpolicy hvs ml mr

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
    (hcycles : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      FieldShape.recursive 0 ∈ (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.h14.shapesAt j) :
    RecPkg P μ K E' rr rm :=
  ⟨PointwisePropRecMem.member_sound P μ K hE hfam hctors hrec hmem hBound hPred α hα
      ctx plans hctx hplans hFaith ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy,
    fun Efin hsub => iota_at P μ K hE hfam hctors hrec hmem hBound hPred α hα
      ctx plans hctx hplans hFaith ctxFull plansFull hctxFull hplansFull hFaithFull
      hProp hpolicy hcycles Efin hsub⟩

end Rcic.F3.PSet.PointwisePropCycleIota

#print axioms Rcic.F3.PSet.PointwisePropCycleIota.iota_eq
#print axioms Rcic.F3.PSet.PointwisePropCycleIota.iota_at
#print axioms Rcic.F3.PSet.PointwisePropCycleIota.rec_pkg
