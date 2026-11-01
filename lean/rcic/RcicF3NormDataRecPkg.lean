import rcic.RcicF3NormDataIota
import rcic.RcicF3NormDataMember

/-!
# Complete normalized DATA recursor package after small-frame production

Full normalized faithfulness produces the original stored constructor
abstractions, the actual normalized family equation and the canonical
nodeCore recursor abstraction. The typed witness-row proof is stable in
any common extension. The actual bounded constructor walk supplies reader
soundness for stored-member typing, independently of this new iota law.

The complete RecPkg therefore has exactly one extra semantic production
input: a small closed normalized candidate. Original bounds, the checked
parameter equality and predecessor invariant remain literal. No global
NoFunRec, current-recursion package or raw-frame identity is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataRecPkg
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Stable DATA iota from the actual installed equations and original
normalized-frame constructor cases. -/
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
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hsmall : ∃ A,
      Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (Efin : ResolvedEnv)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) :
    IotaAt P μ K Efin rr := by
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful role P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hCtor := NormDataRead.constructor_value_of_group P μ hE hfam hctors hrec hmem
    ctx plans hctx hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := NormCandidatePrefix.family_equation_of_group P μ hE hfam hctors hrec hmem
    ctx plans hctx hFaith
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
  have hRec : ∀ vs, Equiv (μ rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p rm) := by
    intro vs
    have h := hFaith rr rm hrm vs
    rw [hctx rr (dom_of_members hrm),
      NormRole.envCtx_group hE hfam hctors hrec hmem,
      groupRoles_at_rr _ hlt] at h
    have hp : plans rr = some p := by
      rw [hplans rr (dom_of_members hrm)]
      change (if rr = rr then some p else EvalRole.envPlan hE rr) = some p
      exact if_pos rfl
    rw [hp] at h
    exact h
  intro S hsub w hwr σ n Γ T ρ _ _ _ _ _ hls _ ml mr
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨_, hnM, _, hfr⟩ := iota_align p.node.a w hwr hm
  have hjk : w.ctorIdx < p.node.a.constructors.length := by have := w.hidx; omega
  let j : Fin p.node.a.constructors.length := ⟨w.ctorIdx, hjk⟩
  have hcref : w.ctorRef = p.node.a.family.ref + 1 + j.val := by rw [w.hctorIdx, hfr]
  have hcm : w.ctorMember = p.node.a.constructors[j.val] := by
    have h1 := hsub _ _ w.hctor
    have h2 := p.node.a.constructorsPresent j
    have h3 := hsubF _ _ (p.node.sub _ _ (members_extend_preserved p.node.fresh _ _ h2))
    rw [hcref] at h1
    rw [h1] at h3
    exact Option.some.inj h3
  have hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K rr := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact hls l hl
  exact NormDataIota.iota_eq P μ K p fm ctors hE hfam hctors hrec hmem
    hBound hBoundD hpar hPred ctx plans hctxE hplansE hFaithE
    hFamily hRec hCtor hsmall hType w hwr hm j rfl hcm σ ρ hvs ml mr

/-- Stored membership and stable iota are both produced. Reader soundness
is obtained from the actual bounded constructor prefix, not supplied. -/
theorem rec_pkg (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hsmall : ∃ A,
      Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    RecPkg P μ K E' rr rm :=
  ⟨NormDataMember.member_sound_of_small_frame P μ K hE hfam hctors hrec hmem
      hAg hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hsmall hType,
    fun Efin hsub => iota_at P μ K hE hfam hctors hrec hmem
      hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hsmall hType Efin hsub⟩

end Rcic.F3.PSet.NormDataRecPkg
