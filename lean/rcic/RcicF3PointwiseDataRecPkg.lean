import rcic.RcicF3PointwiseDataIota
import rcic.RcicF3PointwiseDataMember

/-!
# Complete pointwise DATA recursor package at the checked bounded worlds

New faithfulness supplies the original constructor and recursor operations
and the explicit-arity pointwise family equation. Produced density yields
the literal typed legacy iota law in every common extension. This iota
component needs no candidate-existence or reader-soundness hypothesis.

The complete package also produces stored membership: its ordinary reader
comes from the bounded constructor walk. The ORIGINAL selected D check
supplies parameter equality and the own-constructor-to-recursor bound;
LocalCandidates is the sole additional semantic production input. It is
still unpaid universally. No old/current invariant equality is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataRecPkg
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
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
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
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hCtor := PointwiseRoleEquations.constructor_value_of_group P α μ
    hE hfam hctors hrec hmem ctx plans hctx hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := PointwiseRoleEquations.family_equation_of_group P α μ
    hE hfam hctors hrec hmem hα ctx plans hctx hFaith hType
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hRec := PointwiseRoleEquations.recursor_value_of_group P α μ
    hE hfam hctors hrec hmem ctx plans hctx hplans hFaith
  have hαE : PointwiseRole.AritiesAgree α E :=
    hα.mono (fun r m hm => groupMembersT_preserve hmem r m hm)
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
  exact PointwiseDataIota.iota_eq P μ K p fm ctors hE hfam hctors hrec hmem
    hBound hBoundD hpar hPred α hαE ctx plans hctxE hplansE hFaithE
    hFamily hRec hCtor hType w hwr hm j rfl hcm σ ρ hvs ml mr

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
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hcheck : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hLocal : PointwiseDataLocal.LocalCandidates P μ
      (EvalPlan.ofGroup hE hfam hctors hrec hmem) K)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    RecPkg P μ K E' rr rm := by
  have hs := (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hcheck
  exact ⟨PointwiseDataMember.member_sound_of_local_candidates P μ K hE hfam hctors hrec hmem
      hAg hBound hBoundD hPred α hα ctx plans hctx hplans hFaith hcheck hLocal hType,
    fun Efin hsub => iota_at P μ K hE hfam hctors hrec hmem
      hBound hBoundD hs.1 hPred α hα ctx plans hctx hplans hFaith hType Efin hsub⟩

end Rcic.F3.PSet.PointwiseDataRecPkg
