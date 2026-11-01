import rcic.RcicF3PointwiseDataRecPkg

/-!
# Checked DATA group composition for the separate pointwise invariant

The target is explicitly PointwiseRole.GInv. Original walk/bound/check
conditions are retained. LocalCandidatesAt is only the exact internal
remaining semantic production obligation, quantified over every actual
faithful table and metadata map. No candidate, mask, or fixture is placed
on an unconditional universal edge.

The constructor walk, stored recursor member, and stable legacy iota are
produced and composed here. Prop and the old normalized invariant are not
retargeted by this module. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

def GroupStepAt (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm,
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  PointwiseRole.GInv P K hE →
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- Only actual bounded-world candidate existence remains. This is an
internal conditional decomposition, not a produced universal premise. -/
def LocalCandidatesAt (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm,
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  PointwiseRole.GInv P K hE →
  ∀ α : PointwiseRole.Arities, PointwiseRole.AritiesAgree α E' →
  ∀ ctx : Nat → Role,
    (∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
  ∀ plans : EvalRole.Plans,
    (∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
  ∀ μ, EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E' →
    PointwiseDataLocal.LocalCandidates P μ (EvalPlan.ofGroup hE hfam hctors hrec hmem) K

theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hcheck : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hLocal : LocalCandidatesAt P K hE hfam hctors hrec hmem) :
    GroupStepAt P K hE hfam hctors hrec hmem := by
  intro hAg hBound hBoundD hPred α hα ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hLocalμ := hLocal hAg hBound hBoundD hPred α hα ctx hctx plans hplans μ hFaith
  have hAll := PointwiseDataMember.sound_of_local_candidates P μ K hE hfam hctors hrec hmem
    hAg hBound hBoundD hPred α hα ctx plans hctx hplans hFaith hcheck hLocalμ hType
  have hPkg := PointwiseDataRecPkg.rec_pkg P μ K hE hfam hctors hrec hmem
    hAg hBound hBoundD hPred α hα ctx plans hctx hplans hFaith hcheck hLocalμ hType
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hαE : PointwiseRole.AritiesAgree α E := hα.mono hsubE
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (hsubE r m hm)
  have hPrior := hPred α hαE ctx hctxE plans hplansE μ hFaithE
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  refine ⟨hAll, ?_⟩
  intro Efin hsub r m hm hk
  rcases group_member_cases hmem hL hrr p.node hm with
    hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · exact hPrior.2 Efin (fun s n hn => hsub s n (hsubE s n hn)) r m hold hk
  · rw [hfam] at hk
    cases hk
  · exact hPkg.2 Efin hsub
  · rw [(p.node.a.constructorViews j).hasClass] at hk
    cases hk

end Rcic.F3.PSet.PointwiseDataGroup

namespace Rcic.F3.PSet.PointwiseRole
open Rcic.Declarative Rcic.Model.PS

/-- Finalization uses the SAME actual pointwise table and produced invariant. -/
theorem envSound_of_gInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hI : GInv P K hW) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P hW)) σ K E n := by
  have hIv := hI (arities E) (arities_agree E)
    (NormRole.envCtx hW) (fun _ _ => rfl)
    (EvalRole.envPlan hW) (fun _ _ => rfl) _ (table_spec P hW).2.1
  exact envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) σ n

end Rcic.F3.PSet.PointwiseRole
