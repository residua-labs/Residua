import rcic.RcicF3PointwiseDataFiniteSimple

/-!
# One actual DATA member-walk consumer for produced syntactic cut bounds

This helper owns the shared walk, selected-constructor lookup, stored-type
spine comparison, and all-RecNode invariant assembly. Each public finite
syntax producer supplies ResultCutBound by a proved arithmetic fact.
ResultCutBound is an internal syntactic interface, not an apex hypothesis
or a replacement for the original bounds/invariant.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataCut
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Every alternative decomposition with the SAME total telescope length
and the SAME terminal argument spine has an own cut at most the selected
cut. This is discharged from concrete selected syntax by callers. -/
def ResultCutBound {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm) : Prop :=
  ∀ (j : Fin node.a.constructors.length) (npO nfO : Nat)
    (ixO : List (Expr Nat)),
    npO + nfO = (node.a.constructorViews j).parameters.length +
      (node.a.constructorViews j).fields.length →
    policyParameterLocals npO nfO ++ ixO =
      policyParameterLocals (node.a.constructorViews j).parameters.length
        (node.a.constructorViews j).fields.length ++
        (node.a.constructorViews j).resultIndices →
    npO ≤ (node.a.constructorViews j).parameters.length

/-- One traversal of the original GroupMembersT walk, preserving every
own admission scope and obtaining the two stored-type equalities once. -/
theorem walk_agree
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hCut : ResultCutBound node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hlen := node_ctors_length node hrr
  refine PointwiseDataFiniteSimple.walkAgree_of_views
    ((f, fm) :: ctors ++ [(rr, rm)])
    (AgreeAt node.a.family.parameters.length) E' ?_ hmem
    (fun _ hc => hc) (fun _ _ hm => hm)
  intro Ew r m fam cv hin _
  have hkC : m.mclass = .constructorM := cv.hasClass
  have hctor : ∃ i : Fin node.a.constructors.length,
      r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
    rcases List.mem_cons.mp hin with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [hfam] at hkC
      cases hkC
    · rcases List.mem_append.mp h with hc | hr
      · have href : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, hc, rfl⟩
        rw [hL] at href
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp href
        have hi' : i < node.a.constructors.length := by
          rw [hlen]
          exact List.mem_range.mp hi
        exact ⟨⟨i, hi'⟩, rfl, Option.some.inj
          ((groupMembersT_installed hmem hin).symm.trans
            (node_ctor_member node ⟨i, hi'⟩))⟩
      · rw [List.mem_singleton] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        rw [hrec] at hkC
        cases hkC
  obtain ⟨i, rfl, rfl⟩ := hctor
  have hspl := policyPi_split_eq _ _ _ _
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (cv.storedType.symm.trans (node.a.constructorViews i).storedType)
  have htotal : cv.parameters.length + cv.fields.length =
      (node.a.constructorViews i).parameters.length +
        (node.a.constructorViews i).fields.length := by
    simpa only [List.length_append] using congrArg List.length hspl.1
  have hargs := congrArg (fun e => (appsSpine e).2) hspl.2
  simp only [appsSpine_foldApps, appsSpine, List.nil_append] at hargs
  have hcut := hCut i cv.parameters.length cv.fields.length
    cv.resultIndices htotal hargs
  rw [(node.a.constructorViews i).parameterCount] at hcut
  intro k _ hge hlt
  exact False.elim (by omega)

/-- The generic internal assembly returns the unchanged original group
invariant, with its original bounds and predecessor invariant. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hFinite : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hCut : ResultCutBound (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hwalk : WalkAgree (AgreeAt p.node.a.family.parameters.length) hmem :=
    walk_agree hE hfam hctors hrec hmem p.node hCut
  have hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
    intro node
    rw [← Rcic.F3.StepWGroup.nodeCut_unique p.node node]
    exact hwalk
  exact PointwiseDataFiniteOriginal.group_step P K hE hfam hctors hrec hmem
    hType hFinite hpar hAg hBound hBoundD hPred

end Rcic.F3.PSet.PointwiseDataCut

#print axioms Rcic.F3.PSet.PointwiseDataCut.walk_agree
#print axioms Rcic.F3.PSet.PointwiseDataCut.invariant_step
