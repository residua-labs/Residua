import rcic.RcicF3PointwiseDataCut

/-!
# Finite DATA with a syntax-forced upper bound on the own parameter cut

At a genuine W gap the first selected result index is an own parameter,
so it is literally a bound variable. If that index is absent or is not a
bound variable, equality of the two stored constructor result spines
rules out the gap. This uses the actual own admissions in the member walk;
no level comparison, W check, or semantic agreement is assumed.

The complete invariant step retains literal matching selected parameters
and the actual NoFunRec cache. It includes every nonindexed finite family
with matching parameters and indexed families whose first result index
is not a literal bound variable at every constructor. Arbitrary indexed families
with a variable first result index remain outside this producer.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataFiniteRigid
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The first result index cannot be reclassified as an own parameter.
An empty result-index list also satisfies this concrete syntax condition. -/
def FirstIndexRigid {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ (j : Fin node.a.constructors.length) (k : Nat),
    (node.a.constructorViews j).resultIndices[0]? ≠ some (.bvar k)

/-- In equal result argument lists, a larger own parameter cut would put
a literal bound variable at the first selected index position. -/
theorem result_cut_le {npO nfO np nf : Nat}
    {ixO ix : List (Expr Nat)}
    (hargs : policyParameterLocals npO nfO ++ ixO =
      policyParameterLocals np nf ++ ix)
    (hrigid : ∀ k : Nat, ix[0]? ≠ some (.bvar k)) : npO ≤ np := by
  apply Nat.le_of_not_gt
  intro hlt
  have hlen : np < (policyParameterLocals npO nfO).length := by
    rw [policyParameterLocals_length]
    exact hlt
  have hmem : (policyParameterLocals npO nfO)[np] ∈
      policyParameterLocals npO nfO := List.getElem_mem hlen
  change (policyParameterLocals npO nfO)[np] ∈
    (List.range npO).reverse.map (fun i => Expr.bvar (i + nfO)) at hmem
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hmem
  have hget := List.getElem?_eq_getElem hlen
  rw [← hq] at hget
  have harg : (policyParameterLocals npO nfO ++ ixO)[np]? =
      some (.bvar (q + nfO)) := by
    rw [List.getElem?_append_left hlen]
    exact hget
  rw [hargs] at harg
  have hright : (policyParameterLocals np nf).length ≤ np := by
    simpa only [policyParameterLocals_length] using (Nat.le_refl np)
  rw [List.getElem?_append_right hright, policyParameterLocals_length,
    Nat.sub_self] at harg
  exact hrigid (q + nfO) harg

/-- No indices is one syntax-produced face, with any number of parameters. -/
theorem firstIndexRigid_of_no_indices
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (hix : node.a.family.indices = []) :
    FirstIndexRigid node := by
  intro j k
  have hlen := (node.a.constructorViews j).indexCount
  rw [hix] at hlen
  have hi := List.eq_nil_of_length_eq_zero hlen
  rw [hi]
  intro h
  cases h

/-- The actual constructor walk satisfies W because every putative gap
contradicts its stored result spine. No soundness assumption is used. -/
theorem walk_agree
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hrigid : FirstIndexRigid node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  PointwiseDataCut.walk_agree hE hfam hctors hrec hmem node
    (fun j _ _ _ _ hargs => result_cut_le hargs (hrigid j))

/-- A complete original GInv step. The three shape premises are literal
facts about the selected node and its actual cache, not semantic callbacks. -/
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
    (hrigid : FirstIndexRigid (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  PointwiseDataCut.invariant_step P K hE hfam hctors hrec hmem
    hType hFinite hpar
    (fun j _ _ _ _ hargs => result_cut_le hargs (hrigid j))
    hBound hBoundD hPred

end Rcic.F3.PSet.PointwiseDataFiniteRigid

#print axioms Rcic.F3.PSet.PointwiseDataFiniteRigid.result_cut_le
#print axioms Rcic.F3.PSet.PointwiseDataFiniteRigid.walk_agree
#print axioms Rcic.F3.PSet.PointwiseDataFiniteRigid.invariant_step
