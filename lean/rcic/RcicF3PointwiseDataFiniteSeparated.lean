import rcic.RcicF3PointwiseDataFiniteRigid

/-!
# Finite DATA with exact separation of the first field from the first index

Equality of the stored constructor telescopes fixes the TOTAL binder count.
If an own admission moves the parameter cut to the right of the selected
cut, the first selected result index must therefore be exactly the first
selected field: `bvar (fields.length - 1)`. It cannot be an arbitrary local.

This produces the complete original group invariant when each constructor
has no fields, or its first result index is not that exact local. It includes
the previous FirstIndexRigid cases and also permits a first index that names
a parameter or a later field. All original bounds and invariant conclusions
are retained. This is a broader finite syntax case, not arbitrary DATA
closure. The genuinely ambiguous first-field-index case remains open.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataFiniteSeparated
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The first selected result index is separated from the one local that
could be swallowed by a larger own parameter prefix. Fieldless constructors
have no possible cut gap, independently of their index expressions. -/
def FirstFieldSeparated {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm) : Prop :=
  ∀ j : Fin node.a.constructors.length,
    (node.a.constructorViews j).fields.length = 0 ∨
      (node.a.constructorViews j).resultIndices[0]? ≠
        some (.bvar ((node.a.constructorViews j).fields.length - 1))

/-- The older exclusion of EVERY bound variable implies exact separation. -/
theorem separated_of_firstIndexRigid
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (h : PointwiseDataFiniteRigid.FirstIndexRigid node) :
    FirstFieldSeparated node :=
  fun j => Or.inr (h j ((node.a.constructorViews j).fields.length - 1))

/-- The stronger arithmetic conclusion uses both pieces of stored-type
equality: identical telescope length and identical terminal argument spine. -/
theorem result_cut_le {npO nfO np nf : Nat}
    {ixO ix : List (Expr Nat)}
    (htotal : npO + nfO = np + nf)
    (hargs : policyParameterLocals npO nfO ++ ixO =
      policyParameterLocals np nf ++ ix)
    (hsep : nf = 0 ∨ ix[0]? ≠ some (.bvar (nf - 1))) : npO ≤ np := by
  rcases hsep with hzero | hsep
  · omega
  · apply Nat.le_of_not_gt
    intro hlt
    have hlen : np < (policyParameterLocals npO nfO).length := by
      rw [policyParameterLocals_length]
      exact hlt
    have hentry : (policyParameterLocals npO nfO)[np] =
        Expr.bvar (nf - 1) := by
      simp only [policyParameterLocals, List.getElem_map,
        List.getElem_reverse, List.getElem_range, List.length_range]
      congr 1
      omega
    have hget : (policyParameterLocals npO nfO)[np]? =
        some (.bvar (nf - 1)) := by
      rw [List.getElem?_eq_getElem hlen, hentry]
    have harg : (policyParameterLocals npO nfO ++ ixO)[np]? =
        some (.bvar (nf - 1)) := by
      rw [List.getElem?_append_left hlen]
      exact hget
    rw [hargs] at harg
    have hright : (policyParameterLocals np nf).length ≤ np := by
      rw [policyParameterLocals_length]
      exact Nat.le_refl np
    rw [List.getElem?_append_right hright, policyParameterLocals_length,
      Nat.sub_self] at harg
    exact hsep harg

/-- An actual own constructor admission can have no W gap on this broader
syntax face. The actual member walk and its individual scopes are retained. -/
theorem walk_agree
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hsep : FirstFieldSeparated node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  PointwiseDataCut.walk_agree hE hfam hctors hrec hmem node
    (fun j _ _ _ htotal hargs => result_cut_le htotal hargs (hsep j))

/-- Complete original GInv production. The new condition describes literal
selected syntax; no level-agreement callback or completed soundness is used. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hFinite : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hpar : ∀ j : Fin
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hsep : FirstFieldSeparated (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hBound : BoundG K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  PointwiseDataCut.invariant_step P K hE hfam hctors hrec hmem
    hType hFinite hpar
    (fun j _ _ _ htotal hargs => result_cut_le htotal hargs (hsep j))
    hBound hBoundD hPred

/-! These arithmetic controls are deliberately only syntax controls. They
are not presented as complete admitted-environment witnesses. -/

/-- A first index naming the SECOND of two fields passes the new condition,
although it is a bound variable and fails the old literal condition. -/
theorem later_field_syntax_control :
    ([Expr.bvar 0] : List (Expr Nat))[0]? ≠ some (.bvar (2 - 1)) ∧
      ¬ (∀ k : Nat,
        ([Expr.bvar 0] : List (Expr Nat))[0]? ≠ some (.bvar k)) := by
  constructor
  · decide
  · intro h
    exact h 0 rfl

/-- A first index naming a PARAMETER above the sole field is likewise new. -/
theorem parameter_syntax_control :
    ([Expr.bvar 1] : List (Expr Nat))[0]? ≠ some (.bvar (1 - 1)) ∧
      ¬ (∀ k : Nat,
        ([Expr.bvar 1] : List (Expr Nat))[0]? ≠ some (.bvar k)) := by
  constructor
  · decide
  · intro h
    exact h 1 rfl

/-- The omitted ambiguous case really can have two equal stored spines
with different cuts; syntax alone cannot establish their order. -/
theorem ambiguous_cut_syntax_control :
    (1 : Nat) + 0 = 0 + 1 ∧
      policyParameterLocals 1 0 ++ ([] : List (Expr Nat)) =
        policyParameterLocals 0 1 ++ [Expr.bvar 0] ∧
      ¬ (1 : Nat) ≤ 0 := by
  decide

end Rcic.F3.PSet.PointwiseDataFiniteSeparated

#print axioms Rcic.F3.PSet.PointwiseDataFiniteSeparated.result_cut_le
#print axioms Rcic.F3.PSet.PointwiseDataFiniteSeparated.walk_agree
#print axioms Rcic.F3.PSet.PointwiseDataFiniteSeparated.invariant_step
#print axioms Rcic.F3.PSet.PointwiseDataFiniteSeparated.later_field_syntax_control
#print axioms Rcic.F3.PSet.PointwiseDataFiniteSeparated.ambiguous_cut_syntax_control
