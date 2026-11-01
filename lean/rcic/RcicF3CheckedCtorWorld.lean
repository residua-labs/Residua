import rcic.RcicF3EvalPlan
import rcic.RcicF3StepWDApex
import rcic.RcicF3DBoundDefs

/-!
# One checked constructor invocation supplies the common row world

The unchanged selected-node D check already says that every constructor
bound is at most the recursor bound. An actual MemberSound argument vector
therefore lies at that recursor bound. BoundDG supplies every row's original
field typings at this SAME vector, including rows with a smaller own bound.
The check's literal parameter equality identifies their original contexts.

No minimum/maximum bound, extra check, normalization, masked Fits or local
candidate closure is asserted. NormDataCtor's unchecked interface is
unchanged. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CheckedCtorWorld
open Rcic.Declarative Rcic.F3.StepDGOrder

theorem constructor_world (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length)
    (σ : Nat → Nat) (ls : List Level)
    (hlen : ls.length =
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors[j.val]).arity)
    (hlevels : ∀ l, l ∈ ls → evalTotal σ l ≤ K (f + 1 + j.val)) :
    (ls.map (evalTotal σ)).length =
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.member.arity ∧
    ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hs : StepDGSide K p.node :=
    (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp
  constructor
  · rw [List.length_map, hlen, (p.node.a.constructorViews j).arity]
  · intro v hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    exact Nat.le_trans (hlevels l hl) (hs.2.2 j)

/-- Every row is typed at the invoked constructor's same complete vector.
No comparison between two constructor bounds is required. -/
theorem all_row_fields (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length)
    (σ : Nat → Nat) (ls : List Level)
    (hlen : ls.length =
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors[j.val]).arity)
    (hlevels : ∀ l, l ∈ ls → evalTotal σ l ≤ K (f + 1 + j.val)) :
    let node := (EvalPlan.ofGroup hE hfam hctors hrec hmem).node
    ∀ (i : Fin node.a.constructors.length)
      (k : Fin (node.a.constructorViews i).fields.length),
      ∃ l : Level, ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
        (policyPrefixContext (node.a.family.parameters ++ (node.a.constructorViews i).fields)
          (node.a.family.parameters.length + k.val))
        ((node.a.constructorViews i).fields[k]) (.sort l),
        LOKt (σOf (ls.map (evalTotal σ))) 4 K d := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hs : StepDGSide K p.node :=
    (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp
  have hw := constructor_world K hE hfam hctors hrec hmem hp j σ ls hlen hlevels
  change ∀ (i : Fin p.node.a.constructors.length)
      (k : Fin (p.node.a.constructorViews i).fields.length),
      ∃ l : Level, ∃ d : HasTyT (extendEnv E f fm) p.node.a.family.member.arity
        (policyPrefixContext (p.node.a.family.parameters ++ (p.node.a.constructorViews i).fields)
          (p.node.a.family.parameters.length + k.val))
        ((p.node.a.constructorViews i).fields[k]) (.sort l),
        LOKt (σOf (ls.map (evalTotal σ))) 4 K d
  intro i k
  rw [← hs.1 i]
  exact hD.2 p.node i (ls.map (evalTotal σ)) hw.1 hw.2 k

end Rcic.F3.PSet.CheckedCtorWorld
