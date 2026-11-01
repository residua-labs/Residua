import rcic.RcicF3NormSmallFrame
import rcic.RcicF3PointwiseDataLocal

/-!
# Local small candidates from bounded reached-domain masks

The constructed signature candidate is already admissible at every
universe vector. Proving its constructor closure at one world consumes
domain masks only at that world's canonical vector. The proof retains
the original dependent child keys, output indices and every parameter
representative, using the same bounded intersection as the global
assembler. It does not need masks or closure at unrelated worlds.

The final adapter exposes the existing internal LocalCandidates obligation
from masks at the original arity-correct vectors bounded by K rr. The
mask producer is still unpaid in general. Neither this predicate nor a
new check is added to the checked apex, and the old global interpretation
and its all-world candidate obligation are unchanged.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormSmallFrameLocal
open Rcic.Declarative PiIndex RawFamily RawFamilyRec
open EvalPlanNormal (fd fields specs index)
open NormSmallFrame (candidate model syntaxView syntaxIndex syntax_get cached_leaves)

def ReachedMasksAt (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (vs : List Nat) : Prop :=
  ∀ (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4}),
    TelFits (model P μ p) (σOf vs) (fd p).params ρ0 ps →
    TelFits (model P μ p) (σOf vs) (fields p j) (push ps ρ0) xs →
    SmallAlong (model P μ p) (σOf vs)
      (W4 (evalTotal (σOf vs) (fd p).resLevel)) (fields p j) (push ps ρ0) xs →
    PiSmallMaskShape.TupleMask (model P μ p) (mkM P μ) (σOf vs)
      (specs (p.constructors j).fields) (push ps ρ0) (push ps ρ0) xs

def BoundedReachedMasks (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (K : Nat → Nat) : Prop :=
  ∀ vs : List Nat, vs.length = p.node.a.family.member.arity →
    (∀ v, v ∈ vs → v ≤ K p.rr) → ReachedMasksAt P μ p vs

/-- Closure at this world uses only the exact mask at its canonical
vector. Global admissibility is independent of that mask. -/
theorem closed_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hType : UniformType p.node.a.family.resultLevel)
    (vs : List Nat)
    (hmasks : ReachedMasksAt P μ p (PiSmallFrame.canonical p.node.a.family.member.arity vs)) :
    ∀ i z, CtorAt P μ (fd p) (candidate P μ p) vs i z →
      z ∈ candidate P μ p vs i := by
  have hB := EvalPlanNormal.bounded_of_group p fm ctors hE hmem
  obtain ⟨_, _, hfree, _, _, _⟩ := CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  intro i z hz
  let ws := PiSmallFrame.canonical p.node.a.family.member.arity vs
  let M := model P μ p
  let N := mkM P μ
  have hcan : PiSmallFrame.canonical p.node.a.family.member.arity ws = ws :=
    PiSmallFrame.canonical_idem _ vs
  have hn : evalTotal (σOf ws) (fd p).resLevel ≠ 0 := Nat.ne_of_gt (hType _)
  obtain ⟨j, ps, xs, hp, hx, hs, hi, he⟩ :=
    PiSmallFrame.ctorAt_canonical P μ (fd p) _ hB (candidate P μ p) vs i z hz
  rw [if_neg hn] at hs he
  have hc := EvalPlanNormal.ctor_get p j
  rw [hc] at hx hs hi
  apply (PiSmallFrame.candidate_mem_iff P N (fd p) _ (syntaxView p) vs i z).mpr
  intro ps' hprefix
  have hps : LEq ps ps' := paramKey_reflect (fd p).params.length ps ps'
    ((p.node.a.constructorViews (index p j)).resultIndices.map
      (den M (σOf ws) (push xs (push ps ρ0)))) hp.length
    (by rw [← hi]; exact hprefix.symm)
  have henv : ∀ k, Equiv (push ps ρ0 k) (push ps' ρ0 k) :=
    push_congr hps (fun _ => Equiv.rfl)
  have hp' := TelFits_congr M (σOf ws) (fd p).params
    (fun _ => Equiv.rfl) hps hp
  have hx' := TelFits_congr M (σOf ws) (fields p (index p j)) henv (LEq.refl xs) hx
  have hs' := SmallAlong_congr M (σOf ws) (W4 (evalTotal (σOf ws) (fd p).resLevel))
    (fields p (index p j)) henv (LEq.refl xs) hs
  have hmask := hmasks (index p j) ps' xs hp' hx' hs'
  have hleaf := cached_leaves P μ (fd p) p.node.a.family.member.arity (syntaxView p)
    hB hfree ws hcan (p.constructors (index p j)).fields ps' [] hp'.length rfl xs hx'
  have hproduced := PiSmallFrame.fibre_produce P M N rfl (σOf ws)
    (syntaxView p) ps' (fd p).fref (canonL p.node.a.family.member.arity)
    (syntaxIndex p j) xs (evalTotal (σOf ws) (fd p).resLevel) hn
    (by rw [syntax_get]; exact hx')
    (by rw [syntax_get]; exact hs')
    (by rw [syntax_get]; exact hmask)
    (by rw [syntax_get]; exact hleaf)
  rw [syntax_get] at hproduced
  have hread :
      (p.node.a.constructorViews (index p j)).resultIndices.map
        (den M (σOf ws) (push xs (push ps' ρ0))) =
      (p.node.a.constructorViews (index p j)).resultIndices.map
        (den N (σOf ws) (push xs (push ps' ρ0))) :=
    List.map_congr_left fun e he => den_off P μ (fd p).fref
      (ofFrame P μ (fd p) (candidate P μ p)) (σOf ws) (push xs (push ps' ρ0))
      ((p.node.a.constructorViews (index p j)).noFamilyInIndices e he)
  have hkey : i = key (ps' ++ (p.node.a.constructorViews (index p j)).resultIndices.map
      (den N (σOf ws) (push xs (push ps' ρ0)))) := by
    calc
      i = key (ps ++ (p.node.a.constructorViews (index p j)).resultIndices.map
          (den M (σOf ws) (push xs (push ps ρ0)))) := hi
      _ = key (ps' ++ (p.node.a.constructorViews (index p j)).resultIndices.map
          (den M (σOf ws) (push xs (push ps' ρ0)))) :=
        (key_eq_iff _ _).mpr (LEq_append hps
          (LEq_map_den M (σOf ws) (push_congr (LEq.refl xs) henv) _))
      _ = _ := congrArg (fun is => key (ps' ++ is)) hread
  rw [hkey]
  exact mem_congr_left he.symm hproduced

/-- The local existence witness is this candidate's entire canonical
fibre. No global constructor closure is supplied. -/
theorem exists_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hType : UniformType p.node.a.family.resultLevel)
    (vs : List Nat)
    (hmasks : ReachedMasksAt P μ p (PiSmallFrame.canonical p.node.a.family.member.arity vs)) :
    PointwiseData.ExistsAt P μ (fd p) p.node.a.family.member.arity
      (PiSmallFrame.canonical p.node.a.family.member.arity vs) := by
  let ws := PiSmallFrame.canonical p.node.a.family.member.arity vs
  have hw : PiSmallFrame.canonical p.node.a.family.member.arity ws = ws :=
    PiSmallFrame.canonical_idem _ vs
  apply PointwiseData.exists_of_candidate P μ p fm ctors hE hmem
    (candidate P μ p) (NormSmallFrame.admissible P μ p fm ctors hE hmem) ws hw
  apply closed_at P μ p fm ctors hE hmem hType ws
  rw [hw]
  exact hmasks

/-- The checked world's literal vector bound is retained. Canonicalizing
an already arity-correct vector changes no entry and supplies no new bound. -/
theorem local_candidates (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hType : UniformType p.node.a.family.resultLevel) (K : Nat → Nat)
    (hmasks : BoundedReachedMasks P μ p K) :
    PointwiseDataLocal.LocalCandidates P μ p K := by
  intro vs hvl hvs
  have hcan : PiSmallFrame.canonical p.node.a.family.member.arity vs = vs := by
    change (canonL p.node.a.family.member.arity).map (evalTotal (σOf vs)) = vs
    rw [← hvl]
    exact map_param_σOf vs
  apply exists_at P μ p fm ctors hE hmem hType vs
  rw [hcan]
  exact hmasks vs hvl hvs

end Rcic.F3.PSet.NormSmallFrameLocal
