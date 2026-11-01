import rcic.RcicF3PointwiseData
import rcic.RcicF3EvalPlanNormalSlice
import rcic.RcicF3EvalPlanNormalMono
import rcic.RcicF3EvalPlanNormalLevels

/-!
# Actual normalized constructors read one canonical family world

The retained normalized syntax supplies every locality condition used
below: family-free parameters, family-free recursive domains and complete
arguments, canonical family levels, and family-free result indices. The
actual prior field values and complete parameter/index keys are unchanged.

Consequently, a candidate that is globally admissible and closed only at
one canonical world supplies that world's PointwiseData.ExistsAt. Global
closure is not an input to this adapter. Closure of the alternative frame
at a given world uses existence only there; its density uses no separate
existence premise because membership supplies one.

This module does not produce the remaining bounded masks, install a new
role, or identify either old invariant with a new one. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseData
open Rcic.Declarative PiIndex RawFamily PiValueRule

/-- A normalized constructor depends on its candidate only at the one
canonical world read by every complete recursive family application. -/
theorem ctorAt_sub_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (spec : Fin fd.ctors.length → List FieldSpec)
    (hP : ∀ A ∈ fd.params, occursConst fd.fref A = false)
    (hF : ∀ j, (fd.ctors.get j).1 = (spec j).map (fieldExpr fd.fref (canonL ar)))
    (hClean : ∀ j, Clean fd.fref (fd.params ++ fd.indices).length (spec j))
    (hR : ∀ j, ∀ A ∈ (fd.ctors.get j).2, occursConst fd.fref A = false)
    (C D : Frame) (hC : Admissible fd C) (hD : Admissible fd D)
    (w : List Nat) (hw : PiSmallFrame.canonical ar w = w)
    (hsub : ∀ i, Sub (C w i) (D w i)) (i : Index.{4}) (z : PSet.{4})
    (hz : CtorAt P μ fd C w i z) : CtorAt P μ fd D w i z := by
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  let X := ofFrame P μ fd C
  let Y := ofFrame P μ fd D
  have hworld : (canonL ar).map (evalTotal (σOf w)) = w := hw
  have hL : evalTotal (σOf ((canonL ar).map (evalTotal (σOf w)))) fd.resLevel =
      evalTotal (σOf w) fd.resLevel :=
    congrArg (fun vs => evalTotal (σOf vs) fd.resLevel) hworld
  have hpD : TelFits (mkM P (upd μ fd.fref Y)) (σOf w) fd.params ρ0 ps := by
    apply TelFits_mono fd.params (M₁ := mkM P (upd μ fd.fref X)) _ ρ0 ps hp
    intro A hA ρ x hx
    change x ∈ Ed (mkM P μ) (den (mkM P (upd μ fd.fref X)) (σOf w) ρ A) at hx
    change x ∈ Ed (mkM P μ) (den (mkM P (upd μ fd.fref Y)) (σOf w) ρ A)
    rw [← PiIndependent.den_free P μ fd.fref X Y (σOf w) A (hP A hA) ρ]
    exact hx
  have hxD : TelFits (mkM P (upd μ fd.fref Y)) (σOf w) (fd.ctors.get j).1
      (push ps ρ0) xs := by
    rw [hF j] at hx ⊢
    apply PiTupleMono.fits_mono P μ fd.fref (fd.params ++ fd.indices).length
      X Y (σOf w) (canonL ar) ?_ (spec j) (hClean j) _ xs hx
    intro ys hy
    rw [hworld]
    exact EvalPlanNormalSlice.application_sub_at P μ fd C D hC hD w ys hy
      (hsub (key ys))
  have hsD : if evalTotal (σOf w) fd.resLevel = 0 then True else
      SmallAlong (mkM P (upd μ fd.fref Y)) (σOf w)
        (W4 (evalTotal (σOf w) fd.resLevel)) (fd.ctors.get j).1 (push ps ρ0) xs := by
    split
    · trivial
    · rename_i h0
      rw [if_neg h0] at hs
      rw [hF j] at hx hs ⊢
      have h0' : evalTotal (σOf ((canonL ar).map (evalTotal (σOf w))))
          fd.resLevel ≠ 0 := by
        simpa only [hworld] using h0
      exact PiTupleMono.smallAlong P μ fd.fref (fd.params ++ fd.indices).length
        X Y (σOf w) (canonL ar) _ (stageW4 P _)
        (fun ys hy hm =>
          (apply_ofFrame_data P μ fd C hC _ h0' ys hy).2 pempty hm Equiv.rfl)
        (fun ys hy => by
          have h := (apply_ofFrame_data P μ fd D hD _ h0' ys hy).1
          rw [hL] at h
          exact h) (spec j) (hClean j) _ xs hx hs
  have he : (fd.ctors.get j).2.map (den (mkM P (upd μ fd.fref X)) (σOf w)
      (push xs (push ps ρ0))) =
      (fd.ctors.get j).2.map (den (mkM P (upd μ fd.fref Y)) (σOf w)
        (push xs (push ps ρ0))) := by
    apply List.map_congr_left
    intro A hA
    exact PiIndependent.den_free P μ fd.fref X Y (σOf w) A (hR j A hA) _
  change i = key (ps ++ (fd.ctors.get j).2.map
    (den (mkM P (upd μ fd.fref X)) (σOf w) (push xs (push ps ρ0)))) at hi
  rw [he] at hi
  exact ⟨j, ps, xs, hpD, hxD, hsD, hi, hz⟩

/-- All locality inputs are produced by this actual retained admission. -/
theorem ctorAt_sub_of_plan (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (C D : Frame) (hC : Admissible (EvalPlanNormal.fd p) C)
    (hD : Admissible (EvalPlanNormal.fd p) D)
    (w : List Nat) (hw : PiSmallFrame.canonical p.node.a.family.member.arity w = w)
    (hsub : ∀ i, Sub (C w i) (D w i)) (i : Index.{4}) (z : PSet.{4})
    (hz : CtorAt P μ (EvalPlanNormal.fd p) C w i z) :
    CtorAt P μ (EvalPlanNormal.fd p) D w i z := by
  obtain ⟨_, _, hfree, _, _, _⟩ := CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  apply ctorAt_sub_at P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity
    (fun j => EvalPlanNormal.specs
      (p.constructors (EvalPlanNormal.index p j)).fields)
    ?_ ?_ ?_ ?_ C D hC hD w hw hsub i z hz
  · intro A hA
    exact hfree A (List.mem_append_left _ hA)
  · intro j
    rw [EvalPlanNormal.ctor_get]
    rfl
  · intro j
    simpa only [EvalPlanNormal.fd, famDataOf, List.length_append] using
      EvalPlanNormal.specs_clean (p.constructors (EvalPlanNormal.index p j)).fields
  · intro j A hA
    rw [EvalPlanNormal.ctor_get] at hA
    exact (p.node.a.constructorViews (EvalPlanNormal.index p j)).noFamilyInIndices A hA

/-- A supplied globally admissible candidate needs closure only at this
one world. This is the interface for a future bounded mask producer. -/
theorem exists_of_candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (C : Frame) (hC : Admissible (EvalPlanNormal.fd p) C)
    (w : List Nat) (hw : PiSmallFrame.canonical p.node.a.family.member.arity w = w)
    (hc : ∀ i z, CtorAt P μ (EvalPlanNormal.fd p) C w i z → z ∈ C w i) :
    ExistsAt P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity w := by
  have hB := EvalPlanNormal.bounded_of_group p fm ctors hE hmem
  refine ⟨C w, hC w, ?_⟩
  intro i z hz
  apply hc i z
  apply ctorAt_sub_of_plan P μ p fm ctors hE hmem
    (embed p.node.a.family.member.arity w (C w)) C
    (embed_admissible P _ _ hB w (C w) (hC w)) hC w hw ?_ i z hz
  intro k x hx
  rw [embed_at _ w hw] at hx
  exact hx

/-- Family-level transport changes neither the full key nor the output.
It also permits returning from the canonical world to a short/extra vector. -/
theorem ctorAt_levels (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar) (C : Frame)
    (vs ws : List Nat) (hσ : ∀ k, k < ar → σOf vs k = σOf ws k)
    (i : Index.{4}) (z : PSet.{4}) (hz : CtorAt P μ fd C vs i z) :
    CtorAt P μ fd C ws i z := by
  obtain ⟨j, ps, xs, hp, hx, hs, hi, he⟩ := hz
  let M := mkM P (table P μ fd C)
  have hk := evalTotal_agree hσ fd.resLevel hB.res
  have hc : fd.ctors.get j ∈ fd.ctors := List.getElem_mem j.isLt
  have hb := hB.ctors _ hc
  refine ⟨j, ps, xs, (TelFits_levels M hσ _ hB.params ρ0 ps).mp hp,
    (TelFits_levels M hσ _ hb.1 (push ps ρ0) xs).mp hx, ?_, ?_, ?_⟩
  · by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
    · rw [if_pos (hk.symm.trans h0)]
      trivial
    · have hn : evalTotal (σOf ws) fd.resLevel ≠ 0 := fun h => h0 (hk.trans h)
      rw [if_neg h0] at hs
      rw [if_neg hn]
      rw [hk] at hs
      exact (PiSmallFrame.smallAlong_levels M hσ _ _ hb.1 (push ps ρ0) xs).mp hs
  · rw [← map_den_levels M hσ _ hb.2]
    exact hi
  · rw [← hk]
    exact he

/-- Closure at an arbitrary supplied vector needs a local candidate only
at that vector's canonical family world, with no restriction on its values. -/
theorem frame_closed_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (vs : List Nat)
    (hex : ExistsAt P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity
      (PiSmallFrame.canonical p.node.a.family.member.arity vs))
    (i : Index.{4}) (z : PSet.{4})
    (hz : CtorAt P μ (EvalPlanNormal.fd p)
      (frame P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity) vs i z) :
    z ∈ frame P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity vs i := by
  let d := EvalPlanNormal.fd p
  let ar := p.node.a.family.member.arity
  let w := PiSmallFrame.canonical ar vs
  let L := localFrame P μ d ar w
  let F := frame P μ d ar
  have hw : PiSmallFrame.canonical ar w = w := PiSmallFrame.canonical_idem ar vs
  have hB := EvalPlanNormal.bounded_of_group p fm ctors hE hmem
  have hm := EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem
  have hF := frame_admissible P μ d ar hB
  have hL := local_admissible P μ d ar w
  have hzW := PiSmallFrame.ctorAt_canonical P μ d ar hB F vs i z hz
  have hzL : CtorAt P μ d (embed ar w L) w i z := by
    apply ctorAt_sub_of_plan P μ p fm ctors hE hmem F (embed ar w L)
      hF (embed_admissible P d ar hB w L hL) w hw ?_ i z hzW
    intro k x hx
    rw [embed_at ar w hw]
    change x ∈ localFrame P μ d ar (PiSmallFrame.canonical ar w) k at hx
    rw [hw] at hx
    exact hx
  exact local_closed P μ d ar hB hm w hex i z hzL

/-- Actual frame density returns to the caller's original vector. No
candidate-existence premise, global closure, or bound is added. -/
theorem frame_dense (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (vs : List Nat) (i : Index.{4}) (z : PSet.{4})
    (hz : z ∈ frame P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity vs i) :
    CtorAt P μ (EvalPlanNormal.fd p)
      (frame P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity) vs i z := by
  let d := EvalPlanNormal.fd p
  let ar := p.node.a.family.member.arity
  let w := PiSmallFrame.canonical ar vs
  let L := localFrame P μ d ar w
  let F := frame P μ d ar
  have hw : PiSmallFrame.canonical ar w = w := PiSmallFrame.canonical_idem ar vs
  have hB := EvalPlanNormal.bounded_of_group p fm ctors hE hmem
  have hm := EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem
  have hL := local_admissible P μ d ar w
  have hF := frame_admissible P μ d ar hB
  have hzL := local_dense P μ d ar hB hm w i z hz
  have hzF : CtorAt P μ d F w i z := by
    apply ctorAt_sub_of_plan P μ p fm ctors hE hmem (embed ar w L) F
      (embed_admissible P d ar hB w L hL) hF w hw ?_ i z hzL
    intro k x hx
    rw [embed_at ar w hw] at hx
    change x ∈ localFrame P μ d ar (PiSmallFrame.canonical ar w) k
    rw [hw]
    exact hx
  exact ctorAt_levels P μ d ar hB F w vs
    (fun k hk => (PiSmallFrame.canonical_agree ar vs k hk).symm) i z hzF

end Rcic.F3.PSet.PointwiseData
