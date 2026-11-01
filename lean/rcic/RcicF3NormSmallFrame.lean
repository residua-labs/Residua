import rcic.RcicF3PiSmallFrame
import rcic.RcicF3EvalPlanNormalLevels
import rcic.RcicF3EvalPlanNormalSlice

/-!
# All-instance assembly from the actual normalized small signatures

The candidate uses the actual cached ordinary and recursive fields, full
recursive argument lists, constructor tags and original result indices.
The leaf inclusion required by the small signature is produced from its
own candidate membership and the cache's parameter-prefix equation.
Parameter representatives are handled by intersection and transport of
the same fitting field tuple. No quotient representative is selected.

ReachedMasks is the exact remaining internal domain-only obligation. It
concerns fitting normalized tuples in this constructed candidate model;
it is not a constructor, recursor, closure or small-frame callback. This
module does not derive it universally from typed admission, and does not
add it to the checked apex or change either existing check.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormSmallFrame
open Rcic.Declarative PiIndex RawFamily RawFamilyRec
open EvalPlanNormal (fd fields specs index)

/-- Keep every constructor's actual normalized field cache and every
original result expression, in the original order. -/
noncomputable def syntaxView (p : EvalPlan.Plan) : List PiValueRule.Constructor :=
  (List.range p.node.a.constructors.length).map fun j =>
    if hj : j < p.node.a.constructors.length then
      ⟨specs (p.constructors ⟨j, hj⟩).fields,
        (p.node.a.constructorViews ⟨j, hj⟩).resultIndices⟩
    else ⟨[], []⟩

theorem syntax_length (p : EvalPlan.Plan) :
    (syntaxView p).length = p.node.a.constructors.length := by
  simp only [syntaxView, List.length_map, List.length_range]

noncomputable def syntaxIndex (p : EvalPlan.Plan) (j : Fin (fd p).ctors.length) :
    Fin (syntaxView p).length :=
  ⟨j.val, by simpa only [syntax_length, EvalPlanNormal.ctors_length] using j.isLt⟩

theorem syntax_get (p : EvalPlan.Plan) (j : Fin (fd p).ctors.length) :
    (syntaxView p)[syntaxIndex p j] =
      ⟨specs (p.constructors (index p j)).fields,
        (p.node.a.constructorViews (index p j)).resultIndices⟩ := by
  change (syntaxView p)[j.val]'(syntaxIndex p j).isLt = _
  simp only [syntaxView, List.getElem_map, List.getElem_range]
  have hj : j.val < p.node.a.constructors.length := (index p j).isLt
  rw [dif_pos hj]
  apply congrArg (fun k : Fin p.node.a.constructors.length =>
    (⟨specs (p.constructors k).fields,
      (p.node.a.constructorViews k).resultIndices⟩ : PiValueRule.Constructor))
  apply Fin.ext
  simp only [List.getElem_range, index]

noncomputable def candidate (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan) : Frame :=
  PiSmallFrame.candidate P (mkM P μ) (fd p)
    p.node.a.family.member.arity (syntaxView p)

noncomputable abbrev model (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan) : Interp.{4} :=
  mkM P (table P μ (fd p) (candidate P μ p))

/-- Only reached domain independence remains. Ordinary values are kept;
the recursive slots are masked only for the branch-domain topology. The
full child and result expressions retain every actual recursive value. -/
def ReachedMasks (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) : Prop :=
  ∀ vs : List Nat, vs.length = p.node.a.family.member.arity →
    ∀ (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4}),
      TelFits (model P μ p) (σOf vs) (fd p).params ρ0 ps →
      TelFits (model P μ p) (σOf vs) (fields p j) (push ps ρ0) xs →
      SmallAlong (model P μ p) (σOf vs)
        (W4 (evalTotal (σOf vs) (fd p).resLevel)) (fields p j) (push ps ρ0) xs →
      PiSmallMaskShape.TupleMask (model P μ p) (mkM P μ) (σOf vs)
        (specs (p.constructors j).fields) (push ps ρ0) (push ps ρ0) xs

/-- The child enters the correct per-parameter signature at its literal
complete key. Invalid complete family applications supply no children. -/
theorem recursive_leaf (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (d : FamData) (ar : Nat) (cs : List PiValueRule.Constructor)
    (hB : FamBounded d ar)
    (hfree : ∀ e ∈ d.params ++ d.indices, occursConst d.fref e = false)
    (vs : List Nat) (hcan : PiSmallFrame.canonical ar vs = vs)
    {E : ResolvedEnv} {fuel prior inner : Nat} {A : Expr Nat}
    (r : EvalPlan.Recursive E fuel d.fref ar d.params.length d.indices.length
      prior A inner)
    (ps pre : List PSet.{4}) (hps : ps.length = d.params.length)
    (hpre : pre.length = prior) (zs : List PSet.{4})
    (hzs : TelFits
      (mkM P (table P μ d (PiSmallFrame.candidate P (mkM P μ) d ar cs)))
      (σOf vs) r.domains (push pre (push ps ρ0)) zs) :
    let C := PiSmallFrame.candidate P (mkM P μ) d ar cs
    let M := mkM P (table P μ d C)
    Sub (Ed M (den M (σOf vs) (push zs (push pre (push ps ρ0)))
      (foldApps (.const d.fref (canonL ar)) r.arguments)))
      (PiSmallFrame.fibre P (mkM P μ) (σOf vs) cs ps
        (evalTotal (σOf vs) d.resLevel)
        (read (mkM P μ) (σOf vs) r.arguments (push zs (push pre (push ps ρ0))))) := by
  dsimp only
  let C := PiSmallFrame.candidate P (mkM P μ) d ar cs
  let M := mkM P (table P μ d C)
  let ρ := push zs (push pre (push ps ρ0))
  have hC := PiSmallFrame.candidate_admissible P (mkM P μ) d ar cs hB
  have hargs : r.arguments.map (den M (σOf vs) ρ) =
      r.arguments.map (den (mkM P μ) (σOf vs) ρ) :=
    List.map_congr_left fun e he => den_off P μ d.fref (ofFrame P μ d C)
      (σOf vs) ρ (r.arguments_free e he)
  intro z hz
  rw [den_foldApps] at hz
  change z ∈ Ed M (fapps (M.μ d.fref (PiSmallFrame.canonical ar vs))
    (r.arguments.map (den M (σOf vs) ρ))) at hz
  rw [hcan] at hz
  have hd := (apply_updated_mem_iff P μ d C hC hfree vs
    (r.arguments.map (den M (σOf vs) ρ))
    ((List.length_map _ _).trans
      (by simpa only [List.length_append] using r.argument_count)) z).mp hz
  have hp := EvalPlanNormalSlice.parameter_key M (σOf vs) r ps pre hps hpre zs hzs.length
  have h := PiSmallFrame.candidate_sub P (mkM P μ) d ar cs vs
    (key (r.arguments.map (den M (σOf vs) ρ))) ps hp.symm z hd.2
  rw [hcan, hargs] at h
  exact h

/-- Every reached leaf in the actual cache gets its same-parameter
inclusion. No leaf evaluation or family closure is assumed. -/
theorem cached_leaves (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (d : FamData) (ar : Nat) (cs : List PiValueRule.Constructor)
    (hB : FamBounded d ar)
    (hfree : ∀ e ∈ d.params ++ d.indices, occursConst d.fref e = false)
    (vs : List Nat) (hcan : PiSmallFrame.canonical ar vs = vs)
    {E : ResolvedEnv} {fuel prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (cache : EvalPlan.Fields E fuel d.fref ar d.params.length d.indices.length prior ss Fs) :
    ∀ (ps pre : List PSet.{4}), ps.length = d.params.length → pre.length = prior →
      ∀ xs : List PSet.{4},
      TelFits
        (mkM P (table P μ d (PiSmallFrame.candidate P (mkM P μ) d ar cs)))
        (σOf vs) ((specs cache).map (PiValueRule.fieldExpr d.fref (canonL ar)))
        (push pre (push ps ρ0)) xs →
      PiSmallMaskShape.Leaves
        (mkM P (table P μ d (PiSmallFrame.candidate P (mkM P μ) d ar cs)))
        (mkM P μ) (σOf vs) d.fref (canonL ar)
        (PiSmallFrame.fibre P (mkM P μ) (σOf vs) cs ps
          (evalTotal (σOf vs) d.resLevel))
        (specs cache) (push pre (push ps ρ0)) xs := by
  induction cache with
  | nil prior =>
      intro ps pre hps hpre xs hx
      cases xs with
      | nil => trivial
      | cons => exact hx.elim
  | @cons prior s A ss Fs head tail ih =>
      intro ps pre hps hpre xs hx
      cases xs with
      | nil => exact hx.elim
      | cons x xs =>
          have hpre' : (pre ++ [x]).length = prior + 1 := by
            simp only [List.length_append, List.length_singleton, hpre]
          have hρ : push (pre ++ [x]) (push ps ρ0) = vcons x (push pre (push ps ρ0)) := by
            rw [push_append]
            rfl
          have ht := ih ps (pre ++ [x]) hps hpre' xs (by rw [hρ]; exact hx.2)
          rw [hρ] at ht
          cases head with
          | plain => exact ht
          | recursive r =>
              exact ⟨fun zs hzs => recursive_leaf P μ d ar cs hB hfree vs hcan
                r ps pre hps hpre zs hzs, ht⟩

theorem admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E') :
    Admissible (fd p) (candidate P μ p) :=
  PiSmallFrame.candidate_admissible P (mkM P μ) (fd p)
    p.node.a.family.member.arity (syntaxView p)
    (EvalPlanNormal.bounded_of_group p fm ctors hE hmem)

/-- Conditional assembly pays the entire all-vs small-frame conclusion.
Only the reached domain-mask producer remains; full-key child inclusion,
parameter descent, stage choice and constructor composition are proved. -/
theorem closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hType : UniformType p.node.a.family.resultLevel)
    (hmasks : ReachedMasks P μ p) :
    Closed P μ (fd p) (candidate P μ p) := by
  have hB := EvalPlanNormal.bounded_of_group p fm ctors hE hmem
  obtain ⟨_, _, hfree, _, _, _⟩ := CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  intro vs i z hz
  let ws := PiSmallFrame.canonical p.node.a.family.member.arity vs
  let M := model P μ p
  let N := mkM P μ
  have hcan : PiSmallFrame.canonical p.node.a.family.member.arity ws = ws :=
    PiSmallFrame.canonical_idem _ vs
  have hwl : ws.length = p.node.a.family.member.arity := PiSmallFrame.canonical_length _ vs
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
  have hmask := hmasks ws hwl (index p j) ps' xs hp' hx' hs'
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

theorem component (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hType : UniformType p.node.a.family.resultLevel)
    (hmasks : ReachedMasks P μ p) :
    Admissible (fd p) (candidate P μ p) ∧ Closed P μ (fd p) (candidate P μ p) :=
  ⟨admissible P μ p fm ctors hE hmem, closed P μ p fm ctors hE hmem hType hmasks⟩

end Rcic.F3.PSet.NormSmallFrame
