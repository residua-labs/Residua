import rcic.RcicF3DMinor
import rcic.RcicF3EvalPlanNormal
import rcic.RcicF3EvalPlanValue

/-!
# Operational endpoint compatibility on the A-negative domain

The actual admitted shapes, not a chosen replacement plan, determine the
raw recursor's operational field depths when NoFunRec holds. The existing
ShapesNorm producer supplies both raw occurrence flags and depth zero.
The retained cache also agrees with the existing normalized D descriptor.

This proves exact endpoint and stored-abstraction compatibility for the
data/propOnly fallback. The typed indexed Prop/anySort branch is not
identified with the old unguarded endpoint. No family fixed point, frame
closure, environment invariant, universe bound or semantic normalization
callback is assumed by these syntactic comparisons. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormDPlanBridge
open Rcic.Declarative

/-- Every field's raw occurrence/depth calculation is its admitted shape. -/
theorem raw_shapes {E : ResolvedEnv} {fuel f : Nat}
    {ss : List FieldShape} {Fs Fs' : List (Expr Nat)}
    (h : ShapesNorm E fuel f ss Fs Fs') :
    Fs.map (RecPlan.rawShape f) = ss := by
  apply List.ext_getElem
  · exact (List.length_map _ _).trans h.1.symm
  · intro k hkL hkR
    have hk : k < Fs.length := by
      simpa only [List.length_map] using hkL
    have hk' : k < Fs'.length := by
      rw [h.2.1]
      exact hk
    have hh := h.2.2 k ss[k] Fs[k] Fs'[k]
      (List.getElem?_eq_getElem hkR) (List.getElem?_eq_getElem hk)
      (List.getElem?_eq_getElem hk')
    rw [List.getElem_map]
    rcases hh with ⟨hs, ho, _⟩ | ⟨hs, ho, _, ht⟩
    · simp only [RecPlan.rawShape, ho, Bool.false_eq_true, if_false]
      exact hs.symm
    · rw [RecPlan.rawShape, ho, if_pos rfl, ihDepth_eq_zero_of_telNil ht]
      exact hs.symm

/-- Read uniqueness aligns every cached field with the D normalizer. The
comparison preserves the complete terminal argument list and original scope. -/
theorem cache_fields {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (h : ShapesNorm E fuel f ss Fs (Fs.map (normField E fuel f))) :
    (EvalPlanNormal.specs p).map (PiValueRule.fieldExpr f (canonL nu)) =
      Fs.map (normField E fuel f) := by
  revert h
  induction p with
  | nil => intro _; rfl
  | @cons prior s A ss Fs head tail ih =>
      intro h
      have hh := h.2.2 0 s A (normField E fuel f A)
        (by simp only [List.getElem?_cons_zero])
        (by simp only [List.getElem?_cons_zero])
        (by simp only [List.map_cons, List.getElem?_cons_zero])
      have hhead : PiValueRule.fieldExpr f (canonL nu)
          (EvalPlanNormal.fieldSpec head) = normField E fuel f A := by
        cases head with
        | plain hf => exact (normField_free hf).symm
        | recursive r =>
            rcases hh with ⟨hs, _, _⟩ | ⟨_, _, _, ht⟩
            · exact False.elim (FieldShape.noConfusion hs)
            · have he := Option.some.inj (r.read.symm.trans ht)
              have hd : r.domains = [] := congrArg Prod.fst he
              have hb : foldApps (.const f (canonL nu)) r.arguments =
                  normField E fuel f A := congrArg Prod.snd he
              change policyPi r.domains
                (foldApps (.const f (canonL nu)) r.arguments) = _
              rw [hd, hb]
              rfl
      have htail : ShapesNorm E fuel f ss Fs (Fs.map (normField E fuel f)) := by
        refine ⟨Nat.succ.inj h.1, List.length_map _ _, ?_⟩
        intro k t B B' hs hB hB'
        exact h.2.2 (k + 1) t B B'
          (by simpa only [List.getElem?_cons_succ] using hs)
          (by simpa only [List.getElem?_cons_succ] using hB)
          (by simpa only [List.map_cons, List.getElem?_cons_succ] using hB')
      change PiValueRule.fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec head) ::
        (EvalPlanNormal.specs tail).map (PiValueRule.fieldExpr f (canonL nu)) =
          normField E fuel f A :: Fs.map (normField E fuel f)
      rw [hhead, ih htail]

/-- No change of the actual constructor node or its stored plan is needed. -/
theorem node_raw_plan {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref) (hN : NoFunRec node) :
    RecPlan.rawPlan (famDataOf node.a) = RecPlan.nodePlan node := by
  apply List.ext_getElem
  · simp only [RecPlan.rawPlan, RecPlan.nodePlan, List.length_map,
      List.length_range, famDataOf_ctors_length]
  · intro k hkL hkR
    have hk : k < node.a.constructors.length := by
      simpa only [RecPlan.nodePlan, List.length_map, List.length_range] using hkR
    let j : Fin node.a.constructors.length := ⟨k, hk⟩
    have hS := shapesNorm_of_fieldShapesFuel hFF (node.a.constructorViews j).fields
      node.a.family.parameters.length (node.h14.shapesAt j)
      (node.h14.analyzed j) (hN j)
    have hL : (RecPlan.rawPlan (famDataOf node.a))[k]? =
        some (node.h14.shapesAt j) := by
      unfold RecPlan.rawPlan
      rw [List.getElem?_map, famDataOf_ctor node.a j]
      change some ((node.a.constructorViews j).fields.map
        (RecPlan.rawShape node.a.family.ref)) = some (node.h14.shapesAt j)
      rw [raw_shapes hS]
    have hR : (RecPlan.nodePlan node)[k]? = some (node.h14.shapesAt j) :=
      (RecPlan.nodePlan_spec node j).1
    rw [List.getElem?_eq_getElem hkL] at hL
    rw [List.getElem?_eq_getElem hkR] at hR
    exact Option.some.inj (hL.trans hR.symm)

theorem normalized_fields (p : EvalPlan.Plan)
    (hFF : FamFreeBodies p.node.E0 p.node.a.family.ref) (hN : NoFunRec p.node)
    (j : Fin p.node.a.constructors.length) :
    EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields.map
      (normField p.node.E0 (p.node.h14.fuelAt j) p.node.a.family.ref) := by
  have hN' : ∀ s, s ∈ (p.constructors j).shapes →
      s = .nonrecursive ∨ s = .recursive 0 := by
    intro s hs
    rw [(p.constructors j).shapes_admitted] at hs
    exact hN j s hs
  have hS := shapesNorm_of_fieldShapesFuel hFF (p.node.a.constructorViews j).fields
    p.node.a.family.parameters.length (p.constructors j).shapes
    (p.constructors j).analyzed hN'
  have he := cache_fields (p.constructors j).fields hS
  change EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields.map
    (normField p.node.E0 (p.constructors j).fuel p.node.a.family.ref) at he
  rw [(p.constructors j).fuel_admitted] at he
  exact he

/-- The entire cached descriptor is the existing D descriptor, including
constructor order, parameter/index telescopes, result keys and policy. -/
theorem normalized_descriptor (p : EvalPlan.Plan)
    (hFF : FamFreeBodies p.node.E0 p.node.a.family.ref) (hN : NoFunRec p.node) :
    EvalPlanNormal.fd p = nodeFam p.node := by
  have hct : EvalPlanNormal.constructors p = (nodeFam p.node).ctors := by
    apply List.ext_getElem
    · exact (EvalPlanNormal.ctors_length p).trans (nodeFam_ctors_length p.node).symm
    · intro k hkL hkR
      let j : Fin p.node.a.constructors.length :=
        ⟨k, by simpa only [nodeFam_ctors_length] using hkR⟩
      have hL := EvalPlanNormal.ctor_get p ⟨k, hkL⟩
      have hj : EvalPlanNormal.index p ⟨k, hkL⟩ = j := Fin.ext rfl
      rw [hj, normalized_fields p hFF hN j] at hL
      have hR := nodeFam_ctor p.node j
      rw [List.getElem?_eq_getElem hkR] at hR
      exact hL.trans (Option.some.inj hR).symm
  exact congrArg (fun cs => { famDataOf p.node.a with ctors := cs }) hct

/-- Actual group freshness produces the syntactic body condition; it is
not a new semantic premise of the checked group consumer. -/
theorem bodies_of_group {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) : FamFreeBodies node.E0 node.a.family.ref := by
  rw [node.fam]
  exact famFreeBodies_node hE (groupMembersT_head_fresh hmem) hmem node

theorem node_raw_plan_of_group {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hN : NoFunRec node) :
    RecPlan.rawPlan (famDataOf node.a) = RecPlan.nodePlan node :=
  node_raw_plan node (bodies_of_group hE hmem node) hN

/-- The compatibility hypothesis cannot silently absorb a positive-depth
PendA row. This is a boundary of this adapter, not of the full A target. -/
theorem not_noFun_of_pendA {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    {node : RecNode E E' f rr rm} (hA : PendA node) : ¬ NoFunRec node := by
  intro hN
  obtain ⟨j, k, m, hs⟩ := hA
  rcases hN j (.recursive (m + 1)) (List.getElem?_mem hs) with h | h
  · exact FieldShape.noConfusion h
  · exact Nat.noConfusion (FieldShape.recursive.inj h)

/-- Exact original endpoint at every local environment on the fallback face. -/
theorem endpoint_fallback (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hFF : FamFreeBodies p.node.E0 p.node.a.family.ref) (hN : NoFunRec p.node)
    (hn : ¬ (evalTotal σ p.node.a.family.resultLevel = 0 ∧
      p.node.a.policy = .anySort)) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ p ρ = recEnd M σ (famDataOf p.node.a) ρ := by
  rw [EvalPlanValue.endValue_fallback M σ p ρ hn, ← node_raw_plan p.node hFF hN]
  exact (RecPlanValue.laws M σ (famDataOf p.node.a)
    (RecPlan.rawPlan (famDataOf p.node.a))).2 ρ

theorem member_fallback (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hFF : FamFreeBodies p.node.E0 p.node.a.family.ref) (hN : NoFunRec p.node)
    (hn : ¬ (evalTotal σ p.node.a.family.resultLevel = 0 ∧
      p.node.a.policy = .anySort)) (m : CheckedMember) :
    EvalPlanValue.memberValue M σ p m =
      piLam M σ (recEnd M σ (famDataOf p.node.a)) ρ0 m.mtype := by
  unfold EvalPlanValue.memberValue
  rw [funext (endpoint_fallback M σ p hFF hN hn)]

theorem endpoint_data (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hFF : FamFreeBodies p.node.E0 p.node.a.family.ref) (hN : NoFunRec p.node)
    (hData : evalTotal σ p.node.a.family.resultLevel ≠ 0) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ p ρ = recEnd M σ (famDataOf p.node.a) ρ :=
  endpoint_fallback M σ p hFF hN (fun h => hData h.1) ρ

/-- On a uniformly Prop propOnly family the plan is never read. This
stronger compatibility does not require NoFunRec and proves no typing. -/
theorem endpoint_propOnly (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hPolicy : p.node.a.policy = .propOnly) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ p ρ = recEnd M σ (famDataOf p.node.a) ρ := by
  have hn : ¬ (evalTotal σ p.node.a.family.resultLevel = 0 ∧
      p.node.a.policy = .anySort) := by
    intro h
    rw [hPolicy] at h
    cases h.2
  rw [EvalPlanValue.endValue_fallback M σ p ρ hn]
  unfold RecPlanValue.endValue
  rw [cond_pos (show evalTotal σ (famDataOf p.node.a).resLevel = 0 from hProp σ)]

theorem member_propOnly (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hPolicy : p.node.a.policy = .propOnly) (m : CheckedMember) :
    EvalPlanValue.memberValue M σ p m =
      piLam M σ (recEnd M σ (famDataOf p.node.a)) ρ0 m.mtype := by
  unfold EvalPlanValue.memberValue
  rw [funext (endpoint_propOnly M σ p hProp hPolicy)]

end Rcic.F3.PSet.NormDPlanBridge
