import rcic.RcicF3NormDPlanBridge
import rcic.RcicF3EvalPropRecIota
import rcic.RcicF3DIota

/-!
# A normalized DATA recursor unfolds on the actual legacy witness row

Only the constructor selected by a legacy witness is compared with its
original field list. Its analyzed kinds produce zero-depth shapes, exact
cached-field equality and the direct indexed-field predicate. Other
constructors may have arbitrarily deep recursive fields. No NoFunRec,
raw/normalized fixed-point equality, small frame, semantic child supplier
or iota assumption is used by this operational row theorem.

The theorem is an input to the typed DATA iota composition. By itself it
does not assert that arbitrary recursive calls fit the stored recursor
telescope or that their complete index keys agree. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataIotaRow
open Rcic.Declarative

theorem family_opaque {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    ∀ ls, transparentBody node.E0 node.a.family.ref ls = none := by
  intro ls
  unfold transparentBody
  rw [node.a.family.present]
  show (if transparent node.a.family.member.mclass then _ else none) = none
  rw [node.a.family.hasClass]
  rfl

/-- The row restriction is produced by this row's legacy analysis. -/
theorem row_shapes {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (j : Fin node.a.constructors.length) (ks : List RecKind)
    (hk : analyzeFields node.a.family.ref (node.a.constructorViews j).fields = some ks) :
    ∀ s, s ∈ node.h14.shapesAt j → s = .nonrecursive ∨ s = .recursive 0 := by
  have hs := fieldShapesFuel_eq_kinds hFF (family_opaque node)
    (node.a.constructorViews j).fields node.a.family.parameters.length hk
    (node.h14.analyzed j)
  intro s hm
  rw [hs] at hm
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hm
  cases k with
  | plain => exact Or.inl rfl
  | directRec => exact Or.inr rfl

theorem row_direct {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (j : Fin node.a.constructors.length) (ks : List RecKind)
    (hk : analyzeFields node.a.family.ref (node.a.constructorViews j).fields = some ks) :
    RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length
      (node.a.constructorViews j).fields 0 :=
  recFieldsDirect_of_analyzeFields hFF (family_opaque node) _ _
    (node.h14.analyzed j) (row_shapes node hFF j ks hk) hk

/-- Cached normalization is literally the identity on this witnessed row.
This equality is not asserted for any other constructor. -/
theorem row_fields (p : EvalPlan.Plan)
    (hFF : FamFreeBodies p.node.E0 p.node.a.family.ref)
    (j : Fin p.node.a.constructors.length) (ks : List RecKind)
    (hk : analyzeFields p.node.a.family.ref (p.node.a.constructorViews j).fields = some ks) :
    EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields := by
  have hrow := row_shapes p.node hFF j ks hk
  have hcache : ∀ s, s ∈ (p.constructors j).shapes →
      s = .nonrecursive ∨ s = .recursive 0 := by
    intro s hs
    rw [(p.constructors j).shapes_admitted] at hs
    exact hrow s hs
  have hS := shapesNorm_of_fieldShapesFuel hFF (p.node.a.constructorViews j).fields
    p.node.a.family.parameters.length (p.constructors j).shapes
    (p.constructors j).analyzed hcache
  have h := NormDPlanBridge.cache_fields (p.constructors j).fields hS
  change EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields.map
    (normField p.node.E0 (p.constructors j).fuel p.node.a.family.ref) at h
  have hm : (p.node.a.constructorViews j).fields.map
      (normField p.node.E0 (p.constructors j).fuel p.node.a.family.ref) =
      (p.node.a.constructorViews j).fields := by
    rw [List.map_congr_left (g := id) fun A hA => by
      obtain ⟨k, hA'⟩ := analyzeFields_mem _ hk A hA
      exact normField_eq_self_of_kind (family_opaque p.node) _ hA']
    exact List.map_id _
  exact h.trans hm

/-- Operational depth-zero children need no semantic product witness. -/
theorem children_of_row (f : Nat) (z : PSet.{4}) :
    (ss : List FieldShape) → (xs : List PSet.{4}) →
    (∀ s, s ∈ ss → s = .nonrecursive ∨ s = .recursive 0) →
    RecPlan.Children f z ss xs
  | [], _, _ => True.intro
  | _ :: _, [], _ => True.intro
  | s :: ss, x :: xs, hrow => by
      change (occursConst f (RecPlan.marker f s) = true →
        ihChild z (RecPlan.marker f s) x) ∧ _
      refine ⟨?_, children_of_row f z ss xs
        (fun t ht => hrow t (List.mem_cons_of_mem s ht))⟩
      rcases hrow s (List.mem_cons_self s ss) with hs | hs
      · subst s
        intro _
        exact ihChild_of_depth0 z (A := RecPlan.marker f .nonrecursive) rfl x
      · subst s
        intro _
        exact ihChild_of_depth0 z (A := RecPlan.marker f (.recursive 0)) rfl x

/-- The actual nodeCore unfolds with the original row's indexed IH
argument order. Other rows in nodePlan remain completely unchanged. -/
theorem core_of_row (M : Interp.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (j : Fin node.a.constructors.length) (ks : List RecKind)
    (hk : analyzeFields node.a.family.ref (node.a.constructorViews j).fields = some ks)
    (ms xs : List PSet.{4}) (z : PSet.{4})
    (hl : xs.length = (node.a.constructorViews j).fields.length)
    (hz : Equiv z (dataVal j.val xs)) :
    Equiv (RecPlan.nodeCore M node ms z)
      (fapps (ms.getD j.val pempty)
        (ihArgs node.a.family.ref (RecPlan.nodeCore M node ms)
          (node.a.constructorViews j).fields xs)) := by
  have hrow := row_shapes node hFF j ks hk
  have hS := shapesNorm_of_fieldShapesFuel hFF (node.a.constructorViews j).fields
    node.a.family.parameters.length (node.h14.shapesAt j) (node.h14.analyzed j) hrow
  have hraw := NormDPlanBridge.raw_shapes hS
  have h := RecPlan.core_data M f (RecPlan.nodePlan node) ms
    (RecPlan.nodePlan_spec node j).1 hz
    (hl.trans (RecPlan.nodePlan_spec node j).2.symm)
    (children_of_row f z _ xs hrow)
  change Equiv (RecPlan.nodeCore M node ms z)
    (fapps (ms.getD j.val pempty)
      (RecPlan.args (RecPlan.nodeCore M node ms) (node.h14.shapesAt j) xs)) at h
  rw [← hraw, RecPlan.args_raw] at h
  exact h

/-- Admission supplies the only reader-body fact in the row theorem. -/
theorem core_of_group_row (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (j : Fin node.a.constructors.length)
    (ks : List RecKind)
    (hk : analyzeFields node.a.family.ref (node.a.constructorViews j).fields = some ks)
    (ms xs : List PSet.{4}) (z : PSet.{4})
    (hl : xs.length = (node.a.constructorViews j).fields.length)
    (hz : Equiv z (dataVal j.val xs)) :
    Equiv (RecPlan.nodeCore (mkM P μ) node ms z)
      (fapps (ms.getD j.val pempty)
        (ihArgs node.a.family.ref (RecPlan.nodeCore (mkM P μ) node ms)
          (node.a.constructorViews j).fields xs)) :=
  core_of_row (mkM P μ) node (NormDPlanBridge.bodies_of_group hE hmem node)
    j ks hk ms xs z hl hz

end Rcic.F3.PSet.NormDataIotaRow
