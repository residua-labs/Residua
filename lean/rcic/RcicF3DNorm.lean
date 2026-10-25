import rcic.RcicF3DEnv

/-!
# F3 D-5: the normalized data of a group

`normFamData a fuelAt`: the group's data (`famDataOf a`) with every
constructor's fields normalized (`normField`) at the bounds `fuelAt`. For a
recursor node, admission's descriptor supplies the bounds (`nodeFam`), and
its analysis (`IotaDescriptorClause.analyzed`) the shapes. Under
`NoFunRec` (no function-recursive shape):

- `nodeFam_recDataAgree`: the normalized data agrees with the original in
  everything the recursor's value reads;
- `nodeFam_fields_direct` / `nodeFam_recApp`: the normalized fields are
  family-free or literal family applications, the class the recursive-group
  model (`famLim_fix`, `recVal_mem_rec`) is built for;
- `nodeFam_bounded`: the normalized data's levels are bounded by the arity;
- `bodiesOK_node`, `envClosed_node`: the δ side conditions in the recursor's
  environment.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve)

namespace PSet

/-- The group's data with every constructor's fields normalized at the given bounds. -/
def normFamData {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (fuelAt : Fin a.constructors.length → Nat) : FamData :=
  { famDataOf a with
    ctors := ofFin a.constructors.length fun i =>
      ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref),
        (a.constructorViews i).resultIndices) }

theorem normFamData_ctors_length {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuelAt : Fin a.constructors.length → Nat) :
    (normFamData a fuelAt).ctors.length = a.constructors.length :=
  ofFin_length _ _

theorem normFamData_ctor {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuelAt : Fin a.constructors.length → Nat)
    (i : Fin a.constructors.length) :
    (normFamData a fuelAt).ctors[i.val]? =
      some ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref),
        (a.constructorViews i).resultIndices) :=
  ofFin_get _ _ i

/-- A literal family application is its own normal form. -/
theorem normField_eq_self_of_head {E : ResolvedEnv} {f : Nat} (hop : ∀ ls, transparentBody E f ls = none)
    (fuel : Nat) {A : Expr Nat} {ls : List Level} {args : List (Expr Nat)}
    (hsp : appsSpine A = (.const f ls, args)) : normField E fuel f A = A := by
  unfold normField
  rw [if_pos (occursConst_true_of_head hsp)]
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [whnfFuel_famHead hsp (hop ls) fuel]
      rfl

section Node

variable {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm)

/-- The normalized data of a recursor node, at the descriptor's bounds. -/
def nodeFam : FamData := normFamData node.a node.h14.fuelAt

/-- No function-recursive field: every admitted shape is non-recursive or
directly recursive. -/
def NoFunRec : Prop :=
  ∀ (i : Fin node.a.constructors.length) (s : FieldShape), s ∈ node.h14.shapesAt i →
    s = .nonrecursive ∨ s = .recursive 0

theorem nodeFam_ctors_length : (nodeFam node).ctors.length = node.a.constructors.length :=
  normFamData_ctors_length _ _

theorem nodeFam_ctor (i : Fin node.a.constructors.length) :
    (nodeFam node).ctors[i.val]? =
      some ((node.a.constructorViews i).fields.map (normField node.E0 (node.h14.fuelAt i) node.a.family.ref),
        (node.a.constructorViews i).resultIndices) :=
  normFamData_ctor _ _ i

variable (hFF : FamFreeBodies node.E0 node.a.family.ref) (hsh : NoFunRec node)
include hFF hsh

/-- The normalized fields of a constructor are family-free or literal family
applications at the parameter locals and family-free indices. -/
theorem nodeFam_fields_direct (i : Fin node.a.constructors.length) :
    RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length
      ((node.a.constructorViews i).fields.map (normField node.E0 (node.h14.fuelAt i) node.a.family.ref)) 0 :=
  normFields_direct hFF _ 0 _ (by rw [Nat.add_zero]; exact node.h14.analyzed i) (hsh i)

/-- The normalized data agrees with the original in everything the recursor's
value reads. -/
theorem nodeFam_recDataAgree : RecDataAgree (famDataOf node.a) (nodeFam node) where
  fref := rfl
  indices := rfl
  resLevel := rfl
  policy := rfl
  len := by rw [nodeFam_ctors_length, famDataOf_ctors_length]
  ctor := by
    intro j c c' hc hc'
    have hj : j < node.a.constructors.length := by
      rw [← famDataOf_ctors_length]
      exact (List.getElem?_eq_some_iff.mp hc).1
    have e1 := famDataOf_ctor node.a ⟨j, hj⟩
    have e2 := nodeFam_ctor node ⟨j, hj⟩
    rw [hc] at e1
    rw [hc'] at e2
    cases Option.some.inj e1
    cases Option.some.inj e2
    refine ⟨List.length_map _ _, rfl, fun k hk hk' => ?_⟩
    simp only [List.getElem_map]
    exact ⟨occursConst_normField_of_shapes hFF _ _ _ (node.h14.analyzed ⟨j, hj⟩) (hsh ⟨j, hj⟩) _
      (List.getElem_mem _),
      ihDepth_normField_of_shapes hFF _ _ _ (node.h14.analyzed ⟨j, hj⟩) (hsh ⟨j, hj⟩) _
      (List.getElem_mem _)⟩

/-- The normalized constructors' fields are family-free or the family at its
canonical instance applied to family-free arguments (`RecApp`). -/
theorem nodeFam_recApp : ∀ c, c ∈ (nodeFam node).ctors → ∀ A, A ∈ c.1 →
    occursConst (nodeFam node).fref A = false ∨ RecApp (nodeFam node) node.a.family.member.arity A := by
  intro c hc A hA
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  rcases (fieldsClass_of_direct _ 0 (nodeFam_fields_direct node hFF hsh i)).mem A hA with h | ⟨d, idx, rfl, hl, hidx⟩
  · exact Or.inl h
  · refine Or.inr ⟨policyParameterLocals node.a.family.parameters.length d ++ idx, rfl, ?_, fun e he => ?_⟩
    · show _ = (node.a.family.parameters ++ node.a.family.indices).length
      rw [List.length_append, List.length_append, length_paramLocals, hl]
    · rcases List.mem_append.mp he with he | he
      · exact paramLocals_free _ _ _ e he
      · exact hidx e he

omit hFF hsh in
/-- The normalized data's levels are bounded by the family's arity. -/
theorem nodeFam_bounded (hTF : TypeFacts E')
    (hb0 : ∀ r m b, node.E0.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true) :
    FamBounded (nodeFam node) node.a.family.member.arity := by
  have hB := famBounded_node node hTF
  refine ⟨hB.params, hB.indices, hB.res, fun c hc => ?_⟩
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  have hc0 : ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices) ∈
      (famDataOf node.a).ctors := List.getElem?_mem (famDataOf_ctor node.a i)
  obtain ⟨hF, hR⟩ := hB.ctors _ hc0
  refine ⟨fun A' hA' => ?_, hR⟩
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hA'
  rcases normField_cases node.E0 (node.h14.fuelAt i) node.a.family.ref A with he | ⟨fu, hw⟩
  · rw [he]; exact hF A hA
  · exact whnfFuel_levelsBounded hb0 fu A _ (hF A hA) hw

end Node

/-! ### the recursor's environment -/

section Env

variable {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
  (hE : EnvWfT E) (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
  (node : RecNode E E' f rr rm)

/-- The members of the recursor's environment are members of the final one. -/
theorem node_sub' : ∀ r m, node.E0.members r = some m → E'.members r = some m :=
  fun r m h => node.sub r m (members_extend_preserved node.fresh r m h)

include hmem in
/-- A member of the recursor's environment not in the base is a group member, body-less. -/
theorem node_new_body_none : ∀ r m, node.E0.members r = some m → E.members r = none → m.body = none := by
  intro r m hm h0
  rcases groupMembersT_cases hmem r m (node_sub' node r m hm) with h1 | h1
  · rw [h1] at h0; cases h0
  · exact groupMembersT_body_none hmem r m h1

include hE hmem in
/-- Transparent bodies in the recursor's environment are level-closed. -/
theorem node_bodies_levelsBounded0 (K : Nat → Nat) (hB : BoundG K hE) :
    ∀ r m b, node.E0.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true := by
  intro r m b hm hb htr
  rcases groupMembersT_cases hmem r m (node_sub' node r m hm) with h1 | h1
  · exact (transparent_bodies_of_envWfT K hE hB r m b h1 hb htr).1
  · rw [groupMembersT_body_none hmem r m h1] at hb; cases hb

include hE hmem in
/-- The δ side condition of normalization, in the recursor's environment. -/
theorem bodiesOK_node (K : Nat → Nat) (hB : BoundG K hE) (σ : Nat → Nat) : BodiesOK node.E0 σ K :=
  bodiesOK_of_envWfT K hE hB node.base (node_new_body_none hmem node) σ

/-- The recursor's environment has closed members. -/
theorem envClosed_node (hTF : TypeFacts E') : EnvClosed node.E0 :=
  envClosed_of_typeFacts (typeFacts_sub (node_sub' node) hTF)

end Env


/-! ### normalization does not depend on the bound -/

/-- Two bounds at which admission permits the field with non-function-recursive
shapes normalize it alike. -/
theorem normField_fuel_eq {E : ResolvedEnv} {f nu np nq depth f1 f2 : Nat} {A : Expr Nat} {s1 s2 : FieldShape}
    {i1 i2 : List (Expr Nat)} (hFF : FamFreeBodies E f)
    (h1 : fieldAnalyze E f1 f nu np nq depth A = .permitted s1 i1)
    (h2 : fieldAnalyze E f2 f nu np nq depth A = .permitted s2 i2)
    (hs1 : s1 = .nonrecursive ∨ s1 = .recursive 0) (hs2 : s2 = .nonrecursive ∨ s2 = .recursive 0) :
    normField E f1 f A = normField E f2 f A := by
  rcases hs1 with rfl | rfl
  · have h0 := fieldAnalyze_nonrec_free h1
    rw [normField_free h0, normField_free h0]
  · obtain ⟨b1, hw1, _, _, _, hpf1⟩ := fieldAnalyze_rec0 h1
    obtain ⟨ls, args, hsp⟩ := properFamilyFuel_true_head hpf1
    have hb1 : b1 = foldApps (.const f ls) args := by rw [← foldApps_appsSpine b1, hsp]
    have hocc : occursConst f A = true := by
      rw [hb1] at hw1
      exact occursConst_of_whnf_head hFF hw1
    rcases hs2 with rfl | rfl
    · have h0 := fieldAnalyze_nonrec_free h2
      rw [h0] at hocc
      cases hocc
    · obtain ⟨b2, hw2, _, _, _, _⟩ := fieldAnalyze_rec0 h2
      have hw1' := whnfFuel_mono E (Nat.le_max_left f1 f2) hw1
      have hw2' := whnfFuel_mono E (Nat.le_max_right f1 f2) hw2
      rw [hw1'] at hw2'
      rw [normField_of_whnf hocc hw1, normField_of_whnf hocc hw2, Option.some.inj hw2']

/-- Admission's shapes do not depend on the bound. -/
theorem fieldShapesFuel_unique {E : ResolvedEnv} {f nu np nq depth f1 f2 : Nat} {Fs : List (Expr Nat)}
    {ss1 ss2 : List FieldShape} (h1 : fieldShapesFuel E f1 f nu np nq depth Fs = some ss1)
    (h2 : fieldShapesFuel E f2 f nu np nq depth Fs = some ss2) : ss1 = ss2 := by
  have h1' := fieldShapesFuel_mono E (Nat.le_max_left f1 f2) h1
  have h2' := fieldShapesFuel_mono E (Nat.le_max_right f1 f2) h2
  rw [h1'] at h2'
  exact Option.some.inj h2'

/-- Normalized fields do not depend on the bound, under admission's shapes. -/
theorem normFields_fuel_eq {E : ResolvedEnv} {f nu np nq f1 f2 : Nat} (hFF : FamFreeBodies E f) :
    (Fs : List (Expr Nat)) → (depth : Nat) → (ss1 ss2 : List FieldShape) →
    fieldShapesFuel E f1 f nu np nq depth Fs = some ss1 → fieldShapesFuel E f2 f nu np nq depth Fs = some ss2 →
    (∀ s, s ∈ ss1 → s = .nonrecursive ∨ s = .recursive 0) → (∀ s, s ∈ ss2 → s = .nonrecursive ∨ s = .recursive 0) →
    Fs.map (normField E f1 f) = Fs.map (normField E f2 f)
  | [], _, _, _, _, _, _, _ => rfl
  | A :: Fs, depth, ss1, ss2, h1, h2, hsh1, hsh2 => by
      unfold fieldShapesFuel at h1 h2
      cases ha1 : fieldAnalyze E f1 f nu np nq depth A with
      | permitted s1 i1 =>
          rw [ha1] at h1
          cases hr1 : fieldShapesFuel E f1 f nu np nq (depth + 1) Fs with
          | none => rw [hr1] at h1; cases h1
          | some rest1 =>
              rw [hr1] at h1
              have e1 : ss1 = s1 :: rest1 := (Option.some.inj h1).symm
              subst e1
              cases ha2 : fieldAnalyze E f2 f nu np nq depth A with
              | permitted s2 i2 =>
                  rw [ha2] at h2
                  cases hr2 : fieldShapesFuel E f2 f nu np nq (depth + 1) Fs with
                  | none => rw [hr2] at h2; cases h2
                  | some rest2 =>
                      rw [hr2] at h2
                      have e2 : ss2 = s2 :: rest2 := (Option.some.inj h2).symm
                      subst e2
                      simp only [List.map_cons]
                      rw [normField_fuel_eq hFF ha1 ha2 (hsh1 s1 (List.mem_cons_self _ _)) (hsh2 s2 (List.mem_cons_self _ _)),
                        normFields_fuel_eq hFF Fs (depth + 1) rest1 rest2 hr1 hr2
                          (fun s hs => hsh1 s (List.mem_cons_of_mem _ hs)) (fun s hs => hsh2 s (List.mem_cons_of_mem _ hs))]
              | unresolved => rw [ha2] at h2; cases h2
              | refused _ => rw [ha2] at h2; cases h2
      | unresolved => rw [ha1] at h1; cases h1
      | refused _ => rw [ha1] at h1; cases h1

end PSet

end Rcic.F3
