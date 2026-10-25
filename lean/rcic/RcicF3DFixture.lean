import rcic.RcicF3DMain
import rcic.RcicTypedDeltaRecPins

/-!
# F3 D: the class contains a group whose recursive field is reached only through δ

`drEnvWfT` (`RcicTypedDeltaRecPins`: `Id : Sort 1 → Sort 1 := λ A, A` at 0 as a
definition, then the group `F : Sort 1` at 1, `mk : Id F → F` at 2, `F.rec`
eliminating into any sort at 3) is in `ClassGD`, and in `BoundG K` and
`BoundDG K` for every `K` (`drEnvWfT_classGD`); the induction of
`RcicF3DMain` gives a sound model of it (`drEnvWfT_envSound`). The field
`Id F` is not a literal family application, so the block is outside `ClassG`
(`drEnvWfT_not_classG`); its weak-head normal form is `F`, and the admitted
shape of the field is `recursive 0` at every descriptor (`dr_shapes`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The recursor node of the δ-hidden block. -/
abbrev DrNode := RecNode drBase drEnv 1 3 drRecMember

theorem dr_fam (node : DrNode) : node.a.family.member = drFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- The family view of the block: no parameters, no indices, level 1. -/
theorem dr_family (node : DrNode) :
    node.a.family.parameters = [] ∧ node.a.family.indices = [] ∧ node.a.family.resultLevel = .succ .zero := by
  have hst := node.a.family.storedType
  rw [dr_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

theorem dr_ctor (node : DrNode) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = drMkMember ∧ i.val = 0 := by
  have hlen : node.a.constructors.length = 1 := node_ctors_length (ctors := [(2, drMkMember)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 1 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- The constructor view of `mk`: no parameters or result indices, the one
field `Id F`. -/
theorem dr_view (node : DrNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [] ∧ (node.a.constructorViews i).resultIndices = [] ∧
      (node.a.constructorViews i).fields = [drField] := by
  obtain ⟨hP, hI, _⟩ := dr_family node
  have hp : (node.a.constructorViews i).parameters = [] := by
    have := (node.a.constructorViews i).parameterCount
    rw [hP] at this
    exact List.eq_nil_of_length_eq_zero this
  have hr : (node.a.constructorViews i).resultIndices = [] := by
    have := (node.a.constructorViews i).indexCount
    rw [hI] at this
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨hp, hr, ?_⟩
  have hst := (node.a.constructorViews i).storedType
  rw [hp, List.nil_append] at hst
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals 0 (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  have hm : (node.a.constructors[i.val]).mtype = policyPi [drField] (.const 1 []) := by
    rw [(dr_ctor node i).1]; rfl
  exact (policyPi_split_eq [drField] _ (.const 1 []) _ (fun _ _ h => Expr.noConfusion h) hne
    (hm.symm.trans hst)).1.symm

/-- The node's environment contains `Id` with its body, and `F`. -/
theorem dr_node_members (node : DrNode) :
    node.E0.members 0 = some drIdMember ∧ node.E0.members 1 = some drFamMember := by
  refine ⟨node.base 0 drIdMember rfl, ?_⟩
  have h := node.a.family.present
  rw [node.fam, dr_fam node] at h
  exact h

/-- At the bound `8`, in any environment containing `Id` with its body and
`F`, the field `Id F` analyzes as directly recursive: it normalizes to `F`. -/
theorem dr_fieldShapes8 {E : ResolvedEnv} (h0 : E.members 0 = some drIdMember)
    (h1 : E.members 1 = some drFamMember) :
    fieldShapesFuel E 8 1 0 0 0 0 [drField] = some [.recursive 0] := by
  simp [fieldShapesFuel, fieldAnalyze, piTelescopeFuel, whnfFuel, appsSpine, transparentBody, h0, h1,
    drIdMember, drFamMember, drField, transparent, instantiateLevels, instantiate0, instantiate, foldApps,
    domainsContainFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel, familyIdx]

/-- The admitted shapes of `mk` at every descriptor: the one field directly
recursive (by the uniqueness of the analysis across bounds). -/
theorem dr_shapes (node : DrNode) (i : Fin node.a.constructors.length) :
    node.h14.shapesAt i = [.recursive 0] := by
  obtain ⟨h0, h1⟩ := dr_node_members node
  have hA := node.h14.analyzed i
  rw [node.fam, (dr_view node i).2.2, (dr_family node).1, (dr_family node).2.1, dr_fam node] at hA
  exact fieldShapesFuel_unique hA (dr_fieldShapes8 h0 h1)

/-- The block is outside `ClassG`: `mk`'s field mentions the family but is not
a literal family application (its head is `Id`). -/
theorem drEnvWfT_not_classG : ¬ ClassG drEnvWfT := by
  intro hC
  obtain ⟨node, _⟩ := group_nodeD (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)]) (rr := 3)
    (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT
  obtain ⟨_, hG, _⟩ := hC
  have hlen : node.a.constructors.length = 1 := node_ctors_length (ctors := [(2, drMkMember)]) node rfl
  have h := (hG node).1 ⟨0, by omega⟩
  rw [(dr_view node ⟨0, by omega⟩).2.2] at h
  obtain ⟨h, _⟩ := h
  rcases h with h | ⟨idx, h, _⟩
  · exact absurd h (by decide)
  · exact absurd (foldApps_const_head (h.symm.trans rfl : foldApps (.const 1 _) _ = foldApps (.const 0 []) [.const 1 []]))
      (by decide)

/-- The field typing of `mk`, at any instance within any bound. -/
theorem dr_fields_typed (K : Nat → Nat) (vs : List Nat) (Ps Fs : List (Expr Nat))
    (hP : Ps = []) (hF : Fs = [drField]) (k : Fin Fs.length) :
    ∃ l : Level, ∃ d : HasTyT drFamEnv 0 (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val)) (Fs[k]) (.sort l),
      LOKt (σOf vs) 4 K d := by
  subst hP; subst hF
  match k with
  | ⟨0, _⟩ => exact ⟨.succ .zero, drFieldTyT rfl rfl, fun l hl => absurd hl (List.not_mem_nil _),
      fun l hl => absurd hl (List.not_mem_nil _)⟩

/-- **The δ-hidden block is in the class**, at every instance bound: a `Type`
group whose one recursive field is reached only through the definition `Id`. -/
theorem drEnvWfT_classGD : ClassGD drEnvWfT ∧ ∀ K, BoundG K drEnvWfT ∧ BoundDG K drEnvWfT := by
  refine ⟨⟨trivial, fun node => ⟨fun i s hs => ?_, fun hu _ _ => ?_,
      fun i => (dr_view node i).1.trans (dr_family node).1.symm⟩, fun node => ?_⟩,
    fun K => ⟨⟨⟨trivial, (by decide : 1 + 1 ≤ 4), trivial⟩, fun node i vs _ _ => ?_, ?_,
      fun node hu _ _ _ _ _ => ?_⟩, ⟨trivial, fun node i vs _ _ k => ?_⟩⟩⟩
  · rw [dr_shapes node i] at hs
    exact Or.inr (List.mem_singleton.mp hs)
  · rw [(dr_family node).2.2] at hu
    exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)
  · rw [(dr_family node).1]
    exact ⟨trivial, rfl, rfl, trivial⟩
  · rw [(dr_ctor node i).1]
    exact ⟨_, .pi [] _ _ _ _ (drFieldTyT rfl rfl) (.const _ 1 [] drFamMember rfl rfl rfl),
      (by decide : 1 ≤ 4), (by decide : 1 ≤ 4),
      ⟨fun l hl => absurd hl (List.not_mem_nil _), fun l hl => absurd hl (List.not_mem_nil _)⟩,
      fun l hl => absurd hl (List.not_mem_nil _)⟩
  · refine ⟨trivial, fun vs _ _ k => ?_, trivial, trivial⟩
    obtain ⟨k, hk⟩ := k
    match k, hk with
    | 0, _ => exact ⟨drFieldTyT rfl rfl, fun l hl => absurd hl (List.not_mem_nil _),
        fun l hl => absurd hl (List.not_mem_nil _)⟩
  · rw [(dr_family node).2.2] at hu
    exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)
  · rw [show node.a.family.member.arity = 0 by rw [dr_fam node]; rfl]
    exact dr_fields_typed K vs _ _ (dr_view node i).1 (dr_view node i).2.2 k

/-- The recursor's bound below the constructor's: `K 3 ≤ K 2`. -/
theorem drEnvWfT_recBelowCtors (K : Nat → Nat) (h : K 3 ≤ K 2) : RecBelowCtors K drEnvWfT :=
  ⟨trivial, fun r h1 h2 => by
    have hr : r = 2 := by omega
    subst hr
    exact h⟩

/-- The bridge on the block: `BoundDG` from `BoundG` under the condition (the
fixture also proves `BoundDG` directly, at every `K`). -/
example (K : Nat → Nat) (h : K 3 ≤ K 2) : BoundDG K drEnvWfT :=
  boundDG_of_boundG K drEnvWfT (drEnvWfT_recBelowCtors K h) (drEnvWfT_classGD.2 K).1

/-- The induction applied to the δ-hidden block: its table is a sound model of it. -/
theorem drEnvWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtxD drEnvWfT) drEnvWfT)) σ K drEnv n := by
  have hRA := readsOKAlong_envCtxD drEnvWfT drEnvWfT_classGD.1 (envCtxD drEnvWfT) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtxD drEnvWfT) drEnvWfT hRA).1
  have hI := gInvD P K drEnvWfT drEnvWfT_classGD.1 (drEnvWfT_classGD.2 K).1 (drEnvWfT_classGD.2 K).2
    (envCtxD drEnvWfT) (fun _ _ => rfl) _ hF
  exact envSound_of P (Efin := drEnv) (fun _ _ h => h) hI.1
    (fun r m hm hk => hI.2 _ (fun _ _ h => h) r m hm hk) σ n

end PSet

end Rcic.F3
