import rcic.RcicF3PropEvalValueReads
import rcic.RcicF3DEnv
import rcic.RcicF3MainG
import rcic.RcicConstsClosedEnvWfT

/-!
# The actual typed group produces the indexed endpoint's read support

The ordinary admission scope supplies every original field, stored minor,
constructor result index, and index-type read. Normalized fields and typed
IH expressions stay in the same reader scope by the existing denRefs_whnf
theorem and induction on the telescope reader. New group members are
bodyless, so their reader bodies are exactly inherited closed bodies.

The final certificate is produced from EnvWfT and GroupMembersT. It has no
semantic soundness, evaluation existence, functionality, candidate closure,
or global read-congruence premise. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPlanScope
open Rcic.Declarative PropEval
open Rcic.Model.PS (denRefs denRefs_natExpand hasTyT_denRefs)

private theorem bvar_reads (S : Nat → Prop) (k : Nat) : ExprReads S (.bvar k) :=
  fun r hr => (List.not_mem_nil r hr).elim

private theorem lift_reads {S : Nat → Prop} {e : Expr Nat}
    (he : ExprReads S e) (c a : Nat) : ExprReads S (Rcic.Declarative.lift c a e) := by
  intro r hr
  rw [denRefs_lift] at hr
  exact he r hr

private theorem app_reads {S : Nat → Prop} {f a : Expr Nat}
    (hf : ExprReads S f) (ha : ExprReads S a) : ExprReads S (.app f a) := by
  intro r hr
  exact (List.mem_append.mp hr).elim (hf r) (ha r)

private theorem foldApps_reads {S : Nat → Prop} {f : Expr Nat} {args : List (Expr Nat)}
    (hf : ExprReads S f) (ha : RefsIn S args) : ExprReads S (foldApps f args) := by
  intro r hr
  rcases (denRefs_foldApps_mem f args r).mp hr with hr | ⟨a, harg, hr⟩
  · exact hf r hr
  · exact ha a harg r hr

private theorem policyPi_reads {S : Nat → Prop} {b : Expr Nat}
    (hb : ExprReads S b) : ∀ ds : List (Expr Nat), RefsIn S ds →
      ExprReads S (policyPi ds b)
  | [], _ => hb
  | A :: ds, hd => by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hd A (List.mem_cons_self _ _) r hr
      · exact policyPi_reads hb ds (fun e he => hd e (List.mem_cons_of_mem _ he)) r hr

private theorem appsSpine_args_reads {S : Nat → Prop} {e : Expr Nat}
    (he : ExprReads S e) : RefsIn S (appsSpine e).2 := by
  intro a ha r hr
  apply he r
  rw [← foldApps_appsSpine e]
  exact (denRefs_foldApps_mem _ _ r).mpr (Or.inr ⟨a, ha, hr⟩)

private theorem familyIdx_reads {S : Nat → Prop} {e : Expr Nat}
    (he : ExprReads S e) (np : Nat) : RefsIn S (familyIdx np e) := by
  intro a ha
  exact appsSpine_args_reads he a (List.mem_of_mem_drop ha)

private theorem parameterLocals_reads (S : Nat → Prop) (np prior : Nat) :
    RefsIn S (policyParameterLocals np prior) := by
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact bvar_reads S (i + prior)

/-- A strong syntactic closure certificate includes all literal denotation
aliases; this bridge does not erase the zero/successor reference reads. -/
theorem closed_reads {E : ResolvedEnv} {e : Expr Nat}
    (h : ConstsMemberClosed E e) : ExprReads (Dom E) e := by
  induction h with
  | bvar i => exact bvar_reads (Dom E) i
  | sort l => exact fun r hr => (List.not_mem_nil r hr).elim
  | const r ls m hm _ _ =>
      intro r' hr
      have he : r' = r := List.mem_singleton.mp hr
      subst r'
      exact dom_of_members hm
  | lit t _ ih =>
      intro r hr
      apply ih r
      rw [denRefs_natExpand]
      exact hr
  | app _ _ ihf iha => exact app_reads ihf iha
  | lam _ _ ihA ihb =>
      intro r hr
      exact (List.mem_append.mp hr).elim (ihA r) (ihb r)
  | pi _ _ ihA ihb =>
      intro r hr
      exact (List.mem_append.mp hr).elim (ihA r) (ihb r)
  | letE _ _ _ ihA ihv ihb =>
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact (List.mem_append.mp hr).elim (ihA r) (ihv r)
      · exact ihb r hr

/-- Actual group bodies inherit their complete reference closure from the
predecessor. The new family, constructors, and recursor have no bodies. -/
theorem bodies_read_in_node {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    ∀ r m b ls, node.E0.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads (Dom node.E0) (instantiateLevels ls b) := by
  intro r m b ls hm hb htr
  have hfinal := node.sub r m (members_extend_preserved node.fresh r m hm)
  rcases groupMembersT_cases hmem r m hfinal with hold | hnew
  · exact closed_reads ((bodiesClosed_of_envWfT hE r m hold b htr hb ls).ext node.base)
  · rw [groupMembersT_body_none hmem r m hnew] at hb
    cases hb

/-- The existing head-normalization reference theorem composes through every
Pi layer, preserving the actual domains and terminal expression. -/
theorem telescope_reads {E : ResolvedEnv} {S : Nat → Prop}
    (hbodies : ∀ r m b ls, E.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads S (instantiateLevels ls b)) :
    ∀ (fuel : Nat) (A : Expr Nat) (ds : List (Expr Nat)) (b : Expr Nat),
      piTelescopeFuel E fuel A = some (ds, b) → ExprReads S A →
      RefsIn S ds ∧ ExprReads S b := by
  intro fuel
  induction fuel with
  | zero => intro A ds b hr _; cases hr
  | succ fuel ih =>
      intro A ds b hr hA
      cases hw : whnfFuel E fuel A with
      | none =>
          simp only [piTelescopeFuel, hw] at hr
          cases hr
      | some w =>
          have hwr : ExprReads S w := by
            intro r href
            exact (denRefs_whnf hbodies fuel A w hw r href).elim (hA r) id
          cases w with
          | pi D B =>
              have hD : ExprReads S D := fun r href =>
                hwr r (List.mem_append_left _ href)
              have hB : ExprReads S B := fun r href =>
                hwr r (List.mem_append_right _ href)
              cases ht : piTelescopeFuel E fuel B with
              | none =>
                  simp only [piTelescopeFuel, hw, ht] at hr
                  cases hr
              | some result =>
                  rcases result with ⟨ds', b'⟩
                  have htail := ih B ds' b' ht hB
                  simp only [piTelescopeFuel, hw, ht] at hr
                  cases hr
                  refine ⟨?_, htail.2⟩
                  intro e he
                  rcases List.mem_cons.mp he with rfl | he
                  · exact hD
                  · exact htail.1 e he
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [piTelescopeFuel, hw] at hr
              cases hr
              exact ⟨fun _ he => (List.not_mem_nil _ he).elim, hwr⟩

private theorem funIH_reads {E : ResolvedEnv} {S : Nat → Prop}
    (hbodies : ∀ r m b ls, E.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads S (instantiateLevels ls b))
    (fuel np inner : Nat) {A Mx ihT : Expr Nat}
    (hA : ExprReads S A) (hMx : ExprReads S Mx)
    (hr : funIHType E fuel np A Mx inner = some ihT) : ExprReads S ihT := by
  unfold funIHType at hr
  cases ht : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) with
  | none => rw [ht] at hr; cases hr
  | some result =>
      rcases result with ⟨ds, b⟩
      have hd := telescope_reads hbodies fuel _ ds b ht (lift_reads hA 0 1)
      simp only [ht] at hr
      by_cases hlen : ds.length = inner
      · rw [if_pos hlen] at hr
        cases hr
        apply policyPi_reads
        · apply foldApps_reads (lift_reads (lift_reads hMx 0 1) 0 inner)
          intro e he
          rcases List.mem_append.mp he with he | he
          · exact familyIdx_reads hd.2 np e he
          · have he' := List.mem_singleton.mp he
            subst e
            apply foldApps_reads (bvar_reads S inner)
            intro e he
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
            exact bvar_reads S i
        · exact hd.1
      · rw [if_neg hlen] at hr
        cases hr

/-- All successful input spines inherit support from their actual syntax.
No re-admission of inserted IH binders or semantic fitting is required. -/
theorem spine_reads {E : ResolvedEnv} {S : Nat → Prop}
    (hbodies : ∀ r m b ls, E.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads S (instantiateLevels ls b))
    (f nu np fuel : Nat) : ∀ (ss : List FieldShape) (Mx acc T : Expr Nat),
      ExprReads S Mx → ExprReads S acc → ExprReads S T →
      ReadTransport.spineReads S E f nu np fuel Mx acc ss T := by
  intro ss
  induction ss with
  | nil =>
      intro Mx acc T hMx hacc hT
      exact app_reads (foldApps_reads hMx (familyIdx_reads hT np)) hacc
  | cons s ss ih =>
      intro Mx acc T hMx hacc hT
      cases T with
      | pi A B =>
          have hA : ExprReads S A := fun r hr => hT r (List.mem_append_left _ hr)
          have hB : ExprReads S B := fun r hr => hT r (List.mem_append_right _ hr)
          cases s with
          | nonrecursive =>
              exact ⟨hA, ih _ _ _ (lift_reads hMx 0 1)
                (app_reads (lift_reads hacc 0 1) (bvar_reads S 0)) hB⟩
          | recursive inner =>
              refine ⟨hA, fun ihT hr => funIH_reads hbodies fuel np inner hA hMx hr,
                ?_, ih _ _ _ (lift_reads hMx 0 2)
                  (app_reads (lift_reads hacc 0 2) (bvar_reads S 1)) (lift_reads hB 0 1)⟩
              intro ds args hr
              have ht := telescope_reads hbodies fuel _ ds _ hr (lift_reads hA 0 1)
              refine ⟨ht.1, ?_⟩
              intro e he r href
              exact ht.2 r ((denRefs_foldApps_mem _ _ r).mpr (Or.inr ⟨e, he, href⟩))
      | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
          cases s <;> trivial

private theorem dom_base_node {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : ∀ r, Dom E r → Dom node.E0 r := by
  intro r hr
  cases hm : E.members r with
  | none => unfold Dom at hr; rw [hm] at hr; cases hr
  | some m => exact dom_of_members (node.base r m hm)

/-- Admission pays the entire endpoint read certificate at the actual
constructor-bearing reader prefix, including the family and index types. -/
theorem endpointReads_of_group (C : Context)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E') :
    EndpointReads (Dom C.node.E0) C := by
  obtain ⟨hL, hrr⟩ := group_layout hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hbase := dom_base_node C.node
  have hfamily : Dom C.node.E0 C.node.a.family.ref :=
    dom_of_members C.node.a.family.present
  have hscope : ∀ r, Dom (extendEnv C.E C.f fm) r → Dom C.node.E0 r := by
    intro r hr
    by_cases he : r = C.f
    · subst r
      simpa only [C.node.fam] using hfamily
    · exact hbase r (dom_of_extend_ne hr he)
  have hfamilyTypes := (famReads_node hmem hL hrr C.node).1
  have hparameters : RefsIn (Dom C.node.E0) C.node.a.family.parameters := by
    intro e he r hr
    exact hbase r (hfamilyTypes e (List.mem_append_left _ he) r hr)
  have hindexTypes : RefsIn (Dom C.node.E0) C.node.a.family.indices := by
    intro e he r hr
    exact hbase r (hfamilyTypes e (List.mem_append_right _ he) r hr)
  have hctorType : ∀ j : Fin C.node.a.constructors.length,
      ExprReads (Dom C.node.E0) (C.node.a.constructors[j.val]).mtype := by
    intro j r hr
    exact hscope r (groupMembersT_ctor_refs hmem _ _
      (node_ctor_mem hmem hL hrr C.node j) (C.node.a.constructorViews j).hasClass r hr)
  have hfields : ∀ j, RefsIn (Dom C.node.E0) (C.node.a.constructorViews j).fields := by
    intro j e he r hr
    apply hctorType j r
    rw [(C.node.a.constructorViews j).storedType]
    exact refs_policyPi_dom _ _ e (List.mem_append_right _ he) hr
  have hindices : ∀ j, RefsIn (Dom C.node.E0) (C.node.a.constructorViews j).resultIndices := by
    intro j e he r hr
    apply hctorType j r
    rw [(C.node.a.constructorViews j).storedType]
    exact refs_policyPi_body _ (refs_foldApps _ _
      (Or.inr ⟨e, List.mem_append_right _ he, hr⟩)) _
  have hminors : RefsIn (Dom C.node.E0) C.node.a.minorTypes := by
    intro R hR r hr
    apply hasTyT_denRefs C.node.hT r
    rw [C.node.a.recursorType]
    unfold policyRecursorType
    apply refs_policyPi_body
    exact List.mem_append_right _ (refs_policyPi_dom _ _ R hR hr)
  have hbodies := bodies_read_in_node hE hmem C.node
  refine
    { toNodeReads :=
        { parameters := hparameters
          fields := hfields
          indices := hindices
          minors := hminors
          spines := ?_ }
      family := hfamily
      indexTypes := hindexTypes }
  intro j fuel _
  apply spine_reads hbodies C.node.a.family.ref C.node.a.family.member.arity
    C.node.a.family.parameters.length fuel (C.node.h14.shapesAt j)
  · exact bvar_reads _ j.val
  · apply foldApps_reads
    · intro r hr
      have he : r = C.node.a.family.ref + 1 + j.val := List.mem_singleton.mp hr
      subst r
      exact dom_of_members (C.node.a.constructorsPresent j)
    · exact parameterLocals_reads _ _ _
  · apply lift_reads
    apply policyPi_reads
    · apply foldApps_reads
      · intro r hr
        have he : r = C.node.a.family.ref := List.mem_singleton.mp hr
        subst r
        exact hfamily
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact parameterLocals_reads _ _ _ e he
        · exact hindices j e he
    · exact hfields j

/-- At the group's last recursor cell, every reader member was already
installed. The final-environment equation comes from that cons/nil cell;
no special identity for the selected node's reader environment is needed. -/
theorem reader_sub_before_last {E E' Epre : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (hLast : E' = extendEnv Epre rr rm) :
    ∀ r m, node.E0.members r = some m → Epre.members r = some m := by
  intro r m hm
  have hne : r ≠ rr := by
    intro he
    subst r
    rw [node.fresh] at hm
    cases hm
  have hfinal := node.sub r m (members_extend_preserved node.fresh r m hm)
  rw [hLast, members_extend_ne Epre rr rm r hne] at hfinal
  exact hfinal

end Rcic.F3.PSet.EvalPlanScope
