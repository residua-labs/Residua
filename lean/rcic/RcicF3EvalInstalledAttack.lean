import rcic.RcicF3EvalRawTable
import rcic.RcicF3EvalPlanValueAttack

/-!
# The installed new recursor at the actual admitted AccR environment

The table is EvalRole.rawTable of the actual admitted environment, with its
produced faithfulness and read certificates. Its family/constructor prefix
agrees with the previous table, so the produced endpoint read law transports
the actual candidate-derived evaluation and typed arguments to this table.

The final iota equation uses the installed recursor and an indexed IH whose
leaf map is the new table's own bounded evaluation value. The selected
AccR recursive argument domain remains empty. The old endpoint still fails
under this new table. Universal member typing, universal StepAG and the
checked apex are not asserted. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.EvalInstalledAttack
open Rcic.Declarative PiIndex PropEval PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open EvalPlanValueAttack (plan)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  EvalRole.rawTable P AccEnv.accEnvWfT

/-- Expose the two equality proofs as constructor data at each call.
The uniqueness proof is proposition-valued, so this is definitionally
irrelevant to the walk; it makes its final data elimination compute. -/
private theorem groupRecNode_eta {Ebase : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (hlay : FamilyLayout Ebase) (hrmK : rm.mclass = .recursorM)
    {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E')
    (hl : ∀ c, c ∈ ms → c.1 = f ∨ c.2.mclass ≠ .inductiveM)
    (hinv : GroupWalkInv Ebase E f)
    (hsub : ∀ r m, Ebase.members r = some m → E.members r = some m)
    (huniq : ∀ c, c ∈ ms → c.2.mclass = .recursorM → c.1 = rr ∧ c.2 = rm)
    (hin : (rr, rm) ∈ ms) :
    groupRecNode hlay hrmK hmem hl hinv hsub huniq hin =
      groupRecNode hlay hrmK hmem hl hinv hsub
        (fun c hc hk => ⟨(huniq c hc hk).1, (huniq c hc hk).2⟩) hin := rfl

/-- Compare the scan's actual node before applying the normalized cache
constructor. Proof fields may differ along the prefix traversal. -/
private theorem canonical_node :
    (groupNode (.empty : EnvWfT emptyEnv) (fm := accFamMember)
      (ctors := [(1, accIntroMember)]) (rr := 2) (rm := accRecMember) rfl
      (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT).val =
        PlanPropStepAttack.pNode := by
  unfold groupNode
  rw [groupRecNode_eta]
  with_unfolding_all rfl

theorem canonical_plan : EvalRole.envPlan AccEnv.accEnvWfT 2 = some plan := by
  change some (EvalPlan.ofNode
    (groupNode (.empty : EnvWfT emptyEnv) (fm := accFamMember)
      (ctors := [(1, accIntroMember)]) (rr := 2) (rm := accRecMember) rfl
      (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT).val) =
        some (EvalPlan.ofNode PlanPropStepAttack.pNode)
  exact congrArg (fun n => some (EvalPlan.ofNode n)) canonical_node


/-- Both installers depend on the member list, without reducing the concrete
admission derivation or any value that a later update will discard. -/
private theorem old_group_fold (F : RoleModel.FamilyValue) (P : Premises4)
    (roles : Nat → Role) (plans : PlanRole.Plans)
    {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') (μ : Nat → List Nat → PSet.{4}) :
    PlanRole.groupTable F P roles plans hmem μ =
      ms.foldl (fun ν c => upd ν c.1
        (PlanRole.memberVal F P ν (plans c.1) (roles c.1) c.2)) μ := by
  induction hmem generalizing μ with
  | nil => rfl
  | cons E r m rest E' hfresh hnobody hcl harity hlvl hcanon harities hadm hidx u hT hTc htyped hrest ih =>
      exact ih _

private theorem new_group_fold (F : RoleModel.FamilyValue) (P : Premises4)
    (roles : Nat → Role) (plans : EvalRole.Plans)
    {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') (μ : Nat → List Nat → PSet.{4}) :
    EvalRole.groupTable F P roles plans hmem μ =
      ms.foldl (fun ν c => upd ν c.1
        (EvalRole.memberVal F P ν (plans c.1) (roles c.1) c.2)) μ := by
  induction hmem generalizing μ with
  | nil => rfl
  | cons E r m rest E' hfresh hnobody hcl harity hlvl hcanon harities hadm hidx u hT hTc htyped hrest ih =>
      exact ih _

private theorem old_acc_fold (F : RoleModel.FamilyValue) (P : Premises4)
    (roles : Nat → Role) (plans : PlanRole.Plans) :
    PlanRole.envTable F P roles plans AccEnv.accEnvWfT =
      [(0, accFamMember), (1, accIntroMember), (2, accRecMember)].foldl
        (fun ν c => upd ν c.1
          (PlanRole.memberVal F P ν (plans c.1) (roles c.1) c.2))
        (fun _ _ => pempty) := by
  change PlanRole.groupTable F P roles plans AccEnv.accMembersT
    (fun _ _ => pempty) = _
  exact old_group_fold F P roles plans AccEnv.accMembersT _

private theorem new_acc_fold (F : RoleModel.FamilyValue) (P : Premises4)
    (roles : Nat → Role) (plans : EvalRole.Plans) :
    EvalRole.envTable F P roles plans AccEnv.accEnvWfT =
      [(0, accFamMember), (1, accIntroMember), (2, accRecMember)].foldl
        (fun ν c => upd ν c.1
          (EvalRole.memberVal F P ν (plans c.1) (roles c.1) c.2))
        (fun _ _ => pempty) := by
  change EvalRole.groupTable F P roles plans AccEnv.accMembersT
    (fun _ _ => pempty) = _
  exact new_group_fold F P roles plans AccEnv.accMembersT _

/-- Only the final recursor installation changes between these two tables. -/
theorem family_entry (P : Premises4) (vs : List Nat) :
    installed P 0 vs = table P 0 vs := by
  unfold installed PlanRole.rawTable table EvalRole.rawTable
  rw [old_acc_fold, new_acc_fold]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [upd_ne _ 2 _ (show 0 ≠ 2 from by decide),
    upd_ne _ 1 _ (show 0 ≠ 1 from by decide), upd_eq,
    upd_ne _ 2 _ (show 0 ≠ 2 from by decide),
    upd_ne _ 1 _ (show 0 ≠ 1 from by decide), upd_eq]
  rw [family_context]
  rfl

theorem constructor_entry (P : Premises4) (vs : List Nat) :
    installed P 1 vs = table P 1 vs := by
  unfold installed PlanRole.rawTable table EvalRole.rawTable
  rw [old_acc_fold, new_acc_fold]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [upd_ne _ 2 _ (show 1 ≠ 2 from by decide), upd_eq,
    upd_ne _ 2 _ (show 1 ≠ 2 from by decide), upd_eq]
  rw [constructor_context, family_context]
  rfl

theorem prefix_agree (P : Premises4) :
    AgreeOn (installed P) (table P) (Dom plan.node.E0) := by
  intro r hr vs
  by_cases h1 : r = 1
  · subst r
    exact constructor_entry P vs
  by_cases h0 : r = 0
  · subst r
    exact family_entry P vs
  change Dom (extendEnv (extendEnv emptyEnv 0 accFamMember) 1 accIntroMember) r at hr
  have he := dom_of_extend_ne (dom_of_extend_ne hr h1) h0
  change (false : Bool) = true at he
  cases he

/-- Stored recursor type support comes from the existing actual admitted walk. -/
theorem recursor_reads : ExprReads (Dom plan.node.E0) accRecMember.mtype := by
  have h := Rcic.F3.StepDGOrder.readsOKAlong_envCtxT AccEnv.accEnvWfT
    (envCtx AccEnv.accEnvWfT) (fun _ _ => rfl)
  have hr : PSet.ReadsIn (Dom accPrefix) (envCtx AccEnv.accEnvWfT 2) accRecMember :=
    h.2.2.2.1
  rw [recursor_context] at hr
  exact hr

theorem argument_reads : RefsIn (Dom plan.node.E0)
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] := by
  intro e he r hr
  apply recursor_reads r
  change r ∈ Rcic.Model.PS.denRefs
    (policyPi [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)]
      (.app (.bvar 2) (.bvar 0)))
  exact refs_policyPi_dom _ _ e he hr

/-- The complete actual recursor argument tuple is typed under the new table. -/
theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (table P)) (ctx P).σ
      [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
      [parameter, motive P (installed P), minor P (installed P), pempty] :=
  (TelFits_agreeOn P (prefix_agree P) (ctx P).σ
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] argument_reads ρ0
    [parameter, motive P (installed P), minor P (installed P), pempty]).mp
      (EvalPlanValueAttack.arguments_fit P)

theorem member_equiv (P : Premises4) :
    Equiv (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember)
      (EvalPlanValue.memberValue (mkM P (table P)) (ctx P).σ plan accRecMember) := by
  have hReads := EvalPlanScope.endpointReads_of_group
    (EvalPlanValue.context plan (ctx P).M (ctx P).σ ρ0)
    accFamMember [(1, accIntroMember)] (.empty : EnvWfT emptyEnv) rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT
  exact EvalPlanValue.memberValue_agreeOn P (installed P) (table P) (Dom plan.node.E0)
    (prefix_agree P) plan (ctx P).σ hReads accRecMember recursor_reads

/-- Produced new-table faithfulness identifies the actual installed recursor. -/
theorem recursor_equiv (P : Premises4) :
    Equiv (table P 2 [1])
      (EvalPlanValue.memberValue (ctx P).M (ctx P).σ plan accRecMember) := by
  have h := (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1 2 accRecMember rfl [1]
  rw [canonical_plan, recursor_context] at h
  change Equiv (table P 2 [1])
    (EvalPlanValue.memberValue (mkM P (table P)) (ctx P).σ plan accRecMember) at h
  exact h.trans (member_equiv P).symm

noncomputable def currentContext (P : Premises4) : Context :=
  EvalPlanValue.context plan (mkM P (table P)) (ctx P).σ (input P (installed P))

theorem current_context (P : Premises4) :
    currentContext P = (ctx P).withModel (mkM P (table P)) := by
  rfl

noncomputable def endpoint (P : Premises4) : PSet.{4} :=
  EvalPlanValue.endValue (mkM P (table P)) (ctx P).σ plan (input P (installed P))

theorem endpoint_equiv (P : Premises4) :
    Equiv (PropEvalValueAttack.result P) (endpoint P) := by
  have h := EvalPlanValue.endValue_agreeOn_group P (installed P) (table P)
    plan (ctx P).σ accFamMember [(1, accIntroMember)] (.empty : EnvWfT emptyEnv) rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT
    (prefix_agree P) (input P (installed P))
  change Equiv
    (EvalPlanValue.endValue (ctx P).M (ctx P).σ plan (input P (installed P)))
    (endpoint P) at h
  rw [EvalPlanValueAttack.endpoint_eq P] at h
  exact h

/-- The literal evaluation relation is transported to the actual new table,
and output congruence supplies its actual newly extracted value. -/
theorem endpoint_eval (P : Premises4) :
    Eval (currentContext P) (key [parameter]) (endpoint P) := by
  have hReads := EvalPlanScope.endpointReads_of_group (ctx P)
    accFamMember [(1, accIntroMember)] (.empty : EnvWfT emptyEnv) rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT
  have he := (Eval.model_iff (C := ctx P) P (installed P) (table P) (Dom plan.node.E0)
    rfl (prefix_agree P) hReads.toNodeReads (key [parameter])
    (PropEvalValueAttack.result P)).mp (PropEvalValueAttack.result_spec P).2
  rw [current_context]
  exact he.output_congr (endpoint_equiv P).symm

/-- Decoding uses the shared decider and never reads the constant table.
Prove this with the two tables abstract, before specializing either one. -/
private theorem ed_table (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) (A : PSet.{4}) :
    Ed (mkM P μ) A = Ed (mkM P ν) A := rfl

theorem endpoint_typed (P : Premises4) :
    endpoint P ∈ Ed (mkM P (table P)) (fapp (motive P (installed P)) pempty) := by
  rw [ed_table P (table P) (installed P)]
  exact mem_congr_left (endpoint_equiv P) (PropEvalValueAttack.result_typed P)

/-- This IH uses the new installed table's Context and bounded leaf value. -/
noncomputable def ihValue (P : Premises4) : PSet.{4} :=
  (tel (currentContext P).M (currentContext P).σ [.bvar 2] [.bvar 3]
    (vcons pempty (start P (installed P)))).indexedIH (currentContext P).M
      (fun i _ => PropEvalValue.result (currentContext P) (.param 0) i) pempty

theorem ih_empty (P : Premises4) : Equiv (ihValue P) pempty := by
  let M := mkM P (table P)
  have he : Equiv (Ed M (tyv (Ed M parameter))) pempty :=
    (ed_tyv M (dich_ed M parameter)).trans (parameter_empty P (table P))
  have hLam : ∀ F : PSet.{4} → PSet.{4},
      Equiv (lamVal M (tyv (Ed M parameter)) F) pempty := by
    intro F
    have hp : LamProof M (tyv (Ed M parameter)) F := by
      intro x hx
      exact (not_mem_pempty (mem_congr_right he hx)).elim
    unfold lamVal
    rw [cond_pos hp]
    exact Equiv.rfl
  change Equiv (lamVal M (tyv (Ed M parameter)) _) pempty
  exact hLam _

theorem ih_typed (P : Premises4) :
    ihValue P ∈ Ed (currentContext P).M
      (den (currentContext P).M (currentContext P).σ
        (vcons pempty (start P (installed P))) accIhTy) := by
  let M := mkM P (table P)
  apply mem_congr_left (ih_empty P).symm
  change pempty ∈ Ed M (piVal M parameter
    (fun x => fapp (motive P (installed P)) (fapp pempty x)))
  have hp : PiProp M parameter (fun x => fapp (motive P (installed P)) (fapp pempty x)) := by
    intro x hx
    exact (not_mem_pempty (mem_congr_right (parameter_empty P (table P)) hx)).elim
  apply mem_congr_right (ed_piVal_of_prop M hp).symm
  exact mem_tv.mpr ⟨fun x hx =>
    (not_mem_pempty (mem_congr_right (parameter_empty P (table P)) hx)).elim, Equiv.rfl⟩

/-- Iota for the installed recursor uses its new-table normalized IH. -/
theorem installed_iota (P : Premises4) :
    Equiv (fapps (table P 2 [1])
      [parameter, motive P (installed P), minor P (installed P), pempty])
      (fapps (minor P (installed P)) [pempty, ihValue P]) := by
  have hih : LEq [pempty, PropEvalValueAttack.ihValue P] [pempty, ihValue P] :=
    ⟨Equiv.rfl, ⟨(PropEvalValueAttack.ih_empty P).trans (ih_empty P).symm, True.intro⟩⟩
  exact ((fapps_congr (recursor_equiv P) _).trans
    (EvalPlanValueAttack.member_iota P)).trans
      (fapps_congr_args (minor P (installed P)) hih)

theorem installed_application_typed (P : Premises4) :
    fapps (table P 2 [1])
      [parameter, motive P (installed P), minor P (installed P), pempty] ∈
      Ed (mkM P (table P)) (fapp (motive P (installed P)) pempty) := by
  rw [ed_table P (table P) (installed P)]
  exact mem_congr_left (fapps_congr (recursor_equiv P) _).symm
    (EvalPlanValueAttack.application_typed P)

theorem installed_application_nonempty (P : Premises4) :
    ¬ Equiv (fapps (table P 2 [1])
      [parameter, motive P (installed P), minor P (installed P), pempty]) pempty := by
  have he := (fapps_congr (recursor_equiv P)
    [parameter, motive P (installed P), minor P (installed P), pempty]).trans
      (EvalPlanValueAttack.member_application P)
  rw [EvalPlanValueAttack.endpoint_eq P] at he
  intro h
  exact PropEvalValueAttack.result_nonempty P (he.symm.trans h)

/-- The literal old operation remains rejected even under the new table. -/
theorem old_endpoint_rejected (P : Premises4) (old : List (List FieldShape)) :
    RecPlanValue.endValue (mkM P (table P)) (ctx P).σ fd old (input P (installed P)) ∉
      Ed (mkM P (table P)) (fapp (motive P (installed P)) pempty) := by
  rw [ed_table P (table P) (installed P)]
  have hn := endpoint_not_mem P (installed P) (installed_family P) old
  rw [PlanRole.endpoint_of_dec (M := mkM P (installed P)) (M' := mkM P (table P)) rfl] at hn
  exact hn

def Witness (P : Premises4) : Prop :=
  EvalPlanValueAttack.Witness P ∧
  EvalRole.Faithful RawFamily.role P (table P) (envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  EvalRole.ReadsClosed (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  (currentContext P).σ 0 = 1 ∧
  TelFits (mkM P (table P)) (ctx P).σ
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
    [parameter, motive P (installed P), minor P (installed P), pempty] ∧
  Eval (currentContext P) (key [parameter]) (endpoint P) ∧
  endpoint P ∈ Ed (mkM P (table P)) (fapp (motive P (installed P)) pempty) ∧
  ihValue P ∈ Ed (currentContext P).M (den (currentContext P).M (currentContext P).σ
    (vcons pempty (start P (installed P))) accIhTy) ∧
  fapps (table P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty] ∈
      Ed (mkM P (table P)) (fapp (motive P (installed P)) pempty) ∧
  Equiv (fapps (table P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty])
    (fapps (minor P (installed P)) [pempty, ihValue P]) ∧
  ¬ Equiv (fapps (table P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty]) pempty ∧
  ∀ old : List (List FieldShape),
    RecPlanValue.endValue (mkM P (table P)) (ctx P).σ fd old (input P (installed P)) ∉
      Ed (mkM P (table P)) (fapp (motive P (installed P)) pempty)

/-- The installed equations, typed input, literal Eval and installed iota compose. -/
theorem component_witness (P : Premises4) : Witness P :=
  ⟨EvalPlanValueAttack.component_witness P,
    (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1,
    (EvalRole.rawTable_spec P AccEnv.accEnvWfT).2, rfl, arguments_fit P,
    endpoint_eval P, endpoint_typed P, ih_typed P, installed_application_typed P,
    installed_iota P, installed_application_nonempty P, old_endpoint_rejected P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalInstalledAttack
