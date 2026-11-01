import rcic.RcicF3NormRoleTable
import rcic.RcicF3NatFixture

/-!
# The actual normalized Nat plan and installed endpoint

The canonical plan comes from the admitted Nat group scan. Its successor
field is already reader-normal at every successful fuel. The normalized
descriptor therefore equals that scan's raw descriptor, and the actual
operational plan is [[], [recursive 0]]. These facts give exact endpoint
compatibility and the stored recursor equation at the normalized table.

Only this concrete environment's role contexts are identified. No family
admissibility, family inhabitance, MemberSound, or new invariant is asserted.
The original stored member type and the full universe valuation are retained.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormNatPlan
open Rcic.Declarative Rcic.Model.PS

theorem ctorClasses :
    ∀ c ∈ [(1, natZeroMember), (2, natSuccMember)], c.2.mclass = .constructorM := by
  intro c hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 0) (fm := natFamMember)
    (ctors := [(1, natZeroMember), (2, natSuccMember)]) (rr := 3) (rm := natRecMemberU)
    rfl ctorClasses rfl natMembersT

noncomputable abbrev fd : FamData := famDataOf plan.node.a

theorem scan : scanRec natMembersT = some fd :=
  (groupNode EnvWfT.empty (f := 0) (fm := natFamMember)
    (ctors := [(1, natZeroMember), (2, natSuccMember)]) (rr := 3) (rm := natRecMemberU)
    rfl ctorClasses rfl natMembersT).property

theorem family_body (node : NatNode) : transparentBody node.E0 0 [] = none := by
  have hm := node.a.family.present
  rw [node.fam, nat_fam node] at hm
  unfold transparentBody
  rw [hm]
  rfl

/-- Reading the literal successor field cannot introduce a Pi domain. -/
theorem field_reader (E : ResolvedEnv) (hbody : transparentBody E 0 [] = none)
    (fuel : Nat) (ds : List (Expr Nat)) (b : Expr Nat)
    (hr : piTelescopeFuel E fuel (.const 0 []) = some (ds, b)) :
    (ds, b) = ([], .const 0 []) := by
  cases fuel with
  | zero => cases hr
  | succ fuel =>
      cases fuel with
      | zero => cases hr
      | succ fuel =>
          have he : piTelescopeFuel E (fuel + 1 + 1) (.const 0 []) =
              some ([], .const 0 []) := by
            simp only [piTelescopeFuel, whnfFuel, appsSpine, hbody]
          exact Option.some.inj (hr.symm.trans he)

theorem field_identity (E : ResolvedEnv) (hbody : transparentBody E 0 [] = none)
    {fuel f nu np ni prior : Nat} {s : FieldShape}
    (p : EvalPlan.Field E fuel f nu np ni prior (.const 0 []) s) :
    PiValueRule.fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec p) = .const 0 [] := by
  cases p with
  | plain => rfl
  | recursive r =>
      have h := field_reader E hbody fuel r.domains
        (foldApps (.const f (canonL nu)) r.arguments) r.read
      have hd : r.domains = [] := congrArg Prod.fst h
      have hb : foldApps (.const f (canonL nu)) r.arguments = .const 0 [] :=
        congrArg Prod.snd h
      change policyPi r.domains (foldApps (.const f (canonL nu)) r.arguments) = .const 0 []
      rw [hd, hb]
      rfl

theorem fields_identity (E : ResolvedEnv) (hbody : transparentBody E 0 [] = none)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hfields : ∀ A ∈ Fs, A = .const 0 []) :
    (EvalPlanNormal.specs p).map (PiValueRule.fieldExpr f (canonL nu)) = Fs := by
  revert hfields
  induction p with
  | nil => intro _; rfl
  | @cons prior s A ss Fs head tail ih =>
      intro hfields
      have hA := hfields A (List.mem_cons_self _ _)
      have ht : ∀ B ∈ Fs, B = .const 0 [] :=
        fun B hB => hfields B (List.mem_cons_of_mem A hB)
      have hh : PiValueRule.fieldExpr f (canonL nu)
          (EvalPlanNormal.fieldSpec head) = A := by
        subst A
        exact field_identity E hbody head
      change PiValueRule.fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec head) ::
        (EvalPlanNormal.specs tail).map (PiValueRule.fieldExpr f (canonL nu)) = A :: Fs
      rw [hh, ih ht]

theorem fields_eq (j : Fin plan.node.a.constructors.length) :
    EvalPlanNormal.fields plan j = (plan.node.a.constructorViews j).fields := by
  apply fields_identity plan.node.E0 (family_body plan.node) (plan.constructors j).fields
  intro A hA
  rcases (nat_views plan.node j).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
  · rw [hf] at hA
    exact (List.not_mem_nil _ hA).elim
  · rw [hf] at hA
    exact List.mem_singleton.mp hA

theorem constructors_eq : EvalPlanNormal.constructors plan = fd.ctors := by
  apply List.ext_getElem
  · exact (EvalPlanNormal.ctors_length plan).trans
      (famDataOf_ctors_length plan.node.a).symm
  · intro j hn hr
    let k : Fin plan.node.a.constructors.length :=
      ⟨j, by simpa only [fd, famDataOf_ctors_length] using hr⟩
    have hN := EvalPlanNormal.ctor_get plan ⟨j, hn⟩
    have hk : EvalPlanNormal.index plan ⟨j, hn⟩ = k := Fin.ext rfl
    rw [hk, fields_eq k] at hN
    have hR := famDataOf_ctor plan.node.a k
    change fd.ctors[j]? =
      some ((plan.node.a.constructorViews k).fields,
        (plan.node.a.constructorViews k).resultIndices) at hR
    rw [List.getElem?_eq_getElem hr] at hR
    exact hN.trans (Option.some.inj hR).symm

/-- The complete descriptor retains the constructor fields and policy. -/
theorem normalized_descriptor : EvalPlanNormal.fd plan = fd := by
  unfold EvalPlanNormal.fd
  rw [constructors_eq]

theorem constructors_exact :
    fd.ctors = [([], []), ([.const 0 []], [])] := by
  have hlen : plan.node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) plan.node rfl
  apply List.ext_getElem
  · simpa only [fd, famDataOf_ctors_length, List.length_cons, List.length_nil] using hlen
  · intro j hj hr
    let i : Fin plan.node.a.constructors.length :=
      ⟨j, by simpa only [fd, famDataOf_ctors_length] using hj⟩
    have h := famDataOf_ctor plan.node.a i
    change fd.ctors[j]? = some ((plan.node.a.constructorViews i).fields,
      (plan.node.a.constructorViews i).resultIndices) at h
    rw [List.getElem?_eq_getElem hj] at h
    rw [Option.some.inj h, (nat_views plan.node i).2.1]
    rcases (nat_views plan.node i).2.2 with ⟨hf, hpos⟩ | ⟨hf, hpos⟩
    · change j = 0 at hpos
      subst j
      rw [hf] <;> rfl
    · change j = 1 at hpos
      subst j
      rw [hf] <;> rfl

/-- The scan's entire family descriptor, including its actual policy. -/
theorem descriptor :
    fd = ⟨0, [], [], .succ .zero, [([], []), ([.const 0 []], [])],
      plan.node.a.policy⟩ := by
  change (⟨plan.node.a.family.ref, plan.node.a.family.parameters,
    plan.node.a.family.indices, plan.node.a.family.resultLevel, fd.ctors,
    plan.node.a.policy⟩ : FamData) = _
  rw [plan.node.fam, (nat_family plan.node).1, (nat_family plan.node).2.1,
    (nat_family plan.node).2.2, constructors_exact]
  rfl

theorem arity : plan.node.a.family.member.arity = 0 := by
  rw [nat_fam plan.node]
  rfl

theorem bounded : FamBounded fd 0 := by
  rw [descriptor]
  constructor
  · intro e he
    exact (List.not_mem_nil e he).elim
  · intro e he
    exact (List.not_mem_nil e he).elim
  · rfl
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨fun e he => (List.not_mem_nil e he).elim,
        fun e he => (List.not_mem_nil e he).elim⟩
    · have hc : c = ([.const 0 []], []) := List.mem_singleton.mp hc
      subst c
      exact ⟨fun e he => by rw [List.mem_singleton.mp he]; rfl,
        fun e he => (List.not_mem_nil e he).elim⟩

theorem field_shape (E : ResolvedEnv) (hbody : transparentBody E 0 [] = none)
    {fuel f nu np ni prior : Nat} {s : FieldShape} (hf : f = 0)
    (p : EvalPlan.Field E fuel f nu np ni prior (.const 0 []) s) :
    s = .recursive 0 := by
  subst f
  cases p with
  | plain h => cases h
  | @recursive inner r =>
      have hd : r.domains = [] := congrArg Prod.fst
        (field_reader E hbody fuel r.domains
          (foldApps (.const 0 (canonL nu)) r.arguments) r.read)
      have hi : inner = 0 := r.depth.symm.trans (congrArg List.length hd)
      exact congrArg FieldShape.recursive hi

theorem singleton_shapes (E : ResolvedEnv) (hbody : transparentBody E 0 [] = none)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} (hf : f = 0)
    (p : EvalPlan.Fields E fuel f nu np ni prior ss [.const 0 []]) :
    ss = [.recursive 0] := by
  cases p with
  | cons head tail =>
      cases tail with
      | nil => exact congrArg (fun s => [s]) (field_shape E hbody hf head)

theorem node_shapes (node : NatNode) (i : Fin node.a.constructors.length) :
    node.h14.shapesAt i = if i.val = 0 then [] else [.recursive 0] := by
  let c := EvalPlan.constructorOfNode node i
  have hc : c.shapes = node.h14.shapesAt i := c.shapes_admitted
  rcases (nat_views node i).2.2 with ⟨hfields, hpos⟩ | ⟨hfields, hpos⟩
  · have hl := c.fields.length
    rw [hfields] at hl
    have hs : c.shapes = [] := List.eq_nil_of_length_eq_zero hl
    exact hc.symm.trans (hs.trans (if_pos hpos).symm)
  · have hp := c.fields
    rw [hfields] at hp
    have hs : c.shapes = [.recursive 0] :=
      singleton_shapes node.E0 (family_body node) node.fam hp
    have hn : i.val ≠ 0 := fun h => Nat.noConfusion (hpos.symm.trans h)
    exact hc.symm.trans (hs.trans (if_neg hn).symm)

theorem node_plan (node : NatNode) :
    RecPlan.nodePlan node = [[], [.recursive 0]] := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) node rfl
  apply List.ext_getElem
  · simpa only [RecPlan.nodePlan, List.length_map, List.length_range,
      List.length_cons, List.length_nil] using hlen
  · intro j hj hr
    have hi : j < node.a.constructors.length := by
      rw [hlen]
      exact hr
    let i : Fin node.a.constructors.length := ⟨j, hi⟩
    have hs := (RecPlan.nodePlan_spec node i).1
    rw [List.getElem?_eq_getElem hj] at hs
    refine (Option.some.inj hs).trans ((node_shapes node i).trans ?_)
    change (if j = 0 then [] else [.recursive 0]) =
      ([[], [.recursive 0]] : List (List FieldShape))[j]'hr
    rcases nat_ctor node i with ⟨_, hpos⟩ | ⟨_, hpos⟩
    · change j = 0 at hpos
      subst j
      rfl
    · change j = 1 at hpos
      subst j
      rfl

theorem raw_plan : RecPlan.rawPlan fd = [[], [.recursive 0]] := by
  unfold RecPlan.rawPlan
  rw [constructors_exact]
  have hf : fd.fref = 0 := plan.node.fam
  rw [hf]
  rfl

theorem endpoint_eq (M : Interp.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ plan ρ = recEnd M σ fd ρ := by
  have hn : evalTotal σ plan.node.a.family.resultLevel ≠ 0 := by
    rw [(nat_family plan.node).2.2]
    change 1 ≠ 0
    decide
  rw [EvalPlanValue.endValue_fallback M σ plan ρ (fun h => hn h.1),
    node_plan plan.node, ← raw_plan]
  exact (RecPlanValue.laws M σ fd (RecPlan.rawPlan fd)).2 ρ

theorem member_value_eq (M : Interp.{4}) (σ : Nat → Nat) :
    EvalPlanValue.memberValue M σ plan natRecMemberU =
      piLam M σ (recEnd M σ fd) ρ0 natRecMemberU.mtype := by
  unfold EvalPlanValue.memberValue
  rw [funext (endpoint_eq M σ)]

theorem canonical_plan : EvalRole.envPlan natEnvUWfT 3 = some plan := rfl

theorem normalized_context : NormRole.envCtx natEnvUWfT =
    groupRoles fd 0 3 (fun _ => .plain) := by
  change groupRoles (EvalPlanNormal.fd plan) 0 3 (fun _ => .plain) = _
  rw [normalized_descriptor]

theorem original_context : envCtx natEnvUWfT =
    groupRoles fd 0 3 (fun _ => .plain) :=
  envCtx_group_some (ctors := [(1, natZeroMember), (2, natSuccMember)])
    EnvWfT.empty rfl ctorClasses rfl natMembersT fd scan

/-- Equality of role data at this exact Nat environment only. -/
theorem context_eq : NormRole.envCtx natEnvUWfT = envCtx natEnvUWfT :=
  normalized_context.trans original_context.symm

theorem family_role : NormRole.envCtx natEnvUWfT 0 = .fam fd := by
  rw [normalized_context]
  exact if_pos rfl

theorem recursor_role : NormRole.envCtx natEnvUWfT 3 = .recursor fd := by
  rw [normalized_context]
  exact groupRoles_at_rr fd (by decide : 0 < 3) (fun _ => .plain)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P natEnvUWfT

theorem faithful (P : Premises4) :
    EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx natEnvUWfT)
      (EvalRole.envPlan natEnvUWfT) natEnvU :=
  (NormRole.table_spec P natEnvUWfT).1

theorem family_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 0 vs) (RawFamily.role P (table P) fd vs) := by
  have h := faithful P 0 natFamMember rfl vs
  rw [family_role] at h
  exact h

theorem installed_recursor (P : Premises4) (vs : List Nat) :
    Equiv (table P 3 vs)
      (piLam (mkM P (table P)) (σOf vs)
        (recEnd (mkM P (table P)) (σOf vs) fd) ρ0 natRecMemberU.mtype) := by
  have h := faithful P 3 natRecMemberU rfl vs
  rw [recursor_role, canonical_plan] at h
  change Equiv (table P 3 vs)
    (EvalPlanValue.memberValue (mkM P (table P)) (σOf vs) plan natRecMemberU) at h
  rw [member_value_eq] at h
  exact h

noncomputable def successorSlot : Fin plan.node.a.constructors.length :=
  ⟨1, by
    rw [node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) plan.node rfl]
    decide⟩

/-- Actual stored cache data witnesses the reader/shape premises. -/
theorem actual_fields_inhabited :
    Nonempty (EvalPlan.Fields plan.node.E0
      (plan.constructors successorSlot).fuel 0 0 0 0 0
      [.recursive 0] [.const 0 []]) := by
  have hfields : (plan.node.a.constructorViews successorSlot).fields = [.const 0 []] := by
    rcases (nat_views plan.node successorSlot).2.2 with ⟨_, hzero⟩ | ⟨hf, _⟩
    · have h10 : (1 : Nat) = 0 := hzero
      exact False.elim (Nat.noConfusion h10)
    · exact hf
  have hn : successorSlot.val ≠ 0 := fun h => Nat.noConfusion h
  have hshapes : (plan.constructors successorSlot).shapes = [.recursive 0] :=
    (plan.constructors successorSlot).shapes_admitted.trans
      ((node_shapes plan.node successorSlot).trans (if_neg hn))
  obtain ⟨hparams, hindices, _⟩ := nat_family plan.node
  refine ⟨?_⟩
  simpa only [plan.node.fam, arity, hparams, hindices, hshapes, hfields,
    List.length_nil] using (plan.constructors successorSlot).fields

theorem actual_field_inhabited :
    Nonempty (EvalPlan.Field plan.node.E0
      (plan.constructors successorSlot).fuel 0 0 0 0 0
      (.const 0 []) (.recursive 0)) := by
  obtain ⟨fields⟩ := actual_fields_inhabited
  cases fields with
  | cons head tail => exact ⟨head⟩

def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT natEnvU) ∧
  EvalPlanNormal.fd plan = fd ∧
  fd = ⟨0, [], [], .succ .zero, [([], []), ([.const 0 []], [])],
    plan.node.a.policy⟩ ∧
  plan.node.a.family.member.arity = 0 ∧
  FamBounded fd 0 ∧
  EvalRole.envPlan natEnvUWfT 3 = some plan ∧
  RecPlan.nodePlan plan.node = [[], [.recursive 0]] ∧
  RecPlan.rawPlan fd = [[], [.recursive 0]] ∧
  NormRole.envCtx natEnvUWfT = envCtx natEnvUWfT ∧
  (∀ (M : Interp.{4}) σ ρ,
    EvalPlanValue.endValue M σ plan ρ = recEnd M σ fd ρ) ∧
  EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx natEnvUWfT)
    (EvalRole.envPlan natEnvUWfT) natEnvU ∧
  (∀ vs, Equiv (table P 3 vs)
    (piLam (mkM P (table P)) (σOf vs)
      (recEnd (mkM P (table P)) (σOf vs) fd) ρ0 natRecMemberU.mtype)) ∧
  Nonempty (EvalPlan.Fields plan.node.E0
    (plan.constructors successorSlot).fuel 0 0 0 0 0 [.recursive 0] [.const 0 []]) ∧
  Nonempty (EvalPlan.Field plan.node.E0
    (plan.constructors successorSlot).fuel 0 0 0 0 0 (.const 0 []) (.recursive 0))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨⟨natEnvUWfT⟩, normalized_descriptor, descriptor, arity, bounded,
    canonical_plan, node_plan plan.node,
    raw_plan, context_eq, endpoint_eq, faithful P, installed_recursor P,
    actual_fields_inhabited, actual_field_inhabited⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormNatPlan
