import rcic.RcicF3NormRoleTable
import rcic.RcicF3RawFamilyRecAtAttack

/-!
# The normalized role at the exact admitted PendA W group

The canonical plan is obtained from the actual group scan. Its recursive
field is already reader-normal, independently of the successful reader's
fuel. Consequently its normalized descriptor is exactly PendAWBridge.fd.
The existing raw small-frame and closure producers therefore apply at all
universe vectors and complete parameter/index keys. The actual normalized
installer supplies a faithful table whose family contains fxZW.

The source also transports the existing independent-valuation nodeCore
recursion witness through the descriptor equality. That component uses
its stated RawFamilyRecAtAttack base table; it is not a claim of typing
the new installed recursor. No NormRole.GInv, universal StepAG, or checked
apex composition is asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAW
open Rcic.Declarative PiIndex

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup natEnvUWfT (f := 4) (fm := PendAW.fam)
    (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) (rr := 7) (rm := PendAW.recMem)
    rfl PendAWGroup.ctorClasses rfl PendAW.membersT

/-- The group scan's own equality identifies its raw descriptor. No
equality of the Type-valued canonical node with pNode is required. -/
theorem raw_descriptor : famDataOf plan.node.a = PendAWBridge.fd :=
  Option.some.inj ((groupNode natEnvUWfT (f := 4) (fm := PendAW.fam)
    (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) (rr := 7) (rm := PendAW.recMem)
    rfl PendAWGroup.ctorClasses rfl PendAW.membersT).property.symm.trans
      PendAWGroup.scanHit)

theorem family_body : transparentBody plan.node.E0 4 [] = none := by
  have hm := plan.node.a.family.present
  rw [plan.node.fam, PendAWGroup.familyMember plan.node] at hm
  change plan.node.E0.members 4 = some PendAW.fam at hm
  unfold transparentBody
  rw [hm]
  rfl

/-- Successful reading of this literal field has the literal one-domain
telescope, at any fuel. Exhausted-fuel cases supply no cache data. -/
theorem field_reader (E : ResolvedEnv) (hbody : transparentBody E 4 [] = none)
    (fuel : Nat) (ds : List (Expr Nat)) (b : Expr Nat)
    (hr : piTelescopeFuel E fuel PendAW.field = some (ds, b)) :
    (ds, b) = ([.bvar 0], .app (.const 4 []) (.bvar 1)) := by
  cases fuel with
  | zero => cases hr
  | succ fuel =>
      cases fuel with
      | zero => cases hr
      | succ fuel =>
          cases fuel with
          | zero => cases hr
          | succ fuel =>
              have he : piTelescopeFuel E (fuel + 1 + 1 + 1) PendAW.field =
                  some ([.bvar 0], .app (.const 4 []) (.bvar 1)) := by
                simp only [PendAW.field, piTelescopeFuel, whnfFuel, appsSpine,
                  List.nil_append, hbody]
              exact Option.some.inj (hr.symm.trans he)

theorem field_identity (E : ResolvedEnv) (hbody : transparentBody E 4 [] = none)
    {fuel f nu np ni prior : Nat} {s : FieldShape}
    (p : EvalPlan.Field E fuel f nu np ni prior PendAW.field s) :
    PiValueRule.fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec p) = PendAW.field := by
  cases p with
  | plain => rfl
  | recursive r =>
      have h := field_reader E hbody fuel r.domains
        (foldApps (.const f (canonL nu)) r.arguments) r.read
      have hd : r.domains = [.bvar 0] := congrArg Prod.fst h
      have hb : foldApps (.const f (canonL nu)) r.arguments =
          .app (.const 4 []) (.bvar 1) := congrArg Prod.snd h
      change policyPi r.domains (foldApps (.const f (canonL nu)) r.arguments) = PendAW.field
      rw [hd, hb]
      rfl

theorem fields_identity (E : ResolvedEnv) (hbody : transparentBody E 4 [] = none)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hfields : ∀ A ∈ Fs, A = PendAW.field) :
    (EvalPlanNormal.specs p).map (PiValueRule.fieldExpr f (canonL nu)) = Fs := by
  revert hfields
  induction p with
  | nil => intro _; rfl
  | @cons prior s A ss Fs head tail ih =>
      intro hfields
      have hA := hfields A (List.mem_cons_self _ _)
      have ht : ∀ B ∈ Fs, B = PendAW.field :=
        fun B hB => hfields B (List.mem_cons_of_mem _ hB)
      have hh : PiValueRule.fieldExpr f (canonL nu)
          (EvalPlanNormal.fieldSpec head) = A := by
        subst A
        exact field_identity E hbody head
      change PiValueRule.fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec head) ::
        (EvalPlanNormal.specs tail).map (PiValueRule.fieldExpr f (canonL nu)) = A :: Fs
      rw [hh, ih ht]

theorem fields_eq (j : Fin plan.node.a.constructors.length) :
    EvalPlanNormal.fields plan j = (plan.node.a.constructorViews j).fields := by
  apply fields_identity plan.node.E0 family_body (plan.constructors j).fields
  intro A hA
  rcases (PendAWGroup.views plan.node j).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
  · rw [hf] at hA
    exact (List.not_mem_nil _ hA).elim
  · rw [hf] at hA
    exact List.mem_singleton.mp hA

theorem constructors_eq :
    EvalPlanNormal.constructors plan = (famDataOf plan.node.a).ctors := by
  apply List.ext_getElem
  · exact (EvalPlanNormal.ctors_length plan).trans
      (famDataOf_ctors_length plan.node.a).symm
  · intro j hn hr
    let k : Fin plan.node.a.constructors.length :=
      ⟨j, by simpa only [famDataOf_ctors_length] using hr⟩
    have hN := EvalPlanNormal.ctor_get plan ⟨j, hn⟩
    have hk : EvalPlanNormal.index plan ⟨j, hn⟩ = k := Fin.ext rfl
    rw [hk, fields_eq k] at hN
    have hR := famDataOf_ctor plan.node.a k
    change (famDataOf plan.node.a).ctors[j]? =
      some ((plan.node.a.constructorViews k).fields,
        (plan.node.a.constructorViews k).resultIndices) at hR
    rw [List.getElem?_eq_getElem hr] at hR
    exact hN.trans (Option.some.inj hR).symm

/-- The exact normalized descriptor, including constructor order and its
parameter, index, level and elimination-policy fields, is unchanged here. -/
theorem normalized_descriptor : EvalPlanNormal.fd plan = PendAWBridge.fd := by
  have he : EvalPlanNormal.fd plan = famDataOf plan.node.a := by
    unfold EvalPlanNormal.fd
    rw [constructors_eq]
  exact he.trans raw_descriptor

theorem canonical_plan : EvalRole.envPlan PendAWGroup.wft 7 = some plan := rfl

theorem family_role : NormRole.envCtx PendAWGroup.wft 4 =
    .fam (EvalPlanNormal.fd plan) := by
  change groupRoles (EvalPlanNormal.fd plan) 4 7 (NormRole.envCtx natEnvUWfT) 4 = _
  exact if_pos rfl

theorem node_role : NormRole.envCtx PendAWGroup.wft 6 =
    .ctor (EvalPlanNormal.fd plan) 1 := by
  change groupRoles (EvalPlanNormal.fd plan) 4 7 (NormRole.envCtx natEnvUWfT) 6 = _
  simp only [groupRoles, if_neg (by decide : ¬ (6 = 4)),
    if_neg (by decide : ¬ (6 = 7)), if_pos (by decide : 4 < 6 ∧ 6 < 7)]

theorem normalized_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    RawFamily.Admissible (EvalPlanNormal.fd plan)
      (RawFamily.frame P μ (EvalPlanNormal.fd plan)) := by
  rw [normalized_descriptor]
  exact RawWFrame.raw_admissible P μ

theorem normalized_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    RawFamily.Closed P μ (EvalPlanNormal.fd plan)
      (RawFamily.frame P μ (EvalPlanNormal.fd plan)) := by
  rw [normalized_descriptor]
  exact RawFamilyInductionAttack.w_closed P μ

theorem normalized_mono (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    RawFamily.ConstructorMono P μ (EvalPlanNormal.fd plan) := by
  rw [normalized_descriptor]
  exact RawFamilyInductionAttack.w_mono P μ

theorem exact_stage (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∀ vs i, RawFamily.frame P μ (EvalPlanNormal.fd plan) vs i ∈ W4 1 ∧
      ¬ pempty ∈ RawFamily.frame P μ (EvalPlanNormal.fd plan) vs i := by
  rw [normalized_descriptor]
  intro vs i
  have ha := RawWFrame.raw_admissible P μ vs i
  refine ⟨ha.1, ?_⟩
  have hd := ha.2
  change ∀ z, z ∈ RawFamily.frame P μ PendAWBridge.fd vs i → ¬ Equiv z pempty at hd
  exact fun h => hd pempty h Equiv.rfl

theorem normalized_height_omega (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ Ed (mkM P μ)
      (fapps (RawFamily.role P μ (EvalPlanNormal.fd plan) []) [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P μ (EvalPlanNormal.fd plan) []) [tyv fxS]) := by
  rw [normalized_descriptor]
  exact RawWFrame.heightOmega_gap P μ

theorem omega_constructor (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    RawFamily.CtorAt P μ (EvalPlanNormal.fd plan)
      (RawFamily.frame P μ (EvalPlanNormal.fd plan)) [] (key [tyv fxS]) (fxZW P) := by
  rw [normalized_descriptor]
  exact (RawFamilyInductionAttack.heightOmega_constructor P μ).1

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P PendAWGroup.wft

theorem faithful (P : Premises4) :
    EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) PendAW.eAll :=
  (NormRole.table_spec P PendAWGroup.wft).1

theorem family_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 4 vs) (RawFamily.role P (table P) (EvalPlanNormal.fd plan) vs) := by
  have h := faithful P 4 PendAW.fam rfl vs
  rw [family_role] at h
  exact h

/-- The exact height-omega element is in the actual normalized installed
family, not merely in an auxiliary signature or as an ordinary payload. -/
theorem installed_height_omega (P : Premises4) :
    fxZW P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) :=
  mem_congr_right (ed_congr (mkM P (table P))
    (fapps_congr (family_value P []) [tyv fxS])).symm
      (normalized_height_omega P (table P)).1

theorem wrong_tag_refused (P : Premises4) (j : Nat) (hj : 2 ≤ j) (xs : List PSet.{4}) :
    dataVal j xs ∉ Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) := by
  intro hz
  have h := mem_congr_right (ed_congr (mkM P (table P))
    (fapps_congr (family_value P []) [tyv fxS])) hz
  rw [normalized_descriptor] at h
  exact RawWFrame.wrong_tag_refused P (table P) j hj xs h

/-- Descriptor transport of the existing actual-node recursion witness.
Its base table and its independent full valuation remain explicit. -/
theorem nodeCore_height_omega (P : Premises4) :
    RecPlan.nodeCore
      (RawFamilyRec.model P (RawFamilyRecAtAttack.base P) (EvalPlanNormal.fd plan))
      PendAW.pNode [pempty, pempty] (fxZW P) ∈ tv True := by
  rw [normalized_descriptor]
  exact (RawFamilyRecAtAttack.inhabited P).1

def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT PendAW.eAll) ∧
  Nonempty (HasTyT PendAW.eAll 0 [] PendAW.leafNat PendAW.wNatTy) ∧
  PendA PendAW.pNode ∧
  EvalPlanNormal.fd plan = PendAWBridge.fd ∧
  EvalRole.envPlan PendAWGroup.wft 7 = some plan ∧
  NormRole.envCtx PendAWGroup.wft 4 = .fam (EvalPlanNormal.fd plan) ∧
  NormRole.envCtx PendAWGroup.wft 6 = .ctor (EvalPlanNormal.fd plan) 1 ∧
  EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) PendAW.eAll ∧
  RawFamily.Admissible (EvalPlanNormal.fd plan)
    (RawFamily.frame P (table P) (EvalPlanNormal.fd plan)) ∧
  RawFamily.Closed P (table P) (EvalPlanNormal.fd plan)
    (RawFamily.frame P (table P) (EvalPlanNormal.fd plan)) ∧
  (∀ vs i, RawFamily.frame P (table P) (EvalPlanNormal.fd plan) vs i ∈ W4 1 ∧
    ¬ pempty ∈ RawFamily.frame P (table P) (EvalPlanNormal.fd plan) vs i) ∧
  RawFamily.CtorAt P (table P) (EvalPlanNormal.fd plan)
    (RawFamily.frame P (table P) (EvalPlanNormal.fd plan)) [] (key [tyv fxS]) (fxZW P) ∧
  fxZW P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) ∧
  fxZW P ∉ El (fapps (famLim P (table P) (EvalPlanNormal.fd plan) []) [tyv fxS]) ∧
  (∀ j, 2 ≤ j → ∀ xs, dataVal j xs ∉
    Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS])) ∧
  RecPlan.nodeCore
    (RawFamilyRec.model P (RawFamilyRecAtAttack.base P) (EvalPlanNormal.fd plan))
    PendAW.pNode [pempty, pempty] (fxZW P) ∈ tv True ∧
  (∀ k, ¬ TierGroup.StepAG P (fun _ => k))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨⟨PendAWGroup.wft⟩, ⟨PendAW.leafNat_typed⟩, PendAW.pendA, normalized_descriptor,
    canonical_plan, family_role, node_role, faithful P,
    normalized_admissible P (table P), normalized_closed P (table P),
    exact_stage P (table P), omega_constructor P (table P), installed_height_omega P,
    (normalized_height_omega P (table P)).2, wrong_tag_refused P,
    nodeCore_height_omega P, PendAWGroup.stepAG_false P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPendAW
