import rcic.RcicF3IndexedPropGroup
import rcic.RcicF3IndexedPropEvalAttack
import rcic.RcicF3PointwisePropGroupAttack

/-!
# Actual pointwise-table membership and literal legacy package composition

The new stored recursor, constructor and legacy package producers are
invoked at the actual pointwise table of the admitted AccR fixture. Their
group composition uses the separate indexed bound, the original walk and
D bounds, and the produced empty predecessor. The constructor arguments
are inhabited; the selected recursive child domain remains empty.

The no-legacy-witness theorem is an explicit conjunct of the package
witness. Consequently its IotaAt component is not evidence of actual
higher-order Acc computation. No modern shape-schema equation is proved
here. The previous indexed-evaluation witness is retained separately at
its fixed normalized-role table and the same Premises4; no equality of
those two tables or of their universal invariants is asserted.

This is an AccR fixture, not imported Acc or a complete AccP indexed-bound
instance. The whole checked tier and its descriptor are unchanged.
The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.IndexedPropGroupAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PlanPropEndAttack
open PropEvalAdmittedInputsAttack (bound)
open PointwisePropGroupAttack
  (table ctorClasses faithful canonical_plan uniform_prop policy)

theorem indexed_bound :
    IndexedFieldBounds.BoundGIndexed bound AccEnv.accEnvWfT :=
  IndexedPropEvalAttack.indexed_bound

/-- The new membership producer is invoked directly, independently of
the legacy IotaAt component and of completed-group soundness. -/
theorem recursor_sound (P : Premises4) :
    MemberSound P (table P) bound 2 accRecMember :=
  IndexedPropRecMem.member_sound P (table P) bound
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    .empty rfl ctorClasses rfl AccEnv.accMembersT
    indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) uniform_prop policy

/-- Every original constructor instance uses the retained own-bound
typing conjunct of BoundGIndexed. -/
theorem constructor_sound (P : Premises4) :
    MemberSound P (table P) bound 1 accIntroMember := by
  have hindex : 0 < (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl ctorClasses rfl
      AccEnv.accMembersT).node.a.constructors.length := by
    rw [canonical_plan]
    decide
  have h := IndexedPropCtor.member_sound P (table P) bound
    (f := 0) (fm := accFamMember) (ctors := [(1, accIntroMember)])
    (rr := 2) (rm := accRecMember) .empty rfl ctorClasses rfl AccEnv.accMembersT
    indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (PointwiseRole.arities_agree accEnv)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) uniform_prop ⟨0, hindex⟩
  have hget : (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl ctorClasses rfl
      AccEnv.accMembersT).node.a.constructors[0]? = some accIntroMember := by
    rw [canonical_plan]
    rfl
  have hc := Option.some.inj ((List.getElem?_eq_getElem hindex).symm.trans hget)
  simpa only [hc] using h

theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (table P)) σ [.sort .zero, accField] ρ0 [parameter, pempty] :=
  PointwisePropGroupAttack.arguments_fit P

/-- This actual constructor application uses the new constructor theorem. -/
theorem constructor_mem (P : Premises4) :
    fapps (table P 1 []) [parameter, pempty] ∈
      Ed (mkM P (table P)) (fapp (table P 0 []) parameter) := by
  have hm := (constructor_sound P σ [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1
  change table P 1 [] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi [.sort .zero, accField]
      (accApp (.bvar 1)))) at hm
  exact mem_fapps (mkM P (table P)) σ (accApp (.bvar 1))
    [.sort .zero, accField] ρ0 (table P 1 []) [parameter, pempty] hm (arguments_fit P)

/-- This property is about the legacy witness type in every common
extension. It is independent of a semantic table or Premises4. -/
def NoLegacyWitness : Prop :=
  ∀ (Efin E'' : ResolvedEnv),
    (∀ r m, accEnv.members r = some m → Efin.members r = some m) →
    (∀ r m, E''.members r = some m → Efin.members r = some m) →
    ∀ w : IotaWitness E'', w.recRef = 2 → False

theorem no_legacy_witness : NoLegacyWitness := by
  intro Efin E'' hsubF hsub w hwr
  exact EvalPropRecIota.no_witness
    (f := 0) (rr := 2) (fm := accFamMember) (rm := accRecMember)
    (ctors := [(1, accIntroMember)]) (.empty : EnvWfT emptyEnv)
    AccEnv.accMembersT PlanPropStepAttack.pNode PlanPropStepAttack.pendA
    (by change 1 ≤ 1; exact Nat.le_refl 1) hsubF hsub w hwr

/-- Membership and the empty legacy-witness obligation are composed by
the new package producer. This is not a modern Acc computation law. -/
theorem legacy_package (P : Premises4) :
    RecPkg P (table P) bound accEnv 2 accRecMember :=
  IndexedPropRecPkg.legacy_rec_pkg P (table P) bound
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    .empty rfl ctorClasses rfl AccEnv.accMembersT
    indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities accEnv) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
    uniform_prop policy ⟨PlanPropStepAttack.pNode, PlanPropStepAttack.pendA⟩

/-- The broader bound is used in the actual group composition. The
conclusion remains the current invariant with legacy IotaAt. -/
theorem produced_gInv (P : Premises4) :
    PointwiseRole.GInv P bound AccEnv.accEnvWfT :=
  IndexedPropGroup.legacy_group_step P bound .empty rfl ctorClasses rfl
    AccEnv.accMembersT uniform_prop policy
    ⟨PlanPropStepAttack.pNode, PlanPropStepAttack.pendA⟩
    PlanPropStepAttack.walkAgree indexed_bound PlanPropStepAttack.boundDG
    (PointwiseRole.gInv_empty P bound)

theorem all_sound (P : Premises4) : AllSound P (table P) bound accEnv :=
  (produced_gInv P (PointwiseRole.arities accEnv) (PointwiseRole.arities_agree accEnv)
    (NormRole.envCtx AccEnv.accEnvWfT) (fun _ _ => rfl)
    (EvalRole.envPlan AccEnv.accEnvWfT) (fun _ _ => rfl) (table P) (faithful P)).1

structure RecMemberWitness (P : Premises4) : Prop where
  indexed_bound : IndexedFieldBounds.BoundGIndexed bound AccEnv.accEnvWfT
  faithful : EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities accEnv))
    P (table P) (NormRole.envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv
  member_sound : MemberSound P (table P) bound 2 accRecMember

theorem rec_member_witness (P : Premises4) : RecMemberWitness P :=
  ⟨indexed_bound, faithful P, recursor_sound P⟩

theorem rec_member_nonrefutable (P : Premises4) :
    ¬ (RecMemberWitness P → (Premises4 → False)) :=
  fun h => h (rec_member_witness P) P

structure ConstructorWitness (P : Premises4) : Prop where
  member_sound : MemberSound P (table P) bound 1 accIntroMember
  arguments : TelFits (mkM P (table P)) σ [.sort .zero, accField] ρ0 [parameter, pempty]
  application : fapps (table P 1 []) [parameter, pempty] ∈
    Ed (mkM P (table P)) (fapp (table P 0 []) parameter)
  selected_child_domain_empty : Equiv (Ed (mkM P (table P)) parameter) pempty

theorem constructor_witness (P : Premises4) : ConstructorWitness P :=
  ⟨constructor_sound P, arguments_fit P, constructor_mem P, parameter_empty P (table P)⟩

theorem constructor_nonrefutable (P : Premises4) :
    ¬ (ConstructorWitness P → (Premises4 → False)) :=
  fun h => h (constructor_witness P) P

structure LegacyPackageWitness (P : Premises4) : Prop where
  recursor : RecMemberWitness P
  package : RecPkg P (table P) bound accEnv 2 accRecMember
  no_legacy_witness : NoLegacyWitness

theorem legacy_package_witness (P : Premises4) : LegacyPackageWitness P :=
  ⟨rec_member_witness P, legacy_package P, no_legacy_witness⟩

theorem legacy_package_nonrefutable (P : Premises4) :
    ¬ (LegacyPackageWitness P → (Premises4 → False)) :=
  fun h => h (legacy_package_witness P) P

def Witness (P : Premises4) : Prop :=
  IndexedPropEvalAttack.Witness P ∧
  RecMemberWitness P ∧ ConstructorWitness P ∧ LegacyPackageWitness P ∧
  PointwiseRole.GInv P bound AccEnv.accEnvWfT ∧
  AllSound P (table P) bound accEnv ∧
  ¬ PlanRole.StepAG role P (fun _ => 1)

/-- Same-P composition retains each new producer piece and the literal
old target refutation, with the legacy scope made explicit in its type. -/
theorem component_witness (P : Premises4) : Witness P :=
  ⟨IndexedPropEvalAttack.component_witness P, rec_member_witness P,
    constructor_witness P, legacy_package_witness P, produced_gInv P,
    all_sound P, PlanPropStepAttack.stepAG_false P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedPropGroupAttack
