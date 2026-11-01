import rcic.RcicF3IndexedPropPlainIota
import rcic.RcicF3IndexedPropRecMem
import rcic.RcicF3PointwisePropPlainIotaAttack

/-!
# Same-P ordinary-field recovery and an actual plain True redex

The data-valued telescope witness exercises nonempty-spine recovery with
an actual non-proof field. Separately, the admitted True fixture has an
actual typed legacy redex. The new indexed-bound recursor membership,
redex argument recovery and constructor-key endpoint are composed at its
pointwise table. Its index agreement is proved from this fixture's empty
index telescope; no universal index-coherence producer is asserted.

The resulting installed equation returns an explicit nonempty datum at
motive universe 1. Its proof does not invoke the prior redex_equiv theorem.
The two component scopes are kept separate: the data-valued row is not
claimed to be a complete imported group, and True has no constructor fields.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.IndexedPropPlainAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open NormPropPlainTrue (plan witness)
open PlanPropEndAttack (datum domain)
open NormPropPlainIotaAttack (bound σ)
open PointwisePropPlainIotaAttack
  (table faithful uniform_prop motive ρ arguments recursor_value)

noncomputable def ctor : Fin plan.node.a.constructors.length :=
  ⟨0, by rw [NormPropPlainTrue.count]; decide⟩

theorem indexed_bound : IndexedFieldBounds.BoundGIndexed bound trueEnvUWfT :=
  IndexedFieldBounds.of_boundG bound trueEnvUWfT (NormPropPlainTrue.bound bound)

theorem recursor_sound (P : Premises4) :
    MemberSound P (table P) bound 2 trueRecMemberU :=
  IndexedPropRecMem.member_sound P (table P) bound
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) .empty rfl NormPropPlainTrue.ctorClasses
    rfl trueMembersT indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities trueEnvU) (fun _ _ h => nomatch h)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
    uniform_prop (NormPropPlainTrue.policy plan.node)

/-- Actual left membership is obtained from the new stored-member producer. -/
theorem application_mem (P : Premises4) :
    fapps (table P 2 [1]) (arguments P) ∈
      Ed (mkM P (table P)) (fapp (motive P) (table P 1 [])) := by
  have h := (recursor_sound P σ [.param 0] ρ0 rfl
    (fun l hl => by
      cases List.mem_singleton.mp hl
      exact Nat.le_refl 1)).1
  change table P 2 [1] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0
      (policyPi NormPropPlainIotaAttack.domains (.app (.bvar 2) (.bvar 0)))) at h
  exact mem_fapps (mkM P (table P)) σ (.app (.bvar 2) (.bvar 0))
    NormPropPlainIotaAttack.domains ρ0 (table P 2 [1]) (arguments P) h
    (PointwisePropPlainIotaAttack.arguments_fit P)

def context : LCtx :=
  [.assumption (.app (.bvar 0) (.const 1 [])),
    .assumption (.pi (.const 0 []) (.sort (.param 0)))]

def target : Expr Nat := .app (.bvar 1) (.const 1 [])

noncomputable def rhsTyped : HasTyT trueEnvU 1 context (iotaRhsOf witness) target :=
  .bvar context 0 target rfl

/-- The literal legacy left side also has an actual typed derivation. -/
noncomputable def lhsTyped : HasTyT trueEnvU 1 context (iotaLhsOf witness) target := by
  have hrec := HasTyT.const (E := trueEnvU) (n := 1) context 2 [.param 0]
    trueRecMemberU rfl rfl rfl
  have hmo : HasTyT trueEnvU 1 context (.bvar 1)
      (.pi (.const 0 []) (.sort (.param 0))) :=
    .bvar context 1 _ rfl
  have hctor := HasTyT.const (E := trueEnvU) (n := 1) context 1 []
    trueIntroMember rfl rfl rfl
  have h1 := HasTyT.app context (.const 2 [.param 0]) (.bvar 1) _ _ hrec hmo
  have h2 := HasTyT.app context _ (.bvar 0) _ _ h1 rhsTyped
  exact HasTyT.app context _ (.const 1 []) _ _ h2 hctor

theorem context_fit (P : Premises4) :
    Fits (mkM P (table P)) σ context (ρ P) :=
  ⟨⟨True.intro, PointwisePropPlainIotaAttack.motive_mem P⟩,
    PointwisePropPlainIotaAttack.minor_mem P⟩

theorem rhs_hereditary (P : Premises4) :
    HSoundT (mkM P (table P)) σ rhsTyped := by
  intro η hη
  exact fits_lookupType (mkM P (table P)) σ context η hη 0 target rfl

/-- Same-target membership and the nonempty datum produce the nonempty
left branch without using a previously proved iota equation. -/
theorem lhs_nonempty (P : Premises4) :
    ¬ Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) pempty := by
  intro he
  have h := rhs_eq_ed_pempty (application_mem P)
    (PointwisePropPlainIotaAttack.minor_mem P) he
  exact dataVal_ne_pempty _ _ (h.symm.trans he)

/-- The new actual-redex producer is invoked with a typed right side. -/
theorem recovered_arguments (P : Premises4) :
    ∃ ps mo ms is, IndexedPropPlainIota.Arguments (mkM P (table P))
      plan witness σ (ρ P) ctor ps mo ms is :=
  IndexedPropPlainIota.arguments_of_typed_nonempty P (table P) plan trueFamMember
    [(1, trueIntroMember)] .empty trueMembersT (recursor_value P)
    (NormPropPlainTrue.noFun plan.node) (NormPropPlainTrue.fields_free plan.node)
    witness rfl rfl ctor rfl (NormPropPlainTrue.constructor_member plan.node ctor).symm
    σ (ρ P) rhsTyped (rhs_hereditary P) (context_fit P)
    (application_mem P) (PointwisePropPlainIotaAttack.minor_mem P) (lhs_nonempty P)

theorem family_equation (P : Premises4) :
    ∀ vs, Equiv (table P plan.node.a.family.ref vs)
      (ofFrame P (table P) (famDataOf plan.node.a)
        (frame P (table P) (EvalPlanNormal.fd (EvalPlan.ofNode plan.node))) vs) :=
  PointwisePropPrefix.family_equation_of_group P (PointwiseRole.arities trueEnvU)
    (table P) (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) .empty rfl NormPropPlainTrue.ctorClasses
    rfl trueMembersT (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (faithful P) uniform_prop

/-- In this actual fixture the index lists are both proved empty. The
new endpoint is then composed with the recovered fields and actual minor. -/
theorem redex_equiv (P : Premises4) :
    Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) datum := by
  obtain ⟨ps, mo, ms, is, hA⟩ := recovered_arguments P
  have his0 : is = [] := List.eq_nil_of_length_eq_zero (by
    rw [hA.indices_length, (NormPropPlainTrue.family plan.node).2.1]
    rfl)
  have hidx : is = IndexedPropEval.fieldResultIndices (mkM P (table P)) σ ps
      (witness.fields.map (den (mkM P (table P)) σ (ρ P)))
      (plan.node.a.constructorViews ctor).resultIndices := by
    rw [his0, IndexedPropEval.fieldResultIndices,
      (NormPropPlainTrue.view plan.node ctor).2.2]
    rfl
  have hifs : TelFits (mkM P (table P)) σ plan.node.a.family.indices (push ps ρ0)
      (IndexedPropEval.fieldResultIndices (mkM P (table P)) σ ps
        (witness.fields.map (den (mkM P (table P)) σ (ρ P)))
        (plan.node.a.constructorViews ctor).resultIndices) := by
    rw [← hidx]
    exact hA.indices_fit
  have hmaj : den (mkM P (table P)) σ (ρ P) (ctorMajor witness) ∈
      Ed (mkM P (table P)) (fapps (table P plan.node.a.family.ref
        ((canonL plan.node.a.family.member.arity).map (evalTotal σ)))
        (ps ++ IndexedPropEval.fieldResultIndices (mkM P (table P)) σ ps
          (witness.fields.map (den (mkM P (table P)) σ (ρ P)))
          (plan.node.a.constructorViews ctor).resultIndices)) := by
    rw [← hidx]
    exact hA.major_fit
  have he := IndexedPropEval.endValue_plain_at_fields P (table P) bound plan trueFamMember
    [(1, trueIntroMember)] .empty rfl NormPropPlainTrue.ctorClasses rfl trueMembersT
    indexed_bound (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities trueEnvU) (fun _ _ h => nomatch h)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (family_equation P) [1]
    (fun u hu => by cases List.mem_singleton.mp hu; exact Nat.le_refl 1)
    (by rw [(NormPropPlainTrue.family plan.node).2.2]; rfl)
    (NormPropPlainTrue.policy plan.node) (NormPropPlainTrue.noFun plan.node)
    (NormPropPlainTrue.fields_free plan.node) ps mo ms
    (den (mkM P (table P)) σ (ρ P) (ctorMajor witness)) hA.minors_length
    hA.parameters_fit hA.motive_fit hA.minors_fit ctor
    (witness.fields.map (den (mkM P (table P)) σ (ρ P)))
    hA.fields_fit hifs hmaj
  have hidxFull : IndexedPropEval.fieldResultIndices (mkM P (table P)) (σOf [1]) ps
      (witness.fields.map (den (mkM P (table P)) σ (ρ P)))
      (plan.node.a.constructorViews ctor).resultIndices = is := by
    rw [his0, IndexedPropEval.fieldResultIndices,
      (NormPropPlainTrue.view plan.node ctor).2.2]
    rfl
  rw [hidxFull, hA.minor_read] at he
  exact hA.lhs_endpoint.trans he

theorem result_equiv (P : Premises4) :
    Equiv (PointwisePropPlainIotaAttack.result P) datum := by
  have h := redex_equiv P
  rw [PointwisePropPlainIotaAttack.lhs_application] at h
  exact (PointwisePropPlainIotaAttack.application_result P).symm.trans h

def FieldWitness (P : Premises4) : Prop :=
  Nonempty (HasTyT trueEnvU 1 context (iotaLhsOf witness) target) ∧
  HSoundT (mkM P (table P)) σ rhsTyped ∧ Fits (mkM P (table P)) σ context (ρ P) ∧
  ∃ ps mo ms is, IndexedPropPlainIota.Arguments (mkM P (table P))
    plan witness σ (ρ P) ctor ps mo ms is

theorem field_witness (P : Premises4) : FieldWitness P :=
  ⟨⟨lhsTyped⟩, rhs_hereditary P, context_fit P, recovered_arguments P⟩

theorem field_nonrefutable (P : Premises4) :
    ¬ (FieldWitness P → (Premises4 → False)) :=
  fun h => h (field_witness P) P

def EndpointWitness (P : Premises4) : Prop :=
  IndexedFieldBounds.BoundGIndexed bound trueEnvUWfT ∧
  MemberSound P (table P) bound 2 trueRecMemberU ∧
  σ 0 = 1 ∧ Equiv (den (mkM P (table P)) σ (ρ P) (iotaLhsOf witness)) datum ∧
  Equiv (PointwisePropPlainIotaAttack.result P) datum

theorem endpoint_witness (P : Premises4) : EndpointWitness P :=
  ⟨indexed_bound, recursor_sound P, rfl, redex_equiv P, result_equiv P⟩

theorem endpoint_nonrefutable (P : Premises4) :
    ¬ (EndpointWitness P → (Premises4 → False)) :=
  fun h => h (endpoint_witness P) P

def Witness (P : Premises4) : Prop :=
  IndexedPropSpine.Witness P ∧ FieldWitness P ∧ EndpointWitness P

theorem component_witness (P : Premises4) : Witness P :=
  ⟨IndexedPropSpine.component_witness P, field_witness P, endpoint_witness P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedPropPlainAttack

#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.recursor_sound
#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.recovered_arguments
#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.redex_equiv
#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.field_nonrefutable
#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.endpoint_nonrefutable
#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.component_witness
#print axioms Rcic.F3.PSet.IndexedPropPlainAttack.component_nonrefutable
