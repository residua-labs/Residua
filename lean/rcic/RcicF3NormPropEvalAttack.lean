import rcic.RcicF3NormPropGroupAttack
import rcic.RcicF3PropEvalNormalAttack

/-!
# Indexed evaluation and installed iota at the normalized AccR table

The new normalized-role table supplies the actual typed recursor inputs.
The public normalized candidate closure, normalized-member totality and
typed scalar producer are invoked at that table. The installed recursor
application computes to the same scalar, and its literal indexed IH uses
that table's context and the same scalar operation at every complete key.

AccR's original field is already normalized. The descriptor, role-context
and table equalities below concern this one concrete admitted environment;
they assert no equality of the universal old and new invariants. They allow
the existing checked application/iota fixture to be retained at this table.

The actual valuation keeps the extra motive universe at 1. The selected
AccR parameter has an empty child domain, stated explicitly below. The
inherited depth-three, hidden-head, relabelled, dependent-index and
height-omega fixtures retain their separate literal scopes in the complete
prior conjunction. No imported Acc-on-Nat.lt, universal StepAG, modern
shape-schema iota or checked W/D apex is asserted. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.NormPropEvalAttack
open Rcic.Declarative PiIndex PiValueRule RawFamily PropEval PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open EvalPlanValueAttack (plan)
open PropEvalAdmittedInputsAttack (bound)

noncomputable def μ (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRoleTableAttack.table P

private theorem recursive_field
    (q : EvalPlan.Field accPrefix 8 0 0 1 0 0 accField (.recursive 1)) :
    fieldExpr 0 [] (EvalPlanNormal.fieldSpec q) = accField := by
  cases q with
  | recursive r =>
      have hr : piTelescopeFuel accPrefix 8 accField =
          some ([.bvar 0], foldApps (.const 0 []) [.bvar 1]) := rfl
      have he := Option.some.inj (r.read.symm.trans hr)
      exact congrArg (fun p : List (Expr Nat) × Expr Nat => policyPi p.1 p.2) he

private theorem singleton_fields {fuel : Nat} {ss : List FieldShape}
    (q : EvalPlan.Fields accPrefix fuel 0 0 1 0 0 ss [accField])
    (hf : fuel = 8) (hs : ss = [.recursive 1]) :
    (EvalPlanNormal.specs q).map (fieldExpr 0 []) = [accField] := by
  subst fuel
  subst ss
  cases q with
  | cons head tail =>
      cases tail
      change [fieldExpr 0 [] (EvalPlanNormal.fieldSpec head)] = [accField]
      exact congrArg (fun A => [A]) (recursive_field head)

/-- Compare an abstract cache through its metadata and successful read,
without reducing the admission-produced `of_fields` construction. -/
private theorem constructor_fields
    (j : Fin plan.node.a.constructors.length)
    (q : EvalPlan.Constructor plan.node j) :
    (EvalPlanNormal.specs q.fields).map
        (fieldExpr plan.node.a.family.ref (canonL plan.node.a.family.member.arity)) =
      [accField] := by
  rcases j with ⟨j, hj⟩
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
  subst j
  exact singleton_fields q.fields q.fuel_admitted q.shapes_admitted

/-- Only the already-normalized concrete AccR descriptor is identified. -/
theorem descriptor_eq : EvalPlanNormal.fd plan = fd := by
  have hf : ∀ j : Fin plan.node.a.constructors.length,
      EvalPlanNormal.fields plan j = [accField] :=
    fun j => constructor_fields j (plan.constructors j)
  have hc : EvalPlanNormal.constructors plan = [([accField], [])] := by
    change [(EvalPlanNormal.fields plan ⟨0, by decide⟩, [])] = [([accField], [])]
    rw [hf]
  change { fd with ctors := EvalPlanNormal.constructors plan } = fd
  rw [hc]
  rfl

/-- Concrete role equality is proved before applying either installer. -/
theorem role_context_eq : NormRole.envCtx AccEnv.accEnvWfT =
    envCtx AccEnv.accEnvWfT := by
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    cases List.mem_singleton.mp hc
    rfl
  let p := EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT
  have hp : p = plan := by
    have h := EvalInstalledAttack.canonical_plan
    change some p = some plan at h
    exact Option.some.inj h
  have hcontext := NormRole.envCtx_group (.empty : EnvWfT emptyEnv)
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT
  change NormRole.envCtx AccEnv.accEnvWfT =
    groupRoles (EvalPlanNormal.fd p) 0 2 (fun _ => .plain) at hcontext
  rw [hp, descriptor_eq] at hcontext
  refine hcontext.trans ?_
  funext r
  cases r with
  | zero => exact family_context.symm
  | succ r =>
      cases r with
      | zero => exact constructor_context.symm
      | succ r =>
          cases r with
          | zero => exact recursor_context.symm
          | succ r =>
              change Role.plain = envCtx AccEnv.accEnvWfT
                (Nat.succ (Nat.succ (Nat.succ r)))
              exact (Rcic.F3.StepDGOrder.envCtx_freshT AccEnv.accEnvWfT
                (Nat.succ (Nat.succ (Nat.succ r))) (by rfl)).symm

/-- The two actual installers agree here because their concrete role inputs do. -/
theorem old_table_eq (P : Premises4) : μ P = EvalInstalledAttack.table P := by
  change EvalRole.envTable role P (NormRole.envCtx AccEnv.accEnvWfT)
      (EvalRole.envPlan AccEnv.accEnvWfT) AccEnv.accEnvWfT =
    EvalRole.envTable role P (envCtx AccEnv.accEnvWfT)
      (EvalRole.envPlan AccEnv.accEnvWfT) AccEnv.accEnvWfT
  rw [role_context_eq]

noncomputable def C (P : Premises4) : Context :=
  EvalPlanValue.context plan (mkM P (μ P)) (ctx P).σ (input P (installed P))

noncomputable def X (P : Premises4) : Frame :=
  NormPropEval.candidate P (μ P) (C P)

noncomputable def result (P : Premises4) : PSet.{4} :=
  PropEvalValue.result (C P) (.param 0) (key [parameter])

theorem evaluation_context_eq (P : Premises4) :
    C P = EvalInstalledAttack.currentContext P := by
  unfold C EvalInstalledAttack.currentContext
  rw [old_table_eq P]

/-- These are the complete actual arguments, typed at the normalized table. -/
theorem arguments_fit (P : Premises4) :
    TelFits (mkM P (μ P)) (ctx P).σ
      [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
      [parameter, motive P (installed P), minor P (installed P), pempty] := by
  rw [old_table_eq P]
  exact EvalInstalledAttack.arguments_fit P

/-- The production endpoint uses the full valuation and the complete key. -/
theorem endpoint_eq (P : Premises4) :
    EvalPlanValue.endValue (mkM P (μ P)) (ctx P).σ plan (input P (installed P)) =
      result P := by
  rw [EvalPlanValue.endValue_prop (mkM P (μ P)) (ctx P).σ plan _ rfl rfl]
  rfl

/-- The installed recursor application reaches the newly produced scalar. -/
theorem application_result (P : Premises4) :
    Equiv (fapps (μ P 2 [1])
      [parameter, motive P (installed P), minor P (installed P), pempty])
      (result P) := by
  have hrec := (NormRole.table_spec P AccEnv.accEnvWfT).1 2 accRecMember rfl [1]
  rw [role_context_eq, recursor_context, EvalInstalledAttack.canonical_plan] at hrec
  change Equiv (μ P 2 [1])
    (EvalPlanValue.memberValue (mkM P (μ P)) (ctx P).σ plan accRecMember) at hrec
  have happ := fapps_piLam (mkM P (μ P)) (ctx P).σ
    (EvalPlanValue.endValue_resp (mkM P (μ P)) (ctx P).σ plan)
    (.app (.bvar 2) (.bvar 0))
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
    [parameter, motive P (installed P), minor P (installed P), pempty] (arguments_fit P)
  change Equiv (fapps
      (EvalPlanValue.memberValue (mkM P (μ P)) (ctx P).σ plan accRecMember)
      [parameter, motive P (installed P), minor P (installed P), pempty])
    (EvalPlanValue.endValue (mkM P (μ P)) (ctx P).σ plan (input P (installed P))) at happ
  rw [endpoint_eq P] at happ
  exact (fapps_congr hrec _).trans happ

/-- The actual IH retains the normalized domain, full arguments and new leaf value. -/
noncomputable def ihValue (P : Premises4) : PSet.{4} :=
  (tel (C P).M (C P).σ [.bvar 2] [.bvar 3]
    (vcons pempty (start P (installed P)))).indexedIH (C P).M
      (fun i _ => PropEvalValue.result (C P) (.param 0) i) pempty

theorem ih_eq (P : Premises4) : ihValue P = EvalInstalledAttack.ihValue P := by
  unfold ihValue
  rw [evaluation_context_eq P]
  rfl

/-- Empty child domains are part of the exact scope of this AccR instance. -/
theorem no_children (P : Premises4) (zs : List PSet.{4}) :
    ¬ TelFits (C P).M (C P).σ [.bvar 2]
      (vcons pempty (start P (installed P))) zs := by
  intro hz
  cases zs with
  | nil => exact hz.elim
  | cons z zs =>
      have hz0 : z ∈ Ed (mkM P (μ P)) parameter := hz.1
      exact not_mem_pempty (mem_congr_right (parameter_empty P (μ P)) hz0)

theorem ih_typed (P : Premises4) :
    ihValue P ∈ Ed (C P).M (den (C P).M (C P).σ
      (vcons pempty (start P (installed P))) accIhTy) := by
  rw [ih_eq P, evaluation_context_eq P]
  exact EvalInstalledAttack.ih_typed P

/-- The installed equation uses this normalized table's own generated IH. -/
theorem installed_iota (P : Premises4) :
    Equiv (fapps (μ P 2 [1])
      [parameter, motive P (installed P), minor P (installed P), pempty])
      (fapps (minor P (installed P)) [pempty, ihValue P]) := by
  rw [old_table_eq P, ih_eq P]
  exact EvalInstalledAttack.installed_iota P

/-- Actual admitted support transports the entire scalar operation at every key. -/
theorem value_same (P : Premises4) (i : Index.{4}) :
    Equiv (PropEvalValue.result (ctx P) (.param 0) i)
      (PropEvalValue.result (C P) (.param 0) i) := by
  have hag : AgreeOn (installed P) (μ P) (Dom plan.node.E0) := by
    rw [old_table_eq P]
    exact EvalInstalledAttack.prefix_agree P
  have hC : C P = (ctx P).withModel (mkM P (μ P)) := rfl
  rw [hC]
  exact PropEvalValue.result_model_congr (C := ctx P) P (installed P) (μ P)
    (Dom plan.node.E0) rfl hag (PropEvalValueReadAttack.scope P) (.param 0) i

/-- A surplus index stays rejected at the normalized table despite the same parameter. -/
theorem invalid_key (P : Premises4) :
    Equiv (PropEvalValue.result (C P) (.param 0) (key [parameter, datum])) pempty ∧
      PropEvalValue.result (C P) (.param 0) (key [parameter, datum]) ∉ domain := by
  have he := (value_same P (key [parameter, datum])).symm.trans
    (PropEvalValueAttack.invalid_key P).1
  refine ⟨he, ?_⟩
  intro ht
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans he)

/-- The literal old operation still misses this same actual target type. -/
theorem old_endpoint_rejected (P : Premises4) (old : List (List FieldShape)) :
    RecPlanValue.endValue (mkM P (μ P)) (ctx P).σ fd old (input P (installed P)) ∉
      Ed (mkM P (μ P)) (fapp (motive P (installed P)) pempty) := by
  rw [old_table_eq P]
  exact EvalInstalledAttack.old_endpoint_rejected P old

def Witness (P : Premises4) : Prop :=
  PropEvalNormalAttack.Witness P ∧
  NormPropGroupAttack.Witness P ∧
  EvalPlanNormal.fd plan = fd ∧
  μ P = EvalInstalledAttack.table P ∧
  (C P).σ 0 = 1 ∧
  (∀ zs, ¬ TelFits (C P).M (C P).σ [.bvar 2]
    (vcons pempty (start P (installed P))) zs) ∧
  TelFits (mkM P (μ P)) (ctx P).σ
    [.sort .zero, accMotTy, accMinorTy, accApp (.bvar 2)] ρ0
    [parameter, motive P (installed P), minor P (installed P), pempty] ∧
  Admissible (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) ∧
  Closed P (μ P) (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) ∧
  (∀ vs i z, z ∈ NormPropEval.base P (μ P) (C P) vs i →
    PropEvalCandidate.EvalPredicate (C P) vs i z) ∧
  Eval (C P) (key [parameter]) (result P) ∧
  result P ∈ childCarrier (C P) (.param 0) (key [parameter]) ∧
  result P ∈ Ed (C P).M (fapp (C P).motive pempty) ∧
  result P ∈ domain ∧
  ¬ Equiv (result P) pempty ∧
  ihValue P ∈ Ed (C P).M (den (C P).M (C P).σ
    (vcons pempty (start P (installed P))) accIhTy) ∧
  Equiv (fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty]) (result P) ∧
  fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty] ∈
      Ed (C P).M (fapp (C P).motive pempty) ∧
  Equiv (fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty])
    (fapps (minor P (installed P)) [pempty, ihValue P]) ∧
  ¬ Equiv (fapps (μ P 2 [1])
    [parameter, motive P (installed P), minor P (installed P), pempty]) pempty ∧
  (Equiv (PropEvalValue.result (C P) (.param 0) (key [parameter, datum])) pempty ∧
    PropEvalValue.result (C P) (.param 0) (key [parameter, datum]) ∉ domain) ∧
  ∀ old : List (List FieldShape),
    RecPlanValue.endValue (mkM P (μ P)) (ctx P).σ fd old (input P (installed P)) ∉
      Ed (mkM P (μ P)) (fapp (motive P (installed P)) pempty)

/-- All new totality inputs are obtained at the actual normalized table;
the prior component conjunctions are retained without dropping a face. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    cases List.mem_singleton.mp hc
    rfl
  have hFamily : ∀ vs, Equiv (μ P (C P).node.a.family.ref vs)
      (ofFrame P (μ P) (famDataOf (C P).node.a) (NormPropEval.base P (μ P) (C P)) vs) := by
    intro vs
    have h := (NormRole.table_spec P AccEnv.accEnvWfT).1 0 accFamMember rfl vs
    rw [(NormRoleTableAttack.component_witness P).1] at h
    exact h
  have hArgs := arguments_fit P
  have hps : TelFits (C P).M (C P).σ (C P).node.a.family.parameters ρ0
      (C P).parameters := ⟨hArgs.1, True.intro⟩
  have hmo : (C P).motive ∈ Ed (C P).M (den (C P).M (C P).σ
      (push (C P).parameters ρ0) accMotTy) := hArgs.2.1
  have hminors : TelFits (C P).M (C P).σ (C P).node.a.minorTypes
      (vcons (C P).motive (push (C P).parameters ρ0)) (C P).minors :=
    ⟨hArgs.2.2.1, True.intro⟩
  have hmajor : pempty ∈ Ed (C P).M
      (fapps ((C P).M.μ (C P).node.a.family.ref
        ((canonL (C P).node.a.family.member.arity).map (evalTotal (C P).σ)))
        ((C P).parameters ++ [])) := hArgs.2.2.2.1
  have hvs : ∀ u, u ∈ [1] → u ≤ bound (C P).rr := by
    intro u hu
    cases List.mem_singleton.mp hu
    exact Nat.le_refl 1
  have hClose := NormPropEval.candidate_closed P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound) (NormRole.gInv_empty P bound)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    hFamily [1] rfl hvs rfl rfl (.param 0) hmo hminors
  have hTotal := NormPropEval.normalized_evaluates P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound) (NormRole.gInv_empty P bound)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    hFamily [1] rfl hvs rfl rfl (.param 0) hmo hminors
  have hs := NormPropEval.result_spec P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound) (NormRole.gInv_empty P bound)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    hFamily [1] rfl hvs rfl rfl (.param 0) hmo hminors [] pempty hps True.intro hmajor
  have ht : result P ∈ Ed (C P).M (fapp (C P).motive pempty) := hs.2.2
  have hd : result P ∈ domain :=
    mem_congr_left (value_same P (key [parameter])) (PropEvalValueAttack.result_domain P)
  have hn : ¬ Equiv (result P) pempty := fun he =>
    dataVal_ne_pempty _ _ ((mem_singleton.mp hd).symm.trans he)
  have happ := application_result P
  refine ⟨PropEvalNormalAttack.component_witness P, NormPropGroupAttack.component_witness P,
    descriptor_eq, old_table_eq P, rfl, no_children P, hArgs, hClose.1, hClose.2,
    hTotal, hs.2.1, hs.1, ht, hd, hn, ih_typed P, happ,
    mem_congr_left happ.symm ht, installed_iota P, ?_, invalid_key P,
    old_endpoint_rejected P⟩
  exact fun he => hn (happ.symm.trans he)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropEvalAttack
