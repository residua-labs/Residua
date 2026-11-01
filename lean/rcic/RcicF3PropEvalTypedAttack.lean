import rcic.RcicF3PropEvalTyped
import rcic.RcicF3PropEvalGuardedAttack

/-!
# Actual typed-prefix composition at the admitted AccR fixture

Raw-frame admissibility pays the stored family member at every level instance.
The family-only prefix has no constructors, so its soundness is obtained
without the refuted completed recursor invariant. Existing bounded field
derivations then pay the typed mutual-comparison bridge at the actual extra
motive universe. The resulting extractor has an inhabited, nonempty result.
This is a local component witness; universal StepAG remains open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalTypedAttack
open Rcic.Declarative PiIndex PlanPropEndAttack
open PropEvalUniqueAttack (ctx)

/-- The installed raw role has the actual family type at every instance. -/
theorem family_member (P : Premises4) (K : Nat → Nat) :
    MemberSound P (installed P) K 0 accFamMember := by
  intro τ ls ρ hlen _
  have hnil : ls = [] := List.length_eq_zero.mp hlen
  subst ls
  constructor
  · rw [den_inst_canon (mkM P (installed P)) τ [] ρ accFamMember.mtype
      (by intro k; rfl) (by rfl)]
    exact mem_congr_left (installed_family P).symm
      (RawFamily.ofFrame_mem P (installed P) fd (RawFamily.frame P (installed P) fd)
        (RawFamilyPropAttack.acc_closed P (installed P)).1 [])
  · intro b hb
    cases hb

/-- Only the family prefix is used in the ordinary soundness argument. -/
theorem prefix_members (P : Premises4) (K : Nat → Nat) :
    AllSound P (installed P) K accFamOnly := by
  intro r m hm
  change (if r = 0 then some accFamMember else none) = some m at hm
  by_cases hr : r = 0
  · subst r
    simp only [ite_true, Option.some.injEq] at hm
    subst m
    exact family_member P K
  · simp only [hr, ite_false] at hm
    cases hm

theorem prefix_classes : CtorFreeAxFree accFamOnly := by
  intro r m hm
  change (if r = 0 then some accFamMember else none) = some m at hm
  by_cases hr : r = 0
  · subst r
    simp only [ite_true, Option.some.injEq] at hm
    subst m
    exact ⟨by decide, by decide⟩
  · simp only [hr, ite_false] at hm
    cases hm

theorem prefix_sound (P : Premises4) (K : Nat → Nat) :
    EnvSound (ctx P).M (ctx P).σ K accFamOnly 0 :=
  envSound_of_allSound P (prefix_members P K) prefix_classes (ctx P).σ 0

def TypedFields (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ (j : Fin (ctx P).node.a.constructors.length)
    (k : Fin ((ctx P).node.a.constructorViews j).fields.length),
    ∃ l : Level, evalTotal (ctx P).σ l = 0 ∧
      ∃ d : HasTyT accFamOnly 0
        (policyPrefixContext
          ((ctx P).node.a.family.parameters ++ ((ctx P).node.a.constructorViews j).fields)
          ((ctx P).node.a.family.parameters.length + k.val))
        (((ctx P).node.a.constructorViews j).fields[k]) (.sort l), LOKt (ctx P).σ 4 K d

theorem typed_fields (P : Premises4) (K : Nat → Nat) : TypedFields P K := by
  intro j k
  obtain ⟨l, hl, d, hd⟩ :=
    PlanPropStepAttack.propFieldBound K PlanPropStepAttack.pNode j (ctx P).σ k
  exact ⟨l, hl (ctx P).σ, d, hd⟩

/-- Literal typed-prefix premises and the produced canonical evaluation. -/
def Witness (P : Premises4) (K : Nat → Nat) : Prop :=
  EnvSound (ctx P).M (ctx P).σ K accFamOnly 0 ∧ TypedFields P K ∧
  (ctx P).node.a.family.member.arity = 0 ∧ (ctx P).σ 0 = 1 ∧
  (∀ i z z', PropEval.Eval (ctx P) i z → PropEval.Eval (ctx P) i z' → Equiv z z') ∧
  PropEvalAttack.canonical P ∈ domain ∧
  PropEval.Eval (ctx P) (key [parameter]) (PropEvalAttack.canonical P) ∧
  ¬ Equiv (PropEvalAttack.canonical P) pempty

theorem component_witness (P : Premises4) (K : Nat → Nat) : Witness P K := by
  have hfun : ∀ i z z', PropEval.Eval (ctx P) i z →
      PropEval.Eval (ctx P) i z' → Equiv z z' := by
    intro i z z' h h'
    exact PropEval.Eval.functional_of_typed_proof_fields (ctx P) P (installed P) K
      accFamOnly 0 rfl rfl rfl (prefix_sound P K) (typed_fields P K) h h'
  have hex : ∃ z, z ∈ domain ∧ PropEval.Eval (ctx P) (key [parameter]) z :=
    ⟨datum, mem_singleton.mpr Equiv.rfl, PropEvalAttack.inhabited P⟩
  have hv : PropEvalAttack.canonical P ∈ domain ∧
      PropEval.Eval (ctx P) (key [parameter]) (PropEvalAttack.canonical P) :=
    PropEvalExtract.value_spec_of_output_congr hex
      (fun _ _ _ _ h h' => hfun _ _ _ h h')
      (fun _ _ h => PropEvalAttack.eval_typed P h)
      (fun _ _ he h => h.output_congr he.symm)
  refine ⟨prefix_sound P K, typed_fields P K, rfl, rfl, hfun, hv.1, hv.2, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp hv.1).symm.trans h)

theorem component_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (Witness P K → (Premises4 → False)) :=
  fun h => h (component_witness P K) P


/-- The actual BoundG clause is consumed at [1], with the extra motive slot intact. -/
def BoundedWitness (P : Premises4) : Prop :=
  BoundG (fun _ => 1) AccEnv.accEnvWfT ∧ Witness P (fun _ => 1)

theorem bounded_component_witness (P : Premises4) : BoundedWitness P := by
  have hfun : ∀ i z z', PropEval.Eval (ctx P) i z →
      PropEval.Eval (ctx P) i z' → Equiv z z' := by
    intro i z z' h h'
    exact PropEval.Eval.functional_of_boundG (ctx P) P (installed P) (fun _ => 1)
      (fm := accFamMember) (ctors := [(1, accIntroMember)]) .empty rfl
      (fun c hc => by simp at hc; subst c; rfl) rfl AccEnv.accMembersT
      (PlanPropStepAttack.boundG (fun _ => 1)) rfl rfl rfl
      (prefix_sound P (fun _ => 1)) [1] rfl
      (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst v; exact Nat.le_refl 1)
      h h'
  have hex : ∃ z, z ∈ domain ∧ PropEval.Eval (ctx P) (key [parameter]) z :=
    ⟨datum, mem_singleton.mpr Equiv.rfl, PropEvalAttack.inhabited P⟩
  have hv : PropEvalAttack.canonical P ∈ domain ∧
      PropEval.Eval (ctx P) (key [parameter]) (PropEvalAttack.canonical P) :=
    PropEvalExtract.value_spec_of_output_congr hex
      (fun _ _ _ _ h h' => hfun _ _ _ h h')
      (fun _ _ h => PropEvalAttack.eval_typed P h)
      (fun _ _ he h => h.output_congr he.symm)
  refine ⟨PlanPropStepAttack.boundG (fun _ => 1),
    prefix_sound P (fun _ => 1), typed_fields P (fun _ => 1),
    rfl, rfl, hfun, hv.1, hv.2, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp hv.1).symm.trans h)

theorem bounded_component_nonrefutable (P : Premises4) :
    ¬ (BoundedWitness P → (Premises4 → False)) :=
  fun h => h (bounded_component_witness P) P

/-- The new typed component is inhabited at the same group that refutes
the planned StepAG endpoint. This is not a universal replacement StepAG. -/
theorem component_at_refuted_group (P : Premises4) :
    BoundedWitness P ∧ ¬ PlanRole.StepAG RawFamily.role P (fun _ => 1) :=
  ⟨bounded_component_witness P, PlanPropStepAttack.stepAG_false P⟩

end Rcic.F3.PSet.PropEvalTypedAttack
