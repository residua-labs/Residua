import rcic.RcicF3NormPropEvalAttack
import rcic.RcicF3NormPropCtorUniformAttack
import rcic.RcicF3PiSmallRecursiveAttack
import rcic.RcicF3RawNonIRHiddenAttack

/-!
# Produced normalized Prop face and explicit universal A boundary

The universal Prop/anySort PendA group-step face is produced from the
actual normalized-role invariant. Its complete actual-table AccR witness
retains constructor membership, indexed evaluation and typed-IH iota.
The uniform-Prop constructor witness also retains the policy-independent
constructor producer. Exact-stage small tuple/recursive-value components and the local hidden
raw-occurrence adversary are composed with their literal scopes.

The universal NormRole.StepAG target retains every PendA group, including
data and propOnly faces. It is still an explicit input below. No equality
with an earlier invariant, universal small data signature, checked W/D
apex or overall check-passing non-vacuity is assumed. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ANormRoleContract
open Rcic.Declarative

/-- The proved face is explicit; the full target below is not restricted. -/
def PropFace (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel →
    (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort →
    (∃ node : RecNode E E' f rr rm, PendA node) →
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem

theorem prop_face (P : Premises4) (K : Nat → Nat) : PropFace P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hProp hpolicy hPend
  exact NormPropGroup.group_step P K hE hfam hctors hrec hmem hProp hpolicy hPend

theorem prop_face_nonrefutable (P : Premises4) :
    ¬ ((∀ K, PropFace P K) → (Premises4 → False)) :=
  fun h => h (prop_face P) P

def Components (P : Premises4) : Prop :=
  (∀ K, PropFace P K) ∧ NormPropEvalAttack.Witness P ∧
    NormPropCtorUniformAttack.Witness P ∧ PiSmallRecursiveAttack.Witness P ∧
    RawNonIRHiddenAttack.Witness

theorem components (P : Premises4) : Components P :=
  ⟨prop_face P, NormPropEvalAttack.component_witness P,
    NormPropCtorUniformAttack.component_witness P,
    PiSmallRecursiveAttack.component_witness P,
    RawNonIRHiddenAttack.component_witness⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  (∀ P K, NormRole.StepAG P K) ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => h.1, target_of_stepAG⟩

end Rcic.F3.PSet.ANormRoleContract
