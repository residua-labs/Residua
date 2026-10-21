import rcic.RcicNativeTypedModelCovZFixtures
import rcic.RcicNativeTypedModelCovZRigidId
import rcic.RcicNativeTypedModelCovPRealization

/-!
# A bounded strict-neutral observation measurement

The alternative model is an intersection of the landed ApproxTK relation
with a finite compact predicate. At a body-free nonconstructor rigid head,
a declared syntactic sort-domain position cannot carry a bottom argument
inside a non-bottom spine. The restriction is hereditary in the compact.

This module supplies neither a new fundamental theorem nor a replacement
of the ApproxTKR lane. It measures strictness, preservation of saturated
K introduction/contraction at a fixed compact, and the requested concrete
observations. No native readback rule changes. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open ReadbackCKAudit ReadbackCK2ConvAudit
open TypedModelCovXAudit TypedModelCovYAudit TypedModelCovZAudit
open TypedModelCovZMeasureAudit TypedModelCovNormConvCasesAudit

/-- The declaration provides an actual sort-domain telescope position.
Constructor heads and recursors cannot satisfy this predicate. -/
def CovPNeutralTypeSlot (E : ResolvedEnv) (r i : Nat) : Prop :=
  ∃ m ls l B, E.members r = some m ∧ m.body = none ∧
    m.mclass ≠ .constructorM ∧ RigidConst E r ∧ ls.length = m.arity ∧
    peelPi (instantiateLevels ls m.mtype) i = some (.pi (.sort l) B)

def CovPStrictCompact (E : ResolvedEnv) : CptT → Prop
  | .bot | .prop | .sort => True
  | .pi a rows => CovPStrictCompact E a ∧
      ∀ row ∈ rows, (∀ u ∈ row.1, CovPStrictCompact E u) ∧ CovPStrictCompact E row.2
  | .lam rows =>
      ∀ row ∈ rows, (∀ u ∈ row.1, CovPStrictCompact E u) ∧ CovPStrictCompact E row.2
  | .spine r us => (∀ u ∈ us, CovPStrictCompact E u) ∧
      ∀ i (hi : i < us.length), CovPNeutralTypeSlot E r i → us[i] ≠ .bot
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show u ∈ row.1 from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show row ∈ rows from ‹_›)
       have h₃ := sizeOfT_fst_lt row
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show row ∈ rows from ‹_›)
       have h₂ := sizeOfT_snd_lt row
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show u ∈ us from ‹_›)
       omega)

def ApproxTKStrictP (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (e : Expr Nat) (c : CptT) : Prop :=
  ApproxTK E n Γ ρ e c ∧ CovPStrictCompact E c

def ctxModelT_approxTKStrictP (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : CtxModelT E :=
  ⟨ApproxTKStrictP E n Γ⟩

theorem approxTKStrictP_bot (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvT) (e : Expr Nat) : ApproxTKStrictP E n Γ ρ e .bot := by
  refine ⟨.bot Γ ρ e, ?_⟩
  simp only [CovPStrictCompact]

theorem covP_strict_neutral_bottom_rejected {E : ResolvedEnv} {r i : Nat}
    {us : List CptT} (hi : i < us.length) (hs : CovPNeutralTypeSlot E r i)
    (hb : us[i] = .bot) : ¬ CovPStrictCompact E (.spine r us) := by
  intro h
  rw [CovPStrictCompact] at h
  exact h.2 i hi hs hb

theorem covP_rigidId_type_slot : CovPNeutralTypeSlot covZRigidIdEnv 0 0 :=
  ⟨covZRigidIdMember, [], .succ .zero, .pi (.bvar 0) (.bvar 1),
    rfl, rfl, by decide, covZRigidIdHead_rigid, rfl, rfl⟩

theorem covP_strict_rigidId_action_no (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKStrictP covZRigidIdEnv n Γ ρ
      (.app (.const 0 []) (.sort .zero)) (.spine 0 [.bot]) := by
  intro h
  exact covP_strict_neutral_bottom_rejected (us := [.bot]) (i := 0)
    (by decide) covP_rigidId_type_slot rfl h.2

theorem covP_strict_rigidId_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.app (.const 0 []) (.sort .zero))
      (.pi (.sort .zero) (.sort .zero))) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot
      (.app (.const 0 []) (.sort .zero)) (.spine 0 [.bot]) ∧
    ApproxTKStrictP covZRigidIdEnv n [] EnvT.bot
      (.app (.const 0 []) (.sort .zero)) .bot ∧
    ¬ ApproxTKStrictP covZRigidIdEnv n [] EnvT.bot
      (.app (.const 0 []) (.sort .zero)) (.spine 0 [.bot]) := by
  obtain ⟨ht, ho⟩ := covZRigidId_application_control n [] EnvT.bot
  exact ⟨⟨covZRigidIdEnvWfT⟩, ht, ho, approxTKStrictP_bot _ _ _ _ _,
    covP_strict_rigidId_action_no n [] EnvT.bot⟩

/-- A constructor keeps its old declared-telescope treatment and strict
observations can still contain bottom constructor arguments. -/
theorem covP_constructor_not_type_slot {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hk : m.mclass = .constructorM)
    (i : Nat) : ¬ CovPNeutralTypeSlot E r i := by
  rintro ⟨m', ls, l, B, hm', _, hn, _⟩
  have he : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  exact hn hk

/-- The complete guarded K constructor survives by composition: source
certificate and guards are unchanged, and the RHS carries the same strict
compact predicate as the conclusion. -/
theorem approxTKStrictP_recursorPropK {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitness E) (x : Expr Nat)
    (hk : KCanonW w x) (hn : ¬ IsCtorSpine E x)
    (hi : KIndexGuardAt E n Γ w) (hc : KCommonAt E n Γ w x)
    (hs : ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c)
    (hr : ApproxTKStrictP E n Γ ρ (iotaRhsOf w) c) :
    ApproxTKStrictP E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c :=
  ⟨.recursorPropK w x hk hn hi hc hs hr.1, hr.2⟩

/-- Any existing fixed-compact model contraction, including supplied K
contractions, restricts to the strict model without a new computation proof.
-/
theorem covP_strict_model_contract {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {src dst : Expr Nat}
    (h : CovModelContractAt (ctxModelT_approxTK E n Γ) src dst) :
    CovModelContractAt (ctxModelT_approxTKStrictP E n Γ) src dst :=
  fun ρ c hc => ⟨h ρ c hc.1, hc.2⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_ROOTS
#print axioms CovPNeutralTypeSlot
#print axioms CovPStrictCompact
#print axioms ApproxTKStrictP
#print axioms ctxModelT_approxTKStrictP
#print axioms approxTKStrictP_bot
#print axioms covP_strict_neutral_bottom_rejected
#print axioms covP_rigidId_type_slot
#print axioms covP_strict_rigidId_action_no
#print axioms covP_strict_rigidId_control
#print axioms covP_constructor_not_type_slot
#print axioms approxTKStrictP_recursorPropK
#print axioms covP_strict_model_contract
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
