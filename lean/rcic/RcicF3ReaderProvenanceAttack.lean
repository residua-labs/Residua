import rcic.RcicF3ReaderGroupWorld
import rcic.RcicF3ReaderTelescopeProvenance
import rcic.RcicF3ReaderPacketBinderAttack

/-!
# The complete reader at an inhabited beta/zeta-hidden W telescope

The source is typed in the actual admitted W family prefix. Its first
emitted domain really reads the nonempty recursive W local through the
previous proof consumer and observer. A captured identity on the DATA
family has different values in the two original models. The beta body
ignores that capture, and an outer let forces the actual zeta branch.

The public successful-reader theorem produces all three reached domain
equalities. Both original environments fit, whereas the topology mask
does not fit. The actual tuple [empty, True, empty] inhabits all three
dependent domains. The real height-omega W member and extra motive slot
remain in the literal conjunction. This is an auxiliary typed reader
instance at the admitted prefix, not a new admitted constructor.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderProvenanceAttack
open Rcic.Declarative Rcic.Model.PS PiIndex RawFamily ReaderPacket
open NormFreshHeadAttack (base C D model parameter σ admissible_C admissible_D prefix_sound)
open PendAWBridge (fd)
open RecFieldConsumerAttack (truth)
open RecFieldMaskTypingAttack (Γ marks ρ masked)

def resultLevel : Level :=
  .imax .zero (.imax (.succ .zero) (.imax .zero (.succ .zero)))
def body : Expr Nat :=
  .pi RecFieldMaskSupportAttack.domain
    (.pi (.sort .zero) (.pi (.bvar 0) (.sort .zero)))
def betaSource : Expr Nat :=
  .app (.lam RecFieldMaskSupportAttack.captureType body)
    RecFieldMaskSupportAttack.identity
def source : Expr Nat := .letE (.sort resultLevel) betaSource (.bvar 0)
def domains : List (Expr Nat) :=
  [RecFieldMaskTypingAttack.domain, .sort .zero, .bvar 0]

noncomputable def body_typed : HasTyT PendAW.eFam 0
    RecFieldMaskSupportAttack.Γ body (.sort resultLevel) :=
  .pi _ RecFieldMaskSupportAttack.domain .zero
    (.pi (.sort .zero) (.pi (.bvar 0) (.sort .zero)))
    (.imax (.succ .zero) (.imax .zero (.succ .zero)))
    RecFieldMaskSupportAttack.domain_typed
    (.pi _ (.sort .zero) (.succ .zero) (.pi (.bvar 0) (.sort .zero))
      (.imax .zero (.succ .zero)) (.sort _ .zero)
      (.pi _ (.bvar 0) .zero (.sort .zero) (.succ .zero)
        (.bvar _ 0 (.sort .zero) rfl) (.sort _ .zero)))

noncomputable def beta_typed : HasTyT PendAW.eFam 0 Γ betaSource (.sort resultLevel) :=
  .app _ (.lam RecFieldMaskSupportAttack.captureType body)
    RecFieldMaskSupportAttack.identity RecFieldMaskSupportAttack.captureType
    (.sort resultLevel)
    (.lam _ RecFieldMaskSupportAttack.captureType RecFieldMaskSupportAttack.level
      body (.sort resultLevel) RecFieldMaskSupportAttack.capture_typed body_typed)
    RecFieldMaskSupportAttack.identity_typed

noncomputable def source_typed : HasTyT PendAW.eFam 0 Γ source (.sort resultLevel) :=
  .letE Γ (.sort resultLevel) (.succ resultLevel) betaSource (.sort resultLevel)
    (.bvar 0) (.sort Γ resultLevel) beta_typed
    (.bvar _ 0 (.sort resultLevel) rfl)

theorem body_bound (K : Nat → Nat) : LOKt σ 4 K body_typed := by
  refine ⟨by change 0 ≤ 4; decide, by change 1 ≤ 4; decide,
    RecFieldMaskSupportAttack.domain_bound K, ?_⟩
  change 1 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4 ∧ (0 ≤ 4 ∧ 1 ≤ 4 ∧ True ∧ 1 ≤ 4)
  exact ⟨by decide, by decide, by decide, by decide, by decide, True.intro, by decide⟩

theorem beta_bound (K : Nat → Nat) : LOKt σ 4 K beta_typed :=
  ⟨⟨(RecFieldMaskSupportAttack.source_bound K).1.1, body_bound K⟩,
    RecFieldMaskSupportAttack.identity_bound K⟩

theorem source_bound (K : Nat → Nat) : LOKt σ 4 K source_typed :=
  ⟨by change 2 ≤ 4; decide, beta_bound K, True.intro⟩

theorem reader_prefix : piTelescopeFuel PendAW.eFam 64 source =
    some (domains, .sort .zero) := rfl

theorem reader : piTelescopeFuel NormPendAW.plan.node.E0 64 source =
    some (domains, .sort .zero) := by
  rw [CandidateScope.piTelescopeFuel_of_transparentBody_eq
    (CandidateScope.recNode_transparentBody_prefix PendAW.membersT NormPendAW.plan.node)]
  exact reader_prefix

theorem domains_clean : ∀ A ∈ domains, occursConst fd.fref A = false := by
  intro A hA
  simp only [domains, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl <;> rfl

private theorem predecessor_context (r : Nat) (hr : Dom natEnvU r) :
    NormRole.envCtx PendAWGroup.wft r = NormRole.envCtx natEnvUWfT r :=
  NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT r hr

private theorem predecessor_plan (r : Nat) (hr : Dom natEnvU r) :
    EvalRole.envPlan PendAWGroup.wft r = EvalRole.envPlan natEnvUWfT r :=
  EvalRole.envPlan_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT r hr

private theorem predecessor_faithful (P : Premises4) :
    EvalRole.Faithful role P (base P) (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) natEnvU :=
  fun r m hm => NormPendAW.faithful P r m (groupMembersT_preserve PendAW.membersT r m hm)

/-- The reader environment package is produced from the actual normalized Nat
predecessor, including both fresh-table updates and the old iota laws. -/
noncomputable def world (P : Premises4) (K : Nat → Nat) :
    World P (base P) fd (C P) σ K NormPendAW.plan.node.E0 :=
  World.of_normalized_predecessor P (base P) fd (C P) σ K
    natEnvUWfT (PendAWGroup.boundG K).1 PendAW.membersT NormPendAW.plan.node rfl
    (NormNatInvariant.gInv P K) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) predecessor_context predecessor_plan
    (predecessor_faithful P)

/-- This calls the complete public reader producer, including its beta,
zeta, captured-variable forcing and three literal Pi-entry transitions. -/
theorem produced_domains (P : Premises4) (K : Nat → Nat) :
    PiSmallMaskSpine.Domains (model P (C P)) (mkM P (base P)) σ
      domains (ρ P) (masked P) :=
  domains_base_of_typing (world P K)
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    marks (ρ P) (masked P) (RecFieldMaskTypingAttack.contexts_fit P).1
    (RecFieldMaskTypingAttack.contexts_fit P).2
    (RecFieldMaskTypingAttack.related_context P K)
    source_typed (source_bound K) 64 domains (.sort .zero) reader domains_clean

theorem domain_value (P : Premises4) (K : Nat → Nat) :
    Equiv (den (model P (C P)) σ (ρ P) RecFieldMaskTypingAttack.domain) truth := by
  have ha := sound_ty (P.good _ rfl)
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    RecFieldMaskTypingAttack.inner_typed ⟨True.intro, True.intro⟩
    (ρ P) (RecFieldMaskTypingAttack.contexts_fit P).1
  change den (model P (C P)) σ (ρ P) RecFieldMaskTypingAttack.inner ∈
    Ed (model P (C P)) truth at ha
  exact beta_val (model P (C P)) (fun _ _ _ => Equiv.rfl) ha

/-- Every dependent domain is reached by an actual member; equality of
the first domain is not tested only on an empty branch. -/
theorem tuple_fits (P : Premises4) (K : Nat → Nat) :
    TelFits (model P (C P)) σ domains (ρ P) [pempty, truth, pempty] := by
  have he : Equiv (Ed (model P (C P)) truth) (tv True) :=
    ed_tyv (model P (C P)) (dich_tv True)
  have hp : pempty ∈ Ed (model P (C P)) truth :=
    mem_congr_right he.symm (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  refine ⟨mem_congr_right (ed_congr (model P (C P)) (domain_value P K)).symm hp,
    ?_, hp, True.intro⟩
  exact mem_congr_right (ed_tyv (model P (C P)) (U4_dich 0)).symm
    (RecFieldConsumerAttack.truth_mem P)

def Witness (P : Premises4) : Prop :=
  ReaderPacketBinderAttack.Witness P ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ source (.sort resultLevel)) ∧
  piTelescopeFuel NormPendAW.plan.node.E0 64 source = some (domains, .sort .zero) ∧
  domains.length = 3 ∧
  (∀ A ∈ domains, occursConst fd.fref A = false) ∧
  fxZW P ∈ C P [] (key [parameter]) ∧ σ 0 = 1 ∧
  (∀ K : Nat → Nat, LOKt σ 4 K source_typed ∧
    Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) ∧
    ¬ Fits (model P (C P)) σ Γ (masked P) ∧
    ¬ Equiv (RecFieldMaskSupportAttack.capture P (C P))
      (RecFieldMaskSupportAttack.capture P (D P)) ∧
    TelFits (model P (C P)) σ domains (ρ P) [pempty, truth, pempty] ∧
    PiSmallMaskSpine.Domains (model P (C P)) (mkM P (base P)) σ
      domains (ρ P) (masked P))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨ReaderPacketBinderAttack.component_witness P, ⟨source_typed⟩, reader, rfl,
    domains_clean, NormFreshHeadAttack.omega_C P, rfl,
    fun K => ⟨source_bound K, (RecFieldMaskTypingAttack.contexts_fit P).1,
      (RecFieldMaskTypingAttack.contexts_fit P).2,
      RecFieldMaskTypingAttack.masked_not_fit P K,
      ReaderSupportAttack.capture_values_differ P K,
      tuple_fits P K, produced_domains P K⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.ReaderProvenanceAttack
