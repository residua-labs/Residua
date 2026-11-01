import rcic.RcicF3ReaderProvenanceAttack
import rcic.RcicF3NormDHiddenAttack

/-!
# Actual stored delta provenance and the complete reader

The admitted predecessor contains Id : Sort 1 -> Sort 1 as an actual
transparent definition. Its stored body is typed at valuation zero.
The public group World producer obtains that original derivation and the
two original sound tables from the new singleton predecessor invariant.

The reader evaluates Id (Pi (P : Prop), Prop) at the full valuation whose
extra slot is 1. The public telescope theorem follows delta and beta and
produces the inhabited emitted-domain comparison. A second conjunct calls
the actual body_packet producer and retains its zero source valuation and
finite capture provenance. No source typing bound is transported from zero
to the full reader valuation. The same-P beta/zeta/depth-three W witness is
retained; no inhabitant of the auxiliary recursive dr family is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderDeltaAttack
open Rcic.Declarative Rcic.Model.PS RawFamily ReaderPacket
open NormFreshHeadAttack (σ)

noncomputable abbrev plan : EvalPlan.Plan := NormDHiddenAttack.plan
noncomputable abbrev μ (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormDHiddenAttack.table P
noncomputable abbrev fd : FamData := famDataOf plan.node.a
noncomputable abbrev C (P : Premises4) : Frame := frame P (μ P) fd
noncomputable abbrev model (P : Premises4) (X : Frame) : Interp.{4} :=
  mkM P (table P (μ P) fd X)

def argument : Expr Nat := .pi (.sort .zero) (.sort .zero)
def argumentLevel : Level := .imax (.succ .zero) (.succ .zero)
def source : Expr Nat := .app (.const 0 []) argument
def storedBody : Expr Nat := .lam (.sort (.succ .zero)) (.bvar 0)

noncomputable def argument_typed : HasTyT drBase 0 [] argument (.sort argumentLevel) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort _ .zero)

noncomputable def argument_converted : HasTyT drBase 0 [] argument (.sort (.succ .zero)) :=
  .conv [] argument (.sort argumentLevel) (.sort (.succ .zero)) (.succ argumentLevel)
    argument_typed (.sorts [] argumentLevel (.succ .zero) (fun _ => rfl))

noncomputable def source_typed : HasTyT drBase 0 [] source (.sort (.succ .zero)) :=
  .app [] (.const 0 []) argument (.sort (.succ .zero)) (.sort (.succ .zero))
    (.const [] 0 [] drIdMember rfl rfl rfl) argument_converted

theorem source_bound (K : Nat → Nat) : LOKt σ 4 K source_typed := by
  refine ⟨fun _ h => (List.not_mem_nil _ h).elim, ?_⟩
  change (1 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4) ∧ 2 ≤ 4
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide⟩

theorem reader_base : piTelescopeFuel drBase 16 source =
    some ([.sort .zero], .sort .zero) := rfl

private theorem predecessor_context (r : Nat) (hr : Dom drBase r) :
    NormRole.envCtx drEnvWfT r = NormRole.envCtx drBaseWfT r :=
  NormRole.envCtx_group_stable drBaseWfT rfl NormDHiddenAttack.ctorClasses rfl
    drMembersT r hr

private theorem predecessor_plan (r : Nat) (hr : Dom drBase r) :
    EvalRole.envPlan drEnvWfT r = EvalRole.envPlan drBaseWfT r :=
  EvalRole.envPlan_group_stable drBaseWfT rfl NormDHiddenAttack.ctorClasses rfl
    drMembersT r hr

private theorem predecessor_faithful (P : Premises4) :
    EvalRole.Faithful role P (μ P) (NormRole.envCtx drEnvWfT)
      (EvalRole.envPlan drEnvWfT) drBase :=
  fun r m hm => (NormRole.table_spec P drEnvWfT).1 r m
    (groupMembersT_preserve drMembersT r m hm)

noncomputable def world (P : Premises4) (K : Nat → Nat) :
    World P (μ P) fd (C P) σ K plan.node.E0 :=
  World.of_normalized_predecessor P (μ P) fd (C P) σ K
    (E := drBase) (E' := drEnv) (f := 1) (rr := 3)
    (fm := drFamMember) (rm := drRecMember) (ctors := [(2, drMkMember)])
    drBaseWfT (drEnvWfT_classGD.2 K).1.1 drMembersT plan.node plan.node.fam
    (NormDHiddenAttack.base_invariant P K) (NormRole.envCtx drEnvWfT)
    (EvalRole.envPlan drEnvWfT) predecessor_context predecessor_plan
    (predecessor_faithful P)

theorem original_sound (P : Premises4) (K : Nat → Nat) :
    EnvSound (model P (C P)) σ K drBase 0 ∧
    EnvSound (model P (RawFamilyEnlarge.enlarge fd (C P))) σ K drBase 0 :=
  ⟨envSound_of P (world P K).sub (world P K).allC (world P K).iotaC σ 0,
    envSound_of P (world P K).sub (world P K).allD (world P K).iotaD σ 0⟩

theorem reader (P : Premises4) (K : Nat → Nat) :
    piTelescopeFuel plan.node.E0 16 source = some ([.sort .zero], .sort .zero) :=
  (CandidateScope.piTelescopeFuel_of_transparentBody_eq (world P K).reads
    16 source).trans reader_base

theorem body_read (P : Premises4) (K : Nat → Nat) :
    transparentBody plan.node.E0 0 [] = some storedBody :=
  ((world P K).reads 0 []).trans rfl

/-- The actual stored predecessor derivation, its zero valuation and its
finite neutral-capture provenance are all produced from the read. -/
theorem stored_packet (P : Premises4) (K : Nat → Nat) :
    ∃ p : Packet P (μ P) fd (C P) σ K ρ0 ρ0,
      p.code = storedBody ∧ p.τ = (fun _ => 0) ∧
      Provenance P (μ P) fd (C P) σ K ρ0 ρ0 p.code := by
  obtain ⟨p, hp, ht, hc⟩ := (world P K).body_packet ρ0 ρ0 0 [] storedBody (body_read P K)
  exact ⟨p, hp, ht, Provenance.typed p hc⟩

/-- The complete public telescope theorem consumes the actual delta read,
the original application typing and the produced group World. -/
theorem produced_domains (P : Premises4) (K : Nat → Nat) :
    PiSmallMaskSpine.Domains (model P (C P)) (mkM P (μ P)) σ
      [.sort .zero] ρ0 ρ0 := by
  refine domains_base_of_typing (world P K) (original_sound P K).1
    (original_sound P K).2 (fun _ => none) ρ0 ρ0 True.intro True.intro
    (Γ := []) (A := source) (u := .succ .zero) ?_ source_typed (source_bound K)
    16 [.sort .zero] (.sort .zero) (reader P K) ?_
  · intro i A hi
    have hnone : (none : Option (Expr Nat)) = some A := hi
    cases hnone
  · intro A hA
    cases List.mem_singleton.mp hA
    rfl

theorem reached (P : Premises4) :
    TelFits (model P (C P)) σ [.sort .zero] ρ0 [RecFieldConsumerAttack.truth] :=
  ⟨mem_congr_right (ed_tyv (model P (C P)) (U4_dich 0)).symm
    (RecFieldConsumerAttack.truth_mem P), True.intro⟩

def Witness (P : Premises4) : Prop :=
  ReaderProvenanceAttack.Witness P ∧
  Nonempty (HasTyT drBase 0 [] source (.sort (.succ .zero))) ∧
  σ 0 = 1 ∧
  (∀ K : Nat → Nat, LOKt σ 4 K source_typed ∧
    piTelescopeFuel plan.node.E0 16 source = some ([.sort .zero], .sort .zero) ∧
    transparentBody plan.node.E0 0 [] = some storedBody ∧
    (∃ p : Packet P (μ P) fd (C P) σ K ρ0 ρ0,
      p.code = storedBody ∧ p.τ = (fun _ => 0) ∧
      Provenance P (μ P) fd (C P) σ K ρ0 ρ0 p.code) ∧
    TelFits (model P (C P)) σ [.sort .zero] ρ0 [RecFieldConsumerAttack.truth] ∧
    PiSmallMaskSpine.Domains (model P (C P)) (mkM P (μ P)) σ
      [.sort .zero] ρ0 ρ0)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨ReaderProvenanceAttack.component_witness P, ⟨source_typed⟩, rfl,
    fun K => ⟨source_bound K, reader P K, body_read P K, stored_packet P K,
      reached P, produced_domains P K⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.ReaderDeltaAttack
