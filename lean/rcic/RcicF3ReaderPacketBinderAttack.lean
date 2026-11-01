import rcic.RcicF3ReaderPacketBinder
import rcic.RcicF3RecFieldMaskSupportAttack

/-!
# An inhabited Pi transition after an opaque W identity capture

The source is the actual auxiliary beta-hidden W field from
ReaderSupportAttack. Its identity capture has different original values
in the source and enlarged family models, and no common capture fits.
The emitted domain ignores that capture. At the actual member ord 1,
the new binder transition constructs a sort-typed body packet and lifts
the identity packet's provenance under the new global binder.

Here the two GLOBAL source/mask assignments are the same parameter
assignment. The two ORIGINAL captured assignments differ. The retained
supported-typing witness separately exercises an unfitted mask and
dependent depth-three domains. This component does not assert the
complete successful-reader provenance theorem or a universal mask.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacketBinderAttack
open Rcic.Declarative RawFamily ReaderPacket
open ReaderSubstitution (capture Levels)
open NormFreshHeadAttack (base C D model parameter σ prefix_sound admissible_C admissible_D)
open ReaderSupportAttack (ρ family captureType identity body preDomain level
  body_typed identity_typed identity_bound source_bound value parameter_fits two_body_contexts)
open RecFieldConsumerAttack (parameterΓ)
open PendAWBridge (fd)

def captures : SubstT := SubstT.cons identity SubstT.id

noncomputable def initial (P : Premises4) (K : Nat → Nat) :
    Local P (base P) fd (C P) σ K ρ ρ :=
  Local.initial
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    (parameter_fits P).1 (parameter_fits P).2 (fun _ => none)
    (fun _ _ _ => Equiv.rfl)

noncomputable def identityPacket (P : Premises4) (K : Nat → Nat) :
    Packet P (base P) fd (C P) σ K ρ ρ :=
  (initial P K).term identity_typed (identity_bound σ K) (Levels.refl σ identity)

noncomputable def captured (P : Premises4) (K : Nat → Nat) :
    Local P (base P) fd (C P) σ K ρ ρ where
  E := PendAW.eFam
  n := 0
  Γ := .assumption captureType :: parameterΓ
  τ := σ
  s := captures
  marks := fun _ => none
  soundC := prefix_sound P (C P) (admissible_C P) σ K 0
  soundD := prefix_sound P (D P) (admissible_D P) σ K 0
  fitsC := by
    change Fits (model P (C P)) σ (.assumption captureType :: parameterΓ)
      (vcons (value P (C P)) ρ)
    exact (two_body_contexts P K).1
  fitsD := by
    change Fits (model P (D P)) σ (.assumption captureType :: parameterΓ)
      (vcons (value P (D P)) ρ)
    exact (two_body_contexts P K).2
  context := fun _ _ _ _ => Equiv.rfl

noncomputable def packet (P : Premises4) (K : Nat → Nat) :
    Packet P (base P) fd (C P) σ K ρ ρ :=
  (captured P K).term body_typed (source_bound σ K).1.2 (Levels.refl σ body)

theorem packet_code (P : Premises4) (K : Nat → Nat) :
    (packet P K).code = PendAW.field := rfl

theorem capture_provenance (P : Premises4) (K : Nat → Nat) :
    ∀ i, Provenance P (base P) fd (C P) σ K ρ ρ ((packet P K).s i)
  | 0 => Provenance.typed (identityPacket P K)
      (fun i => @Provenance.neutral P (base P) fd (C P) σ K ρ ρ i)
  | i + 1 => @Provenance.neutral P (base P) fd (C P) σ K ρ ρ i

theorem reached (P : Premises4) :
    ord 1 ∈ Ed (model P (C P)) (den (model P (C P)) σ ρ (.bvar 0)) :=
  RecFieldOriginAttack.argument_mem P (C P)

/-- The PUBLIC transition is called with the actual source packet and
the actual inhabited emitted domain; all child data is produced by it. -/
theorem entered (P : Premises4) (K : Nat → Nat) :
    Equiv (den (model P (C P)) σ ρ (.bvar 0))
      (den (model P (C P)) σ ρ (.bvar 0)) ∧
    ∃ q : Packet P (base P) fd (C P) σ K
        (vcons (ord 1) ρ) (vcons (ord 1) ρ),
      q.code = .app (.const 4 []) (.bvar 1) ∧ q.τ = σ ∧ q.s = captures.up ∧
      (∃ v : Level, q.expected = .sort v) ∧
      Provenance P (base P) fd (C P) σ K
        (vcons (ord 1) ρ) (vcons (ord 1) ρ) q.code ∧
      Fits (model P (C P)) q.τ q.Γ
        (capture (model P (C P)) σ (vcons (ord 1) ρ) q.s) ∧
      Fits (model P (D P)) q.τ q.Γ
        (capture (model P (D P)) σ (vcons (ord 1) ρ) q.s) := by
  have h := (packet P K).enter_pi preDomain (.app (.const 4 []) (.bvar 2))
    (.bvar 0) (.app (.const 4 []) (.bvar 1)) rfl (packet_code P K)
    (capture_provenance P K) rfl
  obtain ⟨q, hq, ht, hs, hv, hp⟩ := h.2 (ord 1) (reached P)
  exact ⟨h.1, q, hq, ht, hs, hv, Provenance.typed q hp, q.fitsC, q.fitsD⟩

def Witness (P : Premises4) : Prop :=
  RecFieldMaskSupportAttack.Witness P ∧
  whnfFuel PendAW.eFam 16 ReaderSupportAttack.source = some PendAW.field ∧
  σ 0 = 1 ∧
  ord 1 ∈ Ed (model P (C P)) (den (model P (C P)) σ ρ (.bvar 0)) ∧
  (∀ K : Nat → Nat,
    (packet P K).code = PendAW.field ∧
    ¬ Equiv (value P (C P)) (value P (D P)) ∧
    (∀ i, Provenance P (base P) fd (C P) σ K ρ ρ ((packet P K).s i)) ∧
    ∃ q : Packet P (base P) fd (C P) σ K
        (vcons (ord 1) ρ) (vcons (ord 1) ρ),
      q.code = .app (.const 4 []) (.bvar 1) ∧ q.τ = σ ∧ q.s = captures.up ∧
      (∃ v : Level, q.expected = .sort v) ∧
      Provenance P (base P) fd (C P) σ K
        (vcons (ord 1) ρ) (vcons (ord 1) ρ) q.code ∧
      Fits (model P (C P)) q.τ q.Γ
        (capture (model P (C P)) σ (vcons (ord 1) ρ) q.s) ∧
      Fits (model P (D P)) q.τ q.Γ
        (capture (model P (D P)) σ (vcons (ord 1) ρ) q.s))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldMaskSupportAttack.component_witness P, ReaderSupportAttack.whnf_reader,
    rfl, reached P, fun K => ⟨packet_code P K,
      ReaderSupportAttack.capture_values_differ P K, capture_provenance P K, (entered P K).2⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.ReaderPacketBinderAttack
