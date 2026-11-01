import rcic.RcicF3ReaderPacket
import rcic.RcicF3DBoundBridge

/-!
# Entering a reader Pi binder with its original typed closure

Global lifting shifts the actual capture expressions. It leaves the
source context, derivation and source universe valuation unchanged, and
its three captured assignments are exactly their previous values. An
actual reached Pi argument then extends both original fitting contexts
and the masking relation with that same ordinary value.

The final transition inverts the packet's actual bounded Pi typing,
including outer conversions. Cleanliness of the emitted domain pays
agreement between the two original family models; the packet's produced
domain theorem pays source/mask equality. No typed reduct, masked Fits,
choice of a typing derivation, or reader-provenance callback is assumed.
All extraction of Type-valued derivations stays under Prop existentials.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open RecFieldMask (ordinary)
open ReaderSubstitution (capture Levels)

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat} {ρ η : Nat → PSet.{4}}

def shiftSubst (s : SubstT) : SubstT := fun i => Declarative.lift 0 1 (s i)

theorem allowed_shift (fd : FamData) (s : SubstT) :
    allowed fd (shiftSubst s) = allowed fd s := by
  funext i
  change (occursConst fd.fref (Declarative.lift 0 1 (s i)) = false) = _
  rw [occursConst_lift]
  rfl

theorem allowed_up (fd : FamData) (s : SubstT) :
    allowed fd s.up = RecFieldMaskSupport.allowCons True (allowed fd s) := by
  funext i
  cases i with
  | zero => exact propext ⟨fun _ => True.intro, fun _ => rfl⟩
  | succ i =>
      change (occursConst fd.fref (Declarative.lift 0 1 (s i)) = false) = _
      rw [occursConst_lift]
      rfl

theorem capture_shift (M : Interp.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) (s : SubstT) (a : PSet.{4}) :
    capture M σ (vcons a ρ) (shiftSubst s) = capture M σ ρ s := by
  funext i
  change den M σ (vcons a ρ) (Declarative.lift 0 1 (s i)) = den M σ ρ (s i)
  rw [den_lift, liftρ_zero, shiftρ_one_cons]

/-- Only the global reader environment is extended. The original local
typing data and all captured values remain unchanged. -/
noncomputable def Local.shift (L : Local P μ fd C σ K ρ η) (a : PSet.{4}) :
    Local P μ fd C σ K (vcons a ρ) (vcons a η) where
  E := L.E
  n := L.n
  Γ := L.Γ
  τ := L.τ
  s := shiftSubst L.s
  marks := L.marks
  soundC := L.soundC
  soundD := L.soundD
  fitsC := by rw [capture_shift]; exact L.fitsC
  fitsD := by rw [capture_shift]; exact L.fitsD
  context := by
    rw [capture_shift, capture_shift, capture_shift, allowed_shift]
    exact L.context

noncomputable def Packet.shift (p : Packet P μ fd C σ K ρ η) (a : PSet.{4}) :
    Packet P μ fd C σ K (vcons a ρ) (vcons a η) where
  toLocal := p.toLocal.shift a
  expr := p.expr
  expected := p.expected
  derivation := p.derivation
  bound := p.bound
  levels := p.levels

theorem Packet.shift_code (p : Packet P μ fd C σ K ρ η) (a : PSet.{4}) :
    (p.shift a).code = Declarative.lift 0 1 p.code :=
  (lift_substT_one 0 p.s p.expr).symm

/-- Provenance is transported with the actual capture packets, rather
than by inventing a new typing derivation in a weakened global context. -/
theorem Provenance.lift {e : Expr Nat}
    (h : Provenance P μ fd C σ K ρ η e) (a : PSet.{4}) :
    Provenance P μ fd C σ K (vcons a ρ) (vcons a η) (Declarative.lift 0 1 e) := by
  induction h with
  | neutral i =>
      simpa only [Declarative.lift, if_pos (Nat.zero_le i)] using
        (@Provenance.neutral P μ fd C σ K (vcons a ρ) (vcons a η) (i + 1))
  | typed p hc ih =>
      rw [← Packet.shift_code p a]
      exact Provenance.typed (p.shift a) (fun i => ih i)

theorem provenance_up (s : SubstT)
    (h : ∀ i, Provenance P μ fd C σ K ρ η (s i)) (a : PSet.{4}) :
    ∀ i, Provenance P μ fd C σ K (vcons a ρ) (vcons a η) (s.up i)
  | 0 => @Provenance.neutral P μ fd C σ K (vcons a ρ) (vcons a η) 0
  | i + 1 => (h i).lift a

/-- The original Pi annotation is used in each original fitted context.
The masking relation needs only reflexivity of the same ordinary value. -/
noncomputable def Local.bind (L : Local P μ fd C σ K ρ η)
    (A : Expr Nat) (a : PSet.{4})
    (hC : a ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) L.τ
        (capture (mkM P (table P μ fd C)) σ ρ L.s) A))
    (hD : a ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) L.τ
        (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ L.s) A)) :
    Local P μ fd C σ K (vcons a ρ) (vcons a η) where
  E := L.E
  n := L.n
  Γ := .assumption A :: L.Γ
  τ := L.τ
  s := L.s.up
  marks := ordinary L.marks
  soundC := L.soundC
  soundD := L.soundD
  fitsC := by
    rw [ReaderSubstitution.capture_up]
    exact ⟨L.fitsC, hC⟩
  fitsD := by
    rw [ReaderSubstitution.capture_up]
    exact ⟨L.fitsD, hD⟩
  context := by
    rw [ReaderSubstitution.capture_up, ReaderSubstitution.capture_up,
      ReaderSubstitution.capture_up, allowed_up]
    exact RecFieldMaskSupport.context_ordinary P μ fd C L.τ L.marks
      (allowed fd L.s) L.Γ _ _ _ L.context (.assumption A) a a a Equiv.rfl

/-- This internal constructor retains the supplied ORIGINAL body
derivation and valuation; the caller obtains that derivation by actual
bounded Pi inversion. -/
noncomputable def Local.piBody (L : Local P μ fd C σ K ρ η)
    {A B : Expr Nat} {v : Level}
    (dB : HasTyT L.E L.n (.assumption A :: L.Γ) B (.sort v))
    (hB : LOKt L.τ 4 K dB) (hlevels : Levels σ L.τ B)
    (a : PSet.{4})
    (hC : a ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) L.τ
        (capture (mkM P (table P μ fd C)) σ ρ L.s) A))
    (hD : a ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) L.τ
        (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ L.s) A)) :
    Packet P μ fd C σ K (vcons a ρ) (vcons a η) :=
  (L.bind A a hC hD).term dB hB hlevels

/-- A successful literal Pi head enters its actual source body. Both
original fitting contexts, body provenance and the source/mask domain
equation are produced, including when the Pi typing has outer conversions.
The complete original substitution is lifted under the new binder. -/
theorem Packet.enter_pi (p : Packet P μ fd C σ K ρ η)
    (A0 B0 A B : Expr Nat) (hexpr : p.expr = .pi A0 B0)
    (hcode : p.code = .pi A B)
    (hcaptures : ∀ i, Provenance P μ fd C σ K ρ η (p.s i))
    (hclean : occursConst fd.fref A = false) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ A)
      (den (mkM P (table P μ fd C)) σ η A) ∧
    ∀ a : PSet.{4}, a ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) σ ρ A) →
    ∃ q : Packet P μ fd C σ K (vcons a ρ) (vcons a η),
      q.code = B ∧ q.τ = p.τ ∧ q.s = p.s.up ∧
      (∃ v : Level, q.expected = .sort v) ∧
      (∀ i, Provenance P μ fd C σ K (vcons a ρ) (vcons a η) (q.s i)) := by
  have hc : Expr.pi (substT p.s A0) (substT p.s.up B0) = .pi A B := by
    change substT p.s p.expr = .pi A B at hcode
    rw [hexpr] at hcode
    exact hcode
  obtain ⟨hAcode, hBcode⟩ := Expr.pi.inj hc
  have hlevels : Levels σ p.τ (.pi A0 B0) := hexpr ▸ p.levels
  obtain ⟨d, hd⟩ := lokt_cast p.τ 4 K hexpr p.derivation p.bound
  obtain ⟨u, v, dA, dB, hA, hB⟩ := pi_inv_lokt p.τ 4 K d hd
  let domain := p.toLocal.term dA hA hlevels.1
  have hdomain : domain.code = A := hAcode
  have hmask := domain.domain u rfl (by rw [hdomain]; exact hclean)
  rw [hdomain] at hmask
  refine ⟨hmask, ?_⟩
  intro a ha
  have hC : a ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) p.τ
        (capture (mkM P (table P μ fd C)) σ ρ p.s) A0) := by
    rw [← ReaderSubstitution.den_closure _ σ p.τ A0 hlevels.1 p.s ρ, hAcode]
    exact ha
  have hfree := PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
    (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ A hclean ρ
  change den (mkM P (table P μ fd C)) σ ρ A =
    den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A at hfree
  have haD : a ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A) := by
    rw [ed_mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) (table P μ fd C),
      ← hfree]
    exact ha
  have hD : a ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.τ
        (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.s) A0) := by
    rw [← ReaderSubstitution.den_closure _ σ p.τ A0 hlevels.1 p.s ρ, hAcode]
    exact haD
  let q := p.toLocal.piBody dB hB hlevels.2 a hC hD
  exact ⟨q, hBcode, rfl, rfl, ⟨v, rfl⟩, provenance_up p.s hcaptures a⟩

end Rcic.F3.PSet.ReaderPacket
