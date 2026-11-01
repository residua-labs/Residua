import rcic.RcicF3ReaderCapture
import rcic.RcicF3ReaderDeltaOrigin

/-!+# Original typed closures for the actual field reader

A packet retains the original derivation, its own universe valuation and
its two original fitting assignments. Its executable expression is the
literal parallel substitution of its source. Captures are evaluated at
the reader's full valuation; only captures whose syntax is family-free
are allowed to contribute a local value relation.

The value and type-domain conclusions below are produced by the bounded
support-aware typing induction. In particular, a dirty unused capture
may evaluate differently in the two family models. Neither a common
capture nor a fitting masked assignment is required. This is the internal
invariant for the remaining reader induction, not a reader callback or a
new premise of the checked apex. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open RecFieldMask (Marks Value mode)
open RecFieldMaskSupport (Agree Context Supported)
open ReaderSubstitution (capture Levels)

def allowed (fd : FamData) (s : SubstT) : Nat → Prop :=
  fun i => occursConst fd.fref (s i) = false

/-- This closure's typing valuation need not be the reader valuation.
Transparent stored bodies retain the zero valuation of their derivation. -/
structure Local (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    (ρ η : Nat → PSet.{4}) where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  τ : Nat → Nat
  s : SubstT
  marks : Marks
  soundC : EnvSound (mkM P (table P μ fd C)) τ K E n
  soundD : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) τ K E n
  fitsC : Fits (mkM P (table P μ fd C)) τ Γ
    (capture (mkM P (table P μ fd C)) σ ρ s)
  fitsD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) τ Γ
    (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ s)
  context : Context P μ fd C τ marks (allowed fd s) Γ
    (capture (mkM P (table P μ fd C)) σ ρ s)
    (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ s)
    (capture (mkM P (table P μ fd C)) σ η s)

structure Packet (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    (ρ η : Nat → PSet.{4}) extends Local P μ fd C σ K ρ η where
  expr : Expr Nat
  expected : Expr Nat
  derivation : HasTyT E n Γ expr expected
  bound : LOKt τ 4 K derivation
  levels : Levels σ τ expr

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat} {ρ η : Nat → PSet.{4}}

/-- Every allowed capture has equal original values, by its actual syntax.
No agreement is asserted for an opaque capture. -/
theorem Local.agree (L : Local P μ fd C σ K ρ η) :
    Agree (allowed fd L.s)
      (capture (mkM P (table P μ fd C)) σ ρ L.s)
      (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ L.s) := by
  intro i hi
  have he := PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
    (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ (L.s i) hi ρ
  change den (mkM P (table P μ fd C)) σ ρ (L.s i) =
    den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (L.s i) at he
  change Equiv (den (mkM P (table P μ fd C)) σ ρ (L.s i))
    (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (L.s i))
  rw [he]
  exact Equiv.rfl

noncomputable def Local.term (L : Local P μ fd C σ K ρ η)
    {e A : Expr Nat} (d : HasTyT L.E L.n L.Γ e A)
    (hd : LOKt L.τ 4 K d) (hl : Levels σ L.τ e) : Packet P μ fd C σ K ρ η :=
  { toLocal := L, expr := e, expected := A,
    derivation := d, bound := hd, levels := hl }

def Packet.code (p : Packet P μ fd C σ K ρ η) : Expr Nat := substT p.s p.expr

def Packet.q (p : Packet P μ fd C σ K ρ η) : Option Nat := mode p.marks p.expr

noncomputable def Packet.typeC (p : Packet P μ fd C σ K ρ η) : PSet.{4} :=
  den (mkM P (table P μ fd C)) p.τ
    (capture (mkM P (table P μ fd C)) σ ρ p.s) p.expected

noncomputable def Packet.typeD (p : Packet P μ fd C σ K ρ η) : PSet.{4} :=
  den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.τ
    (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.s) p.expected

theorem Packet.memberC (p : Packet P μ fd C σ K ρ η) :
    den (mkM P (table P μ fd C)) σ ρ p.code ∈
      Ed (mkM P (table P μ fd C)) p.typeC := by
  change den (mkM P (table P μ fd C)) σ ρ (substT p.s p.expr) ∈ _
  rw [ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ]
  exact sound_ty (P.good _ rfl) p.soundC p.derivation p.bound _ p.fitsC

theorem Packet.memberD (p : Packet P μ fd C σ K ρ η) :
    den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.code ∈
      Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.typeD := by
  change den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
    (substT p.s p.expr) ∈ _
  rw [ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ]
  exact sound_ty (P.good _ rfl) p.soundD p.derivation p.bound _ p.fitsD

/-- Actual cleanliness of the substituted code pays both source cleanliness
and every local support obligation of the bounded relation. -/
theorem Packet.value (p : Packet P μ fd C σ K ρ η)
    (hf : occursConst fd.fref p.code = false) :
    Value (mkM P μ) fd C p.q
      (Ed (mkM P (table P μ fd C)) p.typeC)
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.typeD)
      (den (mkM P (table P μ fd C)) σ ρ p.code)
      (den (mkM P (table P μ fd C)) σ η p.code) := by
  have hsource := ReaderSupport.subst_source_clean fd.fref p.expr p.s hf
  have hs : Supported (allowed fd p.s) p.expr :=
    ReaderSupport.subst_capture_clean fd.fref p.expr p.s hf
  have h := RecFieldMaskSupport.of_typing P μ fd C p.τ K p.soundC p.soundD
    p.derivation p.bound p.marks (allowed fd p.s)
    (capture (mkM P (table P μ fd C)) σ ρ p.s)
    (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.s)
    (capture (mkM P (table P μ fd C)) σ η p.s)
    p.toLocal.agree p.fitsC p.fitsD p.context hsource hs
  change Value (mkM P μ) fd C (mode p.marks p.expr)
    (Ed (mkM P (table P μ fd C)) p.typeC)
    (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.typeD)
    (den (mkM P (table P μ fd C)) σ ρ (substT p.s p.expr))
    (den (mkM P (table P μ fd C)) σ η (substT p.s p.expr))
  rw [ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ,
    ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s η]
  exact h

/-- An emitted clean source type uses the produced relation and its actual
sort typing. This is at the original and masked substitutions, not at a
postulated typed normal form. -/
theorem Packet.domain (p : Packet P μ fd C σ K ρ η)
    (l : Level) (ht : p.expected = .sort l)
    (hf : occursConst fd.fref p.code = false) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ p.code)
      (den (mkM P (table P μ fd C)) σ η p.code) := by
  have hsource := ReaderSupport.subst_source_clean fd.fref p.expr p.s hf
  have hs : Supported (allowed fd p.s) p.expr :=
    ReaderSupport.subst_capture_clean fd.fref p.expr p.s hf
  obtain ⟨d, hd⟩ : ∃ d : HasTyT p.E p.n p.Γ p.expr (.sort l), LOKt p.τ 4 K d :=
    Eq.mp (congrArg (fun T : Expr Nat =>
      ∃ d : HasTyT p.E p.n p.Γ p.expr T, LOKt p.τ 4 K d) ht)
      ⟨p.derivation, p.bound⟩
  have h := RecFieldMaskSupport.domain_eq P μ fd C p.τ K p.soundC p.soundD
    p.marks (allowed fd p.s)
    (capture (mkM P (table P μ fd C)) σ ρ p.s)
    (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.s)
    (capture (mkM P (table P μ fd C)) σ η p.s)
    p.toLocal.agree p.fitsC p.fitsD p.context hsource hs d hd
  change Equiv (den (mkM P (table P μ fd C)) σ ρ (substT p.s p.expr))
    (den (mkM P (table P μ fd C)) σ η (substT p.s p.expr))
  rw [ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ,
    ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s η]
  exact h

/-- The actual constructor prefix initializes a closure without capturing
or erasing any source local. -/
noncomputable def Local.initial {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (marks : Marks) (hctx : RecFieldMask.Context P μ fd C σ marks Γ ρ η) :
    Local P μ fd C σ K ρ η where
  E := E
  n := n
  Γ := Γ
  τ := σ
  s := SubstT.id
  marks := marks
  soundC := hEC
  soundD := hED
  fitsC := hρC
  fitsD := hρD
  context := fun i A _ hi => hctx i A hi

/-- Capture provenance is a finite inductive derivation. Neutral global
locals cannot expose a Pi head; every substituted closure retains all its
capture derivations. The relation makes no evaluation-totality assumption. -/
inductive Provenance (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    (ρ η : Nat → PSet.{4}) : Expr Nat → Prop
  | neutral (i : Nat) : Provenance P μ fd C σ K ρ η (.bvar i)
  | typed (p : Packet P μ fd C σ K ρ η)
      (captures : ∀ i, Provenance P μ fd C σ K ρ η (p.s i)) :
      Provenance P μ fd C σ K ρ η p.code

end Rcic.F3.PSet.ReaderPacket
