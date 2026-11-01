import rcic.RcicF3ReaderPacket

/-!
# Actual transparent-body packets for the reader

The environment facts here are the already-used member soundness, stable
old-recursors' iota, predecessor BoundG and exact body-read equations.
They produce a packet from each actual transparent lookup. The stored
body remains typed in its original predecessor at valuation zero; local
and level closure pay its denotation at the full reader valuation.

No successful-reader provenance or domain mask is an input. The public
group assembly must supply these environment facts from its predecessor,
as it already does for the family-only prefix. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open ReaderSubstitution (capture Levels)

/-- Concrete environment data, rather than a callback that assumes the
existence of a typed reduct. `reader` may contain fresh bodyless slots. -/
structure World (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat) (reader : ResolvedEnv) where
  previous : ResolvedEnv
  finalEnv : ResolvedEnv
  wellformed : EnvWfT previous
  bounded : BoundG K wellformed
  sub : ∀ r m, previous.members r = some m → finalEnv.members r = some m
  allC : AllSound P (table P μ fd C) K previous
  allD : AllSound P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) K previous
  iotaC : ∀ r m, previous.members r = some m → m.mclass = .recursorM →
    IotaAt P (table P μ fd C) K finalEnv r
  iotaD : ∀ r m, previous.members r = some m → m.mclass = .recursorM →
    IotaAt P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) K finalEnv r
  reads : ∀ r ls, transparentBody reader r ls = transparentBody previous r ls
  deltaC : DeltaNormalize.BodyEquations (mkM P (table P μ fd C)) reader σ
  deltaD : DeltaNormalize.BodyEquations
    (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) reader σ

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat} {reader : ResolvedEnv}

/-- This is the actual delta provenance producer. The existential packet
is constructed from the stored derivation, not selected from an assumed
typing of the normal form. -/
theorem World.body_packet (W : World P μ fd C σ K reader)
    (ρ η : Nat → PSet.{4}) (r : Nat) (ls : List Level) (b : Expr Nat)
    (hr : transparentBody reader r ls = some b) :
    ∃ p : Packet P μ fd C σ K ρ η,
      p.code = b ∧ p.τ = (fun _ => 0) ∧
      (∀ i, Provenance P μ fd C σ K ρ η (p.s i)) := by
  have hp : transparentBody W.previous r ls = some b := (W.reads r ls).symm.trans hr
  obtain ⟨m, S, d, _hm, _hb, _ha, hsub, hd, _hcl, hlvl⟩ :=
    ReaderDeltaOrigin.of_read K W.wellformed W.bounded r ls b hp
  have hSC : EnvSound (mkM P (table P μ fd C)) (fun _ => 0) K S 0 :=
    envSound_of P (fun s m hs => W.sub s m (hsub s m hs))
      (fun s m hs => W.allC s m (hsub s m hs))
      (fun s m hs hc => W.iotaC s m (hsub s m hs) hc) (fun _ => 0) 0
  have hSD : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (fun _ => 0) K S 0 :=
    envSound_of P (fun s m hs => W.sub s m (hsub s m hs))
      (fun s m hs => W.allD s m (hsub s m hs))
      (fun s m hs hc => W.iotaD s m (hsub s m hs) hc) (fun _ => 0) 0
  let L : Local P μ fd C σ K ρ η :=
    { E := S, n := 0, Γ := [], τ := fun _ => 0, s := SubstT.id,
      marks := fun _ => none, soundC := hSC, soundD := hSD,
      fitsC := True.intro, fitsD := True.intro,
      context := by
        intro i A _ hi
        have hnone : (none : Option (Expr Nat)) = some A := hi
        cases hnone }
  let p := L.term d hd (Levels.of_closed σ (fun _ => 0) b hlvl)
  refine ⟨p, ?_, rfl, ?_⟩
  · exact substT_id b
  · intro i
    exact Provenance.neutral i

end Rcic.F3.PSet.ReaderPacket
