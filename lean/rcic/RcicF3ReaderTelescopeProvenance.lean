import rcic.RcicF3ReaderWhnfProvenance
import rcic.RcicF3ReaderPacketBinder
import rcic.RcicF3PiSmallMaskSpine

/-!
# Bounded domain masking for a successful normalized telescope

Each actual Pi head is obtained by the executable weak-head provenance
producer. Its original bounded source typing supplies the domain typing
and the next body's sort typing. The reached argument extends both
original fits; the masked assignment is extended by the same value and
is never asserted to fit. This iterates at arbitrary reader depth.

The final theorem starts with the original bounded field typing and the
actual successful reader equation. Only emitted domain syntax is required
to be family-free. The complete terminal expression and all child/output
keys are retained without a mask-independence condition.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open ReaderSubstitution (capture Levels)

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat}

/-- Original sort typing makes both original code denotations nonempty,
even when the original valuation differs from the reader valuation. -/
theorem Packet.nonempty {ρ η : Nat → PSet.{4}}
    (p : Packet P μ fd C σ K ρ η) (l : Level) (ht : p.expected = .sort l) :
    (¬ Equiv (den (mkM P (table P μ fd C)) σ ρ p.code) pempty) ∧
    (¬ Equiv (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.code) pempty) := by
  constructor
  · have hm := p.memberC
    change den (mkM P (table P μ fd C)) σ ρ (substT p.s p.expr) ∈
      Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) p.τ
          (capture (mkM P (table P μ fd C)) σ ρ p.s) p.expected) at hm
    rw [ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ, ht] at hm
    have hn := den_type_ne_pempty (mkM P (table P μ fd C)) p.τ
      (fun k => pempty_not_mem_U4 P k) _ hm
    intro hz
    apply hn
    rw [← ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ]
    exact hz
  · have hm := p.memberD
    change den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (substT p.s p.expr) ∈
      Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.τ
          (capture (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.s)
          p.expected) at hm
    rw [ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ, ht] at hm
    have hn := den_type_ne_pempty (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) p.τ
      (fun k => pempty_not_mem_U4 P k) _ hm
    intro hz
    apply hn
    rw [← ReaderSubstitution.den_closure _ σ p.τ p.expr p.levels p.s ρ]
    exact hz

/-- Actual provenance and a successful reader produce the reached-domain
relation. The terminal expression is unconstrained. -/
theorem telescope_domains {reader : ResolvedEnv} (W : World P μ fd C σ K reader) :
    ∀ (fuel : Nat) (ρ η : Nat → PSet.{4}) (p : Packet P μ fd C σ K ρ η)
      (l : Level), p.expected = .sort l →
      (∀ i, Provenance P μ fd C σ K ρ η (p.s i)) →
      ∀ (ds : List (Expr Nat)) (b : Expr Nat),
        piTelescopeFuel reader fuel p.code = some (ds, b) →
        (∀ A ∈ ds, occursConst fd.fref A = false) →
        PiSmallMaskSpine.Domains (mkM P (table P μ fd C))
          (mkM P (table P μ fd C)) σ ds ρ η
  | 0, _, _, _, _, _, _, _, _, hw, _ => by cases hw
  | fuel + 1, ρ, η, p, l, ht, hcaps, ds, b, hw, hfree => by
      cases hh : whnfFuel reader fuel p.code with
      | none => simp only [piTelescopeFuel, hh] at hw; cases hw
      | some w =>
          cases w with
          | pi A B =>
              cases hr : piTelescopeFuel reader fuel B with
              | none => simp only [piTelescopeFuel, hh, hr] at hw; cases hw
              | some pair =>
                  rcases pair with ⟨as, c⟩
                  simp only [piTelescopeFuel, hh, hr] at hw
                  cases hw
                  have hn := p.nonempty l ht
                  obtain ⟨q, hqcode, ⟨A0, B0, hqexpr⟩, hqcap⟩ :=
                    whnf_pi W fuel p.code (Provenance.typed p hcaps) [] A B
                      True.intro hh hn.1 hn.2
                  have he := q.enter_pi A0 B0 A B hqexpr hqcode hqcap
                    (hfree A (List.mem_cons_self _ _))
                  refine ⟨ed_congr (mkM P (table P μ fd C)) he.1, ?_⟩
                  intro a ha
                  obtain ⟨q', hcode', _hτ, _hs, ⟨v, hv⟩, hcap'⟩ := he.2 a ha
                  apply telescope_domains W fuel (vcons a ρ) (vcons a η) q' v hv hcap' as b
                  · rw [hcode']
                    exact hr
                  · intro D hD
                    exact hfree D (List.mem_cons_of_mem _ hD)
          | bvar i =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro
          | sort v =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro
          | const r ls =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro
          | app f a =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro
          | lam A body =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro
          | letE A value body =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro
          | lit t =>
              simp only [piTelescopeFuel, hh] at hw
              cases hw
              exact True.intro

/-- The original field derivation initializes the produced reader trace.
There is no premise asserting typing or provenance of normalized syntax. -/
theorem domains_of_typing {reader E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (W : World P μ fd C σ K reader)
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : RecFieldMask.Marks) (ρ η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (hctx : RecFieldMask.Context P μ fd C σ marks Γ ρ η)
    {A : Expr Nat} {u : Level} (d : HasTyT E n Γ A (.sort u)) (hd : LOKt σ 4 K d)
    (fuel : Nat) (ds : List (Expr Nat)) (b : Expr Nat)
    (hread : piTelescopeFuel reader fuel A = some (ds, b))
    (hfree : ∀ D ∈ ds, occursConst fd.fref D = false) :
    PiSmallMaskSpine.Domains (mkM P (table P μ fd C))
      (mkM P (table P μ fd C)) σ ds ρ η := by
  let L := Local.initial hEC hED hρC hρD marks hctx
  let p := L.term d hd (Levels.refl σ A)
  apply telescope_domains W fuel ρ η p u rfl (fun i => Provenance.neutral i) ds b
  · change piTelescopeFuel reader fuel (substT SubstT.id A) = some (ds, b)
    rw [substT_id]
    exact hread
  · exact hfree

/-- Clean emitted domains may be compiled in the base table. Only that
domain-table change is made; no terminal or child-key denotation is erased. -/
theorem domains_base (ds : List (Expr Nat))
    (hfree : ∀ D ∈ ds, occursConst fd.fref D = false)
    (ρ η : Nat → PSet.{4})
    (h : PiSmallMaskSpine.Domains (mkM P (table P μ fd C))
      (mkM P (table P μ fd C)) σ ds ρ η) :
    PiSmallMaskSpine.Domains (mkM P (table P μ fd C)) (mkM P μ) σ ds ρ η := by
  induction ds generalizing ρ η with
  | nil => exact True.intro
  | cons A ds ih =>
      have he := den_off P μ fd.fref (ofFrame P μ fd C) σ η
        (hfree A (List.mem_cons_self _ _))
      change den (mkM P (table P μ fd C)) σ η A = den (mkM P μ) σ η A at he
      refine ⟨?_, fun a ha => ih
        (fun D hD => hfree D (List.mem_cons_of_mem _ hD)) _ _ (h.2 a ha)⟩
      apply h.1.trans
      rw [he, ed_mkM P (table P μ fd C) μ]
      exact Equiv.rfl

/-- The actual field-to-compiler interface: the supplied bounded typing
and successful normalized reader produce the complete reached-domain mask. -/
theorem domains_base_of_typing {reader E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (W : World P μ fd C σ K reader)
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : RecFieldMask.Marks) (ρ η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (hctx : RecFieldMask.Context P μ fd C σ marks Γ ρ η)
    {A : Expr Nat} {u : Level} (d : HasTyT E n Γ A (.sort u)) (hd : LOKt σ 4 K d)
    (fuel : Nat) (ds : List (Expr Nat)) (b : Expr Nat)
    (hread : piTelescopeFuel reader fuel A = some (ds, b))
    (hfree : ∀ D ∈ ds, occursConst fd.fref D = false) :
    PiSmallMaskSpine.Domains (mkM P (table P μ fd C)) (mkM P μ) σ ds ρ η :=
  domains_base ds hfree ρ η
    (domains_of_typing W hEC hED marks ρ η hρC hρD hctx d hd fuel ds b hread hfree)

end Rcic.F3.PSet.ReaderPacket
