import rcic.RcicF3ReaderPacketWorld

/-!
# Actual typed arguments on a reader application spine

Every pending argument is an original typed packet with its own complete
capture provenance. The head's expected products come from the original
application derivations. Reduction may replace the head by an equivalent
value while preserving these product memberships. A beta transition then
compares the expected product to the lambda's literal annotation using
the nonempty common function; no syntactic Pi injectivity is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open ReaderSubstitution (capture Levels)

structure Argument (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    (ρ η : Nat → PSet.{4}) where
  packet : Packet P μ fd C σ K ρ η
  captures : ∀ i, Provenance P μ fd C σ K ρ η (packet.s i)

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat} {ρ η : Nat → PSet.{4}}

noncomputable def codes (args : List (Argument P μ fd C σ K ρ η)) : List (Expr Nat) :=
  args.map (fun a => a.packet.code)

def Spine : (gC gD : PSet.{4}) → List (Argument P μ fd C σ K ρ η) → Prop
  | _, _, [] => True
  | gC, gD, a :: args => ∃ BC BD : PSet.{4} → PSet.{4},
      (∀ x y, Equiv x y → Equiv (BC x) (BC y)) ∧
      (∀ x y, Equiv x y → Equiv (BD x) (BD y)) ∧
      gC ∈ Ed (mkM P (table P μ fd C))
        (piVal (mkM P (table P μ fd C)) a.packet.typeC BC) ∧
      gD ∈ Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (piVal (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) a.packet.typeD BD) ∧
      Spine (fapp gC (den (mkM P (table P μ fd C)) σ ρ a.packet.code))
        (fapp gD (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
          σ ρ a.packet.code)) args

theorem Spine.congr : ∀ (args : List (Argument P μ fd C σ K ρ η))
    {gC gD hC hD : PSet.{4}}, Spine gC gD args → Equiv gC hC → Equiv gD hD →
      Spine hC hD args
  | [], _, _, _, _, _, _, _ => True.intro
  | a :: args, _, _, _, _, h, eC, eD => by
      obtain ⟨BC, BD, hBC, hBD, hC, hD, ht⟩ := h
      exact ⟨BC, BD, hBC, hBD, mem_congr_left eC hC, mem_congr_left eD hD,
        Spine.congr args ht (fapp_congr eC Equiv.rfl) (fapp_congr eD Equiv.rfl)⟩

/-- The first pending application cannot be empty when the complete
reader application is nonempty. No typings of the reduced application are
needed to retain this fact. -/
theorem first_ne (M : Interp.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (head arg : Expr Nat) (args : List (Expr Nat))
    (hne : ¬ Equiv (den M σ ρ (foldApps head (arg :: args))) pempty) :
    ¬ Equiv (fapp (den M σ ρ head) (den M σ ρ arg)) pempty := by
  intro he
  apply hne
  change Equiv (den M σ ρ (foldApps (.app head arg) args)) pempty
  rw [den_foldApps]
  exact (fapps_congr he _).trans (fapps_pempty _)

/-- The expected first product is produced from the original application
premise, with the argument's original expected type and valuation intact. -/
theorem application (L : Local P μ fd C σ K ρ η)
    {f a A B : Expr Nat}
    (df : HasTyT L.E L.n L.Γ f (.pi A B)) (da : HasTyT L.E L.n L.Γ a A)
    (hf : LOKt L.τ 4 K df) (ha : LOKt L.τ 4 K da)
    (hlf : Levels σ L.τ f) (hla : Levels σ L.τ a)
    (hcaps : ∀ i, Provenance P μ fd C σ K ρ η (L.s i))
    (args : List (Argument P μ fd C σ K ρ η))
    (ht : Spine
      (den (mkM P (table P μ fd C)) σ ρ (substT L.s (.app f a)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
        (substT L.s (.app f a))) args) :
    Spine
      (den (mkM P (table P μ fd C)) σ ρ (substT L.s f))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (substT L.s f))
      ({ packet := L.term da ha hla, captures := hcaps } :: args) := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  let ρC := capture MC σ ρ L.s
  let ρD := capture MD σ ρ L.s
  refine ⟨(fun x => den MC L.τ (vcons x ρC) B),
    (fun x => den MD L.τ (vcons x ρD) B),
    den_resp MC L.τ ρC B, den_resp MD L.τ ρD B, ?_, ?_, ht⟩
  · exact (L.term df hf hlf).memberC
  · exact (L.term df hf hlf).memberD

end Rcic.F3.PSet.ReaderPacket
