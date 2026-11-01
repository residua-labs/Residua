import rcic.RcicF3ReaderPacketReduce

/-!
# Provenance through the actual weak-head reader

The induction follows the executable reader fuel and the original typing
derivations/capture provenance. Application decomposition retains its
actual typed arguments. Beta, zeta and transparent delta construct the
next packet; a local variable forces its existing capture provenance.
Every successful Pi head is therefore a literal Pi in an original typed
source closure, including converted beta heads and zero-valuation stored
delta bodies. No typed-reduct, Pi-injectivity or normalization callback is
assumed. The masked assignment is never required to fit.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative RawFamily
open ReaderSubstitution (capture Levels)

variable {P : Premises4} {μ : Nat → List Nat → PSet.{4}}
  {fd : FamData} {C : Frame} {σ K : Nat → Nat} {ρ η : Nat → PSet.{4}}

def ExposesPi (A B : Expr Nat) : Prop :=
  ∃ p : Packet P μ fd C σ K ρ η,
    p.code = .pi A B ∧ (∃ A0 B0, p.expr = .pi A0 B0) ∧
      (∀ i, Provenance P μ fd C σ K ρ η (p.s i))

private theorem folded_equiv (M : Interp.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) (head head' : Expr Nat) (args : List (Expr Nat))
    (he : Equiv (den M σ ρ head) (den M σ ρ head')) :
    Equiv (den M σ ρ (foldApps head args))
      (den M σ ρ (foldApps head' args)) := by
  rw [den_foldApps, den_foldApps]
  exact fapps_congr he _

private def TraceGoal (reader : ResolvedEnv) (fuel : Nat) (head : Expr Nat) : Prop :=
  ∀ (args : List (Argument P μ fd C σ K ρ η)) (A B : Expr Nat),
    Spine
      (den (mkM P (table P μ fd C)) σ ρ head)
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ head) args →
    whnfFuel reader fuel (foldApps head (codes args)) = some (.pi A B) →
    (¬ Equiv (den (mkM P (table P μ fd C)) σ ρ
      (foldApps head (codes args))) pempty) →
    (¬ Equiv (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
      (foldApps head (codes args))) pempty) →
    ExposesPi (P := P) (μ := μ) (fd := fd) (C := C) (σ := σ) (K := K)
      (ρ := ρ) (η := η) A B

/-- Administrative application/outer-conversion decomposition is by the
original typing derivation. Actual reductions use the strictly smaller
reader fuel; forcing a capture uses its finite provenance induction. -/
private theorem typed_step {reader : ResolvedEnv}
    (W : World P μ fd C σ K reader) (fuel : Nat)
    (ih : ∀ e, Provenance P μ fd C σ K ρ η e →
      TraceGoal (P := P) (μ := μ) (fd := fd) (C := C) (σ := σ) (K := K)
        (ρ := ρ) (η := η) reader fuel e)
    (L : Local P μ fd C σ K ρ η) :
    {e T : Expr Nat} → (d : HasTyT L.E L.n L.Γ e T) →
      LOKt L.τ 4 K d → Levels σ L.τ e →
      (∀ i, Provenance P μ fd C σ K ρ η (L.s i)) →
      (∀ i, TraceGoal (P := P) (μ := μ) (fd := fd) (C := C) (σ := σ) (K := K)
        (ρ := ρ) (η := η) reader (fuel + 1) (L.s i)) →
      TraceGoal (P := P) (μ := μ) (fd := fd) (C := C) (σ := σ) (K := K)
        (ρ := ρ) (η := η) reader (fuel + 1) (substT L.s e)
  | _, _, .bvar _ i _ _, _, _, _, hcaptures => hcaptures i
  | _, _, .conv _ _ _ _ _ d _, hd, hl, hc, hci =>
      typed_step W fuel ih L d hd.1 hl hc hci
  | _, _, .app _ f a A B df da, hd, hl, hc, hci => by
      intro args A' B' hs hw hnC hnD
      let arg : Argument P μ fd C σ K ρ η :=
        { packet := L.term da hd.2 hl.2, captures := hc }
      have hs' := application L df da hd.1 hd.2 hl.1 hl.2 hc args hs
      exact typed_step W fuel ih L df hd.1 hl.1 hc hci
        (arg :: args) A' B' hs' hw hnC hnD
  | _, _, .sort _ l, _, _, _, _ => by
      intro args A B _ hw _ _
      have he : foldApps (.sort l) (codes args) = .pi A B := Option.some.inj (by
        simpa only [substT, whnfFuel, appsSpine_foldApps, appsSpine, List.nil_append] using hw)
      exact (foldApps_ne_pi (.sort l) (fun _ _ h => Expr.noConfusion h)
        (codes args) A B he).elim
  | _, _, .lit _ t _ _, _, _, _, _ => by
      intro args A B _ hw _ _
      have he : foldApps (.lit t) (codes args) = .pi A B := Option.some.inj (by
        simpa only [substT, whnfFuel, appsSpine_foldApps, appsSpine, List.nil_append] using hw)
      exact (foldApps_ne_pi (.lit t) (fun _ _ h => Expr.noConfusion h)
        (codes args) A B he).elim
  | _, _, .pi _ A0 u B0 v dA dB, hd, hl, hc, _ => by
      intro args A B _ hw _ _
      cases args with
      | nil =>
          have he : (.pi (substT L.s A0) (substT L.s.up B0) : Expr Nat) = .pi A B :=
            Option.some.inj (by
              simpa only [substT, codes, List.map_nil, foldApps, whnfFuel, appsSpine] using hw)
          let p := L.term (.pi L.Γ A0 u B0 v dA dB) hd hl
          exact ⟨p, he, ⟨A0, B0, rfl⟩, hc⟩
      | cons a args =>
          have he : foldApps
              (.app (.pi (substT L.s A0) (substT L.s.up B0)) a.packet.code)
              (codes args) = .pi A B := Option.some.inj (by
            simpa only [substT, codes, List.map_cons, whnfFuel,
              appsSpine_foldApps, appsSpine, List.nil_append] using hw)
          exact (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h)
            (codes args) A B he).elim
  | _, _, .lam _ A0 _ body B0 _ db, hd, hl, hc, _ => by
      intro args A B hs hw hnC hnD
      cases args with
      | nil =>
          have he : (.lam (substT L.s A0) (substT L.s.up body) : Expr Nat) = .pi A B :=
            Option.some.inj (by
              simpa only [substT, codes, List.map_nil, foldApps, whnfFuel, appsSpine] using hw)
          exact Expr.noConfusion he
      | cons a args =>
          obtain ⟨BC, BD, hBC, hBD, hfunC, hfunD, htail⟩ := hs
          have hnC' := first_ne (mkM P (table P μ fd C)) σ ρ
            (substT L.s (.lam A0 body)) a.packet.code (codes args) hnC
          have hnD' := first_ne (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
            (substT L.s (.lam A0 body)) a.packet.code (codes args) hnD
          obtain ⟨p, hp, hpc, eC, eD⟩ := beta_packet L db hd.2 hl.1 hl.2 hc a
            BC BD hBC hBD hfunC hfunD hnC' hnD'
          have hw' : whnfFuel reader fuel (foldApps p.code (codes args)) = some (.pi A B) := by
            rw [hp]
            simpa only [substT, codes, List.map_cons, whnfFuel,
              appsSpine_foldApps, appsSpine, List.nil_append] using hw
          have hs' := Spine.congr args htail eC eD
          have hnC'' : ¬ Equiv (den (mkM P (table P μ fd C)) σ ρ
              (foldApps p.code (codes args))) pempty := by
            intro h0
            exact hnC ((folded_equiv _ σ ρ
              (.app (substT L.s (.lam A0 body)) a.packet.code) p.code (codes args) eC).trans h0)
          have hnD'' : ¬ Equiv (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
              (foldApps p.code (codes args))) pempty := by
            intro h0
            exact hnD ((folded_equiv _ σ ρ
              (.app (substT L.s (.lam A0 body)) a.packet.code) p.code (codes args) eD).trans h0)
          exact ih p.code (Provenance.typed p hpc) args A B hs' hw' hnC'' hnD''
  | _, _, .letE _ A0 _ value B0 body _ dv db, hd, hl, hc, _ => by
      intro args A B hs hw hnC hnD
      obtain ⟨p, hp, hpc⟩ := zeta_packet L dv db hd.2.1 hd.2.2 hl.1.2 hl.2 hc
      have eC : Equiv
          (den (mkM P (table P μ fd C)) σ ρ (substT L.s (.letE A0 value body)))
          (den (mkM P (table P μ fd C)) σ ρ p.code) := by
        rw [hp, den_inst0]
        exact Equiv.rfl
      have eD : Equiv
          (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
            (substT L.s (.letE A0 value body)))
          (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.code) := by
        rw [hp, den_inst0]
        exact Equiv.rfl
      have hw' : whnfFuel reader fuel (foldApps p.code (codes args)) = some (.pi A B) := by
        rw [hp]
        simpa only [substT, whnfFuel, appsSpine_foldApps, appsSpine, List.nil_append] using hw
      exact ih p.code (Provenance.typed p hpc) args A B (Spine.congr args hs eC eD) hw'
        (fun h0 => hnC ((folded_equiv _ σ ρ (substT L.s (.letE A0 value body))
          p.code (codes args) eC).trans h0))
        (fun h0 => hnD ((folded_equiv _ σ ρ (substT L.s (.letE A0 value body))
          p.code (codes args) eD).trans h0))
  | _, _, .const _ r ls _ _ _ _, _, _, _, _ => by
      intro args A B hs hw hnC hnD
      cases hr : transparentBody reader r ls with
      | none =>
          have he : foldApps (.const r ls) (codes args) = .pi A B := Option.some.inj (by
            simpa only [substT, whnfFuel, appsSpine_foldApps, appsSpine,
              List.nil_append, hr] using hw)
          exact (foldApps_ne_pi (.const r ls) (fun _ _ h => Expr.noConfusion h)
            (codes args) A B he).elim
      | some body =>
          obtain ⟨p, hp, _hzero, hpc⟩ := W.body_packet ρ η r ls body hr
          have eC : Equiv (den (mkM P (table P μ fd C)) σ ρ (.const r ls))
              (den (mkM P (table P μ fd C)) σ ρ p.code) := by
            rw [hp]
            exact W.deltaC r ls body hr ρ
          have eD : Equiv
              (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (.const r ls))
              (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ p.code) := by
            rw [hp]
            exact W.deltaD r ls body hr ρ
          have hw' : whnfFuel reader fuel (foldApps p.code (codes args)) = some (.pi A B) := by
            rw [hp]
            simpa only [substT, whnfFuel, appsSpine_foldApps, appsSpine,
              List.nil_append, hr] using hw
          exact ih p.code (Provenance.typed p hpc) args A B (Spine.congr args hs eC eD) hw'
            (fun h0 => hnC ((folded_equiv _ σ ρ (.const r ls) p.code (codes args) eC).trans h0))
            (fun h0 => hnD ((folded_equiv _ σ ρ (.const r ls) p.code (codes args) eD).trans h0))

/-- Every successful literal Pi head has produced original typed provenance.
The only nonemptiness inputs concern the two ORIGINAL evaluations. -/
theorem whnf_pi {reader : ResolvedEnv} (W : World P μ fd C σ K reader)
    (fuel : Nat) (head : Expr Nat) (h : Provenance P μ fd C σ K ρ η head)
    (args : List (Argument P μ fd C σ K ρ η)) (A B : Expr Nat)
    (hs : Spine
      (den (mkM P (table P μ fd C)) σ ρ head)
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ head) args)
    (hw : whnfFuel reader fuel (foldApps head (codes args)) = some (.pi A B))
    (hnC : ¬ Equiv (den (mkM P (table P μ fd C)) σ ρ
      (foldApps head (codes args))) pempty)
    (hnD : ¬ Equiv (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ
      (foldApps head (codes args))) pempty) :
    ExposesPi (P := P) (μ := μ) (fd := fd) (C := C) (σ := σ) (K := K)
      (ρ := ρ) (η := η) A B := by
  have H : ∀ fuel e, Provenance P μ fd C σ K ρ η e →
      TraceGoal (P := P) (μ := μ) (fd := fd) (C := C) (σ := σ) (K := K)
        (ρ := ρ) (η := η) reader fuel e := by
    intro fuel
    induction fuel with
    | zero =>
        intro e _ args A B _ hw _ _
        cases hw
    | succ fuel ih =>
        intro e he
        induction he with
        | neutral i =>
            intro args A B _ hw _ _
            have he : foldApps (.bvar i) (codes args) = .pi A B := Option.some.inj (by
              simpa only [whnfFuel, appsSpine_foldApps, appsSpine, List.nil_append] using hw)
            exact (foldApps_ne_pi (.bvar i) (fun _ _ h => Expr.noConfusion h)
              (codes args) A B he).elim
        | typed p hc hci =>
            exact typed_step W fuel ih p.toLocal p.derivation p.bound p.levels hc hci
  exact H fuel head h args A B hs hw hnC hnD

end Rcic.F3.PSet.ReaderPacket
