import rcic.RcicF3PiHereditaryEnv
import rcic.RcicF3PiLiveField
/-! Hereditary binder-domain smallness from original typing. Successful
normalization yields exact small-telescope field semantics, including proof
leaves, with no original-field inhabitant. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSized
open Rcic.Declarative
def Sized (M : Interp.{4}) (σ : Nat → Nat) :
    Expr Nat → (Nat → PSet.{4}) → Prop
  | .pi A B, ρ => Sized M σ A ρ ∧ Small.{3,4} (Ed M (den M σ ρ A)) ∧
      ∀ x, x ∈ Ed M (den M σ ρ A) →
        Sized M σ B (vcons x ρ) ∧ Small.{3,4} (Ed M (den M σ (vcons x ρ) B))
  | .lam A b, ρ => Sized M σ A ρ ∧ Small.{3,4} (Ed M (den M σ ρ A)) ∧
      ∀ x, x ∈ Ed M (den M σ ρ A) → Sized M σ b (vcons x ρ)
  | .app f a, ρ => Sized M σ f ρ ∧ Sized M σ a ρ
  | .letE A v b, ρ => Sized M σ A ρ ∧ Small.{3,4} (Ed M (den M σ ρ A)) ∧
      Sized M σ v ρ ∧ Sized M σ b (vcons (den M σ ρ v) ρ)
  | _, _ => True

theorem of_hsound (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (d : HasTyT E n Γ e A) (hd : HSoundT (mkM P μ) σ d)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) : Sized (mkM P μ) σ e ρ := by
  let M := mkM P μ
  have small (x : PSet.{4}) (k : Nat) (hx : x ∈ Ed M (tyv (U W4 k))) : Small.{3,4} (Ed M x) :=
    PiSmallCompile.ed_small P M k (mem_congr_right (ed_tyv M (U4_dich k)) hx)
  cases d with
  | sort => trivial
  | bvar => trivial
  | const => trivial
  | @pi _ A B u v hA hB =>
    exact ⟨of_hsound P μ σ hA hd.2.1 ρ hρ,
      small _ _ (hd.2.1.root ρ hρ), fun x hx =>
        ⟨of_hsound P μ σ hB hd.2.2 (vcons x ρ) ⟨hρ, hx⟩,
          small _ _ (hd.2.2.root _ ⟨hρ, hx⟩)⟩⟩
  | @lam _ A u b B hA hb =>
    exact ⟨of_hsound P μ σ hA hd.2.1 ρ hρ,
      small _ _ (hd.2.1.root ρ hρ), fun x hx =>
        of_hsound P μ σ hb hd.2.2 (vcons x ρ) ⟨hρ, hx⟩⟩
  | app _ _ _ _ _ hf ha =>
    exact ⟨of_hsound P μ σ hf hd.2.1 ρ hρ,
      of_hsound P μ σ ha hd.2.2 ρ hρ⟩
  | letE _ _ _ _ _ _ hA hv hb =>
    exact ⟨of_hsound P μ σ hA hd.2.1 ρ hρ,
      small _ _ (hd.2.1.root ρ hρ),
      of_hsound P μ σ hv hd.2.2.1 ρ hρ,
      of_hsound P μ σ hb hd.2.2.2 _ ⟨hρ, hd.2.2.1.root ρ hρ, Equiv.rfl⟩⟩
  | lit => trivial
  | conv _ _ _ _ _ h _ => exact of_hsound P μ σ h hd.2.1 ρ hρ

theorem Sized.congr (M : Interp.{4}) (σ : Nat → Nat) (e : Expr Nat)
    {ρ ρ' : Nat → PSet.{4}} (hρ : ∀ i, Equiv (ρ i) (ρ' i)) :
    Sized M σ e ρ → Sized M σ e ρ' := by
  induction e generalizing ρ ρ' with
  | bvar => exact fun _ => trivial
  | sort => exact fun _ => trivial
  | const => exact fun _ => trivial
  | lit => exact fun _ => trivial
  | app f a ihf iha => exact fun h => ⟨ihf hρ h.1, iha hρ h.2⟩
  | pi A B ihA ihB =>
    intro h
    have eA := den_congr M σ A hρ
    refine ⟨ihA hρ h.1, Small.congr (ed_congr M eA) h.2.1, ?_⟩
    intro x hx
    have hb := h.2.2 x (mem_congr_right (ed_congr M eA.symm) hx)
    have he := vcons_congr (x := x) Equiv.rfl hρ
    exact ⟨ihB he hb.1, Small.congr (ed_congr M (den_congr M σ B he)) hb.2⟩
  | lam A b ihA ihb =>
    intro h
    have eA := den_congr M σ A hρ
    refine ⟨ihA hρ h.1, Small.congr (ed_congr M eA) h.2.1, ?_⟩
    intro x hx
    exact ihb (vcons_congr (x := x) Equiv.rfl hρ)
      (h.2.2 x (mem_congr_right (ed_congr M eA.symm) hx))
  | letE A v b ihA ihv ihb =>
    intro h
    exact ⟨ihA hρ h.1, Small.congr (ed_congr M (den_congr M σ A hρ)) h.2.1,
      ihv hρ h.2.2.1, ihb (vcons_congr (den_congr M σ v hρ) hρ) h.2.2.2⟩

theorem Sized.lift (M : Interp.{4}) (σ : Nat → Nat) (e : Expr Nat)
    (k j : Nat) (ρ : Nat → PSet.{4}) :
    Sized M σ (Rcic.Declarative.lift k j e) ρ ↔
      Sized M σ e (liftρ k j ρ) := by
  induction e generalizing k ρ with
  | bvar i => simp only [Rcic.Declarative.lift]; split <;> trivial
  | sort => rfl
  | const => rfl
  | lit => rfl
  | app f a ihf iha => simp only [Rcic.Declarative.lift, Sized, ihf, iha]
  | pi A B ihA ihB =>
    simp only [Rcic.Declarative.lift, Sized, ihA, ihB, den_lift, liftρ_cons]
  | lam A b ihA ihb =>
    simp only [Rcic.Declarative.lift, Sized, ihA, ihb, den_lift, liftρ_cons]
  | letE A v b ihA ihv ihb =>
    simp only [Rcic.Declarative.lift, Sized, ihA, ihv, ihb, den_lift, liftρ_cons]

theorem Sized.instantiate (M : Interp.{4}) (σ : Nat → Nat)
    (e rep : Expr Nat) (j : Nat) (ρ : Nat → PSet.{4})
    (hr : Sized M σ rep ρ)
    (he : Sized M σ e (insρ j (den M σ ρ rep) ρ)) :
    Sized M σ (Rcic.Declarative.instantiate j rep e) ρ := by
  induction e generalizing rep j ρ with
  | bvar i =>
    simp only [Rcic.Declarative.instantiate]
    split
    · exact hr
    · split <;> trivial
  | sort => trivial
  | const => trivial
  | lit => trivial
  | app f a ihf iha => exact ⟨ihf _ _ _ hr he.1, iha _ _ _ hr he.2⟩
  | pi A B ihA ihB =>
    have hrep : ∀ x : PSet.{4},
        den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 rep) = den M σ ρ rep := by
      intro x
      rw [den_lift, liftρ_zero, shiftρ_one_cons]
    have hreg : ∀ x : PSet.{4}, Sized M σ (Rcic.Declarative.lift 0 1 rep) (vcons x ρ) := by
      intro x
      rw [Sized.lift, liftρ_zero, shiftρ_one_cons]
      exact hr
    refine ⟨ihA _ _ _ hr he.1, ?_, ?_⟩
    · simpa only [den_instantiate] using he.2.1
    · intro x hx
      rw [den_instantiate] at hx
      have hB := he.2.2 x hx
      refine ⟨?_, ?_⟩
      · apply ihB _ _ _ (hreg x)
        simpa only [hrep, insρ_succ_cons] using hB.1
      · simpa only [den_instantiate, hrep, insρ_succ_cons] using hB.2
  | lam A b ihA ihb =>
    have hrep : ∀ x : PSet.{4},
        den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 rep) = den M σ ρ rep := by
      intro x
      rw [den_lift, liftρ_zero, shiftρ_one_cons]
    have hreg : ∀ x : PSet.{4}, Sized M σ (Rcic.Declarative.lift 0 1 rep) (vcons x ρ) := by
      intro x
      rw [Sized.lift, liftρ_zero, shiftρ_one_cons]
      exact hr
    refine ⟨ihA _ _ _ hr he.1, ?_, ?_⟩
    · simpa only [den_instantiate] using he.2.1
    · intro x hx
      rw [den_instantiate] at hx
      apply ihb _ _ _ (hreg x)
      simpa only [hrep, insρ_succ_cons] using he.2.2 x hx
  | letE A v b ihA ihv ihb =>
    have hrep : ∀ x : PSet.{4},
        den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 rep) = den M σ ρ rep := by
      intro x
      rw [den_lift, liftρ_zero, shiftρ_one_cons]
    have hreg : ∀ x : PSet.{4}, Sized M σ (Rcic.Declarative.lift 0 1 rep) (vcons x ρ) := by
      intro x
      rw [Sized.lift, liftρ_zero, shiftρ_one_cons]
      exact hr
    refine ⟨ihA _ _ _ hr he.1, ?_, ihv _ _ _ hr he.2.2.1, ?_⟩
    · simpa only [den_instantiate] using he.2.1
    · apply ihb _ _ _ (hreg _)
      simpa only [den_instantiate, hrep, insρ_succ_cons] using he.2.2.2

theorem Sized.foldApps (M : Interp.{4}) (σ : Nat → Nat) (f : Expr Nat)
    (as : List (Expr Nat)) (ρ : Nat → PSet.{4}) :
    Sized M σ (Rcic.Declarative.foldApps f as) ρ ↔
      Sized M σ f ρ ∧ ∀ a, a ∈ as → Sized M σ a ρ := by
  induction as generalizing f with
  | nil => simp only [Rcic.Declarative.foldApps, List.not_mem_nil, false_implies, implies_true, _root_.and_true]
  | cons a as ih =>
    simp only [Rcic.Declarative.foldApps, ih, Sized, List.mem_cons, forall_eq_or_imp]
    exact and_assoc

def BodiesSized (M : Interp.{4}) (σ K : Nat → Nat) (E : ResolvedEnv) : Prop :=
  ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat) (ls : List Level),
    E.members r = some m → m.body = some b → transparent m.mclass = true →
    ls.length = m.arity → LevelsOK σ (K r) ls →
    ∀ ρ, Sized M σ (instantiateLevels ls b) ρ

theorem Sized.whnf (M : Interp.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound M σ K E n)
    (hbodies : BodiesOK E σ K) (hregBodies : BodiesSized M σ K E)
    (ρ : Nat → PSet.{4}) :
    ∀ fuel e e', whnfFuel E fuel e = some e' → InstOK E σ K e →
      ¬ Equiv (den M σ ρ e) pempty → Sized M σ e ρ → Sized M σ e' ρ
  | 0, _, _, h, _, _, _ => by cases h
  | fuel + 1, e, e', h, hI, hne, hR => by
      have he : Rcic.Declarative.foldApps (appsSpine e).1 (appsSpine e).2 = e := foldApps_appsSpine e
      cases hs : appsSpine e with
      | mk hd args =>
        rw [hs] at he
        simp only at he
        have hRs : Sized M σ hd ρ ∧ ∀ a, a ∈ args → Sized M σ a ρ := by
          apply (Sized.foldApps M σ hd args ρ).mp
          rw [he]
          exact hR
        cases hd with
        | lam A b =>
            cases args with
            | nil =>
                simp only [whnfFuel, hs] at h
                cases h
                exact hR
            | cons a args =>
                simp only [whnfFuel, hs] at h
                have hden : den M σ ρ e = fapps (fapp (lamVal M (den M σ ρ A) fun x => den M σ (vcons x ρ) b)
                    (den M σ ρ a)) (args.map (den M σ ρ)) := by
                  rw [← he, show Rcic.Declarative.foldApps (Expr.lam A b) (a :: args) = Rcic.Declarative.foldApps (.app (.lam A b) a) args from rfl,
                    den_foldApps]
                  rfl
                have hne' : ¬ Equiv (fapp (lamVal M (den M σ ρ A) fun x => den M σ (vcons x ρ) b) (den M σ ρ a))
                    pempty := by
                  intro h0
                  apply hne
                  rw [hden]
                  exact (fapps_congr h0 _).trans (fapps_pempty _)
                have hx := mem_of_fapp_lamVal_ne M hne'
                have hβ := beta_val M (A := den M σ ρ A) (b := fun x => den M σ (vcons x ρ) b)
                  (fun x x' hxx => den_congr M σ b (vcons_congr hxx (fun _ => Equiv.rfl))) hx
                have hstep : Equiv (den M σ ρ (Rcic.Declarative.foldApps (instantiate0 a b) args)) (den M σ ρ e) := by
                  rw [hden, den_foldApps, den_inst0]
                  exact fapps_congr hβ.symm _
                have hI' : InstOK E σ K (Rcic.Declarative.foldApps (instantiate0 a b) args) := by
                  refine InstOK.sub (fun p hp => ?_) hI
                  rw [← he]
                  rcases (constInsts_foldApps _ _ p).mp hp with hp | ⟨c, hc, hp⟩
                  · rcases constInsts_instantiate 0 a b p hp with hp | hp
                    · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨a, List.mem_cons_self _ _, hp⟩)
                    · exact (constInsts_foldApps _ _ p).mpr (Or.inl (List.mem_append_right _ hp))
                  · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨c, List.mem_cons_of_mem _ hc, hp⟩)
                have hRb : Sized M σ (instantiate0 a b) ρ := by
                  apply Sized.instantiate M σ b a 0 ρ (hRs.2 a (List.mem_cons_self _ _))
                  simpa only [insρ_zero] using hRs.1.2.2 (den M σ ρ a) hx
                have hR' := (Sized.foldApps M σ _ args ρ).mpr
                  ⟨hRb, fun c hc => hRs.2 c (List.mem_cons_of_mem _ hc)⟩
                exact Sized.whnf M σ K hE hbodies hregBodies ρ fuel _ e' h hI'
                  (fun h0 => hne (hstep.symm.trans h0)) hR' 
        | letE A v b =>
            simp only [whnfFuel, hs] at h
            have hstep : den M σ ρ (Rcic.Declarative.foldApps (instantiate0 v b) args) = den M σ ρ e := by
              rw [← he, den_foldApps, den_foldApps, den_inst0]
              rfl
            have hI' : InstOK E σ K (Rcic.Declarative.foldApps (instantiate0 v b) args) := by
              refine InstOK.sub (fun p hp => ?_) hI
              rw [← he]
              rcases (constInsts_foldApps _ _ p).mp hp with hp | ⟨c, hc, hp⟩
              · rcases constInsts_instantiate 0 v b p hp with hp | hp
                · exact (constInsts_foldApps _ _ p).mpr
                    (Or.inl (List.mem_append_left _ (List.mem_append_right _ hp)))
                · exact (constInsts_foldApps _ _ p).mpr (Or.inl (List.mem_append_right _ hp))
              · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨c, hc, hp⟩)
            have hRb : Sized M σ (instantiate0 v b) ρ := by
              apply Sized.instantiate M σ b v 0 ρ hRs.1.2.2.1
              simpa only [insρ_zero] using hRs.1.2.2.2
            have hR' := (Sized.foldApps M σ _ args ρ).mpr ⟨hRb, hRs.2⟩
            exact Sized.whnf M σ K hE hbodies hregBodies ρ fuel _ e' h hI'
              (fun h0 => hne (hstep ▸ h0)) hR' 
        | const r ls =>
            cases ht : transparentBody E r ls with
            | none =>
                simp only [whnfFuel, hs, ht] at h
                cases h
                exact hR
            | some body =>
                simp only [whnfFuel, hs, ht] at h
                obtain ⟨m, hres, htr, b, hb, rfl⟩ : ∃ m, E.members r = some m ∧ transparent m.mclass = true ∧
                    ∃ b, m.body = some b ∧ body = instantiateLevels ls b := by
                  unfold transparentBody at ht
                  cases hm : E.members r with
                  | none => rw [hm] at ht; cases ht
                  | some m =>
                      rw [hm] at ht
                      simp only at ht
                      by_cases htr : transparent m.mclass = true
                      · rw [if_pos htr] at ht
                        cases hb : m.body with
                        | none => rw [hb] at ht; cases ht
                        | some b0 =>
                            rw [hb] at ht
                            exact ⟨m, rfl, htr, b0, hb, (Option.some.inj ht).symm⟩
                      · rw [if_neg htr] at ht; cases ht
                have hhead : (r, ls) ∈ constInsts e := by
                  rw [← he]
                  exact (constInsts_foldApps _ _ _).mpr (Or.inl (List.mem_singleton_self _))
                obtain ⟨m', hres', hlen, hl⟩ := hI r ls hhead
                rw [hres] at hres'
                cases hres'
                have hδ := hE.delta [] r ls m b ρ hres hb htr hlen hl trivial
                have hstep : Equiv (den M σ ρ (Rcic.Declarative.foldApps (instantiateLevels ls b) args)) (den M σ ρ e) := by
                  rw [← he, den_foldApps, den_foldApps]
                  exact fapps_congr hδ.symm _
                have hI' : InstOK E σ K (Rcic.Declarative.foldApps (instantiateLevels ls b) args) := by
                  intro r' ls' hp
                  rcases (constInsts_foldApps _ _ _).mp hp with hp | ⟨c, hc, hp⟩
                  · exact hbodies r m b ls hres hb htr hlen hl r' ls' hp
                  · refine hI r' ls' ?_
                    rw [← he]
                    exact (constInsts_foldApps _ _ _).mpr (Or.inr ⟨c, hc, hp⟩)
                have hR' := (Sized.foldApps M σ _ args ρ).mpr
                  ⟨hregBodies r m b ls hres hb htr hlen hl ρ, hRs.2⟩
                exact Sized.whnf M σ K hE hbodies hregBodies ρ fuel _ e' h hI'
                  (fun h0 => hne (hstep.symm.trans h0)) hR' 
        | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact hR
        | sort _ => simp only [whnfFuel, hs] at h; cases h; exact hR
        | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact hR
        | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact hR
        | lit _ => simp only [whnfFuel, hs] at h; cases h; exact hR

theorem Sized.levelsClosed (M : Interp.{4}) (σ σ' : Nat → Nat)
    (e : Expr Nat) (he : exprLevelsBounded 0 e = true) (ρ : Nat → PSet.{4}) :
    Sized M σ e ρ ↔ Sized M σ' e ρ := by
  induction e generalizing ρ with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | lit => rfl
  | app f a ihf iha =>
    simp only [exprLevelsBounded, Bool.and_eq_true] at he
    simp only [Sized, ihf he.1, iha he.2]
  | pi A B ihA ihB =>
    simp only [exprLevelsBounded, Bool.and_eq_true] at he
    simp only [Sized, ihA he.1, ihB he.2,
      den_levels_closed M σ σ' A he.1, den_levels_closed M σ σ' B he.2]
  | lam A b ihA ihb =>
    simp only [exprLevelsBounded, Bool.and_eq_true] at he
    simp only [Sized, ihA he.1, ihb he.2, den_levels_closed M σ σ' A he.1]
  | letE A v b ihA ihv ihb =>
    simp only [exprLevelsBounded, Bool.and_eq_true] at he
    simp only [Sized, ihA he.1.1, ihv he.1.2, ihb he.2,
      den_levels_closed M σ σ' A he.1.1, den_levels_closed M σ σ' v he.1.2]

/-- Successful extraction has small domains at all actual paths. -/
theorem telescope_liveSmall (M : Interp.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound M σ K E n)
    (hbodies : BodiesOK E σ K) (hregBodies : PiHereditary.BodiesRegular M σ K E)
    (hsizeBodies : BodiesSized M σ K E) :
    ∀ fuel T ds b ρ, piTelescopeFuel E fuel T = some (ds, b) → InstOK E σ K T →
      ¬ Equiv (den M σ ρ T) pempty → PiHereditary.Regular M σ T ρ → Sized M σ T ρ →
      PiLive.LiveSmall M σ ds ρ
  | 0, _, _, _, _, h, _, _, _, _ => by cases h
  | fuel + 1, T, ds, b, ρ, h, hI, hne, hR, hS => by
      cases hw : whnfFuel E fuel T with
      | none => simp only [piTelescopeFuel, hw] at h; cases h
      | some w =>
          have hIw := instOK_whnf hbodies fuel T w hw hI
          have hRw := PiHereditary.Regular.whnf M σ K hE hbodies hregBodies ρ fuel T w hw hI hne hR
          have hSw := Sized.whnf M σ K hE hbodies hsizeBodies ρ fuel T w hw hI hne hS
          cases w with
          | pi A B =>
              cases ht : piTelescopeFuel E fuel B with
              | none => simp only [piTelescopeFuel, hw, ht] at h; cases h
              | some p =>
                  rcases p with ⟨as, c⟩
                  simp only [piTelescopeFuel, hw, ht] at h
                  cases h
                  have hIB : InstOK E σ K B := InstOK.sub
                    (fun _ hp => List.mem_append_right _ hp) hIw
                  refine ⟨fun _ => hSw.2.1, fun a ha => ?_⟩
                  have hBa := hRw.2.2 a ha
                  exact telescope_liveSmall M σ K hE hbodies hregBodies hsizeBodies fuel B as b
                    (vcons a ρ) ht hIB hBa.2 hBa.1 (hSw.2.2 a ha).1
          | bvar _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
          | sort _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
          | const _ _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
          | app _ _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
          | lam _ _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
          | letE _ _ _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
          | lit _ => simp only [piTelescopeFuel, hw] at h; cases h; trivial
/-- Elementary composition: original bounded typing pays domain smallness. -/
theorem liveSmall_typed4 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P μ) σ K E n) (hb : BodiesOK E σ K)
    (hR : PiHereditary.BodiesRegular (mkM P μ) σ K E)
    (hS : BodiesSized (mkM P μ) σ K E)
    {Γ : LCtx} {T : Expr Nat} {l : Level} (d : HasTyT E n Γ T (.sort l))
    (hd : LOKt σ 4 K d) {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel E fuel T = some (ds, b))
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    PiLive.LiveSmall (mkM P μ) σ ds ρ := by
  have hs := hsound_ty (P.good _ rfl) hE d hd
  exact telescope_liveSmall (mkM P μ) σ K hE hb hR hS fuel T ds b ρ hw
    (instOK_of_lokt σ 4 K d hd)
    (den_type_ne_pempty (mkM P μ) σ (fun k => pempty_not_mem_U4 P k) ρ (hs.root ρ hρ))
    (PiHereditary.of_hsound (mkM P μ) σ (fun k => pempty_not_mem_U4 P k) d hs ρ hρ)
    (of_hsound P μ σ d hs ρ hρ)
universe v
/-- Elementary composition: both membership directions for small telescopes,
including proof leaves and without a supplied original-field inhabitant. -/
theorem compiled_field_ed {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound (mkM P μ) σ K E n)
    (hb : BodiesOK E σ K) (hR : PiHereditary.BodiesRegular (mkM P μ) σ K E)
    (hS : BodiesSized (mkM P μ) σ K E)
    {Γ : LCtx} {T : Expr Nat} {l : Level} (d : HasTyT E n Γ T (.sort l))
    (hd : LOKt σ 4 K d) {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel E fuel T = some (ds, b))
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (hL : ∀ ρ', Equiv (X (R ρ')) (Ed (mkM P μ) (den (mkM P μ) σ ρ' b)))
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv (Ed (mkM P μ) ((PiSmallCompile.widen (PiSmallCompile.compile P μ σ R ds ρ)).erasedType
      (mkM P μ) X)) (Ed (mkM P μ) (den (mkM P μ) σ ρ T)) :=
  (PiLive.compile_ed P μ σ R X hX b hL ds ρ
    (liveSmall_typed4 P μ σ K hE hb hR hS d hd hw ρ hρ)).trans
      (ed_congr (mkM P μ) (PiHereditary.den_piTelescope_typed4 P μ σ K hE hb hR d hd hw ρ hρ))
end Rcic.F3.PSet.PiSized
