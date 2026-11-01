import rcic.RcicF3Whnf
import rcic.RcicF3PiTypedCompile
/-! Semantic normalization along inhabited fields. No syntactic scope wall.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet
open Rcic.Declarative
universe u

/-- Successful weak-head normalization retains bounded constant instances. -/
theorem instOK_whnf {E : ResolvedEnv} {σ K : Nat → Nat}
    (hb : BodiesOK E σ K) : ∀ fuel e e', whnfFuel E fuel e = some e' →
      InstOK E σ K e → InstOK E σ K e'
  | 0, _, _, h, _ => by cases h
  | fuel + 1, e, e', h, hI => by
      have he : foldApps (appsSpine e).1 (appsSpine e).2 = e := foldApps_appsSpine e
      cases hs : appsSpine e with
      | mk hd args =>
        rw [hs] at he
        simp only at he
        cases hd with
        | lam A b =>
            cases args with
            | nil =>
                simp only [whnfFuel, hs] at h
                cases h
                exact hI
            | cons a args =>
                simp only [whnfFuel, hs] at h
                have hI' : InstOK E σ K (foldApps (instantiate0 a b) args) := by
                  refine InstOK.sub (fun p hp => ?_) hI
                  rw [← he]
                  rcases (constInsts_foldApps _ _ p).mp hp with hp | ⟨c, hc, hp⟩
                  · rcases constInsts_instantiate 0 a b p hp with hp | hp
                    · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨a, List.mem_cons_self _ _, hp⟩)
                    · exact (constInsts_foldApps _ _ p).mpr (Or.inl (List.mem_append_right _ hp))
                  · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨c, List.mem_cons_of_mem _ hc, hp⟩)
                exact instOK_whnf hb fuel _ e' h hI'
        | letE A v b =>
            simp only [whnfFuel, hs] at h
            have hI' : InstOK E σ K (foldApps (instantiate0 v b) args) := by
              refine InstOK.sub (fun p hp => ?_) hI
              rw [← he]
              rcases (constInsts_foldApps _ _ p).mp hp with hp | ⟨c, hc, hp⟩
              · rcases constInsts_instantiate 0 v b p hp with hp | hp
                · exact (constInsts_foldApps _ _ p).mpr
                    (Or.inl (List.mem_append_left _ (List.mem_append_right _ hp)))
                · exact (constInsts_foldApps _ _ p).mpr (Or.inl (List.mem_append_right _ hp))
              · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨c, hc, hp⟩)
            exact instOK_whnf hb fuel _ e' h hI'
        | const r ls =>
            cases ht : transparentBody E r ls with
            | none =>
                simp only [whnfFuel, hs, ht] at h
                cases h
                exact hI
            | some body =>
                simp only [whnfFuel, hs, ht] at h
                obtain ⟨m, hres, htr, b, hbody, rfl⟩ : ∃ m, E.members r = some m ∧ transparent m.mclass = true ∧
                    ∃ b, m.body = some b ∧ body = instantiateLevels ls b := by
                  unfold transparentBody at ht
                  cases hm : E.members r with
                  | none => rw [hm] at ht; cases ht
                  | some m =>
                      rw [hm] at ht
                      simp only at ht
                      by_cases htr : transparent m.mclass = true
                      · rw [if_pos htr] at ht
                        cases hbody : m.body with
                        | none => rw [hbody] at ht; cases ht
                        | some b0 =>
                            rw [hbody] at ht
                            exact ⟨m, rfl, htr, b0, hbody, (Option.some.inj ht).symm⟩
                      · rw [if_neg htr] at ht; cases ht
                have hhead : (r, ls) ∈ constInsts e := by
                  rw [← he]
                  exact (constInsts_foldApps _ _ _).mpr (Or.inl (List.mem_singleton_self _))
                obtain ⟨m', hres', hlen, hl⟩ := hI r ls hhead
                rw [hres] at hres'
                cases hres'
                have hI' : InstOK E σ K (foldApps (instantiateLevels ls b) args) := by
                  intro r' ls' hp
                  rcases (constInsts_foldApps _ _ _).mp hp with hp | ⟨c, hc, hp⟩
                  · exact hb r m b ls hres hbody htr hlen hl r' ls' hp
                  · refine hI r' ls' ?_
                    rw [← he]
                    exact (constInsts_foldApps _ _ _).mpr (Or.inr ⟨c, hc, hp⟩)
                exact instOK_whnf hb fuel _ e' h hI'
        | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact hI
        | sort _ => simp only [whnfFuel, hs] at h; cases h; exact hI
        | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact hI
        | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact hI
        | lit _ => simp only [whnfFuel, hs] at h; cases h; exact hI

/-- The telescope reader preserves the actual type of any inhabited
field. Each recursive codomain is inhabited by application of that field;
no subject-reduction or global scope premise is supplied. -/
theorem den_piTelescope_of_mem (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound M σ K E n)
    (hb : BodiesOK E σ K) : ∀ fuel T ds b ρ x,
      piTelescopeFuel E fuel T = some (ds, b) → InstOK E σ K T →
      x ∈ Ed M (den M σ ρ T) →
      Equiv (den M σ ρ (policyPi ds b)) (den M σ ρ T)
  | 0, _, _, _, _, _, h, _, _ => by cases h
  | fuel + 1, T, ds, b, ρ, x, h, hI, hx => by
      cases hw : whnfFuel E fuel T with
      | none => simp only [piTelescopeFuel, hw] at h; cases h
      | some w =>
          have hne : ¬ Equiv (den M σ ρ T) pempty := by
            intro h0
            exact not_mem_pempty (mem_congr_right ((ed_congr M h0).trans (ed_pempty M)) hx)
          have he := den_whnf M σ K hE ρ hb fuel T w hw hI hne
          have hIw := instOK_whnf hb fuel T w hw hI
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
                  have hx' : x ∈ Ed M (piVal M (den M σ ρ A)
                      (fun a => den M σ (vcons a ρ) B)) :=
                    mem_congr_right (ed_congr M he.symm) hx
                  refine Equiv.trans (show Equiv (den M σ ρ (policyPi (A :: as) b))
                    (den M σ ρ (.pi A B)) from ?_) he
                  change Equiv (piVal M (den M σ ρ A)
                    (fun a => den M σ (vcons a ρ) (policyPi as b)))
                    (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) B))
                  apply piVal_congr_on M
                    (B := fun a => den M σ (vcons a ρ) (policyPi as b))
                    (B' := fun a => den M σ (vcons a ρ) B) Equiv.rfl
                    (fun _ _ ha => den_congr M σ (policyPi as b) (vcons_congr (ρ := ρ) (ρ' := ρ) ha (fun _ => Equiv.rfl)))
                    (fun _ _ ha => den_congr M σ B (vcons_congr (ρ := ρ) (ρ' := ρ) ha (fun _ => Equiv.rfl)))
                  intro a ha
                  have hxa : fapp x a ∈ Ed M (den M σ (vcons a ρ) B) := app_mem M
                    (fun _ _ ha => den_congr M σ B (vcons_congr (ρ := ρ) (ρ' := ρ) ha (fun _ => Equiv.rfl))) hx' ha
                  exact den_piTelescope_of_mem M σ K hE hb fuel B as b (vcons a ρ) (fapp x a) ht hIB hxa
          | bvar _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | sort _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | const _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | app _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | lam _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | letE _ _ _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he
          | lit _ => simp only [piTelescopeFuel, hw] at h; cases h; exact he

/-- Products use only domain and codomain element sets. -/
theorem piVal_ed_congr_on (M : Interp.{u}) {A A' : PSet.{u}}
    {B B' : PSet.{u} → PSet.{u}}
    (eA : Equiv (Ed M A) (Ed M A'))
    (hB : ∀ x x', Equiv x x' → Equiv (Ed M (B x)) (Ed M (B x')))
    (hB' : ∀ x x', Equiv x x' → Equiv (Ed M (B' x)) (Ed M (B' x')))
    (eB : ∀ x, x ∈ Ed M A → Equiv (Ed M (B x)) (Ed M (B' x))) :
    Equiv (piVal M A B) (piVal M A' B') := by
  refine tyv_congr (cond_congr ?_ ?_ (piSet_congr_on eA hB hB' eB))
  · constructor
    · intro h x hx y hy
      have hx' := mem_congr_right eA.symm hx
      exact h x hx' y (mem_congr_right (eB x hx').symm hy)
    · intro h x hx y hy
      exact h x (mem_congr_right eA hx) y (mem_congr_right (eB x hx) hy)
  · refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => by
        have hx' := mem_congr_right eA.symm hx
        exact mem_congr_right (eB x hx') (hφ x hx'), hz⟩
    · obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => mem_congr_right (eB x hx).symm
        (hφ x (mem_congr_right eA hx)), hz⟩

/-- Every structural syntax telescope has the same element set as its
compiled semantic telescope. The leaf index records the current denotation,
so this does not extract an independent inductive signature. -/
theorem syntaxCompile_ed (M : Interp.{u}) (σ : Nat → Nat) (b : Expr Nat) :
    ∀ ds ρ, Equiv
      (Ed M ((PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ b) ds ρ).erasedType
        M (fun i => i.1)))
      (Ed M (den M σ ρ (policyPi ds b))) := by
  intro ds
  induction ds with
  | nil => intro ρ; exact ed_tyv M (dich_ed M _)
  | cons A ds ih =>
    intro ρ
    let D := Ed M (den M σ ρ A)
    let R := PiTypedCompile.leafIndex M σ b
    let C := fun a => tyv (classFiber D (fun q =>
      Ed M ((PiSyntaxCompile.compile M σ R ds
        (vcons (PiCompile.classValue D q) ρ)).erasedType M (fun i => i.1))) a)
    change Equiv (Ed M (piVal M (tyv D) C))
      (Ed M (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) (policyPi ds b))))
    apply ed_congr M
    refine piVal_ed_congr_on M (ed_tyv M (dich_ed M _))
      (fun _ _ h => ed_congr M (tyv_congr (classFiber_congr D _ h)))
      (fun _ _ h => ed_congr M (den_congr M σ (policyPi ds b)
        (vcons_congr (ρ := ρ) (ρ' := ρ) h (fun _ => Equiv.rfl)))) ?_
    intro a ha
    obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M (dich_ed M _)) ha
    let q := Quotient.mk (FSetoid D) i
    have ef := (classFiber_congr D (fun q =>
      Ed M ((PiSyntaxCompile.compile M σ R ds
        (vcons (PiCompile.classValue D q) ρ)).erasedType M (fun i => i.1)))
      hi.symm).trans (classFiber_at D _ i)
    exact ((ed_tyv M ((dich_congr ef).mpr (dich_ed M _))).trans ef).trans
      ((ih (vcons (PiCompile.classValue D q) ρ)).trans
        (ed_congr M (den_congr M σ (policyPi ds b)
          (vcons_congr ((PiCompile.classValue_at D i).trans hi) (fun _ => Equiv.rfl)))))

/-- Elementary composition of inhabited normalization and the structural
compiler. This does not supply an interpretation-independent signature. -/
theorem normalizedField_mem (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound M σ K E n)
    (hb : BodiesOK E σ K) (fuel : Nat) (T : Expr Nat)
    (ds : List (Expr Nat)) (b : Expr Nat) (ρ : Nat → PSet.{u}) (x : PSet.{u})
    (hw : piTelescopeFuel E fuel T = some (ds, b)) (hI : InstOK E σ K T)
    (hx : x ∈ Ed M (den M σ ρ T)) :
    (PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ b) ds ρ).DomainsDich ∧
      x ∈ Ed M ((PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ b) ds ρ).erasedType
        M (fun i => i.1)) := by
  refine ⟨PiSyntaxCompile.compile_domains M σ _ ds ρ, ?_⟩
  have he := den_piTelescope_of_mem M σ K hE hb fuel T ds b ρ x hw hI hx
  exact mem_congr_right ((syntaxCompile_ed M σ b ds ρ).trans (ed_congr M he)).symm hx

end Rcic.F3.PSet
