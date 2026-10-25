import rcic.RcicF3SemTel

/-!
# F3 S6-2a: arguments of type a proposition, read off a typing derivation

For ι at a `Prop` family with large elimination, the right-hand side applies
the minor premise to the constructor's fields, which are proofs, while the
recursor applies it to `∅`. The two agree:

- `spineFacts_of_hsound`: a hereditarily sound typing of an application spine
  gives, at each argument, a product holding the partial application whose
  domain holds the argument (`SpineFacts`);
- `spine_proofs`: if the head lies in a telescope of propositions
  (`PropTel`), its application to such arguments is its application to `∅`.
  A product whose domain is a proposition either is a proposition (both sides
  `∅`), or its members are functions on that domain, and a function lies in
  products over one domain only, so each argument lies in the proposition.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- At each argument, the partial application lies in a product whose domain
holds the argument. -/
def SpineFacts (M : Interp.{T}) : PSet.{T} → List PSet.{T} → Prop
  | _, [] => True
  | g, a :: as => (∃ (D : PSet.{T}) (C : PSet.{T} → PSet.{T}), (∀ x x', Equiv x x' → Equiv (C x) (C x')) ∧
      g ∈ Ed M (piVal M D C) ∧ a ∈ Ed M D) ∧ SpineFacts M (fapp g a) as

theorem SpineFacts.congr {M : Interp.{T}} : {g g' : PSet.{T}} → (as : List PSet.{T}) → Equiv g g' →
    SpineFacts M g as → SpineFacts M g' as
  | _, _, [], _, _ => trivial
  | _, _, _ :: as, e, ⟨⟨D, C, hC, hg, ha⟩, hs⟩ =>
      ⟨⟨D, C, hC, mem_congr_left e hg, ha⟩, SpineFacts.congr as (fapp_congr e Equiv.rfl) hs⟩

/-- The domains of a telescope are propositions, along `∅`. -/
def PropTel (M : Interp.{T}) (σ : Nat → Nat) : List (Expr Nat) → (Nat → PSet.{T}) → Prop
  | [], _ => True
  | F :: Fs, ρ => (∀ y, y ∈ Ed M (den M σ ρ F) → Equiv y pempty) ∧
      (pempty ∈ Ed M (den M σ ρ F) → PropTel M σ Fs (vcons pempty ρ))

theorem equiv_pempty_of_empty {g : PSet.{T}} (h : ∀ z, ¬ z ∈ g) : Equiv g pempty :=
  ext fun z => ⟨fun hz => (h z hz).elim, fun hz => (not_mem_pempty hz).elim⟩

theorem fapps_of_pempty {g : PSet.{T}} (h : Equiv g pempty) (as : List PSet.{T}) :
    Equiv (fapps g as) pempty :=
  (fapps_congr h as).trans (fapps_pempty as)

/-- A member of a product over an inhabited domain is not `∅`. -/
theorem piSet_ne_pempty {A g : PSet.{T}} {B : PSet.{T} → PSet.{T}} (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (hg : g ∈ piSet A B) {a : PSet.{T}} (ha : a ∈ A) : ¬ Equiv g pempty := fun h0 => by
  obtain ⟨b, _, hab⟩ := (isFuncOnDep_of_mem_piSet hB hg).1 a ha
  exact not_mem_pempty (mem_congr_right h0 hab)

/-- A member of two products holds in the second's domain what the first's holds. -/
theorem piSet_dom {A A' g : PSet.{T}} {B B' : PSet.{T} → PSet.{T}} (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (hB' : ∀ a a', Equiv a a' → Equiv (B' a) (B' a')) (hg : g ∈ piSet A B) (hg' : g ∈ piSet A' B')
    {a : PSet.{T}} (ha : a ∈ A') : a ∈ A := by
  obtain ⟨b, _, hab⟩ := (isFuncOnDep_of_mem_piSet hB' hg').1 a ha
  obtain ⟨a', ha', b', _, he⟩ := (isFuncOnDep_of_mem_piSet hB hg).2.1 _ hab
  exact mem_congr_left (ordPair_equiv he).1.symm ha'

/-- **Applying a member of a telescope of propositions**: at arguments a typing
derivation places in products, the application is the application to `∅`. -/
theorem spine_proofs (M : Interp.{T}) (σ : Nat → Nat) (b : Expr Nat) :
    (Fs : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → (g : PSet.{T}) → (as : List PSet.{T}) →
    as.length = Fs.length → g ∈ Ed M (den M σ ρ (policyPi Fs b)) → PropTel M σ Fs ρ → SpineFacts M g as →
    Equiv (fapps g as) (fapps g (as.map fun _ => pempty))
  | [], _, _, [], _, _, _, _ => Equiv.rfl
  | F :: Fs, ρ, g, a :: as, hl, hg, ⟨hP, hPt⟩, ⟨⟨D, C, hC, hgD, haD⟩, hsp⟩ => by
      have hB := den_resp M σ ρ (policyPi Fs b)
      have hg' := mem_congr_right (ed_piVal M _ _ hB) hg
      haveI := M.dec
      by_cases hpp : PiProp M (den M σ ρ F) (fun x => den M σ (vcons x ρ) (policyPi Fs b))
      · rw [cond_pos hpp] at hg'
        have h0 := (mem_tv.mp hg').2
        exact (fapps_of_pempty h0 _).trans (fapps_of_pempty h0 _).symm
      · rw [cond_neg hpp] at hg'
        have hBE : ∀ x x', Equiv x x' → Equiv (Ed M (den M σ (vcons x ρ) (policyPi Fs b)))
            (Ed M (den M σ (vcons x' ρ) (policyPi Fs b))) := fun x x' e => ed_congr M (hB x x' e)
        by_cases hin : pempty ∈ Ed M (den M σ ρ F)
        · -- the argument lies in the proposition
          have haF : a ∈ Ed M (den M σ ρ F) := by
            have hgD' := mem_congr_right (ed_piVal M _ _ hC) hgD
            by_cases hpD : PiProp M D C
            · rw [cond_pos hpD] at hgD'
              exact absurd (mem_tv.mp hgD').2 (piSet_ne_pempty hBE hg' hin)
            · rw [cond_neg hpD] at hgD'
              exact piSet_dom hBE (fun x x' e => ed_congr M (hC x x' e)) hg' hgD' haD
          have ha0 := hP a haF
          have hg1 : fapp g pempty ∈ Ed M (den M σ (vcons pempty ρ) (policyPi Fs b)) :=
            fapp_mem_piSet hBE hg' hin
          have ih := spine_proofs M σ b Fs (vcons pempty ρ) (fapp g pempty) as (Nat.succ.inj hl) hg1 (hPt hin)
            (SpineFacts.congr as (fapp_congr Equiv.rfl ha0) hsp)
          exact (fapps_congr (fapp_congr Equiv.rfl ha0) as).trans ih
        · -- the proposition is empty, and so is the function
          have hempty : ∀ z, ¬ z ∈ g := fun z hz => by
            obtain ⟨a', ha', _, _, _⟩ := (isFuncOnDep_of_mem_piSet hBE hg').2.1 z hz
            exact hin (mem_congr_left (hP a' ha') ha')
          have h0 := equiv_pempty_of_empty hempty
          exact (fapps_of_pempty h0 _).trans (fapps_of_pempty h0 _).symm

/-- Lifting a telescope of propositions past `ys` keeps it one. -/
theorem propTel_liftFields (M : Interp.{T}) (σ : Nat → Nat) (ys : List PSet.{T}) (R : Nat → PSet.{T}) :
    (Ds : List (Expr Nat)) → (zs : List PSet.{T}) →
    PropTel M σ Ds (push zs R) → PropTel M σ (liftFields ys.length Ds zs.length) (push zs (push ys R))
  | [], _, _ => trivial
  | A :: Ds, zs, ⟨hA, hDs⟩ => by
      have e : den M σ (push zs (push ys R)) (Rcic.Declarative.lift zs.length ys.length A) =
          den M σ (push zs R) A := den_lift_push M σ zs ys R A
      have h1 : vcons pempty (push zs (push ys R)) = push (zs ++ [pempty]) (push ys R) := by rw [push_append]; rfl
      have h2 : vcons pempty (push zs R) = push (zs ++ [pempty]) R := by rw [push_append]; rfl
      have hl : zs.length + 1 = (zs ++ [pempty]).length := by simp
      refine ⟨fun y hy => hA y (by rw [← e]; exact hy), fun hin => ?_⟩
      show PropTel M σ (liftFields ys.length Ds (zs.length + 1)) (vcons pempty (push zs (push ys R)))
      rw [h1, hl]
      refine propTel_liftFields M σ ys R Ds (zs ++ [pempty]) ?_
      rw [← h2]
      exact hDs (by rw [← e]; exact hin)

/-- Values fitting a telescope of propositions are `∅`. -/
theorem propTel_fits (M : Interp.{T}) (σ : Nat → Nat) : (Fs : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    (xs : List PSet.{T}) → PropTel M σ Fs ρ → TelFits M σ Fs ρ xs → LEq xs (xs.map fun _ => pempty)
  | [], _, [], _, _ => trivial
  | F :: Fs, ρ, x :: xs, ⟨hP, hPt⟩, ⟨hx, hxs⟩ => by
      have h0 := hP x hx
      have hin : pempty ∈ Ed M (den M σ ρ F) := mem_congr_left h0 hx
      have hxs' : TelFits M σ Fs (vcons pempty ρ) xs :=
        TelFits_congr M σ Fs (vcons_congr h0 (fun _ => Equiv.rfl)) (LEq.refl xs) hxs
      exact ⟨h0, propTel_fits M σ Fs (vcons pempty ρ) xs (hPt hin) hxs'⟩

/-- With no field revealed in the result indices, the reconstruction is `∅` throughout. -/
theorem recon_none (c : List (Expr Nat) × List (Expr Nat)) (is : List PSet.{T})
    (hn : ∀ k, k < c.1.length → posOf (.bvar (c.1.length - 1 - k)) c.2 = none) :
    recon c is = c.1.map fun _ => pempty := by
  apply List.ext_getElem
  · simp [recon]
  · intro k h1 _
    simp only [recon, List.getElem_map, List.getElem_range]
    have hk : k < c.1.length := by simpa [recon] using h1
    unfold reconField
    rw [hn k hk]

/-! ### reading the facts off a derivation -/

variable {E : ResolvedEnv} {n : Nat}

theorem hsound_app_inv_aux (M : Interp.{T}) (σ : Nat → Nat) {Γ : LCtx} {f a : Expr Nat} :
    {e T' : Expr Nat} → (h : HasTyT E n Γ e T') → HSoundT M σ h → e = .app f a →
    ∃ (A B : Expr Nat) (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A), HSoundT M σ hf ∧ HSoundT M σ ha
  | _, _, .app _ _ _ A B hf ha, hs, he => by
      injection he with h1 h2
      subst h1; subst h2
      exact ⟨A, B, hf, ha, hs.2.1, hs.2.2⟩
  | _, _, .conv _ _ _ _ _ h1 _, hs, he => hsound_app_inv_aux M σ h1 hs.2.1 he
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

theorem hsound_app_inv (M : Interp.{T}) (σ : Nat → Nat) {Γ : LCtx} {f a T : Expr Nat}
    (h : HasTyT E n Γ (.app f a) T) (hs : HSoundT M σ h) :
    ∃ (A B : Expr Nat) (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A), HSoundT M σ hf ∧ HSoundT M σ ha :=
  hsound_app_inv_aux M σ h hs rfl

/-- The head of a typed spine is typed. -/
theorem hsound_head (M : Interp.{T}) (σ : Nat → Nat) {Γ : LCtx} : (as : List (Expr Nat)) → (hd : Expr Nat) →
    {T : Expr Nat} → (h : HasTyT E n Γ (foldApps hd as) T) → HSoundT M σ h →
    ∃ (T' : Expr Nat) (h' : HasTyT E n Γ hd T'), HSoundT M σ h'
  | [], _, T, h, hs => ⟨T, h, hs⟩
  | a :: as, hd, _, h, hs => by
      obtain ⟨T', h', hs'⟩ := hsound_head M σ as (.app hd a) h hs
      obtain ⟨A, B, hf, _, hfs, _⟩ := hsound_app_inv M σ h' hs'
      exact ⟨_, hf, hfs⟩

/-- **The facts along a typed spine.** -/
theorem spineFacts_of_hsound (M : Interp.{T}) (σ : Nat → Nat) {Γ : LCtx} (ρ : Nat → PSet.{T})
    (hfit : Fits M σ Γ ρ) : (as : List (Expr Nat)) → (hd : Expr Nat) → {T : Expr Nat} →
    (h : HasTyT E n Γ (foldApps hd as) T) → HSoundT M σ h →
    SpineFacts M (den M σ ρ hd) (as.map (den M σ ρ))
  | [], _, _, _, _ => trivial
  | a :: as, hd, _, h, hs => by
      obtain ⟨T', h', hs'⟩ := hsound_head M σ as (.app hd a) h hs
      obtain ⟨A, B, hf, ha, hfs, has⟩ := hsound_app_inv M σ h' hs'
      exact ⟨⟨den M σ ρ A, fun x => den M σ (vcons x ρ) B, den_resp M σ ρ B, hfs.root ρ hfit, has.root ρ hfit⟩,
        spineFacts_of_hsound M σ ρ hfit as (.app hd a) h hs⟩

/-! ### the level bound at a spine's head -/

theorem lok_app_inv_aux (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) {Γ : LCtx} {f a : Expr Nat} :
    {e T' : Expr Nat} → (h : HasTyT E n Γ e T') → LOKt σ N K h → e = .app f a →
    ∃ (A B : Expr Nat) (hf : HasTyT E n Γ f (.pi A B)), LOKt σ N K hf
  | _, _, .app _ _ _ A B hf _, hl, he => by
      injection he with h1 h2
      subst h1; subst h2
      exact ⟨A, B, hf, hl.1⟩
  | _, _, .conv _ _ _ _ _ h1 _, hl, he => lok_app_inv_aux σ N K h1 hl.1 he
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

theorem lok_head (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) {Γ : LCtx} : (as : List (Expr Nat)) → (hd : Expr Nat) →
    {T : Expr Nat} → (h : HasTyT E n Γ (foldApps hd as) T) → LOKt σ N K h →
    ∃ (T' : Expr Nat) (h' : HasTyT E n Γ hd T'), LOKt σ N K h'
  | [], _, T, h, hl => ⟨T, h, hl⟩
  | a :: as, hd, _, h, hl => by
      obtain ⟨T', h', hl'⟩ := lok_head σ N K as (.app hd a) h hl
      obtain ⟨A, B, hf, hfl⟩ := lok_app_inv_aux σ N K h' hl' rfl
      exact ⟨_, hf, hfl⟩

theorem lok_const_aux (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) {Γ : LCtx} {r : Nat} {ls : List Level} :
    {e T' : Expr Nat} → (h : HasTyT E n Γ e T') → LOKt σ N K h → e = .const r ls → LevelsOK σ (K r) ls
  | _, _, .const _ _ _ _ _ _ _, hl, he => by
      injection he with h1 h2
      subst h1; subst h2
      exact hl
  | _, _, .conv _ _ _ _ _ h1 _, hl, he => lok_const_aux σ N K h1 hl.1 he
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .app _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

/-- The level bound of a typed spine headed by a constant bounds the constant's levels. -/
theorem lok_spine_const (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) {Γ : LCtx} (r : Nat) (ls : List Level)
    (as : List (Expr Nat)) {T : Expr Nat} (h : HasTyT E n Γ (foldApps (.const r ls) as) T) (hl : LOKt σ N K h) :
    LevelsOK σ (K r) ls := by
  obtain ⟨_, h', hl'⟩ := lok_head σ N K as _ h hl
  exact lok_const_aux σ N K h' hl' rfl

end PSet

end Rcic.F3
