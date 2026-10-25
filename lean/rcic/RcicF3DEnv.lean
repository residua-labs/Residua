import rcic.RcicF3DTransfer
import rcic.RcicF3MainG
import rcic.RcicTypedLevels

/-!
# F3 D-4: environment facts for normalization

What the group step must know about the environments a δ-hidden field is
read in:

- `transparent_bodies_of_envWfT`: in an admitted environment whose stored
  derivations respect the instance bound `K` (`BoundG`), every transparent
  body is level-closed and its constant instances are within `K`;
- `bodiesOK_of_envWfT`: hence `BodiesOK` (the δ side condition of
  `den_whnf`) holds in every extension of the environment by body-less members
  (the family, the constructors), at every level valuation;
- `transparentBody_eq_base`: such extensions have the base's transparent
  bodies, so admission's normalization (in the recursor's environment) and a
  constructor's walk environment agree (`whnfFuel_congr_env`);
- `envClosed_of_typeFacts`: closed members (`EnvClosed`) from `TypeFacts`;
- `whnfFuel_levelsBounded`: normalization preserves level bounds.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve denRefs denRefsLit)

namespace PSet

/-! ### constant instances and environments -/

theorem InstOK.mono_env {E₁ E₂ : ResolvedEnv} {σ : Nat → Nat} {K : Nat → Nat} {e : Expr Nat}
    (hsub : ∀ r m, E₁.members r = some m → E₂.members r = some m) (h : InstOK E₁ σ K e) : InstOK E₂ σ K e := by
  intro r ls hm
  obtain ⟨m, hres, hlen, hl⟩ := h r ls hm
  exact ⟨m, hsub r m hres, hlen, hl⟩

/-- The member behind a transparent body. -/
theorem transparentBody_some {E : ResolvedEnv} {r : Nat} {ls : List Level} {body : Expr Nat}
    (h : transparentBody E r ls = some body) :
    ∃ m b, E.members r = some m ∧ transparent m.mclass = true ∧ m.body = some b ∧ body = instantiateLevels ls b := by
  unfold transparentBody at h
  cases hm : E.members r with
  | none => rw [hm] at h; cases h
  | some m =>
      rw [hm] at h
      simp only at h
      by_cases htr : transparent m.mclass = true
      · rw [if_pos htr] at h
        cases hb : m.body with
        | none => rw [hb] at h; cases h
        | some b0 =>
            rw [hb] at h
            exact ⟨m, b0, rfl, htr, hb, (Option.some.inj h).symm⟩
      · rw [if_neg htr] at h; cases h

/-- **Transparent bodies of an admitted environment within the bound**: level-closed,
with constant instances within `K`. -/
theorem transparent_bodies_of_envWfT (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) → BoundG K hW →
    ∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true ∧ InstOK E (fun _ => 0) K b
  | _, .empty, _, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE hfresh _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨h1, h2⟩ := transparent_bodies_of_envWfT K hE hB r m b h hb htr
        exact ⟨h1, h2.mono_env fun r' m' h' => members_extend_preserved hfresh r' m' h'⟩
  | _, .definition E r0 _ v _ hE hfresh _ hv _ _ _ hlvlv, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
        exact ⟨hlvlv, (instOK_of_lokt (fun _ => 0) 4 K hv hB.2).mono_env
          fun r' m' h' => members_extend_preserved hfresh r' m' h'⟩
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨h1, h2⟩ := transparent_bodies_of_envWfT K hE hB.1 r m b h hb htr
        exact ⟨h1, h2.mono_env fun r' m' h' => members_extend_preserved hfresh r' m' h'⟩
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨h1, h2⟩ := transparent_bodies_of_envWfT K hE hB.1 r m b h hb htr
        exact ⟨h1, h2.mono_env fun r' m' h' => members_extend_preserved hfresh r' m' h'⟩
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨h1, h2⟩ := transparent_bodies_of_envWfT K hE hB.1 r m b h hb htr
        exact ⟨h1, h2.mono_env fun r' m' h' => members_extend_preserved hfresh r' m' h'⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, hB, r, m, b, h, hb, htr => by
      rcases groupMembersT_cases hmem r m h with h1 | h1
      · obtain ⟨h1', h2⟩ := transparent_bodies_of_envWfT K hE hB.1 r m b h1 hb htr
        exact ⟨h1', h2.mono_env fun r' m' h' => groupMembersT_preserve hmem r' m' h'⟩
      · rw [groupMembersT_body_none hmem r m h1] at hb
        cases hb

/-- **`BodiesOK` in every extension of an admitted environment by body-less
members**, at every level valuation. -/
theorem bodiesOK_of_envWfT (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hB : BoundG K hW) {E₁ : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none) (σ : Nat → Nat) :
    BodiesOK E₁ σ K := by
  intro r m b ls hm hb htr _ _
  cases h1 : E.members r with
  | none =>
      rw [hnew r m hm h1] at hb
      cases hb
  | some m' =>
      have h2 := hsub r m' h1
      rw [hm] at h2
      cases h2
      obtain ⟨hb0, hI⟩ := transparent_bodies_of_envWfT K hW hB r m b h1 hb htr
      exact (instOK_closed_inst (fun _ => 0) σ K hb0 hI ls).mono_env hsub

/-! ### the transparent bodies along a group -/

/-- An environment between a group's base and its final environment has the
base's transparent bodies: the group's members have none. -/
theorem transparentBody_eq_base {S E E' Ex : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') (hsub : ∀ r m, E.members r = some m → Ex.members r = some m)
    (hsub' : ∀ r m, Ex.members r = some m → E'.members r = some m) (r : Nat) (ls : List Level) :
    transparentBody E r ls = transparentBody Ex r ls :=
  transparentBody_eq_of_sub hsub (fun r m hm h0 => by
    rcases groupMembersT_cases hmem r m (hsub' r m hm) with h1 | h1
    · rw [h1] at h0; cases h0
    · exact groupMembersT_body_none hmem r m h1) r ls

/-- Two environments between a group's base and its final environment normalize alike. -/
theorem whnfFuel_eq_along {S E E' E₁ E₂ : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E')
    (hsub₁ : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hsub₁' : ∀ r m, E₁.members r = some m → E'.members r = some m)
    (hsub₂ : ∀ r m, E.members r = some m → E₂.members r = some m)
    (hsub₂' : ∀ r m, E₂.members r = some m → E'.members r = some m) (fuel : Nat) (e : Expr Nat) :
    whnfFuel E₁ fuel e = whnfFuel E₂ fuel e :=
  whnfFuel_congr_env (fun r ls =>
    (transparentBody_eq_base hmem hsub₁ hsub₁' r ls).symm.trans (transparentBody_eq_base hmem hsub₂ hsub₂' r ls))
    fuel e


/-! ### closed members -/

theorem envClosed_of_typeFacts {E : ResolvedEnv} (h : TypeFacts E) : EnvClosed E :=
  fun r m hm => ⟨(h r m hm).1, fun b hb => ((h r m hm).2.2 b hb).1⟩

theorem typeFacts_sub {E E' : ResolvedEnv} (hsub : ∀ r m, E.members r = some m → E'.members r = some m)
    (h : TypeFacts E') : TypeFacts E :=
  fun r m hm => h r m (hsub r m hm)

/-! ### level bounds through normalization -/

/-- Normalization preserves level bounds, when every transparent body is level-closed. -/
theorem whnfFuel_levelsBounded {E : ResolvedEnv}
    (hb0 : ∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true) {k : Nat} :
    (fuel : Nat) → (e w : Expr Nat) → exprLevelsBounded k e = true → whnfFuel E fuel e = some w →
      exprLevelsBounded k w = true
  | 0, _, _, _, h => by cases h
  | fuel + 1, e, w, hb, h => by
      have he : foldApps (appsSpine e).1 (appsSpine e).2 = e := foldApps_appsSpine e
      cases hs : appsSpine e with
      | mk hd args =>
        rw [hs] at he
        simp only at he
        have hb' : exprLevelsBounded k (foldApps hd args) = true := by rw [he]; exact hb
        obtain ⟨hhd, hargs⟩ := levelsBounded_foldApps k hd args hb'
        cases hd with
        | lam A b =>
            cases args with
            | nil =>
                simp only [whnfFuel, hs] at h
                cases h
                exact hb
            | cons a args =>
                simp only [whnfFuel, hs] at h
                have hbb : exprLevelsBounded k b = true := by
                  simp only [exprLevelsBounded, Bool.and_eq_true] at hhd
                  exact hhd.2
                refine whnfFuel_levelsBounded hb0 fuel _ w ?_ h
                exact exprLevelsBounded_foldApps _ _
                  (exprLevelsBounded_instantiate0 (hargs a (List.mem_cons_self _ _)) hbb)
                  (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
        | letE A v b =>
            simp only [whnfFuel, hs] at h
            have hvb : exprLevelsBounded k v = true ∧ exprLevelsBounded k b = true := by
              simp only [exprLevelsBounded, Bool.and_eq_true] at hhd
              exact ⟨hhd.1.2, hhd.2⟩
            refine whnfFuel_levelsBounded hb0 fuel _ w ?_ h
            exact exprLevelsBounded_foldApps _ _ (exprLevelsBounded_instantiate0 hvb.1 hvb.2) hargs
        | const r ls =>
            cases ht : transparentBody E r ls with
            | none =>
                simp only [whnfFuel, hs, ht] at h
                cases h
                exact hb
            | some body =>
                simp only [whnfFuel, hs, ht] at h
                obtain ⟨m, b, hres, htr, hmb, rfl⟩ := transparentBody_some ht
                have hb0' := hb0 r m b hres hmb htr
                have hbb : exprLevelsBounded k (instantiateLevels ls b) = true := by
                  rw [Rcic.Declarative.Ann.instantiateLevels_closed ls b hb0']
                  exact exprLevelsBounded_mono (Nat.zero_le k) b hb0'
                exact whnfFuel_levelsBounded hb0 fuel _ w (exprLevelsBounded_foldApps _ _ hbb hargs) h
        | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact hb
        | sort _ => simp only [whnfFuel, hs] at h; cases h; exact hb
        | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact hb
        | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact hb
        | lit _ => simp only [whnfFuel, hs] at h; cases h; exact hb

/-! ### the references normalization reads -/

theorem denRefs_lift (c s : Nat) : (e : Expr Nat) → denRefs (Rcic.Declarative.lift c s e) = denRefs e
  | .bvar i => by
      simp only [Rcic.Declarative.lift]
      split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a => by
      show denRefs (Rcic.Declarative.lift c s f) ++ denRefs (Rcic.Declarative.lift c s a) = _
      rw [denRefs_lift c s f, denRefs_lift c s a]; rfl
  | .lam A b => by
      show denRefs (Rcic.Declarative.lift c s A) ++ denRefs (Rcic.Declarative.lift (c + 1) s b) = _
      rw [denRefs_lift c s A, denRefs_lift (c + 1) s b]; rfl
  | .pi A B => by
      show denRefs (Rcic.Declarative.lift c s A) ++ denRefs (Rcic.Declarative.lift (c + 1) s B) = _
      rw [denRefs_lift c s A, denRefs_lift (c + 1) s B]; rfl
  | .letE A v b => by
      show denRefs (Rcic.Declarative.lift c s A) ++ denRefs (Rcic.Declarative.lift c s v) ++
        denRefs (Rcic.Declarative.lift (c + 1) s b) = _
      rw [denRefs_lift c s A, denRefs_lift c s v, denRefs_lift (c + 1) s b]; rfl
  | .lit _ => rfl

theorem denRefs_instantiate (j : Nat) (v : Expr Nat) : (e : Expr Nat) → ∀ r,
    r ∈ denRefs (instantiate j v e) → r ∈ denRefs v ∨ r ∈ denRefs e
  | .bvar i, r, h => by
      simp only [instantiate] at h
      split at h
      · exact Or.inl h
      · split at h <;> exact absurd h (List.not_mem_nil _)
  | .sort _, _, h => absurd h (List.not_mem_nil _)
  | .const _ _, _, h => Or.inr h
  | .lit _, _, h => Or.inr h
  | .app f a, r, h => by
      rcases List.mem_append.mp (show r ∈ denRefs (instantiate j v f) ++ denRefs (instantiate j v a) from h) with h | h
      · rcases denRefs_instantiate j v f r h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · rcases denRefs_instantiate j v a r h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .lam A b, r, h => by
      rcases List.mem_append.mp (show r ∈ denRefs (instantiate j v A) ++
          denRefs (instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) b) from h) with h | h
      · rcases denRefs_instantiate j v A r h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · rcases denRefs_instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) b r h with h | h
        · rw [denRefs_lift] at h
          exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .pi A B, r, h => by
      rcases List.mem_append.mp (show r ∈ denRefs (instantiate j v A) ++
          denRefs (instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) B) from h) with h | h
      · rcases denRefs_instantiate j v A r h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · rcases denRefs_instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) B r h with h | h
        · rw [denRefs_lift] at h
          exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .letE A w b, r, h => by
      rcases List.mem_append.mp (show r ∈ denRefs (instantiate j v A) ++ denRefs (instantiate j v w) ++
          denRefs (instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) b) from h) with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases denRefs_instantiate j v A r h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ (List.mem_append_left _ h))
        · rcases denRefs_instantiate j v w r h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ h))
      · rcases denRefs_instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) b r h with h | h
        · rw [denRefs_lift] at h
          exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)

theorem denRefs_foldApps_mem : (f : Expr Nat) → (as : List (Expr Nat)) → ∀ r,
    r ∈ denRefs (foldApps f as) ↔ r ∈ denRefs f ∨ ∃ a, a ∈ as ∧ r ∈ denRefs a
  | _, [], r => ⟨fun h => Or.inl h, fun h => by
      rcases h with h | ⟨a, ha, _⟩
      · exact h
      · exact absurd ha (List.not_mem_nil _)⟩
  | f, a :: as, r => by
      show r ∈ denRefs (foldApps (.app f a) as) ↔ _
      rw [denRefs_foldApps_mem (.app f a) as r]
      constructor
      · rintro (h | ⟨b, hb, hr⟩)
        · rcases List.mem_append.mp (show r ∈ denRefs f ++ denRefs a from h) with h | h
          · exact Or.inl h
          · exact Or.inr ⟨a, List.mem_cons_self _ _, h⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hr⟩
      · rintro (h | ⟨b, hb, hr⟩)
        · exact Or.inl (List.mem_append_left _ h)
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact Or.inl (List.mem_append_right _ hr)
          · exact Or.inr ⟨b, hb, hr⟩

/-- Normalization reads the term's references and the unfolded bodies'. -/
theorem denRefs_whnf {E : ResolvedEnv} {S : Nat → Prop}
    (hbodies : ∀ r m b ls, E.members r = some m → m.body = some b → transparent m.mclass = true →
      ∀ r', r' ∈ denRefs (instantiateLevels ls b) → S r') :
    (fuel : Nat) → (e w : Expr Nat) → whnfFuel E fuel e = some w → ∀ r, r ∈ denRefs w → r ∈ denRefs e ∨ S r
  | 0, _, _, h, _, _ => by cases h
  | fuel + 1, e, w, h, r, hr => by
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
                exact Or.inl hr
            | cons a args =>
                simp only [whnfFuel, hs] at h
                rcases denRefs_whnf hbodies fuel _ w h r hr with hr' | hS
                · left
                  rw [← he]
                  rcases (denRefs_foldApps_mem _ _ r).mp hr' with h1 | ⟨c, hc, h1⟩
                  · rcases denRefs_instantiate 0 a b r h1 with h2 | h2
                    · exact (denRefs_foldApps_mem _ _ r).mpr (Or.inr ⟨a, List.mem_cons_self _ _, h2⟩)
                    · exact (denRefs_foldApps_mem _ _ r).mpr (Or.inl (List.mem_append_right _ h2))
                  · exact (denRefs_foldApps_mem _ _ r).mpr (Or.inr ⟨c, List.mem_cons_of_mem _ hc, h1⟩)
                · exact Or.inr hS
        | letE A v b =>
            simp only [whnfFuel, hs] at h
            rcases denRefs_whnf hbodies fuel _ w h r hr with hr' | hS
            · left
              rw [← he]
              rcases (denRefs_foldApps_mem _ _ r).mp hr' with h1 | ⟨c, hc, h1⟩
              · rcases denRefs_instantiate 0 v b r h1 with h2 | h2
                · exact (denRefs_foldApps_mem _ _ r).mpr
                    (Or.inl (List.mem_append_left _ (List.mem_append_right _ h2)))
                · exact (denRefs_foldApps_mem _ _ r).mpr (Or.inl (List.mem_append_right _ h2))
              · exact (denRefs_foldApps_mem _ _ r).mpr (Or.inr ⟨c, hc, h1⟩)
            · exact Or.inr hS
        | const r0 ls =>
            cases ht : transparentBody E r0 ls with
            | none =>
                simp only [whnfFuel, hs, ht] at h
                cases h
                exact Or.inl hr
            | some body =>
                simp only [whnfFuel, hs, ht] at h
                obtain ⟨m, b, hres, htr, hmb, rfl⟩ := transparentBody_some ht
                rcases denRefs_whnf hbodies fuel _ w h r hr with hr' | hS
                · rcases (denRefs_foldApps_mem _ _ r).mp hr' with h1 | ⟨c, hc, h1⟩
                  · exact Or.inr (hbodies r0 m b ls hres hmb htr r h1)
                  · left
                    rw [← he]
                    exact (denRefs_foldApps_mem _ _ r).mpr (Or.inr ⟨c, hc, h1⟩)
                · exact Or.inr hS
        | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact Or.inl hr
        | sort _ => simp only [whnfFuel, hs] at h; cases h; exact Or.inl hr
        | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact Or.inl hr
        | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact Or.inl hr
        | lit _ => simp only [whnfFuel, hs] at h; cases h; exact Or.inl hr

end PSet

end Rcic.F3
