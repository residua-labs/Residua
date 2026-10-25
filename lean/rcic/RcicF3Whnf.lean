import rcic.RcicF3Fund
import rcic.RcicF3Env
import rcic.RcicF3EnvSound
import rcic.RcicIotaLegacyShapes
import rcic.RcicSynObsLevels
import rcic.RcicSynSRLitPiInv

/-!
# F3 D-1: weak-head normalization preserves non-empty denotations

Admission reads a constructor field through `whnfFuel`, which performs
untyped β, ζ and δ at transparent heads. The denotation `den` is not
invariant under untyped β: `fapp (lamVal M A g) x` is `∅` when `x ∉ Ed M A`.
It is invariant on **non-empty** denotations:

- β: a non-`∅` value of `fapp (lamVal M A g) x` forces `x ∈ Ed M A`
  (`mem_of_fapp_lamVal_ne`), where β holds in the model (`beta_val`);
- ζ: a `letE` denotes its body at the pushed value (`den_inst0`);
- δ: a transparent constant denotes its body at the instance
  (`EnvSound.delta`), for a member instance within the bound (`InstOK`).

`den_whnf`: if `den M σ ρ e ≉ ∅`, every constant instance of `e` is a
member instance within the bound, and `whnfFuel E fuel e = some e'`, then
`den M σ ρ e' ≈ den M σ ρ e`. Typing enters only once, at the root:
`den_whnf_typed` reads `den M σ ρ A ∈ U l` off a sound typing `A : sort l`
(no universe contains `∅`), so a typed type and its weak-head normal form
denote the same value. No Π-injectivity, and no typing of the intermediate
terms, is used. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-! ### constant instances -/

/-- The constant instances `(r, ls)` of an expression. -/
def constInsts : Expr Nat → List (Nat × List Level)
  | .bvar _ => []
  | .sort _ => []
  | .const r ls => [(r, ls)]
  | .app f a => constInsts f ++ constInsts a
  | .lam A b => constInsts A ++ constInsts b
  | .pi A B => constInsts A ++ constInsts B
  | .letE A v b => constInsts A ++ constInsts v ++ constInsts b
  | .lit _ => []

theorem constInsts_lift (c s : Nat) : (e : Expr Nat) →
    constInsts (Rcic.Declarative.lift c s e) = constInsts e
  | .bvar i => by
      simp only [Rcic.Declarative.lift]
      split <;> rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a => by
      simp only [Rcic.Declarative.lift, constInsts, constInsts_lift c s f, constInsts_lift c s a]
  | .lam A b => by
      simp only [Rcic.Declarative.lift, constInsts, constInsts_lift c s A, constInsts_lift (c + 1) s b]
  | .pi A B => by
      simp only [Rcic.Declarative.lift, constInsts, constInsts_lift c s A, constInsts_lift (c + 1) s B]
  | .letE A v b => by
      simp only [Rcic.Declarative.lift, constInsts, constInsts_lift c s A, constInsts_lift c s v,
        constInsts_lift (c + 1) s b]
  | .lit _ => rfl

/-- The instances of a substitution instance come from the replacement or the body. -/
theorem constInsts_instantiate (j : Nat) (v : Expr Nat) : (e : Expr Nat) → ∀ p,
    p ∈ constInsts (instantiate j v e) → p ∈ constInsts v ∨ p ∈ constInsts e
  | .bvar i, p, h => by
      simp only [instantiate] at h
      split at h
      · exact Or.inl h
      · split at h <;> exact absurd h (List.not_mem_nil _)
  | .sort _, _, h => absurd h (List.not_mem_nil _)
  | .const _ _, _, h => Or.inr h
  | .app f a, p, h => by
      simp only [instantiate, constInsts] at h
      rcases List.mem_append.mp h with h | h
      · rcases constInsts_instantiate j v f p h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · rcases constInsts_instantiate j v a p h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .lam A b, p, h => by
      simp only [instantiate, constInsts] at h
      rcases List.mem_append.mp h with h | h
      · rcases constInsts_instantiate j v A p h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · rcases constInsts_instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) b p h with h | h
        · rw [constInsts_lift] at h
          exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .pi A B, p, h => by
      simp only [instantiate, constInsts] at h
      rcases List.mem_append.mp h with h | h
      · rcases constInsts_instantiate j v A p h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · rcases constInsts_instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) B p h with h | h
        · rw [constInsts_lift] at h
          exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .letE A w b, p, h => by
      simp only [instantiate, constInsts] at h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases constInsts_instantiate j v A p h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ (List.mem_append_left _ h))
        · rcases constInsts_instantiate j v w p h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ h))
      · rcases constInsts_instantiate (j + 1) (Rcic.Declarative.lift 0 1 v) b p h with h | h
        · rw [constInsts_lift] at h
          exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
  | .lit _, _, h => absurd h (List.not_mem_nil _)

/-- The instances of an application spine: the head's and the arguments'. -/
theorem constInsts_foldApps : (f : Expr Nat) → (as : List (Expr Nat)) → ∀ p,
    p ∈ constInsts (foldApps f as) ↔ p ∈ constInsts f ∨ ∃ a, a ∈ as ∧ p ∈ constInsts a
  | _, [], p => ⟨fun h => Or.inl h, fun h => by
      rcases h with h | ⟨a, ha, _⟩
      · exact h
      · exact absurd ha (List.not_mem_nil _)⟩
  | f, a :: as, p => by
      show p ∈ constInsts (foldApps (.app f a) as) ↔ _
      rw [constInsts_foldApps (.app f a) as p]
      constructor
      · rintro (h | ⟨b, hb, hp⟩)
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨a, List.mem_cons_self _ _, h⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hp⟩
      · rintro (h | ⟨b, hb, hp⟩)
        · exact Or.inl (List.mem_append_left _ h)
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact Or.inl (List.mem_append_right _ hp)
          · exact Or.inr ⟨b, hb, hp⟩

/-- Every constant instance of `e` is a member instance within the bound `K`. -/
def InstOK (E : ResolvedEnv) (σ : Nat → Nat) (K : Nat → Nat) (e : Expr Nat) : Prop :=
  ∀ r ls, (r, ls) ∈ constInsts e →
    ∃ m, E.members r = some m ∧ ls.length = m.arity ∧ LevelsOK σ (K r) ls

theorem InstOK.sub {E : ResolvedEnv} {σ : Nat → Nat} {K : Nat → Nat} {e e' : Expr Nat}
    (hsub : ∀ p, p ∈ constInsts e' → p ∈ constInsts e) (h : InstOK E σ K e) : InstOK E σ K e' :=
  fun r ls hm => h r ls (hsub _ hm)

/-- The instances of a typed term are within the derivation's bound. -/
theorem instOK_of_lokt {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → {e A : Expr Nat} → (h : HasTyT E n Γ e A) → LOKt σ N K h → InstOK E σ K e
  | _, _, _, .sort _ _, _ => fun _ _ h => absurd h (List.not_mem_nil _)
  | _, _, _, .bvar _ _ _ _, _ => fun _ _ h => absurd h (List.not_mem_nil _)
  | _, _, _, .const _ r ls m hres hlen _, hl => fun r' ls' h => by
      have h' : (r', ls') = (r, ls) := List.mem_singleton.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
      exact ⟨m, hres, hlen, hl⟩
  | _, _, _, .pi _ _ _ _ _ hA hB, hl => fun r ls h => by
      obtain ⟨_, _, lA, lB⟩ := hl
      rcases List.mem_append.mp h with h | h
      · exact instOK_of_lokt σ N K hA lA r ls h
      · exact instOK_of_lokt σ N K hB lB r ls h
  | _, _, _, .lam _ _ _ _ _ hA hbody, hl => fun r ls h => by
      obtain ⟨lA, lb⟩ := hl
      rcases List.mem_append.mp h with h | h
      · exact instOK_of_lokt σ N K hA lA r ls h
      · exact instOK_of_lokt σ N K hbody lb r ls h
  | _, _, _, .app _ _ _ _ _ hf ha, hl => fun r ls h => by
      obtain ⟨lf, la⟩ := hl
      rcases List.mem_append.mp h with h | h
      · exact instOK_of_lokt σ N K hf lf r ls h
      · exact instOK_of_lokt σ N K ha la r ls h
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, hl => fun r ls h => by
      obtain ⟨lA, lv, lb⟩ := hl
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact instOK_of_lokt σ N K hA lA r ls h
        · exact instOK_of_lokt σ N K hv lv r ls h
      · exact instOK_of_lokt σ N K hb lb r ls h
  | _, _, _, .lit _ _ _ _, _ => fun _ _ h => absurd h (List.not_mem_nil _)
  | _, _, _, .conv _ _ _ _ _ h _, hl => fun r ls hm => by
      obtain ⟨l, _⟩ := hl
      exact instOK_of_lokt σ N K h l r ls hm

/-! ### level-closed bodies -/


/-- The instances of a level-bounded expression are level-bounded. -/
theorem constInsts_levelsBounded {k : Nat} : (e : Expr Nat) → exprLevelsBounded k e = true →
    ∀ r ls, (r, ls) ∈ constInsts e → levelsBounded k ls = true
  | .bvar _, _, _, _, h => absurd h (List.not_mem_nil _)
  | .sort _, _, _, _, h => absurd h (List.not_mem_nil _)
  | .const _ _, hb, _, _, h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
      exact hb
  | .app f a, hb, r, ls, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      rcases List.mem_append.mp h with h | h
      · exact constInsts_levelsBounded f hb.1 r ls h
      · exact constInsts_levelsBounded a hb.2 r ls h
  | .lam A b, hb, r, ls, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      rcases List.mem_append.mp h with h | h
      · exact constInsts_levelsBounded A hb.1 r ls h
      · exact constInsts_levelsBounded b hb.2 r ls h
  | .pi A B, hb, r, ls, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      rcases List.mem_append.mp h with h | h
      · exact constInsts_levelsBounded A hb.1 r ls h
      · exact constInsts_levelsBounded B hb.2 r ls h
  | .letE A v b, hb, r, ls, h => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact constInsts_levelsBounded A hb.1.1 r ls h
        · exact constInsts_levelsBounded v hb.1.2 r ls h
      · exact constInsts_levelsBounded b hb.2 r ls h
  | .lit _, _, _, _, h => absurd h (List.not_mem_nil _)

/-- A level-closed instance list is within a bound at every valuation if at one. -/
theorem levelsOK_of_closed (σ σ' : Nat → Nat) (b : Nat) (ls : List Level) (hb : levelsBounded 0 ls = true)
    (h : LevelsOK σ b ls) : LevelsOK σ' b ls := fun l hl => by
  rw [← evalTotal_levelBounded0 σ σ' l (Rcic.Syn.levelsBounded_mem hb hl)]
  exact h l hl


theorem map_instLevel_levelsClosed (ls : List Level) : (ms : List Level) → levelsBounded 0 ms = true →
    ms.map (instLevel ls) = ms
  | [], _ => rfl
  | m :: ms, h => by
      simp only [levelsBounded, Bool.and_eq_true] at h
      simp only [List.map_cons, Rcic.Syn.instLevel_of_paramFree ls m h.1, map_instLevel_levelsClosed ls ms h.2]


/-- A level-closed body within the bound at one valuation is within it at every
valuation and every level instantiation. -/
theorem instOK_closed_inst {E : ResolvedEnv} (σ σ' : Nat → Nat) (K : Nat → Nat) {b : Expr Nat}
    (hb : exprLevelsBounded 0 b = true) (h : InstOK E σ K b) (ls : List Level) :
    InstOK E σ' K (instantiateLevels ls b) := by
  rw [Rcic.Declarative.Ann.instantiateLevels_closed ls b hb]
  intro r ls' hm
  obtain ⟨m, hres, hlen, hl⟩ := h r ls' hm
  exact ⟨m, hres, hlen, levelsOK_of_closed σ σ' _ ls' (constInsts_levelsBounded b hb r ls' hm) hl⟩

/-! ### β on non-empty values -/

/-- A non-`∅` application of an abstraction's value forces the argument into the domain. -/
theorem mem_of_fapp_lamVal_ne (M : Interp.{T}) {A x : PSet.{T}} {g : PSet.{T} → PSet.{T}}
    (h : ¬ Equiv (fapp (lamVal M A g) x) pempty) : x ∈ Ed M A := by
  refine @Decidable.byCases _ _ (M.dec (x ∈ Ed M A)) (fun hx => hx) (fun hx => ?_)
  exfalso
  apply h
  cases hd : M.dec (LamProof M A g) with
  | isTrue hL =>
      show Equiv (fapp (cond M.dec _ _ _) x) _
      rw [cond_pos hL]
      exact fapp_pempty x
  | isFalse hL =>
      show Equiv (fapp (cond M.dec _ _ _) x) _
      rw [cond_neg hL]
      exact fapp_mkLam_out hx

/-! ### weak-head normalization -/

/-- The body instances a δ step may introduce are within the bound. -/
def BodiesOK (E : ResolvedEnv) (σ : Nat → Nat) (K : Nat → Nat) : Prop :=
  ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat) (ls : List Level), E.members r = some m → m.body = some b →
    transparent m.mclass = true → ls.length = m.arity → LevelsOK σ (K r) ls → InstOK E σ K (instantiateLevels ls b)

/-- **Weak-head normalization preserves non-empty denotations.** -/
theorem den_whnf (M : Interp.{T}) (σ : Nat → Nat) (K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound M σ K E n) (ρ : Nat → PSet.{T}) (hbodies : BodiesOK E σ K) :
    (fuel : Nat) → (e e' : Expr Nat) → whnfFuel E fuel e = some e' → InstOK E σ K e →
      ¬ Equiv (den M σ ρ e) pempty → Equiv (den M σ ρ e') (den M σ ρ e)
  | 0, _, _, h, _, _ => by cases h
  | fuel + 1, e, e', h, hI, hne => by
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
                exact Equiv.rfl
            | cons a args =>
                simp only [whnfFuel, hs] at h
                have hden : den M σ ρ e = fapps (fapp (lamVal M (den M σ ρ A) fun x => den M σ (vcons x ρ) b)
                    (den M σ ρ a)) (args.map (den M σ ρ)) := by
                  rw [← he, show foldApps (Expr.lam A b) (a :: args) = foldApps (.app (.lam A b) a) args from rfl,
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
                have hstep : Equiv (den M σ ρ (foldApps (instantiate0 a b) args)) (den M σ ρ e) := by
                  rw [hden, den_foldApps, den_inst0]
                  exact fapps_congr hβ.symm _
                have hI' : InstOK E σ K (foldApps (instantiate0 a b) args) := by
                  refine InstOK.sub (fun p hp => ?_) hI
                  rw [← he]
                  rcases (constInsts_foldApps _ _ p).mp hp with hp | ⟨c, hc, hp⟩
                  · rcases constInsts_instantiate 0 a b p hp with hp | hp
                    · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨a, List.mem_cons_self _ _, hp⟩)
                    · exact (constInsts_foldApps _ _ p).mpr (Or.inl (List.mem_append_right _ hp))
                  · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨c, List.mem_cons_of_mem _ hc, hp⟩)
                exact (den_whnf M σ K hE ρ hbodies fuel _ e' h hI' (fun h0 => hne (hstep.symm.trans h0))).trans hstep
        | letE A v b =>
            simp only [whnfFuel, hs] at h
            have hstep : den M σ ρ (foldApps (instantiate0 v b) args) = den M σ ρ e := by
              rw [← he, den_foldApps, den_foldApps, den_inst0]
              rfl
            have hI' : InstOK E σ K (foldApps (instantiate0 v b) args) := by
              refine InstOK.sub (fun p hp => ?_) hI
              rw [← he]
              rcases (constInsts_foldApps _ _ p).mp hp with hp | ⟨c, hc, hp⟩
              · rcases constInsts_instantiate 0 v b p hp with hp | hp
                · exact (constInsts_foldApps _ _ p).mpr
                    (Or.inl (List.mem_append_left _ (List.mem_append_right _ hp)))
                · exact (constInsts_foldApps _ _ p).mpr (Or.inl (List.mem_append_right _ hp))
              · exact (constInsts_foldApps _ _ p).mpr (Or.inr ⟨c, hc, hp⟩)
            rw [← hstep] at hne ⊢
            exact den_whnf M σ K hE ρ hbodies fuel _ e' h hI' hne
        | const r ls =>
            cases ht : transparentBody E r ls with
            | none =>
                simp only [whnfFuel, hs, ht] at h
                cases h
                exact Equiv.rfl
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
                have hstep : Equiv (den M σ ρ (foldApps (instantiateLevels ls b) args)) (den M σ ρ e) := by
                  rw [← he, den_foldApps, den_foldApps]
                  exact fapps_congr hδ.symm _
                have hI' : InstOK E σ K (foldApps (instantiateLevels ls b) args) := by
                  intro r' ls' hp
                  rcases (constInsts_foldApps _ _ _).mp hp with hp | ⟨c, hc, hp⟩
                  · exact hbodies r m b ls hres hb htr hlen hl r' ls' hp
                  · refine hI r' ls' ?_
                    rw [← he]
                    exact (constInsts_foldApps _ _ _).mpr (Or.inr ⟨c, hc, hp⟩)
                exact (den_whnf M σ K hE ρ hbodies fuel _ e' h hI' (fun h0 => hne (hstep.symm.trans h0))).trans hstep
        | bvar _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | sort _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | app _ _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | pi _ _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl
        | lit _ => simp only [whnfFuel, hs] at h; cases h; exact Equiv.rfl

/-! ### the typed root -/

/-- A typed type's denotation is not `∅`: it is an element of a universe, and
no universe contains `∅`. -/
theorem den_type_ne_pempty (M : Interp.{T}) (σ : Nat → Nat) (hU : ∀ k, ¬ pempty ∈ M.U k) (ρ : Nat → PSet.{T})
    {A : Expr Nat} {l : Level} (h : den M σ ρ A ∈ Ed M (den M σ ρ (.sort l))) :
    ¬ Equiv (den M σ ρ A) pempty := by
  intro h0
  have h1 : den M σ ρ A ∈ cond M.dec (Dich (El (tyv (M.U (evalTotal σ l)))))
      (El (tyv (M.U (evalTotal σ l)))) pempty := h
  cases hd : M.dec (Dich (El (tyv (M.U (evalTotal σ l))))) with
  | isTrue hdi =>
      rw [cond_pos hdi] at h1
      exact hU _ (mem_congr_left h0 (mem_congr_right el_tyv h1))
  | isFalse hdn =>
      rw [cond_neg hdn] at h1
      exact not_mem_pempty h1

/-- **A typed type and its weak-head normal form denote the same value.** -/
theorem den_whnf_typed (M : Interp.{T}) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) {Lvl : Nat → PSet.{T} → Prop}
    (hG : Good M N Lvl) (hU : ∀ k, ¬ pempty ∈ M.U k) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound M σ K E n) (hbodies : BodiesOK E σ K) {Γ : LCtx} {A : Expr Nat} {l : Level}
    (d : HasTyT E n Γ A (.sort l)) (hd : LOKt σ N K d) {fuel : Nat} {A' : Expr Nat}
    (hw : whnfFuel E fuel A = some A') (ρ : Nat → PSet.{T}) (hρ : Fits M σ Γ ρ) :
    Equiv (den M σ ρ A') (den M σ ρ A) :=
  den_whnf M σ K hE ρ hbodies fuel A A' hw (instOK_of_lokt σ N K d hd)
    (den_type_ne_pempty M σ hU ρ (sound_ty hG hE d hd ρ hρ))

/-- No universe of the height-4 table contains `∅`. -/
theorem pempty_not_mem_U4 (P : Premises4) (k : Nat) : ¬ pempty ∈ U W4 k := fun h => by
  rcases U4_dich k with hl | hr
  · exact tyv_ne_pempty pempty (hl _ (tyv_pempty_mem_U4 P k))
  · exact hr h

/-- `den_whnf_typed` at the height-4 model. -/
theorem den_whnf_typed4 (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound (mkM P μ) σ K E n) (hbodies : BodiesOK E σ K)
    {Γ : LCtx} {A : Expr Nat} {l : Level} (d : HasTyT E n Γ A (.sort l)) (hd : LOKt σ 4 K d)
    {fuel : Nat} {A' : Expr Nat} (hw : whnfFuel E fuel A = some A') (ρ : Nat → PSet.{4})
    (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ A') (den (mkM P μ) σ ρ A) :=
  den_whnf_typed (mkM P μ) σ 4 K (P.good _ rfl) (fun k => pempty_not_mem_U4 P k) hE hbodies d hd hw ρ hρ

end PSet

end Rcic.F3
