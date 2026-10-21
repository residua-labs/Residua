import rcic.RcicAnnDecl

/-!
# M1-c (ii) — sort-directed typed algorithmic conversion on the copy, and the algorithmic rows

Three things, in dependency order.

(1) `whnfA` and `inferA` are fuel-MONOTONE and therefore DETERMINISTIC across
fuels: two `some` answers agree. This is what makes "the sort of a type" a
function of the syntax — `IsPropTy Γ A` below is a predicate on `(Γ, A)` and
nothing else — and it is the lemma the kill criterion (M1-d) leans on.

(2) `AlgEq` / `AlgEqW` / `AlgNeu`: `Γ ⊢ a ≅ b : A` (Abel–Öhman–Vezzosi's
algorithmic equality with Pujet–Tabareau's irrelevance arm). `AlgEq` normalises
the TYPE and decides irrelevance first — at a proposition (`IsPropTy`, keyed on
`inferSortA`) any two well-typed terms are equal, the terms NOT normalised —
otherwise normalises both terms and hands them to `AlgEqW`, which dispatches on
the type's shape: at a pi, η-expand and compare under the binder; sorts by
`eqN`; pis by components WITH THE SAME ANNOTATIONS; neutrals by spine (`AlgNeu`,
which infers the type as it goes).

(3) The algorithmic ROWS, each by inversion of the relation: `piConvInjAlg`,
`sortConvCharAlg`, `famAppConvInjAlg`. They are the rows for `AlgEq`; the
kernel's rows (for `ConvA`) follow when `ConvA ⊆ AlgEq` — M2's fundamental
theorem. Nothing here claims that inclusion.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) monotonicity and determinism -/

theorem whnfA_mono_le (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) :
    (f f' : Nat) → f ≤ f' → (e w : ExprA) → whnfA E iota Γ f e = some w →
      whnfA E iota Γ f' e = some w := by
  intro f f' hle
  induction hle with
  | refl => intro e w h; exact h
  | step _ ih => intro e w h; exact whnfA_fuel_mono E iota Γ _ e w (ih e w h)

theorem whnfA_det (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA)
    {f₁ f₂ : Nat} {e w₁ w₂ : ExprA}
    (h₁ : whnfA E iota Γ f₁ e = some w₁) (h₂ : whnfA E iota Γ f₂ e = some w₂) :
    w₁ = w₂ := by
  have a := whnfA_mono_le E iota Γ f₁ (max f₁ f₂) (Nat.le_max_left _ _) e w₁ h₁
  have b := whnfA_mono_le E iota Γ f₂ (max f₁ f₂) (Nat.le_max_right _ _) e w₂ h₂
  rw [a] at b
  cases b
  rfl

/-! equations of `inferA` at `fuel + 1`, one per constructor, each `rfl`; the
monotonicity proof rewrites with these so that the recursive calls stay folded. -/

theorem inferA_zero (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (e : ExprA) :
    inferA E iota 0 Γ e = none := rfl
theorem inferA_succ_bvar (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA) (i : Nat) :
    inferA E iota (fuel + 1) Γ (.bvar i) = lookupTypeA Γ i := rfl
theorem inferA_succ_sort (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA) (l : Level) :
    inferA E iota (fuel + 1) Γ (.sort l) = some (.sort (.succ l)) := rfl
theorem inferA_succ_const (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (r : Nat) (ls : List Level) :
    inferA E iota (fuel + 1) Γ (.const r ls) =
      match E.members r with
      | some m => if ls.length = m.arity then some (instantiateLevelsA ls m.mtypeA) else none
      | none => none := rfl
theorem inferA_succ_pi (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (A : ExprA) (u : Level) (B : ExprA) (v : Level) :
    inferA E iota (fuel + 1) Γ (.pi A u B v) = some (.sort (.imax u v)) := rfl
theorem inferA_succ_lam (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (A : ExprA) (u : Level) (body : ExprA) :
    inferA E iota (fuel + 1) Γ (.lam A u body) =
      match inferA E iota fuel (.assumption A :: Γ) body with
      | some B =>
          match inferA E iota fuel (.assumption A :: Γ) B with
          | some TB =>
              match whnfA E iota (.assumption A :: Γ) fuel TB with
              | some (.sort v) => some (.pi A u B v)
              | _ => none
          | none => none
      | none => none := rfl
theorem inferA_succ_app (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (f a : ExprA) :
    inferA E iota (fuel + 1) Γ (.app f a) =
      match inferA E iota fuel Γ f with
      | some Tf =>
          match whnfA E iota Γ fuel Tf with
          | some (.pi _A _u B _v) => some (instantiate0A a B)
          | _ => none
      | none => none := rfl
theorem inferA_succ_letE (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (A value body : ExprA) :
    inferA E iota (fuel + 1) Γ (.letE A value body) =
      match inferA E iota fuel (.letBinding A value :: Γ) body with
      | some B => some (instantiate0A value B)
      | none => none := rfl
theorem inferA_succ_lit (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA) (t : Nat) :
    inferA E iota (fuel + 1) Γ (.lit t) = inferA E iota fuel Γ (natExpandA t) := rfl

/-- one more unit of fuel never changes a `some` answer of `inferA`. -/
theorem inferA_fuel_mono (E : ResolvedEnvA) (iota : IotaFnA) :
    (fuel : Nat) → (Γ : LCtxA) → (e T : ExprA) →
      inferA E iota fuel Γ e = some T → inferA E iota (fuel + 1) Γ e = some T
  | 0, Γ, e, T, h => by
      rw [inferA_zero] at h
      exact Option.noConfusion h
  | fuel + 1, Γ, e, T, h => by
      cases e with
      | bvar i => rw [inferA_succ_bvar] at h ⊢; exact h
      | sort l => rw [inferA_succ_sort] at h ⊢; exact h
      | const r ls => rw [inferA_succ_const] at h ⊢; exact h
      | pi A u B v => rw [inferA_succ_pi] at h ⊢; exact h
      | lit t =>
          rw [inferA_succ_lit] at h ⊢
          exact inferA_fuel_mono E iota fuel Γ _ T h
      | letE A value body =>
          rw [inferA_succ_letE] at h ⊢
          cases h1 : inferA E iota fuel (LocalDeclA.letBinding A value :: Γ) body with
          | none => rw [h1] at h; dsimp only at h; exact Option.noConfusion h
          | some B =>
              rw [h1] at h; dsimp only at h
              rw [inferA_fuel_mono E iota fuel _ body B h1]; dsimp only
              exact h
      | app f a =>
          rw [inferA_succ_app] at h ⊢
          cases h1 : inferA E iota fuel Γ f with
          | none => rw [h1] at h; dsimp only at h; exact Option.noConfusion h
          | some Tf =>
              rw [h1] at h; dsimp only at h
              rw [inferA_fuel_mono E iota fuel Γ f Tf h1]; dsimp only
              cases h2 : whnfA E iota Γ fuel Tf with
              | none => rw [h2] at h; dsimp only at h; exact Option.noConfusion h
              | some Tw =>
                  rw [h2] at h
                  rw [whnfA_fuel_mono E iota Γ fuel Tf Tw h2]
                  exact h
      | lam A u body =>
          rw [inferA_succ_lam] at h ⊢
          cases h1 : inferA E iota fuel (LocalDeclA.assumption A :: Γ) body with
          | none => rw [h1] at h; dsimp only at h; exact Option.noConfusion h
          | some B =>
              rw [h1] at h; dsimp only at h
              rw [inferA_fuel_mono E iota fuel _ body B h1]; dsimp only
              cases h2 : inferA E iota fuel (LocalDeclA.assumption A :: Γ) B with
              | none => rw [h2] at h; dsimp only at h; exact Option.noConfusion h
              | some TB =>
                  rw [h2] at h; dsimp only at h
                  rw [inferA_fuel_mono E iota fuel _ B TB h2]; dsimp only
                  cases h3 : whnfA E iota (LocalDeclA.assumption A :: Γ) fuel TB with
                  | none => rw [h3] at h; dsimp only at h; exact Option.noConfusion h
                  | some TBw =>
                      rw [h3] at h
                      rw [whnfA_fuel_mono E iota _ fuel TB TBw h3]
                      exact h

theorem inferA_mono_le (E : ResolvedEnvA) (iota : IotaFnA) :
    (f f' : Nat) → f ≤ f' → (Γ : LCtxA) → (e T : ExprA) →
      inferA E iota f Γ e = some T → inferA E iota f' Γ e = some T := by
  intro f f' hle
  induction hle with
  | refl => intro Γ e T h; exact h
  | step _ ih => intro Γ e T h; exact inferA_fuel_mono E iota _ Γ e T (ih Γ e T h)

theorem inferA_det (E : ResolvedEnvA) (iota : IotaFnA) {f₁ f₂ : Nat} {Γ : LCtxA}
    {e T₁ T₂ : ExprA}
    (h₁ : inferA E iota f₁ Γ e = some T₁) (h₂ : inferA E iota f₂ Γ e = some T₂) :
    T₁ = T₂ := by
  have a := inferA_mono_le E iota f₁ (max f₁ f₂) (Nat.le_max_left _ _) Γ e T₁ h₁
  have b := inferA_mono_le E iota f₂ (max f₁ f₂) (Nat.le_max_right _ _) Γ e T₂ h₂
  rw [a] at b
  cases b
  rfl

theorem inferSortA_mono_le (E : ResolvedEnvA) (iota : IotaFnA) {f f' : Nat} (hle : f ≤ f')
    {Γ : LCtxA} {T : ExprA} {l : Level}
    (h : inferSortA E iota f Γ T = some l) : inferSortA E iota f' Γ T = some l := by
  unfold inferSortA at h ⊢
  cases h1 : inferA E iota f Γ T with
  | none => rw [h1] at h; dsimp only at h; exact Option.noConfusion h
  | some TT =>
      rw [h1] at h; dsimp only at h
      rw [inferA_mono_le E iota f f' hle Γ T TT h1]; dsimp only
      cases h2 : whnfA E iota Γ f TT with
      | none => rw [h2] at h; dsimp only at h; exact Option.noConfusion h
      | some w =>
          rw [h2] at h
          rw [whnfA_mono_le E iota Γ f f' hle TT w h2]
          exact h

theorem inferSortA_det (E : ResolvedEnvA) (iota : IotaFnA) {f₁ f₂ : Nat} {Γ : LCtxA}
    {T : ExprA} {l₁ l₂ : Level}
    (h₁ : inferSortA E iota f₁ Γ T = some l₁) (h₂ : inferSortA E iota f₂ Γ T = some l₂) :
    l₁ = l₂ := by
  have a := inferSortA_mono_le E iota (Nat.le_max_left f₁ f₂) h₁
  have b := inferSortA_mono_le E iota (Nat.le_max_right f₁ f₂) h₂
  rw [a] at b
  cases b
  rfl

/-! ## (2) the relation -/

/-- weak-head reduction as a relation: SOME fuel reaches the normal form
    `t'`. Deterministic by `whnfA_det`. -/
def RedTo (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (t t' : ExprA) : Prop :=
  ∃ fuel, whnfA E I.fn Γ fuel t = some t'

theorem RedTo_det {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {t t₁ t₂ : ExprA}
    (h₁ : RedTo E I Γ t t₁) (h₂ : RedTo E I Γ t t₂) : t₁ = t₂ := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  exact whnfA_det E I.fn Γ h₁ h₂

/-- a level is ZERO under every total valuation, decided syntactically: `zero`
    is, `succ` and `param` are not, `max` iff both sides are, `imax` iff its
    second argument is (`imax a b` evaluates to `0` exactly when `b` does). -/
def isZero : Level → Bool
  | .zero => true
  | .succ _ => false
  | .max a b => isZero a && isZero b
  | .imax _ b => isZero b
  | .param _ => false

theorem eval_total_some : (ρ : Nat → Option Nat) → (hρ : ∀ i, (ρ i).isSome) → (l : Level) →
    (eval ρ l).isSome
  | ρ, hρ, .zero => rfl
  | ρ, hρ, .succ l => by
      have ih := eval_total_some ρ hρ l
      cases hl : eval ρ l with
      | none => rw [hl] at ih; cases ih
      | some k => simp only [eval, hl, Option.map_some', Option.isSome]
  | ρ, hρ, .max a b => by
      have iha := eval_total_some ρ hρ a
      have ihb := eval_total_some ρ hρ b
      cases ha : eval ρ a with
      | none => rw [ha] at iha; cases iha
      | some x =>
          cases hb : eval ρ b with
          | none => rw [hb] at ihb; cases ihb
          | some y => simp only [eval, ha, hb, Option.bind, Option.map_some', Option.isSome]
  | ρ, hρ, .imax a b => by
      have iha := eval_total_some ρ hρ a
      have ihb := eval_total_some ρ hρ b
      cases ha : eval ρ a with
      | none => rw [ha] at iha; cases iha
      | some x =>
          cases hb : eval ρ b with
          | none => rw [hb] at ihb; cases ihb
          | some y =>
              simp only [eval, ha, hb, Option.bind]
              split <;> simp only [Option.isSome, Option.map_some']
  | ρ, hρ, .param i => hρ i

/-- soundness of `isZero`: a zero level evaluates to `0` under every total
    valuation. -/
theorem isZero_eval : (l : Level) → isZero l = true → ∀ (ρ : Nat → Option Nat),
    (∀ i, (ρ i).isSome) → eval ρ l = some 0
  | .zero, _, _, _ => rfl
  | .succ _, h, _, _ => by simp [isZero] at h
  | .param _, h, _, _ => by simp [isZero] at h
  | .max a b, h, ρ, hρ => by
      simp only [isZero, Bool.and_eq_true] at h
      simp only [eval, isZero_eval a h.1 ρ hρ, isZero_eval b h.2 ρ hρ, Option.bind, Option.map_some']
      rfl
  | .imax a b, h, ρ, hρ => by
      simp only [isZero] at h
      simp only [eval, isZero_eval b h ρ hρ, Option.bind]
      rfl

/-- `A` is a PROPOSITION: its inferred sort is zero — a predicate on `(Γ, A)`
    and nothing else, DECIDABLE once the sort is in hand. THE KEY of the
    irrelevance arm and of `LR_A`'s Prop clause. -/
def IsPropTy (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (A : ExprA) : Prop :=
  ∃ fuel l, inferSortA E I.fn fuel Γ A = some l ∧ isZero l = true

/-- the sort of a type is never a proposition: `sort l : sort (succ l)` and
    `succ l ≠ₙ 0` (a TOTAL valuation evaluates `succ l` to a successor). -/
theorem not_eqN_succ_zero (l : Level) : ¬ eqN (.succ l) .zero := by
  intro h
  have h0 := h (fun _ => some 0)
  simp only [eval] at h0
  cases hl : eval (fun _ => some 0) l with
  | none =>
      rw [hl] at h0
      exact Option.noConfusion h0
  | some k =>
      rw [hl] at h0
      simp only [Option.map_some'] at h0
      cases h0

/-- a `sort` is never `IsPropTy`: `inferSortA` of `sort l` is `succ l`. -/
theorem not_isPropTy_sort (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (l : Level) :
    ¬ IsPropTy E I Γ (.sort l) := by
  intro ⟨fuel, l', h, h0⟩
  cases fuel with
  | zero =>
      simp only [inferSortA, inferA] at h
      exact Option.noConfusion h
  | succ fuel =>
      have hw : whnfA E I.fn Γ (fuel + 1) (.sort (.succ l)) = some (.sort (.succ l)) :=
        whnfA_of_normal E I.fn Γ (fuel + 1) _ rfl
      simp only [inferSortA, inferA, hw] at h
      cases h
      simp [isZero] at h0

/-- the sort of a pi is its annotation, so whether a pi is a proposition is
    read off `v`: DECIDABLE, by `isZero`. -/
theorem inferSortA_pi (E : ResolvedEnvA) (iota : IotaFnA) (fuel : Nat) (Γ : LCtxA)
    (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    inferSortA E iota (fuel + 1) Γ (.pi D u C v) = some (.imax u v) := by
  have hw : whnfA E iota Γ (fuel + 1) (.sort (.imax u v)) = some (.sort (.imax u v)) :=
    whnfA_of_normal E iota Γ (fuel + 1) _ rfl
  simp only [inferSortA, inferA, hw]

theorem isPropTy_pi_iff (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA)
    (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    IsPropTy E I Γ (.pi D u C v) ↔ isZero v = true := by
  constructor
  · intro ⟨fuel, l, h, h0⟩
    have e := inferSortA_det E I.fn h (inferSortA_pi E I.fn fuel Γ D u C v)
    subst e
    simpa [isZero] using h0
  · intro h
    exact ⟨1, .imax u v, inferSortA_pi E I.fn 0 Γ D u C v, by simpa [isZero] using h⟩

mutual

/-- `Γ ⊢ a ≅ b : A`: normalise the two terms and the type, then dispatch. -/
inductive AlgEq (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → ExprA → Type
  | red {Γ : LCtxA} {a b A a' b' A' : ExprA}
      (ha : RedTo E I Γ a a') (hb : RedTo E I Γ b b') (hA : RedTo E I Γ A A')
      (h : AlgEqW E I n Γ a' b' A') : AlgEq E I n Γ a b A
  /-- Pujet–Tabareau: the TYPE is normalised first, and if it is a proposition
      (`IsPropTy`, a function of its syntax) any two terms well-typed at it are
      equal WITHOUT normalising them — a proof need not have a normal form for
      the algorithm to answer. -/
  | irr {Γ : LCtxA} {a b A A' : ExprA}
      (hA : RedTo E I Γ A A') (hP : IsPropTy E I Γ A')
      (ha : HasTyA E I n Γ a A') (hb : HasTyA E I n Γ b A') : AlgEq E I n Γ a b A

/-- `Γ ⊢ a ≅w b : A`, all three in weak-head normal form, the type NOT a
    proposition (that case was decided by `AlgEq.irr`); the TYPE's shape decides. -/
inductive AlgEqW (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → ExprA → Type
  /-- at a pi, η: compare the applications to the fresh variable, under the binder. -/
  | eta {Γ : LCtxA} {a b A B : ExprA} {u v : Level}
      (h : AlgEq E I n (.assumption A :: Γ)
        (.app (liftA 0 1 a) (.bvar 0)) (.app (liftA 0 1 b) (.bvar 0)) B) :
      AlgEqW E I n Γ a b (.pi A u B v)
  | sorts {Γ : LCtxA} {l₁ l₂ l : Level} (h : eqN l₁ l₂) :
      AlgEqW E I n Γ (.sort l₁) (.sort l₂) (.sort l)
  /-- pis: the SAME annotations on both sides, components compared at them. -/
  | pi {Γ : LCtxA} {A A' B B' : ExprA} {u v l : Level}
      (hA : AlgEq E I n Γ A A' (.sort u))
      (hB : AlgEq E I n (.assumption A :: Γ) B B' (.sort v)) :
      AlgEqW E I n Γ (.pi A u B v) (.pi A' u B' v) (.sort l)
  /-- neutrals, at a type that is neither a proposition nor a pi: compared by
      spine, their inferred type compared to the ascribed one. -/
  | neu {Γ : LCtxA} {a b A A' : ExprA} {l : Level}
      (h : AlgNeu E I n Γ a b A') (hty : AlgEq E I n Γ A' A (.sort l)) :
      AlgEqW E I n Γ a b A

/-- `Γ ⊢ a ~ b : A`: neutral spines, the type INFERRED along the spine. -/
inductive AlgNeu (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → ExprA → Type
  | bvar {Γ : LCtxA} {i : Nat} {A : ExprA} (h : lookupTypeA Γ i = some A)
      (hv : lookupValueA Γ i = none) :
      AlgNeu E I n Γ (.bvar i) (.bvar i) A
  | const {Γ : LCtxA} {r : Nat} {ls ls' : List Level} {m : CheckedMemberA}
      (hres : E.members r = some m) (h : eqNList ls ls') :
      AlgNeu E I n Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA)
  | app {Γ : LCtxA} {f g a b Tf A B : ExprA} {u v : Level}
      (hf : AlgNeu E I n Γ f g Tf) (hred : RedTo E I Γ Tf (.pi A u B v))
      (ha : AlgEq E I n Γ a b A) :
      AlgNeu E I n Γ (.app f a) (.app g b) (instantiate0A a B)

end

/-! ## (3) the algorithmic rows, by inversion -/

/-- `SortConvChar` for `AlgEqW`: two sorts equal at a sort are `=ₙ`. The `neu`
    arm is excluded because a sort is not a neutral; the remaining arm IS the
    row. (`AlgEq.irr` cannot reach a sort type: `not_isPropTy_sort`.) -/
theorem sortConvCharAlg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {l₁ l₂ l : Level} (h : AlgEqW E I n Γ (.sort l₁) (.sort l₂) (.sort l)) : eqN l₁ l₂ := by
  cases h with
  | sorts h => exact h
  | neu hn _ => cases hn

/-- `PiConvInj` for `AlgEqW`: two pis equal at a sort have the SAME annotations
    and components equal at them. By inversion: `neu` excluded (a pi is not a
    neutral), `pi` is the row. -/
theorem piConvInjAlg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {A A' B B' : ExprA} {u v u' v' l : Level}
    (h : AlgEqW E I n Γ (.pi A u B v) (.pi A' u' B' v') (.sort l)) :
    u = u' ∧ v = v' ∧
      Nonempty (AlgEq E I n Γ A A' (.sort u)) ∧
      Nonempty (AlgEq E I n (.assumption A :: Γ) B B' (.sort v)) := by
  cases h with
  | pi hA hB => exact ⟨rfl, rfl, ⟨hA⟩, ⟨hB⟩⟩
  | neu hn _ => cases hn

/-- pairwise algorithmic equality of two argument spines, each pair at SOME
    type (the telescope's); snoc-shaped to match `appsSpineA`. -/
inductive ArgsEqA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    List ExprA → List ExprA → Prop
  | nil : ArgsEqA E I n Γ [] []
  | snoc {xs xs' : List ExprA} {x x' : ExprA} {A : ExprA}
      (h : ArgsEqA E I n Γ xs xs') (hx : AlgEq E I n Γ x x' A) :
      ArgsEqA E I n Γ (xs ++ [x]) (xs' ++ [x'])

/-- spine inversion for neutrals with constant heads: the heads are the SAME
    constant at `=ₙ` levels and the arguments are pairwise `AlgEq`. By
    recursion on the derivation. -/
theorem algNeu_spine_inv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    {a b T : ExprA} → AlgNeu E I n Γ a b T →
    ∀ {r r' : Nat} {ls ls' : List Level},
      (appsSpineA a).1 = .const r ls → (appsSpineA b).1 = .const r' ls' →
      r = r' ∧ eqNList ls ls' ∧ ArgsEqA E I n Γ (appsSpineA a).2 (appsSpineA b).2
  | _, _, _, .bvar _ _, _, _, _, _, ha, _ => by
      simp only [appsSpineA] at ha
      cases ha
  | _, _, _, .const _ h, _, _, _, _, ha, hb => by
      simp only [appsSpineA] at ha hb ⊢
      cases ha; cases hb
      exact ⟨rfl, h, .nil⟩
  | _, _, _, .app hf _ ha', _, _, _, _, ha, hb => by
      simp only [appsSpineA] at ha hb ⊢
      obtain ⟨hr, hl, hargs⟩ := algNeu_spine_inv hf ha hb
      exact ⟨hr, hl, .snoc hargs ha'⟩

/-- `FamAppConvInj` for `AlgEqW`, in fact for EVERY constant head: two
    constant-headed spines equal at a sort have the same head at `=ₙ` levels
    and pairwise-equal arguments. `eta` excluded by the type, `sorts`/`pi`
    because the sides are applications or constants, `neu` is the row via
    `algNeu_spine_inv`. -/
theorem famAppConvInjAlg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {a b : ExprA} {l : Level} {r r' : Nat} {ls ls' : List Level}
    (h : AlgEqW E I n Γ a b (.sort l))
    (ha : (appsSpineA a).1 = .const r ls) (hb : (appsSpineA b).1 = .const r' ls') :
    r = r' ∧ eqNList ls ls' ∧ ArgsEqA E I n Γ (appsSpineA a).2 (appsSpineA b).2 := by
  cases h with
  | sorts _ => simp only [appsSpineA] at ha; cases ha
  | pi _ _ => simp only [appsSpineA] at ha; cases ha
  | neu hn _ => exact algNeu_spine_inv hn ha hb

/-! ## pins -/

/-- two sorts at a sort: the row delivers `=ₙ` and nothing weaker. -/
example {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (l : Level) :
    AlgEqW E I n Γ (.sort l) (.sort l) (.sort (.succ l)) := .sorts (fun _ => rfl)

#print axioms whnfA_det
#print axioms inferA_fuel_mono
#print axioms inferA_det
#print axioms inferSortA_det
#print axioms RedTo_det
#print axioms not_isPropTy_sort
#print axioms sortConvCharAlg
#print axioms piConvInjAlg
#print axioms algNeu_spine_inv
#print axioms famAppConvInjAlg

end Rcic.Declarative.Ann
