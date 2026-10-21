import rcic.RcicF8OM1

/-!
# `RcicF8CtxConvVar` — D-VAR discharges H-CTX (X tile S2, #7026 S0 §3.3–3.4, cc ruling Q2)

The X tile's weak-row context conversion: a chain under the binder `A'` moves under a
convertible binder `A` along a WEAK domain chain `EvTc R Γ A A'` (no sort typing of either
binder). Weaken the chain under a copy of `A` placed below `A'` (`EvTc.wk … 1`), then
substitute the new variable for the `A'` binder (`EvTc.subst0 … 0`, whose materialization
`tyConvT_substS` takes only the value typing). The value is the bound variable itself,
typed by the premise-free plain rule `HasTyT.bvar` — the new leaf-less lazy constructor
`EvTy.var` (`RcicF8Ev`, this slice) — retyped along the weakened domain chain (`EvTy.rety`).

`instantiate_bvar_lift_succ` is the pure-syntax index cast. Leaves of the result are exactly
`e.leaves ++ cA.leaves`: nothing is invented and no multiplicity is added. Materialization is
`EvTc.val`'s, i.e. the plain weaken-then-substitute; no `CtxConvT`, no sort typing of `A`
or `A'`, which the weak row does not carry (S0 §3.2). `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- substituting the binder variable for itself under a one-step lift is the identity:
    `lift (k+1) 1` leaves `bvar k` alone and shifts the rest up, `instantiate k (bvar k)`
    puts `bvar k` back and shifts the rest down. -/
theorem instantiate_bvar_lift_succ (k : Nat) (e : Expr Nat) :
    instantiate k (.bvar k) (lift (k + 1) 1 e) = e := by
  induction e generalizing k with
  | bvar i =>
      by_cases h : k + 1 ≤ i
      · have h1 : i + 1 ≠ k := by omega
        have h2 : k < i + 1 := by omega
        simp [lift, instantiate, h, h1, h2]
      · by_cases hik : i = k
        · subst hik
          simp [lift, instantiate, h]
        · have h2 : ¬ k < i := by omega
          simp [lift, instantiate, h, hik, h2]
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf, ihx]
  | lam a b iha ihb =>
      simp only [lift, instantiate]
      rw [iha]
      have hb := ihb (k + 1)
      simpa [lift] using hb
  | pi a b iha ihb =>
      simp only [lift, instantiate]
      rw [iha]
      have hb := ihb (k + 1)
      simpa [lift] using hb
  | letE a v b iha ihv ihb =>
      simp only [lift, instantiate]
      rw [iha, ihv]
      have hb := ihb (k + 1)
      simpa [lift] using hb
  | lit t => rfl

/-- H-CTX discharged: the weak-row context conversion of a chain. -/
def ctxConvVar {Γ : LCtx} {A A' B B' : Expr Nat} (cA : EvTc R Γ A A')
    (e : EvTc R (.assumption A' :: Γ) B B') : EvTc R (.assumption A :: Γ) B B' :=
  EvTc.cast rfl (instantiate_bvar_lift_succ 0 B) (instantiate_bvar_lift_succ 0 B')
    (EvTc.subst0 (v := .bvar 0) 0 (EvTc.wk (.assumption A) 1 e) rfl
      (EvTy.cast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm
        (EvTy.rety (EvTy.var 0 (lift 0 1 A) rfl) (EvTc.wk (.assumption A) 0 cA))))

/-- the moved chain cites exactly the two inputs' leaves, in that order. -/
theorem ctxConvVar_leaves {Γ : LCtx} {A A' B B' : Expr Nat} (cA : EvTc R Γ A A')
    (e : EvTc R (.assumption A' :: Γ) B B') :
    (ctxConvVar cA e).leaves = e.leaves ++ cA.leaves := by
  simp only [ctxConvVar, EvTc.cast_leaves, EvTc.leaves, EvTy.cast_leaves, EvTy.leaves,
    List.nil_append]

/-- the contract shape S1 consumes (`CtxConvContract`, stated raw here so this slice lands
    alone): every output leaf is one of the inputs'. -/
theorem ctxConvVar_contract {Γ : LCtx} {A A' B B' : Expr Nat} (cA : EvTc R Γ A A')
    (e : EvTc R (.assumption A' :: Γ) B B') :
    ∀ ℓ ∈ (ctxConvVar cA e).leaves, ℓ ∈ cA.leaves ++ e.leaves := by
  intro ℓ hℓ
  rw [ctxConvVar_leaves] at hℓ
  rcases List.mem_append.mp hℓ with h | h
  · exact List.mem_append.mpr (.inr h)
  · exact List.mem_append.mpr (.inl h)

/-- `var` has no leaves and materializes to the plain variable rule. -/
theorem var_leaves {Γ : LCtx} (i : Nat) (A : Expr Nat) (hlk : lookupType Γ i = some A) :
    (EvTy.var (R := R) i A hlk).leaves = [] := rfl

theorem var_val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {Γ : LCtx}
    (i : Nat) (A : Expr Nat) (hlk : lookupType Γ i = some A) :
    (EvTy.var (R := R) i A hlk).val hcl hinst = .bvar Γ i A hlk := rfl

/-! ### pin at `emptyEnv`: move a chain from under `Sort (max 0 0)` to under `Sort 0` -/

section Pin

/-- `Sort 0 ≡ Sort (max 0 0)` at `Sort 1` — the etaK fixture's domain step, standalone. -/
def pinSorts : ConvT emptyEnv 0 [] (.sort .zero) (.sort (.max .zero .zero)) (.sort (.succ .zero)) :=
  .sorts [] .zero (.max .zero .zero) (fun _ => rfl)

/-- the domain chain over the one-atom root. -/
def pinDom : EvTc [Jd.cv pinSorts] [] (.sort .zero) (.sort (.max .zero .zero)) :=
  .ofCv (.succ .zero) (.lit pinSorts ⟨_, .head _, .inl rfl⟩)

/-- a chain under `Sort (max 0 0)` moved under `Sort 0`. -/
def pinMoved : EvTc [Jd.cv pinSorts] [.assumption (.sort .zero)] (.sort .zero) (.sort .zero) :=
  ctxConvVar pinDom (.refl [.assumption (.sort (.max .zero .zero))] (.sort .zero))

/-- its leaves are exactly the domain chain's one atom. -/
theorem pinMoved_leaves : pinMoved.leaves = [Jd.cv pinSorts] := by
  rw [pinMoved, ctxConvVar_leaves]
  rfl

end Pin

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.instantiate_bvar_lift_succ
#print axioms Rcic.Declarative.F8Measure.ctxConvVar
#print axioms Rcic.Declarative.F8Measure.ctxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.ctxConvVar_contract
#print axioms Rcic.Declarative.F8Measure.var_leaves
#print axioms Rcic.Declarative.F8Measure.var_val
#print axioms Rcic.Declarative.F8Measure.pinSorts
#print axioms Rcic.Declarative.F8Measure.pinDom
#print axioms Rcic.Declarative.F8Measure.pinMoved
#print axioms Rcic.Declarative.F8Measure.pinMoved_leaves
