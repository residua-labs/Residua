import rcic.RcicTypedScopeCheck
import rcic.RcicParRedSRTyped
import rcic.RcicDT0709EnvWf
import rcic.RcicTypedConv
import rcic.RcicCtxConvT
import rcic.RcicRefutations

/-!
# L0 of the piRow S0 — the CONDITIONAL reduction "Stage-1 rows at an erased
convertibility R + LIFT♮ ⇒ the Π row" (research/rcic/semantic/S0_PIROW.md on
PR #6792, cc ruling Q4)

`R` is abstract; the intended instance is `R Γ a b := eps(a) ↔*_{E♮} eps(b)`
(E♮ not built yet). The target proved here is the WEAK Π-chain row — the
`piRow` field of `TypedRowsWf` (`RcicTypedRowsWf.lean`) — plus a TYPED-INPUT
strong form `piRowInjTyped_of_liftNat`. The literal `PiRowInjT`
(`RcicStepArmsEnvWf.lean:34`) is deliberately NOT the target: that contract is
refuted at every `EnvWfT` env by `no_piRowInjT_of_envWfT` on PR #6493
(`TyConvT.refl` accepts an untyped Π, e.g. `pi (bvar 0) (sort 0)` in the empty
context). That refutation is not reproved or imported here.

The conditional triple ships with all three accessories:

* non-refutability witnesses (`erasedRowsAt_tyConv_scopeCheck`,
  `liftNatAt_tyConv_scopeCheck`, `liftNat_premises_empty`): both premises are
  discharged at every `EnvWfT` environment passing the scope test, in
  particular at `emptyEnv`;
* a tooth (`erasedRowsAt_total`, `not_liftNatAt_total`): the total relation
  satisfies the Stage-1 rows but fails LIFT♮ — §6.5's lesson in abstract
  form, a relation coarser than `ConvT` satisfies the rows and fails LIFT♮.

`closure_claim = 0`.
-/

namespace Rcic.Declarative

/-- Stage-1 interface at an abstract erased convertibility R. -/
structure ErasedRowsAt (E : ResolvedEnv) (n : Nat)
    (R : LCtx → Expr Nat → Expr Nat → Prop) : Prop where
  /-- ES♮ on chains. -/
  es : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {X Y : Expr Nat},
    TyConvT E n Γ X Y → R Γ X Y
  /-- Π-injectivity of R (free in E♮ by confluence). -/
  piInj : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    R Γ (.pi A B) (.pi A' B') → R Γ A A' ∧ R (.assumption A :: Γ) B B'

/-- LIFT♮ at R: R-related types, both typed at sorts, are ConvT-convertible at the left sort. -/
def LiftNatAt (E : ResolvedEnv) (n : Nat)
    (R : LCtx → Expr Nat → Expr Nat → Prop) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {X Y : Expr Nat} {u u' : Level},
    R Γ X Y → HasTyT E n Γ X (.sort u) → HasTyT E n Γ Y (.sort u') →
    Nonempty (ConvT E n Γ X Y (.sort u))

/-- Either a `TyConvT` chain is pure reflexivity, or both endpoints are typed at
    sorts (`firstOf` forward and backward, then `DT009T` endpoints at `EnvWfT`). -/
private theorem endpoints_of_tyConvT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y : Expr Nat}
    (h : TyConvT E n Γ X Y) :
    X = Y ∨
      (∃ u, Nonempty (HasTyT E n Γ X (.sort u))) ∧
        ∃ u', Nonempty (HasTyT E n Γ Y (.sort u')) := by
  rcases TyConvT.firstOf h with heq | ⟨C, u, ⟨hC⟩, _⟩
  · exact Or.inl heq
  · rcases TyConvT.firstOf h.symmT with heq' | ⟨C', u', ⟨hC'⟩, _⟩
    · exact Or.inl heq'.symm
    · exact Or.inr ⟨⟨u, (DT009T_endpoints_envWfT hW hΓ hC).1⟩,
        ⟨u', (DT009T_endpoints_envWfT hW hΓ hC').1⟩⟩

/-- L0, weak chain row: exactly the type of `TypedRowsWf.piRow`. -/
theorem piRow_of_liftNat {E : ResolvedEnv} {n : Nat}
    {R : LCtx → Expr Nat → Expr Nat → Prop}
    (hW : EnvWfT E) (hR : ErasedRowsAt E n R) (hL : LiftNatAt E n R) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  intro Γ hΓ A B A' B' h
  rcases endpoints_of_tyConvT hW hΓ h with heq | ⟨⟨uL, ⟨hpiL⟩⟩, ⟨uR, ⟨hpiR⟩⟩⟩
  · injection heq with hAA' hBB'
    subst hAA'; subst hBB'
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpiL rfl
    obtain ⟨u', v', hA', hB', _⟩ := hasTyTInv_pi hpiR rfl
    obtain ⟨hRA, hRB⟩ := hR.piInj hΓ (hR.es hΓ h)
    obtain ⟨hconv⟩ := hL hΓ hRA hA hA'
    obtain ⟨⟨hAu⟩, ⟨hA'u⟩⟩ := DT009T_endpoints_envWfT hW hΓ hconv
    have hcc : CtxConvT E n (.assumption A' :: Γ) (.assumption A :: Γ) :=
      .assumption (ctxConvT_refl Γ) hA'u hAu (.symm _ _ _ _ hconv)
    have hB'Γ : HasTyT E n (.assumption A :: Γ) B' (.sort v') :=
      hasTyT_ctx (envClosed_of_envWfT hW) hcc hB'
    obtain ⟨hconvB⟩ := hL (CtxWfT.assumption Γ A u hΓ hA) hRB hB hB'Γ
    exact ⟨⟨.of _ _ _ _ hconv⟩, ⟨.of _ _ _ _ hconvB⟩⟩

/-- L0, typed-input strong form: PiRowInjT's conclusion for a typed left Π.
    The levels are `hasTyTInv_pi hpi`'s data; the two `Nonempty` components are
    proved inside Prop (the refl/non-refl split of `firstOf` cannot eliminate
    into the `Σ'` type). -/
def piRowInjTyped_of_liftNat {E : ResolvedEnv} {n : Nat}
    {R : LCtx → Expr Nat → Expr Nat → Prop}
    (hW : EnvWfT E) (hR : ErasedRowsAt E n R) (hL : LiftNatAt E n R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A' B' T₀ : Expr Nat}
    (hpi : HasTyT E n Γ (.pi A B) T₀)
    (h : TyConvT E n Γ (.pi A B) (.pi A' B')) :
    Σ' (u v : Level), Nonempty (ConvT E n Γ A A' (.sort u)) ×'
      Nonempty (ConvT E n (.assumption A :: Γ) B B' (.sort v)) := by
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
  have hdom : Nonempty (ConvT E n Γ A A' (.sort u)) := by
    rcases endpoints_of_tyConvT hW hΓ h with heq | ⟨_, ⟨uR, ⟨hpiR⟩⟩⟩
    · injection heq with hAA' _
      subst hAA'
      exact ⟨.refl _ _ _ hA⟩
    · obtain ⟨u', v', hA', _, _⟩ := hasTyTInv_pi hpiR rfl
      obtain ⟨hRA, _⟩ := hR.piInj hΓ (hR.es hΓ h)
      exact hL hΓ hRA hA hA'
  have hcod : Nonempty (ConvT E n (.assumption A :: Γ) B B' (.sort v)) := by
    rcases endpoints_of_tyConvT hW hΓ h with heq | ⟨⟨uL, ⟨hpiL⟩⟩, ⟨uR, ⟨hpiR⟩⟩⟩
    · injection heq with _ hBB'
      subst hBB'
      exact ⟨.refl _ _ _ hB⟩
    · obtain ⟨u', v', hA', hB', _⟩ := hasTyTInv_pi hpiR rfl
      obtain ⟨hRA, hRB⟩ := hR.piInj hΓ (hR.es hΓ h)
      obtain ⟨hconv⟩ := hL hΓ hRA hA hA'
      obtain ⟨⟨hAu⟩, ⟨hA'u⟩⟩ := DT009T_endpoints_envWfT hW hΓ hconv
      have hcc : CtxConvT E n (.assumption A' :: Γ) (.assumption A :: Γ) :=
        .assumption (ctxConvT_refl Γ) hA'u hAu (.symm _ _ _ _ hconv)
      have hB'Γ : HasTyT E n (.assumption A :: Γ) B' (.sort v') :=
        hasTyT_ctx (envClosed_of_envWfT hW) hcc hB'
      exact hL (CtxWfT.assumption Γ A u hΓ hA) hRB hB hB'Γ
  exact ⟨u, v, hdom, hcod⟩

/-- The in-scope instance: R := nonempty TyConvT. -/
def tyConvRel (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → Prop :=
  fun Γ X Y => Nonempty (TyConvT E n Γ X Y)

/-- Non-refutability witness (premises satisfiable, at every ScopeCheck env). -/
theorem erasedRowsAt_tyConv_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E)
    (hC : hW.ScopeCheck) (n : Nat) : ErasedRowsAt E n (tyConvRel E n) := by
  refine ⟨fun {Γ} hΓ {X Y} h => ⟨h⟩, fun {Γ} hΓ {A B A' B'} h => ?_⟩
  obtain ⟨h'⟩ := h
  exact (typedRowsWf_of_scopeCheck hW hC n).piRow hΓ h'

theorem liftNatAt_tyConv_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E)
    (hC : hW.ScopeCheck) (n : Nat) : LiftNatAt E n (tyConvRel E n) := by
  intro Γ hΓ X Y u u' h hX _
  obtain ⟨h'⟩ := h
  exact convT_of_tyConvT_sort_scope hW (hW.inScope_of_scopeCheck hC) hΓ hX h'

/-- concrete pin at the empty environment: both premises hold. -/
theorem liftNat_premises_empty (n : Nat) :
    ErasedRowsAt emptyEnv n (tyConvRel emptyEnv n) ∧
      LiftNatAt emptyEnv n (tyConvRel emptyEnv n) :=
  ⟨erasedRowsAt_tyConv_scopeCheck .empty True.intro n,
    liftNatAt_tyConv_scopeCheck .empty True.intro n⟩

/-- Tooth: the rows alone carry no content — the total relation satisfies them ... -/
theorem erasedRowsAt_total (E : ResolvedEnv) (n : Nat) :
    ErasedRowsAt E n (fun _ _ _ => True) := by
  refine ⟨fun {Γ} _ {X Y} _ => True.intro, fun {Γ} _ {A B A' B'} _ => ?_⟩
  exact ⟨True.intro, True.intro⟩

/-- ... but fails LIFT♮ (sort 0 vs sort 1 at the empty env). This is §6.5's lesson in abstract form:
    a relation coarser than ConvT satisfies the rows and fails LIFT♮. -/
theorem not_liftNatAt_total : ¬ LiftNatAt emptyEnv 0 (fun _ _ _ => True) := by
  intro h
  obtain ⟨h'⟩ := h CtxWfT.nil True.intro
    (HasTyT.sort [] .zero) (HasTyT.sort [] (.succ .zero))
  exact refutEqN_zero_succ_false
    (sortConvCharT_scopeCheck EnvWfT.empty True.intro CtxWfT.nil h')

end Rcic.Declarative

#print axioms Rcic.Declarative.ErasedRowsAt
#print axioms Rcic.Declarative.LiftNatAt
#print axioms Rcic.Declarative.piRow_of_liftNat
#print axioms Rcic.Declarative.piRowInjTyped_of_liftNat
#print axioms Rcic.Declarative.tyConvRel
#print axioms Rcic.Declarative.erasedRowsAt_tyConv_scopeCheck
#print axioms Rcic.Declarative.liftNatAt_tyConv_scopeCheck
#print axioms Rcic.Declarative.liftNat_premises_empty
#print axioms Rcic.Declarative.erasedRowsAt_total
#print axioms Rcic.Declarative.not_liftNatAt_total
