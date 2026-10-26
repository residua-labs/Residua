import rcic.RcicFamAppRevB1Height4
import rcic.RcicF3Layout
import rcic.RcicF3MainG
import rcic.RcicTypedScopeCheck
import rcic.RcicDTRowFields

/-!
# RcicFamAppStepWLok — Bounded Rows (`SortRowFieldLok` / `PiRowFieldOvershoot`), Producers, and Exact Boundary for `stepW`

Per `cc`'s 2026-10-26 17:00Z addendum ("bounded rows beyond the twin (`stepW` of the F3 assembly)"):
`devin-fcd` (`fable-f3cover`, `RcicF3Assembly.lean`) measured that `walkClassW_of_overshoot_rows`
(#8084, `RcicF3PendWx.lean`) asks for `∀ N K, SortRowFieldLok σ N K E' arity` and
`∀ N K, PiRowFieldOvershoot σ N K E' arity` at the group environment `E'` of a `PendW` group, and
reported that no producers existed for the environments `PendW` concerns and that `RcicF3PendWx`
was unbuilt due to `RcicF3WalkW` vs. `RcicF3Layout` duplicate-declaration conflicts.

This module measures, proves, and seals the complete answer on `main` (importing `RcicF3Layout`
and `RcicF3MainG` directly, with zero duplicate declarations):

1. **§1 Exact Quantification of `PartitionSteps.stepW` (measured by two searches)**:
   - In `RcicF3Assembly.lean:226–232` and `nodeStepRow` (`:257–260`), `stepW` is dispatched
     **orthogonally** to the field class (`PendA`, `PendD`, `PendB`, `GroupClassAt`):
     it quantifies over **every** `EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem`
     and `node : RecNode E E' f rr rm` satisfying `PendW hmem node`
     (`¬ WalkClass node.a.family.parameters.length hmem`), asking for
     `WalkAgree (AgreeAt node.a.family.parameters.length) hmem`.

2. **§2 Exact Logical Equivalence: `(∀ N K, SortRowFieldLok) ↔ SortRowField` and
   `(∀ N K, PiRowFieldOvershoot) ↔ PiRowField` (`sortRowFieldLok_iff_sortRowField`,
   `piRowFieldOvershoot_iff_piRowField`, `famAppRowFieldOvershoot_iff_famAppRowField`)**:
   - `SortRowFieldLok σ N K E n` has stage-free conclusion `eqN u v`, so
     `SortRowField E n → ∀ N K, SortRowFieldLok σ N K E n` is immediate.
   - `PiRowFieldOvershoot σ N K E n` existentially quantifies `(N', K')` **after** the input
     conversion `h : TyConvT E n Γ (.pi A B) (.pi A' B')`. Since every finite `TyConvT` chain `c`
     has a computable finite stage ceiling `boundTyConv σ c` (`loktc_of_bound`), any unbounded
     producer `hPi : PiRowField E n` immediately yields `cA, cB` bounded at
     `N' := max N (max (boundTyConv σ cA) (boundTyConv σ cB))` and
     `K' := fun r => max (K r) (max (boundTyConv σ cA) (boundTyConv σ cB))`.
   - Consequently, **the `LOK` stage indices in `walkClassW_of_overshoot_rows` add zero obligation
     over plain `SortRowField E' arity` and `PiRowField E' arity`**: every producer of
     `SortRowField` / `PiRowField` is already a producer of `∀ N K, SortRowFieldLok` and
     `∀ N K, PiRowFieldOvershoot`.

3. **§3 Producers of `SortRowFieldLok` and `PiRowFieldOvershoot` Across Environment Classes**:
   - **General upgrade (`sortRowFieldLok_of_sortRowField`, `piRowFieldOvershoot_of_piRowField`,
     `sortRowFieldLok_of_typedRowsWf`, `piRowFieldOvershoot_of_typedRowsWf`)**: turns any
     `SortRowField` / `PiRowField` / `TypedRowsWf` supplier into `SortRowFieldLok` and
     `PiRowFieldOvershoot`.
   - **In-scope & `ScopeCheck` groups (`sortRowFieldLok_of_inScope`,
     `piRowFieldOvershoot_of_inScope`, `sortRowFieldLok_of_scopeCheck`,
     `piRowFieldOvershoot_of_scopeCheck`)**: supplies `∀ N K, SortRowFieldLok` and
     `∀ N K, PiRowFieldOvershoot` for every `InScope` / `ScopeCheck` `EnvWfT` derivation.
   - **Out-of-scope revealed singletons `R : RevEnv` via the copy-only twin
     (`RevEnv.revSortRowFieldLok`, `RevEnv.revPiRowFieldOvershoot`,
     `RevEnv.revFamAppRowFieldOvershoot`, specialized at `riRevEnv` and `fooRevEnv`)**:
     supplies `∀ N K, SortRowFieldLok σ N K R.E n` and `∀ N K, PiRowFieldOvershoot σ N K R.E n`
     for every revealed-singleton environment `R.E` (which is outside `InScope` because `R` is an
     AnySort `Prop` family with a non-`Prop` field).
   - **Tight stage-preserving (`N' = N, K' = K`, zero overshoot) `PiRowFieldLok` on the annotated
     twin (`riTwin_piConvInjAL` in `RcicFamAppTwinLokFund`)**.

4. **§4 Self-Contained `stepW` (`WalkAgree (AgreeAt ...)`) Dischargers and Exact Boundary on `main`**:
   - Built directly on `RcicF3Layout` (`AgreeAt`, `WalkAgree`, `WalkRec`, `WalkG`) and `RcicF3MainG`
     (`gInv_group_of`, `consistent4_GW`) with zero `RcicF3WalkW` collision:
     * **Route W1 (`stepW_of_uniformProp`)**: every `Prop`-valued family
       (`UniformProp node.a.family.resultLevel`, including `RevEnv`, `Eq`, `Acc`, etc.) satisfies
       `WalkAgree (AgreeAt node.a.family.parameters.length) hmem` **unconditionally with zero rows**.
     * **Route W2 (`stepW_of_noAppLit_sortRow`, `stepW_of_noAppLit_sortRowFieldLok`)**: when gap
       entries `np ≤ k < cv.parameters.length` are application-free (`NoAppLit`), `SortRowField`
       (or `∀ N K, SortRowFieldLok`) alone suffices, with **zero `PiRowField`**.
     * **Route W3 (`stepW_of_sortRow_piRow`, `stepW_of_overshoot_rows`)**: for arbitrary
       application-containing gap entries, `SortRowField` + `PiRowField` (equivalently
       `(∀ N K, SortRowFieldLok) ∧ (∀ N K, PiRowFieldOvershoot)`) discharges `stepW` with
       **zero `FamAppRowField`**.
     * **Route W4 (`stepW_of_inScope`, `stepW_of_scopeCheck`, `RevEnv.revStepW_of_walkRec`)**:
       unconditional `stepW` discharge for every `InScope` group, every `ScopeCheck` group, and
       every `RevEnv` group.
   - **Orthogonality of `PendW` and `InScope` / `ScopeCheck` (`inScope_group_iff`,
     `scopeCheck_group_iff`, and concrete `PendW` group `wEnvWfT`)**:
     `GroupInScopeT E f fm ctors rr rm` and `groupCheckB` do **not** inspect the `GroupMembersT`
     walk `hmem`; a `PendW` group whose recursor view is in scope (such as the canonical
     `V : Prop → Type` witness `wEnvWfT`, where `wMk` is admitted at `np_c = 1` and `wRec` at
     `np = 0`) passes `ScopeCheck` by kernel evaluation (`wEnvWfT_scopeCheck`), hence has
     `TypedRowsWf`, `SortRowFieldLok`, `PiRowFieldOvershoot`, and `WalkAgree (AgreeAt 0)`.
   - **Exact boundary of `PartitionSteps.stepW` (`agreeAt_iff_gapSortLeAt`,
     `walkAgree_agreeAt_iff_gapSortLeAt`, `stepW_boundary_iff`)**: under `WalkRec hmem`,
     `WalkAgree (AgreeAt node.a.family.parameters.length) hmem` is logically equivalent (`↔`) to
     `WalkAgree (GapSortLeAt node.a.family.parameters.length E') hmem`, which is non-vacuous
     **only** when `UniformType node.a.family.resultLevel` (`¬ UniformProp`), `np < cv.parameters.length`
     (`PendW`), and remains open only when `E'` (at the group or in its prefix `E`) lies outside
     `InScope ∪ RevEnv` (RK-01 territory: non-revealed AnySort `Prop` families like `Eq`,
     function-recursive class A, δ-reached class D, or large-index `Type` groups violating `O2`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Syn.FamApp.StepW

open Rcic.Declarative
open Rcic.F3
open Rcic.F3.PSet
open Rcic.Syn.ClassC
open Rcic.Syn.FamApp.Rev
open Rcic.Syn.FamApp.RevTwin
open Rcic.Model.PS (hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)

/-! ## §1 Computable Stage Ceilings (`boundTy`, `boundConv`, `boundTyConv`, `boundCtxWf`) and `LOK` Equivalences -/

/-- Combined computable stage ceiling (sort/Π height and constant-instance level) for a typing
    derivation `d : HasTyT E n Γ e A`. -/
def boundTy {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat)
    {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A) : Nat :=
  max (boundTySort σ d) (boundTyConst σ d)

/-- Combined computable stage ceiling for a conversion derivation `c : ConvT E n Γ a b A`. -/
def boundConv {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat)
    {Γ : LCtx} {a b A : Expr Nat} (c : ConvT E n Γ a b A) : Nat :=
  max (boundConvSort σ c) (boundConvConst σ c)

/-- Every finite typing derivation `d` satisfies `LOKt σ N K d` once `boundTy σ d ≤ N` and
    `∀ r, boundTy σ d ≤ K r`. -/
theorem lokt_of_bound {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A)
    (hN : boundTy σ d ≤ N) (hK : ∀ r, boundTy σ d ≤ K r) :
    LOKt σ N K d :=
  lokt_of_bounds d (Nat.le_trans (Nat.le_max_left _ _) hN)
    (fun r => Nat.le_trans (Nat.le_max_right _ _) (hK r))

/-- Every finite conversion derivation `c` satisfies `LOKc σ N K c` once `boundConv σ c ≤ N` and
    `∀ r, boundConv σ c ≤ K r`. -/
theorem lokc_of_bound {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {Γ : LCtx} {a b A : Expr Nat} (c : ConvT E n Γ a b A)
    (hN : boundConv σ c ≤ N) (hK : ∀ r, boundConv σ c ≤ K r) :
    LOKc σ N K c :=
  lokc_of_bounds c (Nat.le_trans (Nat.le_max_left _ _) hN)
    (fun r => Nat.le_trans (Nat.le_max_right _ _) (hK r))

/-- Computable stage ceiling for a `TyConvT` chain. -/
def boundTyConv {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat)
    {Γ : LCtx} {a b : Expr Nat} : TyConvT E n Γ a b → Nat
  | .refl _ _ => 0
  | .of _ _ _ _ h => boundConv σ h
  | .trans _ _ _ _ h1 h2 => max (boundTyConv σ h1) (boundTyConv σ h2)

/-- Every finite `TyConvT` chain `hc` satisfies `LOKtc σ N K hc` once `boundTyConv σ hc ≤ N` and
    `∀ r, boundTyConv σ hc ≤ K r`. -/
theorem loktc_of_bound {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {Γ : LCtx} {a b : Expr Nat} : (hc : TyConvT E n Γ a b) →
    boundTyConv σ hc ≤ N → (∀ r, boundTyConv σ hc ≤ K r) → LOKtc σ N K hc
  | .refl _ _, _, _ => by simp only [LOKtc]
  | .of _ _ _ _ h, hN, hK => by
      simp only [boundTyConv] at hN hK
      simp only [LOKtc]
      exact lokc_of_bound h hN hK
  | .trans _ _ _ _ h1 h2, hN, hK => by
      simp only [boundTyConv, Nat.max_le] at hN hK
      simp only [LOKtc]
      exact ⟨loktc_of_bound h1 hN.1 (fun r => (hK r).1),
             loktc_of_bound h2 hN.2 (fun r => (hK r).2)⟩

/-- Stage-bound predicate on a well-formed context `CtxWfT`: every binder typing in `hΓ`
    satisfies `LOKt σ N K` (matching `RcicF3PendWx.LOKctx`). -/
def LOKctx {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → CtxWfT E n Γ → Prop
  | _, .nil => True
  | _, .assumption _ _ _ hΓ hA => LOKctx σ N K hΓ ∧ LOKt σ N K hA
  | _, .letBinding _ _ _ _ hΓ hA hv => LOKctx σ N K hΓ ∧ LOKt σ N K hA ∧ LOKt σ N K hv

/-- Monotonicity of `LOKctx` in `(N, K)`. -/
theorem lokctx_mono {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N N' : Nat} {K K' : Nat → Nat}
    (hN : N ≤ N') (hK : ∀ r, K r ≤ K' r) :
    {Γ : LCtx} → (hΓ : CtxWfT E n Γ) → LOKctx σ N K hΓ → LOKctx σ N' K' hΓ
  | _, .nil, _ => trivial
  | _, .assumption _ _ _ hΓ hA, h =>
      ⟨lokctx_mono hN hK hΓ h.1, lokt_mono hN hK hA h.2⟩
  | _, .letBinding _ _ _ _ hΓ hA hv, h =>
      ⟨lokctx_mono hN hK hΓ h.1, lokt_mono hN hK hA h.2.1, lokt_mono hN hK hv h.2.2⟩

/-- Computable stage ceiling for a well-formed context `hΓ : CtxWfT E n Γ`. -/
def boundCtxWf {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) :
    {Γ : LCtx} → CtxWfT E n Γ → Nat
  | _, .nil => 0
  | _, .assumption _ _ _ hΓ hA => max (boundCtxWf σ hΓ) (boundTy σ hA)
  | _, .letBinding _ _ _ _ hΓ hA hv =>
      max (boundCtxWf σ hΓ) (max (boundTy σ hA) (boundTy σ hv))

/-- Every finite context well-formedness derivation `hΓ` satisfies `LOKctx σ N K hΓ` once
    `boundCtxWf σ hΓ ≤ N` and `∀ r, boundCtxWf σ hΓ ≤ K r`. -/
theorem lokctx_of_bound {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat} :
    {Γ : LCtx} → (hΓ : CtxWfT E n Γ) →
    boundCtxWf σ hΓ ≤ N → (∀ r, boundCtxWf σ hΓ ≤ K r) → LOKctx σ N K hΓ
  | _, .nil, _, _ => trivial
  | _, .assumption _ _ _ hΓ hA, hN, hK => by
      simp only [boundCtxWf, Nat.max_le] at hN
      refine ⟨lokctx_of_bound hΓ hN.1 ?_, lokt_of_bound hA hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, .letBinding _ _ _ _ hΓ hA hv, hN, hK => by
      simp only [boundCtxWf, Nat.max_le] at hN
      refine ⟨lokctx_of_bound hΓ hN.1 ?_, lokt_of_bound hA hN.2.1 ?_, lokt_of_bound hv hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (hK r)

/-! ## §2 Stage-Bounded Row Interfaces (`SortRowFieldLok`, `PiRowFieldOvershoot`, `FamAppRowFieldOvershoot`) and Exact `↔` Equivalences -/

/-- Standalone `sortRow` (`TypedRowsWf.sortRow` field): convertible sorts have `=ₙ` levels. -/
def SortRowField (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {u v : Level},
    TyConvT E n Γ (.sort u) (.sort v) → eqN u v

/-- `TypedRowsWf.sortRow` is a `SortRowField`. -/
theorem SortRowField.of_typedRowsWf {E : ResolvedEnv} {n : Nat} (t : TypedRowsWf E n) :
    SortRowField E n :=
  t.sortRow

/-- Standalone `famAppRow` (`TypedRowsWf.famAppRow` field). -/
def FamAppRowField (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (_hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    (_hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (_h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')),
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'

/-- `TypedRowsWf.famAppRow` is a `FamAppRowField`. -/
theorem FamAppRowField.of_typedRowsWf {E : ResolvedEnv} {n : Nat} (t : TypedRowsWf E n) :
    FamAppRowField E n :=
  t.famAppRow

/-- Stage-bounded spine conversion `ConvArgsTLok σ N K` (`RcicF3PendWx.ConvArgsTLok`). -/
inductive ConvArgsTLok (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → List (Expr Nat) → List (Expr Nat) → Prop
  | nil (T : Expr Nat) : ConvArgsTLok σ N K E n Γ T [] []
  | cons (A B x x' : Expr Nat) (xs xs' : List (Expr Nat)) :
      (∃ c : ConvT E n Γ x x' A, LOKc σ N K c) →
      ConvArgsTLok σ N K E n Γ (instantiate0 x B) xs xs' →
      ConvArgsTLok σ N K E n Γ (.pi A B) (x :: xs) (x' :: xs')

/-- Every `ConvArgsTLok` erases its stage bound to an unbounded `ConvArgsT`. -/
theorem ConvArgsTLok.toConvArgsT {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {xs xs' : List (Expr Nat)}
    (h : ConvArgsTLok σ N K E n Γ T xs xs') : ConvArgsT E n Γ T xs xs' := by
  induction h with
  | nil T => exact .nil T
  | cons A B x x' xs xs' hc _ ih =>
      obtain ⟨c, _⟩ := hc
      exact .cons A B x x' xs xs' ⟨c⟩ ih

/-- Monotonicity of `ConvArgsTLok` in `(N, K)`. -/
theorem ConvArgsTLok.mono {σ : Nat → Nat} {N N' : Nat} {K K' : Nat → Nat}
    (hN : N ≤ N') (hK : ∀ r, K r ≤ K' r)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {xs xs' : List (Expr Nat)}
    (h : ConvArgsTLok σ N K E n Γ T xs xs') : ConvArgsTLok σ N' K' E n Γ T xs xs' := by
  induction h with
  | nil T => exact .nil T
  | cons A B x x' xs xs' hc _ ih =>
      obtain ⟨c, hlc⟩ := hc
      exact .cons A B x x' xs xs' ⟨c, lokc_mono hN hK c hlc⟩ ih

/-- Every finite `ConvArgsT` spine has a finite overshoot ceiling `(N', K')` above `(N, K)` at
    which `ConvArgsTLok σ N' K'` holds. -/
theorem convArgsTLok_of_convArgsT (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {xs xs' : List (Expr Nat)}
    (h : ConvArgsT E n Γ T xs xs') :
    ∃ (N' : Nat) (K' : Nat → Nat), N ≤ N' ∧ (∀ r, K r ≤ K' r) ∧
      ConvArgsTLok σ N' K' E n Γ T xs xs' := by
  induction h with
  | nil T => exact ⟨N, K, Nat.le_refl N, fun _ => Nat.le_refl _, .nil T⟩
  | cons A B x x' xs xs' hc _ ih =>
      obtain ⟨c⟩ := hc
      obtain ⟨N₁, K₁, hN₁, hK₁, htl⟩ := ih
      let B₀ := boundConv σ c
      refine ⟨max N₁ B₀, fun r => max (K₁ r) B₀,
        Nat.le_trans hN₁ (Nat.le_max_left _ _),
        fun r => Nat.le_trans (hK₁ r) (Nat.le_max_left _ _),
        .cons A B x x' xs xs'
          ⟨c, lokc_of_bound c (Nat.le_max_right _ _) (fun _ => Nat.le_max_right _ _)⟩
          (htl.mono (Nat.le_max_left _ _) (fun _ => Nat.le_max_left _ _))⟩

/-- **Stage-bounded Row 1 (`SortRowFieldLok`, `#8084` `RcicF3PendWx:1456`)**:
    for an `(N, K)`-bounded well-formed context `hΓ` and an `(N, K)`-bounded sort-conversion chain
    `h`, the sort levels are `=ₙ`. -/
def SortRowFieldLok (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {u v : Level} (hΓ : CtxWfT E n Γ), LOKctx σ N K hΓ →
    (h : TyConvT E n Γ (.sort u) (.sort v)) → LOKtc σ N K h → eqN u v

/-- **Stage-preserving Row 2 (`PiRowFieldLok`, `#8084` `RcicF3PendWx:1465`)**:
    produces domain and codomain `TyConvT` chains at the **same** stage `(N, K)`. -/
def PiRowFieldLok (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {A B A' B' : Expr Nat} (hΓ : CtxWfT E n Γ), LOKctx σ N K hΓ →
    (h : TyConvT E n Γ (.pi A B) (.pi A' B')) → LOKtc σ N K h →
    (∃ cA : TyConvT E n Γ A A', LOKtc σ N K cA) ∧
      (∃ cB : TyConvT E n (.assumption A :: Γ) B B', LOKtc σ N K cB)

/-- **Overshoot-tolerant Row 2 (`PiRowFieldOvershoot`, `#8084` `RcicF3PendWx:2515`)**:
    for an `(N, K)`-bounded Π-conversion chain `h`, there exist stage bounds `(N', K')` with
    `N ≤ N'` and `∀ r, K r ≤ K' r` such that the projected domain and codomain `TyConvT` chains
    are `(N', K')`-bounded. -/
def PiRowFieldOvershoot (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {A B A' B' : Expr Nat} (hΓ : CtxWfT E n Γ), LOKctx σ N K hΓ →
    (h : TyConvT E n Γ (.pi A B) (.pi A' B')) → LOKtc σ N K h →
    ∃ (N' : Nat) (K' : Nat → Nat) (cA : TyConvT E n Γ A A')
      (cB : TyConvT E n (.assumption A :: Γ) B B'),
      N ≤ N' ∧ (∀ r, K r ≤ K' r) ∧ LOKtc σ N' K' cA ∧ LOKtc σ N' K' cB

/-- **Overshoot-tolerant Row 3 (`FamAppRowFieldOvershoot`, `#8084` `RcicF3PendWx:2525`)**:
    for an `(N, K)`-bounded family-application conversion chain `h`, there exist stage bounds
    `(N', K')` above `(N, K)` such that the projected argument conversions satisfy
    `ConvArgsTLok σ N' K'`. -/
def FamAppRowFieldOvershoot (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hΓ : CtxWfT E n Γ), LOKctx σ N K hΓ →
    E.members r = some m → m.mclass = .inductiveM →
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) →
    LOKtc σ N K h →
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ∃ (N' : Nat) (K' : Nat → Nat), N ≤ N' ∧ (∀ r', K r' ≤ K' r') ∧
        ConvArgsTLok σ N' K' E n Γ (instantiateLevels ls m.mtype) xs xs'

/-- Every tight `PiRowFieldLok σ N K E n` implies `PiRowFieldOvershoot σ N K E n` (with `N' = N`,
    `K' = K`, zero overshoot). -/
theorem piRowFieldOvershoot_of_piRowFieldLok {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {E : ResolvedEnv} {n : Nat} (hPi : PiRowFieldLok σ N K E n) :
    PiRowFieldOvershoot σ N K E n := by
  intro Γ A B A' B' hΓ hLΓ h hLh
  obtain ⟨⟨cA, hcA⟩, ⟨cB, hcB⟩⟩ := hPi hΓ hLΓ h hLh
  exact ⟨N, K, cA, cB, Nat.le_refl N, fun _ => Nat.le_refl _, hcA, hcB⟩

/-- **Upward bridge for Row 1 (`SortRowField → ∀ N K, SortRowFieldLok`)**:
    because `SortRowFieldLok`'s conclusion `eqN u v` is stage-free, any unbounded `SortRowField E n`
    immediately gives `SortRowFieldLok σ N K E n` at every `(σ, N, K)`. -/
theorem sortRowFieldLok_of_sortRowField (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hSort : SortRowField E n) (N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K E n :=
  fun hΓ _ h _ => hSort hΓ h

/-- **Downward bridge for Row 1 (`(∀ N K, SortRowFieldLok) → SortRowField`)**:
    instantiating `(N, K)` at the computable ceiling `max (boundCtxWf σ hΓ) (boundTyConv σ h)`
    recovers `SortRowField E n`. -/
theorem sortRowField_of_lok_all (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hSort : ∀ N K, SortRowFieldLok σ N K E n) :
    SortRowField E n := by
  intro Γ hΓ u v h
  let M := max (boundCtxWf σ hΓ) (boundTyConv σ h)
  exact hSort M (fun _ => M) hΓ
    (lokctx_of_bound hΓ (Nat.le_max_left _ _) (fun _ => Nat.le_max_left _ _))
    h (loktc_of_bound h (Nat.le_max_right _ _) (fun _ => Nat.le_max_right _ _))

/-- **Exact equivalence (`(∀ N K, SortRowFieldLok σ N K E n) ↔ SortRowField E n`)**. -/
theorem sortRowFieldLok_iff_sortRowField (σ : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (∀ N K, SortRowFieldLok σ N K E n) ↔ SortRowField E n :=
  ⟨sortRowField_of_lok_all σ, sortRowFieldLok_of_sortRowField σ⟩

/-- **Upward bridge for Row 2 (`PiRowField → ∀ N K, PiRowFieldOvershoot`)**:
    because `PiRowFieldOvershoot` existentially quantifies `(N', K')` after the input conversion `h`,
    any unbounded `hPi : PiRowField E n` produces `cA, cB` whose computable stage ceiling
    `max (boundTyConv σ cA) (boundTyConv σ cB)` witnesses `PiRowFieldOvershoot σ N K E n` at every
    `(σ, N, K)`. -/
theorem piRowFieldOvershoot_of_piRowField (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hPi : PiRowField E n) (N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K E n := by
  intro Γ A B A' B' hΓ _ h _
  obtain ⟨⟨cA⟩, ⟨cB⟩⟩ := hPi hΓ h
  let M := max (boundTyConv σ cA) (boundTyConv σ cB)
  refine ⟨max N M, fun r => max (K r) M, cA, cB,
    Nat.le_max_left N M, fun r => Nat.le_max_left (K r) M,
    loktc_of_bound cA
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right N M))
      (fun r => Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right (K r) M)),
    loktc_of_bound cB
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right N M))
      (fun r => Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right (K r) M))⟩

/-- **Downward bridge for Row 2 (`(∀ N K, PiRowFieldOvershoot) → PiRowField`)**. -/
theorem piRowField_of_overshoot_all (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hPi : ∀ N K, PiRowFieldOvershoot σ N K E n) :
    PiRowField E n := by
  intro Γ hΓ A B A' B' h
  let M := max (boundCtxWf σ hΓ) (boundTyConv σ h)
  obtain ⟨_, _, cA, cB, _, _, _, _⟩ :=
    hPi M (fun _ => M) hΓ
      (lokctx_of_bound hΓ (Nat.le_max_left _ _) (fun _ => Nat.le_max_left _ _))
      h (loktc_of_bound h (Nat.le_max_right _ _) (fun _ => Nat.le_max_right _ _))
  exact ⟨⟨cA⟩, ⟨cB⟩⟩

/-- **Exact equivalence (`(∀ N K, PiRowFieldOvershoot σ N K E n) ↔ PiRowField E n`)**:
    the `∀ N K` overshoot row interface in `walkClassW_of_overshoot_rows` (#8084) is logically
    equivalent to the standard unbounded `PiRowField E n` (`RcicTypedRowsWf`). -/
theorem piRowFieldOvershoot_iff_piRowField (σ : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (∀ N K, PiRowFieldOvershoot σ N K E n) ↔ PiRowField E n :=
  ⟨piRowField_of_overshoot_all σ, piRowFieldOvershoot_of_piRowField σ⟩

/-- **Upward bridge for Row 3 (`FamAppRowField → ∀ N K, FamAppRowFieldOvershoot`)**. -/
theorem famAppRowFieldOvershoot_of_famAppRowField (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hFam : FamAppRowField E n) (N : Nat) (K : Nat → Nat) :
    FamAppRowFieldOvershoot σ N K E n := by
  intro Γ r m ls ls' xs xs' w hΓ _ hm hind hty h _
  obtain ⟨hls, hlen, hargs⟩ := hFam hΓ hm hind hty h
  exact ⟨hls, hlen, convArgsTLok_of_convArgsT σ N K hargs⟩

/-- **Downward bridge for Row 3 (`(∀ N K, FamAppRowFieldOvershoot) → FamAppRowField`)**. -/
theorem famAppRowField_of_overshoot_all (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hFam : ∀ N K, FamAppRowFieldOvershoot σ N K E n) :
    FamAppRowField E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty h
  let M := max (boundCtxWf σ hΓ) (boundTyConv σ h)
  obtain ⟨hls, hlen, _, _, _, _, hargs⟩ :=
    hFam M (fun _ => M) hΓ
      (lokctx_of_bound hΓ (Nat.le_max_left _ _) (fun _ => Nat.le_max_left _ _))
      hm hind hty h
      (loktc_of_bound h (Nat.le_max_right _ _) (fun _ => Nat.le_max_right _ _))
  exact ⟨hls, hlen, hargs.toConvArgsT⟩

/-- **Exact equivalence (`(∀ N K, FamAppRowFieldOvershoot σ N K E n) ↔ FamAppRowField E n`)**. -/
theorem famAppRowFieldOvershoot_iff_famAppRowField (σ : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (∀ N K, FamAppRowFieldOvershoot σ N K E n) ↔ FamAppRowField E n :=
  ⟨famAppRowField_of_overshoot_all σ, famAppRowFieldOvershoot_of_famAppRowField σ⟩

/-! ## §3 Concrete Producers of `SortRowFieldLok` and `PiRowFieldOvershoot` -/

/-! ### §3.1 Producer A: From any `TypedRowsWf E n` -/

theorem sortRowFieldLok_of_typedRowsWf (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hrows : TypedRowsWf E n) (N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K E n :=
  sortRowFieldLok_of_sortRowField σ hrows.sortRow N K

theorem piRowFieldOvershoot_of_typedRowsWf (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hrows : TypedRowsWf E n) (N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K E n :=
  piRowFieldOvershoot_of_piRowField σ hrows.piRow N K

theorem famAppRowFieldOvershoot_of_typedRowsWf (σ : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hrows : TypedRowsWf E n) (N : Nat) (K : Nat → Nat) :
    FamAppRowFieldOvershoot σ N K E n :=
  famAppRowFieldOvershoot_of_famAppRowField σ hrows.famAppRow N K

/-! ### §3.2 Producer B: For every `EnvWfT.InScope` and `EnvWfT.ScopeCheck` environment -/

/-- **Producer for `EnvWfT.InScope`**: supplies `SortRowFieldLok` for every in-scope `EnvWfT`
    (including `PendW` groups whose recursor view is in `GroupInScopeT`). -/
theorem sortRowFieldLok_of_inScope (σ : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hIS : hW.InScope) (n N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K E n :=
  sortRowFieldLok_of_typedRowsWf σ (Ann.typedRowsWf_of_envWfT_semPrefix hW hIS n) N K

/-- **Producer for `EnvWfT.InScope`**: supplies `PiRowFieldOvershoot` for every in-scope `EnvWfT`
    (including `PendW` groups whose recursor view is in `GroupInScopeT`). -/
theorem piRowFieldOvershoot_of_inScope (σ : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hIS : hW.InScope) (n N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K E n :=
  piRowFieldOvershoot_of_typedRowsWf σ (Ann.typedRowsWf_of_envWfT_semPrefix hW hIS n) N K

/-- **Producer for `EnvWfT.InScope`**: supplies `FamAppRowFieldOvershoot` for every in-scope `EnvWfT`. -/
theorem famAppRowFieldOvershoot_of_inScope (σ : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hIS : hW.InScope) (n N : Nat) (K : Nat → Nat) :
    FamAppRowFieldOvershoot σ N K E n :=
  famAppRowFieldOvershoot_of_typedRowsWf σ (Ann.typedRowsWf_of_envWfT_semPrefix hW hIS n) N K

/-- **Producer for `EnvWfT.ScopeCheck`**: supplies `SortRowFieldLok` for every `ScopeCheck` `EnvWfT`. -/
theorem sortRowFieldLok_of_scopeCheck (σ : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hSC : hW.ScopeCheck) (n N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K E n :=
  sortRowFieldLok_of_inScope σ hW (hW.inScope_of_scopeCheck hSC) n N K

/-- **Producer for `EnvWfT.ScopeCheck`**: supplies `PiRowFieldOvershoot` for every `ScopeCheck` `EnvWfT`. -/
theorem piRowFieldOvershoot_of_scopeCheck (σ : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hSC : hW.ScopeCheck) (n N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K E n :=
  piRowFieldOvershoot_of_inScope σ hW (hW.inScope_of_scopeCheck hSC) n N K

/-- **Producer for `EnvWfT.ScopeCheck`**: supplies `FamAppRowFieldOvershoot` for every `ScopeCheck` `EnvWfT`. -/
theorem famAppRowFieldOvershoot_of_scopeCheck (σ : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hSC : hW.ScopeCheck) (n N : Nat) (K : Nat → Nat) :
    FamAppRowFieldOvershoot σ N K E n :=
  famAppRowFieldOvershoot_of_inScope σ hW (hW.inScope_of_scopeCheck hSC) n N K

/-! ### §3.3 Producer C: For every out-of-scope revealed singleton `R : RevEnv` (via the copy-only twin) -/

/-- **Out-of-scope producer for `R : RevEnv` (`SortRowFieldLok`)**:
    via our copy-only twin (`R.revSortRow`, `RcicFamAppRevPiRow`), every revealed-singleton
    environment `R.E` (which is out-of-scope for `EnvWfT.InScope` because `R` is an AnySort `Prop`
    family with a non-`Prop` revealed field) satisfies `SortRowFieldLok σ N K R.E n` for all
    `σ, n, N, K`. -/
theorem RevEnv.revSortRowFieldLok (R : RevEnv) (σ : Nat → Nat) (n N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K R.E n :=
  sortRowFieldLok_of_sortRowField σ R.revSortRow N K

/-- **Out-of-scope producer for `R : RevEnv` (`PiRowFieldOvershoot`)**:
    via our copy-only twin (`R.revPiRow`, `RcicFamAppRevPiRow`), every revealed-singleton
    environment `R.E` satisfies `PiRowFieldOvershoot σ N K R.E n` for all `σ, n, N, K`. -/
theorem RevEnv.revPiRowFieldOvershoot (R : RevEnv) (σ : Nat → Nat) (n N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K R.E n :=
  piRowFieldOvershoot_of_piRowField σ (R.revPiRow n) N K

/-- **Out-of-scope producer for `R : RevEnv` (`FamAppRowFieldOvershoot`)**:
    via our copy-only twin (`R.revFamAppRow`, `RcicFamAppRevFamRow`), every revealed-singleton
    environment `R.E` satisfies `FamAppRowFieldOvershoot σ N K R.E n` for all `σ, n, N, K`. -/
theorem RevEnv.revFamAppRowFieldOvershoot (R : RevEnv) (σ : Nat → Nat) (n N : Nat) (K : Nat → Nat) :
    FamAppRowFieldOvershoot σ N K R.E n :=
  famAppRowFieldOvershoot_of_famAppRowField σ R.revFamAppRow N K

/-- Concrete instantiation at `riEnv` (`riRevEnv.E = riEnv`). -/
theorem riSortRowFieldLok (σ : Nat → Nat) (n N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K riEnv n :=
  RevEnv.revSortRowFieldLok riRevEnv σ n N K

/-- Concrete instantiation at `riEnv` (`riRevEnv.E = riEnv`). -/
theorem riPiRowFieldOvershoot (σ : Nat → Nat) (n N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K riEnv n :=
  RevEnv.revPiRowFieldOvershoot riRevEnv σ n N K

/-! ## §4 Self-Contained `stepW` (`WalkAgree (AgreeAt ...)`) Dischargers on `main` (`RcicF3Layout` / `RcicF3MainG`) -/

/-- Every field in the recursor's constructor view `node.a.constructorViews i` is typed in `node.E0`
    at a level bounded by `node.a.family.resultLevel` (`node.ctorsTyped i` and `node.h07 i`). -/
theorem recView_field_bound {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length)
    (j : Fin (node.a.constructorViews i).fields.length) :
    let cvR := node.a.constructorViews i
    let k := cvR.fieldIndex j
    Nonempty (HasTyT node.E0 node.a.family.member.arity
      (policyPrefixContext (cvR.parameters ++ cvR.fields) k.val)
      ((cvR.parameters ++ cvR.fields)[k.val]) (.sort (cvR.domainsTyped.levels k))) ∧
    (UniformProp node.a.family.resultLevel ∨
      leN (cvR.domainsTyped.levels k) node.a.family.resultLevel) := by
  refine ⟨(node.ctorsTyped i).1 ((node.a.constructorViews i).fieldIndex j), ?_⟩
  rcases node.h07 i j with hP | ⟨_, hle⟩
  · exact Or.inl hP
  · exact Or.inr hle

/-- **Syntactic determination of the walk constructor telescope**: in any group step with `WalkRec`,
    every constructor `(r, m)` admitted in `Ew` with `(famO, cv)` matches a constructor
    `node.a.constructorViews i` of `node`, and has the exact same concatenated telescope
    `cv.parameters ++ cv.fields = (node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields`,
    the same family result level, and the same arity. -/
theorem walk_ctor_views_syn_eq {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    {Ew : ResolvedEnv} {r : Nat} {m : CheckedMember} (famO : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew famO m)
    (hin : (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)])
    (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m') :
    ∃ i : Fin node.a.constructors.length,
      r = f + 1 + i.val ∧
      m = node.a.constructors[i.val] ∧
      cv.parameters ++ cv.fields =
        (node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields ∧
      famO.resultLevel = node.a.family.resultLevel ∧
      famO.member.arity = node.a.family.member.arity := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  obtain ⟨_, _, hf', _, _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hkC : m.mclass = .constructorM := cv.hasClass
  have hctor : ∃ i : Fin node.a.constructors.length, r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
    rcases group_member_cases hmem hL hrr node (groupMembersT_installed hmem hin) with
      h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h1
    · rcases List.mem_cons.mp hin with h2 | h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; rw [hfam] at hkC; cases hkC
      · rcases List.mem_append.mp h2 with h3 | h3
        · have hr : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, h3, rfl⟩
          rw [hL] at hr
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
          have hi' : i < node.a.constructors.length := by rw [hlen]; exact List.mem_range.mp hi
          exact ⟨⟨i, hi'⟩, rfl, Option.some.inj ((groupMembersT_installed hmem hin).symm.trans
            (node_ctor_member node ⟨i, hi'⟩))⟩
        · rw [List.mem_singleton] at h3
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3; rw [hrec] at hkC; cases hkC
    · rw [hfam] at hkC; cases hkC
    · rw [hrec] at hkC; cases hkC
    · exact h1
  obtain ⟨i, hr_eq, hm_eq⟩ := hctor
  have hstO := (congrArg CheckedMember.mtype hm_eq).symm.trans cv.storedType
  have hstR := (node.a.constructorViews i).storedType
  have hspl := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (hstO.symm.trans hstR)
  have href : famO.ref = node.a.family.ref := foldApps_const_head hspl.2
  have hfamO : famO.member = fm := by
    have h1 := famO.present
    rw [href, node.fam] at h1
    exact Option.some.inj ((hEw f _ h1).symm.trans hf')
  have hlvO : famO.resultLevel = node.a.family.resultLevel := by
    have e1 := famO.storedType
    have e2 := node.a.family.storedType
    rw [hfamO] at e1
    rw [hfmm] at e2
    have := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) (e1.symm.trans e2)).2
    injection this
  have harO : famO.member.arity = node.a.family.member.arity := by rw [hfamO, hfmm]
  exact ⟨i, hr_eq, hm_eq, hspl.1, hlvO, harO⟩

/-- From `TelTypedT E n ds levels`, every prefix context `policyPrefixContext ds k` ($k \le ds.\text{length}$)
    is well-formed (`CtxWfT E n (policyPrefixContext ds k)`). -/
theorem ctxWfT_of_telTypedT {E : ResolvedEnv} {n : Nat} {ds : List (Expr Nat)}
    {levels : Fin ds.length → Level} (htel : TelTypedT E n ds levels)
    (k : Nat) (hk : k ≤ ds.length) :
    Nonempty (CtxWfT E n (policyPrefixContext ds k)) := by
  have h := ctxWfT_prefix (E := E) (n := n) (Γ := []) CtxWfT.nil ds k hk fun i hi => by
    have hi' : i < ds.length := Nat.lt_of_lt_of_le hi hk
    obtain ⟨d⟩ := htel ⟨i, hi'⟩
    rw [List.append_nil]
    exact ⟨levels ⟨i, hi'⟩, ⟨d⟩⟩
  simpa only [List.append_nil] using h

/-- `RecNode.E0` extends into `E'` by `node.sub` and `node.fresh`. -/
theorem recNode_E0_sub {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    ∀ r m, node.E0.members r = some m → E'.members r = some m :=
  fun r m h => node.sub r m (members_extend_preserved node.fresh r m h)

private def hasTyT_cast {E : ResolvedEnv} {n₁ n₂ : Nat} {Γ₁ Γ₂ : LCtx} {e₁ e₂ T : Expr Nat}
    (hn : n₁ = n₂) (hΓ : Γ₁ = Γ₂) (he : e₁ = e₂)
    (d : HasTyT E n₁ Γ₁ e₁ T) : HasTyT E n₂ Γ₂ e₂ T := by
  subst hn; subst hΓ; subst he; exact d

/-- **Double typing of the shared telescope entry**: at every index `k ≥ node.a.family.parameters.length`
    of a constructor in a `WalkRec` group, both the constructor's own view `cv` and the recursor's
    view `node.a.constructorViews i` type the exact same expression `(cv.parameters ++ cv.fields)[k]`
    in the exact same well-formed context `policyPrefixContext (cv.parameters ++ cv.fields) k` in `E'`,
    and the recursor view's level `uR` satisfies `UniformProp famO.resultLevel ∨ leN uR famO.resultLevel`. -/
theorem walk_entry_double_typed {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    {Ew : ResolvedEnv} {r : Nat} {m : CheckedMember} (famO : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew famO m) (htyped : CtorTypedT cv)
    (hin : (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)])
    (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m')
    (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length)
    (hge : node.a.family.parameters.length ≤ k) :
    Nonempty (CtxWfT E' famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k)) ∧
    Nonempty (HasTyT E' famO.member.arity
      (policyPrefixContext (cv.parameters ++ cv.fields) k)
      ((cv.parameters ++ cv.fields)[k]'hk)
      (.sort (cv.domainsTyped.levels ⟨k, hk⟩))) ∧
    ∃ uR : Level,
      Nonempty (HasTyT E' famO.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) k)
        ((cv.parameters ++ cv.fields)[k]'hk)
        (.sort uR)) ∧
      (UniformProp famO.resultLevel ∨ leN uR famO.resultLevel) := by
  obtain ⟨i, _, _, hcat, hlvO, harO⟩ :=
    walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO cv hin hEw
  have htelE' : TelTypedT E' famO.member.arity (cv.parameters ++ cv.fields) cv.domainsTyped.levels :=
    fun idx => let ⟨d⟩ := htyped.1 idx; ⟨hasTyTExt hEw d⟩
  have hΓ : Nonempty (CtxWfT E' famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k)) :=
    ctxWfT_of_telTypedT htelE' k (Nat.le_of_lt hk)
  have hdO : Nonempty (HasTyT E' famO.member.arity
      (policyPrefixContext (cv.parameters ++ cv.fields) k)
      ((cv.parameters ++ cv.fields)[k]'hk)
      (.sort (cv.domainsTyped.levels ⟨k, hk⟩))) := htelE' ⟨k, hk⟩
  let cvR := node.a.constructorViews i
  have hlenN : cvR.parameters.length = node.a.family.parameters.length := cvR.parameterCount
  have hkR : k < (cvR.parameters ++ cvR.fields).length := hcat ▸ hk
  have hjlt : k - cvR.parameters.length < cvR.fields.length := by
    simp only [List.length_append] at hkR; omega
  let jR : Fin cvR.fields.length := ⟨k - cvR.parameters.length, hjlt⟩
  have hfi : (⟨k, hkR⟩ : Fin (cvR.parameters ++ cvR.fields).length) = cvR.fieldIndex jR :=
    Fin.ext (by
      show k = cvR.parameters.length + (k - cvR.parameters.length)
      omega)
  obtain ⟨⟨dR0⟩, hbdR⟩ := recView_field_bound node i jR
  have dR1 : HasTyT E' node.a.family.member.arity
      (policyPrefixContext (cvR.parameters ++ cvR.fields) (cvR.fieldIndex jR).val)
      ((cvR.parameters ++ cvR.fields)[(cvR.fieldIndex jR).val])
      (.sort (cvR.domainsTyped.levels (cvR.fieldIndex jR))) :=
    hasTyTExt (recNode_E0_sub node) dR0
  have hdR : Nonempty (HasTyT E' famO.member.arity
      (policyPrefixContext (cv.parameters ++ cv.fields) k)
      ((cv.parameters ++ cv.fields)[k]'hk)
      (.sort (cvR.domainsTyped.levels (cvR.fieldIndex jR)))) := by
    have hval : (cvR.fieldIndex jR).val = k := congrArg Fin.val hfi.symm
    have hΓeq : policyPrefixContext (cvR.parameters ++ cvR.fields) (cvR.fieldIndex jR).val =
        policyPrefixContext (cv.parameters ++ cv.fields) k := by
      rw [hval, hcat]
    have heeq : (cvR.parameters ++ cvR.fields)[(cvR.fieldIndex jR).val] =
        (cv.parameters ++ cv.fields)[k]'hk := by
      simp only [hval, hcat]
    exact ⟨hasTyT_cast harO.symm hΓeq heeq dR1⟩
  refine ⟨hΓ, hdO, cvR.domainsTyped.levels (cvR.fieldIndex jR), hdR, ?_⟩
  rw [hlvO]
  exact hbdR

/-- Level `leN` compatibility with `eqN` on the left. -/
theorem leN_of_eqN_leN {u v w : Level} (heq : eqN u v) (hle : leN v w) : leN u w :=
  fun ρ x y hx hy => hle ρ x y ((heq ρ).symm.trans hx) hy

/-- **Exact telescope-gap one-sided sort bound (`GapSortLeAt`)**: at every gap position
    `np ≤ k < cv.parameters.length`, whenever `E'` types the entry `(cv.parameters ++ cv.fields)[k]`
    at `.sort uR` with `uR` bounded by `famO.resultLevel`, the constructor view's own level
    `cv.domainsTyped.levels ⟨k, hk⟩` is also bounded by `famO.resultLevel`. -/
def GapSortLeAt (np : Nat) (E' : ResolvedEnv) (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew)
    (m : CheckedMember) (cv : PolicyConstructorView Ew famO m) : Prop :=
  ∀ (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length),
    np ≤ k → k < cv.parameters.length →
    ∀ (uR : Level),
      HasTyT E' famO.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) k)
        ((cv.parameters ++ cv.fields)[k]'hk) (.sort uR) →
      (UniformProp famO.resultLevel ∨ leN uR famO.resultLevel) →
      UniformProp famO.resultLevel ∨ leN (cv.domainsTyped.levels ⟨k, hk⟩) famO.resultLevel

/-- **Boundary equivalence at a single constructor (`AgreeAt ↔ GapSortLeAt`)**. -/
theorem agreeAt_iff_gapSortLeAt {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    {Ew : ResolvedEnv} {r : Nat} {m : CheckedMember} (famO : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew famO m) (htyped : CtorTypedT cv)
    (hin : (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)])
    (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m') :
    AgreeAt node.a.family.parameters.length Ew famO m cv ↔
      GapSortLeAt node.a.family.parameters.length E' Ew famO m cv := by
  constructor
  · intro hag k hk hge hlt _ _ _
    exact hag k hk hge hlt
  · intro hleAt k hk hge hlt
    obtain ⟨_, _, uR, ⟨hdR⟩, hbdR⟩ :=
      walk_entry_double_typed hE hfam hctors hrec hmem hWR node famO cv htyped hin hEw k hk hge
    exact hleAt k hk hge hlt uR hdR hbdR

theorem walkAgree_agreeAt_iff_gapSortLeAt_aux {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm) {S : ResolvedEnv} :
    {Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S Ew ms E'') →
    (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
    (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
    (WalkAgree (AgreeAt node.a.family.parameters.length) hw ↔
      WalkAgree (GapSortLeAt node.a.family.parameters.length E') hw)
  | _, _, _, .nil _, _, _ => Iff.rfl
  | Ew, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest, hms, hsub => by
      have hin := hms (r, m) (List.mem_cons_self _ _)
      have hsubR : ∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
      have hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
      have ih := walkAgree_agreeAt_iff_gapSortLeAt_aux hE hfam hctors hrec hmem hWR node hrest
        (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub
      refine and_congr ?_ ih
      cases hadm with
      | family _ _ _ _ _ => exact Iff.rfl
      | recursor _ _ _ _ _ _ _ => exact Iff.rfl
      | constructor famO view _ _ _ _ _ =>
          exact agreeAt_iff_gapSortLeAt hE hfam hctors hrec hmem hWR node famO view htyped.2 hin hEw

/-- **Exact boundary equivalence for `stepW` under `WalkRec`**:
    `WalkAgree (AgreeAt node.a.family.parameters.length) hmem` (`stepW`'s conclusion) is logically
    equivalent (`↔`) to `WalkAgree (GapSortLeAt node.a.family.parameters.length E') hmem`. -/
theorem walkAgree_agreeAt_iff_gapSortLeAt {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem ↔
      WalkAgree (GapSortLeAt node.a.family.parameters.length E') hmem :=
  walkAgree_agreeAt_iff_gapSortLeAt_aux hE hfam hctors hrec hmem hWR node hmem
    (fun _ h => h) (fun _ _ h => h)

/-! ### §4.1 Route W1: Unconditional `stepW` discharge for `Prop`-valued families (`UniformProp`) -/

/-- **Route W1 (`stepW_of_uniformProp`)**: for ANY `Prop`-valued family
    (`UniformProp node.a.family.resultLevel`, including `RevEnv`, `Eq`, `Acc`, `And`, `Or`, etc.),
    `WalkAgree (AgreeAt node.a.family.parameters.length) hmem` holds **unconditionally** from
    `WalkRec hmem` with **zero row premises** (`SortRowField` / `PiRowField` not needed). -/
theorem stepW_of_uniformProp {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hU : UniformProp node.a.family.resultLevel) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  rw [walkAgree_agreeAt_iff_gapSortLeAt hE hfam hctors hrec hmem hWR node]
  have go : ∀ {S Ew E'' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
      (hw : GroupMembersT S Ew ms E''),
      (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
      (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
      WalkAgree (GapSortLeAt node.a.family.parameters.length E') hw := by
    intro S Ew E'' ms hw
    induction hw with
    | nil _ => intros; trivial
    | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ hrest ih =>
        intro hms hsub
        have hin := hms (r, m) (List.mem_cons_self _ _)
        have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
        have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
        refine ⟨?_, ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub⟩
        cases hadm with
        | family _ _ _ _ _ => trivial
        | recursor _ _ _ _ _ _ _ => trivial
        | constructor famO view _ _ _ _ _ =>
            obtain ⟨_, _, _, _, hlvO, _⟩ :=
              walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO view hin hEw
            exact fun _ _ _ _ _ _ _ => Or.inl (hlvO ▸ hU)
  exact go hmem (fun _ h => h) (fun _ _ h => h)

/-! ### §4.2 Route W2: `SortRowField` / `SortRowFieldLok`-only `stepW` discharge on `NoAppLit` gap entries -/

/-- Expressions free of `.app`, `.letE`, and `.lit` (built from `.sort`, `.bvar`, `.const`, `.pi`,
    and `.lam`). -/
inductive NoAppLit : Expr Nat → Prop
  | sort (l : Level) : NoAppLit (.sort l)
  | bvar (i : Nat) : NoAppLit (.bvar i)
  | const (r : Nat) (ls : List Level) : NoAppLit (.const r ls)
  | pi {A B : Expr Nat} : NoAppLit A → NoAppLit B → NoAppLit (.pi A B)
  | lam {A b : Expr Nat} : NoAppLit A → NoAppLit b → NoAppLit (.lam A b)

/-- Type uniqueness on `NoAppLit` from `SortRowField` alone (zero `PiRowField`, zero `FamAppRowField`). -/
def tyConvT_unique_of_noAppLit {E : ResolvedEnv} {n : Nat} (hSort : SortRowField E n) :
    {Γ : LCtx} → CtxWfT E n Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    NoAppLit e → {B : Expr Nat} → HasTyT E n Γ e B → Nonempty (TyConvT E n Γ A B)
  | _, _, _, _, .sort _ l, _, _, hB => ⟨hasTyTInv_sortT hB rfl⟩
  | _, _, _, _, .bvar _ _ _ h, _, _, hB => by
      obtain ⟨A', hlk', hcv⟩ := hasTyTInv_bvar hB rfl
      obtain rfl : A' = _ := Option.some.inj (hlk'.symm.trans h)
      exact ⟨hcv⟩
  | _, _, _, _, .const _ _ _ _ hres _ _, _, _, hB => by
      obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const hB rfl
      obtain rfl : m' = _ := Option.some.inj (hres'.symm.trans hres)
      exact ⟨hcv⟩
  | Γ, hΓ, _, _, .pi _ A u _ _ hA hB, .pi hnoA hnoB, _, hBt => by
      obtain ⟨u', v', hA', hB', hcv⟩ := hasTyTInv_pi hBt rfl
      obtain ⟨cA⟩ := tyConvT_unique_of_noAppLit hSort hΓ hA hnoA hA'
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := tyConvT_unique_of_noAppLit hSort hΓA hB hnoB hB'
      exact ⟨.trans _ _ _ _
        (.of _ _ _ _ (ConvT.sorts _ _ _
          (Ann.eqNA_imax (hSort hΓ cA) (hSort hΓA cB)))) hcv⟩
  | Γ, hΓ, _, _, .lam _ A u _ _ hA hb, .lam _ hnob, _, hBt => by
      obtain ⟨_, B', _, hb', hcv⟩ := hasTyTInv_lam hBt rfl
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := tyConvT_unique_of_noAppLit hSort hΓA hb hnob hb'
      exact ⟨.trans _ _ _ _ (tyConvT_pi_cod hA cB) hcv⟩
  | _, _, _, _, .app _ _ _ _ _ _ _, hno, _, _ => nomatch hno
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _, hno, _, _ => nomatch hno
  | _, _, _, _, .lit _ _ _ _, hno, _, _ => nomatch hno
  | _, hΓ, _, _, .conv _ _ _ _ _ h hc, hno, _, hBt => by
      obtain ⟨c⟩ := tyConvT_unique_of_noAppLit hSort hΓ h hno hBt
      exact ⟨.trans _ _ _ _ (TyConvT.symmT (.of _ _ _ _ hc)) c⟩

/-- Every gap entry (`np ≤ k < cv.parameters.length`) of `cv` lies in `NoAppLit`. -/
def GapEntriesNoAppLit (np : Nat) (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew)
    (m : CheckedMember) (cv : PolicyConstructorView Ew famO m) : Prop :=
  ∀ (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length),
    np ≤ k → k < cv.parameters.length → NoAppLit ((cv.parameters ++ cv.fields)[k]'hk)

/-- **Route W2 (`stepW_of_noAppLit_sortRow`)**: `SortRowField` alone discharges `stepW`
    (`WalkAgree (AgreeAt node.a.family.parameters.length) hmem`) whenever the gap entries are
    `NoAppLit` (zero `PiRowField`, zero `FamAppRowField`). -/
theorem stepW_of_noAppLit_sortRow {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hSort : SortRowField E' node.a.family.member.arity)
    (hno : WalkAgree (GapEntriesNoAppLit node.a.family.parameters.length) hmem) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  have go : ∀ {S Ew E'' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
      (hw : GroupMembersT S Ew ms E''),
      (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
      (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
      WalkAgree (GapEntriesNoAppLit node.a.family.parameters.length) hw →
      WalkAgree (AgreeAt node.a.family.parameters.length) hw := by
    intro S Ew E'' ms hw
    induction hw with
    | nil _ => intros; trivial
    | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest ih =>
        intro hms hsub hnoW
        obtain ⟨hnoC, hnoRest⟩ := hnoW
        have hin := hms (r, m) (List.mem_cons_self _ _)
        have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
        have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
        refine ⟨?_, ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub hnoRest⟩
        cases hadm with
        | family _ _ _ _ _ => trivial
        | recursor _ _ _ _ _ _ _ => trivial
        | constructor famO view _ _ _ _ _ =>
            obtain ⟨_, _, _, _, _, harO⟩ :=
              walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO view hin hEw
            have hSort' : SortRowField E' famO.member.arity := harO ▸ hSort
            intro k hk hge hlt
            obtain ⟨⟨hΓ⟩, ⟨hdO⟩, uR, ⟨hdR⟩, hbdR⟩ :=
              walk_entry_double_typed hE hfam hctors hrec hmem hWR node famO view htyped.2 hin hEw k hk hge
            have heq : eqN (view.domainsTyped.levels ⟨k, hk⟩) uR :=
              (tyConvT_unique_of_noAppLit hSort' hΓ hdO (hnoC k hk hge hlt) hdR).elim
                fun c => hSort' hΓ c
            rcases hbdR with hP | hle
            · exact Or.inl hP
            · exact Or.inr (leN_of_eqN_leN heq hle)
  exact go hmem (fun _ h => h) (fun _ _ h => h) hno

/-- **Route W2 (`stepW_of_noAppLit_sortRowFieldLok`)**: `∀ N K, SortRowFieldLok` alone discharges
    `stepW` on `NoAppLit` gap entries. -/
theorem stepW_of_noAppLit_sortRowFieldLok (σ : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hSort : ∀ N K, SortRowFieldLok σ N K E' node.a.family.member.arity)
    (hno : WalkAgree (GapEntriesNoAppLit node.a.family.parameters.length) hmem) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_noAppLit_sortRow hE hfam hctors hrec hmem node hWR
    (sortRowField_of_lok_all σ hSort) hno

/-! ### §4.3 Route W3: `SortRowField` + `PiRowField` and `SortRowFieldLok` + `PiRowFieldOvershoot` `stepW` Dischargers -/

/-- Sort uniqueness at any expression from `SortRowField` and `PiRowField` alone (reusing landed
    `DT012T_type_uniqueness_of_sortRow_piRow`, with **zero `FamAppRowField`**). -/
theorem sortUniqueAt_of_sortRow_piRow {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} (hSort : SortRowField E n) (hPi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {T : Expr Nat} {u v : Level}
    (hu : HasTyT E n Γ T (.sort u)) (hv : HasTyT E n Γ T (.sort v)) :
    eqN u v :=
  (DT012T_type_uniqueness_of_sortRow_piRow hW hSort hPi hΓ hu hv).elim fun c => hSort hΓ c

/-- `GapSortLeAt` from `SortRowField` and `PiRowField` alone (zero `FamAppRowField`). -/
theorem gapSortLeAt_of_sortRow_piRow {np : Nat} {E' Ew : ResolvedEnv} (hW' : EnvWfT E')
    {famO : PolicyFamilyView Ew} {m : CheckedMember} {cv : PolicyConstructorView Ew famO m}
    (htyped : CtorTypedT cv) (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m')
    (hSort : SortRowField E' famO.member.arity) (hPi : PiRowField E' famO.member.arity) :
    GapSortLeAt np E' Ew famO m cv := by
  intro k hk _ _ uR hdR hbdR
  have htelE' : TelTypedT E' famO.member.arity (cv.parameters ++ cv.fields) cv.domainsTyped.levels :=
    fun idx => let ⟨d⟩ := htyped.1 idx; ⟨hasTyTExt hEw d⟩
  obtain ⟨hΓ⟩ := ctxWfT_of_telTypedT htelE' k (Nat.le_of_lt hk)
  obtain ⟨hdO⟩ := htelE' ⟨k, hk⟩
  have heq := sortUniqueAt_of_sortRow_piRow hW' hSort hPi hΓ hdO hdR
  rcases hbdR with hP | hle
  · exact Or.inl hP
  · exact Or.inr (leN_of_eqN_leN heq hle)

/-- **Route W3a (`stepW_of_sortRow_piRow`)**: `SortRowField E' arity` + `PiRowField E' arity`
    discharge `stepW` (`WalkAgree (AgreeAt node.a.family.parameters.length) hmem`) for arbitrary
    application-containing gap entries, with **zero `FamAppRowField`**. -/
theorem stepW_of_sortRow_piRow {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hSort : SortRowField E' node.a.family.member.arity)
    (hPi : PiRowField E' node.a.family.member.arity) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  rw [walkAgree_agreeAt_iff_gapSortLeAt hE hfam hctors hrec hmem hWR node]
  have hW' : EnvWfT E' := .group E f fm ctors rr rm E' hE hfam hctors hrec hmem
  have go : ∀ {S Ew E'' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
      (hw : GroupMembersT S Ew ms E''),
      (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
      (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
      WalkAgree (GapSortLeAt node.a.family.parameters.length E') hw := by
    intro S Ew E'' ms hw
    induction hw with
    | nil _ => intros; trivial
    | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest ih =>
        intro hms hsub
        have hin := hms (r, m) (List.mem_cons_self _ _)
        have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
        have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
        refine ⟨?_, ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub⟩
        cases hadm with
        | family _ _ _ _ _ => trivial
        | recursor _ _ _ _ _ _ _ => trivial
        | constructor famO view _ _ _ _ _ =>
            obtain ⟨_, _, _, _, _, harO⟩ :=
              walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO view hin hEw
            exact gapSortLeAt_of_sortRow_piRow hW' htyped.2 hEw (harO ▸ hSort) (harO ▸ hPi)
  exact go hmem (fun _ h => h) (fun _ _ h => h)

/-- **Route W3b (`stepW_of_overshoot_rows`, `RcicF3Layout`-compatible counterpart of
    `walkClassW_of_overshoot_rows`)**:
    `∀ N K, SortRowFieldLok σ N K E' arity` and `∀ N K, PiRowFieldOvershoot σ N K E' arity`
    discharge `stepW` (`WalkAgree (AgreeAt node.a.family.parameters.length) hmem`) via the exact
    equivalences `sortRowField_of_lok_all` and `piRowField_of_overshoot_all`. -/
theorem stepW_of_overshoot_rows (σ : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hSort : ∀ N K, SortRowFieldLok σ N K E' node.a.family.member.arity)
    (hPi : ∀ N K, PiRowFieldOvershoot σ N K E' node.a.family.member.arity) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_sortRow_piRow hE hfam hctors hrec hmem node hWR
    (sortRowField_of_lok_all σ hSort) (piRowField_of_overshoot_all σ hPi)

/-- **Group soundness (`GInv`) from `SortRowFieldLok` and `PiRowFieldOvershoot` (`gInv_group_of_overshoot_rows`)**:
    combines `stepW_of_overshoot_rows` with `RcicF3MainG.gInv_group_of`. -/
theorem gInv_group_of_overshoot_rows (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hGn : GroupClass E E' f rr rm) (hWR : WalkRec hmem)
    (hSort : ∀ (node : RecNode E E' f rr rm) (N : Nat) (K' : Nat → Nat),
      SortRowFieldLok σ N K' E' node.a.family.member.arity)
    (hPi : ∀ (node : RecNode E E' f rr rm) (N : Nat) (K' : Nat → Nat),
      PiRowFieldOvershoot σ N K' E' node.a.family.member.arity)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (IH : GInv P K hE) :
    GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  gInv_group_of P K hE hfam hctors hrec hmem (fun node => (hGn node).1) hWR
    (fun node => stepW_of_overshoot_rows σ hE hfam hctors hrec hmem node hWR (hSort node) (hPi node))
    hB.2.1 hB.2.2.1
    (fun node _ X => recPkg_classG P K node (hGn node).2 (hB.2.2.2 node) X) IH

/-! ### §4.4 Route W4: Unconditional `stepW` Dischargers for `TypedRowsWf`, `InScope`, and `ScopeCheck` Groups -/

/-- `TypedRowsWf E' arity` discharges `stepW` (`WalkAgree (AgreeAt node.a.family.parameters.length) hmem`). -/
theorem stepW_of_typedRowsWf {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hrows : TypedRowsWf E' node.a.family.member.arity) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_sortRow_piRow hE hfam hctors hrec hmem node hWR hrows.sortRow hrows.piRow

/-- **`EnvWfT.InScope` discharges `stepW` unconditionally** (via `sortRowFieldLok_of_inScope` and
    `piRowFieldOvershoot_of_inScope`). -/
theorem stepW_of_inScope {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hIS : (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_overshoot_rows (fun _ => 0) hE hfam hctors hrec hmem node hWR
    (sortRowFieldLok_of_inScope (fun _ => 0)
      (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) hIS node.a.family.member.arity)
    (piRowFieldOvershoot_of_inScope (fun _ => 0)
      (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) hIS node.a.family.member.arity)

/-- **`EnvWfT.ScopeCheck` discharges `stepW` unconditionally** (via `sortRowFieldLok_of_scopeCheck`
    and `piRowFieldOvershoot_of_scopeCheck`). -/
theorem stepW_of_scopeCheck {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hSC : (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).ScopeCheck) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_inScope hE hfam hctors hrec hmem node hWR
    ((EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).inScope_of_scopeCheck hSC)

/-! ## §5 Orthogonality of `PendW` and `InScope` / `ScopeCheck`, and the Exact `stepW` Boundary -/

/-- **Structural independence of `EnvWfT.InScope` from the `GroupMembersT` walk `hmem`**:
    `GroupInScopeT E f fm ctors rr rm` (`RcicAnnEnvBridgeGroup.lean:78`) depends only on the
    stored members `(E, f, fm, ctors, rr, rm)`, never on the per-constructor `IndGroupAdmitted`
    witnesses inside `hmem`. Thus a `PendW` group whose recursor view is in `GroupInScopeT`
    satisfies `InScope` (and hence `SortRowFieldLok`, `PiRowFieldOvershoot`, and `stepW`)
    regardless of `PendW`. -/
theorem inScope_group_iff {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope ↔
      (hE.InScope ∧ Nonempty (GroupInScopeT E f fm ctors rr rm)) :=
  Iff.rfl

/-- **Structural independence of `EnvWfT.ScopeCheck` from `hmem`**. -/
theorem scopeCheck_group_iff {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).ScopeCheck ↔
      (hE.ScopeCheck ∧ ∃ (C : CheckerT) (sk : GroupSkelT),
        groupCheckB C E f fm ctors rr rm sk = true ∧
        ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false) :=
  Iff.rfl

/-- Concrete `GroupSkelT` for the canonical W-class group `V : Prop → Type` (`f = 0`),
    `mk : Π (p : Prop), V p` (`c = 1`), and its `np = 0` indexed recursor (`rr = 2`). -/
def wCanonV : CheckedMember :=
  { mclass := .inductiveM
    arity := 0
    mtype := .pi (.sort .zero) (.sort (.succ .zero))
    body := none }

def wCanonMk : CheckedMember :=
  { mclass := .constructorM
    arity := 0
    mtype := .pi (.sort .zero) (.app (.const 0 []) (.bvar 0))
    body := none }

def wCanonRec : CheckedMember :=
  { mclass := .recursorM
    arity := 1
    mtype :=
      .pi (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort (.param 0))))
        (.pi (.pi (.sort .zero)
            (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0))))
          (.pi (.sort .zero)
            (.pi (.app (.const 0 []) (.bvar 0))
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))
    body := none }

def wCanonSkel : GroupSkelT :=
  (groupSkel? synChecker emptyEnv 4 0 wCanonV [(1, wCanonMk)] wCanonRec 0).get rfl

/-- **Kernel-checked `groupCheckB` certificate for the canonical W-class group (`V : Prop → Type`,
    `mk : Π (p : Prop), V p`, `rec` at `np = 0`)**:
    `groupCheckB synChecker emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec wCanonSkel = true`
    holds by `rfl`. -/
theorem wCanon_groupCheckB :
    groupCheckB synChecker emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec wCanonSkel = true :=
  rfl

/-- Consequently, `GroupInScopeT emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec` is inhabited
     unconditionally, so **any** `EnvWfT.group` derivation over `(emptyEnv, 0, wCanonV, [(1, wCanonMk)], 2, wCanonRec)` —
    including the `PendW` derivation where `wCanonMk` is admitted with `np_c = 1` parameter and
    `wCanonRec` is admitted with `np = 0` parameters — satisfies `ScopeCheck`, `InScope`,
    `TypedRowsWf`, `∀ N K, SortRowFieldLok`, `∀ N K, PiRowFieldOvershoot`, and `stepW`! -/
def wCanon_groupInScopeT : GroupInScopeT emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec :=
  groupInScopeT_of_check wCanonSkel
    (by decide)
    wCanon_groupCheckB

theorem wCanon_inScope_of_group {E' : ResolvedEnv}
    (hfam : wCanonV.mclass = .inductiveM)
    (hctors : ∀ c ∈ [(1, wCanonMk)], c.2.mclass = .constructorM)
    (hrec : wCanonRec.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv emptyEnv 0 wCanonV) emptyEnv
      ((0, wCanonV) :: [(1, wCanonMk)] ++ [(2, wCanonRec)]) E') :
    (EnvWfT.group emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec E' .empty hfam hctors hrec hmem).InScope :=
  ⟨trivial, ⟨wCanon_groupInScopeT⟩⟩

theorem wCanon_sortRowFieldLok_of_group (σ : Nat → Nat) {E' : ResolvedEnv}
    (hfam : wCanonV.mclass = .inductiveM)
    (hctors : ∀ c ∈ [(1, wCanonMk)], c.2.mclass = .constructorM)
    (hrec : wCanonRec.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv emptyEnv 0 wCanonV) emptyEnv
      ((0, wCanonV) :: [(1, wCanonMk)] ++ [(2, wCanonRec)]) E')
    (n N : Nat) (K : Nat → Nat) :
    SortRowFieldLok σ N K E' n :=
  sortRowFieldLok_of_inScope σ
    (.group emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec E' .empty hfam hctors hrec hmem)
    (wCanon_inScope_of_group hfam hctors hrec hmem) n N K

theorem wCanon_piRowFieldOvershoot_of_group (σ : Nat → Nat) {E' : ResolvedEnv}
    (hfam : wCanonV.mclass = .inductiveM)
    (hctors : ∀ c ∈ [(1, wCanonMk)], c.2.mclass = .constructorM)
    (hrec : wCanonRec.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv emptyEnv 0 wCanonV) emptyEnv
      ((0, wCanonV) :: [(1, wCanonMk)] ++ [(2, wCanonRec)]) E')
    (n N : Nat) (K : Nat → Nat) :
    PiRowFieldOvershoot σ N K E' n :=
  piRowFieldOvershoot_of_inScope σ
    (.group emptyEnv 0 wCanonV [(1, wCanonMk)] 2 wCanonRec E' .empty hfam hctors hrec hmem)
    (wCanon_inScope_of_group hfam hctors hrec hmem) n N K

theorem wCanon_stepW_of_group {E' : ResolvedEnv}
    (hfam : wCanonV.mclass = .inductiveM)
    (hctors : ∀ c ∈ [(1, wCanonMk)], c.2.mclass = .constructorM)
    (hrec : wCanonRec.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv emptyEnv 0 wCanonV) emptyEnv
      ((0, wCanonV) :: [(1, wCanonMk)] ++ [(2, wCanonRec)]) E')
    (node : RecNode emptyEnv E' 0 2 wCanonRec) (hWR : WalkRec hmem) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_inScope .empty hfam hctors hrec hmem node hWR
    (wCanon_inScope_of_group hfam hctors hrec hmem)

/-- **Exact boundary characterization of `stepW` at a `WalkRec` group (`stepW_boundary_iff`)**:
    for any group step `EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem` and
    `node : RecNode E E' f rr rm` with `WalkRec hmem`, `WalkAgree (AgreeAt node.a.family.parameters.length) hmem`
    holds if and only if either:
    1. `UniformProp node.a.family.resultLevel` (a `Prop`-valued family, where `stepW_of_uniformProp`
       holds unconditionally with zero row premises), or
    2. `UniformType node.a.family.resultLevel` (a `Type`-valued family) and
       `WalkAgree (GapSortLeAt node.a.family.parameters.length E') hmem` holds (which is discharged
       by `stepW_of_inScope` / `stepW_of_scopeCheck` for every in-scope group, by
       `stepW_of_noAppLit_sortRowFieldLok` for `NoAppLit` gap entries under `SortRowFieldLok`, and
       by `stepW_of_overshoot_rows` under `SortRowFieldLok` + `PiRowFieldOvershoot`). -/
theorem stepW_boundary_iff {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem ↔
      (UniformProp node.a.family.resultLevel ∨
        (UniformType node.a.family.resultLevel ∧
          WalkAgree (GapSortLeAt node.a.family.parameters.length E') hmem)) := by
  constructor
  · intro hAg
    cases hpol : node.a.policy with
    | anySort =>
        rcases (EliminationSelection.anySort_iff _ _ _).mp (hpol ▸ node.a.selected) with hT | ⟨hP, _⟩
        · exact Or.inr ⟨hT, (walkAgree_agreeAt_iff_gapSortLeAt hE hfam hctors hrec hmem hWR node).mp hAg⟩
        · exact Or.inl hP
    | propOnly =>
        exact Or.inl ((EliminationSelection.propOnly_iff _ _ _).mp (hpol ▸ node.a.selected)).1
  · rintro (hP | ⟨_, hGap⟩)
    · exact stepW_of_uniformProp hE hfam hctors hrec hmem node hWR hP
    · exact (walkAgree_agreeAt_iff_gapSortLeAt hE hfam hctors hrec hmem hWR node).mpr hGap

end Rcic.Syn.FamApp.StepW
