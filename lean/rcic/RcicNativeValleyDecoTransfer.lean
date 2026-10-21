import rcic.RcicNativeValleyDecoRows
import rcic.RcicParRedTPiHead
import rcic.RcicNativeWallProducer
import rcic.RcicTypedRowsWf

/-!
# RcicNativeValleyDecoTransfer — `Π-injectivity_D` and Decoration Transfer
(Wall 1, `NativeConvValleys`, `NATIVE_VALLEYS_STATUS.md` §9c/§9e, Steps 2–4)

This module completes Steps 2, 3, and 4 of the decorated route:

1. **Step 2a (`peq_sort_source_false`, `peq_pi_source_false`, `parRedT_pi_head_reverse_of_zsc`)**:
   Under `HostPropAudit.ZeroSortCoherence E n`, no `PEq` leaf can have a `.sort u` or `.pi A B`
   source: `hasTyTInv_sortT` / `hasTyTInv_pi` combined with `sort_transport0_data` would type a
   sort at `.sort .zero`, contradicting `ZeroSortCoherence`. This discharges the open leaf premise
   of `RcicParRedTPiHead.parRedT_pi_head_reverse_of_leaf` for every `LeafIface E n PEq`.

2. **Step 2b (`parRedT_sort_inv_of_zsc`, `cstar_sort_inv_of_zsc`, `valleyJoin_sort_inv_of_zsc`,
   `cvalley_sort_inv_of_zsc`, `parRedT_pi_inv_of_zsc`, `cstar_pi_inv_of_zsc`,
   `valleyJoin_pi_inv_of_zsc`, `cvalley_pi_inv_of_zsc`)**:
   * Every `ParRedT` / `ParRedTStar` / `CStar` out of `.sort u` preserves the `.sort` head and
     accumulates `eqN`; hence any `ValleyJoin` or `CValley` between `.sort u₁` and `.sort u₂`
     extracts `eqN u₁ u₂` (`valleyJoin_sort_inv_of_zsc`, `cvalley_sort_inv_of_zsc`).
   * Every `ParRedT` / `ParRedTStar` / `CStar` out of `.pi A B` preserves the `.pi` head and
     accumulates `TyConvT` chains on the domain and codomain (transported along the domain chain by
     `tyConvT_assump_dom`); hence any `ValleyJoin` or `CValley` between `.pi A₁ B₁` and `.pi A₂ B₂`
     extracts `TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂`
     (`valleyJoin_pi_inv_of_zsc`, `cvalley_pi_inv_of_zsc`).
   * Plugging `valleyOf_diamond` (`RcicNativeWallProducer`) into `cvalley_sort_inv_of_zsc` and
     `cvalley_pi_inv_of_zsc` extracts `eqN` and component `TyConvT`s from any single `ConvT`
     between two sorts or two Π-types (`convT_sort_inv_of_diamond`, `convT_pi_inv_of_diamond`).

3. **Step 2c (`SortCoh`, `SortUniq`, `SortRetype`, `PiInj`, `cvalley_of_tyConvT_of_sortRetype`,
   `sortCoh_of_diamond_sortUniq`, `piInj_of_diamond_sortUniq`, `piRow_of_diamond_sortUniq`)**:
   * Under `CDiamond E n PEq` and `SortRetype E n` (supplied by `SortUniq E n` or `Uniq E n`), any
     `TyConvT E n Γ X Y` with `X : .sort w` collapses to a single `CValley E n PEq Γ X Y (.sort w)`,
     yielding full `SortCoh E n` (`TypedRowsWf.sortRow`) and `PiInj E n` (`TypedRowsWf.piRow`).
   * Note: `PiInj E n` (`TyConvT` Π-injectivity) is a **named hypothesis** in Step 3; its only
     producers in this module (`piInj_of_diamond_sortRetype`, `piInj_of_diamond_sortUniq`) consume
     `CDiamond E n PEq`, so the `CR_D ⇒ PiInj` arrow is an open residue.

4. **Step 3 (`uniq_of_piInj_sortUniq`, `uniq_of_piInj_sortCoh`, `retype_of_piInj_sortUniq`,
   `retype_of_piInj_sortCoh`)**:
   Shows how `PiInj E n` pays for type uniqueness across distinct decorations: for ANY two typing
   derivations `h₁ : HasTyT E n Γ e T₁` and `h₂ : HasTyT E n Γ e T₂` of one term `e` — even with
   different decorations `decoOf h₁ ≠ decoOf h₂` (such as the two typings of the middle term of
   `ConvT.trans`) — structural recursion on `sizeOf h₁ + sizeOf h₂` gives `TyConvT E n Γ T₁ T₂`
   (`Uniq E n`, DT-012's shape). At `.app _ f a A₁ B₁ hf₁ ha₁` vs `.app _ f a A₂ B₂ hf₂ ha₂`, the
   induction hypothesis on `hf₁` and `hf₂` produces `TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)`,
   `PiInj E n` extracts `TyConvT E n (.assumption A₁ :: Γ) B₁ B₂`, and `tyConvT_subst0_of_envWfT`
   substitutes `ha₁` to relate `instantiate0 a B₁` and `instantiate0 a B₂`. Consequently, a
   certified step re-types (index only; `stepDeco` is preserved by `stepDeco_reindex`) to any other
   typing of its source via `CStep.reindex` (`retype_of_piInj_sortUniq`,
   `retype_of_piInj_sortCoh : Retype E n PEq`).

5. **Step 4 (`StepDecoTransfer` and non-`peq` constructor combinators)**:
   `StepDecoTransfer E n PEq L` names the single-step source-decoration transfer contract. For a
   generic lawful `LeafIface`, `StepDecoTransfer` is refuted at `peq` by `#7600`
   (`admitted_single_step_transfer_false`), so there is no `peq` combinator and no generic-`L`
   assembler in this module; the per-constructor combinators (`stepDecoTransfer_*`) cover the
   non-`peq` constructors using `PiInj`, `SortUniq`, and two-level inner+outer `CStep.reindex`.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### `TyConvT` context transport and level congruence -/

/-- Full two-argument congruence of `eqN` under `Level.imax`. -/
theorem eqN_imax_both {u₁ u₂ v₁ v₂ : Level} (hu : eqN u₁ u₂) (hv : eqN v₁ v₂) :
    eqN (.imax u₁ v₁) (.imax u₂ v₂) := by
  intro ρ
  simp only [eval, hu ρ, hv ρ]

/-- Transporting a `TyConvT` chain along `CtxConvT`. -/
def tyConvT_ctx (hcl : EnvClosed E) {Γ Γ' : LCtx} (hctx : CtxConvT E n Γ Γ') :
    {X Y : Expr Nat} → TyConvT E n Γ X Y → TyConvT E n Γ' X Y
  | _, _, .refl _ X => .refl Γ' X
  | _, _, .of _ X Y u hc => .of Γ' X Y u (convT_ctx hcl hctx hc)
  | _, _, .trans _ X M Y c₁ c₂ =>
      .trans Γ' X M Y (tyConvT_ctx hcl hctx c₁) (tyConvT_ctx hcl hctx c₂)

/-- Transporting a codomain `TyConvT` chain from `.assumption A₂ :: Γ` to `.assumption A₁ :: Γ`
    along a domain chain `TyConvT E n Γ A₁ A₂`. -/
def tyConvT_assump_dom (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A₁ A₂ : Expr Nat} → TyConvT E n Γ A₁ A₂ →
    {X Y : Expr Nat} → TyConvT E n (.assumption A₂ :: Γ) X Y →
    TyConvT E n (.assumption A₁ :: Γ) X Y
  | _, _, .refl _ _, _, _, c => c
  | _, _, .of _ _ _ _ hc, _, _, c =>
      let ends := convEnds hW hΓ hc
      let hctx : CtxConvT E n (.assumption _ :: Γ) (.assumption _ :: Γ) :=
        .assumption (ctxConvT_refl Γ) ends.2.1 ends.1 (.symm _ _ _ _ hc)
      tyConvT_ctx (envClosed_of_envWfT hW) hctx c
  | _, _, .trans _ _ _ _ c₁ c₂, _, _, c =>
      tyConvT_assump_dom hW hΓ c₁ (tyConvT_assump_dom hW hΓ c₂ c)

/-! ### Step 2a: `PEq` leaf impossibility at `.sort` and `.pi` sources under `ZeroSortCoherence` -/

/-- Neither `DerivedIotaU` arm can have a `.sort` left-hand side. -/
theorem derivedIotaU_sort_source_false {lhs rhs : Expr Nat} {u : Level}
    (h : DerivedIotaU E lhs rhs) (heq : lhs = .sort u) : False := by
  cases h with
  | ofU w =>
      exact foldApps_snoc_ne_sort (.const w.recRef w.ls) (ctorMajor w) w.preMajor heq
  | ofUS w =>
      exact foldApps_snoc_ne_sort (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) w.preMajor heq

/-- Neither `DerivedIotaU` arm can have a `.pi` left-hand side. -/
theorem derivedIotaU_pi_source_false' {lhs rhs A B : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (heq : lhs = .pi A B) : False := by
  cases h with
  | ofU w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls) (ctorMajor w) w.preMajor heq
  | ofUS w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) w.preMajor heq

/-- Under `ZeroSortCoherence`, no `PEq` leaf can have source `.sort u`. -/
theorem peq_sort_source_false (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u : Level} {q T : Expr Nat} (h : PEq Γ (.sort u) q T) : False := by
  have c := hasTyTInv_sortT (L.typed h).1 rfl
  have h0 := HostPropAudit.sort_transport0_data hW zsc hΓ c.symmT (L.prop h)
  have heq : eqN (.succ (.succ u)) .zero := zsc hW hΓ (.sort Γ (.succ u)) h0
  have hρ := heq (fun _ => none)
  change (eval (fun _ => none) (.succ u)).map (fun k => k + 1) = some 0 at hρ
  cases hu : eval (fun _ => none) (.succ u) <;> simp [hu] at hρ

/-- Under `ZeroSortCoherence`, no `PEq` leaf can have source `.pi A B`. -/
theorem peq_pi_source_false (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B q T : Expr Nat} (h : PEq Γ (.pi A B) q T) : False := by
  obtain ⟨u, v, _, _, c⟩ := hasTyTInv_pi (L.typed h).1 rfl
  have h0 := HostPropAudit.sort_transport0_data hW zsc hΓ c.symmT (L.prop h)
  have heq : eqN (.succ (.imax u v)) .zero := zsc hW hΓ (.sort Γ (.imax u v)) h0
  have hρ := heq (fun _ => none)
  change (eval (fun _ => none) (.imax u v)).map (fun k => k + 1) = some 0 at hρ
  cases hu : eval (fun _ => none) (.imax u v) <;> simp [hu] at hρ

/-- Discharging the leaf premise of `RcicParRedTPiHead.parRedT_pi_head_reverse_of_leaf` under
    `ZeroSortCoherence`: every `ParRedT` step out of `.pi A B` preserves the `.pi` head and
    reverses at the same index. -/
def parRedT_pi_head_reverse_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B b T : Expr Nat} (p : ParRedT PEq E n Γ (.pi A B) b T) :
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×' ParRedT PEq E n Γ b (.pi A B) T :=
  parRedT_pi_head_reverse_of_leaf hW hΓ
    (fun h => (peq_pi_source_false hW L zsc hΓ h).elim) p rfl

/-! ### Step 2b: Sort and Π head inversion along `ParRedT`, `ParRedTStar`, `CStar`, `ValleyJoin`,
    and `CValley` -/

/-- Every `ParRedT` step out of `.sort u` preserves the `.sort` head and yields `eqN`, provided
    any `PEq` leaf at `.sort u` does. -/
def parRedT_sort_inv_of_leaf {Γ : LCtx}
    (hLeaf : ∀ {u : Level} {q T : Expr Nat}, PEq Γ (.sort u) q T →
      Σ' (u' : Level), (q = .sort u') ×' eqN u u') :
    {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {u : Level} → a = .sort u →
    Σ' (u' : Level), (b = .sort u') ×' eqN u u'
  | _, _, _, .refl _ _ _ _, u, heq => by
      subst heq
      exact ⟨u, rfl, eqN_refl u⟩
  | _, _, _, .sortEq _ u₀ u' _ h _ _, u, heq => by
      injection heq with hueq
      subst hueq
      exact ⟨u', rfl, h⟩
  | _, _, _, .consts .., _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app .., _, heq => nomatch heq
  | _, _, _, .beta .., _, heq => nomatch heq
  | _, _, _, .lam .., _, heq => nomatch heq
  | _, _, _, .pi .., _, heq => nomatch heq
  | _, _, _, .letE .., _, heq => nomatch heq
  | _, _, _, .zeta .., _, heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, heq => by
      let ⟨_, hhead, _⟩ := parRedT_sort_inv_of_leaf hLeaf hstep heq
      exact False.elim (derivedIotaU_sort_source_false hI hhead)
  | _, _, _, .iotaStarK .., _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .lit .., _, heq => nomatch heq
  | _, _, _, .eta .., _, heq => nomatch heq
  | _, _, _, .peq _ _ _ _ h, _, heq => by
      subst heq
      exact hLeaf h
  | _, _, _, .conv _ _ _ _ _ h _, _, heq =>
      parRedT_sort_inv_of_leaf hLeaf h heq

/-- Under `ZeroSortCoherence`, every `ParRedT` step out of `.sort u` lands at `.sort u'` with
    `eqN u u'`. -/
def parRedT_sort_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (p : ParRedT PEq E n Γ a b T) {u : Level} (heq : a = .sort u) :
    Σ' (u' : Level), (b = .sort u') ×' eqN u u' :=
  parRedT_sort_inv_of_leaf (fun h => (peq_sort_source_false hW L zsc hΓ h).elim) p heq

/-- Under `ZeroSortCoherence`, every `ParRedTStar` out of `.sort u` lands at `.sort u'` with
    `eqN u u'`. -/
def parRedTStar_sort_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → ParRedTStar PEq E n Γ a b T →
    {u : Level} → a = .sort u →
    Σ' (u' : Level), (b = .sort u') ×' eqN u u'
  | _, _, _, .refl _ _ _ _, u, heq => by
      subst heq
      exact ⟨u, rfl, eqN_refl u⟩
  | _, _, _, .tail s hs, _, heq =>
      let ⟨_, hmid, hu₁⟩ := parRedT_sort_inv_of_zsc hW L zsc hΓ s heq
      let ⟨u', hhead, hu₂⟩ := parRedTStar_sort_inv_of_zsc hW L zsc hΓ hs hmid
      ⟨u', hhead, eqN_trans hu₁ hu₂⟩

/-- Under `ZeroSortCoherence`, every `CStar` out of `.sort u` lands at `.sort u'` with
    `eqN u u'`. -/
def cstar_sort_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u : Level} {b T : Expr Nat} (s : CStar E n PEq Γ (.sort u) b T) :
    Σ' (u' : Level), (b = .sort u') ×' eqN u u' :=
  parRedTStar_sort_inv_of_zsc hW L zsc hΓ s.forget rfl

/-- Any `ValleyJoin` between `.sort u₁` and `.sort u₂` extracts `eqN u₁ u₂` under
    `ZeroSortCoherence`. -/
theorem valleyJoin_sort_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u₁ u₂ : Level} {T₁ T₂ : Expr Nat}
    (V : ValleyJoin E n PEq Γ (.sort u₁) (.sort u₂) T₁ T₂) : eqN u₁ u₂ := by
  obtain ⟨u_c, h₁, hu₁⟩ := cstar_sort_inv_of_zsc hW L zsc hΓ V.2.1
  obtain ⟨u_c', h₂, hu₂⟩ := cstar_sort_inv_of_zsc hW L zsc hΓ V.2.2
  have heq : Expr.sort u_c = Expr.sort u_c' := h₁.symm.trans h₂
  injection heq with huc
  subst huc
  exact eqN_trans hu₁ (eqN_symm hu₂)

/-- Any `CValley` between `.sort u₁` and `.sort u₂` extracts `eqN u₁ u₂` under
    `ZeroSortCoherence`. -/
theorem cvalley_sort_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u₁ u₂ : Level} {T : Expr Nat}
    (V : CValley E n PEq Γ (.sort u₁) (.sort u₂) T) : eqN u₁ u₂ :=
  valleyJoin_sort_inv_of_zsc hW L zsc hΓ ⟨V.centre, V.left, V.right⟩

/-- Every `ParRedT` step out of `.pi A B` preserves the `.pi` head and extracts domain and
    codomain `TyConvT` chains, provided any `PEq` leaf at `.pi A B` does. -/
def parRedT_pi_inv_of_leaf {Γ : LCtx}
    (hLeaf : ∀ {A B q T : Expr Nat}, PEq Γ (.pi A B) q T →
      Σ' (A' B' : Expr Nat), (q = .pi A' B') ×'
        TyConvT E n Γ A A' ×' TyConvT E n (.assumption A :: Γ) B B') :
    {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {A B : Expr Nat} → a = .pi A B →
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×'
      TyConvT E n Γ A A' ×' TyConvT E n (.assumption A :: Γ) B B'
  | _, _, _, .refl _ _ _ _, A, B, heq => by
      subst heq
      exact ⟨A, B, rfl, .refl Γ A, .refl (.assumption A :: Γ) B⟩
  | _, _, _, .sortEq .., _, _, heq => nomatch heq
  | _, _, _, .consts .., _, _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, .beta .., _, _, heq => nomatch heq
  | _, _, _, .lam .., _, _, heq => nomatch heq
  | _, _, _, .pi _ A₀ A' B₀ B' u v _ hc _ hcB _, _, _, heq => by
      injection heq with hAeq hBeq
      subst hAeq; subst hBeq
      exact ⟨A', B', rfl, .of Γ A₀ A' u hc, .of (.assumption A₀ :: Γ) B₀ B' v hcB⟩
  | _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, .zeta .., _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, heq => by
      let ⟨_, _, hhead, _⟩ := parRedT_pi_inv_of_leaf hLeaf hstep heq
      exact False.elim (derivedIotaU_pi_source_false' hI hhead)
  | _, _, _, .iotaStarK .., _, _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .lit .., _, _, heq => nomatch heq
  | _, _, _, .eta .., _, _, heq => nomatch heq
  | _, _, _, .peq _ _ _ _ h, _, _, heq => by
      subst heq
      exact hLeaf h
  | _, _, _, .conv _ _ _ _ _ h _, _, _, heq =>
      parRedT_pi_inv_of_leaf hLeaf h heq

/-- Under `ZeroSortCoherence`, every `ParRedT` step out of `.pi A B` lands at `.pi A' B'` with
    domain and codomain `TyConvT` chains. -/
def parRedT_pi_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (p : ParRedT PEq E n Γ a b T) {A B : Expr Nat} (heq : a = .pi A B) :
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×'
      TyConvT E n Γ A A' ×' TyConvT E n (.assumption A :: Γ) B B' :=
  parRedT_pi_inv_of_leaf (fun h => (peq_pi_source_false hW L zsc hΓ h).elim) p heq

/-- Under `ZeroSortCoherence`, every `ParRedTStar` out of `.pi A B` lands at `.pi A' B'` with
    domain and codomain `TyConvT` chains. -/
def parRedTStar_pi_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → ParRedTStar PEq E n Γ a b T →
    {A B : Expr Nat} → a = .pi A B →
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×'
      TyConvT E n Γ A A' ×' TyConvT E n (.assumption A :: Γ) B B'
  | _, _, _, .refl _ _ _ _, A, B, heq => by
      subst heq
      exact ⟨A, B, rfl, .refl Γ A, .refl (.assumption A :: Γ) B⟩
  | _, _, _, .tail s hs, A, B, heq =>
      let ⟨A₁, B₁, hmid, hcA₁, hcB₁⟩ := parRedT_pi_inv_of_zsc hW L zsc hΓ s heq
      let ⟨A', B', hhead, hcA₂, hcB₂⟩ := parRedTStar_pi_inv_of_zsc hW L zsc hΓ hs hmid
      ⟨A', B', hhead,
        .trans Γ A A₁ A' hcA₁ hcA₂,
        .trans (.assumption A :: Γ) B B₁ B' hcB₁ (tyConvT_assump_dom hW hΓ hcA₁ hcB₂)⟩

/-- Under `ZeroSortCoherence`, every `CStar` out of `.pi A B` lands at `.pi A' B'` with domain
    and codomain `TyConvT` chains. -/
def cstar_pi_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B b T : Expr Nat} (s : CStar E n PEq Γ (.pi A B) b T) :
    Σ' (A' B' : Expr Nat), (b = .pi A' B') ×'
      TyConvT E n Γ A A' ×' TyConvT E n (.assumption A :: Γ) B B' :=
  parRedTStar_pi_inv_of_zsc hW L zsc hΓ s.forget rfl

/-- Step 2 (`Π-injectivity_D` on valleys): any `ValleyJoin` between `.pi A₁ B₁` and `.pi A₂ B₂`
    extracts `TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂` under
    `ZeroSortCoherence`. -/
def valleyJoin_pi_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ B₁ A₂ B₂ T₁ T₂ : Expr Nat}
    (V : ValleyJoin E n PEq Γ (.pi A₁ B₁) (.pi A₂ B₂) T₁ T₂) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ := by
  obtain ⟨A_c, B_c, h₁, hcA₁, hcB₁⟩ := cstar_pi_inv_of_zsc hW L zsc hΓ V.2.1
  obtain ⟨A_c', B_c', h₂, hcA₂, hcB₂⟩ := cstar_pi_inv_of_zsc hW L zsc hΓ V.2.2
  have heq : Expr.pi A_c B_c = Expr.pi A_c' B_c' := h₁.symm.trans h₂
  injection heq with hAeq hBeq
  subst hAeq; subst hBeq
  let hcA : TyConvT E n Γ A₁ A₂ := .trans Γ A₁ A_c A₂ hcA₁ hcA₂.symmT
  exact (hcA, .trans (.assumption A₁ :: Γ) B₁ B_c B₂ hcB₁
    (tyConvT_assump_dom hW hΓ hcA hcB₂.symmT))

/-- Step 2 (`Π-injectivity_D` on `CValley`): any `CValley` between `.pi A₁ B₁` and `.pi A₂ B₂`
    extracts `TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂` under
    `ZeroSortCoherence`. -/
def cvalley_pi_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ B₁ A₂ B₂ T : Expr Nat}
    (V : CValley E n PEq Γ (.pi A₁ B₁) (.pi A₂ B₂) T) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ :=
  valleyJoin_pi_inv_of_zsc hW L zsc hΓ ⟨V.centre, V.left, V.right⟩

/-- From `CDiamond` (`valleyOf_diamond`, `#7572`) and `ZeroSortCoherence`, any single `ConvT`
    between `.sort u₁` and `.sort u₂` yields `eqN u₁ u₂`. -/
theorem convT_sort_inv_of_diamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u₁ u₂ : Level} {T : Expr Nat}
    (c : ConvT E n Γ (.sort u₁) (.sort u₂) T) : eqN u₁ u₂ :=
  cvalley_sort_inv_of_zsc hW L zsc hΓ (valleyOf_diamond hW L D hΓ c)

/-- From `CDiamond` (`valleyOf_diamond`, `#7572`) and `ZeroSortCoherence`, any single `ConvT`
    between `.pi A₁ B₁` and `.pi A₂ B₂` yields domain and codomain `TyConvT` chains. -/
def convT_pi_inv_of_diamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ B₁ A₂ B₂ T : Expr Nat}
    (c : ConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ :=
  cvalley_pi_inv_of_zsc hW L zsc hΓ (valleyOf_diamond hW L D hΓ c)

/-! ### Step 2c: Full `TyConvT` chain `SortCoh` and `PiInj` -/

/-- Full sort coherence (`TypedRowsWf.sortRow` shape). -/
def SortCoh (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {u v : Level},
    TyConvT E n Γ (.sort u) (.sort v) → eqN u v

/-- Same-term sort uniqueness: two sortings of one type `A` have `=ₙ` levels. -/
def SortUniq (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u v : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ A (.sort v) → eqN u v

/-- Same-term sort retyping: two sortings of one type `A` are connected by `TyConvT` (supplied by
    either `SortUniq` or `Uniq`). -/
def SortRetype (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u v : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ A (.sort v) →
    TyConvT E n Γ (.sort u) (.sort v)

/-- Full `Type`-valued Π-injectivity (`TypedRowsWf.piRow` in `Type`). -/
def PiInj (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat},
    TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) →
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂

/-- `SortUniq` specializes at `v = .zero` to `HostPropAudit.ZeroSortCoherence`. -/
theorem zsc_of_sortUniq (su : SortUniq E n) : HostPropAudit.ZeroSortCoherence E n :=
  fun _ {_ _ _} hΓ hA hA0 => su hΓ hA hA0

/-- `SortUniq` implies `SortRetype` via `ConvT.sorts`. -/
def sortRetype_of_sortUniq (su : SortUniq E n) : SortRetype E n :=
  fun {Γ} hΓ {_ u v} h₁ h₂ =>
    .of Γ (.sort u) (.sort v) (.succ u) (.sorts Γ u v (su hΓ h₁ h₂))

/-- `Uniq` implies `SortRetype`. -/
def sortRetype_of_uniq (U : Uniq E n) : SortRetype E n :=
  fun {_} hΓ {_ _ _} h₁ h₂ => U hΓ h₁ h₂

/-- `Uniq` and `SortCoh` together yield `SortUniq`. -/
theorem sortUniq_of_uniq_sortCoh (U : Uniq E n) (sc : SortCoh E n) : SortUniq E n :=
  fun {_} hΓ {_ _ _} h₁ h₂ => sc hΓ (U hΓ h₁ h₂)

/-- `PiInj` implies the `Prop`-valued `TypedRowsWf.piRow` field. -/
theorem piRow_of_piInj (piInj : PiInj E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  fun {_} hΓ {_ _ _ _} c =>
    let ⟨cA, cB⟩ := piInj hΓ c
    ⟨⟨cA⟩, ⟨cB⟩⟩

/-- Under `CDiamond` and `SortRetype`, any `TyConvT E n Γ X Y` chain with
    `hX : HasTyT E n Γ X (.sort w)` collapses to a single `CValley E n PEq Γ X Y (.sort w)`
    at `.sort w`. -/
def cvalley_of_tyConvT_of_sortRetype (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (sr : SortRetype E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {X Y : Expr Nat} → {w : Level} → HasTyT E n Γ X (.sort w) →
    TyConvT E n Γ X Y → CValley E n PEq Γ X Y (.sort w)
  | _, _, _, hX, .refl _ _ => CValley.refl hX
  | _, _, _, hX, .of _ _ _ _ hc =>
      let V := valleyOf_diamond hW L D hΓ hc
      let hXu := V.left.leftTyped L hΓ
      V.reindex (sr hΓ hXu hX)
  | _, _, _, hX, .trans _ _ _ _ c₁ c₂ =>
      let V₁ := cvalley_of_tyConvT_of_sortRetype hW L D sr hΓ hX c₁
      let hM := V₁.right.leftTyped L hΓ
      let V₂ := cvalley_of_tyConvT_of_sortRetype hW L D sr hΓ hM c₂
      CValley.trans D L hΓ V₁ V₂

/-- Under `CDiamond` and `SortUniq`, any `TyConvT E n Γ X Y` chain with
    `hX : HasTyT E n Γ X (.sort w)` collapses to a single `CValley E n PEq Γ X Y (.sort w)`. -/
def cvalley_of_tyConvT_of_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (su : SortUniq E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {X Y : Expr Nat} {w : Level} (hX : HasTyT E n Γ X (.sort w))
    (c : TyConvT E n Γ X Y) : CValley E n PEq Γ X Y (.sort w) :=
  cvalley_of_tyConvT_of_sortRetype hW L D (sortRetype_of_sortUniq su) hΓ hX c

/-- Under `CDiamond`, `SortRetype`, and `ZeroSortCoherence`, full `SortCoh` (`TypedRowsWf.sortRow`)
    holds. -/
theorem sortCoh_of_diamond_sortRetype (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : SortCoh E n :=
  fun {Γ} hΓ {u _} c =>
    let V := cvalley_of_tyConvT_of_sortRetype hW L D sr hΓ (.sort Γ u) c
    cvalley_sort_inv_of_zsc hW L zsc hΓ V

/-- Under `CDiamond` and `SortUniq`, full `SortCoh` (`TypedRowsWf.sortRow`) holds. -/
theorem sortCoh_of_diamond_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (su : SortUniq E n) : SortCoh E n :=
  sortCoh_of_diamond_sortRetype hW L D (sortRetype_of_sortUniq su) (zsc_of_sortUniq su)

/-- First-step splitting of a `TyConvT` chain in `Type` (`TyConvT.firstOf` lifted to `Type`). -/
def tyConvT_firstOf_data : {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B →
    PSum (A = B) (Σ' (C : Expr Nat) (u : Level), ConvT E n Γ A C (.sort u) ×' TyConvT E n Γ C B)
  | _, _, _, .refl _ _ => .inl rfl
  | _, _, _, .of Γ _ C u hc => .inr ⟨C, u, hc, .refl Γ C⟩
  | _, _, _, .trans Γ _ _ B c₁ c₂ =>
      match tyConvT_firstOf_data c₁ with
      | .inl h => h ▸ tyConvT_firstOf_data c₂
      | .inr ⟨C, u, hc, rest⟩ => .inr ⟨C, u, hc, .trans Γ C _ B rest c₂⟩

/-- Under `CDiamond`, `SortRetype`, and `ZeroSortCoherence`, full `PiInj` (`Type`-valued
    `TypedRowsWf.piRow`) holds: if `c : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)` is pure
    reflexivity, `Expr.pi.inj` gives `A₁ = A₂` and `B₁ = B₂`; otherwise its first `.of` step types
    `.pi A₁ B₁` at a sort `.sort u`, `cvalley_of_tyConvT_of_sortRetype` collapses `c` to a
    `CValley` at `.sort u`, and `cvalley_pi_inv_of_zsc` extracts the domain and codomain `TyConvT`
    chains. -/
def piInj_of_diamond_sortRetype (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : PiInj E n :=
  fun {Γ} hΓ {A₁ B₁ A₂ B₂} c =>
    match tyConvT_firstOf_data c with
    | .inl heq => by
        injection heq with hA hB
        subst hA; subst hB
        exact (.refl Γ A₁, .refl (.assumption A₁ :: Γ) B₁)
    | .inr ⟨_, u, hc₀, _⟩ =>
        let hPi : HasTyT E n Γ (.pi A₁ B₁) (.sort u) := (convEnds hW hΓ hc₀).1
        let V := cvalley_of_tyConvT_of_sortRetype hW L D sr hΓ hPi c
        cvalley_pi_inv_of_zsc hW L zsc hΓ V

/-- Under `CDiamond` and `SortUniq`, full `PiInj` (`Type`-valued `TypedRowsWf.piRow`) holds. -/
def piInj_of_diamond_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (su : SortUniq E n) : PiInj E n :=
  piInj_of_diamond_sortRetype hW L D (sortRetype_of_sortUniq su) (zsc_of_sortUniq su)

/-- Under `CDiamond` and `SortUniq`, `TypedRowsWf.piRow` holds. -/
theorem piRow_of_diamond_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (su : SortUniq E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_piInj (piInj_of_diamond_sortUniq hW L D su)

/-! ### Step 3: Decoration Transfer — how `Π-injectivity` pays for `Uniq` and `Retype` -/

/-- Step 3 (Decoration Transfer from `PiInj` and `SortUniq`):
    ANY two typing derivations `h₁ : HasTyT E n Γ e T₁` and `h₂ : HasTyT E n Γ e T₂` of one term `e`
    — even with completely unrelated decorations `decoOf h₁ ≠ decoOf h₂` — have convertible types
    `TyConvT E n Γ T₁ T₂`.
    * At `.app _ f a A₁ B₁ hf₁ ha₁` vs `.app _ f a A₂ B₂ hf₂ ha₂`, the two derivations decorate the
      application with potentially different codomains `B₁` and `B₂`. The induction hypothesis on
      `hf₁` and `hf₂` yields `hcPi : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)`; Step 2 (`piInj`)
      extracts `hcB : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂`; and `tyConvT_subst0_of_envWfT`
      substitutes `ha₁ : HasTyT E n Γ a A₁` to bridge `instantiate0 a B₁` and `instantiate0 a B₂`.
    * At `.pi _ A u₁ B v₁ hA₁ hB₁` vs `.pi _ A u₂ B v₂ hA₂ hB₂`, `SortUniq` relates `(u₁, v₁)` and
      `(u₂, v₂)` via `ConvT.sorts`. -/
noncomputable def uniq_of_piInj_sortUniq (hW : EnvWfT E) (piInj : PiInj E n)
    (su : SortUniq E n) : {Γ : LCtx} → CtxWfT E n Γ → {e T₁ T₂ : Expr Nat} →
    (h₁ : HasTyT E n Γ e T₁) → (h₂ : HasTyT E n Γ e T₂) → TyConvT E n Γ T₁ T₂
  | _, hΓ, _, _, _, .conv _ _ _ _ u h hc, h₂ =>
      .trans _ _ _ _ (.of _ _ _ u (.symm _ _ _ _ hc)) (uniq_of_piInj_sortUniq hW piInj su hΓ h h₂)
  | _, hΓ, _, _, _, h₁, .conv _ _ _ _ u h hc =>
      .trans _ _ _ _ (uniq_of_piInj_sortUniq hW piInj su hΓ h₁ h) (.of _ _ _ u hc)
  | _, _, _, _, _, .sort _ _, .sort _ _ => .refl _ _
  | _, _, _, _, _, .bvar _ _ _ h, .bvar _ _ _ h' => by
      have hA := Option.some.inj (h.symm.trans h')
      subst hA; exact .refl _ _
  | _, _, _, _, _, .const _ _ _ _ hres _ _, .const _ _ _ _ hres' _ _ => by
      have hm := Option.some.inj (hres.symm.trans hres')
      subst hm; exact .refl _ _
  | Γ, hΓ, _, _, _, .pi _ A u₁ _ v₁ hA₁ hB₁, .pi _ _ u₂ _ v₂ hA₂ hB₂ =>
      let hu : eqN u₁ u₂ := su hΓ hA₁ hA₂
      let hv : eqN v₁ v₂ := su (.assumption Γ A u₁ hΓ hA₁) hB₁ hB₂
      .of Γ (.sort (.imax u₁ v₁)) (.sort (.imax u₂ v₂)) (.succ (.imax u₁ v₁))
        (.sorts Γ (.imax u₁ v₁) (.imax u₂ v₂) (eqN_imax_both hu hv))
  | Γ, hΓ, _, _, _, .lam _ A u₁ _ _ hA₁ hb₁, .lam _ _ _ _ _ _ hb₂ =>
      tyConvT_pi_codom hA₁
        (uniq_of_piInj_sortUniq hW piInj su (.assumption Γ A u₁ hΓ hA₁) hb₁ hb₂)
  | _, hΓ, _, _, _, .app _ _ _ _ _ hf₁ ha₁, .app _ _ _ _ _ hf₂ _ =>
      let hcPi := uniq_of_piInj_sortUniq hW piInj su hΓ hf₁ hf₂
      let hcB := (piInj hΓ hcPi).2
      tyConvT_subst0_of_envWfT hW ha₁ hcB
  | Γ, hΓ, _, _, _, .letE _ A u₁ value _ _ hA₁ hv₁ hb₁, .letE _ _ _ _ _ _ _ _ hb₂ =>
      tyConvT_substLet0 hW hv₁
        (uniq_of_piInj_sortUniq hW piInj su (.letBinding Γ A u₁ value hΓ hA₁ hv₁) hb₁ hb₂)
  | _, hΓ, _, _, _, .lit _ _ _ hexp₁, .lit _ _ _ hexp₂ =>
      uniq_of_piInj_sortUniq hW piInj su hΓ hexp₁ hexp₂
termination_by _ _ _ _ _ h₁ h₂ => sizeOf h₁ + sizeOf h₂
decreasing_by all_goals (first | assumption | (simp_wf; assumption) | (simp <;> omega) | (simp_wf; simp <;> omega))

/-- Step 3 (Decoration Transfer from `PiInj` and `SortCoh`):
    Here the `.pi` case recurses on `(hA₁, hA₂)` and `(hB₁, hB₂)` and applies `SortCoh` to the
    resulting `TyConvT` chains between `.sort u₁` and `.sort u₂` and between `.sort v₁` and
    `.sort v₂`. -/
noncomputable def uniq_of_piInj_sortCoh (hW : EnvWfT E) (piInj : PiInj E n)
    (sc : SortCoh E n) : {Γ : LCtx} → CtxWfT E n Γ → {e T₁ T₂ : Expr Nat} →
    (h₁ : HasTyT E n Γ e T₁) → (h₂ : HasTyT E n Γ e T₂) → TyConvT E n Γ T₁ T₂
  | _, hΓ, _, _, _, .conv _ _ _ _ u h hc, h₂ =>
      .trans _ _ _ _ (.of _ _ _ u (.symm _ _ _ _ hc)) (uniq_of_piInj_sortCoh hW piInj sc hΓ h h₂)
  | _, hΓ, _, _, _, h₁, .conv _ _ _ _ u h hc =>
      .trans _ _ _ _ (uniq_of_piInj_sortCoh hW piInj sc hΓ h₁ h) (.of _ _ _ u hc)
  | _, _, _, _, _, .sort _ _, .sort _ _ => .refl _ _
  | _, _, _, _, _, .bvar _ _ _ h, .bvar _ _ _ h' => by
      have hA := Option.some.inj (h.symm.trans h')
      subst hA; exact .refl _ _
  | _, _, _, _, _, .const _ _ _ _ hres _ _, .const _ _ _ _ hres' _ _ => by
      have hm := Option.some.inj (hres.symm.trans hres')
      subst hm; exact .refl _ _
  | Γ, hΓ, _, _, _, .pi _ A u₁ _ v₁ hA₁ hB₁, .pi _ _ u₂ _ v₂ hA₂ hB₂ =>
      let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u₁ hΓ hA₁
      let hcA_sort := uniq_of_piInj_sortCoh hW piInj sc hΓ hA₁ hA₂
      let hcB_sort := uniq_of_piInj_sortCoh hW piInj sc hΓA hB₁ hB₂
      let hu : eqN u₁ u₂ := sc hΓ hcA_sort
      let hv : eqN v₁ v₂ := sc hΓA hcB_sort
      .of Γ (.sort (.imax u₁ v₁)) (.sort (.imax u₂ v₂)) (.succ (.imax u₁ v₁))
        (.sorts Γ (.imax u₁ v₁) (.imax u₂ v₂) (eqN_imax_both hu hv))
  | Γ, hΓ, _, _, _, .lam _ A u₁ _ _ hA₁ hb₁, .lam _ _ _ _ _ _ hb₂ =>
      tyConvT_pi_codom hA₁
        (uniq_of_piInj_sortCoh hW piInj sc (.assumption Γ A u₁ hΓ hA₁) hb₁ hb₂)
  | _, hΓ, _, _, _, .app _ _ _ _ _ hf₁ ha₁, .app _ _ _ _ _ hf₂ _ =>
      let hcPi := uniq_of_piInj_sortCoh hW piInj sc hΓ hf₁ hf₂
      let hcB := (piInj hΓ hcPi).2
      tyConvT_subst0_of_envWfT hW ha₁ hcB
  | Γ, hΓ, _, _, _, .letE _ A u₁ value _ _ hA₁ hv₁ hb₁, .letE _ _ _ _ _ _ _ _ hb₂ =>
      tyConvT_substLet0 hW hv₁
        (uniq_of_piInj_sortCoh hW piInj sc (.letBinding Γ A u₁ value hΓ hA₁ hv₁) hb₁ hb₂)
  | _, hΓ, _, _, _, .lit _ _ _ hexp₁, .lit _ _ _ hexp₂ =>
      uniq_of_piInj_sortCoh hW piInj sc hΓ hexp₁ hexp₂
termination_by _ _ _ _ _ h₁ h₂ => sizeOf h₁ + sizeOf h₂
decreasing_by all_goals (first | assumption | (simp_wf; assumption) | (simp <;> omega) | (simp_wf; simp <;> omega))

/-- Step 3 (`Retype` from `PiInj` and `SortUniq`): a certified step re-types (index only;
    `stepDeco` is preserved by `stepDeco_reindex`) to any other typing of its source via
    `CStep.reindex`. -/
noncomputable def retype_of_piInj_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (piInj : PiInj E n) (su : SortUniq E n) : Retype E n PEq :=
  retype_of_uniq L (uniq_of_piInj_sortUniq hW piInj su)

/-- Step 3 (`Retype` from `PiInj` and `SortCoh`): a certified step re-types (index only;
    `stepDeco` is preserved by `stepDeco_reindex`) to any other typing of its source via
    `CStep.reindex`. -/
noncomputable def retype_of_piInj_sortCoh (hW : EnvWfT E) (L : LeafIface E n PEq)
    (piInj : PiInj E n) (sc : SortCoh E n) : Retype E n PEq :=
  retype_of_uniq L (uniq_of_piInj_sortCoh hW piInj sc)

/-- Step 3 from `CDiamond` and `SortUniq`: `CDiamond` + `SortUniq` yields `PiInj`, hence `Uniq`
    (DT-012) and `Retype`. -/
noncomputable def uniq_of_diamond_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) (su : SortUniq E n) : Uniq E n :=
  uniq_of_piInj_sortUniq hW (piInj_of_diamond_sortUniq hW L D su) su

/-! ### Step 4: Single-step decoration transfer contract (`StepDecoTransfer`) -/

set_option linter.unusedVariables false in
/-- Single-step source-decoration transfer contract: given a certified step
    `q : CStep E n PEq Γ b e T` and a typable source decoration `d : Deco b`, produces a certified
    step `q' : CStep E n PEq Γ b e T` with the same endpoints and index whose source decoration is
    `d`. Note: refuted for a generic lawful `LeafIface` at `peq` by `#7600`
    (`admitted_single_step_transfer_false`); there is no `peq` combinator or generic-`L` assembler
    in this module. -/
def StepDecoTransfer (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b e T : Expr Nat}
    (q : CStep E n PEq Γ b e T) (d : Deco b),
    (∃ h : HasTyT E n Γ b T, decoOf h = d) →
    Σ' (q' : CStep E n PEq Γ b e T), stepDeco L q'.step = d

/-! ### Discharging `PropAlign` and `PiPropCodom` from `ZeroSortCoherence` / `SortUniq` / `CDiamond` -/

/-- `PropAlign` (`RcicNativeValleyFronts`) is discharged by `ZeroSortCoherence` via
    `HostPropAudit.hostPropData_of_zeroSortCoherence` (`RcicNativeWallHostProp`), without `Uniq`,
    `Retype`, or `PiInj`. -/
def propAlign_of_zsc (hW : EnvWfT E) (zsc : HostPropAudit.ZeroSortCoherence E n) :
    PropAlign E n :=
  fun {_} hΓ {_ _ _} h₁ h₂ hP₁ =>
    HostPropAudit.hostPropData_of_zeroSortCoherence hW zsc hΓ h₂ hP₁ h₁

/-- `PiPropCodom` (`RcicNativeValleyFronts`) is discharged by `ZeroSortCoherence` via
    `HostPropAudit.pi_codomain_prop_data` (`RcicNativeWallHostProp`), without `Uniq`, `Retype`, or
    `PiInj`. -/
def piPropCodom_of_zsc (hW : EnvWfT E) (zsc : HostPropAudit.ZeroSortCoherence E n) :
    PiPropCodom E n :=
  fun {_} hΓ {_ _} hPi =>
    HostPropAudit.pi_codomain_prop_data hW zsc hΓ hPi

/-- `PropAlign` from `SortUniq`. -/
def propAlign_of_sortUniq (hW : EnvWfT E) (su : SortUniq E n) : PropAlign E n :=
  propAlign_of_zsc hW (zsc_of_sortUniq su)

/-- `PiPropCodom` from `SortUniq`. -/
def piPropCodom_of_sortUniq (hW : EnvWfT E) (su : SortUniq E n) : PiPropCodom E n :=
  piPropCodom_of_zsc hW (zsc_of_sortUniq su)

/-! ### Structural properties of `stepDeco` vs `CStep.reindex` -/

/-- `CStep.reindex` never alters `stepDeco`: if `stepDeco L q.step ≠ d`, no `CStep.reindex` of `q`
    can produce a step with source decoration `d`. Thus `CStep.reindex` realizes `Retype`
    (`retype_of_piInj_sortUniq` / `retype_of_piInj_sortCoh`, changing the type index `T₂ ↦ T₁`
    without changing `stepDeco`), whereas changing `stepDeco` requires rebuilding internal typing
    witnesses of the `ParRedT` derivation. -/
theorem reindex_stepDeco_ne (L : LeafIface E n PEq) {Γ : LCtx} {b e T₁ T₂ : Expr Nat}
    (q : CStep E n PEq Γ b e T₁) (hc : TyConvT E n Γ T₁ T₂) {d : Deco b}
    (hne : stepDeco L q.step ≠ d) :
    stepDeco L (q.reindex hc).step ≠ d := by
  rw [stepDeco_reindex]
  exact hne

/-- For any `ParRedT.beta` step, its `.app` source decoration carries the β-codomain `B` (which is
    typed in `.assumption A :: Γ`) and the syntactic λ-domain `A`; hence if a typing `h` of
    `.app (.lam A body) arg` chooses a distinct application codomain `B' ≠ B`, `stepDeco` of the
    `ParRedT.beta` step cannot equal `decoOf h`. -/
theorem beta_stepDeco_ne_of_codom_ne (L : LeafIface E n PEq) {Γ : LCtx}
    {A body body' arg arg' B B' : Expr Nat} {u v' w' : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
    (df : Deco (.lam A body)) (da : Deco arg) (hBne : B ≠ B') :
    stepDeco L (ParRedT.beta Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂ hred) ≠
      .app (.lam A body) arg B' df da := by
  intro heq
  simp only [stepDeco] at heq
  injection heq with _ _ hB _ _
  exact hBne hB

/-- `stepDeco` of `ParRedT.bvarZeta` is always `.bvar i`, independent of the let-bound value step
    `hv`. -/
@[simp] theorem bvarZeta_stepDeco_eq_bvar (L : LeafIface E n PEq) {Γ : LCtx} {i : Nat}
    {A v v' T : Expr Nat} {h : Γ.get? i = some (.letBinding A v)}
    {hv : ParRedT PEq E n (Γ.drop (i + 1)) v v' A}
    {hl : HasTyT E n Γ (.bvar i) T} {hr : HasTyT E n Γ (lift 0 (i + 1) v') T} :
    stepDeco L (ParRedT.bvarZeta Γ i A v v' T h hv hl hr) = .bvar i :=
  deco_subsingleton_bvar rfl _ _

/-! ### Constructor-level `StepDecoTransfer` combinators (two-level `CStep.reindex` + `PiInj` + `SortUniq`) -/

/-- For `.sort l` sources, `Deco (.sort l)` is a subsingleton (`deco_subsingleton_sort`), so any
    certified step out of `.sort l` already carries every decoration `d : Deco (.sort l)`. -/
def stepDecoTransfer_of_sort (L : LeafIface E n PEq) {Γ : LCtx} {l : Level} {e T : Expr Nat}
    (q : CStep E n PEq Γ (.sort l) e T) (d : Deco (.sort l)) :
    Σ' (q' : CStep E n PEq Γ (.sort l) e T), stepDeco L q'.step = d :=
  ⟨q, deco_subsingleton_sort rfl _ _⟩

/-- For `.bvar i` sources (including `ParRedT.bvarZeta`), `Deco (.bvar i)` is a subsingleton
    (`deco_subsingleton_bvar`), so any certified step out of `.bvar i` already carries every
    decoration `d : Deco (.bvar i)`. -/
def stepDecoTransfer_of_bvar (L : LeafIface E n PEq) {Γ : LCtx} {i : Nat} {e T : Expr Nat}
    (q : CStep E n PEq Γ (.bvar i) e T) (d : Deco (.bvar i)) :
    Σ' (q' : CStep E n PEq Γ (.bvar i) e T), stepDeco L q'.step = d :=
  ⟨q, deco_subsingleton_bvar rfl _ _⟩

/-- For `.const r ls` sources (including `ParRedT.consts` and `ParRedT.delta`),
    `Deco (.const r ls)` is a subsingleton (`deco_subsingleton_const`), so any certified step out of
    `.const r ls` already carries every decoration `d : Deco (.const r ls)`. -/
def stepDecoTransfer_of_const (L : LeafIface E n PEq) {Γ : LCtx} {r : Nat} {ls : List Level}
    {e T : Expr Nat} (q : CStep E n PEq Γ (.const r ls) e T) (d : Deco (.const r ls)) :
    Σ' (q' : CStep E n PEq Γ (.const r ls) e T), stepDeco L q'.step = d :=
  ⟨q, deco_subsingleton_const rfl _ _⟩

/-- `StepDecoTransfer` for `ParRedT.refl`: from `PiInj` and `SortUniq`, `uniq_of_piInj_sortUniq`
    and `hasTyT_of_tyConvT` re-present any typing `h_src : HasTyT E n Γ b T'` as
    `h' : HasTyT E n Γ b T` with `decoOf h' = decoOf h_src`, yielding `ParRedT.refl Γ b T h'` at `T`
    with `stepDeco = decoOf h_src`. -/
noncomputable def stepDecoTransfer_refl (hW : EnvWfT E) (L : LeafIface E n PEq)
    (piInj : PiInj E n) (su : SortUniq E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b T T' : Expr Nat} (h : HasTyT E n Γ b T) (h_src : HasTyT E n Γ b T') :
    Σ' (q' : CStep E n PEq Γ b b T), stepDeco L q'.step = decoOf h_src :=
  let hc : TyConvT E n Γ T' T := uniq_of_piInj_sortUniq hW piInj su hΓ h_src h
  let h' : HasTyT E n Γ b T := hasTyT_of_tyConvT h_src hc
  ⟨⟨.refl Γ b T h', .refl (.refl Γ b T h')⟩, decoOf_hasTyT_of_tyConvT h_src hc⟩

/-- `StepDecoTransfer` for `ParRedT.conv`: transferring the inner step at `A` and applying
    `CStep.reindex hc` preserves `stepDeco` by `stepDeco_reindex`. -/
def stepDecoTransfer_conv (L : LeafIface E n PEq) {Γ : LCtx} {a b A A' : Expr Nat}
    (hc : TyConvT E n Γ A A') {d : Deco a}
    (ih : Σ' (q' : CStep E n PEq Γ a b A), stepDeco L q'.step = d) :
    Σ' (q' : CStep E n PEq Γ a b A'), stepDeco L q'.step = d :=
  ⟨ih.1.reindex hc, (stepDeco_reindex L ih.1 hc).trans ih.2⟩

/-- `StepDecoTransfer` for `ParRedT.iotaSpine`: transferring the spine step `lhs ⇒ lhs'` preserves
    the ι redex `DerivedIotaU E lhs' rhs` and the outer decoration `stepDeco`. -/
def stepDecoTransfer_iotaSpine (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {lhs lhs' rhs T : Expr Nat} (hI : DerivedIotaU E lhs' rhs)
    (hrhs : HasTyT E n Γ rhs T) (c : ConvT E n Γ lhs rhs T) {d : Deco lhs}
    (ih : Σ' (q' : CStep E n PEq Γ lhs lhs' T), stepDeco L q'.step = d) :
    Σ' (q' : CStep E n PEq Γ lhs rhs T), stepDeco L q'.step = d :=
  ⟨⟨.iotaSpine Γ lhs lhs' rhs T ih.1.step hI (ih.1.rightTyped L hΓ) hrhs,
    .iotaSpine c ih.1.cert⟩, ih.2⟩

/-- `StepDecoTransfer` for `ParRedT.lit`: from `PiInj` and `SortUniq`, `uniq_of_piInj_sortUniq` and
    `hasTyT_of_tyConvT` re-present any typing `hexp_src : HasTyT E n Γ (natExpand t) T'` at `T` with
    `decoOf hexp' = decoOf hexp_src`, transferring `.lit Γ t T hexp` to `.lit t (decoOf hexp_src)`. -/
noncomputable def stepDecoTransfer_lit (hW : EnvWfT E) (L : LeafIface E n PEq)
    (piInj : PiInj E n) (su : SortUniq E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {t : Nat} {T T' : Expr Nat} (hexp : HasTyT E n Γ (natExpand t) T)
    (c : ConvT E n Γ (.lit t) (natExpand t) T) (hexp_src : HasTyT E n Γ (natExpand t) T') :
    Σ' (q' : CStep E n PEq Γ (.lit t) (natExpand t) T),
      stepDeco L q'.step = .lit t (decoOf hexp_src) :=
  let hc : TyConvT E n Γ T' T := uniq_of_piInj_sortUniq hW piInj su hΓ hexp_src hexp
  let hexp' : HasTyT E n Γ (natExpand t) T := hasTyT_of_tyConvT hexp_src hc
  ⟨⟨.lit Γ t T hexp', .lit c⟩, congrArg (Deco.lit t) (decoOf_hasTyT_of_tyConvT hexp_src hc)⟩

/-- `StepDecoTransfer` for `ParRedT.pi`: from `SortUniq`, any `ParRedT.pi` step transfers to the
    target decoration `.pi A B u' v' (decoOf hA') (decoOf hB')` of any typings `hA'` and `hB'`,
    via inner sort conversion of `hc` / `hcB` and outer `CStep.reindex` along `eqN_imax_both`. -/
def stepDecoTransfer_pi (L : LeafIface E n PEq) (su : SortUniq E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' B B' : Expr Nat} {u v u' v' : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hc : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v))
    (hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v)))
    (hA' : HasTyT E n Γ A (.sort u'))
    (hB' : HasTyT E n (.assumption A :: Γ) B (.sort v')) :
    Σ' (q' : CStep E n PEq Γ (.pi A B) (.pi A' B') (.sort (.imax u v))),
      stepDeco L q'.step = .pi A B u' v' (decoOf hA') (decoOf hB') :=
  let hu : eqN u u' := su hΓ hA hA'
  let hv : eqN v v' := su (.assumption Γ A u hΓ hA) hB hB'
  let huv : eqN (.imax u v) (.imax u' v') := eqN_imax_both hu hv
  let hc' : ConvT E n Γ A A' (.sort u') :=
    convT_of_tyConv hc (.of Γ (.sort u) (.sort u') (.succ u) (.sorts Γ u u' hu))
  let hcB' : ConvT E n (.assumption A :: Γ) B B' (.sort v') :=
    convT_of_tyConv hcB (.of _ (.sort v) (.sort v') (.succ v) (.sorts _ v v' hv))
  let hrt' : HasTyT E n Γ (.pi A' B') (.sort (.imax u' v')) :=
    .conv Γ (.pi A' B') (.sort (.imax u v)) (.sort (.imax u' v')) (.succ (.imax u v)) hrt
      (.sorts Γ (.imax u v) (.imax u' v') huv)
  let q_inner : CStep E n PEq Γ (.pi A B) (.pi A' B') (.sort (.imax u' v')) :=
    ⟨.pi Γ A A' B B' u' v' hA' hc' hB' hcB' hrt', .pi (.pi Γ A A' B B' u' v' hc' hcB')⟩
  let hc_outer : TyConvT E n Γ (.sort (.imax u' v')) (.sort (.imax u v)) :=
    .of Γ (.sort (.imax u' v')) (.sort (.imax u v)) (.succ (.imax u' v'))
      (.sorts Γ (.imax u' v') (.imax u v) (eqN_symm huv))
  ⟨q_inner.reindex hc_outer, stepDeco_reindex L q_inner hc_outer⟩

/-- `StepDecoTransfer` for `ParRedT.lam`: from `SortUniq` on `A` and a transferred body step `ihb`,
    replaces `(u, hc, hA, hb)` by `(u', hc', hA', ihb.1.step)` at the exact same outer index
    `.pi A B`. -/
def stepDecoTransfer_lam (L : LeafIface E n PEq) (su : SortUniq E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' body body' B : Expr Nat} {u v u' : Level}
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrt : HasTyT E n Γ (.lam A' body') (.pi A B))
    (c : ConvT E n Γ (.lam A body) (.lam A' body') (.pi A B))
    (hA' : HasTyT E n Γ A (.sort u')) {db : Deco body}
    (ihb : Σ' (qb' : CStep E n PEq (.assumption A :: Γ) body body' B), stepDeco L qb'.step = db) :
    Σ' (q' : CStep E n PEq Γ (.lam A body) (.lam A' body') (.pi A B)),
      stepDeco L q'.step = .lam A body u' (decoOf hA') db :=
  let hu : eqN u u' := su hΓ hA hA'
  let hc' : ConvT E n Γ A A' (.sort u') :=
    convT_of_tyConv hc (.of Γ (.sort u) (.sort u') (.succ u) (.sorts Γ u u' hu))
  ⟨⟨.lam Γ A A' body body' B u' v hc' hA' hB ihb.1.step hrt, .lam c ihb.1.cert⟩,
    congrArg (Deco.lam A body u' (decoOf hA')) ihb.2⟩

/-- `StepDecoTransfer` for `ParRedT.letE`: from `SortUniq` on `A`, a transferred value step `ihv`,
    and a transferred body step `ihb`, replaces `(u, hc, hA, hv, hb)` by
    `(u', hc', hA', ihv.1.step, ihb.1.step)` at the exact same outer index `instantiate0 value B`. -/
def stepDecoTransfer_letE (L : LeafIface E n PEq) (su : SortUniq E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A' value value' body body' B : Expr Nat} {u w u' : Level}
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 value B) (.sort w))
    (hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B))
    (c : ConvT E n Γ (.letE A value body) (.letE A' value' body') (instantiate0 value B))
    (hA' : HasTyT E n Γ A (.sort u')) {dv : Deco value} {db : Deco body}
    (ihv : Σ' (qv' : CStep E n PEq Γ value value' A), stepDeco L qv'.step = dv)
    (ihb : Σ' (qb' : CStep E n PEq (.letBinding A value :: Γ) body body' B),
      stepDeco L qb'.step = db) :
    Σ' (q' : CStep E n PEq Γ (.letE A value body) (.letE A' value' body') (instantiate0 value B)),
      stepDeco L q'.step = .letE A value body u' (decoOf hA') dv db :=
  let hu : eqN u u' := su hΓ hA hA'
  let hc' : ConvT E n Γ A A' (.sort u') :=
    convT_of_tyConv hc (.of Γ (.sort u) (.sort u') (.succ u) (.sorts Γ u u' hu))
  ⟨⟨.letE Γ A A' value value' body body' B u' w hc' hA' ihv.1.step hB hTy ihb.1.step hrt,
    .letE c ihv.1.cert ihb.1.cert⟩,
    by simp only [stepDeco, ihv.2, ihb.2]⟩

/-- `StepDecoTransfer` for `ParRedT.zeta`: from any domain typing `hA' : HasTyT E n Γ A (.sort u')`,
    a transferred value step `ihv`, and a transferred body step `ihb`, replaces `(u, hA, hv, hb)` by
    `(u', hA', ihv.1.step, ihb.1.step)` at the exact same outer index `instantiate0 value B`. -/
def stepDecoTransfer_zeta (L : LeafIface E n PEq) {Γ : LCtx}
    {A value value' body body' B : Expr Nat} {w u' : Level}
    (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    (hTy : HasTyT E n Γ (instantiate0 value B) (.sort w))
    (hred : HasTyT E n Γ (instantiate0 value' body') (instantiate0 value B))
    (c : ConvT E n Γ (.letE A value body) (instantiate0 value' body') (instantiate0 value B))
    (hA' : HasTyT E n Γ A (.sort u')) {dv : Deco value} {db : Deco body}
    (ihv : Σ' (qv' : CStep E n PEq Γ value value' A), stepDeco L qv'.step = dv)
    (ihb : Σ' (qb' : CStep E n PEq (.letBinding A value :: Γ) body body' B),
      stepDeco L qb'.step = db) :
    Σ' (q' : CStep E n PEq Γ (.letE A value body) (instantiate0 value' body')
      (instantiate0 value B)),
      stepDeco L q'.step = .letE A value body u' (decoOf hA') dv db :=
  ⟨⟨.zeta Γ A value value' body body' B u' w hA' ihv.1.step hB hTy ihb.1.step hred,
    .zeta c ihv.1.cert ihb.1.cert⟩,
    by simp only [stepDeco, ihv.2, ihb.2]⟩

/-- Two-level `CStep.reindex` for `ParRedT.eta`: inner-reindexes the transferred function step
    `ihf.1` along `tyConvT_pi_codom hA' hcB` to `.pi A B'`, builds the canonical η-step at `.pi A B'`
    using `etaExpansionTy`, and outer-reindexes back to `.pi A B`. -/
def stepDecoTransfer_eta (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' A B B' : Expr Nat} {u' : Level} (hA' : HasTyT E n Γ A (.sort u'))
    (hcB : TyConvT E n (.assumption A :: Γ) B B') {df : Deco f}
    (ihf : Σ' (qf' : CStep E n PEq Γ f f' (.pi A B)), stepDeco L qf'.step = df) :
    Σ' (q' : CStep E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B)),
      stepDeco L q'.step =
        .lam A (.app (lift 0 1 f) (.bvar 0)) u' (decoOf hA')
          (.app (lift 0 1 f) (.bvar 0) (lift 1 1 B') (decoLift 0 1 df) (.bvar 0)) :=
  let hcl := envClosed_of_envWfT hW
  let qf_B' : CStep E n PEq Γ f f' (.pi A B') := ihf.1.reindex (tyConvT_pi_codom hA' hcB)
  let hf_B'_ty : HasTyT E n Γ f (.pi A B') := qf_B'.leftTyped L hΓ
  let hl_B' : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B') :=
    etaExpansionTy hcl hA' hf_B'_ty
  let c_eta : ConvT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B') :=
    .trans Γ _ f f' (.pi A B')
      (.eta Γ f A B' hf_B'_ty)
      qf_B'.toConvT
  let q_at_B' : CStep E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B') :=
    ⟨.eta Γ f f' A B' qf_B'.step hl_B', .eta c_eta qf_B'.cert⟩
  let hc_outer : TyConvT E n Γ (.pi A B') (.pi A B) := tyConvT_pi_codom hA' hcB.symmT
  ⟨q_at_B'.reindex hc_outer, by
    rw [stepDeco_reindex]
    simp only [q_at_B', hl_B', stepDeco, decoOf_etaExpansionTy, hf_B'_ty, decoOf_leftTyped,
      qf_B', stepDeco_reindex, ihf.2]⟩

/-- Two-level `CStep.reindex` for `ParRedT.app`: given `PiInj`, inner-reindexes the transferred
    argument step `iha.1` along `(piInj hΓ (.trans hc.symmT hc')).1 : TyConvT E n Γ A A'`, rebuilds
    `ParRedT.app` at the target codomain `B'` (giving `stepDeco = .app f a B' df da`), and
    outer-reindexes along `tyConvT_subst0_of_envWfT` back to the original index `instantiate0 a B`. -/
noncomputable def stepDecoTransfer_app (hW : EnvWfT E) (L : LeafIface E n PEq)
    (piInj : PiInj E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' a a' A B A' B' T₀ : Expr Nat} {u' v' : Level}
    (hc : TyConvT E n Γ T₀ (.pi A B)) (hc' : TyConvT E n Γ T₀ (.pi A' B'))
    (hA' : HasTyT E n Γ A' (.sort u'))
    (hB' : HasTyT E n (.assumption A' :: Γ) B' (.sort v'))
    {df : Deco f} {da : Deco a}
    (ihf : Σ' (qf' : CStep E n PEq Γ f f' T₀), stepDeco L qf'.step = df)
    (iha : Σ' (qa₀ : CStep E n PEq Γ a a' A), stepDeco L qa₀.step = da) :
    Σ' (q' : CStep E n PEq Γ (.app f a) (.app f' a') (instantiate0 a B)),
      stepDeco L q'.step = .app f a B' df da :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let ⟨hcA, hcB⟩ := piInj hΓ (.trans _ _ _ _ hc.symmT hc')
  let qa' : CStep E n PEq Γ a a' A' := iha.1.reindex hcA
  let ha_A : HasTyT E n Γ a A := iha.1.leftTyped L hΓ
  let ha_A' : HasTyT E n Γ a A' := qa'.leftTyped L hΓ
  let ha'_A' : HasTyT E n Γ a' A' := qa'.rightTyped L hΓ
  let hTy' : HasTyT E n Γ (instantiate0 a B') (.sort v') := hasTyT_subst0S hcl hinst hB' ha_A'
  let hr' : HasTyT E n Γ (.app f' a') (instantiate0 a B') :=
    .conv Γ _ _ _ v'
      (.app Γ f' a' A' B' (hasTyT_of_tyConvT (ihf.1.rightTyped L hΓ) hc') ha'_A')
      (convT_inst0_valueSort hA' hB' ha'_A' ha_A' (.symm _ _ _ _ qa'.toConvT))
  let q_at_B' : CStep E n PEq Γ (.app f a) (.app f' a') (instantiate0 a B') :=
    ⟨.app Γ f f' a a' A' B' T₀ v' v' ihf.1.step hc' hB' hTy' qa'.step hr',
      .app (.app Γ f f' a a' A' B' (convT_of_tyConv ihf.1.toConvT hc') qa'.toConvT)
        ihf.1.cert qa'.cert⟩
  let hc_outer : TyConvT E n Γ (instantiate0 a B') (instantiate0 a B) :=
    tyConvT_subst0_of_envWfT hW ha_A hcB.symmT
  ⟨q_at_B'.reindex hc_outer, by
    rw [stepDeco_reindex]
    simp only [q_at_B', stepDeco, qa', stepDeco_reindex, ihf.2, iha.2]⟩

/-- Two-level `CStep.reindex` for `ParRedT.beta`: inner-reindexes the transferred body step `ihb.1`
    along `hcB : TyConvT E n (.assumption A :: Γ) B B'`, rebuilds `ParRedT.beta` at the target
    domain typing `hA'` and codomain `B'` (giving
    `stepDeco = .app (.lam A body) arg B' (.lam A body u' (decoOf hA') db) da`), and outer-reindexes
    along `tyConvT_subst0_of_envWfT` back to the original index `instantiate0 arg B`. -/
noncomputable def stepDecoTransfer_beta (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body body' arg arg' B B' : Expr Nat} {u' v' : Level}
    (hA' : HasTyT E n Γ A (.sort u'))
    (hB' : HasTyT E n (.assumption A :: Γ) B' (.sort v'))
    (hcB : TyConvT E n (.assumption A :: Γ) B B')
    (c_root : ConvT E n Γ (.app (.lam A body) arg) (instantiate0 arg' body') (instantiate0 arg B))
    {db : Deco body} {da : Deco arg}
    (ihb : Σ' (qb₀ : CStep E n PEq (.assumption A :: Γ) body body' B), stepDeco L qb₀.step = db)
    (iha : Σ' (qa' : CStep E n PEq Γ arg arg' A), stepDeco L qa'.step = da) :
    Σ' (q' : CStep E n PEq Γ (.app (.lam A body) arg) (instantiate0 arg' body')
      (instantiate0 arg B)),
      stepDeco L q'.step =
        .app (.lam A body) arg B' (.lam A body u' (decoOf hA') db) da :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u' hΓ hA'
  let qb' : CStep E n PEq (.assumption A :: Γ) body body' B' := ihb.1.reindex hcB
  let harg_A : HasTyT E n Γ arg A := iha.1.leftTyped L hΓ
  let harg'_A : HasTyT E n Γ arg' A := iha.1.rightTyped L hΓ
  let hbody'_B' : HasTyT E n (.assumption A :: Γ) body' B' := qb'.rightTyped L hΓA
  let hTy' : HasTyT E n Γ (instantiate0 arg B') (.sort v') := hasTyT_subst0S hcl hinst hB' harg_A
  let hred' : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B') :=
    .conv Γ _ _ _ v'
      (hasTyT_subst0S hcl hinst hbody'_B' harg'_A)
      (convT_inst0_valueSort hA' hB' harg'_A harg_A (.symm _ _ _ _ iha.1.toConvT))
  let hc_in : TyConvT E n Γ (instantiate0 arg B) (instantiate0 arg B') :=
    tyConvT_subst0_of_envWfT hW harg_A hcB
  let q_at_B' : CStep E n PEq Γ (.app (.lam A body) arg) (instantiate0 arg' body')
      (instantiate0 arg B') :=
    ⟨.beta Γ A body body' arg arg' B' u' v' v' hA' hB' hTy' qb'.step iha.1.step hred',
      .beta (convT_of_tyConv c_root hc_in) qb'.cert iha.1.cert⟩
  let hc_outer : TyConvT E n Γ (instantiate0 arg B') (instantiate0 arg B) :=
    tyConvT_subst0_of_envWfT hW harg_A hcB.symmT
  ⟨q_at_B'.reindex hc_outer, by
    rw [stepDeco_reindex]
    simp only [q_at_B', stepDeco, qb', stepDeco_reindex, ihb.2, iha.2]⟩

#print axioms eqN_imax_both
#print axioms tyConvT_ctx
#print axioms tyConvT_assump_dom
#print axioms derivedIotaU_sort_source_false
#print axioms derivedIotaU_pi_source_false'
#print axioms peq_sort_source_false
#print axioms peq_pi_source_false
#print axioms parRedT_pi_head_reverse_of_zsc
#print axioms parRedT_sort_inv_of_leaf
#print axioms parRedT_sort_inv_of_zsc
#print axioms parRedTStar_sort_inv_of_zsc
#print axioms cstar_sort_inv_of_zsc
#print axioms valleyJoin_sort_inv_of_zsc
#print axioms cvalley_sort_inv_of_zsc
#print axioms parRedT_pi_inv_of_leaf
#print axioms parRedT_pi_inv_of_zsc
#print axioms parRedTStar_pi_inv_of_zsc
#print axioms cstar_pi_inv_of_zsc
#print axioms valleyJoin_pi_inv_of_zsc
#print axioms cvalley_pi_inv_of_zsc
#print axioms convT_sort_inv_of_diamond
#print axioms convT_pi_inv_of_diamond
#print axioms SortCoh
#print axioms SortUniq
#print axioms SortRetype
#print axioms PiInj
#print axioms zsc_of_sortUniq
#print axioms sortRetype_of_sortUniq
#print axioms sortRetype_of_uniq
#print axioms sortUniq_of_uniq_sortCoh
#print axioms piRow_of_piInj
#print axioms cvalley_of_tyConvT_of_sortRetype
#print axioms cvalley_of_tyConvT_of_sortUniq
#print axioms sortCoh_of_diamond_sortRetype
#print axioms sortCoh_of_diamond_sortUniq
#print axioms tyConvT_firstOf_data
#print axioms piInj_of_diamond_sortRetype
#print axioms piInj_of_diamond_sortUniq
#print axioms piRow_of_diamond_sortUniq
#print axioms uniq_of_piInj_sortUniq
#print axioms uniq_of_piInj_sortCoh
#print axioms retype_of_piInj_sortUniq
#print axioms retype_of_piInj_sortCoh
#print axioms uniq_of_diamond_sortUniq
#print axioms StepDecoTransfer
#print axioms propAlign_of_zsc
#print axioms piPropCodom_of_zsc
#print axioms propAlign_of_sortUniq
#print axioms piPropCodom_of_sortUniq
#print axioms reindex_stepDeco_ne
#print axioms beta_stepDeco_ne_of_codom_ne
#print axioms bvarZeta_stepDeco_eq_bvar
#print axioms stepDecoTransfer_of_sort
#print axioms stepDecoTransfer_of_bvar
#print axioms stepDecoTransfer_of_const
#print axioms stepDecoTransfer_refl
#print axioms stepDecoTransfer_conv
#print axioms stepDecoTransfer_iotaSpine
#print axioms stepDecoTransfer_lit
#print axioms stepDecoTransfer_pi
#print axioms stepDecoTransfer_lam
#print axioms stepDecoTransfer_letE
#print axioms stepDecoTransfer_zeta
#print axioms stepDecoTransfer_eta
#print axioms stepDecoTransfer_app
#print axioms stepDecoTransfer_beta

end Rcic.Declarative.NativeValleys
