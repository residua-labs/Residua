import rcic.RcicF8XValley
import rcic.RcicDT0709EnvWf

/-!
# `RcicF8XBinderWf` — where the binder context's `CtxWfT` comes from (S3c)

cc's ruling of 2026-10-14 on #7035 (binding for #7026 §3): Stratum B runs where `CtxWfT`
holds, and the X lane must show where `CtxWfT` of each recursive context comes from —
expected: binder contexts `A :: Γ` get their sort typing from the endpoint regularity (DT009
under `CtxWfT`) of the LITERAL links, not from the weak chain itself — and name any failing
case exactly.

Inside `xValley` (S3b) no call ever enters a binder context: J is called at the caller's `Γ`
or at the tail of a cutoff-0 weakening (`ctxWfT_tail`); U, D, S, K, `xStructTc` carry no
context premise. The binder context `.assumption A :: Γ` is the CONSUMER's: the next call on
the codomain component. This module supplies its `CtxWfT`, as data:

* `convT_endpoints_data` — DT009 as DATA: `endpoints3_of_envWfT` with its two fronts
  (`SubstLetT`, `ConstsRightDataT`) discharged from `EnvWfT` — both endpoints of a conversion
  are typed at its index, in a well-formed context;
* `ctxWfT_binder_of_lit` — cc's route: a literal link out of `.pi A B` gives
  `HasTyT Γ (.pi A B) (.sort u)`, `hasTyTInv_pi` gives `A : sort`, `CtxWfT.assumption` closes;
* `ctxWfT_binder_of_evTy` — the valley route: from a carried endpoint typing (`Valley.ty₁`);
* `tyLeft` / `tyRight` — the scan of a PLAIN chain for the typings its endpoints expose: the
  first (last) `of` node by regularity, `refl` chains in front (behind) passed through since
  their endpoints coincide (`tyReflChain_eq`);
* `tcLeft` / `tcRight` / `chainBinderWf` — the scan of an X input through its MATERIALIZATION
  `EvTc.val` at the caller's context. Typing is semantic: provenance transports (`wk` at any
  cutoff, `subst0`/`substLet`, `piCod`, `symm`) are no obstacle, because the materialized
  `TyConvT` lives at `Γ`, where `CtxWfT` is given. So W-X-WK / W-X-SUBST (walls of the VALLEY
  route, which must call J on the literal at ITS context) do not touch the binder question.

**The one failing case, named and pinned:** a chain that converts nothing — its
materialization is a `refl` chain (`tyReflChain`) — exposes no typing at all; the caller must
bring the Π's typing (`ctxWfT_binder_of_piTyped`; the D tile's step premises or a `Valley.ty₁`).
`chainBinderWf_isSome` is the exact characterization: both binder contexts are supplied iff the
materialized chain is not a `refl` chain. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### DT009 as data, and the binder context -/

/-- both endpoints of a conversion in a well-formed context are typed at its index, and the
    index at a sort: `endpoints3_of_envWfT`, its two fronts discharged from `EnvWfT`. -/
def convT_endpoints_data (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    HasTyT E n Γ a T ×' HasTyT E n Γ b T ×' (Σ' w, HasTyT E n Γ T (.sort w)) :=
  endpoints3_of_envWfT hW (substLetT_of_envWfT hW) (constsRightDataT_of_envWfT hW) hΓ h

/-- the binder context of a typed Π. -/
def ctxWfT_binder_of_piTyped {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B T : Expr Nat}
    (h : HasTyT E n Γ (.pi A B) T) : CtxWfT E n (.assumption A :: Γ) :=
  let r := hasTyTInv_pi h rfl
  .assumption Γ A r.1 hΓ r.2.2.1

/-- cc's route: the binder context of a LITERAL link out of a Π, by endpoint regularity. -/
def ctxWfT_binder_of_lit (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B q T : Expr Nat}
    (h : ConvT E n Γ (.pi A B) q T) : CtxWfT E n (.assumption A :: Γ) :=
  ctxWfT_binder_of_piTyped hΓ (convT_endpoints_data hW hΓ h).1

/-- the valley route: from a carried endpoint typing. -/
def ctxWfT_binder_of_evTy (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B T : Expr Nat}
    (D : EvTy R Γ (.pi A B) T) : CtxWfT E n (.assumption A :: Γ) :=
  ctxWfT_binder_of_piTyped hΓ
    (D.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))

/-! ### the scan of a plain chain -/

/-- a sort typing of a type at a context. -/
abbrev SortTyped (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (P : Expr Nat) : Type :=
  Σ' u : Level, HasTyT E n Γ P (.sort u)

/-- a plain chain that converts nothing: `refl`s only. -/
def tyReflChain : {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → Bool
  | _, _, _, .refl _ _ => true
  | _, _, _, .of .. => false
  | _, _, _, .trans _ _ _ _ d₁ d₂ => tyReflChain d₁ && tyReflChain d₂

/-- a `refl` chain's endpoints coincide. -/
theorem tyReflChain_eq : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
    tyReflChain d = true → A = B
  | _, _, _, .refl _ _, _ => rfl
  | _, _, _, .of .., h => by simp only [tyReflChain, Bool.false_eq_true] at h
  | _, _, _, .trans _ _ _ _ d₁ d₂, h => by
      have h' : tyReflChain d₁ = true ∧ tyReflChain d₂ = true := by
        simpa only [tyReflChain, Bool.and_eq_true] using h
      exact (tyReflChain_eq d₁ h'.1).trans (tyReflChain_eq d₂ h'.2)

/-- the sort typing of the LEFT endpoint a plain chain exposes: its first `of` node, by endpoint
    regularity (data); a `refl` chain in front is passed through. -/
def tyLeft (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) : {A B : Expr Nat} →
    TyConvT E n Γ A B → Option (SortTyped E n Γ A)
  | _, _, .refl _ _ => none
  | _, _, .of _ _ _ u h => some ⟨u, (convT_endpoints_data hW hΓ h).1⟩
  | _, _, .trans _ _ _ _ d₁ d₂ =>
      match tyLeft hW hΓ d₁ with
      | some s => some s
      | none =>
          if hr : tyReflChain d₁ = true then (tyReflChain_eq d₁ hr) ▸ tyLeft hW hΓ d₂ else none

/-- the sort typing of the RIGHT endpoint a plain chain exposes: its last `of` node. -/
def tyRight (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) : {A B : Expr Nat} →
    TyConvT E n Γ A B → Option (SortTyped E n Γ B)
  | _, _, .refl _ _ => none
  | _, _, .of _ _ _ u h => some ⟨u, (convT_endpoints_data hW hΓ h).2.1⟩
  | _, _, .trans _ _ _ _ d₁ d₂ =>
      match tyRight hW hΓ d₂ with
      | some s => some s
      | none =>
          if hr : tyReflChain d₂ = true then (tyReflChain_eq d₂ hr) ▸ tyRight hW hΓ d₁ else none

theorem tyLeft_isSome (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) : {A B : Expr Nat} →
    (d : TyConvT E n Γ A B) → (tyLeft hW hΓ d).isSome = !tyReflChain d
  | _, _, .refl _ _ => by simp only [tyLeft, tyReflChain, Option.isSome_none, Bool.not_true]
  | _, _, .of .. => by simp only [tyLeft, tyReflChain, Option.isSome_some, Bool.not_false]
  | _, _, .trans _ A M B d₁ d₂ => by
      have ih₁ := tyLeft_isSome hW hΓ d₁
      have ih₂ := tyLeft_isSome hW hΓ d₂
      rw [tyLeft, tyReflChain]
      cases hl : tyLeft hW hΓ d₁ with
      | some s =>
          rw [hl] at ih₁
          have hr : tyReflChain d₁ = false := by
            cases h : tyReflChain d₁ with
            | false => rfl
            | true => rw [h] at ih₁; simp at ih₁
          simp only [hr, Bool.false_and, Bool.not_false, Option.isSome_some]
      | none =>
          rw [hl] at ih₁
          have hr : tyReflChain d₁ = true := by
            cases h : tyReflChain d₁ with
            | true => rfl
            | false => rw [h] at ih₁; simp at ih₁
          simp only [hr, Bool.true_and, dif_pos hr]
          have hAM := tyReflChain_eq d₁ hr
          subst hAM
          exact ih₂

theorem tyRight_isSome (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) : {A B : Expr Nat} →
    (d : TyConvT E n Γ A B) → (tyRight hW hΓ d).isSome = !tyReflChain d
  | _, _, .refl _ _ => by simp only [tyRight, tyReflChain, Option.isSome_none, Bool.not_true]
  | _, _, .of .. => by simp only [tyRight, tyReflChain, Option.isSome_some, Bool.not_false]
  | _, _, .trans _ A M B d₁ d₂ => by
      have ih₁ := tyRight_isSome hW hΓ d₁
      have ih₂ := tyRight_isSome hW hΓ d₂
      rw [tyRight, tyReflChain]
      cases hl : tyRight hW hΓ d₂ with
      | some s =>
          rw [hl] at ih₂
          have hr : tyReflChain d₂ = false := by
            cases h : tyReflChain d₂ with
            | false => rfl
            | true => rw [h] at ih₂; simp at ih₂
          simp only [hr, Bool.and_false, Bool.not_false, Option.isSome_some]
      | none =>
          rw [hl] at ih₂
          have hr : tyReflChain d₂ = true := by
            cases h : tyReflChain d₂ with
            | true => rfl
            | false => rw [h] at ih₂; simp at ih₂
          simp only [hr, Bool.and_true, dif_pos hr]
          have hMB := tyReflChain_eq d₂ hr
          subst hMB
          exact ih₁

/-! ### the scan of an X input, through its materialization -/

/-- the LEFT endpoint typing an X input exposes: scan the materialized chain at the caller's
    context (typing is semantic; provenance transports are no obstacle). -/
def tcLeft (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (c : EvTc R Γ A B) :
    Option (SortTyped E n Γ A) :=
  tyLeft hW hΓ (c.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))

def tcRight (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (c : EvTc R Γ A B) :
    Option (SortTyped E n Γ B) :=
  tyRight hW hΓ (c.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))

/-- the two binder contexts of an X input, where its materialization exposes the Π endpoints'
    typings; `none` exactly when the chain converts nothing (`chainBinderWf_isSome`). -/
def chainBinderWf (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    Option (CtxWfT E n (.assumption A :: Γ)) × Option (CtxWfT E n (.assumption A' :: Γ)) :=
  ((tcLeft hW hΓ c).map (fun p => ctxWfT_binder_of_piTyped hΓ p.2),
   (tcRight hW hΓ c).map (fun p => ctxWfT_binder_of_piTyped hΓ p.2))

/-- the exact characterization: both binder contexts are supplied iff the materialized chain is
    not a `refl` chain. -/
theorem chainBinderWf_isSome (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    (chainBinderWf hW hΓ c).1.isSome =
      !tyReflChain (c.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)) ∧
    (chainBinderWf hW hΓ c).2.isSome =
      !tyReflChain (c.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)) := by
  have hm : ∀ {α β : Type} (f : α → β) (o : Option α), (o.map f).isSome = o.isSome := by
    intro α β f o; cases o <;> rfl
  simp only [chainBinderWf, hm, tcLeft, tcRight, tyLeft_isSome, tyRight_isSome, and_self]

/-! ### the failing case, pinned; the fixtures -/

/-- a chain that converts nothing exposes nothing. -/
theorem tcLeft_refl (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A : Expr Nat) :
    tcLeft (R := R) hW hΓ (EvTc.refl Γ A) = none := by simp only [tcLeft, EvTc.val, tyLeft]

theorem tcRight_refl (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A : Expr Nat) :
    tcRight (R := R) hW hΓ (EvTc.refl Γ A) = none := by simp only [tcRight, EvTc.val, tyRight]

/-- an `of` node is never a `refl` chain: a weakened or substituted `of` node stays an `of`
    node, so provenance transports do not hide typings from the scan. -/
theorem tyReflChain_of (Γ : LCtx) (A B : Expr Nat) (u : Level) (h : ConvT E n Γ A B (.sort u)) :
    tyReflChain (.of Γ A B u h) = false := by simp only [tyReflChain]

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the etaK fixture's request is not a `refl` chain: `cL` is, but `cR` is an `of`. -/
theorem pin_request_notRefl :
    tyReflChain (request.val (envClosed_of_envWfT EnvWfT.empty)
      (envMembersSubstStable_of_envWfT EnvWfT.empty)) = false := by
  simp only [request, annotRequest, cL, cR, EvTc.val, TyConvT.symmT, tyReflChain, Bool.and_false,
    Bool.true_and, Bool.false_and]

/-- so it exposes both binder contexts (`cL` passed through to `cR`'s regularity). -/
theorem pin_request_binderWf :
    (chainBinderWf EnvWfT.empty CtxWfT.nil request).1.isSome = true ∧
    (chainBinderWf EnvWfT.empty CtxWfT.nil request).2.isSome = true := by
  rw [(chainBinderWf_isSome EnvWfT.empty CtxWfT.nil request).1,
    (chainBinderWf_isSome EnvWfT.empty CtxWfT.nil request).2, pin_request_notRefl]
  exact ⟨rfl, rfl⟩

/-- the β fixture (`Π ≡ redex ≡ Π`, two `of` links) is not a `refl` chain either. -/
theorem pin_betaMiddle_notRefl :
    tyReflChain ((EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
      EvTc [Jd.tc betaMiddleT] [] piX piX).val (envClosed_of_envWfT EnvWfT.empty)
        (envMembersSubstStable_of_envWfT EnvWfT.empty)) = false := by
  simp only [EvTc.val, betaMiddleT, tyReflChain, Bool.and_false, Bool.and_self]

theorem pin_betaMiddle_binderWf :
    (chainBinderWf EnvWfT.empty CtxWfT.nil
      (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
        EvTc [Jd.tc betaMiddleT] [] piX piX)).1.isSome = true ∧
    (chainBinderWf EnvWfT.empty CtxWfT.nil
      (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
        EvTc [Jd.tc betaMiddleT] [] piX piX)).2.isSome = true := by
  rw [(chainBinderWf_isSome EnvWfT.empty CtxWfT.nil _).1,
    (chainBinderWf_isSome EnvWfT.empty CtxWfT.nil _).2, pin_betaMiddle_notRefl]
  exact ⟨rfl, rfl⟩

/-- a `refl` X input exposes neither (the caller brings the typing). -/
theorem pin_refl_binderWf (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A B : Expr Nat) :
    chainBinderWf (R := R) hW hΓ (EvTc.refl Γ (.pi A B)) = (none, none) := by
  simp only [chainBinderWf, tcLeft, tcRight, EvTc.val, tyLeft, tyRight, Option.map_none']

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.convT_endpoints_data
#print axioms Rcic.Declarative.F8Measure.ctxWfT_binder_of_piTyped
#print axioms Rcic.Declarative.F8Measure.ctxWfT_binder_of_lit
#print axioms Rcic.Declarative.F8Measure.ctxWfT_binder_of_evTy
#print axioms Rcic.Declarative.F8Measure.SortTyped
#print axioms Rcic.Declarative.F8Measure.tyReflChain
#print axioms Rcic.Declarative.F8Measure.tyReflChain_eq
#print axioms Rcic.Declarative.F8Measure.tyLeft
#print axioms Rcic.Declarative.F8Measure.tyRight
#print axioms Rcic.Declarative.F8Measure.tyLeft_isSome
#print axioms Rcic.Declarative.F8Measure.tyRight_isSome
#print axioms Rcic.Declarative.F8Measure.tcLeft
#print axioms Rcic.Declarative.F8Measure.tcRight
#print axioms Rcic.Declarative.F8Measure.chainBinderWf
#print axioms Rcic.Declarative.F8Measure.chainBinderWf_isSome
#print axioms Rcic.Declarative.F8Measure.tcLeft_refl
#print axioms Rcic.Declarative.F8Measure.tcRight_refl
#print axioms Rcic.Declarative.F8Measure.tyReflChain_of
#print axioms Rcic.Declarative.F8Measure.pin_request_notRefl
#print axioms Rcic.Declarative.F8Measure.pin_request_binderWf
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_notRefl
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_binderWf
#print axioms Rcic.Declarative.F8Measure.pin_refl_binderWf
