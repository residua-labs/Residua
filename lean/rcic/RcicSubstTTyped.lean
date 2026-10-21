import rcic.RcicSubstT
import rcic.RcicTypedWeaken
import rcic.RcicNativeValleyOf
import rcic.RcicTypedEnvEntry
import rcic.RcicLevelCalc

/-!
# RcicSubstTTyped — simultaneous substitution is typed: `Δ ⊢ σ : Γ` moves `HasTyT`/`ConvT`

Item 1 (syntactic half) of the ruling after segment 6.  Main has the single-variable typed
substitution (`RcicTypedSubst`: `hasTyT_subst`/`convT_subst` over `instantiate j`) and the
simultaneous substitution calculus (`RcicSubstT`: `substT`, `SubstT.cons`/`up`,
`substT_instantiate0`, `substT_up_lift`), but no typed simultaneous substitution — and the
fundamental lemma in related-substitution form needs exactly that: `M[σ]` typed at `A[σ]`,
`M[σ] ≡ M'[σ]`, and `M[σ] ≡ M[σ']` for pointwise-convertible `σ ≡ σ'`.

* `TypedSubstT E n Δ σ Γ` — every variable of `Γ` (assumption or let) goes to a term of the
  substituted type; a let-bound variable goes to a term convertible to its substituted value.
  `typedSubstT_id`; extension under a binder into an arbitrary head declaration
  (`typedSubstT_up_decl`, `typedSubstT_upLet_decl`), so that `σ` and `σ'` extend into the SAME
  context (`typedSubstT_up`, `typedSubstT_up_conv`, `typedSubstT_upLet`, `typedSubstT_upLet_conv`).
* `hasTyT_substT` / `convT_substT` — THE typed simultaneous substitution theorem (mutual), by
  induction on the derivation under `EnvWfT` and `EnvClosed` (member types/bodies are closed, so
  `substT` is the identity on them: `EnvMembersSubstTStable`), and the ι transport `IotaSubstT`
  (derived ι is stable under `substT`; the single-variable `iotaSubst` is landed, the simultaneous
  one is a named premise here).
* `convT_substT_pointwise` — `M[σ] ≡ M[σ']` at `A[σ]` for `σ ≡ σ'` pointwise (`ConvSubstT`), by
  induction on `M`'s typing.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative

/-! ### §1 — typed substitutions -/

/-- `Δ ⊢ σ : Γ`. -/
def TypedSubstT (E : ResolvedEnv) (n : Nat) (Δ : LCtx) (σ : SubstT) (Γ : LCtx) : Prop :=
  (∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A →
      Nonempty (HasTyT E n Δ (σ i) (substT σ A))) ∧
  (∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v →
      ∃ A, lookupType Γ i = some A ∧ Nonempty (ConvT E n Δ (σ i) (substT σ v) (substT σ A)))

/-- The looked-up value of a let binder is typed at the looked-up type. -/
theorem ctxWfT_lookupValue_typed {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {i : Nat} {v A : Expr Nat},
      lookupValue Γ i = some v → lookupType Γ i = some A → Nonempty (HasTyT E n Γ v A)
  | [], _, i, _, _, hv, _ => by simp [lookupValue] at hv
  | _ :: _, .assumption Γ A₀ u hΓ hA₀, 0, v, A, hv, _ => by simp [lookupValue] at hv
  | _ :: _, .letBinding Γ A₀ u v₀ hΓ hA₀ hv₀, 0, v, A, hv, hA => by
      simp only [lookupValue, List.get?_cons_zero] at hv
      simp only [lookupType, List.get?_cons_zero] at hA
      injection hv with hv; injection hA with hA
      subst hv; subst hA
      exact ⟨hasTyTWeaken (.letBinding A₀ v₀) hcl (c := 0) hv₀⟩
  | _ :: _, .assumption Γ A₀ u hΓ hA₀, i + 1, v, A, hv, hA => by
      rw [lookupValue_cons_succ] at hv
      rw [lookupType_cons_succ] at hA
      cases hv₀ : lookupValue Γ i with
      | none => rw [hv₀] at hv; exact Option.noConfusion hv
      | some v₀ =>
          cases hA₀' : lookupType Γ i with
          | none => rw [hA₀'] at hA; exact Option.noConfusion hA
          | some A' =>
              rw [hv₀] at hv; rw [hA₀'] at hA
              injection hv with hv; injection hA with hA
              subst hv; subst hA
              obtain ⟨h⟩ := ctxWfT_lookupValue_typed hcl hΓ hv₀ hA₀'
              exact ⟨hasTyTWeaken (.assumption A₀) hcl (c := 0) h⟩
  | _ :: _, .letBinding Γ A₀ u v₀ hΓ hA₀ hv₀, i + 1, v, A, hv, hA => by
      rw [lookupValue_cons_succ] at hv
      rw [lookupType_cons_succ] at hA
      cases hv₁ : lookupValue Γ i with
      | none => rw [hv₁] at hv; exact Option.noConfusion hv
      | some v₁ =>
          cases hA₁ : lookupType Γ i with
          | none => rw [hA₁] at hA; exact Option.noConfusion hA
          | some A' =>
              rw [hv₁] at hv; rw [hA₁] at hA
              injection hv with hv; injection hA with hA
              subst hv; subst hA
              obtain ⟨h⟩ := ctxWfT_lookupValue_typed hcl hΓ hv₁ hA₁
              exact ⟨hasTyTWeaken (.letBinding A₀ v₀) hcl (c := 0) h⟩

/-- The looked-up type of a variable is a type. -/
theorem ctxWfT_lookupType_sort {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {i : Nat} {A : Expr Nat},
      lookupType Γ i = some A → ∃ w, Nonempty (HasTyT E n Γ A (.sort w))
  | [], _, i, _, hA => by simp [lookupType] at hA
  | _ :: _, .assumption Γ A₀ u hΓ hA₀, 0, A, hA => by
      simp only [lookupType, List.get?_cons_zero] at hA
      injection hA with hA; subst hA
      exact ⟨u, ⟨hasTyTWeaken (.assumption A₀) hcl (c := 0) hA₀⟩⟩
  | _ :: _, .letBinding Γ A₀ u v₀ hΓ hA₀ hv₀, 0, A, hA => by
      simp only [lookupType, List.get?_cons_zero] at hA
      injection hA with hA; subst hA
      exact ⟨u, ⟨hasTyTWeaken (.letBinding A₀ v₀) hcl (c := 0) hA₀⟩⟩
  | _ :: _, .assumption Γ A₀ u hΓ hA₀, i + 1, A, hA => by
      rw [lookupType_cons_succ] at hA
      cases hA₁ : lookupType Γ i with
      | none => rw [hA₁] at hA; exact Option.noConfusion hA
      | some A' =>
          rw [hA₁] at hA; injection hA with hA; subst hA
          obtain ⟨w, ⟨h⟩⟩ := ctxWfT_lookupType_sort hcl hΓ hA₁
          exact ⟨w, ⟨hasTyTWeaken (.assumption A₀) hcl (c := 0) h⟩⟩
  | _ :: _, .letBinding Γ A₀ u v₀ hΓ hA₀ hv₀, i + 1, A, hA => by
      rw [lookupType_cons_succ] at hA
      cases hA₁ : lookupType Γ i with
      | none => rw [hA₁] at hA; exact Option.noConfusion hA
      | some A' =>
          rw [hA₁] at hA; injection hA with hA; subst hA
          obtain ⟨w, ⟨h⟩⟩ := ctxWfT_lookupType_sort hcl hΓ hA₁
          exact ⟨w, ⟨hasTyTWeaken (.letBinding A₀ v₀) hcl (c := 0) h⟩⟩

/-- A let-bound variable has a looked-up type. -/
theorem lookupType_of_lookupValue {Γ : LCtx} {i : Nat} {v : Expr Nat} (h : lookupValue Γ i = some v) :
    ∃ A, lookupType Γ i = some A := by
  obtain ⟨A₀, v₀, hg, _⟩ := lookupValue_inv h
  exact ⟨lift 0 (i + 1) A₀, by rw [lookupType, hg]⟩

/-- The identity substitution is typed. -/
theorem typedSubstT_id {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) : TypedSubstT E n Γ SubstT.id Γ := by
  refine ⟨fun i A h => ⟨?_⟩, fun i v hv => ?_⟩
  · rw [substT_id]; exact .bvar _ _ _ h
  · obtain ⟨A, hA⟩ := lookupType_of_lookupValue hv
    obtain ⟨hvt⟩ := ctxWfT_lookupValue_typed hcl hΓ hv hA
    exact ⟨A, hA, ⟨by rw [substT_id, substT_id]; exact .zetaLocal _ _ _ _ hv hA hvt⟩⟩

/-- Extension under an assumption binder, into an arbitrary head declaration `d` of `Δ` at which
    `bvar 0` has the lifted substituted type. -/
theorem typedSubstT_up_decl {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx}
    {σ : SubstT} {Γ : LCtx} (hT : TypedSubstT E n Δ σ Γ) (A : Expr Nat) (d : LocalDecl)
    (h0 : HasTyT E n (d :: Δ) (.bvar 0) (lift 0 1 (substT σ A))) :
    TypedSubstT E n (d :: Δ) σ.up (.assumption A :: Γ) := by
  refine ⟨fun i A' h => ?_, fun i v hv => ?_⟩
  · cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at h
        injection h with h
        subst h
        exact ⟨by rw [substT_up_lift]; exact h0⟩
    | succ i =>
        rw [lookupType_cons_succ] at h
        cases hA₀ : lookupType Γ i with
        | none => rw [hA₀] at h; exact Option.noConfusion h
        | some A₀ =>
            rw [hA₀] at h
            injection h with h
            subst h
            obtain ⟨ht⟩ := hT.1 i A₀ hA₀
            exact ⟨by rw [substT_up_lift]; exact hasTyTWeaken d hcl (c := 0) ht⟩
  · cases i with
    | zero => simp [lookupValue] at hv
    | succ i =>
        rw [lookupValue_cons_succ] at hv
        cases hv₀ : lookupValue Γ i with
        | none => rw [hv₀] at hv; exact Option.noConfusion hv
        | some v₀ =>
            rw [hv₀] at hv
            injection hv with hv
            subst hv
            obtain ⟨A₀, hA₀, ⟨hc⟩⟩ := hT.2 i v₀ hv₀
            refine ⟨lift 0 1 A₀, by rw [lookupType_cons_succ, hA₀]; rfl, ⟨?_⟩⟩
            rw [substT_up_lift, substT_up_lift]
            exact convTWeaken d hcl (c := 0) hc

/-- Extension under a let binder, into an arbitrary head declaration at which `bvar 0` has the
    lifted substituted type and is convertible to the lifted substituted value. -/
theorem typedSubstT_upLet_decl {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx}
    {σ : SubstT} {Γ : LCtx} (hT : TypedSubstT E n Δ σ Γ) (A v : Expr Nat) (d : LocalDecl)
    (h0 : HasTyT E n (d :: Δ) (.bvar 0) (lift 0 1 (substT σ A)))
    (hval : ConvT E n (d :: Δ) (.bvar 0) (lift 0 1 (substT σ v)) (lift 0 1 (substT σ A))) :
    TypedSubstT E n (d :: Δ) σ.up (.letBinding A v :: Γ) := by
  refine ⟨fun i A' h => ?_, fun i v' hv' => ?_⟩
  · cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at h
        injection h with h
        subst h
        exact ⟨by rw [substT_up_lift]; exact h0⟩
    | succ i =>
        rw [lookupType_cons_succ] at h
        cases hA₀ : lookupType Γ i with
        | none => rw [hA₀] at h; exact Option.noConfusion h
        | some A₀ =>
            rw [hA₀] at h
            injection h with h
            subst h
            obtain ⟨ht⟩ := hT.1 i A₀ hA₀
            exact ⟨by rw [substT_up_lift]; exact hasTyTWeaken d hcl (c := 0) ht⟩
  · cases i with
    | zero =>
        simp only [lookupValue, List.get?_cons_zero] at hv'
        injection hv' with hv'
        subst hv'
        refine ⟨lift 0 1 A, rfl, ⟨?_⟩⟩
        rw [substT_up_lift, substT_up_lift]
        exact hval
    | succ i =>
        rw [lookupValue_cons_succ] at hv'
        cases hv₀ : lookupValue Γ i with
        | none => rw [hv₀] at hv'; exact Option.noConfusion hv'
        | some v₀ =>
            rw [hv₀] at hv'
            injection hv' with hv'
            subst hv'
            obtain ⟨A₀, hA₀, ⟨hc⟩⟩ := hT.2 i v₀ hv₀
            refine ⟨lift 0 1 A₀, by rw [lookupType_cons_succ, hA₀]; rfl, ⟨?_⟩⟩
            rw [substT_up_lift, substT_up_lift]
            exact convTWeaken d hcl (c := 0) hc

/-- The canonical extensions. -/
theorem typedSubstT_up {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx} {σ : SubstT}
    {Γ : LCtx} (hT : TypedSubstT E n Δ σ Γ) (A : Expr Nat) :
    TypedSubstT E n (.assumption (substT σ A) :: Δ) σ.up (.assumption A :: Γ) :=
  typedSubstT_up_decl hcl hT A _ (.bvar _ 0 _ rfl)

theorem typedSubstT_upLet {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx} {σ : SubstT}
    {Γ : LCtx} (hT : TypedSubstT E n Δ σ Γ) (A v : Expr Nat)
    (hv : HasTyT E n Δ (substT σ v) (substT σ A)) :
    TypedSubstT E n (.letBinding (substT σ A) (substT σ v) :: Δ) σ.up (.letBinding A v :: Γ) :=
  typedSubstT_upLet_decl hcl hT A v _ (.bvar _ 0 _ rfl)
    (.zetaLocal _ 0 _ _ rfl rfl (hasTyTWeaken (.letBinding (substT σ A) (substT σ v)) hcl (c := 0) hv))

/-- `σ'` extended into the context `σ` builds, along `A[σ'] ≡ A[σ]`. -/
theorem typedSubstT_up_conv {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx}
    {σ σ' : SubstT} {Γ : LCtx} (hT' : TypedSubstT E n Δ σ' Γ) (A : Expr Nat) (u : Level)
    (hAc : ConvT E n Δ (substT σ A) (substT σ' A) (.sort u)) :
    TypedSubstT E n (.assumption (substT σ A) :: Δ) σ'.up (.assumption A :: Γ) :=
  typedSubstT_up_decl hcl hT' A _
    (.conv _ _ _ _ u (.bvar _ 0 _ rfl) (convTWeaken (.assumption (substT σ A)) hcl (c := 0) hAc))

theorem typedSubstT_upLet_conv {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx}
    {σ σ' : SubstT} {Γ : LCtx} (hT' : TypedSubstT E n Δ σ' Γ) (A v : Expr Nat) (u : Level)
    (hv : HasTyT E n Δ (substT σ v) (substT σ A))
    (hAc : ConvT E n Δ (substT σ A) (substT σ' A) (.sort u))
    (hvc : ConvT E n Δ (substT σ v) (substT σ' v) (substT σ A)) :
    TypedSubstT E n (.letBinding (substT σ A) (substT σ v) :: Δ) σ'.up (.letBinding A v :: Γ) :=
  let d : LocalDecl := .letBinding (substT σ A) (substT σ v)
  typedSubstT_upLet_decl hcl hT' A v d
    (.conv _ _ _ _ u (.bvar _ 0 _ rfl) (convTWeaken d hcl (c := 0) hAc))
    (.tyConv _ _ _ _ _ u
      (.trans _ _ _ _ _ (.zetaLocal _ 0 _ _ rfl rfl (hasTyTWeaken d hcl (c := 0) hv))
        (convTWeaken d hcl (c := 0) hvc))
      (convTWeaken d hcl (c := 0) hAc))

/-! ### §2 — member stability and ι transport -/

/-- `substT` is the identity on the (closed) member types and bodies. -/
def EnvMembersSubstTStable (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m →
    (∀ ls σ, substT σ (instantiateLevels ls m.mtype) = instantiateLevels ls m.mtype) ∧
    (∀ b, m.body = some b → ∀ ls σ, substT σ (instantiateLevels ls b) = instantiateLevels ls b)

theorem envMembersSubstTStable_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E) :
    EnvMembersSubstTStable E := by
  intro r m hm
  obtain ⟨hty, hbody⟩ := hcl r m hm
  refine ⟨fun ls σ => substT_closed (fun k => ?_) σ, fun b hb ls σ => substT_closed (fun k => ?_) σ⟩
  · rw [lift_instantiateLevels, hty k]
  · rw [lift_instantiateLevels, hbody b hb k]

/-- Derived ι is stable under simultaneous substitution (a named premise: the landed
    single-variable `iotaSubst`, iterated). -/
def IotaSubstT (E : ResolvedEnv) : Prop :=
  ∀ lhs rhs, DerivedIota E lhs rhs → ∀ σ : SubstT,
    Nonempty (DerivedIota E (substT σ lhs) (substT σ rhs))

/-- The literal expansion is closed. -/
theorem substT_natExpand (σ : SubstT) (t : Nat) : substT σ (natExpand t) = natExpand t :=
  substT_closed (fun k => natExpand_lift k 1 t) σ

/-! ### §3 — the typed simultaneous substitution theorem -/

mutual

/-- **Typed simultaneous substitution, typing side.** -/
def hasTyT_substT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E) :
    {Γ : LCtx} → CtxWfT E n Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    {Δ : LCtx} → CtxWfT E n Δ → {σ : SubstT} → TypedSubstT E n Δ σ Γ →
    Nonempty (HasTyT E n Δ (substT σ e) (substT σ A))
  | Γ, hΓ, e, A, h, Δ, hΔ, σ, hT =>
      match h with
      | .sort _ l => ⟨.sort _ l⟩
      | .bvar _ i A hlook => hT.1 i A hlook
      | .const _ r ls m hres hlen hwf => by
          rw [(hst r m hres).1 ls σ]
          exact ⟨.const _ r ls m hres hlen hwf⟩
      | .pi Γ A u B v hA hB => by
          obtain ⟨hA'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hB'⟩ := hasTyT_substT hW hcl hst hι (.assumption Γ A u hΓ hA) hB
            (.assumption Δ _ u hΔ hA') (typedSubstT_up hcl hT A)
          exact ⟨.pi Δ _ u _ v hA' hB'⟩
      | .lam Γ A u body B hA hbody => by
          obtain ⟨hA'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hb'⟩ := hasTyT_substT hW hcl hst hι (.assumption Γ A u hΓ hA) hbody
            (.assumption Δ _ u hΔ hA') (typedSubstT_up hcl hT A)
          exact ⟨.lam Δ _ u _ _ hA' hb'⟩
      | .app Γ f a A B hf ha => by
          obtain ⟨hf'⟩ := hasTyT_substT hW hcl hst hι hΓ hf hΔ hT
          obtain ⟨ha'⟩ := hasTyT_substT hW hcl hst hι hΓ ha hΔ hT
          rw [substT_instantiate0]
          exact ⟨.app Δ _ _ _ _ hf' ha'⟩
      | .letE Γ A u value B body hA hv hb => by
          obtain ⟨hA'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hv'⟩ := hasTyT_substT hW hcl hst hι hΓ hv hΔ hT
          obtain ⟨hb'⟩ := hasTyT_substT hW hcl hst hι (.letBinding Γ A u value hΓ hA hv) hb
            (.letBinding Δ _ u _ hΔ hA' hv') (typedSubstT_upLet hcl hT A value hv')
          rw [substT_instantiate0]
          exact ⟨.letE Δ _ u _ _ _ hA' hv' hb'⟩
      | .lit Γ t T hexp => by
          obtain ⟨h'⟩ := hasTyT_substT hW hcl hst hι hΓ hexp hΔ hT
          rw [substT_natExpand] at h'
          exact ⟨.lit Δ t _ h'⟩
      | .conv Γ e A B u h hc => by
          obtain ⟨h'⟩ := hasTyT_substT hW hcl hst hι hΓ h hΔ hT
          obtain ⟨hc'⟩ := convT_substT hW hcl hst hι hΓ hc hΔ hT
          exact ⟨.conv Δ _ _ _ u h' hc'⟩

/-- **Typed simultaneous substitution, conversion side.** -/
def convT_substT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E) :
    {Γ : LCtx} → CtxWfT E n Γ → {a b T : Expr Nat} → ConvT E n Γ a b T →
    {Δ : LCtx} → CtxWfT E n Δ → {σ : SubstT} → TypedSubstT E n Δ σ Γ →
    Nonempty (ConvT E n Δ (substT σ a) (substT σ b) (substT σ T))
  | Γ, hΓ, a, b, T, hc0, Δ, hΔ, σ, hT =>
      match hc0 with
      | .refl _ a A h => by
          obtain ⟨h'⟩ := hasTyT_substT hW hcl hst hι hΓ h hΔ hT
          exact ⟨.refl Δ _ _ h'⟩
      | .symm _ a b A h => by
          obtain ⟨h'⟩ := convT_substT hW hcl hst hι hΓ h hΔ hT
          exact ⟨.symm Δ _ _ _ h'⟩
      | .trans _ a b c A h1 h2 => by
          obtain ⟨h1'⟩ := convT_substT hW hcl hst hι hΓ h1 hΔ hT
          obtain ⟨h2'⟩ := convT_substT hW hcl hst hι hΓ h2 hΔ hT
          exact ⟨.trans Δ _ _ _ _ h1' h2'⟩
      | .beta Γ A body arg B u hA hbody harg => by
          obtain ⟨hA'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hbody'⟩ := hasTyT_substT hW hcl hst hι (.assumption Γ A u hΓ hA) hbody
            (.assumption Δ _ u hΔ hA') (typedSubstT_up hcl hT A)
          obtain ⟨harg'⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT
          rw [substT_instantiate0, substT_instantiate0]
          exact ⟨.beta Δ _ _ _ _ u hA' hbody' harg'⟩
      | .zeta Γ A value body B u hA hv hb => by
          obtain ⟨hA'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hv'⟩ := hasTyT_substT hW hcl hst hι hΓ hv hΔ hT
          obtain ⟨hb'⟩ := hasTyT_substT hW hcl hst hι (.letBinding Γ A u value hΓ hA hv) hb
            (.letBinding Δ _ u _ hΔ hA' hv') (typedSubstT_upLet hcl hT A value hv')
          rw [substT_instantiate0, substT_instantiate0]
          exact ⟨.zeta Δ _ _ _ _ u hA' hv' hb'⟩
      | .zetaLocal Γ i A v hval hty _ => by
          obtain ⟨A', hA', ⟨hc⟩⟩ := hT.2 i v hval
          rw [hty] at hA'
          injection hA' with hA'
          subst hA'
          exact ⟨hc⟩
      | .delta Γ r ls m b hres hbody htr hlen hwf hb => by
          obtain ⟨hb'⟩ := hasTyT_substT hW hcl hst hι hΓ hb hΔ hT
          rw [(hst r m hres).1 ls σ, (hst r m hres).2 b hbody ls σ] at hb' ⊢
          exact ⟨.delta Δ r ls m b hres hbody htr hlen hwf hb'⟩
      | .iota Γ lhs rhs T h hlhs hrhs => by
          obtain ⟨hlhs'⟩ := hasTyT_substT hW hcl hst hι hΓ hlhs hΔ hT
          obtain ⟨hrhs'⟩ := hasTyT_substT hW hcl hst hι hΓ hrhs hΔ hT
          obtain ⟨h'⟩ := hι lhs rhs h σ
          exact ⟨.iota Δ _ _ _ h' hlhs' hrhs'⟩
      | .lit Γ t exp T h hexp => by
          obtain ⟨hexp'⟩ := hasTyT_substT hW hcl hst hι hΓ hexp hΔ hT
          cases h with
          | of =>
              rw [substT_natExpand] at hexp' ⊢
              exact ⟨.lit Δ t _ _ (.of t) hexp'⟩
      | .app Γ f g a b A B h1 h2 => by
          obtain ⟨h1'⟩ := convT_substT hW hcl hst hι hΓ h1 hΔ hT
          obtain ⟨h2'⟩ := convT_substT hW hcl hst hι hΓ h2 hΔ hT
          rw [substT_instantiate0]
          exact ⟨.app Δ _ _ _ _ _ _ h1' h2'⟩
      | .lam Γ A A' b b' B u hA hb => by
          obtain ⟨hA'⟩ := convT_substT hW hcl hst hι hΓ hA hΔ hT
          have hAty : HasTyT E n Γ A (.sort u) := (convEnds hW hΓ hA).1
          have hAty' : HasTyT E n Δ (substT σ A) (.sort u) := (convEnds hW hΔ hA').1
          obtain ⟨hb'⟩ := convT_substT hW hcl hst hι (.assumption Γ A u hΓ hAty) hb
            (.assumption Δ _ u hΔ hAty') (typedSubstT_up hcl hT A)
          exact ⟨.lam Δ _ _ _ _ _ u hA' hb'⟩
      | .pi Γ A A' B B' u v hA hB => by
          obtain ⟨hA'⟩ := convT_substT hW hcl hst hι hΓ hA hΔ hT
          have hAty : HasTyT E n Γ A (.sort u) := (convEnds hW hΓ hA).1
          have hAty' : HasTyT E n Δ (substT σ A) (.sort u) := (convEnds hW hΔ hA').1
          obtain ⟨hB'⟩ := convT_substT hW hcl hst hι (.assumption Γ A u hΓ hAty) hB
            (.assumption Δ _ u hΔ hAty') (typedSubstT_up hcl hT A)
          exact ⟨.pi Δ _ _ _ _ u v hA' hB'⟩
      | .letE Γ A A' v v' b b' B u hA hv hb => by
          obtain ⟨hA'⟩ := convT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hv'⟩ := convT_substT hW hcl hst hι hΓ hv hΔ hT
          have hAty : HasTyT E n Γ A (.sort u) := (convEnds hW hΓ hA).1
          have hvty : HasTyT E n Γ v A := (convEnds hW hΓ hv).1
          have hAty' : HasTyT E n Δ (substT σ A) (.sort u) := (convEnds hW hΔ hA').1
          have hvty' : HasTyT E n Δ (substT σ v) (substT σ A) := (convEnds hW hΔ hv').1
          obtain ⟨hb'⟩ := convT_substT hW hcl hst hι (.letBinding Γ A u v hΓ hAty hvty) hb
            (.letBinding Δ _ u _ hΔ hAty' hvty') (typedSubstT_upLet hcl hT A v hvty')
          rw [substT_instantiate0]
          exact ⟨.letE Δ _ _ _ _ _ _ _ u hA' hv' hb'⟩
      | .sorts _ l₁ l₂ h => ⟨.sorts Δ l₁ l₂ h⟩
      | .consts _ r ls ls' m hres hlen hwf hwf' h => by
          rw [(hst r m hres).1 ls σ]
          exact ⟨.consts Δ r ls ls' m hres hlen hwf hwf' h⟩
      | .eta Γ f A B h => by
          obtain ⟨h'⟩ := hasTyT_substT hW hcl hst hι hΓ h hΔ hT
          simp only [substT]
          rw [substT_up_lift]
          exact ⟨.eta Δ _ _ _ h'⟩
      | .irr Γ P p q hP hp hq => by
          obtain ⟨hP'⟩ := hasTyT_substT hW hcl hst hι hΓ hP hΔ hT
          obtain ⟨hp'⟩ := hasTyT_substT hW hcl hst hι hΓ hp hΔ hT
          obtain ⟨hq'⟩ := hasTyT_substT hW hcl hst hι hΓ hq hΔ hT
          exact ⟨.irr Δ _ _ _ hP' hp' hq'⟩
      | .tyConv Γ a b A A' u h hA => by
          obtain ⟨h'⟩ := convT_substT hW hcl hst hι hΓ h hΔ hT
          obtain ⟨hA'⟩ := convT_substT hW hcl hst hι hΓ hA hΔ hT
          exact ⟨.tyConv Δ _ _ _ _ u h' hA'⟩

end

/-! ### §4 — pointwise-convertible substitutions give convertible instances -/

/-- `σ ≡ σ'` pointwise at the substituted types. -/
def ConvSubstT (E : ResolvedEnv) (n : Nat) (Δ : LCtx) (σ σ' : SubstT) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A →
    Nonempty (ConvT E n Δ (σ i) (σ' i) (substT σ A))

/-- Extension of a pointwise conversion under a binder of `Γ` (`dΓ`), into the head `d` of `Δ`
    at which `bvar 0` has the lifted substituted type. -/
theorem convSubstT_up_decl {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx}
    {σ σ' : SubstT} {Γ : LCtx} (hc : ConvSubstT E n Δ σ σ' Γ) (dΓ d : LocalDecl) (A : Expr Nat)
    (hdΓ : lookupType (dΓ :: Γ) 0 = some (lift 0 1 A))
    (h0 : HasTyT E n (d :: Δ) (.bvar 0) (lift 0 1 (substT σ A))) :
    ConvSubstT E n (d :: Δ) σ.up σ'.up (dΓ :: Γ) := by
  intro i A' h
  cases i with
  | zero =>
      rw [hdΓ] at h
      injection h with h
      subst h
      rw [substT_up_lift]
      exact ⟨.refl _ _ _ h0⟩
  | succ i =>
      rw [lookupType_cons_succ] at h
      cases hA₀ : lookupType Γ i with
      | none => rw [hA₀] at h; exact Option.noConfusion h
      | some A₀ =>
          rw [hA₀] at h
          injection h with h
          subst h
          obtain ⟨hc₀⟩ := hc i A₀ hA₀
          rw [substT_up_lift]
          exact ⟨convTWeaken d hcl (c := 0) hc₀⟩

/-- **Pointwise-convertible substitutions give convertible instances.** -/
def convT_substT_pointwise {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E) :
    {Γ : LCtx} → CtxWfT E n Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    {Δ : LCtx} → CtxWfT E n Δ → {σ σ' : SubstT} → TypedSubstT E n Δ σ Γ → TypedSubstT E n Δ σ' Γ →
    ConvSubstT E n Δ σ σ' Γ →
    Nonempty (ConvT E n Δ (substT σ e) (substT σ' e) (substT σ A))
  | Γ, hΓ, e, A, h, Δ, hΔ, σ, σ', hT, hT', hc =>
      match h with
      | .sort _ l => ⟨.refl Δ _ _ (.sort Δ l)⟩
      | .bvar _ i A hlook => hc i A hlook
      | .const _ r ls m hres hlen hwf => by
          rw [(hst r m hres).1 ls σ]
          exact ⟨.refl Δ _ _ (.const Δ r ls m hres hlen hwf)⟩
      | .pi Γ A u B v hA hB => by
          obtain ⟨hA'⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hc
          obtain ⟨hAty'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hB'⟩ := convT_substT_pointwise hW hcl hst hι (.assumption Γ A u hΓ hA) hB
            (.assumption Δ _ u hΔ hAty') (typedSubstT_up hcl hT A) (typedSubstT_up_conv hcl hT' A u hA')
            (convSubstT_up_decl hcl hc _ _ A rfl (.bvar _ 0 _ rfl))
          exact ⟨.pi Δ _ _ _ _ u v hA' hB'⟩
      | .lam Γ A u body B hA hbody => by
          obtain ⟨hA'⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hc
          obtain ⟨hAty'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hb'⟩ := convT_substT_pointwise hW hcl hst hι (.assumption Γ A u hΓ hA) hbody
            (.assumption Δ _ u hΔ hAty') (typedSubstT_up hcl hT A) (typedSubstT_up_conv hcl hT' A u hA')
            (convSubstT_up_decl hcl hc _ _ A rfl (.bvar _ 0 _ rfl))
          exact ⟨.lam Δ _ _ _ _ _ u hA' hb'⟩
      | .app Γ f a A B hf ha => by
          obtain ⟨hf'⟩ := convT_substT_pointwise hW hcl hst hι hΓ hf hΔ hT hT' hc
          obtain ⟨ha'⟩ := convT_substT_pointwise hW hcl hst hι hΓ ha hΔ hT hT' hc
          rw [substT_instantiate0]
          exact ⟨.app Δ _ _ _ _ _ _ hf' ha'⟩
      | .letE Γ A u value B body hA hv hb => by
          obtain ⟨hA'⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hc
          obtain ⟨hv'⟩ := convT_substT_pointwise hW hcl hst hι hΓ hv hΔ hT hT' hc
          obtain ⟨hAty'⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
          obtain ⟨hvty'⟩ := hasTyT_substT hW hcl hst hι hΓ hv hΔ hT
          obtain ⟨hb'⟩ := convT_substT_pointwise hW hcl hst hι (.letBinding Γ A u value hΓ hA hv) hb
            (.letBinding Δ _ u _ hΔ hAty' hvty') (typedSubstT_upLet hcl hT A value hvty')
            (typedSubstT_upLet_conv hcl hT' A value u hvty' hA' hv')
            (convSubstT_up_decl hcl hc _ _ A rfl (.bvar _ 0 _ rfl))
          rw [substT_instantiate0]
          exact ⟨.letE Δ _ _ _ _ _ _ _ u hA' hv' hb'⟩
      | .lit Γ t T hexp => by
          obtain ⟨h'⟩ := hasTyT_substT hW hcl hst hι hΓ hexp hΔ hT
          rw [substT_natExpand] at h'
          exact ⟨.refl Δ _ _ (.lit Δ t _ h')⟩
      | .conv Γ e A B u h hcv => by
          obtain ⟨h'⟩ := convT_substT_pointwise hW hcl hst hι hΓ h hΔ hT hT' hc
          obtain ⟨hcv'⟩ := convT_substT hW hcl hst hι hΓ hcv hΔ hT
          exact ⟨.tyConv Δ _ _ _ _ u h' hcv'⟩

#print axioms TypedSubstT
#print axioms ctxWfT_lookupValue_typed
#print axioms ctxWfT_lookupType_sort
#print axioms lookupType_of_lookupValue
#print axioms typedSubstT_id
#print axioms typedSubstT_up_decl
#print axioms typedSubstT_upLet_decl
#print axioms typedSubstT_up
#print axioms typedSubstT_upLet
#print axioms typedSubstT_up_conv
#print axioms typedSubstT_upLet_conv
#print axioms EnvMembersSubstTStable
#print axioms envMembersSubstTStable_of_envClosed
#print axioms IotaSubstT
#print axioms substT_natExpand
#print axioms hasTyT_substT
#print axioms convT_substT
#print axioms ConvSubstT
#print axioms convSubstT_up_decl
#print axioms convT_substT_pointwise

end Rcic.Declarative.NativeValleys.TypedModelAudit
