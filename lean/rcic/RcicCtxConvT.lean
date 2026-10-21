import rcic.RcicTypedWeaken

/-!
# `CtxConvT` — pointwise-convertible contexts for the plain typed judgment

The plain (`*T`) twin of `RcicAnnCtxConv` §1/§3, for the F-ι★-7 half of the
Seg-B substitution kit (PiRow ATR route, #6293 — plain ruling).

Two contexts whose declarations are pointwise convertible (`CtxConvT`: the
same declaration, or an assumption / let-binding whose type and value are
convertible, typed, in the target context) type the same terms at the same
types: `hasTyT_ctx`, `convT_ctx`. A variable's type in the target is the
original or a convertible one (`ctxConvT_lookupType`, `TyLookT`), and the
`bvar` case retypes through `.conv`; a let-bound variable's value is the
original or a convertible one (`ctxConvT_lookupValue`, `ValLookT`), and the
`zetaLocal` case composes the ζ-step with that conversion through `tyConv`
and `trans`. The binder cases extend the conversion by the SAME declaration
(`CtxConvT.same`), which needs no typing.

DATA DISCIPLINE: unlike `CtxConvA` (a `Prop` with `Nonempty` fields), this
stack is TYPE-valued throughout — `CtxConvT` carries the raw `HasTyT`/`ConvT`
fields and `TyLookT`/`ValLookT`/`ctxConvT_lookupType` return `Σ'`-data — so
`hasTyT_ctx`/`convT_ctx` yield the judgments themselves, which the `PEqT`
`proof` leaf's four typing fields consume directly (the `*A` version stops
at `Nonempty` because a `Prop` context relation cannot eliminate into
`Type`; `CtxWfT`/`SubstTyA`/`ConvSubstA` set the Type-valued precedent).

Difference from the `*A` side: `ConvT.iota` carries a `DerivedIota` witness,
which reads the environment only — never the context — so the `.iota` arm
needs no `IotaRecHead`-style premise; `.consts` carries no typing premise at
all. The only gates are `EnvClosed E` (the weakenings the lookup transports
consume) and, downstream, `EnvMembersSubstStable E` for the substitution
kit; `envClosed_of_envWfT` / `envMembersSubstStable_of_envWfT` supply both
at `EnvWfT` call sites.
-/

namespace Rcic.Declarative

/-! ## (1) pointwise convertible contexts -/

inductive CtxConvT (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type
  | nil : CtxConvT E n [] []
  /-- the same declaration on both sides: no typing needed. -/
  | same {Γ Γ' : LCtx} (d : LocalDecl) (h : CtxConvT E n Γ Γ') :
      CtxConvT E n (d :: Γ) (d :: Γ')
  | assumption {Γ Γ' : LCtx} {A A' : Expr Nat} {u : Level} (h : CtxConvT E n Γ Γ')
      (hA : HasTyT E n Γ' A (.sort u)) (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u)) :
      CtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ')
  | letBinding {Γ Γ' : LCtx} {A A' v v' : Expr Nat} {u : Level} (h : CtxConvT E n Γ Γ')
      (hA : HasTyT E n Γ' A (.sort u)) (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u))
      (hv' : HasTyT E n Γ' v' A') (hcv : ConvT E n Γ' v v' A) :
      CtxConvT E n (.letBinding A v :: Γ) (.letBinding A' v' :: Γ')

def ctxConvT_refl {E : ResolvedEnv} {n : Nat} :
    (Γ : LCtx) → CtxConvT E n Γ Γ
  | [] => .nil
  | d :: Γ => .same d (ctxConvT_refl Γ)

section Look
variable {E : ResolvedEnv} {n : Nat}

/-- a variable's type in the target: the original, or a convertible one, both typed. -/
inductive TyLookT (E : ResolvedEnv) (n : Nat) (Γ' : LCtx) (A A' : Expr Nat) : Type
  | same (h : A' = A) : TyLookT E n Γ' A A'
  | conv (u : Level) (hA : HasTyT E n Γ' A (.sort u)) (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u)) : TyLookT E n Γ' A A'

/-- a let-bound variable's value in the target: the original, or a convertible one. -/
inductive ValLookT (E : ResolvedEnv) (n : Nat) (Γ' : LCtx) (A A' v v' : Expr Nat) : Type
  | same (hA : A' = A) (hv : v' = v) : ValLookT E n Γ' A A' v v'
  | conv (u : Level) (hA : HasTyT E n Γ' A (.sort u)) (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u)) (hv' : HasTyT E n Γ' v' A')
      (hcv : ConvT E n Γ' v v' A) : ValLookT E n Γ' A A' v v'

def tyLookT_lift (hcl : EnvClosed E) (d : LocalDecl) {Γ' : LCtx}
    {A A' : Expr Nat} (h : TyLookT E n Γ' A A') :
    TyLookT E n (d :: Γ') (lift 0 1 A) (lift 0 1 A') :=
  match h with
  | TyLookT.same e => TyLookT.same (by rw [e])
  | TyLookT.conv u hA hA' hc => TyLookT.conv u (hasTyTWeaken d hcl (c := 0) hA)
      (hasTyTWeaken d hcl (c := 0) hA') (convTWeaken d hcl (c := 0) hc)

def valLookT_lift (hcl : EnvClosed E) (d : LocalDecl) {Γ' : LCtx}
    {A A' v v' : Expr Nat} (h : ValLookT E n Γ' A A' v v') :
    ValLookT E n (d :: Γ') (lift 0 1 A) (lift 0 1 A') (lift 0 1 v) (lift 0 1 v') :=
  match h with
  | ValLookT.same eA ev => ValLookT.same (by rw [eA]) (by rw [ev])
  | ValLookT.conv u hA hA' hc hv' hcv => ValLookT.conv u (hasTyTWeaken d hcl (c := 0) hA)
      (hasTyTWeaken d hcl (c := 0) hA') (convTWeaken d hcl (c := 0) hc)
      (hasTyTWeaken d hcl (c := 0) hv') (convTWeaken d hcl (c := 0) hcv)

/-- the tail step of the type lookup: index `i + 1` reads the tail at `i`, lifted. -/
def lookupType_succ_convT (hcl : EnvClosed E) {Γ Γ' : LCtx} (d d' : LocalDecl)
    {i : Nat}
    (ih : ∀ {A₀ : Expr Nat}, lookupType Γ i = some A₀ →
      Σ' A', lookupType Γ' i = some A' ×' TyLookT E n Γ' A₀ A')
    {A : Expr Nat} (h : lookupType (d :: Γ) (i + 1) = some A) :
    Σ' A', lookupType (d' :: Γ') (i + 1) = some A' ×' TyLookT E n (d' :: Γ') A A' := by
  rw [lookupType_cons_succ] at h
  cases hΓ : lookupType Γ i with
  | none => rw [hΓ] at h; cases h
  | some A₀ =>
      rw [hΓ] at h
      cases h
      obtain ⟨A', hA', hl⟩ := ih hΓ
      exact ⟨lift 0 1 A', by rw [lookupType_cons_succ, hA']; rfl, tyLookT_lift hcl d' hl⟩

/-- the tail step of the value lookup: index `i + 1` reads the tail at `i`, lifted. -/
def lookupValue_succ_convT (hcl : EnvClosed E) {Γ Γ' : LCtx} (d d' : LocalDecl)
    {i : Nat}
    (ih : ∀ {v₀ : Expr Nat}, lookupValue Γ i = some v₀ →
      Σ' v' A A', lookupType Γ i = some A ×' lookupValue Γ' i = some v' ×'
        lookupType Γ' i = some A' ×' ValLookT E n Γ' A A' v₀ v')
    {v : Expr Nat} (h : lookupValue (d :: Γ) (i + 1) = some v) :
    Σ' v' A A', lookupType (d :: Γ) (i + 1) = some A ×' lookupValue (d' :: Γ') (i + 1) = some v' ×'
      lookupType (d' :: Γ') (i + 1) = some A' ×' ValLookT E n (d' :: Γ') A A' v v' := by
  rw [lookupValue_cons_succ] at h
  cases hΓ : lookupValue Γ i with
  | none => rw [hΓ] at h; cases h
  | some v₀ =>
      rw [hΓ] at h
      cases h
      obtain ⟨v', A, A', hty, hval', hty', hl⟩ := ih hΓ
      exact ⟨lift 0 1 v', lift 0 1 A, lift 0 1 A',
        by rw [lookupType_cons_succ, hty]; rfl, by rw [lookupValue_cons_succ, hval']; rfl,
        by rw [lookupType_cons_succ, hty']; rfl, valLookT_lift hcl d' hl⟩

def ctxConvT_lookupType (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → (i : Nat) → {A : Expr Nat} →
    lookupType Γ i = some A → Σ' A', lookupType Γ' i = some A' ×' TyLookT E n Γ' A A'
  | _, _, .nil, i, _, h => by cases i <;> cases h
  | _, _, .same d _, 0, A, h => ⟨A, by cases d <;> exact h, TyLookT.same rfl⟩
  | _, _, .same d hcc, i + 1, _, h =>
      lookupType_succ_convT hcl d d (fun h₀ => ctxConvT_lookupType hcl hcc i h₀) h
  | _, _, .assumption (A := A₀) (A' := A₀') (u := u) _ hA hA' hc, 0, _, h => by
      cases h
      exact ⟨lift 0 1 A₀', rfl, tyLookT_lift hcl (.assumption A₀') (TyLookT.conv u hA hA' hc)⟩
  | _, _, .assumption (A := A₀) (A' := A₀') hcc _ _ _, i + 1, _, h =>
      lookupType_succ_convT hcl (.assumption A₀) (.assumption A₀')
        (fun h₀ => ctxConvT_lookupType hcl hcc i h₀) h
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') (u := u) _ hA hA' hc _ _, 0, _, h => by
      cases h
      exact ⟨lift 0 1 A₀', rfl,
        tyLookT_lift hcl (.letBinding A₀' v₀') (TyLookT.conv u hA hA' hc)⟩
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') hcc _ _ _ _ _, i + 1, _, h =>
      lookupType_succ_convT hcl (.letBinding A₀ v₀) (.letBinding A₀' v₀')
        (fun h₀ => ctxConvT_lookupType hcl hcc i h₀) h

def ctxConvT_lookupValue (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → (i : Nat) → {v : Expr Nat} →
    lookupValue Γ i = some v →
    Σ' v' A A', lookupType Γ i = some A ×' lookupValue Γ' i = some v' ×'
      lookupType Γ' i = some A' ×' ValLookT E n Γ' A A' v v'
  | _, _, .nil, i, _, h => by cases i <;> cases h
  | _, _, .same (.assumption a) _, 0, _, h => by cases h
  | _, _, .same (.letBinding a w) _, 0, _, h => by
      cases h
      exact ⟨lift 0 1 w, lift 0 1 a, lift 0 1 a, rfl, rfl, rfl, ValLookT.same rfl rfl⟩
  | _, _, .same d hcc, i + 1, _, h =>
      lookupValue_succ_convT hcl d d (fun h₀ => ctxConvT_lookupValue hcl hcc i h₀) h
  | _, _, .assumption _ _ _ _, 0, _, h => by cases h
  | _, _, .assumption (A := A₀) (A' := A₀') hcc _ _ _, i + 1, _, h =>
      lookupValue_succ_convT hcl (.assumption A₀) (.assumption A₀')
        (fun h₀ => ctxConvT_lookupValue hcl hcc i h₀) h
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') (u := u) _ hA hA' hc hv' hcv, 0, _, h => by
      cases h
      exact ⟨lift 0 1 v₀', lift 0 1 A₀, lift 0 1 A₀', rfl, rfl, rfl,
        valLookT_lift hcl (.letBinding A₀' v₀') (ValLookT.conv u hA hA' hc hv' hcv)⟩
  | _, _, .letBinding (A := A₀) (A' := A₀') (v := v₀) (v' := v₀') hcc _ _ _ _ _, i + 1, _, h =>
      lookupValue_succ_convT hcl (.letBinding A₀ v₀) (.letBinding A₀' v₀')
        (fun h₀ => ctxConvT_lookupValue hcl hcc i h₀) h

end Look

/-! ## (2) the judgments under context conversion -/

section Conv
variable {E : ResolvedEnv} {n : Nat}

mutual

/-- typing transports across pointwise-convertible contexts. `bvar` retypes
    through `.conv` at the lookup's convertible type; binder cases extend by
    `.same`. -/
def hasTyT_ctx (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → {e A : Expr Nat} → HasTyT E n Γ e A →
    HasTyT E n Γ' e A
  | _, Γ', _, _, _, .sort _ l => .sort Γ' l
  | _, Γ', hcc, _, _, .bvar _ i A h => by
      obtain ⟨A', hA', hl⟩ := ctxConvT_lookupType hcl hcc i h
      cases hl with
      | same e =>
          rw [e] at hA'
          exact .bvar Γ' i A hA'
      | conv u' _tA _tA' hc =>
          exact .conv Γ' (.bvar i) A' A u' (.bvar Γ' i A' hA') (.symm Γ' A A' (.sort u') hc)
  | _, Γ', _, _, _, .const _ r ls m hres hlen hwf =>
      .const Γ' r ls m hres hlen hwf
  | _, Γ', hcc, _, _, .pi _ A u B v hA hB =>
      .pi Γ' A u B v (hasTyT_ctx hcl hcc hA)
        (hasTyT_ctx hcl (.same (.assumption A) hcc) hB)
  | _, Γ', hcc, _, _, .lam _ A u body B hA hbody =>
      .lam Γ' A u body B (hasTyT_ctx hcl hcc hA)
        (hasTyT_ctx hcl (.same (.assumption A) hcc) hbody)
  | _, Γ', hcc, _, _, .app _ f a A B hf ha =>
      .app Γ' f a A B (hasTyT_ctx hcl hcc hf) (hasTyT_ctx hcl hcc ha)
  | _, Γ', hcc, _, _, .letE _ A u value B body hA hv hb =>
      .letE Γ' A u value B body (hasTyT_ctx hcl hcc hA) (hasTyT_ctx hcl hcc hv)
        (hasTyT_ctx hcl (.same (.letBinding A value) hcc) hb)
  | _, Γ', hcc, _, _, .lit _ t T hexp => .lit Γ' t T (hasTyT_ctx hcl hcc hexp)
  | _, Γ', hcc, _, _, .conv _ e A B u h hc =>
      .conv Γ' e A B u (hasTyT_ctx hcl hcc h) (convT_ctx hcl hcc hc)

/-- conversions transport across pointwise-convertible contexts. `zetaLocal`
    composes the ζ-step with the lookup's conversion through `tyConv` and
    `trans`; `iota`'s `DerivedIota` witness reads no context. -/
def convT_ctx (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → {a b T : Expr Nat} → ConvT E n Γ a b T →
    ConvT E n Γ' a b T
  | _, Γ', hcc, _, _, _, .refl _ a A h => .refl Γ' a A (hasTyT_ctx hcl hcc h)
  | _, Γ', hcc, _, _, _, .symm _ a b A h => .symm Γ' a b A (convT_ctx hcl hcc h)
  | _, Γ', hcc, _, _, _, .trans _ a b c A h1 h2 =>
      .trans Γ' a b c A (convT_ctx hcl hcc h1) (convT_ctx hcl hcc h2)
  | _, Γ', hcc, _, _, _, .beta _ A body arg B u hA hbody harg =>
      .beta Γ' A body arg B u (hasTyT_ctx hcl hcc hA)
        (hasTyT_ctx hcl (.same (.assumption A) hcc) hbody) (hasTyT_ctx hcl hcc harg)
  | _, Γ', hcc, _, _, _, .zeta _ A value body B u hA hv hb =>
      .zeta Γ' A value body B u (hasTyT_ctx hcl hcc hA) (hasTyT_ctx hcl hcc hv)
        (hasTyT_ctx hcl (.same (.letBinding A value) hcc) hb)
  | _, Γ', hcc, _, _, _, .zetaLocal _ i A v hval hty hv => by
      obtain ⟨v', A₀, A', hty₀, hval', hty', hl⟩ := ctxConvT_lookupValue hcl hcc i hval
      have eA : A₀ = A := Option.some.inj (hty₀.symm.trans hty)
      rw [eA] at hl
      cases hl with
      | same eA' ev =>
          rw [eA'] at hty'
          rw [ev] at hval'
          exact .zetaLocal Γ' i A v hval' hty' (hasTyT_ctx hcl hcc hv)
      | conv u _tA _tA' hc tv' hcv =>
          exact .trans Γ' (.bvar i) v' v A
            (.tyConv Γ' (.bvar i) v' A' A u (.zetaLocal Γ' i A' v' hval' hty' tv')
              (.symm Γ' A A' (.sort u) hc))
            (.symm Γ' v v' A hcv)
  | _, Γ', hcc, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ' r ls m b hres hbody htr hlen hwf (hasTyT_ctx hcl hcc hb)
  | _, Γ', hcc, _, _, _, .iota _ lhs rhs T h hlhs hrhs =>
      .iota Γ' lhs rhs T h (hasTyT_ctx hcl hcc hlhs) (hasTyT_ctx hcl hcc hrhs)
  | _, Γ', hcc, _, _, _, .lit _ t exp T h hexp =>
      .lit Γ' t exp T h (hasTyT_ctx hcl hcc hexp)
  | _, Γ', hcc, _, _, _, .app _ f g a b A B h1 h2 =>
      .app Γ' f g a b A B (convT_ctx hcl hcc h1) (convT_ctx hcl hcc h2)
  | _, Γ', hcc, _, _, _, .lam _ A A' b b' B u hA hb =>
      .lam Γ' A A' b b' B u (convT_ctx hcl hcc hA)
        (convT_ctx hcl (.same (.assumption A) hcc) hb)
  | _, Γ', hcc, _, _, _, .pi _ A A' B B' u v hA hB =>
      .pi Γ' A A' B B' u v (convT_ctx hcl hcc hA)
        (convT_ctx hcl (.same (.assumption A) hcc) hB)
  | _, Γ', hcc, _, _, _, .letE _ A A' v v' b b' B u hA hv hb =>
      .letE Γ' A A' v v' b b' B u (convT_ctx hcl hcc hA) (convT_ctx hcl hcc hv)
        (convT_ctx hcl (.same (.letBinding A v) hcc) hb)
  | _, Γ', _, _, _, _, .sorts _ l₁ l₂ h => .sorts Γ' l₁ l₂ h
  | _, Γ', _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h =>
      .consts Γ' r ls ls' m hres hlen hwf hwf' h
  | _, Γ', hcc, _, _, _, .eta _ f A B h => .eta Γ' f A B (hasTyT_ctx hcl hcc h)
  | _, Γ', hcc, _, _, _, .irr _ P p q hP hp hq =>
      .irr Γ' P p q (hasTyT_ctx hcl hcc hP) (hasTyT_ctx hcl hcc hp) (hasTyT_ctx hcl hcc hq)
  | _, Γ', hcc, _, _, _, .tyConv _ a b A A' u h hA =>
      .tyConv Γ' a b A A' u (convT_ctx hcl hcc h) (convT_ctx hcl hcc hA)

end

end Conv

#print axioms ctxConvT_lookupType
#print axioms ctxConvT_lookupValue
#print axioms hasTyT_ctx
#print axioms convT_ctx

end Rcic.Declarative
