import rcic.RcicDeclarative

/-!
# M3-b GLM-2 — typed inversions, on the landed judgment

The typed counterpart of `RcicInvert`'s HasTy-family template, for the judgment
GLM-2 landed in `RcicDeclarative` (GLM-2 section, single owner). Same two
disciplines as the ruled witness (issue: inversion-family wall):

1. DATA IN `Σ'`/`×'`, never `∃` — `∃` is the Nonempty barrier; constructions
   chain in Type, Prop wrappers are terminal quotes.
2. FORDING — the derivation is taken at an UNCONSTRAINED index plus a
   propositional equation (`e = .app f a`); each arm consumes the equation,
   `injection`/`subst` in matching arms, `nomatch heq` dismisses the rest.

One difference from the raw template, forced by the typed judgment's own shape:
the raw `hasTyLamInv` accumulates the `.conv` arm's residue as a `Conv` (the raw
judgment's conversion is UNINDEXED). `ConvT` is indexed by the type it converts
AT, and the two links of an accumulation live at different indices — so the
accumulation is a `TyConvT` chain (the judgment's own unindexed type-conversion
chain; `TyConvT.of` lifts each `ConvT`-at-a-sort link, `TyConvT.trans` splices).
The conclusion's third component is therefore a `TyConvT` from the constructor's
own conclusion type to the derivation's — strictly more information than the
raw template's `Conv`, which it specializes at a fixed type.

DT009T's `app` arm (and the consumer units' endpoint-typing reads) consume
`hasTyTInv_app`; nothing here pre-claims DT009T itself (its `lam`/`pi`/`letE`
RIGHT-endpoint transport remains open, recorded in the migration map).
-/

namespace Rcic.Declarative

/-- `lam`-inversion, typed: every typing of `.lam A body` reads off the domain's
    sort-typing, the body's typing, and the type as a `TyConvT` from `.pi A B`. -/
def hasTyTInv_lam {E : ResolvedEnv} {n : Nat} {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T → e = .lam A body →
    Σ' (u : Level) (B : Expr Nat),
      HasTyT E n Γ A (.sort u) ×'
      HasTyT E n (LocalDecl.assumption A :: Γ) body B ×'
      TyConvT E n Γ (.pi A B) T
  | _, _, _, .lam _ A' u body' B hA hb, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨u, B, hA, hb, .refl _ _⟩
  | _, _, _, .conv _ e A0 B0 u h hc, heq =>
      let ⟨u', B, hA, hb, hcv⟩ := hasTyTInv_lam h heq
      ⟨u', B, hA, hb, .trans _ _ _ _ hcv (.of _ _ _ u hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `app`-inversion, typed: every typing of `.app f a` reads off the function's
    π-typing, the argument's typing, and the type as a `TyConvT` from
    `instantiate0 a B`. -/
def hasTyTInv_app {E : ResolvedEnv} {n : Nat} {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat}→
    HasTyT E n Γ e T → e = .app f a →
    Σ' (A B : Expr Nat),
      HasTyT E n Γ f (.pi A B) ×'
      HasTyT E n Γ a A ×'
      TyConvT E n Γ (instantiate0 a B) T
  | _, _, _, .app _ _ _ A B hf ha, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨A, B, hf, ha, .refl _ _⟩
  | _, _, _, .conv _ e A0 B0 u h hc, heq =>
      let ⟨A, B, hf, ha, hcv⟩ := hasTyTInv_app h heq
      ⟨A, B, hf, ha, .trans _ _ _ _ hcv (.of _ _ _ u hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `letE`-inversion, typed: every typing of `.letE A value body` reads off the
    domain's sort-typing, the value's typing, the body's typing, and the type as
    a `TyConvT` from `instantiate0 value B`. -/
def hasTyTInv_letE {E : ResolvedEnv} {n : Nat} {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat}→
    HasTyT E n Γ e T → e = .letE A value body →
    Σ' (u : Level) (B : Expr Nat),
      HasTyT E n Γ A (.sort u) ×'
      HasTyT E n Γ value A ×'
      HasTyT E n (LocalDecl.letBinding A value :: Γ) body B ×'
      TyConvT E n Γ (instantiate0 value B) T
  | _, _, _, .letE _ A' u value' B body' hA hv hb, heq => by
      injection heq with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨u, B, hA, hv, hb, .refl _ _⟩
  | _, _, _, .conv _ e A0 B0 u h hc, heq =>
      let ⟨u', B, hA, hv, hb, hcv⟩ := hasTyTInv_letE h heq
      ⟨u', B, hA, hv, hb, .trans _ _ _ _ hcv (.of _ _ _ u hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `pi`-inversion, typed: every typing of `.pi A B` reads off both domains'
    sort-typings and the type as a `TyConvT` from `.sort (.imax u v)`. -/
def hasTyTInv_pi {E : ResolvedEnv} {n : Nat} {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat}→
    HasTyT E n Γ e T → e = .pi A B →
    Σ' (u v : Level),
      HasTyT E n Γ A (.sort u) ×'
      HasTyT E n (LocalDecl.assumption A :: Γ) B (.sort v) ×'
      TyConvT E n Γ (.sort (.imax u v)) T
  | _, _, _, .pi _ A' u B' v hA hB, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨u, v, hA, hB, .refl _ _⟩
  | _, _, _, .conv _ e A0 B0 u h hc, heq =>
      let ⟨u', v, hA, hB, hcv⟩ := hasTyTInv_pi h heq
      ⟨u', v, hA, hB, .trans _ _ _ _ hcv (.of _ _ _ u hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-! ## consumption pins (real derivations, components read back through the
interface — two constructor arms, one `.conv`-accumulation arm) -/

section Pins

variable (E : ResolvedEnv) (n : Nat)

/-- a real `lam` typing: `λ (x : Sort 0), Sort 0 : Π (x : Sort 0), Sort 1` —
    the identity-on-sorts domain instantiation, at `u = 1`, `B = Sort 1`. -/
def pinLamT :
    HasTyT E n [] (.lam (.sort .zero) (.sort .zero))
      (.pi (.sort .zero) (.sort (.succ .zero))) :=
  .lam [] (.sort .zero) (.succ .zero) (.sort .zero) (.sort (.succ .zero))
    (pinSortT E n)
    (.sort [LocalDecl.assumption (.sort .zero)] .zero)

/-- PIN (constructor arm, `lam`): the inversion reads back `u = 1`, `B = Sort 1`,
    and a `refl` chain. -/
theorem pin_invLam_components :
    (∃ (u : Level) (B : Expr Nat), u = .succ .zero ∧ B = .sort (.succ .zero)) ∧
    Nonempty (TyConvT E n []
      (.pi (.sort .zero) (.sort (.succ .zero)))
      (.pi (.sort .zero) (.sort (.succ .zero)))) :=
  let r := hasTyTInv_lam (pinLamT E n) rfl
  ⟨⟨r.1, r.2.1, rfl, rfl⟩, ⟨r.2.2.2.2⟩⟩

/-- PIN (constructor arm, `pi`): inverting `pinPiT` reads back `u = v = 1` and a
    `refl` chain at `Sort (imax 1 1)`. -/
theorem pin_invPi_components :
    (∃ (u v : Level), u = .succ .zero ∧ v = .succ .zero) ∧
    Nonempty (TyConvT E n []
      (.sort (.imax (.succ .zero) (.succ .zero)))
      (.sort (.imax (.succ .zero) (.succ .zero)))) :=
  let r := hasTyTInv_pi (pinPiT E n) rfl
  ⟨⟨r.1, r.2.1, rfl, rfl⟩, ⟨r.2.2.2.2⟩⟩

/-- the sort-typing of `Π (x : Sort 0), Sort 1` itself: at `Sort (imax 1 2)`. -/
def pinPi01T :
    HasTyT E n [] (.pi (.sort .zero) (.sort (.succ .zero)))
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort (.succ .zero)) (.succ (.succ .zero))
    (pinSortT E n) (.sort [LocalDecl.assumption (.sort .zero)] (.succ .zero))

/-- the same `lam` typing, but LANDED through the judgment's `.conv` rule with a
    `refl` conversion at the pi's own sort — so the derivation is `.conv`-headed
    and the inversion must take the accumulating arm. -/
def pinLamConvT :
    HasTyT E n [] (.lam (.sort .zero) (.sort .zero))
      (.pi (.sort .zero) (.sort (.succ .zero))) :=
  .conv [] _ _ _ (.imax (.succ .zero) (.succ (.succ .zero))) (pinLamT E n)
    (ConvT.refl [] _ (.sort (.imax (.succ .zero) (.succ (.succ .zero))))
      (pinPi01T E n))

/-- PIN (accumulation arm): inverting the `.conv`-headed derivation returns the
    SAME components as the constructor arm — the accumulation is identity on a
    `refl` leg (`trans refl (of refl)` still lands `u = 1`, `B = Sort 1`). -/
theorem pin_invLamConv_components :
    (∃ (u : Level) (B : Expr Nat), u = .succ .zero ∧ B = .sort (.succ .zero)) ∧
    Nonempty (TyConvT E n []
      (.pi (.sort .zero) (.sort (.succ .zero)))
      (.pi (.sort .zero) (.sort (.succ .zero)))) :=
  let r := hasTyTInv_lam (pinLamConvT E n) rfl
  ⟨⟨r.1, r.2.1, rfl, rfl⟩, ⟨r.2.2.2.2⟩⟩

end Pins

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyTInv_lam
#print axioms Rcic.Declarative.hasTyTInv_app
#print axioms Rcic.Declarative.hasTyTInv_letE
#print axioms Rcic.Declarative.hasTyTInv_pi
