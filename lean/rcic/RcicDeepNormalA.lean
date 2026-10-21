/-
DT-025 M4 statement: deep normality for the endpoint transfer.

`DeepNormalA E I Γ e` asserts that `hStepFnA` has no step at the head of `e`
AND at every subterm position, with the local context extended per binder —
exactly the positions the erased `ParRed`'s congruence arms reach
(`ParRed.app` in both children, `ParRed.lam`/`.pi`/`letE` in
`assumption`-extended contexts; `ParRed.sortEq`/`.consts` level drift is
`eqExprN`-absorbed and therefore unconstrained).

Per-case content, at the node's head:

- `.bvar i`: `lookupValueA Γ i = none` — no local-ζ (erased `ParRed.bvarZeta`
  needs a `.letBinding` cell at `i`; `get?_eraseCtx` makes that equivalent).
- `.const r ls`: member absent or non-transparent or bodiless — no δ
  (`ParRed.delta`'s `members`/`body`/`transparent` triple is erasure-exact).
- `.lit t`: `hStepFnA` fires unconditionally (`natExpandA`), so the clause is
  `False` — matching the erased side's unconditional `ParRed.lit`.
- `.letE A v b`: `hStepFnA` fires ζ unconditionally — `False`, matching the
  erased side's unconditional `ParRed.zeta`.
- `.app f a`: `hStepFnA`-inertia excludes β (app-of-lam), the struct arm,
  `I.fn` ι (the function's only ι call site), and the major arm (unit/struct
  K and argument stepping). The K-rules have no erased counterpart, so this
  head clause is conservative there — `NoUnitStructA`-free environments can
  satisfy `hStepFnA = none` at a K-reducible spine only vacuously.
- `.lam`/`.pi`: no head step exists; the domain is deep-normal and the body
  is deep-normal in the `assumption`-extended context.
- `.sort`: inert (erased `ParRed.sortEq` is `eqExprN`'s `.sort` clause).
-/

import rcic.RcicAnnStep
import rcic.RcicAnnErase

namespace Rcic.Declarative.Ann

/-- Deep-normal: `hStepFnA` has no step at the head AND at every subterm
position, with the context extended per binder. The erased endpoint-transfer
theorem (`deepNormalA_parRed_eqExprN`, `RcicEraseNormalEnd`) shows this is
sufficient for `∀ N', ParRed (eraseEnv E) n (eraseCtx Γ) (erase e) N' →
eqExprN N' (erase e)`. -/
def DeepNormalA (E : ResolvedEnvA) (I : IotaIfaceA) : LCtxA → ExprA → Prop
  | Γ, .bvar i => hStepFnA E I.fn Γ (.bvar i) = none
  | _, .sort _ => True
  | Γ, .const r ls => hStepFnA E I.fn Γ (.const r ls) = none
  | Γ, .app f a =>
      hStepFnA E I.fn Γ (.app f a) = none ∧ DeepNormalA E I Γ f ∧ DeepNormalA E I Γ a
  | Γ, .lam A _u b => DeepNormalA E I Γ A ∧ DeepNormalA E I (.assumption A :: Γ) b
  | Γ, .pi A _u B _v => DeepNormalA E I Γ A ∧ DeepNormalA E I (.assumption A :: Γ) B
  | Γ, .letE A v b => hStepFnA E I.fn Γ (.letE A v b) = none
  | Γ, .lit t => hStepFnA E I.fn Γ (.lit t) = none

end Rcic.Declarative.Ann
