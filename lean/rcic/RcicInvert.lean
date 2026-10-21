/-
RCIC inversion templates — the ruling witness for the batch's named wall
on the inversion family (DT-003/007/012/015/021/023):

  "mutual-inductive constructors cannot be pattern-matched inside
   ∃/Conv conclusions; implicit (E, n) inference fails."

THE WALL DISSOLVES into two disciplines, both already ruled once:

1. ∃ IS THE NONEMPTY BARRIER AGAIN. An inversion that RETURNS data
   (the premise derivations, the intermediate type, the conversion) is a
   Type-valued def yielding `Σ'`/`×'` — never `∃`. `∃` lives in Prop;
   building data out of it needs Classical.choice, which the axiom
   whitelist does not have. Same ruling as #3687: constructions chain in
   Type; Prop wrappers (`∃`, `Nonempty`) are TERMINAL quotes only. The
   sealed DT statements may quote 02 with `∃` — as one-line wrappers
   over these Type-valued inversions, exactly like DT-004/DT-005.

2. CONSTRAINED INDICES WANT FORDING. Matching a derivation whose
   expression index is a constructor pattern (`HasTy E n Γ (.lam A b) T`)
   fights the equation compiler. The idiom: take the derivation at an
   UNCONSTRAINED index plus a propositional equation (`e = .lam A b`),
   match on the derivation, and let each arm consume the equation —
   `injection`/`subst` in the matching arms, `nomatch heq` dismisses
   every constructor whose subject cannot have that shape. No custom
   eliminators, no Prop-valued judgments, no mirror judgments.

The conv rule is why inversion results carry a `Conv` component: the
result type is determined only up to conversion, and the `.conv` arm
ACCUMULATES its conversion by `.trans` onto the recursive call. That is
the whole trick.

`hasTyLamInv` is the HasTy-family template (regularity / uniqueness /
the typed inversions ride this shape); `stepConstInv` is the Step-family
template (DT-015's "a step from a rigid const is an iota step" rides
this shape — under the landed placeholder DerivedIota it is delta-or-
iota, and the rigidity hypothesis kills the delta arm by `transparent`).

00 §20.6 lands `instantiateLevels` in `Step.delta`'s conclusion index;
`stepConstInv`'s delta summand is restated to bind the stored body
separately (sealed-statement change, old/new recorded at the
declaration). `hasTyLamInv` is unaffected — its `.const` arm is an
arity-only `nomatch`.

INFRASTRUCTURE (M-010): the DT statements themselves remain the
batch's — quoted from 02, as wrappers over these templates.
-/
import rcic.RcicDeclarative

namespace Rcic.Declarative

/-- HasTy inversion at a lambda subject (fording form). The result is
DATA: the domain sort, the codomain, both premise derivations, and the
conversion connecting the syntactic pi to the ascribed type. -/
def hasTyLamInv {E : ResolvedEnv} {n : Nat} {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .lam A body →
    Σ' (u : Level) (B : Expr Nat),
      HasTy E n Γ A (.sort u) ×'
      HasTy E n (LocalDecl.assumption A :: Γ) body B ×'
      Conv E n Γ (.pi A B) T
  | _, _, _, .lam Γ A' u body' B hA hb, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨u, B, hA, hb, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨u, B, hA, hb, hcv⟩ := hasTyLamInv h heq
      ⟨u, B, hA, hb, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Step inversion at a const source (fording form): a step out of
`.const r ls` is a delta unfolding (with its member evidence, killed by
a rigidity hypothesis via `transparent`) or a derived-iota step.

00 §20.6 SEALED-STATEMENT CHANGE (M-003). `Step.delta`'s conclusion
index is now `instantiateLevels ls b`, so the STORED body and the
STEPPED-TO expression are no longer the same expression and the
inversion has to bind them separately:

    old: Σ' (m : CheckedMember),
           (E.members r = some m) ×' (m.body = some b) ×'
           (transparent m.mclass = true)
    new: Σ' (m : CheckedMember) (b0 : Expr Nat),
           (E.members r = some m) ×' (m.body = some b0) ×'
           (transparent m.mclass = true) ×' (b = instantiateLevels ls b0)

NOTHING IS WEAKENED. The old conclusion asserted `m.body = some b` for
the very `b` the step lands on; the new one asserts it for `b0` and then
says how `b` is built from it, which is strictly more information (the
old form is the image of the new one under the fourth component). Under
`EnvWf` every member that HAS a body has `arity = 0`
(`envWf_body_arity_zero`), so `HasTy.const`'s `hlen` forces `ls = []`,
`instantiateLevels_nil` collapses the fourth component to `b = b0`, and
the old statement is recovered verbatim. DT-015's rigidity argument
reads only `transparent`, which is untouched. -/
def stepConstInv {E : ResolvedEnv} {n : Nat} {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {s b : Expr Nat} →
    Step E n Γ s b → s = .const r ls →
    (Σ' (m : CheckedMember) (b0 : Expr Nat),
      (E.members r = some m) ×' (m.body = some b0) ×'
      (transparent m.mclass = true) ×' (b = instantiateLevels ls b0)) ⊕'
    DerivedIota E (.const r ls) b
  | _, _, _, .delta Γ r' ls' m b0 hres hbody htr, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact .inl ⟨m, b0, hres, hbody, htr, rfl⟩
  | _, _, _, .iota Γ lhs rhs h, heq => by
      subst heq
      exact .inr h
  | _, _, _, .beta _ _ _ _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _, heq => nomatch heq
  | _, _, _, .zetaLocal _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

end Rcic.Declarative
