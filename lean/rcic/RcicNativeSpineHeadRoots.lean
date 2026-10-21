import rcic.RcicNativeSpineHead

set_option autoImplicit false

/-!
# Native root builders at arbitrary result indices

Sort-indexed callers reuse SortHeadStep. These builders also serve roots
whose results are functions, so they can be used below an application spine.
No generic head-step back-lift is used. closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.NativeSpineHead

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- The body type keeps the original let context until native substitution. -/
def Step.zeta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
    Step E n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B) := by
  let ctx : CtxWfT E n (.letBinding A value :: Γ) :=
    .letBinding Γ A u value hΓ hA hv
  let sb := tySort hW ctx hb
  let ht : HasTyT E n Γ (instantiate0 value B) (.sort sb.1) :=
    hasTyT_substLet0_of_envWfT hW sb.2 hv
  let hr := hasTyT_substLet0_of_envWfT hW hb hv
  exact .root (.zeta Γ A value body B u sb.1 hA hv sb.2 ht hb hr)
    (.zeta Γ A value body B u hA hv hb)

def Step.delta {r : Nat} {ls : List Level} {m : CheckedMember} {body : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some body)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls body) (instantiateLevels ls m.mtype)) :
    Step E n Γ (.const r ls) (instantiateLevels ls body) (instantiateLevels ls m.mtype) :=
  .root (.delta Γ r ls m body _ hres hbody htr hlen hwf
    (.const Γ r ls m hres hlen hwf) hb)
    (.delta Γ r ls m body hres hbody htr hlen hwf hb)

/-- Native iota is the legacy witness arm of the existing calculus. -/
def Step.iota {lhs rhs T : Expr Nat} (h : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T) :
    Step E n Γ lhs rhs T := by
  cases h with
  | of w => exact .root (.iota Γ w T hlhs hrhs) (.iota Γ _ _ T (.of w) hlhs hrhs)

def Step.lit {t : Nat} {exp T : Expr Nat}
    (h : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp T) :
    Step E n Γ (.lit t) exp T := by
  cases h with
  | of => exact .root (.lit Γ t T hexp) (.lit Γ t (natExpand t) T (.of t) hexp)

end Rcic.Declarative.NativeValleys.NativeSpineHead
