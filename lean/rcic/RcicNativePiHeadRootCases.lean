import rcic.RcicNativePiHeadObs
import rcic.RcicTypedValidity
import rcic.RcicTypedSubst
import rcic.RcicTypedSubstLet
import rcic.RcicDT0709EnvWf

set_option autoImplicit false

/-!
# Native root-rule construction for finite Pi observations

This module constructs the root-step data for arbitrary native beta, zeta,
delta, ordinary iota, and literal rule instances at an explicitly known
sort. It also constructs a literal-Pi observation from the two original
native children of `ConvT.pi`.

`SortHeadStep` retains both an actual `HeadStepT` and an independently built
native `ConvT`. The native certificate is constructed from the original
native rule; it is never inferred from a raw head trace. Its left and right
expansion functions consume an existing observation of the reduct.

For beta and zeta, the head step asks for more typing data than the native
conversion constructor does. These fields are constructed here:

* `regularT_of_envWfT`, with its two named supplies discharged by
  `substLetT_of_envWfT` and `constsRightDataT_of_envWfT`, supplies the sorting
  of the original body type in its original extended context.
* Native assumption/let substitution supplies both the reduct typing and
  the sorting of its type. The same level returned by regularity serves
  these fields; no sorting equality or retyping supplier is needed.
* The index equations for beta, zeta, and delta are literal syntactic
  equalities saying that the original conversion's index is a written
  sort. They do not convert one sorting of a term to another sorting.

All new functions are nonrecursive. The calls to established regularity
and substitution are native data constructions; no new semantic procedure
is recursively called on any generated typing or conversion. The iota
and literal cases inspect their original rule witnesses once.

Scope: these are root-rule data and observation-expansion constructions.
They do not supply the reduct observations, semantic stages, a fundamental
theorem, application-spine closure, local-zeta observation, eta observation,
or proof-irrelevance observation. They do not supply `PiInj` or a family
argument comparison. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativePiHeadObs

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- The actual root step and native conversion are retained separately
at the original rule's explicitly identified sort. -/
structure SortHeadStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (source target : Expr Nat) : Type where
  level : Level
  step : HeadStepT E n Γ source target (.sort level)
  cert : ConvT E n Γ source target (.sort level)

namespace SortHeadStep

/-- The native type-chain certificate is built from `cert`, not `step`. -/
def typeCert {s t : Expr Nat} (h : SortHeadStep E n Γ s t) :
    TyConvT E n Γ s t :=
  .of Γ s t h.level h.cert

/-- Any constructed root case expands an existing observation on the left. -/
def expand_left {s s' t : Expr Nat} (h : SortHeadStep E n Γ s s')
    (obs : PiHeadObs E n Γ s' t) : PiHeadObs E n Γ s t :=
  PiHeadObs.expand_left (.cons h.step (.refl _)) h.typeCert obs

/-- The same independently certified root case expands on the right. -/
def expand_right {s t t' : Expr Nat} (h : SortHeadStep E n Γ t t')
    (obs : PiHeadObs E n Γ s t') : PiHeadObs E n Γ s t :=
  PiHeadObs.expand_right (.cons h.step (.refl _)) h.typeCert obs

/-- Generic native beta, including a body type that becomes a sort only
after substituting the actual argument. All extra head-step typings are
constructed from the original native premises. -/
def beta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A body arg B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A)
    (hindex : instantiate0 arg B = .sort w) :
    SortHeadStep E n Γ (.app (.lam A body) arg) (instantiate0 arg body) := by
  let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
  obtain ⟨v, hB⟩ := regularT_of_envWfT hW
    (substLetT_of_envWfT hW) (constsRightDataT_of_envWfT hW) hΓA hbody
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let hTy : HasTyT E n Γ (instantiate0 arg B) (.sort v) :=
    hasTyT_subst0S hcl hinst hB harg
  let hred : HasTyT E n Γ (instantiate0 arg body) (instantiate0 arg B) :=
    hasTyT_subst0S hcl hinst hbody harg
  let step : HeadStepT E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B) :=
    .beta Γ A body arg B u v v hA hB hTy hbody harg hred
  let cert : ConvT E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B) :=
    .beta Γ A body arg B u hA hbody harg
  exact ⟨w, hindex ▸ step, hindex ▸ cert⟩

/-- Generic native zeta, with the body and its sorting kept in the
original let context until native let substitution removes that binder. -/
def zeta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A value body B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B)
    (hindex : instantiate0 value B = .sort w) :
    SortHeadStep E n Γ (.letE A value body) (instantiate0 value body) := by
  let hΓv : CtxWfT E n (.letBinding A value :: Γ) :=
    .letBinding Γ A u value hΓ hA hv
  obtain ⟨v, hB⟩ := regularT_of_envWfT hW
    (substLetT_of_envWfT hW) (constsRightDataT_of_envWfT hW) hΓv hb
  let hTy : HasTyT E n Γ (instantiate0 value B) (.sort v) :=
    hasTyT_substLet0_of_envWfT hW hB hv
  let hred : HasTyT E n Γ (instantiate0 value body) (instantiate0 value B) :=
    hasTyT_substLet0_of_envWfT hW hb hv
  let step : HeadStepT E n Γ (.letE A value body)
      (instantiate0 value body) (instantiate0 value B) :=
    .zeta Γ A value body B u v hA hv hB hTy hb hred
  let cert : ConvT E n Γ (.letE A value body)
      (instantiate0 value body) (instantiate0 value B) :=
    .zeta Γ A value body B u hA hv hb
  exact ⟨w, hindex ▸ step, hindex ▸ cert⟩

/-- Generic native delta. The original lookup, body, transparency, arity,
and boundedness premises are retained. `HasTyT.const` constructs the
head-step's left typing directly; no environment or row supplier is added. -/
def delta {r : Nat} {ls : List Level} {m : CheckedMember} {body : Expr Nat}
    {w : Level} (hres : E.members r = some m) (hbody : m.body = some body)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls body) (instantiateLevels ls m.mtype))
    (hindex : instantiateLevels ls m.mtype = .sort w) :
    SortHeadStep E n Γ (.const r ls) (instantiateLevels ls body) := by
  let hl : HasTyT E n Γ (.const r ls) (instantiateLevels ls m.mtype) :=
    .const Γ r ls m hres hlen hwf
  let step : HeadStepT E n Γ (.const r ls)
      (instantiateLevels ls body) (instantiateLevels ls m.mtype) :=
    .delta Γ r ls m body _ hres hbody htr hlen hwf hl hb
  let cert : ConvT E n Γ (.const r ls)
      (instantiateLevels ls body) (instantiateLevels ls m.mtype) :=
    .delta Γ r ls m body hres hbody htr hlen hwf hb
  exact ⟨w, hindex ▸ step, hindex ▸ cert⟩

/-- Ordinary native iota inspects the original `DerivedIota` witness,
whose own recursor and constructor data determine both endpoints. This
case makes no claim about proof-irrelevant neutral-major elimination. -/
def iota {lhs rhs : Expr Nat} {u : Level}
    (h : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs (.sort u))
    (hrhs : HasTyT E n Γ rhs (.sort u)) : SortHeadStep E n Γ lhs rhs := by
  cases h with
  | of witness =>
      exact ⟨u, .iota Γ witness (.sort u) hlhs hrhs,
        .iota Γ _ _ (.sort u) (.of witness) hlhs hrhs⟩

/-- A native literal expansion supplies its actual expanded expression;
the single witness constructor identifies it with `natExpand`. -/
def lit {t : Nat} {exp : Expr Nat} {u : Level}
    (h : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp (.sort u)) :
    SortHeadStep E n Γ (.lit t) exp := by
  cases h with
  | of =>
      exact ⟨u, .lit Γ t (.sort u) hexp,
        .lit Γ t (natExpand t) (.sort u) (.of t) hexp⟩

end SortHeadStep

/-- The native Pi-congruence case supplies the actual two component
chains directly from its original conversion children. No Pi inversion
is applied to the parent conversion. -/
def pi_observation_of_native_congruence {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    PiHeadObs E n Γ (.pi A B) (.pi A' B') :=
  PiHeadObs.of_components (.of Γ A A' u hA)
    (.of (.assumption A :: Γ) B B' v hB)

#print axioms SortHeadStep.typeCert
#print axioms SortHeadStep.expand_left
#print axioms SortHeadStep.expand_right
#print axioms SortHeadStep.beta
#print axioms SortHeadStep.zeta
#print axioms SortHeadStep.delta
#print axioms SortHeadStep.iota
#print axioms SortHeadStep.lit
#print axioms pi_observation_of_native_congruence

end Rcic.Declarative.NativeValleys.NativePiHeadObs
