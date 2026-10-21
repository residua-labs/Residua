import rcic.RcicDTMeta
import rcic.RcicTypedSubst

/-!
# M3-b GLM-2 — first consumer migration: DTMeta's conversion interface on the typed judgment

`RcicDTMeta`'s conversion infrastructure (`convExt`, DT008, DT009) is written on the
RAW 3-arg `Conv`. This module lands the TYPED counterparts GLM-2's later units
consume, WITHOUT deleting or editing the raw ones (they stay Legacy, quarantined by
the GLM-2 seal audit):

* `hasTyTExt` / `convTExt` / `tyConvTExt`: environment-extension transport for
  `HasTyT`, `ConvT` and `TyConvT` — the exact hypothesis `convExt` reads (member
  extensionality only; NO row premise, NO environment semantics), constructor by
  constructor.
* `DT008T_closure_fixedType`: DT008's three closure facts restated on `ConvT` at a
  fixed type — reflexivity TYPING-CONDITIONED (the typed judgment's `refl` needs the
  endpoint's typing; the raw DT008's unconditioned refl has no typed analogue, and
  inventing one would be assuming every term typable), symmetry and transitivity
  unconditional — all from the typed judgment's own constructors, existence-valued.

DT009's typed restatement (2026-10-06): `DT009T_endpoints` — EVERY conversion
determines BOTH endpoints' typings — debt-carrying in the raw house style (raw
DT-021 carries `SortConvChar` as a named premise): five named debts, one per
measured wall (`ConvTEtaLeftT` eta-left, `ConvTAppRightT` app-right,
`ConvTCtxDomT`/`ConvTCtxLetT` context transports, `ConvTConstsRightT`
consts-right), each individually dischargeable and each a premise, never a
silent assumption. Everything else folds from the rules' own fields; `beta`'s
and `zeta`'s right ends are head substitution (`hasTyT_subst0`, this branch);
`sorts`' right end retypes along an `eqN_succ`-built sorts conversion. The
single-direction statements do NOT fold: `symm` needs the sub-derivation's
other endpoint, so the both-endpoints form is the honest minimal one.

Existence discipline (Global Constraint 4): every existence conclusion stays
`Nonempty` inside Prop; no runtime data is extracted.
-/

namespace Rcic.Declarative

/-! ## extension transport (the typed `convExt`) -/

section Ext

variable {E E' : ResolvedEnv} {n : Nat}

mutual
/-- `HasTyT` transports along member extensionality — the same hypothesis the raw
    judgment's environment-morphism lemmas read; no rows involved. -/
def hasTyTExt (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a A : Expr Nat} → HasTyT E n Γ a A → HasTyT E' n Γ a A
  | _, _, _, .bvar _ _ _ h => .bvar _ _ _ h
  | _, _, _, .sort _ _ => .sort _ _
  | _, _, _, .const _ r ls m hres hlen hwf => .const _ r ls m (hext r m hres) hlen hwf
  | _, _, _, .app _ _ _ _ _ hf ha => .app _ _ _ _ _ (hasTyTExt hext hf) (hasTyTExt hext ha)
  | _, _, _, .lam _ _ _ _ _ hA hbody => .lam _ _ _ _ _ (hasTyTExt hext hA)
      (hasTyTExt hext hbody)
  | _, _, _, .pi _ _ _ _ _ hA hB => .pi _ _ _ _ _ (hasTyTExt hext hA)
      (hasTyTExt hext hB)
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => .letE _ _ _ _ _ _ (hasTyTExt hext hA)
      (hasTyTExt hext hv) (hasTyTExt hext hb)
  | _, _, _, .lit _ _ _ h => .lit _ _ _ (hasTyTExt hext h)
  | _, _, _, .conv _ _ _ _ _ hA hc => .conv _ _ _ _ _ (hasTyTExt hext hA)
      (convTExt hext hc)

/-- `ConvT` at a fixed type transports along the same extensionality — the typed
    counterpart of `RcicDTMeta.convExt`, constructor by constructor. -/
def convTExt (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → ConvT E' n Γ a b T
  | _, _, _, _, .refl _ _ _ hA => .refl _ _ _ (hasTyTExt hext hA)
  | _, _, _, _, .symm _ _ _ _ h => .symm _ _ _ _ (convTExt hext h)
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => .trans _ _ _ _ _ (convTExt hext h1)
      (convTExt hext h2)
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg => .beta _ _ _ _ _ _
      (hasTyTExt hext hA) (hasTyTExt hext hbody) (hasTyTExt hext harg)
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => .zeta _ _ _ _ _ _
      (hasTyTExt hext hA) (hasTyTExt hext hv) (hasTyTExt hext hb)
  | _, _, _, _, .zetaLocal _ _ _ _ hval hty hv => .zetaLocal _ _ _ _ hval hty
      (hasTyTExt hext hv)
  | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb => .delta _ r ls m b
      (hext r m hres) hbody htr hlen hwf (hasTyTExt hext hb)
  | _, _, _, _, .iota _ _ _ _ h hl hr => .iota _ _ _ _ (derivedIotaExt hext h)
      (hasTyTExt hext hl) (hasTyTExt hext hr)
  -- `derivedIotaExt` is RcicIota's own (same hypothesis), reused — not redefined
  | _, _, _, _, .lit _ _ _ _ h hexp => .lit _ _ _ _ h (hasTyTExt hext hexp)
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => .app _ _ _ _ _ _ _ (convTExt hext h1)
      (convTExt hext h2)
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => .lam _ _ _ _ _ _ _ (convTExt hext hA)
      (convTExt hext hb)
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => .pi _ _ _ _ _ _ _ (convTExt hext hA)
      (convTExt hext hB)
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => .letE _ _ _ _ _ _ _ _ _
      (convTExt hext hA) (convTExt hext hv) (convTExt hext hb)
  | _, _, _, _, .sorts _ _ _ h => .sorts _ _ _ h
  | _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h => .consts _ r ls ls' m
      (hext r m hres) hlen hwf hwf' h
  | _, _, _, _, .eta _ _ _ _ h => .eta _ _ _ _ (hasTyTExt hext h)
  | _, _, _, _, .irr _ _ _ _ hP hp hq => .irr _ _ _ _ (hasTyTExt hext hP)
      (hasTyTExt hext hp) (hasTyTExt hext hq)
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => .tyConv _ _ _ _ _ _ (convTExt hext h)
      (convTExt hext hA)

end

/-- `TyConvT` chains transport along the same extensionality, leg by leg. -/
def tyConvTExt (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a b : Expr Nat} → TyConvT E n Γ a b → TyConvT E' n Γ a b
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .of _ _ _ u h => .of _ _ _ u (convTExt hext h)
  | _, _, _, .trans _ _ _ _ h1 h2 => .trans _ _ _ _ (tyConvTExt hext h1)
      (tyConvTExt hext h2)

end Ext

/-! ## DT008 restated: closure at a fixed type, from the constructors -/

/-- DT008's closure facts on the TYPED judgment, at a fixed type `T`:
    reflexivity TYPING-CONDITIONED (the typed `refl` carries an endpoint typing —
    the raw DT008's unconditioned refl would amount to assuming every term typable
    and has NO typed analogue; the conditioning is the honest statement), symmetry
    and transitivity unconditional. Existence-valued; no annotation, no bridge, no
    row premise. -/
theorem DT008T_closure_fixedType {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (∀ (a T : Expr Nat), Nonempty (HasTyT E n Γ a T) → Nonempty (ConvT E n Γ a a T))
    ∧ (∀ T a b, ConvT E n Γ a b T → Nonempty (ConvT E n Γ b a T))
    ∧ (∀ T a b c, ConvT E n Γ a b T → ConvT E n Γ b c T →
        Nonempty (ConvT E n Γ a c T)) := by
  refine ⟨fun a T hT => hT.elim (fun hT' => ⟨ConvT.refl _ _ _ hT'⟩), ?_, ?_⟩
  · intro T a b h
    exact ⟨ConvT.symm _ _ _ _ h⟩
  · intro T a b c h1 h2
    exact ⟨ConvT.trans _ _ _ _ _ h1 h2⟩

/-! ## DT009, typed: BOTH endpoints of every conversion are typed — under seven
named debts, one per measured wall (the raw house style: DT-021 carries
`SortConvChar` as a premise; debts here are premises, never silent
assumptions).

DOMAIN FIX (2026-10-06, review round on 540d5656d4 — two source-level
counterexamples against the first debt definitions, mechanized in scratch
against that head and recorded below):

* `ConvTConstsRightT` originally omitted the `consts` rule's own premises
  (`ls.length = m.arity`, both `levelsBounded`) — refutable on ANY environment
  with a member via `ls = ls' = replicate (arity+1) 0` and const-inversion.
  Receipt: `ce_not_constsRight : ¬ ConvTConstsRightT ceEnv n` compiled against
  540d5656d4 (scratch `dt009t_domain/ce_head.lean`, axioms [propext]). The
  definition now carries all three conditions; the call site supplies them from
  the rule's own fields (`hlen hwf hwf' hh`).
* `ConvTEtaLeftT` originally demanded nothing of the context — `HasTyT.bvar`
  reads only `lookupType`, so an ill-formed context `[assumption (Π (const 0
  []) (Sort 0))]` at `emptyEnv` types `bvar 0` there, and `hasTyT_constsIn`
  refutes the promised lambda typing (its domain names a nonexistent constant).
  Receipt: `ce_not_etaLeft : ¬ ConvTEtaLeftT emptyEnv n` compiled against
  540d5656d4 (same scratch, zero axioms). Every debt — and the endpoint theorem
  itself — now carries `CtxWfT E n Γ`; the theorem derives the EXTENDED
  contexts' `CtxWfT` at each recursive call from rule fields and induction
  results, never assuming them.

A POSITIVE instance (`pin_etaLeft_identity`) shows the revised η promise is
constructible on a legal input — the revised call goes through the target
branch; excluding the old counterexamples is not the whole story.

SECOND RECEIPT (post-fix): re-running the consts refutation against the FIXED
definition fails to instantiate the debt — the call now demands `CtxWfT` and
the arity premise `1 = 0` before any conclusion (compile-failure receipt,
scratch `dt009t_domain/ce_new.lean`); the η bad-context instantiation is
excluded the same way (no `CtxWfT` of the ill-formed context exists — its
domain typing is refuted by `hasTyT_constsIn`).

The other five debts were checked against their rules' premises for the same
omission class (missing rule premises / missing context well-formedness); each
now carries `CtxWfT`. They remain unproven and individually dischargeable; no
claim is made that the domain fixes discharge them. -/

/-- level `succ` congruence: pointwise-evaluated levels stay equal under succ. -/
theorem eqN_succ {l1 l2 : Level} (h : eqN l1 l2) : eqN (.succ l1) (.succ l2) :=
  fun ρ => by simp only [eval] at *; rw [h ρ]

/-- DEBT (eta, left): the eta rule's left end is the lam-expansion; typing it
    needs the domain's sort-typing, which the rule does not carry. Domain: a
    WELL-FORMED context (the ill-formed-context counterexample is excluded by
    `CtxWfT`). -/
def ConvTEtaLeftT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f A B : Expr Nat},
    HasTyT E n Γ f (.pi A B) →
    Nonempty (HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))

/-- DEBT (app, right): the congruence rule's right end `g b` lives at the LEFT
    argument's instantiation `instantiate0 a B`; building that typing needs the
    codomain instantiation congruence, not yet paid. -/
def ConvTAppRightT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f g a b A B : Expr Nat},
    ConvT E n Γ f g (.pi A B) → ConvT E n Γ a b A →
    Nonempty (HasTyT E n Γ (.app g b) (instantiate0 a B))

/-- DEBT (lam, right): the right lambda `.lam A' b'` at the rule's index
    `.pi A B` — transport to the right domain AND retype to the left π-type;
    both legs are future work. -/
def ConvTLamRightT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' b b' B : Expr Nat} {u : Level},
    ConvT E n Γ A A' (.sort u) →
    ConvT E n (LocalDecl.assumption A :: Γ) b b' B →
    Nonempty (HasTyT E n Γ (.lam A' b') (.pi A B))

/-- DEBT (pi, right): the right π at the rule's index `Sort (imax u v)`. -/
def ConvTPiRightT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' B B' : Expr Nat} {u v : Level},
    ConvT E n Γ A A' (.sort u) →
    ConvT E n (LocalDecl.assumption A :: Γ) B B' (.sort v) →
    Nonempty (HasTyT E n Γ (.pi A' B') (.sort (.imax u v)))

/-- DEBT (letE, right): the right let at the rule's index `instantiate0 v B`. -/
def ConvTLetRightT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' v v' b b' B : Expr Nat} {u : Level},
    ConvT E n Γ A A' (.sort u) → ConvT E n Γ v v' A →
    ConvT E n (LocalDecl.letBinding A v :: Γ) b b' B →
    Nonempty (HasTyT E n Γ (.letE A' v' b') (instantiate0 v B))

/-- DEBT (zeta, right): the zeta rule's right end is head substitution in a
    LET-binding context; the typed let-substitution (analogue of the raw
    `hasTySubstLet`) is not yet paid. -/
def ConvTZetaRightT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A value body B : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ value A →
    HasTyT E n (LocalDecl.letBinding A value :: Γ) body B →
    Nonempty (HasTyT E n Γ (instantiate0 value body) (instantiate0 value B))

/-- DEBT (consts, right): the right const's own typing sits at
    `instantiateLevels ls' m.mtype`; the conversion's index is the LEFT levels'
    instantiation. DOMAIN: the `consts` rule's own premises — arity match and
    BOTH sides level-bounded — are carried (the first definition omitted them
    and was refutable on any membered environment; receipt above). -/
def ConvTConstsRightT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember} {ls ls' : List Level},
    E.members r = some m → ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true →
    eqNList ls ls' →
    Nonempty (HasTyT E n Γ (.const r ls') (instantiateLevels ls m.mtype))

/-- DT009 (typed, debt-carrying): in a WELL-FORMED context, under the seven
    named debts, every typed conversion determines BOTH its endpoints' typings
    at the conversion's own type. The `CtxWfT` premise propagates: every
    recursive call into an EXTENDED context derives that context's
    well-formedness from the rule's own typing fields or the induction pair —
    `assumption A :: Γ` via `CtxWfT.cons` on the domain's sort-typing,
    `letBinding A v :: Γ` via `CtxWfT.letBinding` on the domain and value
    typings. `sorts`' right end retypes along an `eqN_succ`-built sorts
    conversion (no debt); `beta`'s right end is head substitution
    (`hasTyT_subst0`, this branch). Existence-valued. -/
def DT009T_endpointsS {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hη : ConvTEtaLeftT E n) (happ : ConvTAppRightT E n)
    (hlam : ConvTLamRightT E n) (hpi : ConvTPiRightT E n)
    (hlet : ConvTLetRightT E n) (hzeta : ConvTZetaRightT E n)
    (hconst : ConvTConstsRightT E n) :
    {a b T : Expr Nat}→
    ConvT E n Γ a b T →
    Nonempty (HasTyT E n Γ a T) ∧ Nonempty (HasTyT E n Γ b T) :=
  fun h =>
  match h with
  | .refl _ _ _ hA => ⟨⟨hA⟩, ⟨hA⟩⟩
  | .symm _ _ _ _ h =>
      have ih := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst h
      ⟨ih.2, ih.1⟩
  | .trans _ _ _ _ _ h1 h2 =>
      have ih1 := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst h1
      have ih2 := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst h2
      ⟨ih1.1, ih2.2⟩
  | .beta _ A _ _ _ _ hA hbody harg =>
      ⟨⟨HasTyT.app _ _ _ _ _ (HasTyT.lam _ _ _ _ _ hA hbody) harg⟩,
        ⟨hasTyT_subst0S hcl hinst hbody harg⟩⟩
  | .zeta _ _ _ _ _ _ hA hv hb =>
      ⟨⟨HasTyT.letE _ _ _ _ _ _ hA hv hb⟩,
        hzeta hΓ hA hv hb⟩
  | .zetaLocal _ _ _ _ _ hty hv => ⟨⟨HasTyT.bvar _ _ _ hty⟩, ⟨hv⟩⟩
  | .delta _ r ls m _ hres _ _ hlen hwf hb =>
      ⟨⟨HasTyT.const _ r ls m hres hlen hwf⟩, ⟨hb⟩⟩
  | .iota _ _ _ _ _ hlhs hrhs => ⟨⟨hlhs⟩, ⟨hrhs⟩⟩
  | .lit _ tN exp _ h hexp => by
      cases h
      exact ⟨⟨HasTyT.lit _ _ _ hexp⟩, ⟨hexp⟩⟩
  | .app _ _ _ _ _ _ _ h1 h2 => by
      have ih1 := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst h1
      have ih2 := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst h2
      exact ih1.1.elim fun l1 => ih2.1.elim fun a2 =>
        ⟨⟨HasTyT.app _ _ _ _ _ l1 a2⟩, happ hΓ h1 h2⟩
  | .lam _ A _ _ _ _ u hA hb => by
      have ihA := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst hA
      obtain ⟨hAsort⟩ := ihA.1
      have ihb := DT009T_endpointsS hcl hinst
        (CtxWfT.assumption _ A u hΓ hAsort) hη happ hlam hpi hlet
        hzeta hconst hb
      exact ihA.1.elim fun al => ihb.1.elim fun bl =>
        ⟨⟨HasTyT.lam _ _ _ _ _ al bl⟩, hlam hΓ hA hb⟩
  | .pi _ A _ _ _ u _ hA hB => by
      have ihA := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst hA
      obtain ⟨hAsort⟩ := ihA.1
      have ihb := DT009T_endpointsS hcl hinst
        (CtxWfT.assumption _ A u hΓ hAsort) hη happ hlam hpi hlet
        hzeta hconst hB
      exact ihA.1.elim fun al => ihb.1.elim fun bl =>
        ⟨⟨HasTyT.pi _ _ _ _ _ al bl⟩, hpi hΓ hA hB⟩
  | .letE _ A _ v _ _ _ _ u hA hv hb => by
      have ihA := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst hA
      have ihv := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst hv
      obtain ⟨hAsort⟩ := ihA.1
      obtain ⟨hvA⟩ := ihv.1
      have ihb := DT009T_endpointsS hcl hinst
        (CtxWfT.letBinding _ A u v hΓ hAsort hvA) hη happ hlam
        hpi hlet hzeta hconst hb
      exact ihA.1.elim fun al => ihv.1.elim fun vl => ihb.1.elim fun bl =>
        ⟨⟨HasTyT.letE _ _ _ _ _ _ al vl bl⟩, hlet hΓ hA hv hb⟩
  | .sorts _ l1 l2 h =>
      ⟨⟨HasTyT.sort _ l1⟩,
        ⟨HasTyT.conv _ _ _ _ _ (HasTyT.sort _ l2)
          (ConvT.symm _ _ _ _
            (ConvT.sorts _ _ _ (eqN_succ h)))⟩⟩
  | .consts _ r ls _ m hres hlen hwf hwf' hh =>
      ⟨⟨HasTyT.const _ r ls m hres hlen hwf⟩, hconst hΓ hres hlen hwf hwf' hh⟩
  | .eta _ f A B hf => ⟨hη hΓ hf, ⟨hf⟩⟩
  | .irr _ _ _ _ _ hp hq => ⟨⟨hp⟩, ⟨hq⟩⟩
  | .tyConv _ _ _ _ _ _ h hA =>
      have ih := DT009T_endpointsS hcl hinst hΓ hη happ hlam hpi hlet hzeta hconst h
      ⟨ih.1.elim fun hl => ⟨HasTyT.conv _ _ _ _ _ hl hA⟩,
        ih.2.elim fun hr => ⟨HasTyT.conv _ _ _ _ _ hr hA⟩⟩

/-- the conditional endpoint theorem, `EnvWf`-fronted one-liner over the
    structure core. -/
def DT009T_endpoints {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hη : ConvTEtaLeftT E n) (happ : ConvTAppRightT E n)
    (hlam : ConvTLamRightT E n) (hpi : ConvTPiRightT E n)
    (hlet : ConvTLetRightT E n) (hzeta : ConvTZetaRightT E n)
    (hconst : ConvTConstsRightT E n) :
    {a b T : Expr Nat}→
    ConvT E n Γ a b T →
    Nonempty (HasTyT E n Γ a T) ∧ Nonempty (HasTyT E n Γ b T) :=
  DT009T_endpointsS (envWf_closed hE) (envWf_subst_inst hE) hΓ hη happ hlam hpi
    hlet hzeta hconst

/-! ## the positive instance: the revised η promise, constructibly, on legal
input. `f0 := λ (x : Sort 0), x` at `Sort 0`; the eta expansion's typing is
built from the judgment's own constructors + the typed weakening — the revised
call's target branch is real, not merely non-refuted. -/

/-- `f0 : Π (x : Sort 0), Sort 0` — the identity on sorts. -/
def pinEtaF0 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)) :=
  HasTyT.lam [] (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
    (HasTyT.sort [] .zero) (HasTyT.bvar _ _ _ rfl)

/-- the eta expansion of `f0` — typed at the SAME π, from constructors and the
    typed weakening only (this is a legal-input witness of `ConvTEtaLeftT`'s
    conclusion shape; the DEBT remains universally quantified and unproven). -/
def pin_etaLeft_identity (E : ResolvedEnv) (n : Nat) (hcl : EnvClosed E) :
    Nonempty (HasTyT E n []
      (.lam (.sort .zero) (.app (lift 0 1 (.lam (.sort .zero) (.bvar 0))) (.bvar 0)))
      (.pi (.sort .zero) (.sort .zero))) :=
  ⟨HasTyT.lam [] (.sort .zero) (.succ .zero)
    (.app (lift 0 1 (.lam (.sort .zero) (.bvar 0))) (.bvar 0)) (.sort .zero)
    (HasTyT.sort [] .zero)
    (HasTyT.app _ _ _ _ _
      (hasTyTWeaken (LocalDecl.assumption (.sort .zero)) hcl
        (c := 0) (pinEtaF0 E n))
      (HasTyT.bvar _ _ _ rfl))⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyTExt
#print axioms Rcic.Declarative.convTExt
#print axioms Rcic.Declarative.tyConvTExt
#print axioms Rcic.Declarative.DT008T_closure_fixedType
#print axioms Rcic.Declarative.eqN_succ
#print axioms Rcic.Declarative.ConvTEtaLeftT
#print axioms Rcic.Declarative.ConvTAppRightT
#print axioms Rcic.Declarative.ConvTLamRightT
#print axioms Rcic.Declarative.ConvTPiRightT
#print axioms Rcic.Declarative.eqN_succ
#print axioms Rcic.Declarative.ConvTEtaLeftT
#print axioms Rcic.Declarative.ConvTAppRightT
#print axioms Rcic.Declarative.ConvTLamRightT
#print axioms Rcic.Declarative.ConvTPiRightT
#print axioms Rcic.Declarative.ConvTLetRightT
#print axioms Rcic.Declarative.ConvTZetaRightT
#print axioms Rcic.Declarative.ConvTConstsRightT
#print axioms Rcic.Declarative.DT009T_endpoints
