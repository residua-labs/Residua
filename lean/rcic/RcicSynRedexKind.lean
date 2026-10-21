import rcic.RcicSynDomPath
import rcic.RcicIota

/-!
# Syntactic sortRow — T13: redex kind views (ChatGPT S8, #7338)

Spec: `research/rcic/sortrow/S8_REDEX_KIND_VIEWS.md`. `closure_claim = 0`.

`RedexKindView c p` is an evidenced domain view for an original redex
occurrence `c` — the produced `p : TyP … domT (sort α)` is built from **that
node's real fields only**; the ctor name is the original redex position and
direction, and the `hdom`-style fields keep the exact equations between the
displayed lhs/rhs and the original node:

- **β-under** (`body = pi A₀ B₀`, S8 §2): `piInvP` reads the domain template
  out of the original `hbody`; the original lazy substitution `k3DomInst`
  instantiates it at the original `harg`/`hA` — atoms concatenate the three
  original fields, no new β/Π conversion node is generated.
- **β-hit** (`body = bvar 0`, `arg = pi A' B'`): `piInvP` of the original
  `harg` directly — never keeps requiring `hbody` to be a Π typing and never
  takes another same-type argument.
- **δ** (`instantiateLevels ls b = pi A' B'`, S8 §3): `piInvP` of the original
  `hb`, cast through the displayed equation — the **same stored body**, never
  a regenerated unfolding compared against a second one.
- **ζ-under** (`body = pi A₀ B₀`, S8 §4): `piInvP` of the original `hb` in the
  `letBinding` context, then the real `lsub` at `j = 0` — `.letBinding` is
  never swapped for `.assumption` to reuse the β helper.
- **ζ-hit** (`body = bvar 0`, `value = pi A' B'`): `piInvP` of the original
  `hv`.
- **ι direct** (`rhs = pi A' B'`, S8 §5): `piInvP` of the original `hrhs` —
  reading `hrhs` needs no subject reduction and never takes the current ι's
  own ES as premise (a same-rank cycle, refused structurally: no ctor field
  can carry it).

A `RedexKindView` carries **no final kind equation**: connecting two views is
a separate request (K0/K2/K3 of T12), and equal middle expressions never
identify two reads.

Unpaid reads stay recorded as `RedexKindObligation` — the original demand and
its node: `betaPending`/`zetaPending` (the rhs Π is not exposed by the direct
body split; continue along the finite original path, never evaluate the rhs
recursively), `deltaPending`, `iotaPlan` (the RHS template plan — the actual
minor position, ctorParams/recursor parameters, ls/lsC and rhsArgs order all
stay inside the original `h : DerivedIota` field of the node), `arm` (every
other arm's own route). A recursive result is never evaluated at compile
time — there is no evaluator field anywhere.

`redexDom` is the read: it inspects only the original node's real fields and
the displayed Π shape, never normalizes "until a Π appears". T13 stays OPEN:
general head-view coherence across different computation paths, bounded reads
of deep transports, and the full ι RHS slot correspondence are not covered.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- An evidenced domain view for an original redex occurrence: index `c` is the
    original node, index `p` the produced domain sort typing built from `c`'s
    real fields. -/
inductive RedexKindView : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {lhs rhs T : Expr Nat} → CvP E n Γ lhs rhs T → {domT : Expr Nat} →
    {α : Level} → TyP E n Γ domT (.sort α) → Type where
  /-- β-under: the original body template `A₀ : sort uπ` read out of `hbody`,
      instantiated at the original `harg`/`hA` by `k3DomInst` (the lazy
      substitution — `instEnd`). -/
  | betaUnder {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A body arg B : Expr Nat} {u : Level} {A₀ B₀ : Expr Nat}
      {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B}
      {harg : TyP E n Γ arg A}
      {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
      {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
      (hdom : body = .pi A₀ B₀) :
      RedexKindView
        (.beta E n Γ A body arg B u hA hbody harg dl dr)
        (k3DomInst
          (piInvP (envExt_refl E) (tyCast hdom rfl hbody) rfl).hA hA harg)
  /-- β-hit: the substituted variable exposes the Π — read the original
      `harg`'s domain directly. -/
  | betaHit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A body arg B : Expr Nat} {u : Level} {A' B' : Expr Nat}
      {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B}
      {harg : TyP E n Γ arg A}
      {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
      {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
      (hdom : body = .bvar 0) (hargPi : arg = .pi A' B') :
      RedexKindView
        (.beta E n Γ A body arg B u hA hbody harg dl dr)
        (piInvP (envExt_refl E) (tyCast hargPi rfl harg) rfl).hA
  /-- δ: the stored body viewed under the same `ls` — `piInvP` of the original
      `hb`, cast through `instantiateLevels ls b = pi A' B'`. Never a second
      unfolding. -/
  | deltaRhs {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {r : Nat} {ls : List Level} {m : CheckedMember} {b A' B' : Expr Nat}
      {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      (hdom : instantiateLevels ls b = .pi A' B') :
      RedexKindView
        (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        (piInvP (envExt_refl E) (tyCast hdom rfl hb) rfl).hA
  /-- ζ-under: `piInvP` of the original `hb` in the `letBinding` context, then
      the real `lsub` at `j = 0` — never an `.assumption` swap. -/
  | zetaUnder {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level} {A₀ B₀ : Expr Nat}
      {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
      {hb : TyP E n (.letBinding A value :: Γ) body B}
      {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
      {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
      (hdom : body = .pi A₀ B₀) :
      RedexKindView
        (.zeta E n Γ A value body B u hA hv hb dl dr)
        (TyP.lsub E n (.letBinding A value :: Γ) A₀ _ A value 0 u
          (piInvP (envExt_refl E) (tyCast hdom rfl hb) rfl).hA
          List.getElem?_cons_zero
          (tyCast (lift_zero_idx 0 value).symm (lift_zero_idx 0 A).symm hv)
          (tyCast (lift_zero_idx 0 A).symm rfl hA))
  /-- ζ-hit: the value exposes the Π — `piInvP` of the original `hv`. -/
  | zetaHit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level} {A' B' : Expr Nat}
      {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
      {hb : TyP E n (.letBinding A value :: Γ) body B}
      {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
      {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
      (hdom : body = .bvar 0) (hvPi : value = .pi A' B') :
      RedexKindView
        (.zeta E n Γ A value body B u hA hv hb dl dr)
        (piInvP (envExt_refl E) (tyCast hvPi rfl hv) rfl).hA
  /-- ι direct: `rhs` is literally a Π — `piInvP` of the original `hrhs`. The
      current ι's ES is never a premise (the cycle is refused structurally:
      there is no field for it). -/
  | iotaDirect {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {lhs rhs T A' B' : Expr Nat}
      {h : DerivedIota E lhs rhs}
      {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
      {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
      (hdom : rhs = .pi A' B') :
      RedexKindView
        (.iota E n Γ lhs rhs T h hlhs hrhs dl dr)
        (piInvP (envExt_refl E) (tyCast hdom rfl hrhs) rfl).hA

/-- The unpaid redex-read demand (S8 §2–5): the original node is the index —
    every real field stays reachable through it. -/
inductive RedexKindObligation : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {lhs rhs T : Expr Nat} → CvP E n Γ lhs rhs T → Type where
  /-- The β rhs is not exposed by the direct body split — more original
      conversion fields follow; continue along the finite original path,
      never evaluate the rhs recursively. -/
  | betaPending {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A body arg B : Expr Nat} {u : Level}
      {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B}
      {harg : TyP E n Γ arg A}
      {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
      {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)} :
      RedexKindObligation (.beta E n Γ A body arg B u hA hbody harg dl dr)
  /-- The ζ rhs is not exposed by the direct body split — same original-path
      continuation demand. -/
  | zetaPending {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level}
      {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
      {hb : TyP E n (.letBinding A value :: Γ) body B}
      {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
      {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)} :
      RedexKindObligation (.zeta E n Γ A value body B u hA hv hb dl dr)
  /-- The δ rhs is not a literal Π — the stored body supplies only itself;
      the rest must consume the β/app occurrences on the original path. -/
  | deltaPending {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
      {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)} :
      RedexKindObligation
        (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
  /-- The ι rhs is not a literal Π — the finite RHS template plan: the actual
      minor position, ctorParams/recursor parameters, ls/lsC, rhsArgs order
      and kept recursive results all stay inside the original `h` field. -/
  | iotaPlan {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {lhs rhs T : Expr Nat}
      {h : DerivedIota E lhs rhs}
      {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
      {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T} :
      RedexKindObligation (.iota E n Γ lhs rhs T h hlhs hrhs dl dr)
  /-- Every other arm: its own route (§6's call table), never a forced read. -/
  | arm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
      (c : CvP E n Γ lhs rhs T) : RedexKindObligation c

/-- The read result inside the fixed original forest `H`: an evidenced
    `RedexKindView` **at an actual occurrence** — the `CvPOcc H` certificate on
    `view`/`obligation` is the same P2 contract as `DomPath.edge`: no generated
    `symm`/`fsub`/hconv node can be read, since it cannot produce the cert. -/
inductive RedexKindRead (H : CvPAny) : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {lhs rhs T : Expr Nat} → CvP E n Γ lhs rhs T → Type where
  | view {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T domT : Expr Nat}
      {α : Level} {c : CvP E n Γ lhs rhs T} {p : TyP E n Γ domT (.sort α)}
      (v : RedexKindView c p)
      (occ : CvPOcc H (.mk c)) : RedexKindRead H c
  | obligation {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
      {c : CvP E n Γ lhs rhs T} (d : RedexKindObligation c)
      (occ : CvPOcc H (.mk c)) : RedexKindRead H c

/-- Decidable "this stored body instantiates to a literal Π" — the δ
    dispatch premise (S8 §3). A pure structural decision on the instantiated
    expression: no unfolding is regenerated and no index is rewritten, so the
    `dite` in `redexDom` never touches the node's own field types (the
    dependent `match h : instantiateLevels ls b` would try to abstract the
    scrutinee out of `hb`/`dr`/`hocc` and fail to produce a type-correct
    motive). -/
def decPiEq (e : Expr Nat) : Decidable (∃ A' B' : Expr Nat, e = .pi A' B') :=
  match e with
  | .pi A' B' => isTrue ⟨A', B', rfl⟩
  | .bvar _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h
  | .sort _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h
  | .const _ _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h
  | .app _ _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h
  | .lam _ _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h
  | .letE _ _ _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h
  | .lit _ => isFalse fun ⟨_, _, h⟩ => Expr.noConfusion h

attribute [instance] decPiEq

/-- The Π domain projection: `A` of `pi A B`, the expression itself
    otherwise. -/
def piDom : Expr Nat → Expr Nat
  | .pi A _ => A
  | e => e

/-- The Π codomain projection: `B` of `pi A B`, the expression itself
    otherwise. -/
def piCod : Expr Nat → Expr Nat
  | .pi _ B => B
  | e => e

/-- The decidable Π shape hands back the equation in projection form —
    `∃`-elimination stays at `Prop`, so `redexDom` never eliminates the
    witness into `Type` (the produced `RedexKindRead` lives in `Type`). -/
theorem pi_shape_dom_cod {e : Expr Nat}
    (h : ∃ A' B' : Expr Nat, e = .pi A' B') :
    e = .pi (piDom e) (piCod e) := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- The T13 read (S8 §1): accepts only an original redex occurrence — `hocc` is
    the `CvPOcc H` certificate that `c` sits inside the original forest `H` —
    that node's real fields are the index; the displayed Π shape is what the
    original input or the position still gives. It takes no evaluator and never
    defines its domain by "a Π was eventually obtained". On `beta`/`zeta` it
    splits the *original* body (`pi` → the template route, `bvar 0` → the hit
    route over the actual `arg`/`value`), on `delta` it asks whether the *same
    stored body* instantiates to a literal Π, on `iota` it reads the original
    `hrhs` only when the rhs is literally a Π — everything else stays recorded
    as its own obligation. -/
def redexDom {H : CvPAny} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {lhs rhs T : Expr Nat} → (c : CvP E n Γ lhs rhs T) →
    CvPOcc H (.mk c) → RedexKindRead H c
  | _, _, _, .beta _ _ _ _ body arg _ _ _ _ _ _ _, hocc =>
      match body with
      | .pi _ _ => .view (.betaUnder rfl) hocc
      | .bvar 0 =>
          match arg with
          | .pi _ _ => .view (.betaHit rfl rfl) hocc
          | _ => .obligation .betaPending hocc
      | _ => .obligation .betaPending hocc
  | _, _, _, .zeta _ _ _ _ value body _ _ _ _ _ _ _, hocc =>
      match body with
      | .pi _ _ => .view (.zetaUnder rfl) hocc
      | .bvar 0 =>
          match value with
          | .pi _ _ => .view (.zetaHit rfl rfl) hocc
          | _ => .obligation .zetaPending hocc
      | _ => .obligation .zetaPending hocc
  | _, _, _, .delta _ _ _ _ ls _ b _ _ _ _ _ _ _ _, hocc =>
      if h : ∃ A' B' : Expr Nat, instantiateLevels ls b = .pi A' B' then
        .view (.deltaRhs (pi_shape_dom_cod h)) hocc
      else .obligation .deltaPending hocc
  | _, _, _, .iota _ _ _ _ rhs _ _ _ _ _ _, hocc =>
      match rhs with
      | .pi _ _ => .view (.iotaDirect rfl) hocc
      | _ => .obligation .iotaPlan hocc
  | _, _, _, c, hocc => .obligation (.arm c) hocc

/-! ## The ι RHS template plan and head-view coherence (S8 §5–6) -/

/-- The finite ι RHS template plan (S8 §5): every component is an original
    field of the node's own witness — the actual minor position with its
    lookup certificate, the original `ctorParams` and recursor-side
    parameters, the original `ls`/`lsC`, the plain/`directRec` order, and
    the kept RHS spine whose `directRec` entries carry their
    `recCallField` recursive results **unevaluated**. -/
structure IotaRhsPlan (E : ResolvedEnv) (w : IotaWitness E) where
  /-- Index of the actual minor inside `preMajor`
      (`nparams + motive + ctorIdx`). -/
  minorPos : Nat
  /-- The actual minor. -/
  minor : Expr Nat
  /-- `preMajor[minorPos]?` is literally this minor (the original `hminor`). -/
  minorAt : w.preMajor[minorPos]? = some minor
  /-- Original constructor-side parameters of the major. -/
  ctorParams : List (Expr Nat)
  /-- Original recursor-side parameters (`preMajor.take nparams`). -/
  recParams : List (Expr Nat)
  /-- Original recursor universe vector. -/
  ls : List Level
  /-- Original constructor universe vector. -/
  lsC : List Level
  /-- The plain/`directRec` order the `rhsArgs` walk keeps. -/
  kinds : List RecKind
  /-- The kept RHS argument spine — `directRec` entries carry their
      `recCallField` recursive results unevaluated. -/
  args : List (Expr Nat)

/-- Extract the plan from the original witness — every field is a
    projection of `w`, so the plan can never carry a regenerated body. -/
def iotaRhsPlan {E : ResolvedEnv} (w : IotaWitness E) : IotaRhsPlan E w where
  minorPos := w.nparams + 1 + w.ctorIdx
  minor := w.minor
  minorAt := w.hminor
  ctorParams := w.ctorParams
  recParams := w.preMajor.take w.nparams
  ls := w.ls
  lsC := w.lsC
  kinds := w.kinds
  args := rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
    w.fields w.kinds w.ctorAfterParams

/-- The plan's spine IS `iotaRhsOf`'s: the rhs is `foldApps` of the kept
    minor and the kept args — the recursive results stay inside `args`,
    never computed to the end. -/
theorem iotaRhsOf_eq_plan {E : ResolvedEnv} (w : IotaWitness E) :
    iotaRhsOf w = foldApps (iotaRhsPlan w).minor (iotaRhsPlan w).args := rfl

/-- The node's own `h` field hands over the plan — `DerivedIota` is `.of w`,
    so the plan's witness is the original field itself. -/
def iotaRhsPlanOf {E : ResolvedEnv} {lhs rhs : Expr Nat} :
    (h : DerivedIota E lhs rhs) → Σ' w : IotaWitness E, IotaRhsPlan E w
  | .of w => ⟨w, iotaRhsPlan w⟩

/-- §6 control (ι, same-rank ES cycle): every view produced at an original
    ι node is `.iotaDirect` — the produced domain is `piInvP` of **that
    node's own** `hrhs`; there is no ctor that could take the current ι's
    ES as a premise. (`cases` here is direct: `.iota`'s type indices are
    the ctor's own fields, not computed terms; β/ζ/δ cannot be inverted
    this way since their `CvP` indices carry `instantiate0`/
    `instantiateLevels`-computed positions.) -/
theorem redexKindView_iota {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T domT : Expr Nat} {α : Level}
    {h : DerivedIota E lhs rhs}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
    {p : TyP E n Γ domT (.sort α)}
    (v : RedexKindView (.iota E n Γ lhs rhs T h hlhs hrhs dl dr) p) :
    ∃ A' B', ∃ hdom : rhs = .pi A' B',
      HEq p (piInvP (envExt_refl E) (tyCast hdom rfl hrhs) rfl).hA := by
  cases v with
  | iotaDirect hdom => exact ⟨_, _, hdom, HEq.rfl⟩

/-- The positive generic β-under read: the original body is literally a Π,
    so `redexDom` produces the `.betaUnder` view — `piInvP` of `hbody` plus
    the lazy `k3DomInst`. -/
theorem redexDom_beta_under {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A arg B A₀ B₀ : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) (.pi A₀ B₀) B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A (.pi A₀ B₀)) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg (.pi A₀ B₀)) (instantiate0 arg B)}
    (hocc : CvPOcc H
      (.mk (.beta E n Γ A (.pi A₀ B₀) arg B u hA hbody harg dl dr))) :
    redexDom (.beta E n Γ A (.pi A₀ B₀) arg B u hA hbody harg dl dr) hocc =
      .view (.betaUnder rfl) hocc := rfl

/-- The positive generic β-hit read: the original body is `bvar 0` and the
    original argument literally a Π — `piInvP` of `harg`. -/
theorem redexDom_beta_hit {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B A' B' : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) (.bvar 0) B}
    {harg : TyP E n Γ (.pi A' B') A}
    {dl : TyP E n Γ (.app (.lam A (.bvar 0)) (.pi A' B')) (instantiate0 (.pi A' B') B)}
    {dr : TyP E n Γ (instantiate0 (.pi A' B') (.bvar 0)) (instantiate0 (.pi A' B') B)}
    (hocc : CvPOcc H
      (.mk (.beta E n Γ A (.bvar 0) (.pi A' B') B u hA hbody harg dl dr))) :
    redexDom (.beta E n Γ A (.bvar 0) (.pi A' B') B u hA hbody harg dl dr)
        hocc = .view (.betaHit rfl rfl) hocc := rfl

/-- The positive generic ζ-under read. -/
theorem redexDom_zeta_under {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A value B A₀ B₀ : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) (.pi A₀ B₀) B}
    {dl : TyP E n Γ (.letE A value (.pi A₀ B₀)) (instantiate0 value B)}
    {dr : TyP E n Γ (instantiate0 value (.pi A₀ B₀)) (instantiate0 value B)}
    (hocc : CvPOcc H
      (.mk (.zeta E n Γ A value (.pi A₀ B₀) B u hA hv hb dl dr))) :
    redexDom (.zeta E n Γ A value (.pi A₀ B₀) B u hA hv hb dl dr) hocc =
      .view (.zetaUnder rfl) hocc := rfl

/-- The positive generic ζ-hit read. -/
theorem redexDom_zeta_hit {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B A' B' : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ (.pi A' B') A}
    {hb : TyP E n (.letBinding A (.pi A' B') :: Γ) (.bvar 0) B}
    {dl : TyP E n Γ (.letE A (.pi A' B') (.bvar 0)) (instantiate0 (.pi A' B') B)}
    {dr : TyP E n Γ (instantiate0 (.pi A' B') (.bvar 0)) (instantiate0 (.pi A' B') B)}
    (hocc : CvPOcc H
      (.mk (.zeta E n Γ A (.pi A' B') (.bvar 0) B u hA hv hb dl dr))) :
    redexDom (.zeta E n Γ A (.pi A' B') (.bvar 0) B u hA hv hb dl dr)
        hocc = .view (.zetaHit rfl rfl) hocc := rfl

/-- A β node whose original body is neither a literal Π nor `bvar 0` keeps
    its `.betaPending` obligation — the read never evaluates the rhs. -/
theorem redexDom_beta_pending {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
    (hocc : CvPOcc H (.mk (.beta E n Γ A body arg B u hA hbody harg dl dr)))
    (hnp : ∀ A₀ B₀ : Expr Nat, body ≠ .pi A₀ B₀) (hnb : body ≠ .bvar 0) :
    redexDom (.beta E n Γ A body arg B u hA hbody harg dl dr) hocc =
      .obligation .betaPending hocc := by
  cases body <;> first
    | rfl
    | exact absurd rfl (hnp _ _)
    | (rename_i k; cases k <;> first
        | rfl
        | exact absurd rfl hnb)

/-- β-hit miss: the body is `bvar 0` but the original `arg` is not a
    literal Π — `.betaPending`, the demand kept. -/
theorem redexDom_beta_hit_pending {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
    (hocc : CvPOcc H (.mk (.beta E n Γ A body arg B u hA hbody harg dl dr)))
    (h0 : body = .bvar 0) (hargnp : ∀ A' B' : Expr Nat, arg ≠ .pi A' B') :
    redexDom (.beta E n Γ A body arg B u hA hbody harg dl dr) hocc =
      .obligation .betaPending hocc := by
  subst h0
  cases arg <;> first | rfl | exact absurd rfl (hargnp _ _)

/-- A ζ node whose original body is neither a literal Π nor `bvar 0` keeps
    its `.zetaPending` obligation. -/
theorem redexDom_zeta_pending {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
    {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
    (hocc : CvPOcc H (.mk (.zeta E n Γ A value body B u hA hv hb dl dr)))
    (hnp : ∀ A₀ B₀ : Expr Nat, body ≠ .pi A₀ B₀) (hnb : body ≠ .bvar 0) :
    redexDom (.zeta E n Γ A value body B u hA hv hb dl dr) hocc =
      .obligation .zetaPending hocc := by
  cases body <;> first
    | rfl
    | exact absurd rfl (hnp _ _)
    | (rename_i k; cases k <;> first
        | rfl
        | exact absurd rfl hnb)

/-- ζ-hit miss: the body is `bvar 0` but the original `value` is not a
    literal Π — `.zetaPending`. -/
theorem redexDom_zeta_hit_pending {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
    {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
    (hocc : CvPOcc H (.mk (.zeta E n Γ A value body B u hA hv hb dl dr)))
    (h0 : body = .bvar 0) (hvnp : ∀ A' B' : Expr Nat, value ≠ .pi A' B') :
    redexDom (.zeta E n Γ A value body B u hA hv hb dl dr) hocc =
      .obligation .zetaPending hocc := by
  subst h0
  cases value <;> first | rfl | exact absurd rfl (hvnp _ _)

/-- An ι node whose rhs is literally a Π gives the `.iotaDirect` view —
    `piInvP` of the original `hrhs`. -/
theorem redexDom_iota_direct {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs T A' B' : Expr Nat}
    {h : DerivedIota E lhs (.pi A' B')}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ (.pi A' B') T}
    {dl : TyP E n Γ lhs T} {dr : TyP E n Γ (.pi A' B') T}
    (hocc : CvPOcc H
      (.mk (.iota E n Γ lhs (.pi A' B') T h hlhs hrhs dl dr))) :
    redexDom (.iota E n Γ lhs (.pi A' B') T h hlhs hrhs dl dr) hocc =
      .view (.iotaDirect rfl) hocc := rfl

/-- §6 control (Loop): an ι node whose rhs is not a literal Π keeps its
    `.iotaPlan` obligation — the RHS template plan stays inside the
    original `h`, the recursive results are never evaluated to the end. -/
theorem redexDom_iota_plan {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat} {h : DerivedIota E lhs rhs}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
    (hocc : CvPOcc H (.mk (.iota E n Γ lhs rhs T h hlhs hrhs dl dr)))
    (hnp : ∀ A' B' : Expr Nat, rhs ≠ .pi A' B') :
    redexDom (.iota E n Γ lhs rhs T h hlhs hrhs dl dr) hocc =
      .obligation .iotaPlan hocc := by
  cases rhs <;> first | rfl | exact absurd rfl (hnp _ _)

/-- The positive generic δ read: the node's **own** stored body `b`
    (`m.body = some b`) instantiates under the node's own `ls` to a literal
    Π — `piInvP` of the stored `hb`, never a second unfolding. The produced
    domain is read through the `piDom`/`piCod` projections of that same
    instantiated body. -/
theorem redexDom_delta_rhs {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    (hocc : CvPOcc H
      (.mk (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)))
    (hpi : ∃ A' B' : Expr Nat, instantiateLevels ls b = .pi A' B') :
    redexDom (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) hocc =
      .view (.deltaRhs (pi_shape_dom_cod hpi)) hocc := by
  show (if h : ∃ A' B' : Expr Nat, instantiateLevels ls b = .pi A' B' then
      RedexKindRead.view (.deltaRhs (pi_shape_dom_cod h)) hocc
    else .obligation .deltaPending hocc) =
      .view (.deltaRhs (pi_shape_dom_cod hpi)) hocc
  rw [dif_pos hpi]

/-- §6 control (δ, same-stored-body): the node's own stored body `b` does not
    instantiate to a literal Π under the node's own `ls` — the read keeps
    `.deltaPending` even though some *other* body `b₂` of the same member
    would instantiate to a Π. A reader that swaps `b` for `b₂` is not
    `redexDom`: the result is computed from the node's own `m.body = some b`
    field only. -/
theorem redexDom_delta_pending {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b b₂ A₀ B₀ : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    (hocc : CvPOcc H
      (.mk (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)))
    (hnp : ∀ A' B' : Expr Nat, instantiateLevels ls b ≠ .pi A' B')
    (_ : instantiateLevels ls b₂ = .pi A₀ B₀) :
    redexDom (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) hocc =
      .obligation .deltaPending hocc := by
  show (if h : ∃ A' B' : Expr Nat, instantiateLevels ls b = .pi A' B' then
      RedexKindRead.view (.deltaRhs (pi_shape_dom_cod h)) hocc
    else .obligation .deltaPending hocc) =
      .obligation .deltaPending hocc
  rw [dif_neg (fun ⟨A', B', h⟩ => hnp A' B' h)]

/-- §5/§6 ι RHS slot correspondence (per-slot): the `rhsArgs` walk keeps each
    original field `f` in order; a `plain` slot contributes `f` alone, a
    `directRec` slot contributes `f` then the field's own
    `recCallField` recursive result — kept as a spine, never evaluated. -/
theorem rhsArgs_plain_slot (rec f : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (fs : List (Expr Nat)) (ks : List RecKind)
    (A B : Expr Nat) :
    rhsArgs rec preMajor nparams nMinors (f :: fs) (.plain :: ks) (.pi A B) =
      f :: rhsArgs rec preMajor nparams nMinors fs ks
        (instantiate0 f B) := rfl

/-- The `directRec` slot: `f` then `recCallField` at the field's own domain
    `A` — the recursive result stays an unevaluated spine entry. -/
theorem rhsArgs_directRec_slot (rec f : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (fs : List (Expr Nat)) (ks : List RecKind)
    (A B : Expr Nat) :
    rhsArgs rec preMajor nparams nMinors (f :: fs) (.directRec :: ks)
        (.pi A B) =
      f :: recCallField rec preMajor nparams nMinors f A ::
        rhsArgs rec preMajor nparams nMinors fs ks
          (instantiate0 f B) := rfl

/-- A field slot whose `kinds` ran out keeps the field — kind exhaustion is
    not a read failure. -/
theorem rhsArgs_kind_nil_slot (rec f : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (fs : List (Expr Nat)) (T : Expr Nat) :
    rhsArgs rec preMajor nparams nMinors (f :: fs) [] T =
      f :: rhsArgs rec preMajor nparams nMinors fs [] T := rfl

/-- Every original field appears, in order, inside the produced RHS spine —
    the read never drops a field and never inserts anything but the slot's
    own `recCallField`. -/
theorem rhsArgs_keeps_fields (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) :
    ∀ (fs : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat),
      List.Sublist fs (rhsArgs rec preMajor nparams nMinors fs ks T)
  | [], _, _ => .slnil
  | f :: fs, [], T =>
      .cons₂ f (rhsArgs_keeps_fields rec preMajor nparams nMinors fs [] T)
  | f :: fs, .plain :: ks, .pi _ B =>
      .cons₂ f (rhsArgs_keeps_fields rec preMajor nparams nMinors fs ks
        (instantiate0 f B))
  | f :: fs, .directRec :: ks, .pi A B =>
      .cons₂ f (.cons _
        (rhsArgs_keeps_fields rec preMajor nparams nMinors fs ks
          (instantiate0 f B)))
  | f :: fs, k :: ks, T => by
      have ih := fun t =>
        rhsArgs_keeps_fields rec preMajor nparams nMinors fs ks t
      cases k <;> cases T <;>
        first
          | exact .cons₂ f (.cons _ (ih _))
          | exact .cons₂ f (ih _)

/-- The slot count bound: each original field occupies at most its own slot
    plus one `directRec` insertion — the spine is `O(#fields)`, never the
    unbounded recursive evaluation S8 §6 refuses. -/
theorem rhsArgs_length_le (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) :
    ∀ (fs : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat),
      (rhsArgs rec preMajor nparams nMinors fs ks T).length ≤
        fs.length + fs.length
  | [], _, _ => Nat.zero_le _
  | f :: fs, [], T => by
      have ih := rhsArgs_length_le rec preMajor nparams nMinors fs [] T
      simp only [rhsArgs, List.length_cons]; omega
  | f :: fs, .plain :: ks, .pi _ B => by
      have ih := rhsArgs_length_le rec preMajor nparams nMinors fs ks
        (instantiate0 f B)
      simp only [rhsArgs, List.length_cons]; omega
  | f :: fs, .directRec :: ks, .pi A B => by
      have ih := rhsArgs_length_le rec preMajor nparams nMinors fs ks
        (instantiate0 f B)
      simp only [rhsArgs, List.length_cons]; omega
  | f :: fs, k :: ks, T => by
      have ih := fun t => rhsArgs_length_le rec preMajor nparams nMinors
        fs ks t
      cases k <;> cases T <;>
        simp only [rhsArgs, List.length_cons] <;>
        first
          | exact Nat.le_trans (Nat.add_le_add_right (ih _) 2) (by omega)
          | exact Nat.le_trans (Nat.add_le_add_right (ih _) 1) (by omega)

/-- The plan's spine keeps the original fields: `w.fields` is a sublist of
    `(iotaRhsPlan w).args` — every ctor field of the original witness is a
    slot of the RHS plan, in order. -/
theorem iotaRhsPlan_fields_sublist {E : ResolvedEnv} (w : IotaWitness E) :
    List.Sublist w.fields (iotaRhsPlan w).args :=
  rhsArgs_keeps_fields _ _ _ _ _ _ _

/-- The plan's spine is bounded by the original slot count: at most one
    `recCallField` insertion per original field/kind pair. -/
theorem iotaRhsPlan_length_le {E : ResolvedEnv} (w : IotaWitness E) :
    (iotaRhsPlan w).args.length ≤ w.fields.length + w.fields.length :=
  rhsArgs_length_le _ _ _ _ _ _ _

/-- Number of `directRec` slots in a `RecKind` list — each contributes
    exactly one `recCallField` entry to `rhsArgs`. -/
def numDirectRec : List RecKind → Nat
  | [] => 0
  | .directRec :: ks => numDirectRec ks + 1
  | _ :: ks => numDirectRec ks

/-- §5/§6 ι RHS slot correspondence (exact count): under the real
    `isPiTel` telescope gate and the real `fields/kinds` length equality —
    the same gates `IotaWitness` stores — every `rhsArgs` walk takes a
    typed slot arm, so the output spine is exactly `fields.length` kept
    fields plus `numDirectRec kinds` recursive results. -/
theorem rhsArgs_length_eq_of_tel (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) :
    ∀ (fs : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat),
      fs.length = ks.length → isPiTel ks.length T = true →
      (rhsArgs rec preMajor nparams nMinors fs ks T).length =
        fs.length + numDirectRec ks
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hfsk, _ => by nomatch hfsk
  | _ :: _, [], _, hfsk, _ => by nomatch hfsk
  | f :: fs, k :: ks, T, hfsk, htel => by
      have hfs : fs.length = ks.length :=
        Nat.succ.inj (by simpa only [List.length_cons] using hfsk)
      cases k <;> cases T <;>
        simp only [isPiTel, Bool.false_eq_true] at htel <;>
        first
          | exact htel.elim
          | (have htel' : isPiTel ks.length (instantiate0 f _) = true :=
              isPiTel_instantiate 0 f ks.length _ htel
             have h := rhsArgs_length_eq_of_tel rec preMajor nparams nMinors
               fs ks (instantiate0 f _) hfs htel'
             simp only [rhsArgs, List.length_cons, numDirectRec]
             rw [h]; ac_rfl)

/-- The plan's arg spine is exactly the original field count plus the
    original `directRec` slot count — no slot is dropped, duplicated, or
    added beyond the `recCallField` of each `.directRec` kind. -/
theorem iotaRhsPlan_args_length {E : ResolvedEnv} (w : IotaWitness E) :
    (iotaRhsPlan w).args.length = w.fields.length + numDirectRec w.kinds :=
  rhsArgs_length_eq_of_tel _ _ _ _ _ _ _ w.hlen.symm w.hctorTel

/-! ## `.arm` controls — transports and congruences are never views

A `trans`/`symm`/`fsub`/`cctx`/substitution node is a deep transport:
`redexDom` records its own `.arm` obligation — the read continues along
the finite original path instead of synthesizing a kind view. This is
the read-level form of S7 §2's `trans (symm b) b` control: a transport
node between two equal middles never produces a `RedexKindView`. -/

/-- `trans` is not a redex: the read is the node's own `.arm`. -/
theorem redexDom_trans_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b c T : Expr Nat} {h1 : CvP E n Γ a b T}
    {h2 : CvP E n Γ b c T} {dl : TyP E n Γ a T} {dr : TyP E n Γ c T}
    (hocc : CvPOcc H (.mk (.trans E n Γ a b c T h1 h2 dl dr))) :
    redexDom (.trans E n Γ a b c T h1 h2 dl dr) hocc =
      .obligation (.arm (.trans E n Γ a b c T h1 h2 dl dr)) hocc := rfl

/-- `symm` is not a redex. -/
theorem redexDom_symm_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} {h : CvP E n Γ a b T}
    {dl : TyP E n Γ b T} {dr : TyP E n Γ a T}
    (hocc : CvPOcc H (.mk (.symm E n Γ a b T h dl dr))) :
    redexDom (.symm E n Γ a b T h dl dr) hocc =
      .obligation (.arm (.symm E n Γ a b T h dl dr)) hocc := rfl

/-- `fsub` (functionality transport) is not a redex. -/
theorem redexDom_fsub_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B S a b : Expr Nat} {u : Level}
    {hB : TyP E n (.assumption A :: Γ) B S}
    {hA : TyP E n Γ A (.sort u)} {hab : CvP E n Γ a b A}
    {dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S)}
    {dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S)}
    (hocc : CvPOcc H
      (.mk (.fsub E n Γ A B S a b u hB hA hab dl dr))) :
    redexDom (.fsub E n Γ A B S a b u hB hA hab dl dr) hocc =
      .obligation (.arm (.fsub E n Γ A B S a b u hB hA hab dl dr))
        hocc := rfl

/-- `cctx` (binder context transport) is not a redex. -/
theorem redexDom_cctx_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T A A' : Expr Nat} {u : Level}
    {h : CvP E n (.assumption A :: Γ) a b T}
    {hA : CvP E n Γ A A' (.sort u)}
    (hocc : CvPOcc H (.mk (.cctx E n Γ a b T A A' u h hA))) :
    redexDom (.cctx E n Γ a b T A A' u h hA) hocc =
      .obligation (.arm (.cctx E n Γ a b T A A' u h hA)) hocc := rfl

/-- `tyConv` (type transport) is not a redex. -/
theorem redexDom_tyConv_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
    {h : CvP E n Γ a b A} {hA : CvP E n Γ A A' (.sort u)}
    {dl : TyP E n Γ a A'} {dr : TyP E n Γ b A'}
    (hocc : CvPOcc H (.mk (.tyConv E n Γ a b A A' u h hA dl dr))) :
    redexDom (.tyConv E n Γ a b A A' u h hA dl dr) hocc =
      .obligation (.arm (.tyConv E n Γ a b A A' u h hA dl dr)) hocc := rfl

/-- `wk` (context weakening) is not a redex. -/
theorem redexDom_wk_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} {d : LocalDecl} {c : Nat}
    {h : CvP E n Γ a b T}
    (hocc : CvPOcc H (.mk (.wk E n Γ a b T d c h))) :
    redexDom (.wk E n Γ a b T d c h) hocc =
      .obligation (.arm (.wk E n Γ a b T d c h)) hocc := rfl

/-- `esub` (expression substitution transport) is not a redex. -/
theorem redexDom_esub_arm {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T t v : Expr Nat} {j : Nat} {u : Level}
    {h : CvP E n Γ a b T} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    (hocc : CvPOcc H (.mk (.esub E n Γ a b T t v j u h hget hv hvT))) :
    redexDom (.esub E n Γ a b T t v j u h hget hv hvT) hocc =
      .obligation (.arm (.esub E n Γ a b T t v j u h hget hv hvT))
        hocc := rfl

/-- `linst` (level instantiation transport) is not a redex. -/
theorem redexDom_linst_arm {H : CvPAny} {E : ResolvedEnv} {a' n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a'}
    {h : CvP E a' Γ a b T}
    (hocc : CvPOcc H (.mk (.linst E a' n Γ a b T ls hls hlen h))) :
    redexDom (.linst E a' n Γ a b T ls hls hlen h) hocc =
      .obligation (.arm (.linst E a' n Γ a b T ls hls hlen h)) hocc :=
  rfl

/-- `ewk` (environment weakening) is not a redex. -/
theorem redexDom_ewk_arm {H : CvPAny} {E₀ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} {hext : EnvExt E₀ E}
    {h : CvP E₀ n Γ a b T}
    (hocc : CvPOcc H (.mk (.ewk E₀ E n Γ a b T hext h))) :
    redexDom (.ewk E₀ E n Γ a b T hext h) hocc =
      .obligation (.arm (.ewk E₀ E n Γ a b T hext h)) hocc := rfl

/-- The read's view/obligation tag — `hocc` is pure payload, so the tag is
    all that distinguishes a successful view from an unpaid demand. -/
def RedexKindRead.isView {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat} {c : CvP E n Γ lhs rhs T} :
    RedexKindRead H c → Bool
  | .view _ _ => true
  | .obligation _ _ => false

/-- Occurrence invariance (S8 §6 cross-path seed): WHICH route `redexDom`
    takes depends only on the node's own fields — the certificate records
    where the node sits in the original forest and never changes the read.
    The same original node read at two different occurrences is the same
    view/obligation; an occurrence positioned deeper along a transport
    path cannot turn a demand into a view. -/
theorem redexDom_occ_invariant {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {l r T : Expr Nat} (c : CvP E n Γ l r T)
    (hocc hocc' : CvPOcc H (.mk c)) :
    (redexDom c hocc).isView = (redexDom c hocc').isView := by
  cases c <;> simp only [redexDom] <;>
    repeat' (first
      | rfl
      | (split <;> simp only [RedexKindRead.isView]))

end Rcic.Syn

#print axioms Rcic.Syn.redexDom
#print axioms Rcic.Syn.redexKindView_iota
#print axioms Rcic.Syn.redexDom_iota_direct
#print axioms Rcic.Syn.redexDom_iota_plan
