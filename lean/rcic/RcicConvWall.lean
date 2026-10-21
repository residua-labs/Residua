/-
RCIC F-05b wall segment (00 §20.8; attempt 55's record made greppable).

This module is a STATEMENT CORRECTION (00 §19.6 shape), not a discharge.
It flips NO 00 §19.2 row, deletes NO premise, creates NO obligation and
adds NO row: `SortConvChar` / `PiConvInj` / `FamAppConvInj` stay OPEN
with `RedOnly` on them, `IotaPreserve` stays conditional, and
`closure_claim` stays `0`. What it does is turn three clauses of 00
§19.3 F-05b's ATTEMPT 55 record from sentences a reader must trust into
sealed names a reader can grep:

  * C-4  the `irr` arm's measure obstruction is DISSOLVED — a cut that
         consumes `hP` and EXACTLY ONE endpoint typing decreases
         UNCONDITIONALLY (`sizeConv_irr_cut_decreases`), and at a sort
         endpoint the actual inversion call is bounded too
         (`sizeConv_irr_sortCut`).  The `irr` arm is NOT where the wall
         is; NOTHING here says the arm is "closed".
  * C-5  `Conv.eta`'s left endpoint is always a `.lam`, so `eta` is
         `nomatch` at all three 00 §19.2 rows
         (`convEta_lhs_ne_sort` / `_ne_pi` / `_ne_famApp`).
  * the ARTIFACT (type-④): the reduction-class horn of the dilemma is
    REFUTED at the `app` congruence, over an `EnvWf` environment at
    `CtxWf.nil`, with no junk member, no junk local let and no
    non-arity family (`convClassTransfer_false`).

Placement: a LEAF importing `rcic.RcicParRedSR` only. Nothing lands
inside the ParRed tower.

Refutation discipline (`RcicRefutations.lean:25-29`): the artifact's
target is written out below as a LOCAL, UNCONDITIONED copy of the shape
being refuted, inline in `convClassTransfer_false`'s own statement — it
is never read from a shared reduction-class definition, and no such
shared definition is introduced (00 §20.8 S-5). `NoSortProp` is likewise
NOT defined here under any name (S-2), so
`noSortProp_piArm_readout` (`RcicParRedSR.lean:678`) keeps pointing at
nothing.

No `sorry`, no `native_decide`, no bare `simp`/`simpa`; axioms ⊆
{propext, Quot.sound}.
-/
import rcic.RcicParRedSR

namespace Rcic.Declarative

/-! ## Batch 1 — the `irr` measure fact (00 §19.3 C-4)

`sizeConv (.irr Γ P p q hP hp hq) = sizeHasTy hP + sizeHasTy hp +
sizeHasTy hq + 1` (`RcicDerivationRec.lean:68`). A recursion that
consumes `hP` and exactly ONE of the two endpoint typings therefore has
room to spare, by `sizeHasTy_pos` alone and with NO side condition —
which is what `irr_sorts_char` (`RcicParRedSortWall.lean:3512`) already
does silently by recomposing `hp` and `hq` and DISCARDING `hP`.

WHAT THIS IS NOT. It is not a discharge of any row, and it does not say
the `irr` arm is closed. Attempt 55's dilemma is unmoved: the invariant
a `Conv`-recursion carries must survive `Conv.trans` with an arbitrary
middle AND the term congruences with arbitrary components. These two
statements say only that the ARITHMETIC at `irr` is not the obstacle. -/

/-- The `irr` cut decreases UNCONDITIONALLY. A recursive call that
carries `hP` and ONE endpoint typing is bounded by
`sizeConv (.irr …) − 2`, at every `P`, `p`, `q` — no `sizeHasTy hP > 1`
side condition, which is the condition attempt 53's reading needed and
which fails at every leaf `hP`. -/
theorem sizeConv_irr_cut_decreases {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ p P) (hq : HasTy E n Γ q P) :
    sizeHasTy hP + sizeHasTy hp + 2
      ≤ sizeConv (Conv.irr (E := E) (n := n) Γ P p q hP hp hq) := by
  simp only [sizeConv]
  have hpos := sizeHasTy_pos hq
  omega

/-- The same bound for the call a SORT endpoint actually makes: the
`Conv` that `hasTySortInv` builds is itself bounded by `sizeHasTy hp`
(the sealed `sizeConv_hasTySortInv`, `RcicParRedSortWall.lean:3436`), so
the composite still fits under `sizeConv (.irr …) − 2`. The sort
endpoint is exactly where attempt 55 measured the recorded obstruction,
which is why the correction stands on this form. -/
theorem sizeConv_irr_sortCut {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {P q : Expr Nat} {u : Level}
    (hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ (.sort u) P) (hq : HasTy E n Γ q P) :
    sizeConv (hasTySortInv hp rfl) + sizeHasTy hP + 2
      ≤ sizeConv (Conv.irr (E := E) (n := n) Γ P (.sort u) q hP hp hq) := by
  simp only [sizeConv]
  have hinv := sizeConv_hasTySortInv hp rfl
  have hpos := sizeHasTy_pos hq
  omega

/-! ## Batch 2 — the `eta` shape fact (00 §19.3 C-5)

`Conv.eta`'s LEFT endpoint is always `.lam A (.app (lift 0 1 f) (.bvar 0))`
(`RcicDeclarative.lean:1118`) — always a `.lam`. No 00 §19.2 row has
`.lam` as an endpoint shape: the three left endpoints are `.sort u`,
`.pi A B` and `foldApps (.const r ls) xs`. So `Conv.eta` is `nomatch`
at all three rows, and eta-postponement past `⇒*` is a residual of the
JOIN route (`convRedOnly_join`, `RcicConvChar.lean:528`), NOT of a
direct `Conv`-recursion on the rows.

These three statements carry NO `HasTy` premise: one would be
content-free here. Their value is not proof content — it is that C-5's
clause becomes GREPPABLE. The family row needs NO new
`foldApps_snoc_ne_lam` (that name is measured absent, and a design that
inferred the FACT absent from the absent NAME was wrong): the fact is
landed as `foldApps_const_ne_lam` (`RcicParRedCore.lean:609`), which
covers EVERY `xs`, including `[]`. Zero new lemmas land in the ParRed
tower. -/

/-- C-5, sort row: `Conv.eta`'s left endpoint is never a sort. -/
theorem convEta_lhs_ne_sort {A f : Expr Nat} {u : Level} :
    (Expr.lam A (.app (lift 0 1 f) (.bvar 0)) : Expr Nat) ≠ .sort u :=
  fun h => Expr.noConfusion h

/-- C-5, Π row: `Conv.eta`'s left endpoint is never a Π. -/
theorem convEta_lhs_ne_pi {A f X Y : Expr Nat} :
    (Expr.lam A (.app (lift 0 1 f) (.bvar 0)) : Expr Nat) ≠ .pi X Y :=
  fun h => Expr.noConfusion h

/-- C-5, family row: `Conv.eta`'s left endpoint is never a const-headed
application spine — at EVERY `xs`, `[]` included, by the LANDED
`foldApps_const_ne_lam`. -/
theorem convEta_lhs_ne_famApp {A f : Expr Nat} {r : Nat}
    {ls : List Level} (xs : List (Expr Nat)) :
    (Expr.lam A (.app (lift 0 1 f) (.bvar 0)) : Expr Nat)
      ≠ foldApps (.const r ls) xs :=
  fun h => foldApps_const_ne_lam xs h.symm

/-! ## Batch 3 — the `app`-congruence refutation (00 §19.3's ARTIFACT; type-④)

THE CARRIER. `wallProp := Π (Q : Prop). Q` is Prop-typed at EVERY `E`,
`n`, `Γ` (the landed `noSortProp_piArm_witness`, `RcicParRedSR.lean:663`),
so `wallQ := wallProp → wallProp` is Prop-typed too, by impredicativity
(`HasTy.pi` lands at `.sort (.imax .zero .zero)` and `Conv.sorts` on
`eqN_imax_zero .zero` lifts it to `.sort .zero`). `wallEnv` extends
`emptyEnv` with ONE `axiomM` member at `wallQ`. There is NO junk local
let (`junkLetCtx`), NO junk env member (`piIrrMember`) and NO non-arity
family (`famPropMember`): the environment is `EnvWf` and the context is
`CtxWf.nil`, so both of 00 §19.2's conditioning corrections (errata 2
and 3) are SATISFIED and powerless here — the junk lives in the TERM.

THE MECHANISM. `wallQ` is a Prop with two inhabitants: the computing
`.lam wallProp (.bvar 0)` and the rigid `.const 0 []` (an `axiomM`
stores `body = none`, and `parRed_const`'s delta summand requires
`m.body = some body`, `RcicParRedWeight.lean:39`). `Conv.irr` identifies
them, `Conv.app` carries that node into an application whose ARGUMENT is
junk for the domain — and the whole application is UNTYPABLE, so no
typing exists downstream to cut the `irr` node. The left side beta-
reduces to a sort; the right side reduces only to const-headed
applications. The reduction class is therefore NOT transferred along
`Conv` at the `app` congruence, and that is a REFUTATION, not a gap.

WHAT IT REFUTES AND WHAT IT DOES NOT. It refutes the reduction-class
horn of attempt 55's dilemma. It refutes NO 00 §19.2 row: the endpoints
here are APPLICATIONS, not sorts, Π's or family applications. It does
not touch `convRedOnly_join` (`RcicConvChar.lean:528`) — `RedOnly` is
`False` on this `Conv` by its `irr` leaf, exactly as that predicate
intends.

THE INDEPENDENT CROSS-CHECK (RECORDED FROM THE DESIGN, NOT RE-MEASURED
ON THIS TREE, and nothing in this batch depends on it). Attempt 55
produced a SECOND, independent carrier for the same conclusion, on a
DIFFERENT environment and a DIFFERENT context: `emptyEnv` itself
(`EnvWf` by `EnvWf.empty`, `RcicEnv.lean:452`) with a five-assumption
`CtxWf` context

    Γ₁ = [assumption (.sort (.succ .zero))]                 -- U : Sort 1
    Γ₂ = assumption (.sort .zero)             :: Γ₁         -- P : Prop
    Γ₃ = assumption (.pi (.bvar 0) (.bvar 2)) :: Γ₂         -- f : P → U
    Γ₄ = assumption (.bvar 1)                 :: Γ₃         -- p : P
    Γ₅ = assumption (.bvar 2)                 :: Γ₄         -- q : P

where `.bvar 1` and `.bvar 0` are two proofs of the Prop `.bvar 3`,
`Conv.irr` identifies them, and `Conv.app` lifts that to
`f p ≡ f q` — an `irr` node at DEPTH 1 under a congruence, with no
common `⇒*` reduct (both sides are `⇒*`-normal: `parRed_app`'s beta
summand needs a `.lam` head, its iotaSpine summand is refuted by the
`foldApps`-head fact, and the congruence summand recurses into
`parRed_bvar`, whose `bvarZeta` branch needs a `letBinding`). Its
one-line content is the sentence the record otherwise lacks:
`Conv.irr` occurs at ARBITRARY DEPTH under congruence, so no relation
whose irrelevance component sits at the ENDPOINTS is closed under
`Conv.app`. That two independent carriers — different environment,
different context, different depth — reach the same conclusion is this
artifact's strongest property. -/

/-- `Π (Q : Prop). Q`: the impredicative Prop. Prop-typed at EVERY `E`,
`n`, `Γ` by the landed `noSortProp_piArm_witness`. -/
def wallProp : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- `wallProp → wallProp`. A Prop again, by impredicativity. -/
def wallQ : Expr Nat := .pi wallProp wallProp

/-- ONE `axiomM` member at `wallQ`, over `emptyEnv`. No junk. -/
def wallEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.axiomM, 0, wallQ, none⟩

/-- `wallQ : Prop`, at every environment, universe bound and context.
`HasTy.pi` gives `.sort (.imax .zero .zero)`; `Conv.sorts` on
`eqN_imax_zero .zero` lifts it to the `.sort .zero` that `Conv.irr`
demands — the idiom `noSortProp_piArm_witness` itself uses. -/
def wallQ_isProp {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ wallQ (.sort .zero) :=
  .conv Γ wallQ (.sort (.imax .zero .zero)) (.sort .zero)
    (.pi Γ wallProp .zero wallProp .zero
      (noSortProp_piArm_witness Γ)
      (noSortProp_piArm_witness (LocalDecl.assumption wallProp :: Γ)))
    (.sorts Γ (.imax .zero .zero) .zero (eqN_imax_zero .zero))

/-- `EnvWf.axiom`'s closedness side condition, by explicit `if_neg` on
`lift`'s `.bvar` clause — never a bare `simp` (§18.3 rule 3); this is
the landed `famPropMember_closed` idiom (`RcicRefutations.lean:207`). -/
theorem wallQ_closed (k : Nat) : lift k 1 wallQ = wallQ := by
  simp only [wallQ, wallProp, lift]
  rw [if_neg (Nat.not_succ_le_zero k), if_neg (Nat.not_succ_le_zero (k + 1))]

/-- The carrier environment is WELL-FORMED. `hfresh` is `rfl`
(`emptyEnv.members := fun _ => none`); `hA` is `wallQ_isProp []` at
`emptyEnv`; `hcl` is `wallQ_closed`. Type-valued conclusion, so a
`def` (§18.3). -/
def wallEnv_envWf (n : Nat) : EnvWf wallEnv n :=
  .axiom (n := n) emptyEnv 0 wallQ .zero (.empty n) rfl (wallQ_isProp []) wallQ_closed

/-- THE `Conv`: a `Conv.irr` at the Prop `wallQ`, between the computing
`.lam` and the rigid axiom constant, placed UNDER a `Conv.app`. `Γ = []`,
so `CtxWf` is `CtxWf.nil`; `EnvWf` is `wallEnv_envWf`. The argument
`.sort w` is not typed at `wallProp` — the application is untypable, and
that is the point: `Conv.app` carries the `irr` node into a position
where no typing exists to cut it. -/
def wall_conv_app_irr (n : Nat) (w : Level) :
    Conv wallEnv n []
      (.app (.lam wallProp (.bvar 0)) (.sort w))
      (.app (.const 0 []) (.sort w)) :=
  .app [] (.lam wallProp (.bvar 0)) (.const 0 []) (.sort w) (.sort w)
    (.irr [] wallQ (.lam wallProp (.bvar 0)) (.const 0 [])
      (wallQ_isProp [])
      (.lam [] wallProp .zero (.bvar 0) wallProp
        (noSortProp_piArm_witness [])
        (.bvar (LocalDecl.assumption wallProp :: []) 0 wallProp rfl))
      (.const [] 0 [] ⟨.axiomM, 0, wallQ, none⟩ rfl rfl (fun _ hl => nomatch hl)))
    (.refl [] (.sort w))

/-- The RIGHT-HAND shape analysis, forded on the source exactly as the
landed `parRedStar_lam_app_body_sort` (`RcicParRedWeight.lean:258`) is
written: every `⇒*` reduct of an application of the AXIOM constant is
AGAIN an application of that constant. Three summands of `parRed_app`
(`RcicParRedWeight.lean:203`): CONGRUENCE keeps the const head
(`parRed_const`'s delta summand needs `m.body = some body` and this
member stores `none`); BETA needs a `.lam` head; IOTASPINE would force
`w.recRef = 0` through `foldApps_const_inj`, and `wallEnv.members 0` is
the `axiomM` member, contradicting `IotaWitness.hrecK`. Type-valued
conclusion, so a `def`. -/
def parRedStar_constApp_shape {n : Nat} {Γ : LCtx}
    {ls : List Level} {arg a e : Expr Nat}
    (h : ParRedStar wallEnv n Γ a e)
    (ha : a = .app (.const 0 ls) arg) :
    Σ' (ls' : List Level) (x' : Expr Nat), e = .app (.const 0 ls') x' :=
  match h with
  | .refl _ _ => ⟨ls, arg, ha⟩
  | .tail h0 hs =>
      match parRed_app h0 ha with
      | .inl ⟨f', x', hc, hf, _hx⟩ =>
          match parRed_const hf rfl with
          | .inl ⟨ls', hf', _⟩ =>
              parRedStar_constApp_shape (ls := ls') (arg := x') hs
                (hc.trans (congrArg (fun t => Expr.app t x') hf'))
          | .inr ⟨_m, _body, hres, hbody, _htr, _⟩ => by
              have hm : (some ⟨.axiomM, 0, wallQ, none⟩ : Option CheckedMember)
                  = some _m := hres
              injection hm with hmeq
              rw [← hmeq] at hbody
              exact Option.noConfusion hbody
      | .inr (.inl ⟨_A, _body, _A', _body', _x', hlam, _, _, _, _⟩) =>
          nomatch hlam
      | .inr (.inr ⟨w, lsR, lsC, pre, _pre', fields, _fields',
                    _, _, _, _, _, _, _, hcall, _⟩) => by
          have hfold := foldApps_const_inj
            (show foldApps (.const w.recRef lsR)
                (pre ++ [foldApps (.const w.ctorRef lsC) fields])
              = foldApps (.const 0 ls) [arg] from hcall)
          have hhead := hfold.1
          injection hhead with hr _
          have hrec := w.hrec
          rw [hr] at hrec
          have hax : (some ⟨.axiomM, 0, wallQ, none⟩ : Option CheckedMember)
              = some w.recMember := hrec
          injection hax with hmeq
          have hk := w.hrecK
          rw [← hmeq] at hk
          exact MemberClass.noConfusion hk

/-- NO `ParRed` star out of an application of the AXIOM constant reaches
a sort. This is the right-hand half of the class mismatch. -/
theorem parRedStar_constApp_ne_sort {n : Nat} {Γ : LCtx}
    {ls : List Level} {a e : Expr Nat} {v : Level} :
    ParRedStar wallEnv n Γ (.app (.const 0 ls) a) e →
    e = .sort v → False :=
  fun h he =>
    let ⟨_ls', _x', hshape⟩ := parRedStar_constApp_shape h rfl
    Expr.noConfusion (hshape.symm.trans he)

/-- TYPE-④ (00 §19.3's ARTIFACT). The reduction class
`Σ' u, e ⇒* .sort u` is NOT transferred along `Conv` at the `app`
congruence, under `EnvWf` (`wallEnv_envWf`) at `CtxWf.nil`.

The refuted shape is written out HERE as a LOCAL, UNCONDITIONED copy,
inline in this statement, per `RcicRefutations`' own discipline
(`RcicRefutations.lean:25-29`): a refutation that reads its own target
from a definition another patch may edit is not evidence about the
shape it names. No shared reduction-class definition is introduced
anywhere (00 §20.8 S-5).

It refutes NO 00 §19.2 row: the endpoints are APPLICATIONS. -/
theorem convClassTransfer_false :
    ((n : Nat) → (Γ : LCtx) → (a b : Expr Nat) →
      Conv wallEnv n Γ a b →
      (Σ' u, ParRedStar wallEnv n Γ a (.sort u)) →
      (Σ' v, ParRedStar wallEnv n Γ b (.sort v))) → False :=
  fun htransfer =>
    let hleft : Σ' u, ParRedStar wallEnv 0 []
        (.app (.lam wallProp (.bvar 0)) (.sort .zero)) (.sort u) :=
      ⟨.zero,
        .tail
          (.beta [] wallProp wallProp (.bvar 0) (.bvar 0)
            (.sort .zero) (.sort .zero)
            (.refl _ _) (.refl _ _) (.refl _ _))
          (.refl _ _)⟩
    let hright := htransfer 0 []
      (.app (.lam wallProp (.bvar 0)) (.sort .zero))
      (.app (.const 0 []) (.sort .zero))
      (wall_conv_app_irr 0 .zero) hleft
    parRedStar_constApp_ne_sort hright.2 rfl

/-- The LEFT-HAND analysis (00 §20.8 NAMED GAP 3). It CANNOT reuse the
landed `parRedStar_lam_app_body_sort` (`RcicParRedWeight.lean:258`):
measured, that lemma takes `hbod : body = .sort u`, and this carrier's
body is `.bvar 0`. So the star is walked here. `parRed_lam_app`
(`RcicParRedWeight.lean:150`) already kills the iotaSpine summand
(`foldApps_const_ne_lam`), leaving CONGRUENCE — where `parRed_bvar`
(`RcicParRedDiamond.lean:1439`) pins `body' = .bvar 0`, its `bvarZeta`
branch needing a `letBinding` that an `assumption` context head cannot
supply, and `parRed_sort` pins `arg' = .sort w'`, so the shape is
PRESERVED — and BETA, where the reduct is `instantiate0 (.sort w')
(.bvar 0)`, i.e. `.sort w'`, from which `parRedStar_sort` gives only
sorts. Either way the left side never reaches a const-headed
application. -/
theorem parRedStar_lamBvar_app_ne_constApp {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {x : Expr Nat}
    {A a e : Expr Nat} {w : Level}
    (h : ParRedStar wallEnv n Γ a e)
    (ha : a = .app (.lam A (.bvar 0)) (.sort w))
    (he : e = .app (.const r ls) x) : False :=
  match h with
  | .refl _ _ => by
      injection (ha.symm.trans he) with hhead _
      exact Expr.noConfusion hhead
  | .tail h0 hs =>
      match parRed_lam_app h0 ha with
      | .inl ⟨A', body', arg', heq, _hA, hb, hx⟩ =>
          match parRed_bvar hb rfl with
          | .inl hbody =>
              let ⟨w', harg, _⟩ := parRed_sort hx rfl
              parRedStar_lamBvar_app_ne_constApp (A := A') (w := w') hs
                (by rw [hbody, harg] at heq; exact heq) he
          | .inr ⟨A0, v0, _v', hget, _, _⟩ => by
              have hg : (some (LocalDecl.assumption A) : Option LocalDecl)
                  = some (.letBinding A0 v0) := hget
              injection hg with hg1
              exact LocalDecl.noConfusion hg1
      | .inr ⟨_A', body', arg', _hA, hb, hx, heq⟩ =>
          match parRed_bvar hb rfl with
          | .inl hbody =>
              let ⟨w', harg, _⟩ := parRed_sort hx rfl
              let hc : _ = Expr.sort w' := by
                rw [hbody, harg] at heq; exact heq
              let ⟨_v0, hsort, _⟩ := parRedStar_sort hs hc
              Expr.noConfusion (hsort.symm.trans he)
          | .inr ⟨A0, v0, _v', hget, _, _⟩ => by
              have hg : (some (LocalDecl.assumption A) : Option LocalDecl)
                  = some (.letBinding A0 v0) := hget
              injection hg with hg1
              exact LocalDecl.noConfusion hg1

/-- The two sides of `wall_conv_app_irr` have NO common `⇒*` reduct.
This is the OPTIONAL half of the artifact (00 §20.8 NAMED GAP 3):
`convClassTransfer_false` alone already carries the record, and the
second carrier recorded in the module docstring is the independent
route to the same conclusion. It kills the CLASS-CONDITIONED JOIN with
the same term that kills the class transfer. -/
theorem wall_conv_app_no_join {n : Nat} {w : Level} {c : Expr Nat} :
    ParRedStar wallEnv n [] (.app (.lam wallProp (.bvar 0))
      (.sort w)) c →
    ParRedStar wallEnv n [] (.app (.const 0 []) (.sort w)) c →
    False :=
  fun hleft hright =>
    let ⟨_ls', _x', hshape⟩ := parRedStar_constApp_shape hright rfl
    parRedStar_lamBvar_app_ne_constApp hleft rfl hshape

/-! ## Batch 4 — the Π-endpoint sibling (00 §20.8 NAMED GAP 1)

Authority: Annex 22 UNIT A2. The route is the auxiliary inversion
`hasTyPiInvConv` (A2-1) with its size bound (A2-2). §20.8's second
named route — an O-3 restatement of a landed inversion — is the one
§20.8's own stop rule forbids; `hasTyPiInv` is not restated and
`RcicInvertFamily.lean` is not opened. A2-3 (`hasTyPiInvConv_eq`) is
deleted: the bridge is ill-typed. A2-5 is stated over the auxiliary
so it does not depend on A2-4.

WHAT THIS IS NOT (00 §20.8 S-8). The `irr` arm is NOT closed. No
§19.2 row moves. `closure_claim` stays `0`. The second endpoint
shape's measure obstruction is dissolved — nothing wider. -/

/-- Auxiliary inversion at a pi subject, returning the `Conv` tail
with only the existential levels in the `Σ'`. Nine arms, copied
from `hasTyPiInv`: `.pi` and `.conv` live, seven `nomatch`. The
vacuous form that takes the `Conv` as input is not this statement. -/
def hasTyPiInvConv {E : ResolvedEnv} {n : Nat} {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .pi A B →
    Σ' (u : Level) (v : Level), Conv E n Γ (.sort (.imax u v)) T
  | _, _, _, .pi Γ A' u B' v _hA _hB, heq => by
      injection heq with h1 h2; subst h1; subst h2
      exact ⟨u, v, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨u, v, hcv⟩ := hasTyPiInvConv h heq
      ⟨u, v, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- The `Conv` `hasTyPiInvConv` builds is no larger than the typing
it inverts. `.pi` is `1 ≤ sizeHasTy hA + sizeHasTy hB + 1` (`omega`,
not `Nat.le_refl 1`). `.conv` is the sort sibling's arithmetic. -/
theorem sizeConv_hasTyPiInvConv {E : ResolvedEnv} {n : Nat}
    {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    (h : HasTy E n Γ e T) → (heq : e = .pi A B) →
    sizeConv (hasTyPiInvConv h heq).2.2 ≤ sizeHasTy h
  | _, _, _, .pi _Γ _A' _u _B' _v _hA _hB, heq => by
      injection heq with h1 h2; subst h1; subst h2
      simp only [hasTyPiInvConv, sizeConv, sizeHasTy]
      omega
  | _, _, _, .conv _Γ _e _A0 _B0 h hc, heq => by
      simp only [hasTyPiInvConv, sizeConv, sizeHasTy]
      have ih := sizeConv_hasTyPiInvConv h heq
      exact Nat.add_le_add_right (Nat.add_le_add_right ih _) _
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- The same bound for the call a Π endpoint actually makes, stated
over the auxiliary. Sibling of `sizeConv_irr_sortCut`. The `irr`
arm is NOT closed; this dissolves the measure obstruction at a
second endpoint shape — nothing wider. `P` is kept in `Conv.irr`'s
arguments (the known transcription slip of the sort form). -/
theorem sizeConv_irr_piCut {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {P q : Expr Nat} {A B : Expr Nat}
    (hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ (.pi A B) P) (hq : HasTy E n Γ q P) :
    sizeConv (hasTyPiInvConv hp rfl).2.2 + sizeHasTy hP + 2
      ≤ sizeConv (Conv.irr (E := E) (n := n) Γ P (.pi A B) q hP hp hq) := by
  simp only [sizeConv]
  have hinv := sizeConv_hasTyPiInvConv hp rfl
  have hpos := sizeHasTy_pos hq
  omega

/-- NAMED GAP 1's own statement, attempted DIRECTLY on the landed
inversion. The projection is `.2.2.2.2` (the `Conv` tail of
`hasTyPiInv`'s `Σ'`). If the `.conv` arm walls, GAP 1 stays OPEN. -/
theorem sizeConv_hasTyPiInv {E : ResolvedEnv} {n : Nat}
    {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    (h : HasTy E n Γ e T) → (heq : e = .pi A B) →
    sizeConv (hasTyPiInv h heq).2.2.2.2 ≤ sizeHasTy h
  | _, _, _, .pi _Γ _A' _u _B' _v _hA _hB, heq => by
      injection heq with h1 h2; subst h1; subst h2
      simp only [hasTyPiInv, sizeConv, sizeHasTy]
      omega
  | _, _, _, .conv _Γ _e _A0 _B0 h hc, heq => by
      simp only [hasTyPiInv, sizeConv, sizeHasTy]
      have ih := sizeConv_hasTyPiInv h heq
      exact Nat.add_le_add_right (Nat.add_le_add_right ih _) _
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

end Rcic.Declarative
