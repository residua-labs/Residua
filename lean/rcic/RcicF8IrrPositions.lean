import rcic.RcicF8IrrProducerPins
import rcic.RcicConvProofProducerCerts
import rcic.RcicOccurrenceFrames
import rcic.RcicEtaKDecide
import rcic.RcicA2SortSupport

/-!
# `RcicF8IrrPositions` — the latent `ConvT.irr` positions inside J

J translates a `ConvT` derivation arm by arm; the ONLY source of a
`PEqT.proof` occurrence in J's output is a `ConvT.irr` node. `IrrOcc`
is occurrence evidence for a latent J irr site inside an EXISTING
`ConvT` derivation — not a new relation — and `IrrOcc.site` computes
the site J would emit for it: the host context and index, the irr's
own literal children (`hP`, `hp`, `hq` as `HasTyT` data), and the lazy
`EvTc` chain `host ≡ P` assembled from the spine's literal `tyConv`
children.

## Arm classification (all 18 `ConvT` arms)

| arm | `IrrOcc` ctor(s) | status / site host |
| --- | --- | --- |
| `refl` | — | no occurrence (no `ConvT` child) |
| `symm` | `symm` | spine, index preserved |
| `trans` | `transLeft`, `transRight` | spine, index preserved |
| `beta` | — | no occurrence (`HasTyT` premises only) |
| `zeta` | — | no occurrence |
| `zetaLocal` | — | no occurrence |
| `delta` | — | no occurrence |
| `iota` | — | no occurrence |
| `lit` | — | no occurrence |
| `app` | `appFun` | congruence host `pi A B` |
|       | `appArg` | congruence host `A` |
| `lam` | `lamDom` | sort host `sort u` — refuted under `SortUnique` |
|       | `lamBody` | congruence host `B` under `assumption A :: Γ` |
| `pi`  | `piDom`, `piCod` | sort hosts `sort u`/`sort v` — refuted |
| `letE` | `letEAnn` | sort host `sort u` — refuted |
|        | `letEVal` | congruence host `A` |
|        | `letEBody` | congruence host `B` under `letBinding A v :: Γ` |
| `sorts` | — | no occurrence |
| `consts` | — | no occurrence |
| `eta` | — | no occurrence (`HasTyT` premise only) |
| `irr` | `irr` | root occurrence, host `P` |
| `tyConv` | `tyConv` | spine, index-moving (`A'`) |

An irr inside a `HasTyT.conv` premise stays inside typing; J does not
translate it. The four sort-index congruence arms and a sort-valued
root index carry no valid occurrence under `SortUnique`
(`irrSite_sortHost_false`); `SortUnique` is a NAMED premise of the
refutation theorem, never inside a definition.

`IrrChain` is the snoc-accumulated link list the `site` recursion
carries: `IrrOcc.siteAux` descends with `top` = the index of the
innermost host-level node (the deepest congruence entry's child index,
or the derivation's own index when no congruence is entered) and
appends a `symm (ofCv u (lit hA))` link at every `tyConv` link, so the
materialized chain is the right-associated
`trans (of (symm hc)) …` chain `F8ConvProofProducer.Trace.certificate`
builds — `Trace.toIrrOcc_chain` is an exact term equality, not an
index agreement. At congruence arms the accumulated links and `top`
are discarded: the site is the child's site computed relative to the
child's own context and index.

Every site is ANSWERED at the occurrence's exact request
(`IrrSite.requests`/`frameAnswers`/`rawAnswered`, the B5
`a1SubstStatus` format): both side requests sit at `index := s.host`
with the position typing transported along `s.chain.symmT`, and both
answers are `s.chain` materialized. `IrrOcc.site_strict` shows every
chain leaf and the three typing children are strictly below the input
`cv`, and `IrrOcc.site_edge` is the O-M3(b) edge reading.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Declarative.F8Occurrences
open Rcic.Declarative.F8ConvProofProducer

variable {E : ResolvedEnv} {n : Nat}
variable {R : List (Jd E n)}

/-- the site J emits for an irr node: the host context and index, the
    proposition, the proof terms, the literal typing children, and a
    lazy `EvTc` chain `host ≡ P` assembled from the spine's literal
    `tyConv` children (`refl`/`trans`/`symm`/`ofCv` over `EvCv.lit`
    only). -/
structure IrrSite (R : List (Jd E n)) where
  ctx : LCtx
  host : Expr Nat
  P : Expr Nat
  p : Expr Nat
  q : Expr Nat
  hP : HasTyT E n ctx P (.sort .zero)
  hp : HasTyT E n ctx p P
  hq : HasTyT E n ctx q P
  chain : EvTc R ctx host P

/-- the site's literal leaves: the chain's literal `tyConv` children,
    then the three original typing children of the irr node. -/
def IrrSite.leaves (s : IrrSite R) : List (Jd E n) :=
  s.chain.leaves ++ [.ty s.hP, .ty s.hp, .ty s.hq]

/-- occurrence evidence for a latent J irr site inside an EXISTING
    `ConvT` derivation — not a new relation. One constructor per arm in
    the classification: `irr` (root), `symm`/`transLeft`/`transRight`/
    `tyConv` (spine), `appFun`/`appArg`/`lamBody`/`letEVal`/`letEBody`
    (congruence hosts), and `lamDom`/`piDom`/`piCod`/`letEAnn`
    (sort-index congruence children). The sibling derivations are
    carried as constructor arguments so the parent node is
    reconstructed. -/
inductive IrrOcc : {Γ : LCtx} → {a b T : Expr Nat} →
    ConvT E n Γ a b T → Type where
  | irr {Γ : LCtx} {P p q : Expr Nat}
      {hP : HasTyT E n Γ P (.sort .zero)}
      {hp : HasTyT E n Γ p P} {hq : HasTyT E n Γ q P} :
      IrrOcc (.irr Γ P p q hP hp hq)
  | symm {Γ : LCtx} {a b T : Expr Nat} {h : ConvT E n Γ a b T}
      (o : IrrOcc h) : IrrOcc (.symm Γ a b T h)
  | transLeft {Γ : LCtx} {a b c T : Expr Nat} {h : ConvT E n Γ a b T}
      (k : ConvT E n Γ b c T) (o : IrrOcc h) :
      IrrOcc (.trans Γ a b c T h k)
  | transRight {Γ : LCtx} {a b c T : Expr Nat} (h : ConvT E n Γ a b T)
      {k : ConvT E n Γ b c T} (o : IrrOcc k) :
      IrrOcc (.trans Γ a b c T h k)
  | tyConv {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      {h : ConvT E n Γ a b A} (hA : ConvT E n Γ A A' (.sort u))
      (o : IrrOcc h) : IrrOcc (.tyConv Γ a b A A' u h hA)
  | appFun {Γ : LCtx} {f g a b A B : Expr Nat}
      {h1 : ConvT E n Γ f g (.pi A B)} (h2 : ConvT E n Γ a b A)
      (o : IrrOcc h1) : IrrOcc (.app Γ f g a b A B h1 h2)
  | appArg {Γ : LCtx} {f g a b A B : Expr Nat}
      (h1 : ConvT E n Γ f g (.pi A B)) {h2 : ConvT E n Γ a b A}
      (o : IrrOcc h2) : IrrOcc (.app Γ f g a b A B h1 h2)
  | lamDom {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
      {hA : ConvT E n Γ A A' (.sort u)}
      (hb : ConvT E n (.assumption A :: Γ) b b' B) (o : IrrOcc hA) :
      IrrOcc (.lam Γ A A' b b' B u hA hb)
  | lamBody {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u))
      {hb : ConvT E n (.assumption A :: Γ) b b' B} (o : IrrOcc hb) :
      IrrOcc (.lam Γ A A' b b' B u hA hb)
  | piDom {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      {hA : ConvT E n Γ A A' (.sort u)}
      (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) (o : IrrOcc hA) :
      IrrOcc (.pi Γ A A' B B' u v hA hB)
  | piCod {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      (hA : ConvT E n Γ A A' (.sort u))
      {hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)} (o : IrrOcc hB) :
      IrrOcc (.pi Γ A A' B B' u v hA hB)
  | letEAnn {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      {hA : ConvT E n Γ A A' (.sort u)} (hv : ConvT E n Γ v v' A)
      (hb : ConvT E n (.letBinding A v :: Γ) b b' B) (o : IrrOcc hA) :
      IrrOcc (.letE Γ A A' v v' b b' B u hA hv hb)
  | letEVal {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u)) {hv : ConvT E n Γ v v' A}
      (hb : ConvT E n (.letBinding A v :: Γ) b b' B) (o : IrrOcc hv) :
      IrrOcc (.letE Γ A A' v v' b b' B u hA hv hb)
  | letEBody {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ v v' A)
      {hb : ConvT E n (.letBinding A v :: Γ) b b' B} (o : IrrOcc hb) :
      IrrOcc (.letE Γ A A' v v' b b' B u hA hv hb)

/-- the lazily accumulated spine links of a `site` recursion, in snoc
    order: `nil` is the identity run; `snoc links link` appends one
    `EvTc` link `B ≡ C` to a run `A ≡ B`. `materialize` right-folds the
    run into an `EvTc`, so a run `⟨l₁, l₂, …⟩` reads
    `trans l₁ (trans l₂ …)` — the `Trace.certificate` shape. -/
inductive IrrChain (R : List (Jd E n)) :
    LCtx → Expr Nat → Expr Nat → Type where
  | nil {Γ : LCtx} {T : Expr Nat} : IrrChain R Γ T T
  | snoc {Γ : LCtx} {A B C : Expr Nat} (links : IrrChain R Γ A B)
      (link : EvTc R Γ B C) : IrrChain R Γ A C

def IrrChain.leaves : {Γ : LCtx} → {A B : Expr Nat} →
    IrrChain R Γ A B → List (Jd E n)
  | _, _, _, .nil => []
  | _, _, _, .snoc c l => c.leaves ++ l.leaves

/-- right-fold a link run onto a tail chain. -/
def IrrChain.materialize : {Γ : LCtx} → {A B C : Expr Nat} →
    IrrChain R Γ A B → EvTc R Γ B C → EvTc R Γ A C
  | _, _, _, _, .nil, rest => rest
  | _, _, _, _, .snoc c l, rest => c.materialize (.trans l rest)

/-- the site's stored chain: the run folded onto `refl`. -/
def IrrChain.toEvTc {Γ : LCtx} {A B : Expr Nat} (c : IrrChain R Γ A B) :
    EvTc R Γ A B :=
  c.materialize (.refl Γ B)

theorem IrrChain.materialize_leaves : {Γ : LCtx} → {A B C : Expr Nat} →
    (c : IrrChain R Γ A B) → (rest : EvTc R Γ B C) →
    (c.materialize rest).leaves = c.leaves ++ rest.leaves
  | _, _, _, _, .nil, _ => by
      simp [IrrChain.materialize, IrrChain.leaves]
  | _, _, _, _, .snoc c l, rest => by
      simp only [IrrChain.materialize]
      rw [IrrChain.materialize_leaves c]
      simp [IrrChain.leaves, EvTc.leaves, List.append_assoc]

theorem IrrChain.toEvTc_leaves {Γ : LCtx} {A B : Expr Nat}
    (c : IrrChain R Γ A B) : c.toEvTc.leaves = c.leaves := by
  simp [IrrChain.toEvTc, IrrChain.materialize_leaves, EvTc.leaves]

/-- the materialized fold on the plain `TyConvT` side. -/
def IrrChain.materializeT (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) : {Γ : LCtx} → {A B C : Expr Nat} →
    IrrChain R Γ A B → TyConvT E n Γ B C → TyConvT E n Γ A C
  | _, _, _, _, .nil, rest => rest
  | _, _, _, _, .snoc c l, rest =>
      IrrChain.materializeT hcl hinst c
        (.trans _ _ _ _ (l.val hcl hinst) rest)

theorem IrrChain.materialize_val (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) : {Γ : LCtx} → {A B C : Expr Nat} →
    (c : IrrChain R Γ A B) → (rest : EvTc R Γ B C) →
    (c.materialize rest).val hcl hinst =
      c.materializeT hcl hinst (rest.val hcl hinst)
  | _, _, _, _, .nil, _ => by
      simp [IrrChain.materialize, IrrChain.materializeT]
  | _, _, _, _, .snoc c l, rest => by
      simp only [IrrChain.materialize, IrrChain.materializeT, EvTc.val]
      exact IrrChain.materialize_val hcl hinst c (.trans l rest)

/-- a judgment immediately below `.cv h` stays inside the root bundle:
    `Child` gives `SubOf`, and `subOf_trans_subEq` keeps the `SubEq`
    certificate of `.cv h`. -/
theorem IrrOcc.child_subEq {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} {j : Jd E n}
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) (hc : Child j (.cv h)) :
    ∃ r ∈ R, SubEq j r :=
  hsub.elim fun r hr => ⟨r, hr.1, .inr (subOf_trans_subEq (.child hc) hr.2)⟩

/-- a `Child` of `.cv h` stays strictly below `hTop` through `h`'s own
    `SubEq` certificate — the composition every `siteAux_strict` arm
    needs, with `h` explicit so the child list reduces. -/
theorem IrrOcc.child_subOf {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} {j hTop : Jd E n}
    (hle : SubEq (.cv h) hTop) (hc : Child j (.cv h)) :
    SubOf j hTop :=
  subOf_trans_subEq (.child hc) hle

/-- the site of an occurrence, computed with the accumulated link run:
    `top` is the index of the innermost host-level node — the index of
    the node the occurrence sits at when no congruence has been entered
    since — and `acc` collects the `symm (ofCv (lit hA))` links of the
    `tyConv` spine below it. At `irr` the run becomes the site chain;
    at congruence arms `top`/`acc` are reset to the child's own index
    and `nil` (a new host-level run). -/
def IrrOcc.siteAux : {Δ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Δ a b T} → IrrOcc h → {top : Expr Nat} →
    IrrChain R Δ top T → (∃ r ∈ R, SubEq (.cv h) r) → IrrSite R
  | _, _, _, _, _, .irr (Γ := Γ) (P := P) (p := p) (q := q)
      (hP := hP) (hp := hp) (hq := hq), top, acc, _ =>
      ⟨Γ, top, P, p, q, hP, hp, hq, acc.toEvTc⟩
  | _, _, _, _, _, .symm o, top, acc, hsub =>
      IrrOcc.siteAux o acc (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .transLeft _ o, top, acc, hsub =>
      IrrOcc.siteAux o acc (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .transRight _ o, top, acc, hsub =>
      IrrOcc.siteAux o acc (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .tyConv (u := u) hA o, top, acc, hsub =>
      IrrOcc.siteAux o
        (acc.snoc (.symm (.ofCv u
          (.lit hA (IrrOcc.child_subEq hsub (.tail _ (.head _)))))))
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .appFun _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .appArg _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .lamDom _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .lamBody _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .piDom _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .piCod _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .letEAnn _ _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .letEVal _ _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .letEBody _ _ o, _, _, hsub =>
      IrrOcc.siteAux o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.tail _ (.head _))))

/-- the site of a latent J irr position inside `h`: the host is the
    conclusion index of `h` itself when the occurrence never enters a
    congruence, else the deepest congruence child's index. -/
def IrrOcc.site {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) (o : IrrOcc h) : IrrSite R :=
  IrrOcc.siteAux o .nil hsub

/-- the same index tracking as `siteAux`, returning only the host
    expression. -/
def IrrOcc.hostAux : {Δ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Δ a b T} → IrrOcc h → (top : Expr Nat) → Expr Nat
  | _, _, _, _, _, .irr, top => top
  | _, _, _, _, _, .symm o, top => IrrOcc.hostAux o top
  | _, _, _, _, _, .transLeft _ o, top => IrrOcc.hostAux o top
  | _, _, _, _, _, .transRight _ o, top => IrrOcc.hostAux o top
  | _, _, _, _, _, .tyConv _ o, top => IrrOcc.hostAux o top
  | _, _, _, _, _, .appFun (A := A) (B := B) _ o, _ =>
      IrrOcc.hostAux o (.pi A B)
  | _, _, _, _, _, .appArg (A := A) _ o, _ =>
      IrrOcc.hostAux o A
  | _, _, _, _, _, .lamDom (u := u) _ o, _ =>
      IrrOcc.hostAux o (.sort u)
  | _, _, _, _, _, .lamBody (B := B) _ o, _ =>
      IrrOcc.hostAux o B
  | _, _, _, _, _, .piDom (u := u) _ o, _ =>
      IrrOcc.hostAux o (.sort u)
  | _, _, _, _, _, .piCod (v := v) _ o, _ =>
      IrrOcc.hostAux o (.sort v)
  | _, _, _, _, _, .letEAnn (u := u) _ _ o, _ =>
      IrrOcc.hostAux o (.sort u)
  | _, _, _, _, _, .letEVal (A := A) _ _ o, _ =>
      IrrOcc.hostAux o A
  | _, _, _, _, _, .letEBody (B := B) _ _ o, _ =>
      IrrOcc.hostAux o B

/-- the host expression the site computes for this occurrence. -/
def IrrOcc.hostExpr {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (o : IrrOcc h) : Expr Nat :=
  IrrOcc.hostAux o T

/-- true exactly when the host is literally a sort: the final
    congruence entry was `lamDom`/`piDom`/`piCod`/`letEAnn`, or the
    host-level index (the root index when no congruence was entered)
    is literally a `.sort`. -/
def IrrOcc.hostIsSortArm {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (o : IrrOcc h) : Bool :=
  match o.hostExpr with
  | .sort _ => true
  | _ => false

/-- the occurrence path stays on the spine: no congruence ctor. -/
def IrrOcc.isSpineOnly : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → IrrOcc h → Bool
  | _, _, _, _, _, .irr => true
  | _, _, _, _, _, .symm o => o.isSpineOnly
  | _, _, _, _, _, .transLeft _ o => o.isSpineOnly
  | _, _, _, _, _, .transRight _ o => o.isSpineOnly
  | _, _, _, _, _, .tyConv _ o => o.isSpineOnly
  | _, _, _, _, _, .appFun _ _ => false
  | _, _, _, _, _, .appArg _ _ => false
  | _, _, _, _, _, .lamDom _ _ => false
  | _, _, _, _, _, .lamBody _ _ => false
  | _, _, _, _, _, .piDom _ _ => false
  | _, _, _, _, _, .piCod _ _ => false
  | _, _, _, _, _, .letEAnn _ _ _ => false
  | _, _, _, _, _, .letEVal _ _ _ => false
  | _, _, _, _, _, .letEBody _ _ _ => false

theorem IrrOcc.siteAux_host : {Δ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Δ a b T} → (o : IrrOcc h) → {top : Expr Nat} →
    (acc : IrrChain R Δ top T) → (hsub : ∃ r ∈ R, SubEq (.cv h) r) →
    (IrrOcc.siteAux o acc hsub).host = IrrOcc.hostAux o top
  | _, _, _, _, _, .irr, _, _, _ => rfl
  | _, _, _, _, _, .symm o, top, acc, hsub =>
      IrrOcc.siteAux_host o acc
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .transLeft _ o, top, acc, hsub =>
      IrrOcc.siteAux_host o acc
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .transRight _ o, top, acc, hsub =>
      IrrOcc.siteAux_host o acc
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .tyConv hA o, top, acc, hsub =>
      IrrOcc.siteAux_host o
        (acc.snoc (.symm (.ofCv _
          (.lit hA (IrrOcc.child_subEq hsub (.tail _ (.head _)))))))
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .appFun _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .appArg _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .lamDom _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .lamBody _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .piDom _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .piCod _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .letEAnn _ _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .letEVal _ _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .letEBody _ _ o, _, _, hsub =>
      IrrOcc.siteAux_host o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.tail _ (.head _))))

/-- on a pure-spine occurrence the tracked host never moves. -/
theorem IrrOcc.hostAux_spine : {Δ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Δ a b T} → (o : IrrOcc h) → (top : Expr Nat) →
    o.isSpineOnly = true → IrrOcc.hostAux o top = top
  | _, _, _, _, _, .irr, _, _ => rfl
  | _, _, _, _, _, .symm o, top, hs => IrrOcc.hostAux_spine o top hs
  | _, _, _, _, _, .transLeft _ o, top, hs =>
      IrrOcc.hostAux_spine o top hs
  | _, _, _, _, _, .transRight _ o, top, hs =>
      IrrOcc.hostAux_spine o top hs
  | _, _, _, _, _, .tyConv _ o, top, hs =>
      IrrOcc.hostAux_spine o top hs
  | _, _, _, _, _, .appFun _ _, _, hs => nomatch hs
  | _, _, _, _, _, .appArg _ _, _, hs => nomatch hs
  | _, _, _, _, _, .lamDom _ _, _, hs => nomatch hs
  | _, _, _, _, _, .lamBody _ _, _, hs => nomatch hs
  | _, _, _, _, _, .piDom _ _, _, hs => nomatch hs
  | _, _, _, _, _, .piCod _ _, _, hs => nomatch hs
  | _, _, _, _, _, .letEAnn _ _ _, _, hs => nomatch hs
  | _, _, _, _, _, .letEVal _ _ _, _, hs => nomatch hs
  | _, _, _, _, _, .letEBody _ _ _, _, hs => nomatch hs

/-- every leaf of the site — the accumulated `tyConv` links and the
    three typing children of the irr node — is a strict sub-derivation
    of any `hTop` the current `.cv h` sits under. The top-level reading
    takes `hTop := .cv h` itself; at congruence arms `hTop`/`hle` are
    updated to the child's own `SubEq` under the parent. -/
theorem IrrOcc.siteAux_strict : {Δ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Δ a b T} → (o : IrrOcc h) → {top : Expr Nat} →
    (acc : IrrChain R Δ top T) → (hsub : ∃ r ∈ R, SubEq (.cv h) r) →
    {hTop : Jd E n} → (hle : SubEq (.cv h) hTop) →
    (∀ ℓ ∈ acc.leaves, SubOf ℓ hTop) →
    ∀ ℓ ∈ (IrrOcc.siteAux o acc hsub).leaves, SubOf ℓ hTop
  | _, _, _, _, _, .irr, _, acc, _, _, hle, hacc => fun ℓ hℓ => by
      simp only [IrrOcc.siteAux, IrrSite.leaves,
        IrrChain.toEvTc_leaves] at hℓ
      rcases List.mem_append.mp hℓ with hc | ht
      · exact hacc ℓ hc
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact IrrOcc.child_subOf hle (.head _)
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact IrrOcc.child_subOf hle (.tail _ (.head _))
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact IrrOcc.child_subOf hle
                (.tail _ (.tail _ (.head _)))
            · exact absurd ht (List.not_mem_nil _)
  | _, _, _, _, _, .symm o, top, acc, hsub, _, hle, hacc =>
      IrrOcc.siteAux_strict o acc
        (IrrOcc.child_subEq hsub (.head _))
        (.inr (IrrOcc.child_subOf hle (.head _))) hacc
  | _, _, _, _, _, .transLeft _ o, top, acc, hsub, _, hle, hacc =>
      IrrOcc.siteAux_strict o acc
        (IrrOcc.child_subEq hsub (.head _))
        (.inr (IrrOcc.child_subOf hle (.head _))) hacc
  | _, _, _, _, _, .transRight _ o, top, acc, hsub, _, hle, hacc =>
      IrrOcc.siteAux_strict o acc
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
        (.inr (IrrOcc.child_subOf hle
          (.tail _ (.head _)))) hacc
  | _, _, _, _, _, .tyConv hA o, top, acc, hsub, _, hle, hacc =>
      IrrOcc.siteAux_strict o
        (acc.snoc (.symm (.ofCv _
          (.lit hA (IrrOcc.child_subEq hsub (.tail _ (.head _)))))))
        (IrrOcc.child_subEq hsub (.head _))
        (.inr (IrrOcc.child_subOf hle (.head _)))
        (fun ℓ hℓ => by
          have h' : ℓ ∈ acc.leaves ++ [.cv hA] := by
            simpa only [IrrChain.leaves, EvTc.leaves, EvCv.leaves]
              using hℓ
          rcases List.mem_append.mp h' with ha | hlit
          · exact hacc ℓ ha
          · rcases List.mem_cons.mp hlit with rfl | hnil
            · exact IrrOcc.child_subOf hle
                (.tail _ (.head _))
            · exact absurd hnil (List.not_mem_nil _))
  | _, _, _, _, _, .appFun _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.head _))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.head _))
  | _, _, _, _, _, .appArg _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.tail _ (.head _)))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.tail _ (.head _)))
  | _, _, _, _, _, .lamDom _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.head _))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.head _))
  | _, _, _, _, _, .lamBody _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.tail _ (.head _)))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.tail _ (.head _)))
  | _, _, _, _, _, .piDom _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.head _))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.head _))
  | _, _, _, _, _, .piCod _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.tail _ (.head _)))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.tail _ (.head _)))
  | _, _, _, _, _, .letEAnn _ _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.head _))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.head _))
  | _, _, _, _, _, .letEVal _ _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.tail _ (.head _)))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle (.tail _ (.head _)))
  | _, _, _, _, _, .letEBody _ _ o, _, _, hsub, _, hle, _ =>
      fun ℓ hℓ =>
        .trans
          (IrrOcc.siteAux_strict o .nil
            (IrrOcc.child_subEq hsub (.tail _ (.tail _ (.head _))))
            (.inl rfl)
            (fun _ h => by simp [IrrChain.leaves] at h) ℓ hℓ)
          (IrrOcc.child_subOf hle
            (.tail _ (.tail _ (.head _))))

/-- every site leaf is strictly below the input `cv`. -/
theorem IrrOcc.site_strict {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (o : IrrOcc h)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) :
    ∀ ℓ ∈ (o.site h hsub).leaves, SubOf ℓ (.cv h) :=
  IrrOcc.siteAux_strict o .nil hsub (.inl rfl)
    (fun _ hℓ => by simp [IrrChain.leaves] at hℓ)

/-- the O-M3(b) edge reading: the site's literal leaves are DM-below
    the input `cv`. -/
theorem IrrOcc.site_edge {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (o : IrrOcc h)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) (Z : List (Jd E n)) :
    OM3_edge (.cv h :: Z) ((o.site h hsub).leaves ++ Z) :=
  om3_edge_of_strictLeaves (X := [.cv h]) (List.cons_ne_nil _ _)
    fun ℓ hℓ => ⟨.cv h, .head _, o.site_strict hsub ℓ hℓ⟩

/-! ### answered status at the occurrence's exact request -/

/-- the two side requests at the occurrence's exact raw leaf: both
    sides ask `index := s.host`, with the position typing transported
    from the literal `hp`/`hq` along `s.chain` reversed. -/
def IrrSite.requests (s : IrrSite R) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) :
    F8Occurrences.RawRequests
      (PEqT.proof s.ctx s.p s.q s.P s.P s.hP s.hP s.hp s.hq)
  | _, .left =>
      ⟨s.host, hasTyT_of_tyConvT s.hp (s.chain.val hcl hinst).symmT⟩
  | _, .right =>
      ⟨s.host, hasTyT_of_tyConvT s.hq (s.chain.val hcl hinst).symmT⟩

/-- both sides answer with the site's lazy chain materialized. -/
def IrrSite.frameAnswers (s : IrrSite R) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) :
    F8Occurrences.RawFrameAnswers
      (PEqT.proof s.ctx s.p s.q s.P s.P s.hP s.hP s.hp s.hq)
      (s.requests hcl hinst) :=
  fun
    | .left => s.chain.val hcl hinst
    | .right => s.chain.val hcl hinst

/-- the answered store at the occurrence's exact request, the B5
    `a1SubstStatus` format. -/
def IrrSite.rawAnswered (s : IrrSite R) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) :
    F8Occurrences.RawAnswered
      (PEqT.proof s.ctx s.p s.q s.P s.P s.hP s.hP s.hp s.hq)
      (s.requests hcl hinst) :=
  F8Occurrences.rawAnswers_of_frame _ (s.requests hcl hinst)
    (s.frameAnswers hcl hinst)

/-! ### sort-host refutation (named premise) -/

/-- a sort-valued host carries no valid occurrence under `SortUnique`:
    the chain reads `.sort l ≡ P` while `P : Prop`, which
    `separationAt_of_sortUniq` refutes. The four sort-index congruence
    arms and a sort root are refuted by this theorem applied at the
    computed site — conditional on the named premise, never embedded
    in a definition. -/
theorem irrSite_sortHost_false (s : IrrSite R) (hW : EnvWfT E)
    (hSort : F8A2Support.SortUnique E n) (hΓ : CtxWfT E n s.ctx)
    {l : Level} (hhost : s.host = .sort l) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) : False :=
  F8EtaK.separationAt_of_sortUniq hW (hSort hW) hΓ s.hP
    (hhost ▸ s.chain.val hcl hinst)

/-! ### exhaustiveness over the input derivation

`IrrOcc`/`IrrOcc.site` describe only the positions J translates. The
exhaustiveness statement over the actual INPUT derivation is
`IrrNodeC.classify`: the mutual `IrrNodeC`/`IrrNodeH` enumerate every
`ConvT.irr` node inside a `ConvT`/`HasTyT` derivation — through EVERY
judgment-valued child of EVERY constructor, including `HasTyT` typing
premises and `tyConv`'s index-conversion child `hA` — and `classify`
returns one of three verdicts per node:

- `translated o ag` — an `IrrOcc` with the same `irr` target;
- `inTypingPremise` — the path crosses a `HasTyT`-valued child
  (every `refl`/`beta`/`zeta`/`zetaLocal`/`delta`/`iota`/`lit`/`eta`
  premise, `irr`'s own three typings, and — via `HasTyT.conv`'s `hc`,
  the only `ConvT`-valued child of a `HasTyT` — any `ConvT` nested
  inside a typing);
- `inIndexChain` — the path crosses `ConvT.tyConv`'s index child
  `hA : ConvT Γ A A' (.sort u)`, which J uses as a `TyConvT` index
  chain and does not translate.

`IrrOcc.parentArm`/`IrrOcc_parentArm_mem` below are kept only as the
structural membership fact; they do NOT establish exhaustiveness.

## J-side obligation (cross-reference)

The "no occurrence" reading of `inTypingPremise` nodes — in
particular all irr nodes under `beta`/`zeta`/`zetaLocal`/`delta`/
`iota`/`lit`/`eta`, whose children are typings — and of
`inIndexChain` nodes relies on J not translating typing premises or
the `tyConv` index-conversion child. That is part of J's contract
`JContractWf`, owned by the #6493 (ChatGPT) line: it now EXISTS on
main at 1b1158b7cf — `lean/rcic/RcicF8EvParStar.lean:303`
(`def JContractWf (J : ∀ R : List (Jd E n), JProcWf R) : Prop`,
`JProcWf` at :298, sealed at `RcicFoundationSeal.lean:12790-12791`;
verified by two greps: an identifier grep and `git grep` on
`origin/main`). cc ruled the unconditional J false (#7035,
regressions #7059): J is `JProcWf` (CtxWfT), consistent with the
sort-host refutation above already carrying `CtxWfT`. -/

/-- the `ConvT` arm an `IrrOcc` sits at: exactly the eight arms that can
    carry a translated occurrence. -/
inductive IrrParentArm where
  | irr | symm | trans | tyConv | app | lam | pi | letE
  deriving DecidableEq

def IrrOcc.parentArm {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (o : IrrOcc h) : IrrParentArm :=
  match o with
  | .irr => .irr
  | .symm _ => .symm
  | .transLeft _ _ => .trans
  | .transRight _ _ => .trans
  | .tyConv _ _ => .tyConv
  | .appFun _ _ => .app
  | .appArg _ _ => .app
  | .lamDom _ _ => .lam
  | .lamBody _ _ => .lam
  | .piDom _ _ => .pi
  | .piCod _ _ => .pi
  | .letEAnn _ _ _ => .letE
  | .letEVal _ _ _ => .letE
  | .letEBody _ _ _ => .letE

/-- STRUCTURAL ONLY: each `IrrOcc` constructor sits at one of the
    eight listed arms. This cases on `IrrOcc`, whose constructors were
    already chosen to be those arms — it does NOT establish
    exhaustiveness over `ConvT` input derivations. The real
    exhaustiveness statement is `IrrNodeC.classify`, which covers the
    whole input derivation mutually over `HasTyT`. -/
theorem IrrOcc_parentArm_mem {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (o : IrrOcc h) :
    o.parentArm ∈
      ([.irr, .symm, .trans, .tyConv, .app, .lam, .pi, .letE] :
        List IrrParentArm) := by
  cases o <;> first | decide | simp [IrrOcc.parentArm]

/-- the concrete `ConvT.irr` subderivation a position reaches: the
    host context, the proposition, the proof terms, and the three
    literal typing children. -/
structure IrrTarget (E : ResolvedEnv) (n : Nat) where
  ctx : LCtx
  P : Expr Nat
  p : Expr Nat
  q : Expr Nat
  hP : HasTyT E n ctx P (.sort .zero)
  hp : HasTyT E n ctx p P
  hq : HasTyT E n ctx q P

mutual

/-- an `irr` node somewhere inside the `ConvT` derivation `h`:
    one constructor per `ConvT`-valued AND `HasTyT`-valued child of
    every `ConvT` constructor, plus `here` at `.irr` itself. Unlike
    `IrrOcc`, nothing is omitted — typing premises and `tyConv`'s
    index child are all reachable. -/
inductive IrrNodeC : {Γ : LCtx} → {a b T : Expr Nat} →
    ConvT E n Γ a b T → Type where
  | here {Γ : LCtx} {P p q : Expr Nat}
      {hP : HasTyT E n Γ P (.sort .zero)}
      {hp : HasTyT E n Γ p P} {hq : HasTyT E n Γ q P} :
      IrrNodeC (.irr Γ P p q hP hp hq)
  | irrP {Γ : LCtx} {P p q : Expr Nat}
      {hP : HasTyT E n Γ P (.sort .zero)} {hp : HasTyT E n Γ p P}
      {hq : HasTyT E n Γ q P} (x : IrrNodeH hP) :
      IrrNodeC (.irr Γ P p q hP hp hq)
  | irrL {Γ : LCtx} {P p q : Expr Nat}
      {hP : HasTyT E n Γ P (.sort .zero)} {hp : HasTyT E n Γ p P}
      {hq : HasTyT E n Γ q P} (x : IrrNodeH hp) :
      IrrNodeC (.irr Γ P p q hP hp hq)
  | irrR {Γ : LCtx} {P p q : Expr Nat}
      {hP : HasTyT E n Γ P (.sort .zero)} {hp : HasTyT E n Γ p P}
      {hq : HasTyT E n Γ q P} (x : IrrNodeH hq) :
      IrrNodeC (.irr Γ P p q hP hp hq)
  | reflTy {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A}
      (x : IrrNodeH h) : IrrNodeC (.refl Γ a A h)
  | symm {Γ : LCtx} {a b T : Expr Nat} {h : ConvT E n Γ a b T}
      (x : IrrNodeC h) : IrrNodeC (.symm Γ a b T h)
  | transLeft {Γ : LCtx} {a b c T : Expr Nat}
      {h : ConvT E n Γ a b T} (k : ConvT E n Γ b c T)
      (x : IrrNodeC h) : IrrNodeC (.trans Γ a b c T h k)
  | transRight {Γ : LCtx} {a b c T : Expr Nat}
      (h : ConvT E n Γ a b T) {k : ConvT E n Γ b c T}
      (x : IrrNodeC k) : IrrNodeC (.trans Γ a b c T h k)
  | betaA {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
      {hA : HasTyT E n Γ A (.sort u)}
      {hbody : HasTyT E n (.assumption A :: Γ) body B}
      {harg : HasTyT E n Γ arg A} (x : IrrNodeH hA) :
      IrrNodeC (.beta Γ A body arg B u hA hbody harg)
  | betaBody {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
      {hA : HasTyT E n Γ A (.sort u)}
      {hbody : HasTyT E n (.assumption A :: Γ) body B}
      {harg : HasTyT E n Γ arg A} (x : IrrNodeH hbody) :
      IrrNodeC (.beta Γ A body arg B u hA hbody harg)
  | betaArg {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
      {hA : HasTyT E n Γ A (.sort u)}
      {hbody : HasTyT E n (.assumption A :: Γ) body B}
      {harg : HasTyT E n Γ arg A} (x : IrrNodeH harg) :
      IrrNodeC (.beta Γ A body arg B u hA hbody harg)
  | zetaA {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hv : HasTyT E n Γ value A}
      {hb : HasTyT E n (.letBinding A value :: Γ) body B}
      (x : IrrNodeH hA) :
      IrrNodeC (.zeta Γ A value body B u hA hv hb)
  | zetaV {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hv : HasTyT E n Γ value A}
      {hb : HasTyT E n (.letBinding A value :: Γ) body B}
      (x : IrrNodeH hv) :
      IrrNodeC (.zeta Γ A value body B u hA hv hb)
  | zetaB {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
      {hA : HasTyT E n Γ A (.sort u)} {hv : HasTyT E n Γ value A}
      {hb : HasTyT E n (.letBinding A value :: Γ) body B}
      (x : IrrNodeH hb) :
      IrrNodeC (.zeta Γ A value body B u hA hv hb)
  | zetaLocalV {Γ : LCtx} {i : Nat} {A v : Expr Nat}
      {hval : lookupValue Γ i = some v}
      {hty : lookupType Γ i = some A} {hv : HasTyT E n Γ v A}
      (x : IrrNodeH hv) :
      IrrNodeC (.zetaLocal Γ i A v hval hty hv)
  | deltaB {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {hres : E.members r = some m}
      {hbody : m.body = some b} {htr : transparent m.mclass = true}
      {hlen : ls.length = m.arity} {hwf : levelsBounded n ls = true}
      {hb : HasTyT E n Γ (instantiateLevels ls b)
        (instantiateLevels ls m.mtype)} (x : IrrNodeH hb) :
      IrrNodeC (.delta Γ r ls m b hres hbody htr hlen hwf hb)
  | iotaL {Γ : LCtx} {lhs rhs T : Expr Nat} {h : DerivedIota E lhs rhs}
      {hlhs : HasTyT E n Γ lhs T} {hrhs : HasTyT E n Γ rhs T}
      (x : IrrNodeH hlhs) :
      IrrNodeC (.iota Γ lhs rhs T h hlhs hrhs)
  | iotaR {Γ : LCtx} {lhs rhs T : Expr Nat} {h : DerivedIota E lhs rhs}
      {hlhs : HasTyT E n Γ lhs T} {hrhs : HasTyT E n Γ rhs T}
      (x : IrrNodeH hrhs) :
      IrrNodeC (.iota Γ lhs rhs T h hlhs hrhs)
  | litE {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
      {h : LiteralExpansion t exp} {hexp : HasTyT E n Γ exp T}
      (x : IrrNodeH hexp) :
      IrrNodeC (.lit Γ t exp T h hexp)
  | appFun {Γ : LCtx} {f g a b A B : Expr Nat}
      {h1 : ConvT E n Γ f g (.pi A B)} (h2 : ConvT E n Γ a b A)
      (x : IrrNodeC h1) : IrrNodeC (.app Γ f g a b A B h1 h2)
  | appArg {Γ : LCtx} {f g a b A B : Expr Nat}
      (h1 : ConvT E n Γ f g (.pi A B)) {h2 : ConvT E n Γ a b A}
      (x : IrrNodeC h2) : IrrNodeC (.app Γ f g a b A B h1 h2)
  | lamDom {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
      {hA : ConvT E n Γ A A' (.sort u)}
      (hb : ConvT E n (.assumption A :: Γ) b b' B)
      (x : IrrNodeC hA) :
      IrrNodeC (.lam Γ A A' b b' B u hA hb)
  | lamBody {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u))
      {hb : ConvT E n (.assumption A :: Γ) b b' B}
      (x : IrrNodeC hb) :
      IrrNodeC (.lam Γ A A' b b' B u hA hb)
  | piDom {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      {hA : ConvT E n Γ A A' (.sort u)}
      (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v))
      (x : IrrNodeC hA) :
      IrrNodeC (.pi Γ A A' B B' u v hA hB)
  | piCod {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      (hA : ConvT E n Γ A A' (.sort u))
      {hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)}
      (x : IrrNodeC hB) :
      IrrNodeC (.pi Γ A A' B B' u v hA hB)
  | letEAnn {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      {hA : ConvT E n Γ A A' (.sort u)} (hv : ConvT E n Γ v v' A)
      (hb : ConvT E n (.letBinding A v :: Γ) b b' B)
      (x : IrrNodeC hA) :
      IrrNodeC (.letE Γ A A' v v' b b' B u hA hv hb)
  | letEVal {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u)) {hv : ConvT E n Γ v v' A}
      (hb : ConvT E n (.letBinding A v :: Γ) b b' B)
      (x : IrrNodeC hv) :
      IrrNodeC (.letE Γ A A' v v' b b' B u hA hv hb)
  | letEBody {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ v v' A)
      {hb : ConvT E n (.letBinding A v :: Γ) b b' B}
      (x : IrrNodeC hb) :
      IrrNodeC (.letE Γ A A' v v' b b' B u hA hv hb)
  | etaF {Γ : LCtx} {f A B : Expr Nat}
      {h : HasTyT E n Γ f (.pi A B)} (x : IrrNodeH h) :
      IrrNodeC (.eta Γ f A B h)
  | tyConv {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      {h : ConvT E n Γ a b A} (hA : ConvT E n Γ A A' (.sort u))
      (x : IrrNodeC h) : IrrNodeC (.tyConv Γ a b A A' u h hA)
  | tyConvIdx {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      (h : ConvT E n Γ a b A) {hA : ConvT E n Γ A A' (.sort u)}
      (x : IrrNodeC hA) : IrrNodeC (.tyConv Γ a b A A' u h hA)

/-- an `irr` node somewhere inside a `HasTyT` derivation: one
    constructor per `HasTyT`-valued or `ConvT`-valued child of every
    `HasTyT` constructor. `sort`/`bvar`/`const` have no children;
    `conv`'s `hc` is the only `ConvT`-valued child of any `HasTyT`. -/
inductive IrrNodeH : {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T → Type where
  | piDom {Γ : LCtx} {A : Expr Nat} {u : Level} {B : Expr Nat}
      {v : Level} {hA : HasTyT E n Γ A (.sort u)}
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (x : IrrNodeH hA) : IrrNodeH (.pi Γ A u B v hA hB)
  | piCod {Γ : LCtx} {A : Expr Nat} {u : Level} {B : Expr Nat}
      {v : Level} (hA : HasTyT E n Γ A (.sort u))
      {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
      (x : IrrNodeH hB) : IrrNodeH (.pi Γ A u B v hA hB)
  | lamDom {Γ : LCtx} {A : Expr Nat} {u : Level} {body B : Expr Nat}
      {hA : HasTyT E n Γ A (.sort u)}
      (hbody : HasTyT E n (.assumption A :: Γ) body B)
      (x : IrrNodeH hA) : IrrNodeH (.lam Γ A u body B hA hbody)
  | lamBody {Γ : LCtx} {A : Expr Nat} {u : Level} {body B : Expr Nat}
      (hA : HasTyT E n Γ A (.sort u))
      {hbody : HasTyT E n (.assumption A :: Γ) body B}
      (x : IrrNodeH hbody) : IrrNodeH (.lam Γ A u body B hA hbody)
  | appFun {Γ : LCtx} {f a A B : Expr Nat}
      {hf : HasTyT E n Γ f (.pi A B)} (ha : HasTyT E n Γ a A)
      (x : IrrNodeH hf) : IrrNodeH (.app Γ f a A B hf ha)
  | appArg {Γ : LCtx} {f a A B : Expr Nat}
      (hf : HasTyT E n Γ f (.pi A B)) {ha : HasTyT E n Γ a A}
      (x : IrrNodeH ha) : IrrNodeH (.app Γ f a A B hf ha)
  | letEAnn {Γ : LCtx} {A : Expr Nat} {u : Level} {value B body : Expr Nat}
      {hA : HasTyT E n Γ A (.sort u)} (hv : HasTyT E n Γ value A)
      (hb : HasTyT E n (.letBinding A value :: Γ) body B)
      (x : IrrNodeH hA) :
      IrrNodeH (.letE Γ A u value B body hA hv hb)
  | letEVal {Γ : LCtx} {A : Expr Nat} {u : Level} {value B body : Expr Nat}
      (hA : HasTyT E n Γ A (.sort u)) {hv : HasTyT E n Γ value A}
      (hb : HasTyT E n (.letBinding A value :: Γ) body B)
      (x : IrrNodeH hv) :
      IrrNodeH (.letE Γ A u value B body hA hv hb)
  | letEBody {Γ : LCtx} {A : Expr Nat} {u : Level} {value B body : Expr Nat}
      (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
      {hb : HasTyT E n (.letBinding A value :: Γ) body B}
      (x : IrrNodeH hb) :
      IrrNodeH (.letE Γ A u value B body hA hv hb)
  | litExp {Γ : LCtx} {t : Nat} {T : Expr Nat}
      {hexp : HasTyT E n Γ (natExpand t) T} (x : IrrNodeH hexp) :
      IrrNodeH (.lit Γ t T hexp)
  | convTy {Γ : LCtx} {e A B : Expr Nat} {u : Level}
      {h : HasTyT E n Γ e A} (hc : ConvT E n Γ A B (.sort u))
      (x : IrrNodeH h) : IrrNodeH (.conv Γ e A B u h hc)
  | convIdx {Γ : LCtx} {e A B : Expr Nat} {u : Level}
      (h : HasTyT E n Γ e A) {hc : ConvT E n Γ A B (.sort u)}
      (x : IrrNodeC hc) : IrrNodeH (.conv Γ e A B u h hc)

end

mutual

/-- the `irr` subderivation a `ConvT` occurrence node reaches. -/
def IrrNodeC.target : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → IrrNodeC h → IrrTarget E n
  | _, _, _, _, _, .here (Γ := Γ') (P := P') (p := p') (q := q')
      (hP := hP) (hp := hp) (hq := hq) => ⟨Γ', P', p', q', hP, hp, hq⟩
  | _, _, _, _, _, .irrP x => x.target
  | _, _, _, _, _, .irrL x => x.target
  | _, _, _, _, _, .irrR x => x.target
  | _, _, _, _, _, .reflTy x => x.target
  | _, _, _, _, _, .symm x => x.target
  | _, _, _, _, _, .transLeft _ x => x.target
  | _, _, _, _, _, .transRight _ x => x.target
  | _, _, _, _, _, .betaA x => x.target
  | _, _, _, _, _, .betaBody x => x.target
  | _, _, _, _, _, .betaArg x => x.target
  | _, _, _, _, _, .zetaA x => x.target
  | _, _, _, _, _, .zetaV x => x.target
  | _, _, _, _, _, .zetaB x => x.target
  | _, _, _, _, _, .zetaLocalV x => x.target
  | _, _, _, _, _, .deltaB x => x.target
  | _, _, _, _, _, .iotaL x => x.target
  | _, _, _, _, _, .iotaR x => x.target
  | _, _, _, _, _, .litE x => x.target
  | _, _, _, _, _, .appFun _ x => x.target
  | _, _, _, _, _, .appArg _ x => x.target
  | _, _, _, _, _, .lamDom _ x => x.target
  | _, _, _, _, _, .lamBody _ x => x.target
  | _, _, _, _, _, .piDom _ x => x.target
  | _, _, _, _, _, .piCod _ x => x.target
  | _, _, _, _, _, .letEAnn _ _ x => x.target
  | _, _, _, _, _, .letEVal _ _ x => x.target
  | _, _, _, _, _, .letEBody _ _ x => x.target
  | _, _, _, _, _, .etaF x => x.target
  | _, _, _, _, _, .tyConv _ x => x.target
  | _, _, _, _, _, .tyConvIdx _ x => x.target

/-- the `irr` subderivation a `HasTyT` occurrence node reaches. -/
def IrrNodeH.target : {Γ : LCtx} → {e T : Expr Nat} →
    {d : HasTyT E n Γ e T} → IrrNodeH d → IrrTarget E n
  | _, _, _, _, .piDom _ x => x.target
  | _, _, _, _, .piCod _ x => x.target
  | _, _, _, _, .lamDom _ x => x.target
  | _, _, _, _, .lamBody _ x => x.target
  | _, _, _, _, .appFun _ x => x.target
  | _, _, _, _, .appArg _ x => x.target
  | _, _, _, _, .letEAnn _ _ x => x.target
  | _, _, _, _, .letEVal _ _ x => x.target
  | _, _, _, _, .letEBody _ _ x => x.target
  | _, _, _, _, .litExp x => x.target
  | _, _, _, _, .convTy _ x => x.target
  | _, _, _, _, .convIdx _ x => x.target

end

/-- the `irr` subderivation an `IrrOcc` reaches — the leaf of the
    spine/congruence path. -/
def IrrOcc.target : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → IrrOcc h → IrrTarget E n
  | _, _, _, _, _, .irr (Γ := Γ') (P := P') (p := p') (q := q')
      (hP := hP) (hp := hp) (hq := hq) => ⟨Γ', P', p', q', hP, hp, hq⟩
  | _, _, _, _, _, .symm o => o.target
  | _, _, _, _, _, .transLeft _ o => o.target
  | _, _, _, _, _, .transRight _ o => o.target
  | _, _, _, _, _, .tyConv _ o => o.target
  | _, _, _, _, _, .appFun _ o => o.target
  | _, _, _, _, _, .appArg _ o => o.target
  | _, _, _, _, _, .lamDom _ o => o.target
  | _, _, _, _, _, .lamBody _ o => o.target
  | _, _, _, _, _, .piDom _ o => o.target
  | _, _, _, _, _, .piCod _ o => o.target
  | _, _, _, _, _, .letEAnn _ _ o => o.target
  | _, _, _, _, _, .letEVal _ _ o => o.target
  | _, _, _, _, _, .letEBody _ _ o => o.target

/-- the site's non-chain fields equal a target's — componentwise, with
    `HEq` for the typing children (their types agree only
    propositionally through the context/proposition equalities). -/
structure IrrSiteTarget (s : IrrSite R) (t : IrrTarget E n) : Prop where
  ctx : s.ctx = t.ctx
  P : s.P = t.P
  p : s.p = t.p
  q : s.q = t.q
  hP : HEq s.hP t.hP
  hp : HEq s.hp t.hp
  hq : HEq s.hq t.hq

/-- the site's ctx/P/p/q/hP/hp/hq are the occurrence's own `irr` node's
    — independent of the accumulated spine data and certificates. -/
theorem IrrOcc.siteAux_target : {Δ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Δ a b T} → (o : IrrOcc h) → {top : Expr Nat} →
    (acc : IrrChain R Δ top T) → (hsub : ∃ r ∈ R, SubEq (.cv h) r) →
    IrrSiteTarget (IrrOcc.siteAux o acc hsub) o.target
  | _, _, _, _, _, .irr, _, _, _ => ⟨rfl, rfl, rfl, rfl, .rfl, .rfl, .rfl⟩
  | _, _, _, _, _, .symm o, _, acc, hsub =>
      IrrOcc.siteAux_target o acc (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .transLeft _ o, _, acc, hsub =>
      IrrOcc.siteAux_target o acc (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .transRight _ o, _, acc, hsub =>
      IrrOcc.siteAux_target o acc
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .tyConv hA o, _, acc, hsub =>
      IrrOcc.siteAux_target o
        (acc.snoc (.symm (.ofCv _
          (.lit hA (IrrOcc.child_subEq hsub (.tail _ (.head _)))))))
        (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .appFun _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .appArg _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .lamDom _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .lamBody _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .piDom _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .piCod _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .letEAnn _ _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil (IrrOcc.child_subEq hsub (.head _))
  | _, _, _, _, _, .letEVal _ _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | _, _, _, _, _, .letEBody _ _ o, _, _, hsub =>
      IrrOcc.siteAux_target o .nil
        (IrrOcc.child_subEq hsub (.tail _ (.tail _ (.head _))))

/-- the site's fields are the occurrence's target. -/
theorem IrrOcc.site_target {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (.cv h) r)
    (o : IrrOcc h) : IrrSiteTarget (o.site h hsub) o.target :=
  IrrOcc.siteAux_target o .nil hsub

/-- the path-route of an occurrence node: `translated` while the path
    stays inside J's translated arms, `typing` once it crosses a
    `HasTyT`-valued child, `index` once it crosses `tyConv`'s
    index-conversion child `hA`. -/
inductive IrrRoute where
  | translated | typing | index
  deriving DecidableEq

/-- the route of a `ConvT` occurrence node, independent of
    `classify`: the first non-translated step decides; every
    `HasTyT`-valued child gives `.typing` (so `IrrNodeH` nodes never
    need a route of their own — the recursion stops at the typing
    step), `tyConv`'s `hA` child gives `.index`, each translated
    `ConvT` child passes its own route through, `.here` is
    `.translated`. -/
def IrrNodeC.route : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → IrrNodeC h → IrrRoute
  | _, _, _, _, _, .here => .translated
  | _, _, _, _, _, .irrP _ => .typing
  | _, _, _, _, _, .irrL _ => .typing
  | _, _, _, _, _, .irrR _ => .typing
  | _, _, _, _, _, .reflTy _ => .typing
  | _, _, _, _, _, .symm x => x.route
  | _, _, _, _, _, .transLeft _ x => x.route
  | _, _, _, _, _, .transRight _ x => x.route
  | _, _, _, _, _, .betaA _ => .typing
  | _, _, _, _, _, .betaBody _ => .typing
  | _, _, _, _, _, .betaArg _ => .typing
  | _, _, _, _, _, .zetaA _ => .typing
  | _, _, _, _, _, .zetaV _ => .typing
  | _, _, _, _, _, .zetaB _ => .typing
  | _, _, _, _, _, .zetaLocalV _ => .typing
  | _, _, _, _, _, .deltaB _ => .typing
  | _, _, _, _, _, .iotaL _ => .typing
  | _, _, _, _, _, .iotaR _ => .typing
  | _, _, _, _, _, .litE _ => .typing
  | _, _, _, _, _, .appFun _ x => x.route
  | _, _, _, _, _, .appArg _ x => x.route
  | _, _, _, _, _, .lamDom _ x => x.route
  | _, _, _, _, _, .lamBody _ x => x.route
  | _, _, _, _, _, .piDom _ x => x.route
  | _, _, _, _, _, .piCod _ x => x.route
  | _, _, _, _, _, .letEAnn _ _ x => x.route
  | _, _, _, _, _, .letEVal _ _ x => x.route
  | _, _, _, _, _, .letEBody _ _ x => x.route
  | _, _, _, _, _, .etaF _ => .typing
  | _, _, _, _, _, .tyConv _ x => x.route
  | _, _, _, _, _, .tyConvIdx _ _ => .index

/-- the J-status of one `IrrNodeC` position, by the highest
    discriminating step on the path. `translated` carries the `IrrOcc`
    site whose target is the node's own (`agree` bundles the
    ctx/P/p/q/hP/hp/hq equality); every verdict carries its route
    equation `hr`, so the classification cannot be inhabited by a
    route-free vacuous function. -/
inductive IrrClass : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → IrrNodeC h → Type where
  | translated {Γ : LCtx} {a b T : Expr Nat}
      {h : ConvT E n Γ a b T} {x : IrrNodeC h} (o : IrrOcc h)
      (agree : o.target = x.target)
      (hr : x.route = .translated) : IrrClass x
  | inTypingPremise {Γ : LCtx} {a b T : Expr Nat}
      {h : ConvT E n Γ a b T} {x : IrrNodeC h}
      (hr : x.route = .typing) : IrrClass x
  | inIndexChain {Γ : LCtx} {a b T : Expr Nat}
      {h : ConvT E n Γ a b T} {x : IrrNodeC h}
      (hr : x.route = .index) : IrrClass x

/-- propagate a child classification through a translated `IrrOcc`
    parent arm: `lift` maps the child occurrence to the parent's. -/
def IrrClass.through {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} {x : IrrNodeC h}
    {Γ' : LCtx} {a' b' T' : Expr Nat} {h' : ConvT E n Γ' a' b' T'}
    {x' : IrrNodeC h'} (lift : IrrOcc h' → IrrOcc h)
    (hlift : ∀ o : IrrOcc h', (lift o).target = o.target)
    (hx : x.target = x'.target) (hxr : x.route = x'.route) :
    IrrClass x' → IrrClass x
  | .translated o ag hr =>
      .translated (lift o) ((hlift o).trans (ag.trans hx.symm))
        (hxr.trans hr)
  | .inTypingPremise hr => .inTypingPremise (hxr.trans hr)
  | .inIndexChain hr => .inIndexChain (hxr.trans hr)

/-- which verdict a classification carries — equal to the node's
    route (`IrrNodeC.classify_route`). -/
def IrrClass.route {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} {x : IrrNodeC h} :
    IrrClass x → IrrRoute
  | .translated _ _ _ => .translated
  | .inTypingPremise _ => .typing
  | .inIndexChain _ => .index

/-- EXHAUSTIVENESS over the input derivation: every `irr` node inside
    `h` — through every `ConvT` and `HasTyT` judgment child —
    classifies as `translated`, `inTypingPremise`, or `inIndexChain`.
    The theorem is the definition itself: total by construction over
    the full tree. -/
def IrrNodeC.classify : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → (x : IrrNodeC h) → IrrClass x
  | _, _, _, _, _, .here => .translated .irr rfl rfl
  | _, _, _, _, _, .irrP _ => .inTypingPremise rfl
  | _, _, _, _, _, .irrL _ => .inTypingPremise rfl
  | _, _, _, _, _, .irrR _ => .inTypingPremise rfl
  | _, _, _, _, _, .reflTy _ => .inTypingPremise rfl
  | _, _, _, _, _, .symm x =>
      x.classify.through .symm (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .transLeft k x =>
      x.classify.through (.transLeft k) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .transRight h x =>
      x.classify.through (.transRight h) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .betaA _ => .inTypingPremise rfl
  | _, _, _, _, _, .betaBody _ => .inTypingPremise rfl
  | _, _, _, _, _, .betaArg _ => .inTypingPremise rfl
  | _, _, _, _, _, .zetaA _ => .inTypingPremise rfl
  | _, _, _, _, _, .zetaV _ => .inTypingPremise rfl
  | _, _, _, _, _, .zetaB _ => .inTypingPremise rfl
  | _, _, _, _, _, .zetaLocalV _ => .inTypingPremise rfl
  | _, _, _, _, _, .deltaB _ => .inTypingPremise rfl
  | _, _, _, _, _, .iotaL _ => .inTypingPremise rfl
  | _, _, _, _, _, .iotaR _ => .inTypingPremise rfl
  | _, _, _, _, _, .litE _ => .inTypingPremise rfl
  | _, _, _, _, _, .appFun h2 x =>
      x.classify.through (.appFun h2) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .appArg h1 x =>
      x.classify.through (.appArg h1) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .lamDom hb x =>
      x.classify.through (.lamDom hb) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .lamBody hA x =>
      x.classify.through (.lamBody hA) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .piDom hB x =>
      x.classify.through (.piDom hB) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .piCod hA x =>
      x.classify.through (.piCod hA) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .letEAnn hv hb x =>
      x.classify.through (.letEAnn hv hb) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .letEVal hA hb x =>
      x.classify.through (.letEVal hA hb) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .letEBody hA hv x =>
      x.classify.through (.letEBody hA hv) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .etaF _ => .inTypingPremise rfl
  | _, _, _, _, _, .tyConv hA x =>
      x.classify.through (.tyConv hA) (fun _ => rfl) rfl rfl
  | _, _, _, _, _, .tyConvIdx _ _ => .inIndexChain rfl

/-- a `.translated` route always carries its site — the classification
    cannot claim `translated` without the `IrrOcc`. -/
def IrrNodeC.route_translated_has_site {Γ : LCtx}
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (x : IrrNodeC h)
    (hr : x.route = .translated) :
    Σ' o : IrrOcc h, o.target = x.target :=
  match x.classify with
  | .translated o ag _ => ⟨o, ag⟩
  | .inTypingPremise hrt =>
      IrrRoute.noConfusion (hr.symm.trans hrt)
  | .inIndexChain hri =>
      IrrRoute.noConfusion (hr.symm.trans hri)

/-- the classification's verdict is the node's route — `classify`
    agrees with `route` on every node. -/
theorem IrrNodeC.classify_route {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (x : IrrNodeC h) :
    x.classify.route = x.route :=
  match x.classify with
  | .translated _ _ hr => hr.symm
  | .inTypingPremise hr => hr.symm
  | .inIndexChain hr => hr.symm

/-- the site a `translated` classification names really is at `x`'s
    target: the site's ctx/P/p/q/hP/hp/hq equal the node's `irr`
    fields. -/
theorem IrrNodeC.classify_translated_site {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (x : IrrNodeC h)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) {o : IrrOcc h}
    {ag : o.target = x.target} {hr : x.route = .translated}
    (_hc : x.classify = .translated o ag hr) :
    IrrSiteTarget (o.site h hsub) x.target :=
  ag ▸ IrrOcc.site_target h hsub o

/-- the request and answered status a `translated` classification
    produces — the site's own `requests`/`rawAnswered`, already built.
    `none` for the non-translated verdicts: their non-occurrence is
    the J-side obligation, not answerable here. -/
def IrrClass.requestsAnswered {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (hsub : ∃ r ∈ R, SubEq (.cv h) r)
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {x : IrrNodeC h} : IrrClass x → Option (Σ' s : IrrSite R,
      (req : F8Occurrences.RawRequests
        (PEqT.proof s.ctx s.p s.q s.P s.P s.hP s.hP s.hp s.hq)) ×'
      F8Occurrences.RawAnswered
        (PEqT.proof s.ctx s.p s.q s.P s.P s.hP s.hP s.hp s.hq) req)
  | .translated o _ _ =>
      some ⟨o.site h hsub, (o.site h hsub).requests hcl hinst,
        (o.site h hsub).rawAnswered hcl hinst⟩
  | .inTypingPremise _ => none
  | .inIndexChain _ => none

/-- for `translated o`, the request and answer at the occurrence are
    exactly `(o.site h hsub).requests`/`.rawAnswered` — the ones
    already built — bundled with the site itself. -/
theorem IrrNodeC.classify_translated_requests {Γ : LCtx}
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (x : IrrNodeC h)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {o : IrrOcc h}
    {ag : o.target = x.target} {hr : x.route = .translated}
    (hc : x.classify = .translated o ag hr) :
    IrrClass.requestsAnswered hsub hcl hinst x.classify =
      some ⟨o.site h hsub, (o.site h hsub).requests hcl hinst,
        (o.site h hsub).rawAnswered hcl hinst⟩ := by
  rw [hc]
  simp only [IrrClass.requestsAnswered]

/-! ### link to the landed producers -/

section LiteralIrrLink
variable {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q P)

/-- the landed `literalIrrProducer` is the `irr` root: its `IrrSite`
    host is `P`. -/
theorem irrSite_literalIrr_host
    (hsub : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) :
    (IrrOcc.site (.irr Γ P p q hP hp hq) hsub .irr).host = P := rfl

/-- its lazy chain is reflexivity, exactly the payload's lazy answer. -/
theorem irrSite_literalIrr_chain
    (hsub : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) :
    (IrrOcc.site (.irr Γ P p q hP hp hq) hsub .irr).chain =
      EvTc.refl Γ P := by
  simp [IrrOcc.site, IrrOcc.siteAux, IrrChain.toEvTc,
    IrrChain.materialize]

/-- the site's request at each side coincides with the payload's. -/
theorem irrSite_literalIrr_requests (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E)
    (hsub : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) (side : Side) :
    HEq ((IrrOcc.site (.irr Γ P p q hP hp hq) hsub .irr).requests
          hcl hinst PUnit.unit side)
      (EvPar.proofIndexRequests hcl hinst (literalIrrPayload hP hp hq)
        PUnit.unit side) := by
  cases side <;> simp [IrrOcc.site, IrrOcc.siteAux,
    IrrSite.requests, IrrChain.toEvTc, IrrChain.materialize,
    EvTc.val, EvTy.val, TyConvT.symmT, hasTyT_of_tyConvT,
    EvPar.proofIndexRequests, ProofIndexPayload.requests,
    F8Occurrences.rootRequests, literalIrrPayload, EvPar.val,
    peqLeafT_reconcile_propIndex, F8Occurrences.site,
    F8Occurrences.rawSite]

/-- the site's answer at each side coincides with the payload's. -/
theorem irrSite_literalIrr_answers (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E)
    (hsub : ∃ r ∈ R, SubEq (.cv (.irr Γ P p q hP hp hq)) r) (side : Side) :
    HEq ((IrrOcc.site (.irr Γ P p q hP hp hq) hsub .irr).rawAnswered
          hcl hinst PUnit.unit side)
      (EvPar.proofIndexAnswers hcl hinst (literalIrrPayload hP hp hq)
        PUnit.unit side) := by
  cases side <;> simp [IrrOcc.site, IrrOcc.siteAux,
    IrrSite.rawAnswered, IrrSite.requests, IrrSite.frameAnswers,
    F8Occurrences.rawAnswers_of_frame, IrrChain.toEvTc,
    IrrChain.materialize, EvTc.val, EvTy.val, TyConvT.symmT,
    hasTyT_of_tyConvT, EvPar.proofIndexAnswers,
    ProofIndexPayload.answers, F8Occurrences.rootAnswers,
    literalIrrPayload, EvPar.val, peqLeafT_reconcile_propIndex,
    F8Occurrences.site, F8Occurrences.rawSite]

end LiteralIrrLink

/-! ### the `F8ConvProofProducer.Trace` spine embeds -/

end Rcic.Declarative.F8Measure

namespace Rcic.Declarative.F8ConvProofProducer
open Rcic.Declarative.F8Measure
open Rcic.Declarative.F8Occurrences

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- a `Trace` is exactly the pure-spine subset of `IrrOcc`, by
    structural recursion on the trace. -/
def Trace.toIrrOcc {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} : Trace h → IrrOcc h
  | .irr _ _ _ => .irr
  | .symm ht => .symm (Trace.toIrrOcc ht)
  | .transLeft k ht => .transLeft k (Trace.toIrrOcc ht)
  | .transRight h ht => .transRight h (Trace.toIrrOcc ht)
  | .tyConv hc ht => .tyConv hc (Trace.toIrrOcc ht)

theorem Trace.toIrrOcc_spine {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} :
    (ht : Trace h) → ht.toIrrOcc.isSpineOnly = true
  | .irr _ _ _ => rfl
  | .symm ht => ht.toIrrOcc_spine
  | .transLeft _ ht => ht.toIrrOcc_spine
  | .transRight _ ht => ht.toIrrOcc_spine
  | .tyConv _ ht => ht.toIrrOcc_spine

/-- a `Trace` site hosts at the conversion's own index `T`. -/
theorem Trace.toIrrOcc_host {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (ht : Trace h)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) :
    (ht.toIrrOcc.site h hsub).host = T := by
  show (IrrOcc.siteAux ht.toIrrOcc .nil hsub).host = T
  rw [IrrOcc.siteAux_host ht.toIrrOcc .nil hsub]
  exact IrrOcc.hostAux_spine _ _ ht.toIrrOcc_spine

/-- a `Trace` site lives in the conversion's own context — the same
    index the certificate lives at. -/
theorem Trace.toIrrOcc_ctx : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → (ht : Trace h) → {top : Expr Nat} →
    (acc : IrrChain R Γ top T) → (hsub : ∃ r ∈ R, SubEq (.cv h) r) →
    (IrrOcc.siteAux ht.toIrrOcc acc hsub).ctx = Γ := by
  intro Γ a b T h ht top acc hsub
  revert top acc hsub
  induction ht with
  | irr hP hp hq =>
      intro top acc hsub
      simp [Trace.toIrrOcc, IrrOcc.siteAux]
  | symm ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.head _))
  | transLeft _ ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.head _))
  | transRight _ ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | tyConv _ ht ih =>
      intro top acc hsub
      exact ih _ (IrrOcc.child_subEq hsub (.head _))

/-- a `Trace` site's proposition is the certificate's proposition. -/
theorem Trace.toIrrOcc_P : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → (ht : Trace h) → {top : Expr Nat} →
    (acc : IrrChain R Γ top T) → (hsub : ∃ r ∈ R, SubEq (.cv h) r) →
    (IrrOcc.siteAux ht.toIrrOcc acc hsub).P =
      ht.certificate.proposition := by
  intro Γ a b T h ht top acc hsub
  revert top acc hsub
  induction ht with
  | irr hP hp hq =>
      intro top acc hsub
      simp [Trace.toIrrOcc, IrrOcc.siteAux, Trace.certificate]
  | symm ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.head _))
  | transLeft _ ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.head _))
  | transRight _ ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | tyConv _ ht ih =>
      intro top acc hsub
      exact ih _ (IrrOcc.child_subEq hsub (.head _))

/-- the materialized site chain equals the trace certificate chain —
    by structural recursion on the trace. Stated as `HEq` because the
    site's `ctx`/`host`/`P` fields are only propositionally the
    certificate's indices (`toIrrOcc_ctx`/`toIrrOcc_host`/`toIrrOcc_P`). -/
theorem Trace.toIrrOcc_chain_aux (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → {h : ConvT E n Γ a b T} →
    (ht : Trace h) → {top : Expr Nat} →
    (acc : IrrChain R Γ top T) → (hsub : ∃ r ∈ R, SubEq (.cv h) r) →
    HEq ((IrrOcc.siteAux ht.toIrrOcc acc hsub).chain.val hcl hinst)
        (acc.materializeT hcl hinst ht.certificate.chain) := by
  intro Γ a b T h ht top acc hsub
  revert top acc hsub
  induction ht with
  | irr hP hp hq =>
      intro top acc hsub
      simp [Trace.toIrrOcc, IrrOcc.siteAux, IrrChain.toEvTc,
        IrrChain.materialize_val, EvTc.val, Trace.certificate]
  | symm ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.head _))
  | transLeft _ ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.head _))
  | transRight _ ht ih =>
      intro top acc hsub
      exact ih acc (IrrOcc.child_subEq hsub (.tail _ (.head _)))
  | tyConv hc ht ih =>
      intro top acc hsub
      simp only [Trace.toIrrOcc, IrrOcc.siteAux, Trace.certificate,
        IrrChain.materializeT, EvTc.val, EvCv.val, TyConvT.symmT]
      have hih := ih
        (acc.snoc (.symm (.ofCv _
          (.lit hc (IrrOcc.child_subEq hsub (.tail _ (.head _)))))))
        (IrrOcc.child_subEq hsub (.head _))
      simpa only [IrrChain.materializeT, EvTc.val, EvCv.val,
        TyConvT.symmT] using hih

/-- the materialized site chain matches the trace certificate chain.
    Stated as `HEq` because the site's indices are only
    propositionally the certificate's indices (`toIrrOcc_ctx`,
    `toIrrOcc_host`, `toIrrOcc_P`); the inductive form is
    `toIrrOcc_chain_aux`. -/
theorem Trace.toIrrOcc_chain (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (ht : Trace h)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) :
    HEq ((ht.toIrrOcc.site h hsub).chain.val hcl hinst)
        ht.certificate.chain := by
  simpa [IrrOcc.site, IrrChain.materializeT] using
    Trace.toIrrOcc_chain_aux hcl hinst ht .nil hsub

end Rcic.Declarative.F8ConvProofProducer

namespace Rcic.Declarative.F8Measure
open Rcic.Declarative.F8Occurrences
open Rcic.Declarative.F8ConvProofProducer
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### pins -/

section IrrPosPins
open Rcic.Declarative.PEqTProofFront

private def pinClosed : EnvClosed emptyEnv :=
  fun _ _ h => Option.noConfusion h
private def pinSubstStable : EnvMembersSubstStable emptyEnv :=
  fun _ _ h => Option.noConfusion h

/-- the literal `irr` at the shared PEqTProofFront fixture. -/
private def pinIrrCv : ConvT emptyEnv 0 [] p q P :=
  .irr [] P p q (P_ty []) (p_ty []) (q_ty [])

/-- a nontrivial index step over the proposition: `P ≡ P` at `sort 0`. -/
private def pinIdxCv : ConvT emptyEnv 0 [] P P (.sort .zero) :=
  .refl [] P (.sort .zero) (P_ty [])

/-- the argument conversion carries the irr through a `tyConv` index
    step, so the site's chain is a real `trans`, not bare `refl`. -/
private def pinArgCv : ConvT emptyEnv 0 [] p q P :=
  .tyConv [] p q P P .zero pinIrrCv pinIdxCv

/-- `idP ≡ idP` at `pi P P`. -/
private def pinFunCv : ConvT emptyEnv 0 [] idP idP (.pi P P) :=
  .refl [] idP (.pi P P) (idP_ty [])

/-- a real `app` congruence whose argument conversion is a literal
    `irr` under one `tyConv`: `(idP p) ≡ (idP q)` at `P`. -/
def pinOccCv : ConvT emptyEnv 0 [] (.app idP p) (.app idP q) P :=
  .app [] idP idP p q P P pinFunCv pinArgCv

/-- its `appArg` occurrence. -/
def pinOcc : IrrOcc pinOccCv :=
  .appArg pinFunCv (.tyConv pinIdxCv .irr)

private def pinRoot : Jd emptyEnv 0 := .cv pinOccCv
private def pinR : List (Jd emptyEnv 0) := [pinRoot]
private def pinSub : ∃ r ∈ pinR, SubEq (.cv pinOccCv) r :=
  ⟨pinRoot, .head _, .inl rfl⟩

/-- the site of the `appArg` occurrence. -/
def pinSite : IrrSite pinR := IrrOcc.site pinOccCv pinSub pinOcc

/-- the host is the argument's own index `A` — here literally `P`. -/
theorem pin_appArg_host : pinSite.host = P := rfl
/-- the context is the app's context. -/
theorem pin_appArg_ctx : pinSite.ctx = [] := rfl
/-- the site chain is nontrivial: it carries the `tyConv` leaf. -/
theorem pin_appArg_chain_leaves :
    pinSite.chain.leaves = [.cv pinIdxCv] := by
  simp [pinSite, IrrOcc.site, IrrOcc.siteAux, pinOcc, pinOccCv,
    pinArgCv, pinIrrCv, pinIdxCv, IrrChain.toEvTc,
    IrrChain.materialize, IrrChain.leaves, EvTc.leaves, EvCv.leaves]
/-- both side requests sit at the host index. -/
theorem pin_appArg_request_index (side : Side) :
    ((pinSite.requests pinClosed pinSubstStable) PUnit.unit side).index =
      P := by
  cases side <;> rfl
/-- the left side is answered by the site chain materialized. -/
theorem pin_appArg_answer_left :
    pinSite.rawAnswered pinClosed pinSubstStable PUnit.unit .left =
      pinSite.chain.val pinClosed pinSubstStable := rfl
/-- the right side is answered by the site chain materialized. -/
theorem pin_appArg_answer_right :
    pinSite.rawAnswered pinClosed pinSubstStable PUnit.unit .right =
      pinSite.chain.val pinClosed pinSubstStable := rfl
/-- every site leaf is strictly below the app's `cv`. -/
theorem pin_appArg_strict :
    ∀ ℓ ∈ pinSite.leaves, SubOf ℓ (.cv pinOccCv) :=
  IrrOcc.site_strict pinOcc pinSub
/-- `site_edge` instantiated at the pin. -/
theorem pin_appArg_edge :
    OM3_edge ([.cv pinOccCv] ++ []) (pinSite.leaves ++ []) :=
  IrrOcc.site_edge pinOcc pinSub []

/-- a `lam`-body position: `lam P p ≡ lam P q` at `pi P P`, the `irr`
    itself sitting under the binder in the body arm. -/
private def pinLamIrrCv :
    ConvT emptyEnv 0 (.assumption P :: []) p q P :=
  .irr _ P p q (P_ty _) (p_ty _) (q_ty _)
private def pinLamDomCv : ConvT emptyEnv 0 [] P P (.sort .zero) :=
  pinIdxCv
/-- `lam P p ≡ lam P q` — the binder is real, the `irr` is in the body
    conversion. -/
def pinLamCv :
    ConvT emptyEnv 0 [] (.lam P p) (.lam P q) (.pi P P) :=
  .lam [] P P p q P .zero pinLamDomCv pinLamIrrCv
/-- the `lamBody` occurrence. -/
def pinLamOcc : IrrOcc pinLamCv := .lamBody pinLamDomCv .irr
/-- the same position as an input-derivation node. -/
def pinLamNode : IrrNodeC pinLamCv := .lamBody pinLamDomCv .here
private def pinLamRoot : Jd emptyEnv 0 := .cv pinLamCv
private def pinLamSub : ∃ r ∈ [pinLamRoot], SubEq (.cv pinLamCv) r :=
  ⟨pinLamRoot, .head _, .inl rfl⟩

/-- the `lamBody` node classifies as a `translated` occurrence —
    literally `.lamBody … .irr`. -/
theorem pin_lamBody_classify :
    ∃ (ag : pinLamOcc.target = pinLamNode.target)
      (hr : pinLamNode.route = .translated),
      pinLamNode.classify = .translated pinLamOcc ag hr := ⟨_, _, rfl⟩
/-- the `lamBody` node's route is `translated`. -/
theorem pin_lamBody_route : pinLamNode.route = .translated := rfl
/-- the `lamBody` site's host is the body's own index `P`. -/
theorem pin_lamBody_host :
    (pinLamOcc.site pinLamCv pinLamSub).host = P := rfl
/-- `site_edge` instantiated at the `lamBody` pin. -/
theorem pin_lamBody_edge :
    OM3_edge ([.cv pinLamCv] ++ [])
      ((pinLamOcc.site pinLamCv pinLamSub).leaves ++ []) :=
  IrrOcc.site_edge pinLamOcc pinLamSub []

/-- the sort-codomain function `λ _ : P. sort 0 : pi P (sort 1)` —
    the carrier under which a sort-indexed conversion can hold an
    `irr` (its `app` argument conversion's index is free). -/
private def pinIdxF : Expr Nat := .lam P (.sort .zero)
private def pinIdxF_ty :
    HasTyT emptyEnv 0 [] pinIdxF (.pi P (.sort (.succ .zero))) :=
  .lam [] P .zero (.sort .zero) (.sort (.succ .zero)) (P_ty [])
    (.sort (.assumption P :: []) .zero)
/-- `app f p ≡ sort 0` at `sort 1`, by `beta`. -/
private def pinIdxBeta :
    ConvT emptyEnv 0 [] (.app pinIdxF p) (.sort .zero)
      (.sort (.succ .zero)) :=
  .beta [] P (.sort .zero) p (.sort (.succ .zero)) .zero (P_ty [])
    (.sort (.assumption P :: []) .zero) (p_ty [])
/-- `P : app f p` — `app f p` is a sort-1 type (beta-equal to
    `sort 0`). -/
private def pinIdxP_ty : HasTyT emptyEnv 0 [] P (.app pinIdxF p) :=
  .conv [] P (.sort .zero) (.app pinIdxF p) (.succ .zero) (P_ty [])
    (.symm _ _ _ _ pinIdxBeta)
/-- the outer `tyConv`'s main child: `P ≡ P` at index `app f p`. -/
private def pinIdxMainCv :
    ConvT emptyEnv 0 [] P P (.app pinIdxF p) :=
  .refl [] P _ pinIdxP_ty
/-- the index child `app f p ≡ app f q` at `sort 1` — it contains the
    literal `irr` as its argument conversion (`appArg`). -/
private def pinIdxChainCv :
    ConvT emptyEnv 0 [] (.app pinIdxF p) (.app pinIdxF q)
      (.sort (.succ .zero)) :=
  .app [] pinIdxF pinIdxF p q P (.sort (.succ .zero))
    (.refl [] pinIdxF _ pinIdxF_ty) pinIrrCv
/-- `P ≡ P` at `app f q`, the outer `tyConv` whose index child `hA`
    carries an `irr`. -/
def pinIdxOuterCv : ConvT emptyEnv 0 [] P P (.app pinIdxF q) :=
  .tyConv [] P P (.app pinIdxF p) (.app pinIdxF q) (.succ .zero)
    pinIdxMainCv pinIdxChainCv
/-- the `inIndexChain` position: the path crosses `tyConv`'s index
    child `hA`, then `appArg` reaches the `irr`. -/
def pinIdxChainNode : IrrNodeC pinIdxOuterCv :=
  .tyConvIdx pinIdxMainCv (.appArg _ .here)
/-- an `irr` inside `tyConv`'s index-conversion child is
    `inIndexChain`, not a translated site — J uses `hA` as a `TyConvT`
    index chain and does not translate it. -/
theorem pin_inIndexChain :
    ∃ hr : pinIdxChainNode.route = .index,
      pinIdxChainNode.classify = .inIndexChain hr := ⟨_, rfl⟩
/-- the index-chain node's route is `index`. -/
theorem pin_inIndexChain_route : pinIdxChainNode.route = .index := rfl
/-- the node still reaches the literal `irr` target. -/
theorem pin_inIndexChain_target :
    pinIdxChainNode.target =
      ⟨[], P, p, q, P_ty [], p_ty [], q_ty []⟩ := rfl

/-- `sort 0 ≡ app f q` at `sort 1`, with the `irr` under `appArg` on
    the right leg — the `hc` of the `conv` below. -/
private def pinTpHc :
    ConvT emptyEnv 0 [] (.sort .zero) (.app pinIdxF q)
      (.sort (.succ .zero)) :=
  .trans _ _ _ _ _ (.symm _ _ _ _ pinIdxBeta) pinIdxChainCv
/-- `P : app f q` — a typing whose `conv` child `hc` carries an
    `irr`. -/
private def pinTpTy : HasTyT emptyEnv 0 [] P (.app pinIdxF q) :=
  .conv [] P (.sort .zero) (.app pinIdxF q) (.succ .zero) (P_ty [])
    pinTpHc
/-- `refl` at the typing premise: `P ≡ P` at `app f q`. -/
def pinTpCv : ConvT emptyEnv 0 [] P P (.app pinIdxF q) :=
  .refl [] P _ pinTpTy
/-- the `inTypingPremise` position: `refl`'s typing child `h`, then
    `HasTyT.conv`'s `hc`, then `trans`/`appArg` down to the `irr`. -/
def pinTpNode : IrrNodeC pinTpCv :=
  .reflTy (.convIdx (P_ty []) (.transRight _ (.appArg _ .here)))
/-- an `irr` under a `HasTyT` premise is `inTypingPremise` — J does
    not translate typing premises. -/
theorem pin_inTypingPremise :
    ∃ hr : pinTpNode.route = .typing,
      pinTpNode.classify = .inTypingPremise hr := ⟨_, rfl⟩
/-- the typing-premise node's route is `typing`. -/
theorem pin_inTypingPremise_route : pinTpNode.route = .typing := rfl
/-- the node still reaches the literal `irr` target. -/
theorem pin_inTypingPremise_target :
    pinTpNode.target =
      ⟨[], P, p, q, P_ty [], p_ty [], q_ty []⟩ := rfl

end IrrPosPins

#print axioms IrrSite
#print axioms IrrSite.leaves
#print axioms IrrSite.requests
#print axioms IrrSite.frameAnswers
#print axioms IrrSite.rawAnswered
#print axioms IrrChain
#print axioms IrrChain.leaves
#print axioms IrrChain.materialize
#print axioms IrrChain.toEvTc
#print axioms IrrChain.materialize_leaves
#print axioms IrrChain.toEvTc_leaves
#print axioms IrrChain.materializeT
#print axioms IrrChain.materialize_val
#print axioms IrrOcc
#print axioms IrrOcc.child_subEq
#print axioms IrrOcc.child_subOf
#print axioms IrrOcc.siteAux
#print axioms IrrOcc.site
#print axioms IrrOcc.hostAux
#print axioms IrrOcc.hostExpr
#print axioms IrrOcc.hostIsSortArm
#print axioms IrrOcc.isSpineOnly
#print axioms IrrOcc.siteAux_host
#print axioms IrrOcc.hostAux_spine
#print axioms IrrOcc.siteAux_strict
#print axioms IrrOcc.site_strict
#print axioms IrrOcc.site_edge
#print axioms irrSite_sortHost_false
#print axioms IrrParentArm
#print axioms IrrOcc.parentArm
#print axioms IrrOcc_parentArm_mem
#print axioms IrrTarget
#print axioms IrrNodeC
#print axioms IrrNodeH
#print axioms IrrNodeC.target
#print axioms IrrNodeH.target
#print axioms IrrOcc.target
#print axioms IrrSiteTarget
#print axioms IrrOcc.siteAux_target
#print axioms IrrOcc.site_target
#print axioms IrrRoute
#print axioms IrrNodeC.route
#print axioms IrrClass
#print axioms IrrClass.through
#print axioms IrrClass.route
#print axioms IrrClass.requestsAnswered
#print axioms IrrNodeC.classify
#print axioms IrrNodeC.route_translated_has_site
#print axioms IrrNodeC.classify_route
#print axioms IrrNodeC.classify_translated_site
#print axioms IrrNodeC.classify_translated_requests
#print axioms irrSite_literalIrr_host
#print axioms irrSite_literalIrr_chain
#print axioms irrSite_literalIrr_requests
#print axioms irrSite_literalIrr_answers
#print axioms F8ConvProofProducer.Trace.toIrrOcc
#print axioms F8ConvProofProducer.Trace.toIrrOcc_spine
#print axioms F8ConvProofProducer.Trace.toIrrOcc_host
#print axioms F8ConvProofProducer.Trace.toIrrOcc_ctx
#print axioms F8ConvProofProducer.Trace.toIrrOcc_P
#print axioms F8ConvProofProducer.Trace.toIrrOcc_chain_aux
#print axioms F8ConvProofProducer.Trace.toIrrOcc_chain
#print axioms pinOccCv
#print axioms pinOcc
#print axioms pinSite
#print axioms pin_appArg_host
#print axioms pin_appArg_ctx
#print axioms pin_appArg_chain_leaves
#print axioms pin_appArg_request_index
#print axioms pin_appArg_answer_left
#print axioms pin_appArg_answer_right
#print axioms pin_appArg_strict
#print axioms pin_appArg_edge
#print axioms pinLamCv
#print axioms pinLamOcc
#print axioms pinLamNode
#print axioms pin_lamBody_classify
#print axioms pin_lamBody_route
#print axioms pin_lamBody_host
#print axioms pin_lamBody_edge
#print axioms pinIdxOuterCv
#print axioms pinIdxChainNode
#print axioms pin_inIndexChain
#print axioms pin_inIndexChain_route
#print axioms pin_inIndexChain_target
#print axioms pinTpCv
#print axioms pinTpNode
#print axioms pin_inTypingPremise
#print axioms pin_inTypingPremise_route
#print axioms pin_inTypingPremise_target

end Rcic.Declarative.F8Measure
