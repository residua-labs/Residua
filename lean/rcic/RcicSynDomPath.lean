import rcic.RcicSynEnrich
import rcic.RcicSynAppBvarPBit

/-!
# Syntactic sortRow — T12: the original domain-kind trace (ChatGPT S7, #7330)

Spec: `research/rcic/sortrow/S7_ORIGINAL_DOMAIN_KIND_TRACE.md` §2–§5.
`closure_claim = 0`.

1. **`DomPath` (§2)**: an execution-provenance domain-conversion path — `same`,
   `edge` (an original `CvP … A A' (.sort u)` occurrence), `reverse`, `append`, and
   the `forwardView` family (the original `wk` / `linst` / `ewk` / `cctx` /
   same-value `esub` transports, each keeping its actual fields). It is not a new
   primitive conversion and no arbitrary finished `hconv` may be filled in.
   `append` records the actually equal middle domain with BOTH real sort typings
   on the two sides — two typings are never identified because their judgments
   agree. `DomPath.atoms` is the payment multiset; transports flatten exactly like
   `CvP.atoms`.

2. **`KindTrace` (§2)**: the bit equation, built after aligning the path's
   endpoints and junctions with the actual natural/declaration typings. Per
   original edge `c` it issues the two real smaller queries `SortCoh σ pNatural
   c.dl` and `SortCoh σ c.dr pDeclared` (or their mixed versions) and composes
   through the shared `u`; an `append` adds the junction `SortCoh σ dlM drM`; each
   forward view adds the boundary alignments at the transported typings (`linst`
   at `σ ∘ instLevel ls`, matching `LevelSub.linst` / `dispFor_instLvlsCtx`).
   `kindTrace_sortCoh` composes the end-to-end `eqN (σ s) (σ t)`.
   `domPath_edge_dm` is §2's atom edge: original field atoms `< N` keep
   `C.atoms ++ [N]` one `DMStep` above each smaller query multiset.

3. **§3 readers**: `domRead` reads the original `CvP`. `CvP.pi` hands over the
   original `hA` directly (`DomPath.edge hA`, the cheapest positive arm); `symm`
   keeps reading the original child through a `reverse` view (never rebuilding a
   larger symm judgment); `trans` splits on the literal middle — a `pi Am Bm`
   middle appends the two child paths at the two actual `Am` sort typings (`piInvP`
   of `c₁.dr` / `c₂.dl`, with the junction `SortCoh` as the smaller A6 query), a
   non-Π middle records `DomObligation.nonPiMiddle` (the original demand kept —
   never "the reader returned none, so the demand does not exist"). Every other
   arm records `DomObligation.arm` (its own §6 route; never a Π→Π read forced
   onto inputs that do not fit the interface).

4. **K3 — SameTemplateSort (§5)**: `k3DomInst` is the original lazy substitution
   (`instEnd`) of an original template `pTpl : TyP (C::Γ) A₀ (sort α)` at a legal
   `a : C`; both instances keep the sort **literally α**, atom list
   `pTpl.atoms ++ ha.atoms ++ hC.atoms`. `k3_compose`: aligned against the actual
   endpoint typings by two same-subject A6 queries, the kind equation follows even
   when `A₀[a]` and `A₀[b]` differ — K3 supplies the sort kind, never a conversion
   between the arguments. `k3Fsub` is the generated `CvP.fsub` when a real `hab`
   exists: a new rule atom whose bound is its own obligation (`k3Fsub_wt` /
   `k3Fsub_atoms`), never re-entered on P2.

The §4 `trans (symm b) b` control (weights 3/9/18/31/56, the non-Π `app` middle,
and the reflexive domain conclusion) is pinned in `RcicSynDomPathPins`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 Original-occurrence certificates (S7 §2, #7351 verdict)

A `DomPath.edge` may only wrap a `CvP` that is a **real field at an actual
occurrence inside the original forest** — a generated `symm` / `fsub` / `hconv`
never counts as original. The certificate is an occurrence path: `CvPOcc H c`
says `c` sits inside `H`'s tree along literal `CvP`-typed child fields. The
child relation `CvPChild` enumerates every `CvP`-typed argument position of
every constructor; `CvPAny` packages the heterogeneous nodes (children live in
extended contexts, predecessor environments, smaller level arities). -/

/-- A heterogeneous original conversion node: the `CvP` packed behind one
    constructor, indices implicit. Needed because original children live in
    extended contexts (`pi.hB`, `lam.hb`, `letE.hb`, `cctx.h`), predecessor
    environments (`ewk.h`) and different level arities (`linst.h`). -/
inductive CvPAny where
  | mk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (c : CvP E n Γ a b T) : CvPAny

/-- The literal `CvP`-typed fields of an original node — a plain function on
    the unwrapped `CvP` (matching on a `CvPAny.mk`-packed node can't invert the
    context/type transforms in its implicit indices). The `refl`-style leaves
    and the `TyP`-only constructors (`beta`, `zeta`, `delta`, `iota`, `sort`,
    `hconv`, `equiv`) have no `CvP` fields. -/
def fieldsOfCvP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    CvP E n Γ a b T → List CvPAny
  | .symm _ _ _ _ _ _ h _ _ => [.mk h]
  | .trans _ _ _ _ _ _ _ c₁ c₂ _ _ => [.mk c₁, .mk c₂]
  | .app _ _ _ _ _ _ _ _ _ h₁ h₂ _ _ => [.mk h₁, .mk h₂]
  | .lam _ _ _ _ _ _ _ _ _ hA hb _ _ => [.mk hA, .mk hb]
  | .pi _ _ _ _ _ _ _ _ _ hA hB _ _ => [.mk hA, .mk hB]
  | .letE _ _ _ _ _ _ _ _ _ _ _ hA hv hb _ _ => [.mk hA, .mk hv, .mk hb]
  | .tyConv _ _ _ _ _ _ _ _ h hA _ _ => [.mk h, .mk hA]
  | .wk _ _ _ _ _ _ _ _ h => [.mk h]
  | .esub _ _ _ _ _ _ _ _ _ _ h _ _ _ => [.mk h]
  | .linst _ _ _ _ _ _ _ _ _ _ h => [.mk h]
  | .ewk _ _ _ _ _ _ _ _ h => [.mk h]
  | .cctx _ _ _ _ _ _ _ _ _ h hA => [.mk h, .mk hA]
  | .fsub _ _ _ _ _ _ _ _ _ _ _ hab _ _ => [.mk hab]
  | _ => []

/-- The literal `CvP`-typed fields of a packed original node. -/
def fieldsOf : CvPAny → List CvPAny
  | .mk c => fieldsOfCvP c

/-- `CvPChild p c`: `c` is literally a `CvP`-typed field of the original node
    `p` — membership in `fieldsOf p`, never a regenerated judgment. -/
abbrev CvPChild (p c : CvPAny) : Prop := c ∈ fieldsOf p

/-- `CvPOcc H c`: the original-occurrence certificate — `c` sits inside `H`'s
    tree along literal `CvP`-typed fields. `root` is the input node itself;
    `step` descends one real field. A freshly built `CvP.symm` / `fsub` /
    `hconv` cannot produce this unless it literally occurs in `H`. -/
inductive CvPOcc (H : CvPAny) : CvPAny → Prop where
  | root : CvPOcc H H
  | step {p c : CvPAny} (h : CvPOcc H p) (s : CvPChild p c) : CvPOcc H c

/-! ## §1 `DomPath` — the provenance path (S7 §2) -/

/-- A typed domain-conversion path with its execution provenance, relative to a
    fixed original forest `H`. `edge` wraps an original `CvP … A A' (.sort u)`
    **occurrence** — its second field is the `CvPOcc H` certificate, so no
    arbitrary finished hconv may be filled in. The `forwardView` ctors keep only
    the original `wk` / `linst` / `ewk` / `cctx` / same-value `esub` transports
    with their actual fields (the `cctx` binder bridge `hA` carries the same
    `CvPOcc` certificate — it is an actual `CvP` field of the original `cctx`
    node), never freely connecting different subjects (`fsub` is a generated
    rule node, not a view). -/
inductive DomPath (H : CvPAny) :
    ResolvedEnv → Nat → LCtx → Expr Nat → Expr Nat → Type where
  | same {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      (hA : TyP E n Γ A (.sort u)) : DomPath H E n Γ A A
  | edge {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {u : Level}
      (c : CvP E n Γ A A' (.sort u))
      (occ : CvPOcc H (.mk c)) : DomPath H E n Γ A A'
  | reverse {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
      (p : DomPath H E n Γ A A') : DomPath H E n Γ A' A
  | append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A M A' : Expr Nat} {u v : Level}
      (p : DomPath H E n Γ A M) (dlM : TyP E n Γ M (.sort u))
      (drM : TyP E n Γ M (.sort v)) (q : DomPath H E n Γ M A') :
      DomPath H E n Γ A A'
  | forwardWk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat}
      (d : LocalDecl) (c : Nat) (p : DomPath H E n Γ a b) :
      DomPath H E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
  | forwardLinst {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {a b : Expr Nat}
      (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a')
      (p : DomPath H E a' Γ a b) :
      DomPath H E n (instLvlsCtx ls Γ) (instantiateLevels ls a) (instantiateLevels ls b)
  | forwardEwk {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat}
      (hext : EnvExt E₀ E) (p : DomPath H E₀ n Γ a b) : DomPath H E n Γ a b
  | forwardCctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat}
      {u : Level} (hA : CvP E n Γ A A' (.sort u))
      (occA : CvPOcc H (.mk hA))
      (p : DomPath H E n (.assumption A :: Γ) a b) :
      DomPath H E n (.assumption A' :: Γ) a b
  | forwardEsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b t v : Expr Nat}
      {j : Nat} {u : Level} (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (p : DomPath H E n Γ a b) :
      DomPath H E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)

/-- The payment multiset: original fields are paid by their own atoms, transports
    flatten (atoms do not grow under a forward view, matching `CvP.atoms`). -/
def DomPath.atoms (Aw : Nat → Nat) {H : CvPAny} :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b : Expr Nat} → DomPath H E n Γ a b → List Nat
  | _, _, _, _, _, .same hA => hA.atoms Aw
  | _, _, _, _, _, .edge c _ => c.atoms Aw
  | _, _, _, _, _, .reverse p => p.atoms Aw
  | _, _, _, _, _, .append p dlM drM q =>
      p.atoms Aw ++ dlM.atoms Aw ++ drM.atoms Aw ++ q.atoms Aw
  | _, _, _, _, _, .forwardWk _ _ p => p.atoms Aw
  | _, _, _, _, _, .forwardLinst _ _ _ p => p.atoms Aw
  | _, _, _, _, _, .forwardEwk _ p => p.atoms Aw
  | _, _, _, _, _, .forwardCctx hA _ p => p.atoms Aw ++ hA.atoms Aw
  | _, _, _, _, _, .forwardEsub _ hv hvT p => p.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw

/-! ## §2 `KindTrace` — the bit equation supply -/

/-- §2: the supply of real `SortCoh` queries along a `DomPath`. Per original edge
    `c` it issues `SortCoh σ pNatural c.dl` and `SortCoh σ c.dr pDeclared`; per
    `append` junction the `SortCoh σ dlM drM` of the two actual middle typings;
    per forward view the boundary alignments at the transported typings. `σ` is an
    index (not a parameter): the `linst` view legitimately reads its child at
    `fun l => σ (instLevel ls l)`, matching `LevelSub.linst`/`dispFor_instLvlsCtx`. -/
inductive KindTrace {H : CvPAny} : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {A A' : Expr Nat} → {s t : Level} → (σ : Level → Level) →
    DomPath H E n Γ A A' → TyP E n Γ A (.sort s) → TyP E n Γ A' (.sort t) → Prop where
  | same {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A : Expr Nat} {s t u : Level}
      {hA : TyP E n Γ A (.sort u)} {pN : TyP E n Γ A (.sort s)}
      {pD : TyP E n Γ A (.sort t)}
      (hL : SortCoh σ pN hA) (hR : SortCoh σ hA pD) : KindTrace σ (.same hA) pN pD
  | edge {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A A' : Expr Nat} {s t u : Level}
      {c : CvP E n Γ A A' (.sort u)} {occ : CvPOcc H (.mk c)}
      {pN : TyP E n Γ A (.sort s)}
      {pD : TyP E n Γ A' (.sort t)}
      (hL : SortCoh σ pN c.dl) (hR : SortCoh σ c.dr pD) :
      KindTrace σ (.edge c occ) pN pD
  | reverse {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A A' : Expr Nat} {s t : Level}
      {p : DomPath H E n Γ A A'} {pN : TyP E n Γ A' (.sort s)}
      {pD : TyP E n Γ A (.sort t)}
      (tr : KindTrace σ p pD pN) : KindTrace σ (.reverse p) pN pD
  | append {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A M A' : Expr Nat} {s u v t : Level}
      {p : DomPath H E n Γ A M} {q : DomPath H E n Γ M A'}
      {dlM : TyP E n Γ M (.sort u)} {drM : TyP E n Γ M (.sort v)}
      {pN : TyP E n Γ A (.sort s)} {pD : TyP E n Γ A' (.sort t)}
      (trL : KindTrace σ p pN dlM) (hj : SortCoh σ dlM drM)
      (trR : KindTrace σ q drM pD) : KindTrace σ (.append p dlM drM q) pN pD
  | forwardWk {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b : Expr Nat} {s t s₀ t₀ : Level} {p : DomPath H E n Γ a b}
      (d : LocalDecl) (c : Nat)
      {pN₀ : TyP E n Γ a (.sort s₀)} {pD₀ : TyP E n Γ b (.sort t₀)}
      {pN : TyP E n (insertAt d c Γ) (lift c 1 a) (.sort s)}
      {pD : TyP E n (insertAt d c Γ) (lift c 1 b) (.sort t)}
      (tr : KindTrace σ p pN₀ pD₀)
      (hL : SortCoh σ pN (TyP.wk E n Γ a (.sort s₀) d c pN₀))
      (hR : SortCoh σ (TyP.wk E n Γ b (.sort t₀) d c pD₀) pD) :
      KindTrace σ (.forwardWk d c p) pN pD
  | forwardLinst {σ : Level → Level} {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx}
      {a b : Expr Nat} {s t s₀ t₀ : Level} {p : DomPath H E a' Γ a b}
      (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a')
      {pN₀ : TyP E a' Γ a (.sort s₀)} {pD₀ : TyP E a' Γ b (.sort t₀)}
      {pN : TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls a) (.sort s)}
      {pD : TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls b) (.sort t)}
      (tr : KindTrace (fun l => σ (instLevel ls l)) p pN₀ pD₀)
      (hL : SortCoh σ pN (TyP.linst E a' n Γ a (.sort s₀) ls hls hlen pN₀))
      (hR : SortCoh σ (TyP.linst E a' n Γ b (.sort t₀) ls hls hlen pD₀) pD) :
      KindTrace σ (.forwardLinst ls hls hlen p) pN pD
  | forwardEwk {σ : Level → Level} {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b : Expr Nat} {s t s₀ t₀ : Level} (hext : EnvExt E₀ E)
      {p : DomPath H E₀ n Γ a b}
      {pN₀ : TyP E₀ n Γ a (.sort s₀)} {pD₀ : TyP E₀ n Γ b (.sort t₀)}
      {pN : TyP E n Γ a (.sort s)} {pD : TyP E n Γ b (.sort t)}
      (tr : KindTrace σ p pN₀ pD₀)
      (hL : SortCoh σ pN (TyP.ewk E₀ E n Γ a (.sort s₀) hext pN₀))
      (hR : SortCoh σ (TyP.ewk E₀ E n Γ b (.sort t₀) hext pD₀) pD) :
      KindTrace σ (.forwardEwk hext p) pN pD
  | forwardCctx {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b A A' : Expr Nat} {u s t s₀ t₀ : Level}
      (hA : CvP E n Γ A A' (.sort u))
      (occA : CvPOcc H (.mk hA))
      {p : DomPath H E n (.assumption A :: Γ) a b}
      {pN₀ : TyP E n (.assumption A :: Γ) a (.sort s₀)}
      {pD₀ : TyP E n (.assumption A :: Γ) b (.sort t₀)}
      {pN : TyP E n (.assumption A' :: Γ) a (.sort s)}
      {pD : TyP E n (.assumption A' :: Γ) b (.sort t)}
      (tr : KindTrace σ p pN₀ pD₀)
      (hL : SortCoh σ pN (TyP.cctx E n Γ a (.sort s₀) A A' u pN₀ hA))
      (hR : SortCoh σ (TyP.cctx E n Γ b (.sort t₀) A A' u pD₀ hA) pD) :
      KindTrace σ (.forwardCctx hA occA p) pN pD
  | forwardEsub {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b t v : Expr Nat} {j : Nat} {u s t₀ s₀ t₁ : Level}
      (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      {p : DomPath H E n Γ a b}
      {pN₀ : TyP E n Γ a (.sort s₀)} {pD₀ : TyP E n Γ b (.sort t₀)}
      {pN : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) a) (.sort s)}
      {pD : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) b) (.sort t₁)}
      (tr : KindTrace σ p pN₀ pD₀)
      (hL : SortCoh σ pN (TyP.esub E n Γ a (.sort s₀) t v j u pN₀ hget hv hvT))
      (hR : SortCoh σ (TyP.esub E n Γ b (.sort t₀) t v j u pD₀ hget hv hvT) pD) :
      KindTrace σ (.forwardEsub hget hv hvT p) pN pD

/-- §2: the per-edge and per-junction queries compose to the end-to-end bit
    equation `eqN (σ s) (σ t)` — never a global `SortUnique`, only the shared
    `u` at each edge and the junction sort coherence at each `append`. The two
    endpoints have different subjects, so the conclusion is the `eqN`, not a
    `SortCoh` — every leg inside *is* a same-subject `SortCoh` query. -/
theorem kindTrace_sortCoh {σ : Level → Level} {H : CvPAny} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' : Expr Nat} {s t : Level} {p : DomPath H E n Γ A A'}
    {pN : TyP E n Γ A (.sort s)} {pD : TyP E n Γ A' (.sort t)}
    (tr : KindTrace σ p pN pD) : eqN (σ s) (σ t) := by
  induction tr with
  | same hL hR => exact eqN_trans hL hR
  | edge hL hR => exact eqN_trans hL hR
  | reverse _ ih => exact eqN_symm ih
  | append _ hj _ ihL ihR => exact eqN_trans ihL (eqN_trans hj ihR)
  | forwardWk _ _ _ hL hR ih => exact eqN_trans hL (eqN_trans ih hR)
  | forwardLinst _ _ _ _ hL hR ih => exact eqN_trans hL (eqN_trans ih hR)
  | forwardEwk _ _ hL hR ih => exact eqN_trans hL (eqN_trans ih hR)
  | forwardCctx _ _ _ hL hR ih => exact eqN_trans hL (eqN_trans ih hR)
  | forwardEsub _ _ _ _ hL hR ih => exact eqN_trans hL (eqN_trans ih hR)

/-- §2's atom edges: if every atom entering the query is `< N`, then
    `C.atoms ++ [N]` stays one `DMStep` above each of the two smaller query
    multisets `pNatural.atoms ++ c.dl.atoms` and `c.dr.atoms ++ pDeclared.atoms`.
    The edges and local compositions of `dmStep_under_rule` are reused; no old
    `Below` is constructed. -/
theorem domPath_edge_dm {C : List Nat} {N : Nat} (Y : List Nat)
    (h : ∀ y ∈ Y, y < N) : DMStep (C ++ Y) (C ++ [N]) := by
  refine ⟨[N], Y, C, List.cons_ne_nil _ _, List.perm_append_comm,
    List.perm_append_comm, fun y hy => ⟨N, List.mem_singleton_self _, h y hy⟩⟩

/-- §2's atom edges, instantiated at an original `edge c`: the two real smaller
    queries of `KindTrace.edge`, each below the same `N` when the entering atoms
    are. -/
theorem domPath_edge_atoms_dm (Aw : Nat → Nat) {C : List Nat} {N : Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {s t u : Level}
    {pN : TyP E n Γ A (.sort s)} {pD : TyP E n Γ A' (.sort t)}
    {c : CvP E n Γ A A' (.sort u)}
    (hL : ∀ y ∈ pN.atoms Aw ++ c.dl.atoms Aw, y < N)
    (hR : ∀ y ∈ c.dr.atoms Aw ++ pD.atoms Aw, y < N) :
    DMStep (C ++ (pN.atoms Aw ++ c.dl.atoms Aw)) (C ++ [N]) ∧
    DMStep (C ++ (c.dr.atoms Aw ++ pD.atoms Aw)) (C ++ [N]) :=
  ⟨domPath_edge_dm _ hL, domPath_edge_dm _ hR⟩

/-! ## §3 `domRead` — the exact reading of `pi` / `symm` / `trans` -/

mutual

/-- The §3 domain read of an original conversion `c` inside the fixed forest `H`:
    an actual `DomPath` between the two Π domains (every edge certified into `H`),
    or the recorded obligation left unpaid. -/
inductive DomRead (H : CvPAny) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a : Expr Nat} → {b : Expr Nat} → {T : Expr Nat} →
    CvP E n Γ a b T → Type where
  | path {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      {c : CvP E n Γ a b T} {Ad Bd Ar Br : Expr Nat}
      (p : DomPath H E n Γ Ad Ar)
      (ha : a = .pi Ad Bd) (hb : b = .pi Ar Br) : DomRead H c
  | obligation {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      {c : CvP E n Γ a b T} (d : DomObligation H c) : DomRead H c

/-- An unpaid domain-read demand (§3): the original demand kept with its real
    children, the actual middle, and which junction side is owed — indexed by the
    actual node, so the demand is bound to the input that owes it. -/
inductive DomObligation (H : CvPAny) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a : Expr Nat} → {b : Expr Nat} → {T : Expr Nat} →
    CvP E n Γ a b T → Type where
  | nonPiMiddle {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a m b T : Expr Nat}
      {c₁ : CvP E n Γ a m T} {c₂ : CvP E n Γ m b T}
      {dl : TyP E n Γ a T} {dr : TyP E n Γ b T}
      (hnot : ∀ Am Bm : Expr Nat, m ≠ .pi Am Bm)
      (lr : DomRead H c₁) (rr : DomRead H c₂) :
      DomObligation H (.trans E n Γ a m b T c₁ c₂ dl dr)
  | symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      {c : CvP E n Γ a b T}
      {dl : TyP E n Γ b T} {dr : TyP E n Γ a T}
      (d : DomObligation H c) : DomObligation H (.symm E n Γ a b T c dl dr)
  | junctionLeft {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a m b T Am Bm : Expr Nat}
      (hm : m = .pi Am Bm)
      {c₁ : CvP E n Γ a m T} {c₂ : CvP E n Γ m b T}
      {dl : TyP E n Γ a T} {dr : TyP E n Γ b T}
      (d : DomObligation H c₁) (rr : DomRead H c₂) :
      DomObligation H (.trans E n Γ a m b T c₁ c₂ dl dr)
  | junctionRight {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a m b T Am Bm : Expr Nat}
      (hm : m = .pi Am Bm)
      {c₁ : CvP E n Γ a m T} {c₂ : CvP E n Γ m b T}
      {dl : TyP E n Γ a T} {dr : TyP E n Γ b T}
      (lr : DomRead H c₁) (d : DomObligation H c₂) :
      DomObligation H (.trans E n Γ a m b T c₁ c₂ dl dr)
  | arm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (c : CvP E n Γ a b T) : DomObligation H c

end

/-- §3: the exact reading of an original `CvP` at its `pi`, `symm`, `trans` arms —
    the input is an actual **occurrence** `hocc` of `c` inside `H`, so the produced
    path is related to the input conversion and every `.edge` cites its real
    position. `pi` hands the original `hA` over at `hocc.step .piHA`; `symm` reads
    the original child through `reverse` at `.symmH`; `trans` splits on the literal
    middle — `pi Am Bm` appends the two child paths (read at `.transL` / `.transR`)
    at the actual `Am` sort typings inverted out of `c₁.dr` / `c₂.dl`, anything
    else records `nonPiMiddle`. Every other arm records `arm`. -/
def domRead {H : CvPAny} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {a b T : Expr Nat} → (c : CvP E n Γ a b T) →
    CvPOcc H (.mk c) → DomRead H c
  | _, _, _, .pi _ _ _ _ _ _ _ _ _ hA _ _ _, hocc =>
      .path (.edge hA (hocc.step (.head _))) rfl rfl
  | _, _, _, .symm _ _ _ _ _ _ c _ _, hocc =>
      match domRead c (hocc.step (.head _)) with
      | .path p ha hb => .path (.reverse p) hb ha
      | .obligation d => .obligation (.symm d)
  | _, _, _, .trans _ _ _ _ m _ _ c₁ c₂ _ _, hocc =>
      match m with
      | .pi Am Bm =>
          match domRead c₁ (hocc.step (.head _)),
              domRead c₂ (hocc.step (.tail _ (.head _))) with
          | .path p₁ ha₁ hb₁, .path p₂ ha₂ hb₂ => by
              obtain ⟨rfl, -⟩ := Expr.pi.inj hb₁
              obtain ⟨rfl, -⟩ := Expr.pi.inj ha₂
              exact .path (.append p₁
                (piInvP (envExt_refl _) c₁.dr rfl).hA
                (piInvP (envExt_refl _) c₂.dl rfl).hA p₂) ha₁ hb₂
          | .obligation d₁, r₂ => .obligation (.junctionLeft rfl d₁ r₂)
          | r₁, .obligation d₂ => .obligation (.junctionRight rfl r₁ d₂)
      | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .letE _ _ _ | .lit _ =>
          .obligation (.nonPiMiddle (fun _ _ h => Expr.noConfusion h)
            (domRead c₁ (hocc.step (.head _)))
            (domRead c₂ (hocc.step (.tail _ (.head _)))))
  | _, _, _, c, _ => .obligation (.arm c)

/-! ## §5 K3 — SameTemplateSort -/

/-- K3 (S7 §5): one original lazy substitution of the template `pTpl : A₀ : sort α`
    under `assumption C :: Γ` at a legal `a : C`. The result is at sort
    **literally α** — `instEnd`, not a new large Π typing. -/
def k3DomInst {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α)) (hC : TyP E n Γ C (.sort γ))
    {a : Expr Nat} (ha : TyP E n Γ a C) : TyP E n Γ (instantiate0 a A₀) (.sort α) :=
  instEnd pTpl ha hC

/-- §5: each instance's atom list is `pTpl.atoms ++ argument.atoms ++ hC.atoms`;
    when `pTpl`, `hC` and the argument are original fields of a real β path, `N`
    pays per atom — no new large Π typing is synthesized. -/
theorem k3DomInst_atoms (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    {a : Expr Nat} (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) :
    (k3DomInst pTpl hC ha).atoms Aw = pTpl.atoms Aw ++ ha.atoms Aw ++ hC.atoms Aw := by
  rw [k3DomInst, atoms_instEnd]

theorem k3DomInst_wt (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    {a : Expr Nat} (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) :
    (k3DomInst pTpl hC ha).wt Aw = 1 + pTpl.wt Aw + ha.wt Aw + hC.wt Aw := by
  rw [k3DomInst, instEnd_wt]

/-- §5: `pA` and `pB` share the sort kind literally — `eqN (σ α) (σ α)`
    reflexively. No `a ≡ b` is claimed: K3 is not a constructor for arbitrary
    domain conversions. -/
theorem k3_same_sort {σ : Level → Level} (α : Level) : eqN (σ α) (σ α) :=
  eqN_refl _

/-- §5: align `actual left domain typing ↔ pA` and `pB ↔ actual right
    declaration-domain typing`, each a same-subject A6 query; the needed kind
    equation follows even when `A₀[a]` and `A₀[b]` are different terms. -/
theorem k3_compose {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    {a b : Expr Nat} {s t : Level}
    (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α)) (hC : TyP E n Γ C (.sort γ))
    (ha : TyP E n Γ a C) (hb : TyP E n Γ b C)
    {pA' : TyP E n Γ (instantiate0 a A₀) (.sort s)}
    {pB' : TyP E n Γ (instantiate0 b A₀) (.sort t)}
    (hL : SortCoh σ pA' (k3DomInst pTpl hC ha))
    (hR : SortCoh σ (k3DomInst pTpl hC hb) pB') : eqN (σ s) (σ t) :=
  eqN_trans hL (eqN_trans (k3_same_sort α) hR)

/-- §5: when the real path also carries `hab : a ≡ b : C`, the `fsub` domain
    conversion `A₀[a] ≡ A₀[b]` can be built — a GENERATED judgment (a new rule
    atom), never a K3 deliverable and never re-entered on P2. -/
def k3Fsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    {a b : Expr Nat} (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) (hb : TyP E n Γ b C)
    (hab : CvP E n Γ a b C) :
    CvP E n Γ (instantiate0 a A₀) (instantiate0 b A₀) (.sort α) :=
  .fsub E n Γ C A₀ (.sort α) a b γ pTpl hC hab
    (k3DomInst pTpl hC ha) (k3DomInst pTpl hC hb)

/-- The generated `fsub` is one new rule atom — its bound is a separate
    obligation, never inherited from the original fields. -/
theorem k3Fsub_atoms (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    {a b : Expr Nat} (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) (hb : TyP E n Γ b C)
    (hab : CvP E n Γ a b C) :
    (k3Fsub pTpl hC ha hb hab).atoms Aw = [(k3Fsub pTpl hC ha hb hab).wt Aw] := by
  simp only [k3Fsub, CvP.atoms]

theorem k3Fsub_wt (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C A₀ : Expr Nat} {α γ : Level}
    {a b : Expr Nat} (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) (hb : TyP E n Γ b C)
    (hab : CvP E n Γ a b C) :
    (k3Fsub pTpl hC ha hb hab).wt Aw =
      1 + pTpl.wt Aw + hC.wt Aw + hab.wt Aw +
        (k3DomInst pTpl hC ha).wt Aw + (k3DomInst pTpl hC hb).wt Aw := by
  simp only [k3Fsub, CvP.wt]

end Rcic.Syn

#print axioms Rcic.Syn.DomPath.atoms
#print axioms Rcic.Syn.kindTrace_sortCoh
#print axioms Rcic.Syn.domPath_edge_dm
#print axioms Rcic.Syn.domPath_edge_atoms_dm
#print axioms Rcic.Syn.domRead
#print axioms Rcic.Syn.k3DomInst
#print axioms Rcic.Syn.k3DomInst_atoms
#print axioms Rcic.Syn.k3DomInst_wt
#print axioms Rcic.Syn.k3_same_sort
#print axioms Rcic.Syn.k3_compose
#print axioms Rcic.Syn.k3Fsub
#print axioms Rcic.Syn.k3Fsub_atoms
#print axioms Rcic.Syn.k3Fsub_wt
