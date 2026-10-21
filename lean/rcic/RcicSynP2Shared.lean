import rcic.RcicSynViewPlan
import rcic.RcicSynBelowScoped
import rcic.RcicSynES
import rcic.RcicSynBelow
import rcic.RcicSynObsLevels
import rcic.RcicSynZetaMeasureRefute
import rcic.RcicSynEnrich
import rcic.RcicSynSlotKind
import rcic.RcicSynLetInline
import rcic.RcicSynCtsLocal
import rcic.RcicSynObsSupplier

/-!
# P2 shared types — `P2Tag`, `RoutedDisp`, `P2Query`, `Demand`, `Goal`, `ResolvedView`, rank

`research/rcic/sortrow/S8_P2_CONDITIONAL_STEP.md` — the versioned shared
interface the P2 conditional skeleton is built on, repaired in place for the
three findings of `research/rcic/sortrow/STEP_SUPPLIERS.md` (fable-step ITEM 2,
2026-10-17; S15 §6–7). `closure_claim` stays 0; nothing here is registered as
discharged hcoh.

* **Frame (finding 1).** Every query carries the *original ambient receipt* it
  was issued under — a `ScopedCtx Eₐ E₀ n₀ Γ₀`, the frame — separately from the
  context `Γ` of its own derivation. `P2Query.rank` reads the frame: first
  coordinate `Γ₀.length`, local key `combMeas` at the frame's canonical spine.
  A sub-request under one more binder keeps its parent's frame and descends by
  `LexDM` on the local key (S15 §6 "introduced fields paid by the surviving N").
  The pre-repair first coordinate — the derivation's own `Γ.length` — is kept as
  `P2Query.ownPrefixLength`, a frozen control only.
* **Explicit display (finding 3).** Every query carries the display `ρ` its goal
  is evaluated at. `RoutedDisp σ E n Γ ρ` is the display's provenance: canonical
  from a `CtxP`, or reached from a routed display by one real binder /
  transport step (S15 §7 "transport by the original active/pending occurrence
  table", in miniature; the full `DisplayRoute` of `RcicSynDisplayRoute` is not
  yet wired in). Transport children (`wk`/`esub`/`linst`/`ewk`/`cctx`) are
  therefore genuine `P2Query`s at the parent's transformed `ρ`.
* **`Demand` carries the public roots' side conditions (finding 2).** A root is
  demanded with exactly what `BelowScoped`'s public fields require — the
  inputs' `AssumpPref` and `LevelHom σ` (`cts` has no `σ`) — at its own scope's
  canonical display. Nothing is narrower than the public roots. The pre-repair
  shape (any public query, any `σ`, no `AssumpPref`) is kept as `DemandWide`, a
  frozen control: `step_refuted_const_zero` in `RcicSynStepSkeleton` refutes its
  `Step`.
* **Issuance is an answer-free edge (Q267, fable-step ITEM 3).** `Issues issuer q`
  is an inductive relation with one constructor per actual request row: the
  issuing query's constructor and the field slot the target is read from (same
  frame, same level map, display routed across the binder or transport actually
  crossed), the S9 any-pair rows of `cts`/`bitCoh`, the same-rank `cl/eut →
  mixed` and `bitCoh → eut` local dependencies, the landed `RcicSynRouteSlot`
  `pb` edges (the let-value edge moves to the prefix frame certified by
  `Γ.drop (i+1) = Γ₀`), the two `head` legs with the kind sources bound to the
  conversion's endpoints, and same-site occurrence rows indexed by `DNode.subAt`
  paths into the issuer's payload (the landed K1 occurrence receipt of
  `RcicSynSlotKind`). `Demand.issued` takes only `Demand issuer` and
  `Issues issuer q`; `AssumpPref`/`LevelHom`/`RoutedDisp` of the target are
  theorems (`Issues.ap/hom/routed`), never external witnesses, and there is no
  `AlignRequest` payload. The Q267 shape — `issued` with an unindexed
  `AlignRequest` and caller-supplied `AP`/`Hom`/`Routed` — is kept as
  `DemandFree`, a frozen control; `RoutedDisp.esub`'s kind is tied to the node's
  actual `hv`/`hvT` (the free-`u` arm is kept as `RoutedDispFree`).
* **Observations are individual positions of one original derivation (Q269,
  fable-step ITEM 4).** `.observation D θ φ ψ pos` owes ONE level observation of ONE
  derivation `D` at the observer position `pos` (`ObsPos.out k` / `.gate k`, S4
  `TyP.outLevels`/`gateLevels` under the entered `linst` composite `θ`) between the
  two comparison maps `φ`/`ψ` — the exact premise shape of the landed `obsLvlEq_eps` /
  `obsLvlEq_eps_delta`. The only issuing rows are the δ node's `delta_obs_out` /
  `delta_obs_gate`: the observed derivation is the ACTUAL admission the frame's
  receipt selects (`((enrichEnvWfT S.env).defAdm hres hbody htr).hv` — S7 T3
  `DefAdm`, `AdmObsPlan.Db_eq`), the maps are the δ-exchange maps, and EVERY actual
  position of its observer lists is issued **unconditionally** (Q270, fable-step
  ITEM 5): the row carries no `ObsCert` and no supply guard — the answer belongs to
  the `StepSuppliers.delta_obs` field (which may use the S7 §3 routes inside its
  proof), never to the demand (BELOWC_OBSERVATION_REQUESTS.md §1.4, §2.1, §6;
  W-TABLE-DELTA-OBSERVATION-STABILITY). The ITEM 3 shape —
  a two-derivation request whose goal zipped two ENTIRE out/gate traversals, issued by
  `occ_obs` (two same-site occurrences) and `delta_obs` (`hb` against `dr`) — is kept
  as the frozen `P2Query.obsPair` / `IssuesObsFree` / `DemandObsFree`; both Q269
  countermodels are reproduced against it in `RcicSynStepSkeleton`, and no live row
  targets `.obsPair` (`obsPair_not_demanded`).
* **Original-source contracts (Q269 P2).** The `cts`/`bitCoh` rows select the
  consumers' finite original ports — the issuer's own `dl`/`reg` fields against
  `sortNode` (`cts_eut_dlX`, `cts_cl_regL`, `cts_cl_regX`, `bitCoh_cl_regL/R`) — never
  a fresh same-context pair; `pb_letValue` reads the let entry's tail receipt and its
  stored type/value typings off the frame receipt's own `letBinding` node
  (`LetEntryAt`, the §6.1 `CtxEntrySel` decoder) and issues at that node's tail scope.
* `Goal` is closed — computed from the query by this file's own definition; it
  is never a caller-presented proposition.
* `ResolvedView` is the consumer-usable working view: the computed `ViewPlan`,
  how the context side was obtained, and the real subquery budget. It contains
  no current `Goal q` and never uniformly requires a source `CtxP`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The ten P2 dispatch tags: six public, four internal. -/
inductive P2Tag : Type where
  | es | cl | eut | cts | pb | bitCoh
  | mixed | head | slot | observation
  deriving DecidableEq

/-- The position of one individual level observation in a derivation's observer lists
    (S4 `TyP.outLevels` / `TyP.gateLevels`): an output level or a gate level, by index. -/
inductive ObsPos : Type where
  | out (k : Nat)
  | gate (k : Nat)
  deriving DecidableEq

/-- **FROZEN CONTROL (Q267 countermodel 2).** The ITEM 2 display provenance, whose
    `esub` arm takes the kind `u` **freely** — not tied to the node's `hv`/`hvT`.
    `Rcic.Syn.Q267RoutedEsub.routed_bad_free` (`RcicSynStepSkeleton`) still builds the
    wrong display `[.drop]` from it. Not used by `Demand`.

    Original docstring: `ρ` is a legitimate display for `Γ` under `σ` when it is
    the canonical disposition of a real `CtxP`, or is reached from a routed
    display by one real step — a binder entered (`assumption`/`letDrop`/
    `letInline`, mirroring `DispFor`), or a transport crossed in the direction
    the landed `es_*` transport lemmas read it (`wk`: `removeAt`; `esub`:
    `insertDisp`; `linst`: the composite level map; `ewk`: the source
    environment; `cctx`: the source binder, display unchanged). No source
    `CtxP` is ever required for a transport child (S15 §7). -/
inductive RoutedDispFree : (Level → Level) → ResolvedEnv → Nat → LCtx → List Disp → Prop where
  | canon {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (C : CtxP E n Γ) :
      RoutedDispFree σ E n Γ (C.disp σ)
  | assumption {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A : Expr Nat} {u : Level} :
      RoutedDispFree σ E n Γ ρ → TyP E n Γ A (.sort u) →
      RoutedDispFree σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u)) :: ρ)
  | letDrop {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A v : Expr Nat} {u : Level} :
      RoutedDispFree σ E n Γ ρ → (hA : TyP E n Γ A (.sort u)) → (hv : TyP E n Γ v A) →
      hv.eps σ ρ = .star → RoutedDispFree σ E n (.letBinding A v :: Γ) (.drop :: ρ)
  | letInline {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A v : Expr Nat} {u : Level} :
      RoutedDispFree σ E n Γ ρ → (hA : TyP E n Γ A (.sort u)) → (hv : TyP E n Γ v A) →
      RoutedDispFree σ E n (.letBinding A v :: Γ) (.inline (hv.eps σ ρ) :: ρ)
  | wk {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      (d : LocalDecl) (c : Nat) :
      RoutedDispFree σ E n (insertAt d c Γ) ρ → RoutedDispFree σ E n Γ (removeAt ρ c)
  | esub {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {t v : Expr Nat} {j : Nat} (u : Level) (hget : Γ[j]? = some (.assumption t)) :
      RoutedDispFree σ E n (substRemove v j Γ) ρ →
      RoutedDispFree σ E n Γ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ)
  | linst {σ : Level → Level} {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {ρ : List Disp}
      (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a') :
      RoutedDispFree σ E n (instLvlsCtx ls Γ) ρ → RoutedDispFree (fun l => σ (instLevel ls l)) E a' Γ ρ
  | ewk {σ : Level → Level} {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      (hext : EnvExt E₀ E) : RoutedDispFree σ E n Γ ρ → RoutedDispFree σ E₀ n Γ ρ
  | cctx {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A A' : Expr Nat} {u : Level} (hA : CvP E n Γ A A' (.sort u)) :
      RoutedDispFree σ E n (.assumption A' :: Γ) ρ → RoutedDispFree σ E n (.assumption A :: Γ) ρ

/-- Display provenance: `ρ` is a legitimate display for `Γ` under `σ` when it is
    the canonical disposition of a real `CtxP`, or is reached from a routed
    display by one real step — a binder entered (`assumption`/`letDrop`/
    `letInline`, mirroring `DispFor`), or a transport crossed in the direction
    the landed `es_*` transport lemmas read it (`wk`: `removeAt`; `esub`:
    `insertDisp`; `linst`: the composite level map; `ewk`: the source
    environment; `cctx`: the source binder, display unchanged). No source
    `CtxP` is ever required for a transport child (S15 §7). **Q267 repair:** the
    `esub` arm's kind `u` is the kind of the removed binder's type as the original
    node certifies it — the arm takes the node's `hv`/`hvT` (replacement typing and
    type-at-kind) together with `hget`; it is never freely supplied. -/
inductive RoutedDisp : (Level → Level) → ResolvedEnv → Nat → LCtx → List Disp → Prop where
  | canon {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (C : CtxP E n Γ) :
      RoutedDisp σ E n Γ (C.disp σ)
  | assumption {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A : Expr Nat} {u : Level} :
      RoutedDisp σ E n Γ ρ → TyP E n Γ A (.sort u) →
      RoutedDisp σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u)) :: ρ)
  | letDrop {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A v : Expr Nat} {u : Level} :
      RoutedDisp σ E n Γ ρ → (hA : TyP E n Γ A (.sort u)) → (hv : TyP E n Γ v A) →
      hv.eps σ ρ = .star → RoutedDisp σ E n (.letBinding A v :: Γ) (.drop :: ρ)
  | letInline {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A v : Expr Nat} {u : Level} :
      RoutedDisp σ E n Γ ρ → (hA : TyP E n Γ A (.sort u)) → (hv : TyP E n Γ v A) →
      RoutedDisp σ E n (.letBinding A v :: Γ) (.inline (hv.eps σ ρ) :: ρ)
  | wk {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      (d : LocalDecl) (c : Nat) :
      RoutedDisp σ E n (insertAt d c Γ) ρ → RoutedDisp σ E n Γ (removeAt ρ c)
  | esub {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {t v : Expr Nat} {j : Nat} {u : Level} (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      RoutedDisp σ E n (substRemove v j Γ) ρ →
      RoutedDisp σ E n Γ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ)
  | linst {σ : Level → Level} {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {ρ : List Disp}
      (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a') :
      RoutedDisp σ E n (instLvlsCtx ls Γ) ρ → RoutedDisp (fun l => σ (instLevel ls l)) E a' Γ ρ
  | ewk {σ : Level → Level} {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      (hext : EnvExt E₀ E) : RoutedDisp σ E n Γ ρ → RoutedDisp σ E₀ n Γ ρ
  | cctx {σ : Level → Level} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A A' : Expr Nat} {u : Level} (hA : CvP E n Γ A A' (.sort u)) :
      RoutedDisp σ E n (.assumption A' :: Γ) ρ → RoutedDisp σ E n (.assumption A :: Γ) ρ

/-- A scope's canonical display is routed (the `canon` base). -/
theorem ScopedCtx.canRouted {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) : RoutedDisp σ E n Γ (S.can σ) :=
  .canon (enrichCtxWfT_of_envWfT S.env S.ctx)

/-- The bounded query language over the ambient admitted environment `Eₐ`.
    Every constructor carries its actual original objects, the **frame**
    `S : ScopedCtx Eₐ E₀ n₀ Γ₀` (the original ambient receipt the query was
    issued under — its canonical spine and `Γ₀.length` are the rank), the level
    map actually applied (`cts` has none; its spine is `id`), and the **display**
    `ρ : List Disp` its goal is evaluated at. Internal tags carry the objects
    their owed semantic needs — `mixed` the same-subject typing pair, `head` the
    original conversion path plus the two domain-kind sources, `slot` the
    actual ι-slot lookup and slot sort, `observation` ONE observed derivation, the
    entered `linst` composite, the two comparison maps and the observer position
    (Q269: never two derivations' whole traversals). -/
inductive P2Query (Eₐ : ResolvedEnv) : Type where
  | es {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b T : Expr Nat} :
      CvP E n Γ a b T → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp → P2Query Eₐ
  | cl {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T₁ T₂ : Expr Nat} :
      TyP E n Γ e T₁ → TyP E n Γ e T₂ → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp →
      P2Query Eₐ
  | eut {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T₁ T₂ : Expr Nat} :
      TyP E n Γ e T₁ → TyP E n Γ e T₂ → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp →
      P2Query Eₐ
  | cts {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {X Y : Expr Nat} {w s : Level} :
      CvP E n Γ X Y (.sort w) → TyP E n Γ X (.sort s) → ScopedCtx Eₐ E₀ n₀ Γ₀ → List Disp →
      P2Query Eₐ
  | pb {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T : Expr Nat} {s : Level} :
      TyP E n Γ e T → TyP E n Γ T (.sort s) → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) →
      List Disp → P2Query Eₐ
  | bitCoh {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {T : Expr Nat} {u v : Level} :
      TyP E n Γ T (.sort u) → TyP E n Γ T (.sort v) → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) →
      List Disp → P2Query Eₐ
  | mixed {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T₁ T₂ : Expr Nat} :
      TyP E n Γ e T₁ → TyP E n Γ e T₂ → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp →
      P2Query Eₐ
  | head {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a b : Expr Nat} {u : Level} {A A' : Expr Nat} :
      CvP E n Γ a b (.sort u) → (uL uR : Level) →
      TyP E n Γ A (.sort uL) → TyP E n Γ A' (.sort uR) →
      ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp → P2Query Eₐ
  | slot {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {r : Nat} {m : CheckedMember} {T : Expr Nat} :
      (u uD : Level) → E.members r = some m → TyP E n Γ T (.sort u) →
      (ls : List Level) → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp → P2Query Eₐ
  | observation {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T : Expr Nat} :
      TyP E n Γ e T → (Level → Level) → (Level → Level) → (Level → Level) → ObsPos →
      ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp → P2Query Eₐ
  /-- **FROZEN CONTROL (Q269).** The ITEM 3 observation request: two typings of one
      subject, whose goal zipped the two ENTIRE out/gate traversals. No live `Issues` row
      targets it (`obsPair_not_demanded`, `RcicSynStepSkeleton`); it is kept so both Q269
      countermodels stay constructible against `IssuesObsFree` / `DemandObsFree`. Shares
      the `observation` dispatch tag. -/
  | obsPair {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T : Expr Nat} :
      TyP E n Γ e T → TyP E n Γ e T → ScopedCtx Eₐ E₀ n₀ Γ₀ → (Level → Level) → List Disp →
      P2Query Eₐ

/-- The dispatch tag, computed by the constructor (the frozen `obsPair` shares
    `observation`'s). -/
def P2Query.tag {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Tag
  | .es .. => .es
  | .cl .. => .cl
  | .eut .. => .eut
  | .cts .. => .cts
  | .pb .. => .pb
  | .bitCoh .. => .bitCoh
  | .mixed .. => .mixed
  | .head .. => .head
  | .slot .. => .slot
  | .observation .. => .observation
  | .obsPair .. => .observation

/-- The six public tags are the independent roots of demand. -/
def P2Query.isPublic {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Bool :=
  match q.tag with
  | .es | .cl | .eut | .cts | .pb | .bitCoh => true
  | .mixed | .head | .slot | .observation => false

/-- `AssumpPref` of the query's actual derivations — what `BelowScoped`'s public
    fields require of their inputs. -/
def P2Query.AP {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop
  | .es h _ _ _ => h.AssumpPref
  | .cl D₁ D₂ _ _ _ => D₁.AssumpPref ∧ D₂.AssumpPref
  | .eut D₁ D₂ _ _ _ => D₁.AssumpPref ∧ D₂.AssumpPref
  | .cts h DX _ _ => h.AssumpPref ∧ DX.AssumpPref
  | .pb D DT _ _ _ => D.AssumpPref ∧ DT.AssumpPref
  | .bitCoh D₁ D₂ _ _ _ => D₁.AssumpPref ∧ D₂.AssumpPref
  | .mixed D₁ D₂ _ _ _ => D₁.AssumpPref ∧ D₂.AssumpPref
  | .head c _ _ dL dR _ _ _ => c.AssumpPref ∧ dL.AssumpPref ∧ dR.AssumpPref
  | .slot _ _ _ dSlot _ _ _ _ => dSlot.AssumpPref
  | .observation D _ _ _ _ _ _ _ => D.AssumpPref
  | .obsPair D₁ D₂ _ _ _ => D₁.AssumpPref ∧ D₂.AssumpPref

/-- `LevelHom` of the level map actually applied (`cts` applies none). -/
def P2Query.Hom {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop
  | .es _ _ σ _ => LevelHom σ
  | .cl _ _ _ σ _ => LevelHom σ
  | .eut _ _ _ σ _ => LevelHom σ
  | .cts _ _ _ _ => True
  | .pb _ _ _ σ _ => LevelHom σ
  | .bitCoh _ _ _ σ _ => LevelHom σ
  | .mixed _ _ _ σ _ => LevelHom σ
  | .head _ _ _ _ _ _ σ _ => LevelHom σ
  | .slot _ _ _ _ _ _ σ _ => LevelHom σ
  | .observation _ _ _ _ _ _ σ _ => LevelHom σ
  | .obsPair _ _ _ θ _ => LevelHom θ

/-- **FROZEN CONTROL (Q267).** `P2Query.Routed` over the free-`u` `RoutedDispFree`; the
    routed witness `DemandFree.issued` took from its caller. -/
def P2Query.RoutedFree {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop
  | .es (E := E) (n := n) (Γ := Γ) _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .cl (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .eut (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .cts (E := E) (n := n) (Γ := Γ) _ _ _ ρ => RoutedDispFree id E n Γ ρ
  | .pb (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .bitCoh (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .mixed (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .head (E := E) (n := n) (Γ := Γ) _ _ _ _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .slot (E := E) (n := n) (Γ := Γ) _ _ _ _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .observation (E := E) (n := n) (Γ := Γ) _ _ _ _ _ _ σ ρ => RoutedDispFree σ E n Γ ρ
  | .obsPair (E := E) (n := n) (Γ := Γ) _ _ _ θ ρ => RoutedDispFree θ E n Γ ρ

/-- The display is routed for the query's own context under its own level map
    (`id` for `cts`). -/
def P2Query.Routed {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop
  | .es (E := E) (n := n) (Γ := Γ) _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .cl (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .eut (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .cts (E := E) (n := n) (Γ := Γ) _ _ _ ρ => RoutedDisp id E n Γ ρ
  | .pb (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .bitCoh (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .mixed (E := E) (n := n) (Γ := Γ) _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .head (E := E) (n := n) (Γ := Γ) _ _ _ _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .slot (E := E) (n := n) (Γ := Γ) _ _ _ _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .observation (E := E) (n := n) (Γ := Γ) _ _ _ _ _ _ σ ρ => RoutedDisp σ E n Γ ρ
  | .obsPair (E := E) (n := n) (Γ := Γ) _ _ _ θ ρ => RoutedDisp θ E n Γ ρ

/-! ## The payload forest, the site, and original occurrences -/

/-- The payload forest of a query: its actual derivations as `DNode`s, in
    constructor order. Occurrence paths (`P2Query.subAt`) are read in it. -/
def P2Query.payload {Eₐ : ResolvedEnv} : P2Query Eₐ → List DNode
  | .es h _ _ _ => [.cv h]
  | .cl D₁ D₂ _ _ _ => [.ty D₁, .ty D₂]
  | .eut D₁ D₂ _ _ _ => [.ty D₁, .ty D₂]
  | .cts h DX _ _ => [.cv h, .ty DX]
  | .pb D DT _ _ _ => [.ty D, .ty DT]
  | .bitCoh D₁ D₂ _ _ _ => [.ty D₁, .ty D₂]
  | .mixed D₁ D₂ _ _ _ => [.ty D₁, .ty D₂]
  | .head c _ _ dL dR _ _ _ => [.cv c, .ty dL, .ty dR]
  | .slot _ _ _ dSlot _ _ _ _ => [.ty dSlot]
  | .observation D _ _ _ _ _ _ _ => [.ty D]
  | .obsPair D₁ D₂ _ _ _ => [.ty D₁, .ty D₂]

/-- The original occurrence at `(k, p)` of a query: payload node `k`, child path
    `p` — `DNode.subAt`, the landed K1 occurrence receipt (`RcicSynSlotKind`). A
    freshly built judgment is never at such a position. -/
def P2Query.subAt {Eₐ : ResolvedEnv} (q : P2Query Eₐ) (k : Nat) (p : List Nat) : Option DNode :=
  (q.payload[k]?).bind (·.subAt p)

/-- The site of a query: the context its derivations live in, its frame, the
    level map actually applied (`id` for `cts`), and its display. A sub-request
    "at the same site" reuses all of these. -/
structure Site (Eₐ : ResolvedEnv) : Type where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  E₀ : ResolvedEnv
  n₀ : Nat
  Γ₀ : LCtx
  S : ScopedCtx Eₐ E₀ n₀ Γ₀
  σ : Level → Level
  ρ : List Disp

/-- The site, read off the constructor. -/
def P2Query.site {Eₐ : ResolvedEnv} : P2Query Eₐ → Site Eₐ
  | .es (E := E) (n := n) (Γ := Γ) _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .cl (E := E) (n := n) (Γ := Γ) _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .eut (E := E) (n := n) (Γ := Γ) _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .cts (E := E) (n := n) (Γ := Γ) _ _ S ρ => ⟨E, n, Γ, _, _, _, S, id, ρ⟩
  | .pb (E := E) (n := n) (Γ := Γ) _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .bitCoh (E := E) (n := n) (Γ := Γ) _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .mixed (E := E) (n := n) (Γ := Γ) _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .head (E := E) (n := n) (Γ := Γ) _ _ _ _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .slot (E := E) (n := n) (Γ := Γ) _ _ _ _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .observation (E := E) (n := n) (Γ := Γ) _ _ _ _ _ S σ ρ => ⟨E, n, Γ, _, _, _, S, σ, ρ⟩
  | .obsPair (E := E) (n := n) (Γ := Γ) _ _ S θ ρ => ⟨E, n, Γ, _, _, _, S, θ, ρ⟩

/-- A same-site `es` request. -/
@[reducible] def Site.es {Eₐ : ResolvedEnv} (s : Site Eₐ) {a b T : Expr Nat}
    (h : CvP s.E s.n s.Γ a b T) : P2Query Eₐ := .es h s.S s.σ s.ρ
/-- A same-site `cl` request. -/
@[reducible] def Site.cl {Eₐ : ResolvedEnv} (s : Site Eₐ) {e T₁ T₂ : Expr Nat}
    (D₁ : TyP s.E s.n s.Γ e T₁) (D₂ : TyP s.E s.n s.Γ e T₂) : P2Query Eₐ := .cl D₁ D₂ s.S s.σ s.ρ
/-- A same-site `eut` request. -/
@[reducible] def Site.eut {Eₐ : ResolvedEnv} (s : Site Eₐ) {e T₁ T₂ : Expr Nat}
    (D₁ : TyP s.E s.n s.Γ e T₁) (D₂ : TyP s.E s.n s.Γ e T₂) : P2Query Eₐ := .eut D₁ D₂ s.S s.σ s.ρ
/-- A same-site `pb` request. -/
@[reducible] def Site.pb {Eₐ : ResolvedEnv} (s : Site Eₐ) {e T : Expr Nat} {u : Level}
    (D : TyP s.E s.n s.Γ e T) (DT : TyP s.E s.n s.Γ T (.sort u)) : P2Query Eₐ := .pb D DT s.S s.σ s.ρ
/-- A same-site `bitCoh` request. -/
@[reducible] def Site.bitCoh {Eₐ : ResolvedEnv} (s : Site Eₐ) {T : Expr Nat} {u v : Level}
    (D₁ : TyP s.E s.n s.Γ T (.sort u)) (D₂ : TyP s.E s.n s.Γ T (.sort v)) : P2Query Eₐ :=
  .bitCoh D₁ D₂ s.S s.σ s.ρ
/-- A same-site `head` request with the kind sources **bound to the path's
    endpoints**: `c : A ≡ B`, `dL` types `A`, `dR` types `B`. -/
@[reducible] def Site.head {Eₐ : ResolvedEnv} (s : Site Eₐ) {A B : Expr Nat} {u uL uR : Level}
    (c : CvP s.E s.n s.Γ A B (.sort u)) (dL : TyP s.E s.n s.Γ A (.sort uL))
    (dR : TyP s.E s.n s.Γ B (.sort uR)) : P2Query Eₐ := .head c uL uR dL dR s.S s.σ s.ρ

/-- A routed query's site display is routed for its site context. -/
theorem P2Query.routed_site {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (h : q.Routed) :
    RoutedDisp q.site.σ q.site.E q.site.n q.site.Γ q.site.ρ := by
  cases q <;> exact h

/-- A hom query's site level map is a `LevelHom` (`id` for `cts`). -/
theorem P2Query.hom_site {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (h : q.Hom) : LevelHom q.site.σ := by
  cases q <;> first | exact h | exact levelHom_id

/-! ## The original context-entry decoder (Q269 P2, `pb_letValue`) -/

/-- **The original receipt decoder** (`BELOWC_DEMAND_GRAMMAR_CONTINUATION` §6.1
    `CtxEntrySel := hereLet | throughAssumption tail | throughLet tail`, as a relation
    indexed by the retained native receipt itself). `LetEntryAt hΓ i hΓ' hA hv` holds
    exactly when the entry at depth `i` of the context receipt `hΓ : CtxWfT E n Γ` IS a
    `letBinding` node whose tail receipt, stored-type typing and stored-value typing are
    `hΓ'`, `hA`, `hv` — read off that node, never supplied from outside. -/
inductive LetEntryAt {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → CtxWfT E n Γ → Nat →
    {Γ' : LCtx} → {A₀ : Expr Nat} → {u₀ : Level} → {v₀ : Expr Nat} →
    CtxWfT E n Γ' → HasTyT E n Γ' A₀ (.sort u₀) → HasTyT E n Γ' v₀ A₀ → Prop where
  | hereLet {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
      (hΓ' : CtxWfT E n Γ') (hA : HasTyT E n Γ' A₀ (.sort u₀)) (hv : HasTyT E n Γ' v₀ A₀) :
      LetEntryAt (.letBinding Γ' A₀ u₀ v₀ hΓ' hA hv) 0 hΓ' hA hv
  | throughAssumption {Γ : LCtx} {A : Expr Nat} {u : Level} {hΓ : CtxWfT E n Γ}
      (hA' : HasTyT E n Γ A (.sort u)) {i : Nat}
      {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
      {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀} :
      LetEntryAt hΓ i hΓ' hA hv → LetEntryAt (.assumption Γ A u hΓ hA') (i + 1) hΓ' hA hv
  | throughLet {Γ : LCtx} {A : Expr Nat} {u : Level} {v : Expr Nat} {hΓ : CtxWfT E n Γ}
      (hA' : HasTyT E n Γ A (.sort u)) (hv' : HasTyT E n Γ v A) {i : Nat}
      {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
      {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀} :
      LetEntryAt hΓ i hΓ' hA hv → LetEntryAt (.letBinding Γ A u v hΓ hA' hv') (i + 1) hΓ' hA hv

/-- The selected tail is the receipt's context after the entry: `Γ.drop (i + 1) = Γ'`. -/
theorem LetEntryAt.drop_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {hΓ : CtxWfT E n Γ} {i : Nat}
    {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
    {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀}
    (h : LetEntryAt hΓ i hΓ' hA hv) : Γ.drop (i + 1) = Γ' := by
  induction h with
  | hereLet _ _ _ => rfl
  | throughAssumption _ _ ih => exact ih
  | throughLet _ _ _ ih => exact ih

/-- The selected tail is strictly shorter than the receipt's context (the rank edge of
    the let-value `pb` request: a strict original-receipt suffix). -/
theorem LetEntryAt.length_lt {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {hΓ : CtxWfT E n Γ} {i : Nat}
    {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
    {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀}
    (h : LetEntryAt hΓ i hΓ' hA hv) : Γ'.length < Γ.length := by
  induction h with
  | hereLet _ _ _ => exact Nat.lt_succ_self _
  | throughAssumption _ _ ih => exact Nat.lt_trans ih (Nat.lt_succ_self _)
  | throughLet _ _ _ ih => exact Nat.lt_trans ih (Nat.lt_succ_self _)

/-- The tail scope of a retained receipt at a selected entry: the same environment receipt
    and ambient inclusion, the selected tail context receipt. -/
def ScopedCtx.tail {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ)
    {Γ' : LCtx} (hΓ' : CtxWfT E n Γ') : ScopedCtx Eₐ E n Γ' :=
  ⟨S.env, S.ext, hΓ'⟩

/-! ## Issuance: the answer-free edge -/

/-- **Issuance (Q267 repair).** `Issues issuer q`: the issuing query actually
    issues `q`. One constructor per request row of the design tables (S15 §7–8,
    S9, S16 §2, S7 T12): the row names the issuer's constructor and the field slot
    the target's objects are read from; the frame `S` is kept (or, for the let-value
    `pb` edge, moved to the prefix frame certified by `Γ.drop (i+1) = Γ₀`); the
    display is kept or routed across the binder / transport actually crossed; the
    `cts`/`bitCoh` rows are the consumers' finite original ports; the let-value `pb`
    edge reads the frame receipt's own `letBinding` node; the δ observation rows
    observe the receipt's own admission derivation at one position each; the
    `head` legs bind both kind sources to the conversion's endpoints; the
    occurrence rows `occ_*` issue same-site requests over nodes at `DNode.subAt`
    paths of the issuer's payload. Nothing here is an answer, a view, or a
    caller-presented proposition; `AssumpPref`/`LevelHom`/`RoutedDisp` of every
    target are theorems below (`Issues.ap/hom/routed`). -/
inductive Issues {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  -- §A rule nodes of `.es` (S15 §8): endpoint `CL`s, sub-conversion `ES`s
  | refl_cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {ht dl dr : TyP E n Γ a A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.refl E n Γ a A ht dl dr) S σ ρ) (.cl dl dr S σ ρ)
  | symm_es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat} {h : CvP E n Γ a b A}
      {dl : TyP E n Γ b A} {dr : TyP E n Γ a A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.symm E n Γ a b A h dl dr) S σ ρ) (.es h S σ ρ)
  | symm_clL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat} {h : CvP E n Γ a b A}
      {dl : TyP E n Γ b A} {dr : TyP E n Γ a A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.symm E n Γ a b A h dl dr) S σ ρ) (.cl dl h.dr S σ ρ)
  | symm_clR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat} {h : CvP E n Γ a b A}
      {dl : TyP E n Γ b A} {dr : TyP E n Γ a A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.symm E n Γ a b A h dl dr) S σ ρ) (.cl h.dl dr S σ ρ)
  | trans_es1 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
      {h1 : CvP E n Γ a b A} {h2 : CvP E n Γ b c A} {dl : TyP E n Γ a A} {dr : TyP E n Γ c A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) (.es h1 S σ ρ)
  | trans_es2 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
      {h1 : CvP E n Γ a b A} {h2 : CvP E n Γ b c A} {dl : TyP E n Γ a A} {dr : TyP E n Γ c A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) (.es h2 S σ ρ)
  | trans_clL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
      {h1 : CvP E n Γ a b A} {h2 : CvP E n Γ b c A} {dl : TyP E n Γ a A} {dr : TyP E n Γ c A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) (.cl dl h1.dl S σ ρ)
  | trans_clM {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
      {h1 : CvP E n Γ a b A} {h2 : CvP E n Γ b c A} {dl : TyP E n Γ a A} {dr : TyP E n Γ c A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) (.cl h1.dr h2.dl S σ ρ)
  | trans_clR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
      {h1 : CvP E n Γ a b A} {h2 : CvP E n Γ b c A} {dl : TyP E n Γ a A} {dr : TyP E n Γ c A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) (.cl h2.dr dr S σ ρ)
  | tyConv_es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      {h : CvP E n Γ a b A} {hA : CvP E n Γ A A' (.sort u)} {dl : TyP E n Γ a A'} {dr : TyP E n Γ b A'}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.tyConv E n Γ a b A A' u h hA dl dr) S σ ρ) (.es h S σ ρ)
  | tyConv_clL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      {h : CvP E n Γ a b A} {hA : CvP E n Γ A A' (.sort u)} {dl : TyP E n Γ a A'} {dr : TyP E n Γ b A'}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.tyConv E n Γ a b A A' u h hA dl dr) S σ ρ) (.cl dl h.dl S σ ρ)
  | tyConv_clR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      {h : CvP E n Γ a b A} {hA : CvP E n Γ A A' (.sort u)} {dl : TyP E n Γ a A'} {dr : TyP E n Γ b A'}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.tyConv E n Γ a b A A' u h hA dl dr) S σ ρ) (.cl h.dr dr S σ ρ)
  /-- the inner index against the outer sort (S15 §8 tyConv; S7 T12): the kind
      sources are the natural sorts `(h.dl).reg` of `A` and `dl.reg` of `A'`, the
      path is the node's own `hA : A ≡ A'`. -/
  | tyConv_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
      {h : CvP E n Γ a b A} {hA : CvP E n Γ A A' (.sort u)} {dl : TyP E n Γ a A'} {dr : TyP E n Γ b A'}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.tyConv E n Γ a b A A' u h hA dl dr) S σ ρ)
        (.head hA (h.dl).reg.1 dl.reg.1 (h.dl).reg.2 dl.reg.2 S σ ρ)
  | irr_pbL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P p q : Expr Nat}
      {hP : TyP E n Γ P (.sort .zero)} {hp : TyP E n Γ p P} {hq : TyP E n Γ q P}
      {dl : TyP E n Γ p P} {dr : TyP E n Γ q P}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.irr E n Γ P p q hP hp hq dl dr) S σ ρ) (.pb dl hP S σ ρ)
  | irr_pbR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P p q : Expr Nat}
      {hP : TyP E n Γ P (.sort .zero)} {hp : TyP E n Γ p P} {hq : TyP E n Γ q P}
      {dl : TyP E n Γ p P} {dr : TyP E n Γ q P}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.irr E n Γ P p q hP hp hq dl dr) S σ ρ) (.pb dr hP S σ ρ)
  | sorts_clL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l₁ l₂ : Level} {hl : eqN l₁ l₂}
      {dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁))} {dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁))}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.sorts E n Γ l₁ l₂ hl dl dr) S σ ρ) (.cl dl (sortNode E n Γ l₁) S σ ρ)
  | sorts_clR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l₁ l₂ : Level} {hl : eqN l₁ l₂}
      {dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁))} {dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁))}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.sorts E n Γ l₁ l₂ hl dl dr) S σ ρ) (.cl dr (sortNode E n Γ l₂) S σ ρ)
  | iota_pbL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
      {w : DerivedIota E lhs rhs} {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
      {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) (.pb dl hlhs.reg.2 S σ ρ)
  | iota_pbR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
      {w : DerivedIota E lhs rhs} {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
      {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) (.pb dr hlhs.reg.2 S σ ρ)
  | delta_cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
        (.cl hb dr S σ ρ)
  /-- **the δ admission observation, one OUT position (Q269 repair; S4
      `obsLvlEq_eps_delta`, S7 T3).** The observed derivation is the ACTUAL admission of
      `r` the frame's own receipt selects — `((enrichEnvWfT S.env).defAdm hres hbody htr).hv`,
      the landed `DefAdm` lineage (`AdmObsPlan.Db_eq`) — never `hb`, `dr`, or any same-judgment
      substitute; the frame's environment is the node's (`S : ScopedCtx Eₐ E n₀ Γ₀`). The
      comparison maps are the δ-exchange maps `instLevel (ls.map σ)` / `fun l => σ (instLevel
      ls l)`; the position `k` is an actual entry `l` of `Db.outLevels id`. **Answer-free
      (Q270, fable-step ITEM 5):** the row carries no `ObsCert` and no supply guard — every
      actual position is issued, and its `eqN` is owed by the `StepSuppliers.delta_obs`
      field (a supplier may route it through the S7 §3 certificates inside its proof; a
      position no route supplies, `PendingActualObservation`, is exactly
      W-TABLE-DELTA-OBSERVATION-STABILITY). The ITEM 4 shape — the certificate as a row
      premise — is not kept: it read the answer off the demand
      (BELOWC_OBSERVATION_REQUESTS.md §1.4). -/
  | delta_obs_out {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
      {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
      {k : Nat} {l : Level}
      (hk : (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = some l)
      (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref) :
      Issues (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
        (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
          (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) (.out k) S σ [])
  /-- the δ admission observation, one GATE position (same selection, same maps, same
      answer-free issuance; the bit equation is owed by `StepSuppliers.delta_obs`). -/
  | delta_obs_gate {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
      {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
      {k : Nat} {l : Level}
      (hk : (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l)
      (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref) :
      Issues (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
        (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
          (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) (.gate k) S σ [])
  | lit_cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
      {hlit : LiteralExpansion t exp} {hexp : TyP E n Γ exp T}
      {dl : TyP E n Γ (.lit t) T} {dr : TyP E n Γ exp T}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) (.cl hexp dr S σ ρ)
  | eta_cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat} {hf : TyP E n Γ f (.pi A B)}
      {dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)} {dr : TyP E n Γ f (.pi A B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) (.cl hf dr S σ ρ)
  /-- the stored value's `PB` at the node's own `hA` (S15 §8 ζ, S16 §2.3). -/
  | zeta_pb {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
      {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
      {hb : TyP E n (.letBinding A value :: Γ) body B}
      {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
      {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) (.pb hv hA S σ ρ)
  | zetaLocal_cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
      {hval : lookupValue Γ i = some v} {hty : lookupType Γ i = some A} {hv : TyP E n Γ v A}
      {dl : TyP E n Γ (.bvar i) A} {dr : TyP E n Γ v A}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) (.cl hv dr S σ ρ)
  | app_es1 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
      {h1 : CvP E n Γ f g (.pi A B)} {h2 : CvP E n Γ a b A}
      {dl : TyP E n Γ (.app f a) (instantiate0 a B)} {dr : TyP E n Γ (.app g b) (instantiate0 a B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) (.es h1 S σ ρ)
  | app_es2 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
      {h1 : CvP E n Γ f g (.pi A B)} {h2 : CvP E n Γ a b A}
      {dl : TyP E n Γ (.app f a) (instantiate0 a B)} {dr : TyP E n Γ (.app g b) (instantiate0 a B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) (.es h2 S σ ρ)
  | lam_esA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hb : CvP E n (.assumption A :: Γ) b b' B}
      {dl : TyP E n Γ (.lam A b) (.pi A B)} {dr : TyP E n Γ (.lam A' b') (.pi A B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) (.es hA S σ ρ)
  /-- the body one binder up, at the binder's display (S15 §6, `binder_body_before`). -/
  | lam_esB {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hb : CvP E n (.assumption A :: Γ) b b' B}
      {dl : TyP E n Γ (.lam A b) (.pi A B)} {dr : TyP E n Γ (.lam A' b') (.pi A B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        (.es hb S σ (binderDisp (levelIsZero (σ u)) :: ρ))
  | pi_esA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hB : CvP E n (.assumption A :: Γ) B B' (.sort v)}
      {dl : TyP E n Γ (.pi A B) (.sort (.imax u v))} {dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) (.es hA S σ ρ)
  | pi_esB {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hB : CvP E n (.assumption A :: Γ) B B' (.sort v)}
      {dl : TyP E n Γ (.pi A B) (.sort (.imax u v))} {dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)
        (.es hB S σ (binderDisp (levelIsZero (σ u)) :: ρ))
  | letE_esA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
      {hb : CvP E n (.letBinding A v :: Γ) b b' B}
      {dl : TyP E n Γ (.letE A v b) (instantiate0 v B)} {dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) (.es hA S σ ρ)
  | letE_esV {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
      {hb : CvP E n (.letBinding A v :: Γ) b b' B}
      {dl : TyP E n Γ (.letE A v b) (instantiate0 v B)} {dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) (.es hv S σ ρ)
  /-- the body one let-binder up at the `drop` view (the value erases to `star`). -/
  | letE_esB_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
      {hb : CvP E n (.letBinding A v :: Γ) b b' B}
      {dl : TyP E n Γ (.letE A v b) (instantiate0 v B)} {dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} (hvs : hv.dl.eps σ ρ = .star) :
      Issues (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) (.es hb S σ (.drop :: ρ))
  /-- the body one let-binder up at the `inline` view. -/
  | letE_esB_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
      {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
      {hb : CvP E n (.letBinding A v :: Γ) b b' B}
      {dl : TyP E n Γ (.letE A v b) (instantiate0 v B)} {dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        (.es hb S σ (.inline (hv.dl.eps σ ρ) :: ρ))
  | fsub_es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B Sx a b : Expr Nat} {u : Level}
      {hB : TyP E n (.assumption A :: Γ) B Sx} {hA : TyP E n Γ A (.sort u)} {hab : CvP E n Γ a b A}
      {dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx)}
      {dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) (.es hab S σ ρ)
  -- §B transports: the child at the parent's transformed display (S15 §7)
  | wk_es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} {d : LocalDecl} {c : Nat}
      {h : CvP E n Γ a b T}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.wk E n Γ a b T d c h) S σ ρ) (.es h S σ (removeAt ρ c))
  | esub_es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T t v : Expr Nat} {j : Nat} {u : Level}
      {h : CvP E n Γ a b T} {hget : Γ[j]? = some (.assumption t)}
      {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
      {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.esub E n Γ a b T t v j u h hget hv hvT) S σ ρ)
        (.es h S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
  | linst_es {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {a b T : Expr Nat} {ls : List Level}
      {hls : levelsBounded n ls = true} {hlen : ls.length = a'} {h : CvP E a' Γ a b T}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.linst E a' n Γ a b T ls hls hlen h) S σ ρ)
        (.es h S (fun l => σ (instLevel ls l)) ρ)
  | ewk_es {Eₚ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} {hext : EnvExt Eₚ E}
      {h : CvP Eₚ n Γ a b T}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.ewk Eₚ E n Γ a b T hext h) S σ ρ) (.es h S σ ρ)
  | cctx_es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T A A' : Expr Nat} {u : Level}
      {h : CvP E n (.assumption A :: Γ) a b T} {hA : CvP E n Γ A A' (.sort u)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.es (CvP.cctx E n Γ a b T A A' u h hA) S σ ρ) (.es h S σ ρ)
  -- §C the `cts` / `bitCoh` ports (Q269 repair): exactly the finite original operands
  -- the landed consumers read — `cts_of_eut_cl` (the `EUT` of `h.dl` against `DX`, the
  -- reg-`CL` of `h.dl` at `sortNode w`, the reg-`CL` of `DX` at `sortNode s`) and
  -- `bitCoh_of_eut_cl` (the reg-`CL`s of `D₁`/`D₂`); a sort/Π-headed `reg` needs no
  -- request (`cl_reg_sort_of_isSortOrPiHead`), so those rows are issued only when the
  -- operand is not sort/Π-headed. Never a fresh same-context pair.
  | cts_eut_dlX {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
      {h : CvP E n Γ X Y (.sort w)} {DX : TyP E n Γ X (.sort s)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {ρ : List Disp} :
      Issues (.cts h DX S ρ) (.eut h.dl DX S id ρ)
  | cts_cl_regL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
      {h : CvP E n Γ X Y (.sort w)} {DX : TyP E n Γ X (.sort s)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {ρ : List Disp} :
      Issues (.cts h DX S ρ) (.cl h.dl.reg.2 (sortNode E n Γ w) S id ρ)
  | cts_cl_regX {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
      {h : CvP E n Γ X Y (.sort w)} {DX : TyP E n Γ X (.sort s)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {ρ : List Disp}
      (hs : DX.isSortOrPiHead = false) :
      Issues (.cts h DX S ρ) (.cl DX.reg.2 (sortNode E n Γ s) S id ρ)
  | bitCoh_cl_regL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
      {D₁ : TyP E n Γ T (.sort u)} {D₂ : TyP E n Γ T (.sort v)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} (hs : D₁.isSortOrPiHead = false) :
      Issues (.bitCoh D₁ D₂ S σ ρ) (.cl D₁.reg.2 (sortNode E n Γ u) S σ ρ)
  | bitCoh_cl_regR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
      {D₁ : TyP E n Γ T (.sort u)} {D₂ : TyP E n Γ T (.sort v)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} (hs : D₂.isSortOrPiHead = false) :
      Issues (.bitCoh D₁ D₂ S σ ρ) (.cl D₂.reg.2 (sortNode E n Γ v) S σ ρ)
  /-- the same pair's `EUT` at the same rank (S9 §5: a local data dependency). -/
  | bitCoh_eut {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
      {D₁ : TyP E n Γ T (.sort u)} {D₂ : TyP E n Γ T (.sort v)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.bitCoh D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ)
  -- §D the moved pair (S17): the same objects, same rank
  | cl_mixed {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.cl D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ)
  | eut_mixed {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.eut D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ)
  -- §E the landed `pb` edges (`RcicSynRouteSlot`, S16 §2)
  /-- the bvar's actual `hA` against `DT` (`bvar_bit_request_below`). -/
  | pb_bvar_bitCoh {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u s : Level}
      {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)} {DT : TyP E n Γ A (.sort s)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) (.bitCoh hA DT S σ ρ)
  /-- **the let-value `PB` at the prefix frame (Q269 repair; `slot_value_request_below`,
      S16 §2.3).** The derivation's context extends the issuer's frame by `k` binders
      (`Γ.drop k = Γ₀`); the entry read is the frame receipt's own `letBinding` node at depth
      `i` (`LetEntryAt S.ctx i hΓ' hA hv` — the §6.1 `CtxEntrySel` decoder, indexed by the
      receipt itself), so the issued `PB` is of that node's stored value typing against its
      stored type typing (both enriched by the frame's `EnvWfT`), at the node's tail scope
      `S.tail hΓ'` with its canonical display: no separately accepted scope, typing witness
      or route. The frame's environment is the derivation's. `AssumpPref` of the enriched
      witnesses is a side condition (no `EnvWfT`-fronted `AssumpPref` lemma for
      `enrichHasTyT_of_envWfT` is on the tree). -/
  | pb_letValue {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
      {D : TyP E n Γ e T} {DT : TyP E n Γ T (.sort s)}
      {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n Γ₀} {σ : Level → Level} {ρ : List Disp}
      {k i : Nat} (hframe : Γ.drop k = Γ₀)
      {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
      {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀}
      (hsel : LetEntryAt S.ctx i hΓ' hA hv)
      (hapA : (enrichHasTyT_of_envWfT S.env hΓ' hA).AssumpPref)
      (hapv : (enrichHasTyT_of_envWfT S.env hΓ' hv).AssumpPref) :
      Issues (.pb D DT S σ ρ)
        (.pb (enrichHasTyT_of_envWfT S.env hΓ' hv) (enrichHasTyT_of_envWfT S.env hΓ' hA)
          (S.tail hΓ') σ ((S.tail hΓ').can σ))
  -- §F the `head` legs (S7 T12 `KindTrace.edge`): same-subject `BitCoh` at each
  -- endpoint of the path, the sources bound to the endpoints
  | head_legL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {u uL uR : Level}
      {c : CvP E n Γ A A' (.sort u)} {dL : TyP E n Γ A (.sort uL)} {dR : TyP E n Γ A' (.sort uR)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.head c uL uR dL dR S σ ρ) (.bitCoh dL c.dl S σ ρ)
  | head_legR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {u uL uR : Level}
      {c : CvP E n Γ A A' (.sort u)} {dL : TyP E n Γ A (.sort uL)} {dR : TyP E n Γ A' (.sort uR)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      Issues (.head c uL uR dL dR S σ ρ) (.bitCoh c.dr dR S σ ρ)
  -- §G same-site occurrence rows: the target's objects sit at `DNode.subAt` paths
  -- of the issuer's payload, in the issuer's own context, at the issuer's site
  | occ_es {q : P2Query Eₐ} {k : Nat} {p : List Nat} {a b T : Expr Nat}
      {h : CvP q.site.E q.site.n q.site.Γ a b T}
      (hocc : q.subAt k p = some (.cv h)) (hap : h.AssumpPref) : Issues q (q.site.es h)
  | occ_cl {q : P2Query Eₐ} {k₁ k₂ : Nat} {p₁ p₂ : List Nat} {e T₁ T₂ : Expr Nat}
      {D₁ : TyP q.site.E q.site.n q.site.Γ e T₁} {D₂ : TyP q.site.E q.site.n q.site.Γ e T₂}
      (h₁ : q.subAt k₁ p₁ = some (.ty D₁)) (h₂ : q.subAt k₂ p₂ = some (.ty D₂))
      (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) : Issues q (q.site.cl D₁ D₂)
  | occ_eut {q : P2Query Eₐ} {k₁ k₂ : Nat} {p₁ p₂ : List Nat} {e T₁ T₂ : Expr Nat}
      {D₁ : TyP q.site.E q.site.n q.site.Γ e T₁} {D₂ : TyP q.site.E q.site.n q.site.Γ e T₂}
      (h₁ : q.subAt k₁ p₁ = some (.ty D₁)) (h₂ : q.subAt k₂ p₂ = some (.ty D₂))
      (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) : Issues q (q.site.eut D₁ D₂)
  | occ_pb {q : P2Query Eₐ} {k₁ k₂ : Nat} {p₁ p₂ : List Nat} {e T : Expr Nat} {u : Level}
      {D : TyP q.site.E q.site.n q.site.Γ e T} {DT : TyP q.site.E q.site.n q.site.Γ T (.sort u)}
      (h₁ : q.subAt k₁ p₁ = some (.ty D)) (h₂ : q.subAt k₂ p₂ = some (.ty DT))
      (hap₁ : D.AssumpPref) (hap₂ : DT.AssumpPref) : Issues q (q.site.pb D DT)
  | occ_bitCoh {q : P2Query Eₐ} {k₁ k₂ : Nat} {p₁ p₂ : List Nat} {T : Expr Nat} {u v : Level}
      {D₁ : TyP q.site.E q.site.n q.site.Γ T (.sort u)} {D₂ : TyP q.site.E q.site.n q.site.Γ T (.sort v)}
      (h₁ : q.subAt k₁ p₁ = some (.ty D₁)) (h₂ : q.subAt k₂ p₂ = some (.ty D₂))
      (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) : Issues q (q.site.bitCoh D₁ D₂)
  /-- a `TyP.conv` node at a path: the path is its own `c : A ≡ B`, the sources are
      the natural sort `D.reg` of `A` and the index's `c.dr` of `B` (S7 T12 K3, S16
      §2 conv) — never independent kind sources. -/
  | occ_head {q : P2Query Eₐ} {k : Nat} {p : List Nat} {e A B : Expr Nat} {u : Level}
      {D : TyP q.site.E q.site.n q.site.Γ e A} {c : CvP q.site.E q.site.n q.site.Γ A B (.sort u)}
      (hocc : q.subAt k p = some (.ty (TyP.conv q.site.E q.site.n q.site.Γ e A B u D c)))
      (hapD : D.AssumpPref) (hapc : c.AssumpPref) : Issues q (q.site.head c D.reg.2 c.dr)

/-- Every issued query's derivations are `AssumpPref` once the issuer's are. -/
theorem Issues.ap {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.AP) (e : Issues q q') : q'.AP := by
  cases e with
  | refl_cl => obtain ⟨_, hdl, hdr⟩ := hi; exact ⟨hdl, hdr⟩
  | symm_es => obtain ⟨hh, _, _⟩ := hi; exact hh
  | symm_clL => obtain ⟨hh, hdl, _⟩ := hi; exact ⟨hdl, assumpPref_dr hh⟩
  | symm_clR => obtain ⟨hh, _, hdr⟩ := hi; exact ⟨assumpPref_dl hh, hdr⟩
  | trans_es1 => obtain ⟨h1, _, _, _⟩ := hi; exact h1
  | trans_es2 => obtain ⟨_, h2, _, _⟩ := hi; exact h2
  | trans_clL => obtain ⟨h1, _, hdl, _⟩ := hi; exact ⟨hdl, assumpPref_dl h1⟩
  | trans_clM => obtain ⟨h1, h2, _, _⟩ := hi; exact ⟨assumpPref_dr h1, assumpPref_dl h2⟩
  | trans_clR => obtain ⟨_, h2, _, hdr⟩ := hi; exact ⟨assumpPref_dr h2, hdr⟩
  | tyConv_es => obtain ⟨hh, _, _, _⟩ := hi; exact hh
  | tyConv_clL => obtain ⟨hh, _, hdl, _⟩ := hi; exact ⟨hdl, assumpPref_dl hh⟩
  | tyConv_clR => obtain ⟨hh, _, _, hdr⟩ := hi; exact ⟨assumpPref_dr hh, hdr⟩
  | tyConv_head =>
      obtain ⟨hh, hhA, hdl, _⟩ := hi
      exact ⟨hhA, assumpPref_reg (assumpPref_dl hh), assumpPref_reg hdl⟩
  | irr_pbL => obtain ⟨hP, _, _, hdl, _⟩ := hi; exact ⟨hdl, hP⟩
  | irr_pbR => obtain ⟨hP, _, _, _, hdr⟩ := hi; exact ⟨hdr, hP⟩
  | sorts_clL => obtain ⟨hdl, _⟩ := hi; exact ⟨hdl, sortNode_assumpPref⟩
  | sorts_clR => obtain ⟨_, hdr⟩ := hi; exact ⟨hdr, sortNode_assumpPref⟩
  | iota_pbL => obtain ⟨hl, _, hdl, _⟩ := hi; exact ⟨hdl, assumpPref_reg hl⟩
  | iota_pbR => obtain ⟨hl, _, _, hdr⟩ := hi; exact ⟨hdr, assumpPref_reg hl⟩
  | delta_cl => obtain ⟨hb, _, hdr⟩ := hi; exact ⟨hb, hdr⟩
  | delta_obs_out _ hap => exact hap
  | delta_obs_gate _ hap => exact hap
  | lit_cl => obtain ⟨hexp, _, hdr⟩ := hi; exact ⟨hexp, hdr⟩
  | eta_cl => obtain ⟨hf, _, hdr⟩ := hi; exact ⟨hf, hdr⟩
  | zeta_pb => obtain ⟨hA, hv, _, _, _⟩ := hi; exact ⟨hv, hA⟩
  | zetaLocal_cl => obtain ⟨hv, _, hdr⟩ := hi; exact ⟨hv, hdr⟩
  | app_es1 => obtain ⟨h1, _, _, _⟩ := hi; exact h1
  | app_es2 => obtain ⟨_, h2, _, _⟩ := hi; exact h2
  | lam_esA => obtain ⟨hA, _, _, _⟩ := hi; exact hA
  | lam_esB => obtain ⟨_, hb, _, _⟩ := hi; exact hb
  | pi_esA => obtain ⟨hA, _, _, _⟩ := hi; exact hA
  | pi_esB => obtain ⟨_, hB, _, _⟩ := hi; exact hB
  | letE_esA => obtain ⟨hA, _, _, _, _⟩ := hi; exact hA
  | letE_esV => obtain ⟨_, hv, _, _, _⟩ := hi; exact hv
  | letE_esB_drop _ => obtain ⟨_, _, hb, _, _⟩ := hi; exact hb
  | letE_esB_inline => obtain ⟨_, _, hb, _, _⟩ := hi; exact hb
  | fsub_es => obtain ⟨_, _, hab, _, _⟩ := hi; exact hab
  | wk_es => obtain ⟨_, hh⟩ := hi; exact hh
  | esub_es => obtain ⟨_, hh, _, _⟩ := hi; exact hh
  | linst_es => exact hi
  | ewk_es => exact hi
  | cctx_es => obtain ⟨hh, _⟩ := hi; exact hh
  | cts_eut_dlX => obtain ⟨hh, hDX⟩ := hi; exact ⟨assumpPref_dl hh, hDX⟩
  | cts_cl_regL => obtain ⟨hh, _⟩ := hi; exact ⟨assumpPref_reg (assumpPref_dl hh), sortNode_assumpPref⟩
  | cts_cl_regX _ => obtain ⟨_, hDX⟩ := hi; exact ⟨assumpPref_reg hDX, sortNode_assumpPref⟩
  | bitCoh_cl_regL _ => obtain ⟨h₁, _⟩ := hi; exact ⟨assumpPref_reg h₁, sortNode_assumpPref⟩
  | bitCoh_cl_regR _ => obtain ⟨_, h₂⟩ := hi; exact ⟨assumpPref_reg h₂, sortNode_assumpPref⟩
  | bitCoh_eut => exact hi
  | cl_mixed => exact hi
  | eut_mixed => exact hi
  | pb_bvar_bitCoh => obtain ⟨hA, hDT⟩ := hi; exact ⟨hA, hDT⟩
  | pb_letValue _ _ hapA hapv => exact ⟨hapv, hapA⟩
  | head_legL => obtain ⟨hc, hdL, _⟩ := hi; exact ⟨hdL, assumpPref_dl hc⟩
  | head_legR => obtain ⟨hc, _, hdR⟩ := hi; exact ⟨assumpPref_dr hc, hdR⟩
  | occ_es _ hap => exact hap
  | occ_cl _ _ hap₁ hap₂ => exact ⟨hap₁, hap₂⟩
  | occ_eut _ _ hap₁ hap₂ => exact ⟨hap₁, hap₂⟩
  | occ_pb _ _ hap₁ hap₂ => exact ⟨hap₁, hap₂⟩
  | occ_bitCoh _ _ hap₁ hap₂ => exact ⟨hap₁, hap₂⟩
  | occ_head _ hapD hapc => exact ⟨hapc, assumpPref_reg hapD, assumpPref_dr hapc⟩

/-- Every issued query's level map is a `LevelHom` once the issuer's is (`linst`
    composes with `instLevel`; `cts` rows issue at `id`). -/
theorem Issues.hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.Hom) (e : Issues q q') : q'.Hom := by
  cases e <;> first
    | exact hi
    | exact levelHom_id
    | exact LevelHom.linst hi _
    | exact P2Query.hom_site hi

/-- Every issued query's display is routed once the issuer's is: kept at the same
    site, or routed across the binder / transport the row crosses, or the selected
    tail scope's canonical display, or the empty display of the admission's empty
    context. -/
theorem Issues.routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hr : q.Routed) (e : Issues q q') :
    q'.Routed := by
  cases e with
  | @lam_esB E n Γ A A' b b' B u hA hb dl dr E₀ n₀ Γ₀ S σ ρ =>
      exact RoutedDisp.assumption hr hA.dl
  | @pi_esB E n Γ A A' B B' u v hA hB dl dr E₀ n₀ Γ₀ S σ ρ =>
      exact RoutedDisp.assumption hr hA.dl
  | @letE_esB_drop E n Γ A A' v v' b b' B u hA hv hb dl dr E₀ n₀ Γ₀ S σ ρ hvs =>
      exact RoutedDisp.letDrop hr hA.dl hv.dl hvs
  | @letE_esB_inline E n Γ A A' v v' b b' B u hA hv hb dl dr E₀ n₀ Γ₀ S σ ρ =>
      exact RoutedDisp.letInline hr hA.dl hv.dl
  | @wk_es E n Γ a b T d c h E₀ n₀ Γ₀ S σ ρ => exact RoutedDisp.wk d c hr
  | @esub_es E n Γ a b T t v j u h hget hv hvT E₀ n₀ Γ₀ S σ ρ => exact RoutedDisp.esub hget hv hvT hr
  | @linst_es E a' n Γ a b T ls hls hlen h E₀ n₀ Γ₀ S σ ρ => exact RoutedDisp.linst ls hls hlen hr
  | @ewk_es Eₚ E n Γ a b T hext h E₀ n₀ Γ₀ S σ ρ => exact RoutedDisp.ewk hext hr
  | @cctx_es E n Γ a b T A A' u h hA E₀ n₀ Γ₀ S σ ρ => exact RoutedDisp.cctx hA hr
  | pb_letValue _ _ _ _ => exact ScopedCtx.canRouted _ _
  | delta_obs_out _ _ => exact RoutedDisp.canon (CtxP.nil _ _)
  | delta_obs_gate _ _ => exact RoutedDisp.canon (CtxP.nil _ _)
  | _ => first | exact hr | exact P2Query.routed_site hr

/-! ## Demand -/

/-- Membership in the demand domain. A public root is demanded at its own
    scope's canonical display with exactly the side conditions `BelowScoped`'s
    public fields carry (`AssumpPref` of the inputs, `LevelHom σ`); an issued
    query is demanded by an actual issuance edge `Issues issuer q` from a
    demanded issuer — nothing else: no `AlignRequest`, no caller-presented
    `AP`/`Hom`/`Routed` witness (those are theorems of the edge), no `Goal`,
    `ResolvedView`, or worker answer. -/
inductive Demand {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | rootEs {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (h : CvP E n Γ a b T) (hAP : h.AssumpPref) (S : ScopedCtx Eₐ E n Γ)
      (σ : Level → Level) (hσ : LevelHom σ) : Demand (.es h S σ (S.can σ))
  | rootCl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      Demand (.cl D₁ D₂ S σ (S.can σ))
  | rootEut {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      Demand (.eut D₁ D₂ S σ (S.can σ))
  | rootCts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
      (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
      (hAP : h.AssumpPref) (hDX : DX.AssumpPref) (S : ScopedCtx Eₐ E n Γ) :
      Demand (.cts h DX S (S.can id))
  | rootPb {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
      (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (hD : D.AssumpPref) (hDT : DT.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      Demand (.pb D DT S σ (S.can σ))
  | rootBitCoh {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
      (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
      (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      Demand (.bitCoh D₁ D₂ S σ (S.can σ))
  | issued (issuer q : P2Query Eₐ) : Demand issuer → Issues issuer q → Demand q

/-- Every demanded query's derivations are `AssumpPref`. -/
theorem Demand.ap {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : Demand q) : q.AP := by
  induction hq with
  | rootEs _ hAP _ _ _ => exact hAP
  | rootCl _ _ h₁ h₂ _ _ _ => exact ⟨h₁, h₂⟩
  | rootEut _ _ h₁ h₂ _ _ _ => exact ⟨h₁, h₂⟩
  | rootCts _ _ hAP hDX _ => exact ⟨hAP, hDX⟩
  | rootPb _ _ hD hDT _ _ _ => exact ⟨hD, hDT⟩
  | rootBitCoh _ _ h₁ h₂ _ _ _ => exact ⟨h₁, h₂⟩
  | issued _ _ _ e ih => exact Issues.ap ih e

/-- Every demanded query's level map is a `LevelHom`. -/
theorem Demand.hom {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : Demand q) : q.Hom := by
  induction hq with
  | rootEs _ _ _ _ hσ => exact hσ
  | rootCl _ _ _ _ _ _ hσ => exact hσ
  | rootEut _ _ _ _ _ _ hσ => exact hσ
  | rootCts _ _ _ _ _ => exact trivial
  | rootPb _ _ _ _ _ _ hσ => exact hσ
  | rootBitCoh _ _ _ _ _ _ hσ => exact hσ
  | issued _ _ _ e ih => exact Issues.hom ih e

/-- Every demanded query's display is routed. -/
theorem Demand.routed {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : Demand q) : q.Routed := by
  induction hq with
  | rootEs _ _ S σ _ => exact S.canRouted σ
  | rootCl _ _ _ _ S σ _ => exact S.canRouted σ
  | rootEut _ _ _ _ S σ _ => exact S.canRouted σ
  | rootCts _ _ _ _ S => exact S.canRouted id
  | rootPb _ _ _ _ S σ _ => exact S.canRouted σ
  | rootBitCoh _ _ _ _ S σ _ => exact S.canRouted σ
  | issued _ _ _ e ih => exact Issues.routed ih e

/-- **Q267 countermodel 1, rejected.** A demanded `head` query has its kind sources
    bound to the endpoints of its conversion path: `dL` types the path's left
    endpoint, `dR` its right endpoint. The only rows that issue a `head` are
    `tyConv_head` and `occ_head`, both bound; no root is a `head`. -/
theorem Demand.head_bound {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat} {u : Level}
    {A A' : Expr Nat} {uL uR : Level}
    {c : CvP E n Γ a b (.sort u)} {dL : TyP E n Γ A (.sort uL)} {dR : TyP E n Γ A' (.sort uR)}
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {σ : Level → Level} {ρ : List Disp}
    (hq : Demand (.head c uL uR dL dR S σ ρ)) : a = A ∧ b = A' := by
  cases hq with
  | issued _ _ _ e => cases e <;> exact ⟨rfl, rfl⟩

/-- **FROZEN CONTROL — the Q267 shape of issuance (ITEM 2).** The six roots as in
    `Demand`, but `issued` admits any target from any demanded issuer through an
    unindexed `AlignRequest` and caller-presented `AP`/`Hom`/`RoutedFree` witnesses.
    Both Q267 countermodels (`RcicSynStepSkeleton`, namespaces `Q267HeadInjection`
    and `Q267RoutedEsub`) refute the `Step` over it (`no_stepFree`). Not used by
    `Demand`. -/
inductive DemandFree {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | rootEs {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (h : CvP E n Γ a b T) (hAP : h.AssumpPref) (S : ScopedCtx Eₐ E n Γ)
      (σ : Level → Level) (hσ : LevelHom σ) : DemandFree (.es h S σ (S.can σ))
  | rootCl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      DemandFree (.cl D₁ D₂ S σ (S.can σ))
  | rootEut {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      DemandFree (.eut D₁ D₂ S σ (S.can σ))
  | rootCts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
      (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
      (hAP : h.AssumpPref) (hDX : DX.AssumpPref) (S : ScopedCtx Eₐ E n Γ) :
      DemandFree (.cts h DX S (S.can id))
  | rootPb {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
      (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (hD : D.AssumpPref) (hDT : DT.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      DemandFree (.pb D DT S σ (S.can σ))
  | rootBitCoh {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
      (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
      (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
      DemandFree (.bitCoh D₁ D₂ S σ (S.can σ))
  | issued (issuer q : P2Query Eₐ) : DemandFree issuer → AlignRequest →
      q.AP → q.Hom → q.RoutedFree → DemandFree q

/-- **FROZEN CONTROL — the pre-repair demand (finding 2, ITEM 1).** Any public query
    at any `σ`, without `AssumpPref`, and any issued query. Kept only so that
    `step_refuted_const_zero` (`RcicSynStepSkeleton`) can go on refuting the
    `Step` built over it. Not used by `Demand`. -/
inductive DemandWide {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | publicRoot (q : P2Query Eₐ) : q.isPublic = true → DemandWide q
  | issued (issuer q : P2Query Eₐ) : DemandWide issuer → AlignRequest → DemandWide q

/-- **FROZEN CONTROL — the Q269 observation rows (ITEM 3).** `occ_obs` issued the
    two-derivation observation of any two same-site occurrences of the issuer's payload;
    `delta_obs` issued `hb` against `dr` of a δ node. Both target the frozen `obsPair`,
    whose goal zips the two ENTIRE out/gate traversals — refuted by the two Q269
    countermodels (`RcicSynStepSkeleton`, namespaces `Q269ObservationAudit` and
    `Q269DeltaObservationIndependent`). Not used by `Demand`. -/
inductive IssuesObsFree {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | delta_obs {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
      {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesObsFree (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
        (.obsPair hb dr S σ ρ)
  | occ_obs {q : P2Query Eₐ} {k₁ k₂ : Nat} {p₁ p₂ : List Nat} {e T : Expr Nat}
      {D₁ D₂ : TyP q.site.E q.site.n q.site.Γ e T}
      (h₁ : q.subAt k₁ p₁ = some (.ty D₁)) (h₂ : q.subAt k₂ p₂ = some (.ty D₂))
      (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
      IssuesObsFree q (.obsPair D₁ D₂ q.site.S q.site.σ q.site.ρ)

/-- **FROZEN CONTROL (Q269).** The live `Demand` closed under the ITEM 3 observation
    rows. `no_stepObsFree` (`RcicSynStepSkeleton`) refutes the `Step` over it. Not used
    by `Demand`. -/
inductive DemandObsFree {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | live (q : P2Query Eₐ) : Demand q → DemandObsFree q
  | issued (issuer q : P2Query Eₐ) : DemandObsFree issuer → IssuesObsFree issuer q → DemandObsFree q

/-- Pairwise relation over level lists (used only by the frozen `obsPair` goal). -/
def lvlForall2 (R : Level → Level → Prop) : List Level → List Level → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ lvlForall2 R as bs

/-- One individual level observation (S4 §2, S7 T3): at `out k`, the `k`-th recorded
    output level of `D` under the entered composite `θ` has `eqN` images under the two
    comparison maps; at `gate k`, the `k`-th recorded gate level has equal
    `levelIsZero` bits. Exactly one premise of the landed `obsLvlEq_eps`. -/
def ObsGoal {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP E n Γ e T)
    (θ φ ψ : Level → Level) : ObsPos → Prop
  | .out k => ∀ l, (D.outLevels θ)[k]? = some l → eqN (φ l) (ψ l)
  | .gate k => ∀ l, (D.gateLevels θ)[k]? = some l → levelIsZero (φ l) = levelIsZero (ψ l)

/-- The owed semantic answer to `q`, computed from `q` at the query's own
    display — never a caller-presented proposition.

    `mixed` owes the CL and EUT halves of its same-subject pair (the Sort/Bit
    and declared TagCoh obligations ride the query's declared view; they are
    not silently discharged here). `head` owes the bit equation of the two
    domain-kind sources. `slot` owes the bit equation of the actual slot sort
    and the instantiated declared sort. `observation` owes ONE level observation of
    ONE derivation at ONE position (`ObsGoal`). The frozen `obsPair` keeps the ITEM 3
    goal — the two ENTIRE traversals zipped positionally — only so the Q269
    countermodels stay measurable against it. -/
def Goal (tbl : List CRule) {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop
  | .es h _ σ ρ => ES tbl σ ρ h
  | .cl D₁ D₂ _ σ ρ => CL tbl σ ρ D₁ D₂
  | .eut D₁ D₂ _ σ ρ => EUT tbl σ ρ D₁ D₂
  | .cts h DX _ _ => CTS h DX
  | .pb D DT _ σ ρ => PBit σ ρ D DT
  | .bitCoh D₁ D₂ _ σ _ => BitCoh σ D₁ D₂
  | .mixed D₁ D₂ _ σ ρ => CL tbl σ ρ D₁ D₂ ∧ EUT tbl σ ρ D₁ D₂
  | .head _ uL uR _ _ _ σ _ => levelIsZero (σ uL) = levelIsZero (σ uR)
  | .slot u uD _ _ ls _ σ _ => levelIsZero (σ u) = levelIsZero (σ (instLevel ls uD))
  | .observation D θ φ ψ pos _ _ _ => ObsGoal D θ φ ψ pos
  | .obsPair D₁ D₂ _ θ _ =>
      lvlForall2 eqN (D₁.outLevels θ) (D₂.outLevels θ) ∧
      lvlForall2 (fun a b => levelIsZero a = levelIsZero b) (D₁.gateLevels θ) (D₂.gateLevels θ)

/-- How the context side of a resolved view was obtained. `nativeSpine`: the
    original source `CtxP` exists and is used. `ambientView`/`terminalClause`:
    display-side views — the pending source obligation stays in the plan, never
    silently dropped. -/
inductive ViewSourceKind : Type where
  | nativeSpine | ambientView | terminalClause

/-- The consumer-usable working view of `q`: the computed plan, how the context
    side was obtained, and the real keys of the semantic subqueries this
    consumer will issue. No `Goal q` and no synonymous supplier is stored; a
    source `CtxP` is never uniformly required. -/
structure ResolvedView (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Type where
  /-- the working-view plan computed over the query's actual objects -/
  plan : ViewPlan Eₐ
  /-- how the context side was obtained -/
  source : ViewSourceKind
  /-- the real rank keys of the semantic subqueries this consumer issues -/
  budget : List (Nat × (List Nat × Nat))

/-- The approved moved measure for a mixed query. The definitive moved measure
    is versioned separately; the skeleton records the same two-typing multiset
    under the canonical context. -/
def movedMeas (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) :
    List Nat × Nat :=
  tyPairMeas Aw D₁ D₂

/-- The original prefix length: the length of the query's **frame** — the
    original ambient receipt `Γ₀` it was issued under (S15 §6). -/
def P2Query.originalPrefixLength {Eₐ : ResolvedEnv} : P2Query Eₐ → Nat
  | .es (Γ₀ := Γ₀) _ _ _ _ => Γ₀.length
  | .cl (Γ₀ := Γ₀) _ _ _ _ _ => Γ₀.length
  | .eut (Γ₀ := Γ₀) _ _ _ _ _ => Γ₀.length
  | .cts (Γ₀ := Γ₀) _ _ _ _ => Γ₀.length
  | .pb (Γ₀ := Γ₀) _ _ _ _ _ => Γ₀.length
  | .bitCoh (Γ₀ := Γ₀) _ _ _ _ _ => Γ₀.length
  | .mixed (Γ₀ := Γ₀) _ _ _ _ _ => Γ₀.length
  | .head (Γ₀ := Γ₀) _ _ _ _ _ _ _ _ => Γ₀.length
  | .slot (Γ₀ := Γ₀) _ _ _ _ _ _ _ _ => Γ₀.length
  | .observation (Γ₀ := Γ₀) _ _ _ _ _ _ _ _ => Γ₀.length
  | .obsPair (Γ₀ := Γ₀) _ _ _ _ _ => Γ₀.length

/-- **FROZEN CONTROL — the pre-repair first coordinate (finding 1):** the length
    of the derivation's **own** context. Under it a binder-body sub-request is
    never `Before` its parent (`binder_body_not_before`, `RcicSynStepSkeleton`).
    Not used by `rank`. -/
def P2Query.ownPrefixLength {Eₐ : ResolvedEnv} : P2Query Eₐ → Nat
  | .es (Γ := Γ) _ _ _ _ => Γ.length
  | .cl (Γ := Γ) _ _ _ _ _ => Γ.length
  | .eut (Γ := Γ) _ _ _ _ _ => Γ.length
  | .cts (Γ := Γ) _ _ _ _ => Γ.length
  | .pb (Γ := Γ) _ _ _ _ _ => Γ.length
  | .bitCoh (Γ := Γ) _ _ _ _ _ => Γ.length
  | .mixed (Γ := Γ) _ _ _ _ _ => Γ.length
  | .head (Γ := Γ) _ _ _ _ _ _ _ _ => Γ.length
  | .slot (Γ := Γ) _ _ _ _ _ _ _ _ => Γ.length
  | .observation (Γ := Γ) _ _ _ _ _ _ _ _ => Γ.length
  | .obsPair (Γ := Γ) _ _ _ _ _ => Γ.length

/-- The local key: `combMeas` of the query's payload measure under the
    canonical spine of its **frame** (closed `enrichCtxWfT_of_envWfT` of the
    frame scope — computable from the query's own fields). Within one frame the
    context extension beyond `Γ₀` is paid by the node that introduced it, never
    counted again (S15 §6). -/
noncomputable def P2Query.localKey (Aw : Nat → Nat) {Eₐ : ResolvedEnv} :
    P2Query Eₐ → List Nat × Nat
  | .es h S _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (cvMeas Aw h)
  | .cl D₁ D₂ S _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)
  | .eut D₁ D₂ S _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)
  | .cts h DX S _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (cvTyMeas Aw h DX)
  | .pb D DT S _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D DT)
  | .bitCoh D₁ D₂ S _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)
  | .mixed D₁ D₂ S _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (movedMeas Aw D₁ D₂)
  | .head c _ _ dL dR S _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx)
        (c.atoms Aw ++ dL.atoms Aw ++ dR.atoms Aw, c.wt Aw + dL.wt Aw + dR.wt Aw)
  | .slot _ _ _ dSlot _ S _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyMeas Aw dSlot)
  | .observation D _ _ _ _ S _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyMeas Aw D)
  | .obsPair D₁ D₂ S _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)

/-- The full rank key: the frame's prefix length, then the local `LexDM` key. -/
noncomputable def P2Query.rank (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) :
    Nat × (List Nat × Nat) :=
  (q.originalPrefixLength, q.localKey Aw)

end Rcic.Syn
