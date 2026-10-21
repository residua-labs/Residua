import rcic.RcicSynSpineComb
import rcic.RcicSynSlotOrigin

/-!
# `DispForPath`: the total transport-suffix path family

A `DispForPathTy D σ ρ C` (resp. `DispForPathCv`) is a certificate that the
derivation `D` at the endpoint `(σ, ρ, C)` carries a valid `DispForC`, and that
descends through every transport constructor to the first rule node. It is the
S1C `DispForPath`/`DispForPathTy`/`DispForPathCv` family made total: every
`TyP`/`CvP` constructor has a corresponding path constructor, so the family
covers the whole derivation tree — the transport suffix and the per-call forest
of rule children alike.

At each node the path retains the endpoint's `DispForC`. At each transport
step it stores the payload of the corresponding `SortTyTransport` constructor
(§1.3) — `EnvClosed`/`EnvMembersSubstStable` for `wk`/`esub`/`lsub`,
`EnvLevelsT`/`IotaLevelsT` for `linst`, and the native `HasTyT` replacement for
`esub`/`lsub` — plus the source endpoint (map, disposition, spine) the child
path is indexed by. `ewk` and `cctx` are genuine path steps here even though
`SortTyTransport` has no constructor for them: `ewk` records the node's own
`EnvExt`, and `cctx` records the typed bridge's own path, whose shared `ρ`
makes the head-clause bit comparison a premise of path existence rather than an
oracle.

The source spine and source disposition of each transport step are stored
data, not derived by inverting `DispFor` — this family is provenance, not an
inversion principle. Where the removed binder's clause has two valid shapes
(`letBinding`, or an inserted clause at arbitrary index `j`) the clause is a
parameter and the child path's own `DispForC` pins it; where the clause is
forced (an `.assumption` head) it is fixed as `binderDisp (levelIsZero (σ u))`.

`DispForPathSpine C σ ρ` supplies paths for the typings stored inside the
spine `C` itself, at each entry's tail endpoint — the "spine-entry typings" of
the S1 forest inventory.

## Coverage status

This family is a *sufficient sub-certificate*, not the coverage entry for
arbitrary `AssumptionPrefix` derivations. Each transport node requires a
strict source spine `C₀ : CtxP _ _ Γ_src`, which does not exist for every
public AP input: for `.ewk`, S1 (#7307) exhibits `E₀ = emptyEnv` with
`Γ = [.assumption (const 0 [])]` — the head entry's domain references a
member absent from `emptyEnv`, so no `CtxP E₀ n Γ` exists and the strict
`ewk` step has no path (W-COV-EWK-SOURCE-CTX). Coverage of those inputs
goes through the environment rebase (ct001), not through this family.

This module asserts no decrease and no arbitrary `AssumptionPrefix` coverage;
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

mutual

/-- A transport-suffix path for a typing derivation: `hC` retained at the
    current endpoint, rule nodes carry their children's paths, transport nodes
    carry the §1.3 step payload and the source-indexed child path. -/
inductive DispForPathTy : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → (σ : Level → Level) → List Disp → CtxP E n Γ → Type where
  | sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k : Level} {h : eqN k (.succ l)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ) :
      DispForPathTy (.sort E n Γ l k h) σ ρ C
  | bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u : Level}
      {h : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathTy hA σ ρ C) :
      DispForPathTy (.bvar E n Γ i A u h hA) σ ρ C
  | const {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
      {m : CheckedMember} {u : Level} {hres : E.members r = some m}
      {hlen : ls.length = m.arity} {hwf : levelsBounded n ls = true}
      {hls : eqNList ls ls₀} {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pT : DispForPathTy hT σ ρ C) :
      DispForPathTy (.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) σ ρ C
  | pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      {B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
      {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathTy hA σ ρ C)
      (pB : DispForPathTy hB σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA)) :
      DispForPathTy (.pi E n Γ A u B v hA hB) σ ρ C
  | lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      {body B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B}
      {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathTy hA σ ρ C)
      (pbody : DispForPathTy hbody σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA))
      (pB : DispForPathTy hB σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA)) :
      DispForPathTy (.lam E n Γ A u body B v hA hbody hB) σ ρ C
  | app {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w : Level}
      {hf : TyP E n Γ f (.pi A B)} {ha : TyP E n Γ a A}
      {hT : TyP E n Γ (instantiate0 a B) (.sort w)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pf : DispForPathTy hf σ ρ C)
      (pa : DispForPathTy ha σ ρ C)
      (pT : DispForPathTy hT σ ρ C) :
      DispForPathTy (.app E n Γ f a A B w hf ha hT) σ ρ C
  | letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      {value B body : Expr Nat} {w : Level} {hA : TyP E n Γ A (.sort u)}
      {hv : TyP E n Γ value A} {hb : TyP E n (.letBinding A value :: Γ) body B}
      {hT : TyP E n Γ (instantiate0 value B) (.sort w)}
      {dlet : Disp} {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathTy hA σ ρ C)
      (pv : DispForPathTy hv σ ρ C)
      (pb : DispForPathTy hb σ (dlet :: ρ) (.letBinding E n Γ A u value C hA hv))
      (pT : DispForPathTy hT σ ρ C) :
      DispForPathTy (.letE E n Γ A u value B body w hA hv hb hT) σ ρ C
  | lit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat}
      {hexp : TyP E n Γ (natExpand t) T}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pexp : DispForPathTy hexp σ ρ C) :
      DispForPathTy (.lit E n Γ t T hexp) σ ρ C
  | conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
      {h : TyP E n Γ e A} {hc : CvP E n Γ A B (.sort u)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (ph : DispForPathTy h σ ρ C)
      (pc : DispForPathCv hc σ ρ C) :
      DispForPathTy (.conv E n Γ e A B u h hc) σ ρ C
  /-- `wk`: the source keeps the same `σ`; its disposition is `removeAt ρ c`
      (`es_wk`'s endpoint). `hcl` is the `SortTyTransport.wk` payload. -/
  | wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
      {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n (insertAt d c Γ)}
      {C₀ : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (hcl : EnvClosed E)
      (src : DispForPathTy D σ (removeAt ρ c) C₀) :
      DispForPathTy (.wk E n Γ e A d c D) σ ρ C
  /-- `esub`: the removed `.assumption` slot's clause `dj` is a parameter (the
      child path's `DispForC` pins it to `binderDisp (levelIsZero (σ u₀))` for
      the source spine's recorded sort `u₀`). `hvN` is the native
      `SortTyTransport.esub` payload — `hv` enriched is not demoted. -/
  | esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
      {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
      {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
      {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
      {dj : Disp} {σ : Level → Level} {ρ : List Disp}
      {C : CtxP E n (substRemove v j Γ)} {C₀ : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (hcl : EnvClosed E)
      (hinst : EnvMembersSubstStable E)
      (hvN : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (src : DispForPathTy D σ (insertDisp dj j ρ) C₀)
      (pv : DispForPathTy hv σ ρ C)
      (pvT : DispForPathTy hvT σ ρ C) :
      DispForPathTy (.esub E n Γ e A t v j u D hget hv hvT) σ ρ C
  /-- `lsub`: the removed `.letBinding` slot's clause `dj` is a parameter
      (`.drop` or `.inline _`, pinned by the child's `DispForC`). -/
  | lsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
      {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.letBinding t v)}
      {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
      {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
      {dj : Disp} {σ : Level → Level} {ρ : List Disp}
      {C : CtxP E n (substRemove v j Γ)} {C₀ : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (hcl : EnvClosed E)
      (hinst : EnvMembersSubstStable E)
      (hvN : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (src : DispForPathTy D σ (insertDisp dj j ρ) C₀)
      (pv : DispForPathTy hv σ ρ C)
      (pvT : DispForPathTy hvT σ ρ C) :
      DispForPathTy (.lsub E n Γ e A t v j u D hget hv hvT) σ ρ C
  /-- `linst`: the source map is `fun l => σ (instLevel ls l)`
      (`es_linst`'s endpoint); `hEL`/`hIL` are the `SortTyTransport.linst`
      payload. -/
  | linst {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat} {ls : List Level}
      {hls : levelsBounded n ls = true} {hlen : ls.length = a}
      {D : TyP E a Γ e A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n (instLvlsCtx ls Γ)}
      {C₀ : CtxP E a Γ}
      (hC : DispForC σ C ρ)
      (hEL : EnvLevelsT E)
      (hIL : IotaLevelsT E)
      (src : DispForPathTy D (fun l => σ (instLevel ls l)) ρ C₀) :
      DispForPathTy (.linst E a n Γ e A ls hls hlen D) σ ρ C
  /-- `ewk`: same map and disposition on both sides (`es_ewk`'s endpoint); the
      node's own `EnvExt E₀ E` is the step payload. The strict source spine
      `C₀ : CtxP E₀ n Γ` makes this a sufficient step, not a total one —
      public inputs whose `Γ` admits no `CtxP` at `E₀` (e.g. `emptyEnv` with
      `[.assumption (const 0 [])]`, W-COV-EWK-SOURCE-CTX) have no `ewk` path;
      their coverage goes through the environment rebase (ct001). -/
  | ewk {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
      {hext : EnvExt E₀ E} {D : TyP E₀ n Γ e A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ} {C₀ : CtxP E₀ n Γ}
      (hC : DispForC σ C ρ)
      (src : DispForPathTy D σ ρ C₀) :
      DispForPathTy (.ewk E₀ E n Γ e A hext D) σ ρ C
  /-- `cctx`: same `σ` and `ρ` on both sides (`es_cctx`'s endpoint). Sharing
      `ρ` across the two `.assumption` spines forces the head clauses'
      `levelIsZero (σ ·)` bits to agree — the paid bit comparison. `bridge` is
      the typed bridge's own path at the tail endpoint. -/
  | cctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u : Level}
      {D : TyP E n (.assumption A :: Γ) e T} {hA : CvP E n Γ A A' (.sort u)}
      {u' : Level} {Ct : CtxP E n Γ} {hA₀' : TyP E n Γ A' (.sort u')}
      {d₀ : Disp} {ρt : List Disp} {C₀ : CtxP E n (.assumption A :: Γ)}
      {σ : Level → Level}
      (hC : DispForC σ (.assumption E n Γ A' u' Ct hA₀') (d₀ :: ρt))
      (src : DispForPathTy D σ (d₀ :: ρt) C₀)
      (bridge : DispForPathCv hA σ ρt Ct) :
      DispForPathTy (.cctx E n Γ e T A A' u D hA) σ (d₀ :: ρt)
        (.assumption E n Γ A' u' Ct hA₀')

/-- A transport-suffix path for a conversion derivation. Same discipline as
    `DispForPathTy`: `hC` at the current endpoint, children's paths at rule
    nodes, the §1.3 step payload plus the source-indexed child at transports. -/
inductive DispForPathCv : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} →
    CvP E n Γ a b T → (σ : Level → Level) → List Disp → CtxP E n Γ → Type where
  | refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat}
      {h dl dr : TyP E n Γ a A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (ph : DispForPathTy h σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.refl E n Γ a A h dl dr) σ ρ C
  | symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat}
      {h : CvP E n Γ a b A} {dl : TyP E n Γ b A} {dr : TyP E n Γ a A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (ph : DispForPathCv h σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.symm E n Γ a b A h dl dr) σ ρ C
  | trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
      {h1 : CvP E n Γ a b A} {h2 : CvP E n Γ b c A}
      {dl : TyP E n Γ a A} {dr : TyP E n Γ c A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (p1 : DispForPathCv h1 σ ρ C) (p2 : DispForPathCv h2 σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.trans E n Γ a b c A h1 h2 dl dr) σ ρ C
  | beta {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat}
      {u : Level} {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B} {harg : TyP E n Γ arg A}
      {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
      {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathTy hA σ ρ C)
      (pbody : DispForPathTy hbody σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA))
      (parg : DispForPathTy harg σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.beta E n Γ A body arg B u hA hbody harg dl dr) σ ρ C
  | zeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body B : Expr Nat}
      {u : Level} {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
      {hb : TyP E n (.letBinding A value :: Γ) body B}
      {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
      {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
      {dlet : Disp} {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathTy hA σ ρ C)
      (pv : DispForPathTy hv σ ρ C)
      (pb : DispForPathTy hb σ (dlet :: ρ)
        (.letBinding E n Γ A u value C hA hv))
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.zeta E n Γ A value body B u hA hv hb dl dr) σ ρ C
  | zetaLocal {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
      {hval : lookupValue Γ i = some v} {hty : lookupType Γ i = some A}
      {hv : TyP E n Γ v A} {dl : TyP E n Γ (.bvar i) A} {dr : TyP E n Γ v A}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pv : DispForPathTy hv σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.zetaLocal E n Γ i A v hval hty hv dl dr) σ ρ C
  | delta {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
      {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m}
      {hbody : m.body = some b} {htr : transparent m.mclass = true}
      {hlen : ls.length = m.arity} {hwf : levelsBounded n ls = true}
      {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pb : DispForPathTy hb σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) σ ρ C
  | iota {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
      {h : DerivedIota E lhs rhs}
      {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
      {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (plhs : DispForPathTy hlhs σ ρ C) (prhs : DispForPathTy hrhs σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.iota E n Γ lhs rhs T h hlhs hrhs dl dr) σ ρ C
  | lit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
      {h : LiteralExpansion t exp}
      {hexp : TyP E n Γ exp T} {dl : TyP E n Γ (.lit t) T} {dr : TyP E n Γ exp T}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pexp : DispForPathTy hexp σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.lit E n Γ t exp T h hexp dl dr) σ ρ C
  | app {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
      {h1 : CvP E n Γ f g (.pi A B)} {h2 : CvP E n Γ a b A}
      {dl : TyP E n Γ (.app f a) (instantiate0 a B)}
      {dr : TyP E n Γ (.app g b) (instantiate0 a B)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (p1 : DispForPathCv h1 σ ρ C) (p2 : DispForPathCv h2 σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.app E n Γ f g a b A B h1 h2 dl dr) σ ρ C
  | lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat}
      {u : Level} {hA : CvP E n Γ A A' (.sort u)}
      {hb : CvP E n (.assumption A :: Γ) b b' B}
      {dl : TyP E n Γ (.lam A b) (.pi A B)} {dr : TyP E n Γ (.lam A' b') (.pi A B)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathCv hA σ ρ C)
      (pb : DispForPathCv hb σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA.dl))
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.lam E n Γ A A' b b' B u hA hb dl dr) σ ρ C
  | pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat}
      {u v : Level} {hA : CvP E n Γ A A' (.sort u)}
      {hB : CvP E n (.assumption A :: Γ) B B' (.sort v)}
      {dl : TyP E n Γ (.pi A B) (.sort (.imax u v))}
      {dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathCv hA σ ρ C)
      (pB : DispForPathCv hB σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA.dl))
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.pi E n Γ A A' B B' u v hA hB dl dr) σ ρ C
  | letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' v v' b b' B : Expr Nat}
      {u : Level} {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
      {hb : CvP E n (.letBinding A v :: Γ) b b' B}
      {dl : TyP E n Γ (.letE A v b) (instantiate0 v B)}
      {dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)}
      {dlet : Disp} {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pA : DispForPathCv hA σ ρ C) (pv : DispForPathCv hv σ ρ C)
      (pb : DispForPathCv hb σ (dlet :: ρ)
        (.letBinding E n Γ A u v C hA.dl hv.dl))
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) σ ρ C
  | sorts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l₁ l₂ : Level}
      {h : eqN l₁ l₂}
      {dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁))}
      {dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁))}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.sorts E n Γ l₁ l₂ h dl dr) σ ρ C
  | consts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
      {m : CheckedMember} {hres : E.members r = some m}
      {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true} {hwf' : levelsBounded n ls' = true}
      {h : eqNList ls ls'}
      {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
      {dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) σ ρ C
  | eta {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
      {h : TyP E n Γ f (.pi A B)}
      {dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
      {dr : TyP E n Γ f (.pi A B)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (ph : DispForPathTy h σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.eta E n Γ f A B h dl dr) σ ρ C
  | irr {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P p q : Expr Nat}
      {hP : TyP E n Γ P (.sort .zero)} {hp : TyP E n Γ p P} {hq : TyP E n Γ q P}
      {dl : TyP E n Γ p P} {dr : TyP E n Γ q P}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pP : DispForPathTy hP σ ρ C)
      (pp : DispForPathTy hp σ ρ C) (pq : DispForPathTy hq σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.irr E n Γ P p q hP hp hq dl dr) σ ρ C
  | tyConv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat}
      {u : Level} {h : CvP E n Γ a b A} {hA : CvP E n Γ A A' (.sort u)}
      {dl : TyP E n Γ a A'} {dr : TyP E n Γ b A'}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (ph : DispForPathCv h σ ρ C) (pA : DispForPathCv hA σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.tyConv E n Γ a b A A' u h hA dl dr) σ ρ C
  /-- `fsub` is a rule node (functionality): `hB`'s path is at the extended
      assumption endpoint built from the node's own `hA`. -/
  | fsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B S a b : Expr Nat}
      {u : Level} {hB : TyP E n (.assumption A :: Γ) B S}
      {hA : TyP E n Γ A (.sort u)} {hab : CvP E n Γ a b A}
      {dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S)}
      {dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S)}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (pB : DispForPathTy hB σ (binderDisp (levelIsZero (σ u)) :: ρ)
        (.assumption E n Γ A u C hA))
      (pA : DispForPathTy hA σ ρ C)
      (pab : DispForPathCv hab σ ρ C)
      (pdl : DispForPathTy dl σ ρ C) (pdr : DispForPathTy dr σ ρ C) :
      DispForPathCv (.fsub E n Γ A B S a b u hB hA hab dl dr) σ ρ C
  | wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      {d : LocalDecl} {c : Nat} {h : CvP E n Γ a b T}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n (insertAt d c Γ)}
      {C₀ : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (hcl : EnvClosed E)
      (src : DispForPathCv h σ (removeAt ρ c) C₀) :
      DispForPathCv (.wk E n Γ a b T d c h) σ ρ C
  | esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T t v : Expr Nat} {j : Nat}
      {u : Level} {h : CvP E n Γ a b T} {hget : Γ[j]? = some (.assumption t)}
      {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
      {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
      {dj : Disp} {σ : Level → Level} {ρ : List Disp}
      {C : CtxP E n (substRemove v j Γ)} {C₀ : CtxP E n Γ}
      (hC : DispForC σ C ρ)
      (hcl : EnvClosed E)
      (hinst : EnvMembersSubstStable E)
      (hvN : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (src : DispForPathCv h σ (insertDisp dj j ρ) C₀)
      (pv : DispForPathTy hv σ ρ C)
      (pvT : DispForPathTy hvT σ ρ C) :
      DispForPathCv (.esub E n Γ a b T t v j u h hget hv hvT) σ ρ C
  | linst {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      {ls : List Level}
      {hls : levelsBounded n ls = true} {hlen : ls.length = a'}
      {h : CvP E a' Γ a b T}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n (instLvlsCtx ls Γ)}
      {C₀ : CtxP E a' Γ}
      (hC : DispForC σ C ρ)
      (hEL : EnvLevelsT E)
      (hIL : IotaLevelsT E)
      (src : DispForPathCv h (fun l => σ (instLevel ls l)) ρ C₀) :
      DispForPathCv (.linst E a' n Γ a b T ls hls hlen h) σ ρ C
  /-- `ewk` (conversion side): same strict source-spine discipline as the
      typing side — `C₀ : CtxP E₀ n Γ` is sufficient but not coverable for
      every public AP input (W-COV-EWK-SOURCE-CTX); see the module header. -/
  | ewk {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      {hext : EnvExt E₀ E} {h : CvP E₀ n Γ a b T}
      {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ} {C₀ : CtxP E₀ n Γ}
      (hC : DispForC σ C ρ)
      (src : DispForPathCv h σ ρ C₀) :
      DispForPathCv (.ewk E₀ E n Γ a b T hext h) σ ρ C
  | cctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T A A' : Expr Nat}
      {u : Level} {h : CvP E n (.assumption A :: Γ) a b T}
      {hA : CvP E n Γ A A' (.sort u)}
      {u' : Level} {Ct : CtxP E n Γ} {hA₀' : TyP E n Γ A' (.sort u')}
      {d₀ : Disp} {ρt : List Disp} {C₀ : CtxP E n (.assumption A :: Γ)}
      {σ : Level → Level}
      (hC : DispForC σ (.assumption E n Γ A' u' Ct hA₀') (d₀ :: ρt))
      (src : DispForPathCv h σ (d₀ :: ρt) C₀)
      (bridge : DispForPathCv hA σ ρt Ct) :
      DispForPathCv (.cctx E n Γ a b T A A' u h hA) σ (d₀ :: ρt)
        (.assumption E n Γ A' u' Ct hA₀')

/-- Paths for the typings stored inside a context spine `C`, each at its tail
    endpoint: for `.assumption` the domain typing, for `.letBinding` the domain
    and value typings. The head clause `d` belongs to the head declaration and
    is unconstrained here — the entries' own paths carry the tail's validity. -/
inductive DispForPathSpine : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → (σ : Level → Level) → List Disp → Type where
  | nil {E : ResolvedEnv} {n : Nat} {σ : Level → Level} {ρ : List Disp} :
      DispForPathSpine (.nil E n) σ ρ
  | assumption {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      {Ct : CtxP E n Γ} {hA₀ : TyP E n Γ A (.sort u)}
      {d : Disp} {σ : Level → Level} {ρt : List Disp}
      (pA : DispForPathTy hA₀ σ ρt Ct)
      (rest : DispForPathSpine Ct σ ρt) :
      DispForPathSpine (.assumption E n Γ A u Ct hA₀) σ (d :: ρt)
  | letBinding {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      {v : Expr Nat} {Ct : CtxP E n Γ} {hA₀ : TyP E n Γ A (.sort u)}
      {hv₀ : TyP E n Γ v A}
      {d : Disp} {σ : Level → Level} {ρt : List Disp}
      (pA : DispForPathTy hA₀ σ ρt Ct)
      (pv : DispForPathTy hv₀ σ ρt Ct)
      (rest : DispForPathSpine Ct σ ρt) :
      DispForPathSpine (.letBinding E n Γ A u v Ct hA₀ hv₀) σ (d :: ρt)

end

/-! ## endpoint validity is retained at every node -/

/-- The endpoint `DispForC` a path retains. -/
def DispForPathTy.hC : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    {σ : Level → Level} → {ρ : List Disp} → {C : CtxP E n Γ} →
    {D : TyP E n Γ e T} → DispForPathTy D σ ρ C → DispForC σ C ρ
  | _, _, _, _, _, _, _, _, _, .sort hC => hC
  | _, _, _, _, _, _, _, _, _, .bvar hC _ => hC
  | _, _, _, _, _, _, _, _, _, .const hC _ => hC
  | _, _, _, _, _, _, _, _, _, .pi hC _ _ => hC
  | _, _, _, _, _, _, _, _, _, .lam hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, .app hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, .letE hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, .lit hC _ => hC
  | _, _, _, _, _, _, _, _, _, .conv hC _ _ => hC
  | _, _, _, _, _, _, _, _, _, .wk hC _ _ => hC
  | _, _, _, _, _, _, _, _, _, .esub hC _ _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, .lsub hC _ _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, .linst hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, .ewk hC _ => hC
  | _, _, _, _, _, _, _, _, _, .cctx hC _ _ => hC

/-- The endpoint `DispForC` a conversion path retains. -/
def DispForPathCv.hC : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    {σ : Level → Level} → {ρ : List Disp} → {C : CtxP E n Γ} →
    {h : CvP E n Γ a b T} → DispForPathCv h σ ρ C → DispForC σ C ρ
  | _, _, _, _, _, _, _, _, _, _, .refl hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .symm hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .trans hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .beta hC _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .zeta hC _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .zetaLocal hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .delta hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .iota hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .lit hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .app hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .lam hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .pi hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .letE hC _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .sorts hC _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .consts hC _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .eta hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .irr hC _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .tyConv hC _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .fsub hC _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .wk hC _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .esub hC _ _ _ _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .linst hC _ _ _ => hC
  | _, _, _, _, _, _, _, _, _, _, .ewk hC _ => hC
  | _, _, _, _, _, _, _, _, _, _, .cctx hC _ _ => hC

/-- A path yields the endpoint's `DispFor` (forgetting the spine). -/
theorem DispForPathTy.toDispFor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
    {D : TyP E n Γ e T} (p : DispForPathTy D σ ρ C) : DispFor σ E n Γ ρ :=
  p.hC.toDispFor

/-- A conversion path yields the endpoint's `DispFor` (forgetting the spine). -/
theorem DispForPathCv.toDispFor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
    {h : CvP E n Γ a b T} (p : DispForPathCv h σ ρ C) : DispFor σ E n Γ ρ :=
  p.hC.toDispFor

end Rcic.Syn
