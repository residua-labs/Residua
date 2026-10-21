import rcic.RcicSynTyView
import rcic.RcicSynGroupStage
import rcic.RcicSynBelowScoped

/-!
# C5 layer 2 — `ContextView`: records of internal source/working-view operations

`research/rcic/sortrow/S7_COMPLETE_WORKING_VIEWS.md` §3 (ChatGPT S7 #7330).
`closure_claim` stays 0.

The original `CtxP` has only `nil / assumption / letBinding` (they are
`CtxNode`s). The twelve constructors below are **records of internal
source/working-view operations, not new `CtxP` constructors**. Each keeps the
operation's actual data; each also records both environments — the native
environment `Eₙ` the carried objects live in (through their indices) and the
admitted working environment `Ew` the comparison happens in (`hw : EnvWfT Ew`),
since collapsing them to one bare `E` would lose the `.ewk` provenance.

| op | actual data kept |
|---|---|
| `root` | the original `ScopedCtx`, canonical `C`, original `S.can σ` |
| `tailFocus` | the original `C`'s actual suffix, lookup and occurrence decomposition |
| `assumptionBody` | the introducing node's own `hA` |
| `letBody` | the original `hA`, `hv` and the real stored value |
| `wkSource` | the original target, `d`, cutoff, `removeAt` and post-lift |
| `esubSource` | the original `hget`, `hv`, `hvT`, `j`, source/target syntax |
| `lsubSource` | as above, with the actual let value fixed |
| `linstSource` | the original `ls`/arity, the composed source map |
| `ewkSource` | the original `EnvExt`, the original source identity |
| `cctxSource` | the original bridge with actual `dl`/`dr`, the original target entry |
| `groupStage` | the actual `GroupStageAt` / `EnvWfT` node |
| `refocus` | the reassignment and permutation of original occurrences |

None of these resolves to usable evidence by construction (§3's right column);
they are plan data. A source-view obligation that cannot be discharged stays
a pending record — never a deleted request or a forged source `CtxP`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Internal source/working-view operations over original contexts. Each
    constructor records its actual data plus `Ew`/`hw`, the admitted working
    environment in which the comparison happens; the native environment is the
    one the carried objects' indices live in. -/
inductive ContextView : Type where
  /-- The original `ScopedCtx` and the display map: canonical `C` is computed
      directly as `S.can σ`. -/
  | root {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) : ContextView
  /-- Focus a suffix of the original `C`: the context node, the looked-up index
      and the occurrence it selects. Consumes M3; never copies the selected
      provider. -/
  | tailFocus {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
      (C : CtxNode E n Γ) (hlook : lookupType Γ i = some A)
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- The introducing assumption node's own `hA`: builds the original binder
      `C`; slot-bit alignment is by A1/A6. -/
  | assumptionBody {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      (hA : TyNode E n Γ A (.sort u))
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- The introducing let node's own `hA`, `hv` and the real stored value:
      builds the original let `C`; drop/inline correspondence is by a real
      `PBit`. -/
  | letBody {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v : Expr Nat} {u : Level}
      (hA : TyNode E n Γ A (.sort u)) (hv : TyNode E n Γ v A)
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- A weakening source view: the original target context
      `insertAt d c Γ`, the inserted declaration `d`, the cutoff `c`, and the
      post-lift identity `removeAt c` of the target. A source spine only with a
      real forward origin; otherwise it stays a source-view obligation. -/
  | wkSource {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (d : LocalDecl) (c : Nat)
      (target : CtxNode E n (insertAt d c Γ))
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- An assumption-substitution source view: the original `hget`, `hv`,
      `hvT`, `j` and the source (`Γ`) / target (`substRemove v j Γ`) syntax.
      Index `0` can consume the original strip construction; at general depth
      target evidence is never rewritten backward into source. -/
  | esubSource {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t v : Expr Nat} {j : Nat} {u : Level}
      (hget : Γ[j]? = some (.assumption t))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- The let-substitution source view, with the actual let value fixed.
      Never turned into an assumption; AP cutoffs are verified step by step. -/
  | lsubSource {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t v : Expr Nat} {j : Nat} {u : Level}
      (hget : Γ[j]? = some (.letBinding t v))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- A level-instantiation source view: the original `ls`, the source arity
      `a` it satisfies and the composed source map `instLevel ls`. No inversion
      of `ls`; map facts are not a source spine. -/
  | linstSource {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} (ls : List Level)
      (hlen : ls.length = a)
      (srcMap : Level → Level) (hmap : srcMap = fun l => instLevel ls l)
      (src : CtxNode E a Γ)
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- An environment-extension source view: the original `EnvExt` and the
      original source context's identity. Consumes the post-rebase working
      correspondence; never forges a source `CtxP`. -/
  | ewkSource {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      (hext : EnvExt E₀ E) (src : CtxNode E₀ n Γ)
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- A context-conversion source view: the original bridge `A ≡ A'` with its
      actual `dl`/`dr` (inside the `CvNode`) and the original target entry.
      Consumes S6's smaller cctx alignment and endpoint DM. -/
  | cctxSource {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {u : Level}
      (bridge : CvNode E n Γ A A' (.sort u)) (entry : LocalDecl)
      (hentry : entry = .assumption A')
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- A native group-stage position, or a whole admitted environment node.
      Only for the corresponding internal stage; never auto-generates a
      public `EnvWfT`. -/
  | groupStage {S E₀ : ResolvedEnv} {ms : List (Nat × CheckedMember)} {Eend Eᵢ : ResolvedEnv}
      {g : GroupMembersT S E₀ ms Eend} (stage : GroupStageAt g Eᵢ)
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView
  /-- A refocus: the reassignment of original occurrences by an explicit
      permutation. A role change inside the current step; the permutation is
      not a recursive descent. -/
  | refocus {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      (C : CtxNode E n Γ) (perm : List Nat)
      (Ew : ResolvedEnv) (hw : EnvWfT Ew) : ContextView

/-- Which admitted working environment a context-view record compares in —
    never collapsed onto the native one (`root` keeps `Eₐ` through `S`). -/
def ContextView.workEnv : ContextView → ResolvedEnv
  | @ContextView.root Eₐ _ _ _ _ _ => Eₐ
  | @ContextView.tailFocus _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.assumptionBody _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.letBody _ _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.wkSource _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.esubSource _ _ _ _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.lsubSource _ _ _ _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.linstSource _ _ _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.ewkSource _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.cctxSource _ _ _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.groupStage _ _ _ _ _ _ _ Ew _ => Ew
  | @ContextView.refocus _ _ _ _ _ Ew _ => Ew

end Rcic.Syn
