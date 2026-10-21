import rcic.RcicSynRawForest

/-!
# C5 layer 2 — `TyView`: the display operations along `TyNode`s

`research/rcic/sortrow/S7_COMPLETE_WORKING_VIEWS.md` §2 (ChatGPT S7 #7330).
`closure_claim` stays 0.

`TyView` is the display operation along the raw nodes, adding no arbitrary map.
Each `through*` constructor keeps the corresponding original transport node's
actual fields, with the source view as its single predecessor:

- `throughWk`: the original target is `insertAt d c Γ`, displayed terms are the
  `lift c 1` images — the record keeps `d` and `c`, never a weaker abstract
  weakening.
- `throughEsub` / `throughLsub`: keep the real `hget`, `hv`, `hvT`, `j` and the
  actual source/target syntax; the original assumption/let distinction is kept.
- `throughLinst`: keeps `ls`, the arity equation and the boundedness proof.
- `throughEwk`: keeps the original `EnvExt` and the source-view identity.
- `throughCctx`: keeps the original binder bridge `A ≡ A'`.
- `throughConvIndex` keeps `d` and `c`: the term view is transparent for term
  erasure, opaque for the type and regularity (the conversion is displayed as
  the index conversion, not unfolded).

A `TyView` never deletes an original request and never asserts source
readiness: it is a plan datum, not a `ResolvedView`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The display-side grammar over `TyNode`. Indices are the displayed
    (working) coordinates; every `through*` arm records the original
    transport's actual fields. -/
inductive TyView : ResolvedEnv → Nat → LCtx → Expr Nat → Expr Nat → Type where
  /-- The identity display: the original node itself. -/
  | atOriginal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat)
      (nd : TyNode E n Γ e T) : TyView E n Γ e T
  /-- Display through an original `wk` transport. -/
  | throughWk (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) (d : LocalDecl)
      (c : Nat) (src : TyView E n Γ e A) :
      TyView E n (insertAt d c Γ) (lift c 1 e) (lift c 1 A)
  /-- Display through an original `esub` transport (assumption entry). -/
  | throughEsub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A t v : Expr Nat) (j : Nat)
      (u : Level) (src : TyView E n Γ e A) (hget : Γ[j]? = some (.assumption t))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      TyView E n (substRemove v j Γ) (instantiate j (lift 0 j v) e)
        (instantiate j (lift 0 j v) A)
  /-- Display through an original `lsub` transport (let entry, real stored
      value fixed). -/
  | throughLsub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A t v : Expr Nat) (j : Nat)
      (u : Level) (src : TyView E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      TyView E n (substRemove v j Γ) (instantiate j (lift 0 j v) e)
        (instantiate j (lift 0 j v) A)
  /-- Display through an original `linst` transport: the real `ls`, its arity
      equation and its boundedness are kept. -/
  | throughLinst (E : ResolvedEnv) (a n : Nat) (Γ : LCtx) (e A : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a)
      (src : TyView E a Γ e A) :
      TyView E n (instLvlsCtx ls Γ) (instantiateLevels ls e) (instantiateLevels ls A)
  /-- Display through an original `ewk` transport: the real `EnvExt` and the
      source view's identity are kept. -/
  | throughEwk (E₀ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat)
      (hext : EnvExt E₀ E) (src : TyView E₀ n Γ e A) : TyView E n Γ e A
  /-- Display through an original `cctx` transport: the real binder bridge. -/
  | throughCctx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T A A' : Expr Nat) (u : Level)
      (src : TyView E n (.assumption A :: Γ) e T) (hA : CvNode E n Γ A A' (.sort u)) :
      TyView E n (.assumption A' :: Γ) e T
  /-- Display through an original `conv` index: `d` is the term view, `c` the
      recorded index conversion — transparent for term erasure, opaque for the
      type and regularity. -/
  | throughConvIndex (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A B : Expr Nat) (u : Level)
      (d : TyView E n Γ e A) (c : CvNode E n Γ A B (.sort u)) : TyView E n Γ e B

/-- The original node a display chain starts from, if it is displayed at the
    original coordinates (the `atOriginal` root). -/
def TyView.root : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyView E n Γ e T → TyView E n Γ e T
  | _, _, _, _, _, v => v

end Rcic.Syn
