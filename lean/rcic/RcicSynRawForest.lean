import rcic.RcicConvPlus

/-!
# C5 layer 1 — the raw forest grammar (`TyNode` / `CvNode` / `CtxNode`)

`research/rcic/sortrow/S7_COMPLETE_WORKING_VIEWS.md` §1–§2 (ChatGPT S7 #7330).
`closure_claim` stays 0.

**RawForest** records every original object and every actual field position:

- `TyNode` corresponds one to one with the fifteen original `TyP` arms — each
  constructor keeps all of the arm's actual fields, with derivation children
  re-typed as nodes of the grammar (`TyP → TyNode`, `CvP → CvNode`).
- `CvNode` builds the tree from the original fields of the 24 `CvP` arms
  (`S7_ORIGINAL_DOMAIN_KIND_TRACE` §6): `refl` three (`h`, `dl`, `dr`),
  `trans` four (`h1`, `h2`, `dl`, `dr`), `irr` five (`hP`, `hp`, `hq`, `dl`,
  `dr`), `tyConv` four (the subject `h`, the index `hA`, `dl`, `dr`), and every
  other arm keeps all its actual fields likewise. `CvP` has no primitive
  `lsub`; neither does `CvNode`.
- `CtxNode` mirrors the three original `CtxP` constructors
  (`nil` / `assumption` / `letBinding`). Internal source/working-view
  operations are `ContextView` records (S7 §3), never new `CtxNode` arms.

`RawForest` is the kind-sum over the three families; `children` enumerates a
node's direct derivation-field positions in declaration order. The
`toTyNode`/`toCvNode`/`toCtxNode` traversals are the total structural pass of
§1 — the first layer's totality never stands in for a `ResolvedView`.
-/

namespace Rcic.Syn

open Rcic.Declarative

mutual

/-- The raw typing-node grammar: one arm per original `TyP` constructor,
    keeping all actual fields with derivation children as grammar nodes. -/
inductive TyNode : ResolvedEnv → Nat → LCtx → Expr Nat → Expr Nat → Type
  | sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l k : Level) (h : eqN k (.succ l)) :
      TyNode E n Γ (.sort l) (.sort k)
  | bvar (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) (A : Expr Nat) (u : Level)
      (h : lookupType Γ i = some A) (hA : TyNode E n Γ A (.sort u)) :
      TyNode E n Γ (.bvar i) A
  | const (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls ls₀ : List Level)
      (m : CheckedMember) (u : Level) (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
      (hT : TyNode E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)) :
      TyNode E n Γ (.const r ls) (instantiateLevels ls₀ m.mtype)
  | pi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) (B : Expr Nat) (v : Level)
      (hA : TyNode E n Γ A (.sort u)) (hB : TyNode E n (.assumption A :: Γ) B (.sort v)) :
      TyNode E n Γ (.pi A B) (.sort (.imax u v))
  | lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) (body B : Expr Nat)
      (v : Level) (hA : TyNode E n Γ A (.sort u))
      (hbody : TyNode E n (.assumption A :: Γ) body B)
      (hB : TyNode E n (.assumption A :: Γ) B (.sort v)) :
      TyNode E n Γ (.lam A body) (.pi A B)
  | app (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f a A B : Expr Nat) (w : Level)
      (hf : TyNode E n Γ f (.pi A B)) (ha : TyNode E n Γ a A)
      (hT : TyNode E n Γ (instantiate0 a B) (.sort w)) :
      TyNode E n Γ (.app f a) (instantiate0 a B)
  | letE (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level)
      (value B body : Expr Nat) (w : Level)
      (hA : TyNode E n Γ A (.sort u)) (hv : TyNode E n Γ value A)
      (hb : TyNode E n (.letBinding A value :: Γ) body B)
      (hT : TyNode E n Γ (instantiate0 value B) (.sort w)) :
      TyNode E n Γ (.letE A value body) (instantiate0 value B)
  | lit (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) (T : Expr Nat)
      (hexp : TyNode E n Γ (natExpand t) T) : TyNode E n Γ (.lit t) T
  | conv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A B : Expr Nat) (u : Level)
      (h : TyNode E n Γ e A) (hc : CvNode E n Γ A B (.sort u)) : TyNode E n Γ e B
  | wk (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) (d : LocalDecl) (c : Nat)
      (D : TyNode E n Γ e A) : TyNode E n (insertAt d c Γ) (lift c 1 e) (lift c 1 A)
  | esub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A t v : Expr Nat) (j : Nat) (u : Level)
      (D : TyNode E n Γ e A) (hget : Γ[j]? = some (.assumption t))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      TyNode E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  | lsub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A t v : Expr Nat) (j : Nat) (u : Level)
      (D : TyNode E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      TyNode E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  | linst (E : ResolvedEnv) (a n : Nat) (Γ : LCtx) (e A : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a) (D : TyNode E a Γ e A) :
      TyNode E n (instLvlsCtx ls Γ) (instantiateLevels ls e) (instantiateLevels ls A)
  | ewk (E₀ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) (hext : EnvExt E₀ E)
      (D : TyNode E₀ n Γ e A) : TyNode E n Γ e A
  | cctx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T A A' : Expr Nat) (u : Level)
      (D : TyNode E n (.assumption A :: Γ) e T) (hA : CvNode E n Γ A A' (.sort u)) :
      TyNode E n (.assumption A' :: Γ) e T

/-- The raw conversion-node grammar: one arm per original `CvP` constructor,
    keeping all actual fields (the `dl`/`dr` endpoint typings included —
    `refl` 3, `trans` 4, `irr` 5, `tyConv` 4 as in the S7 §6 table). -/
inductive CvNode : ResolvedEnv → Nat → LCtx → Expr Nat → Expr Nat → Expr Nat → Type
  | refl (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a A : Expr Nat) (h : TyNode E n Γ a A)
      (dl dr : TyNode E n Γ a A) : CvNode E n Γ a a A
  | symm (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b A : Expr Nat) (h : CvNode E n Γ a b A)
      (dl : TyNode E n Γ b A) (dr : TyNode E n Γ a A) : CvNode E n Γ b a A
  | trans (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b c A : Expr Nat) (h1 : CvNode E n Γ a b A)
      (h2 : CvNode E n Γ b c A) (dl : TyNode E n Γ a A) (dr : TyNode E n Γ c A) :
      CvNode E n Γ a c A
  | beta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A body arg B : Expr Nat) (u : Level)
      (hA : TyNode E n Γ A (.sort u)) (hbody : TyNode E n (.assumption A :: Γ) body B)
      (harg : TyNode E n Γ arg A)
      (dl : TyNode E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
      (dr : TyNode E n Γ (instantiate0 arg body) (instantiate0 arg B)) :
      CvNode E n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B)
  | zeta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A value body B : Expr Nat) (u : Level)
      (hA : TyNode E n Γ A (.sort u)) (hv : TyNode E n Γ value A)
      (hb : TyNode E n (.letBinding A value :: Γ) body B)
      (dl : TyNode E n Γ (.letE A value body) (instantiate0 value B))
      (dr : TyNode E n Γ (instantiate0 value body) (instantiate0 value B)) :
      CvNode E n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B)
  | zetaLocal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) (A v : Expr Nat)
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyNode E n Γ v A)
      (dl : TyNode E n Γ (.bvar i) A) (dr : TyNode E n Γ v A) : CvNode E n Γ (.bvar i) v A
  | delta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
      (b : Expr Nat) (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hb : TyNode E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
      (dl : TyNode E n Γ (.const r ls) (instantiateLevels ls m.mtype))
      (dr : TyNode E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
      CvNode E n Γ (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype)
  | iota (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (lhs rhs T : Expr Nat) (h : DerivedIota E lhs rhs)
      (hlhs : TyNode E n Γ lhs T) (hrhs : TyNode E n Γ rhs T)
      (dl : TyNode E n Γ lhs T) (dr : TyNode E n Γ rhs T) : CvNode E n Γ lhs rhs T
  | lit (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) (exp T : Expr Nat)
      (h : LiteralExpansion t exp) (hexp : TyNode E n Γ exp T)
      (dl : TyNode E n Γ (.lit t) T) (dr : TyNode E n Γ exp T) : CvNode E n Γ (.lit t) exp T
  | app (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f g a b A B : Expr Nat)
      (h1 : CvNode E n Γ f g (.pi A B)) (h2 : CvNode E n Γ a b A)
      (dl : TyNode E n Γ (.app f a) (instantiate0 a B))
      (dr : TyNode E n Γ (.app g b) (instantiate0 a B)) :
      CvNode E n Γ (.app f a) (.app g b) (instantiate0 a B)
  | lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' b b' B : Expr Nat) (u : Level)
      (hA : CvNode E n Γ A A' (.sort u)) (hb : CvNode E n (.assumption A :: Γ) b b' B)
      (dl : TyNode E n Γ (.lam A b) (.pi A B)) (dr : TyNode E n Γ (.lam A' b') (.pi A B)) :
      CvNode E n Γ (.lam A b) (.lam A' b') (.pi A B)
  | pi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' B B' : Expr Nat) (u v : Level)
      (hA : CvNode E n Γ A A' (.sort u)) (hB : CvNode E n (.assumption A :: Γ) B B' (.sort v))
      (dl : TyNode E n Γ (.pi A B) (.sort (.imax u v)))
      (dr : TyNode E n Γ (.pi A' B') (.sort (.imax u v))) :
      CvNode E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))
  | letE (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' v v' b b' B : Expr Nat) (u : Level)
      (hA : CvNode E n Γ A A' (.sort u)) (hv : CvNode E n Γ v v' A)
      (hb : CvNode E n (.letBinding A v :: Γ) b b' B)
      (dl : TyNode E n Γ (.letE A v b) (instantiate0 v B))
      (dr : TyNode E n Γ (.letE A' v' b') (instantiate0 v B)) :
      CvNode E n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B)
  | sorts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂)
      (dl : TyNode E n Γ (.sort l₁) (.sort (.succ l₁)))
      (dr : TyNode E n Γ (.sort l₂) (.sort (.succ l₁))) :
      CvNode E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))
  | consts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls ls' : List Level)
      (m : CheckedMember) (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls')
      (dl : TyNode E n Γ (.const r ls) (instantiateLevels ls m.mtype))
      (dr : TyNode E n Γ (.const r ls') (instantiateLevels ls m.mtype)) :
      CvNode E n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype)
  | eta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f A B : Expr Nat) (h : TyNode E n Γ f (.pi A B))
      (dl : TyNode E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
      (dr : TyNode E n Γ f (.pi A B)) :
      CvNode E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B)
  | irr (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (P p q : Expr Nat)
      (hP : TyNode E n Γ P (.sort .zero))
      (hp : TyNode E n Γ p P) (hq : TyNode E n Γ q P)
      (dl : TyNode E n Γ p P) (dr : TyNode E n Γ q P) : CvNode E n Γ p q P
  | tyConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b A A' : Expr Nat) (u : Level)
      (h : CvNode E n Γ a b A) (hA : CvNode E n Γ A A' (.sort u))
      (dl : TyNode E n Γ a A') (dr : TyNode E n Γ b A') : CvNode E n Γ a b A'
  | wk (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T : Expr Nat) (d : LocalDecl) (c : Nat)
      (h : CvNode E n Γ a b T) :
      CvNode E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | esub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T t v : Expr Nat) (j : Nat) (u : Level)
      (h : CvNode E n Γ a b T) (hget : Γ[j]? = some (.assumption t))
      (hv : TyNode E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyNode E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      CvNode E n (substRemove v j Γ) (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
        (instantiate j (lift 0 j v) T)
  | linst (E : ResolvedEnv) (a' n : Nat) (Γ : LCtx) (a b T : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a') (h : CvNode E a' Γ a b T) :
      CvNode E n (instLvlsCtx ls Γ) (instantiateLevels ls a) (instantiateLevels ls b)
        (instantiateLevels ls T)
  | ewk (E₀ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T : Expr Nat) (hext : EnvExt E₀ E)
      (h : CvNode E₀ n Γ a b T) : CvNode E n Γ a b T
  | cctx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T A A' : Expr Nat) (u : Level)
      (h : CvNode E n (.assumption A :: Γ) a b T) (hA : CvNode E n Γ A A' (.sort u)) :
      CvNode E n (.assumption A' :: Γ) a b T
  | fsub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B S a b : Expr Nat) (u : Level)
      (hB : TyNode E n (.assumption A :: Γ) B S) (hA : TyNode E n Γ A (.sort u))
      (hab : CvNode E n Γ a b A)
      (dl : TyNode E n Γ (instantiate0 a B) (instantiate0 a S))
      (dr : TyNode E n Γ (instantiate0 b B) (instantiate0 a S)) :
      CvNode E n Γ (instantiate0 a B) (instantiate0 b B) (instantiate0 a S)

/-- The raw context-node grammar: the three original `CtxP` constructors,
    nothing else. -/
inductive CtxNode : ResolvedEnv → Nat → LCtx → Type
  | nil (E : ResolvedEnv) (n : Nat) : CtxNode E n []
  | assumption (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level)
      (hΓ : CtxNode E n Γ) (hA : TyNode E n Γ A (.sort u)) :
      CtxNode E n (.assumption A :: Γ)
  | letBinding (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) (v : Expr Nat)
      (hΓ : CtxNode E n Γ) (hA : TyNode E n Γ A (.sort u)) (hv : TyNode E n Γ v A) :
      CtxNode E n (.letBinding A v :: Γ)

end

/-- A `RawForest` object: one original grammar node with its indices
    existentially recorded. -/
inductive RawForest : Type where
  | ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} :
      TyNode E n Γ e T → RawForest
  | cv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
      CvNode E n Γ a b T → RawForest
  | ctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
      CtxNode E n Γ → RawForest

/-- A node's direct derivation-field positions, in declaration order.
    Non-derivation fields are recorded in place on the node itself. -/
def TyNode.children : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyNode E n Γ e T → List RawForest
  | _, _, _, _, _, .sort .. => []
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ hA => [.ty hA]
  | _, _, _, _, _, .const _ _ _ _ _ _ _ _ _ _ _ _ hT => [.ty hT]
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => [.ty hA, .ty hB]
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ hA hbody hB => [.ty hA, .ty hbody, .ty hB]
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT => [.ty hf, .ty ha, .ty hT]
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT =>
      [.ty hA, .ty hv, .ty hb, .ty hT]
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => [.ty hexp]
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h hc => [.ty h, .cv hc]
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => [.ty D]
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT => [.ty D, .ty hv, .ty hvT]
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT => [.ty D, .ty hv, .ty hvT]
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => [.ty D]
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => [.ty D]
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => [.ty D, .cv hA]

/-- A conversion node's direct derivation-field positions, in declaration
    order. -/
def CvNode.children : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvNode E n Γ a b T → List RawForest
  | _, _, _, _, _, _, .refl _ _ _ _ _ h dl dr => [.ty h, .ty dl, .ty dr]
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ h dl dr => [.cv h, .ty dl, .ty dr]
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ h1 h2 dl dr => [.cv h1, .cv h2, .ty dl, .ty dr]
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ hA hbody harg dl dr =>
      [.ty hA, .ty hbody, .ty harg, .ty dl, .ty dr]
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      [.ty hA, .ty hv, .ty hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ hv dl dr => [.ty hv, .ty dl, .ty dr]
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ hb dl dr => [.ty hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ hlhs hrhs dl dr =>
      [.ty hlhs, .ty hrhs, .ty dl, .ty dr]
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ hexp dl dr => [.ty hexp, .ty dl, .ty dr]
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 dl dr => [.cv h1, .cv h2, .ty dl, .ty dr]
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hA hb dl dr => [.cv hA, .cv hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ hA hB dl dr => [.cv hA, .cv hB, .ty dl, .ty dr]
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      [.cv hA, .cv hv, .cv hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl dr => [.ty dl, .ty dr]
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl dr => [.ty dl, .ty dr]
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ h dl dr => [.ty h, .ty dl, .ty dr]
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ hP hp hq dl dr =>
      [.ty hP, .ty hp, .ty hq, .ty dl, .ty dr]
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h hA dl dr => [.cv h, .cv hA, .ty dl, .ty dr]
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => [.cv h]
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ hv hvT => [.cv h, .ty hv, .ty hvT]
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => [.cv h]
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => [.cv h]
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA => [.cv h, .cv hA]
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ hB hA hab dl dr =>
      [.ty hB, .ty hA, .cv hab, .ty dl, .ty dr]

/-- A context node's direct derivation-field positions. -/
def CtxNode.children : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxNode E n Γ → List RawForest
  | _, _, _, .nil _ _ => []
  | _, _, _, .assumption _ _ _ _ _ hΓ hA => [.ctx hΓ, .ty hA]
  | _, _, _, .letBinding _ _ _ _ _ _ hΓ hA hv => [.ctx hΓ, .ty hA, .ty hv]

/-- The direct field positions of a raw-forest object. -/
def RawForest.children : RawForest → List RawForest
  | .ty n => n.children
  | .cv n => n.children
  | .ctx n => n.children

/-! ## §1 totality of the structural traversal -/

mutual

/-- Every original `TyP` has its `TyNode`: the traversal is total (it never
    deletes or rewrites an original request). -/
def TyP.toTyNode : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → TyNode E n Γ e T
  | _, _, _, _, _, .sort E n Γ l k h => .sort E n Γ l k h
  | _, _, _, _, _, .bvar E n Γ i A u h hA => .bvar E n Γ i A u h hA.toTyNode
  | _, _, _, _, _, .const E n Γ r ls ls₀ m u hres hlen hwf hls hT =>
      .const E n Γ r ls ls₀ m u hres hlen hwf hls hT.toTyNode
  | _, _, _, _, _, .pi E n Γ A u B v hA hB => .pi E n Γ A u B v hA.toTyNode hB.toTyNode
  | _, _, _, _, _, .lam E n Γ A u body B v hA hbody hB =>
      .lam E n Γ A u body B v hA.toTyNode hbody.toTyNode hB.toTyNode
  | _, _, _, _, _, .app E n Γ f a A B w hf ha hT =>
      .app E n Γ f a A B w hf.toTyNode ha.toTyNode hT.toTyNode
  | _, _, _, _, _, .letE E n Γ A u value B body w hA hv hb hT =>
      .letE E n Γ A u value B body w hA.toTyNode hv.toTyNode hb.toTyNode hT.toTyNode
  | _, _, _, _, _, .lit E n Γ t T hexp => .lit E n Γ t T hexp.toTyNode
  | _, _, _, _, _, .conv E n Γ e A B u h hc => .conv E n Γ e A B u h.toTyNode hc.toCvNode
  | _, _, _, _, _, .wk E n Γ e A d c D => .wk E n Γ e A d c D.toTyNode
  | _, _, _, _, _, .esub E n Γ e A t v j u D hget hv hvT =>
      .esub E n Γ e A t v j u D.toTyNode hget hv.toTyNode hvT.toTyNode
  | _, _, _, _, _, .lsub E n Γ e A t v j u D hget hv hvT =>
      .lsub E n Γ e A t v j u D.toTyNode hget hv.toTyNode hvT.toTyNode
  | _, _, _, _, _, .linst E a n Γ e A ls hls hlen D => .linst E a n Γ e A ls hls hlen D.toTyNode
  | _, _, _, _, _, .ewk E₀ E n Γ e A hext D => .ewk E₀ E n Γ e A hext D.toTyNode
  | _, _, _, _, _, .cctx E n Γ e T A A' u D hA => .cctx E n Γ e T A A' u D.toTyNode hA.toCvNode

/-- Every original `CvP` has its `CvNode`. -/
def CvP.toCvNode : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T → CvNode E n Γ a b T
  | _, _, _, _, _, _, .refl E n Γ a A h dl dr =>
      .refl E n Γ a A h.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .symm E n Γ a b A h dl dr =>
      .symm E n Γ a b A h.toCvNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .trans E n Γ a b c A h1 h2 dl dr =>
      .trans E n Γ a b c A h1.toCvNode h2.toCvNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .beta E n Γ A body arg B u hA hbody harg dl dr =>
      .beta E n Γ A body arg B u hA.toTyNode hbody.toTyNode harg.toTyNode
        dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .zeta E n Γ A value body B u hA hv hb dl dr =>
      .zeta E n Γ A value body B u hA.toTyNode hv.toTyNode hb.toTyNode
        dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .zetaLocal E n Γ i A v hval hty hv dl dr =>
      .zetaLocal E n Γ i A v hval hty hv.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr =>
      .delta E n Γ r ls m b hres hbody htr hlen hwf hb.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .iota E n Γ lhs rhs T h hlhs hrhs dl dr =>
      .iota E n Γ lhs rhs T h hlhs.toTyNode hrhs.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .lit E n Γ t exp T h hexp dl dr =>
      .lit E n Γ t exp T h hexp.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .app E n Γ f g a b A B h1 h2 dl dr =>
      .app E n Γ f g a b A B h1.toCvNode h2.toCvNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .lam E n Γ A A' b b' B u hA hb dl dr =>
      .lam E n Γ A A' b b' B u hA.toCvNode hb.toCvNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .pi E n Γ A A' B B' u v hA hB dl dr =>
      .pi E n Γ A A' B B' u v hA.toCvNode hB.toCvNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .letE E n Γ A A' v v' b b' B u hA hv hb dl dr =>
      .letE E n Γ A A' v v' b b' B u hA.toCvNode hv.toCvNode hb.toCvNode
        dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .sorts E n Γ l₁ l₂ h dl dr =>
      .sorts E n Γ l₁ l₂ h dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr =>
      .consts E n Γ r ls ls' m hres hlen hwf hwf' h dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .eta E n Γ f A B h dl dr =>
      .eta E n Γ f A B h.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .irr E n Γ P p q hP hp hq dl dr =>
      .irr E n Γ P p q hP.toTyNode hp.toTyNode hq.toTyNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .tyConv E n Γ a b A A' u h hA dl dr =>
      .tyConv E n Γ a b A A' u h.toCvNode hA.toCvNode dl.toTyNode dr.toTyNode
  | _, _, _, _, _, _, .wk E n Γ a b T d c h => .wk E n Γ a b T d c h.toCvNode
  | _, _, _, _, _, _, .esub E n Γ a b T t v j u h hget hv hvT =>
      .esub E n Γ a b T t v j u h.toCvNode hget hv.toTyNode hvT.toTyNode
  | _, _, _, _, _, _, .linst E a' n Γ a b T ls hls hlen h =>
      .linst E a' n Γ a b T ls hls hlen h.toCvNode
  | _, _, _, _, _, _, .ewk E₀ E n Γ a b T hext h => .ewk E₀ E n Γ a b T hext h.toCvNode
  | _, _, _, _, _, _, .cctx E n Γ a b T A A' u h hA =>
      .cctx E n Γ a b T A A' u h.toCvNode hA.toCvNode
  | _, _, _, _, _, _, .fsub E n Γ A B S a b u hB hA hab dl dr =>
      .fsub E n Γ A B S a b u hB.toTyNode hA.toTyNode hab.toCvNode dl.toTyNode dr.toTyNode

/-- Every original `CtxP` has its `CtxNode`. -/
def CtxP.toCtxNode : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → CtxNode E n Γ
  | _, _, _, .nil E n => .nil E n
  | _, _, _, .assumption E n Γ A u hΓ hA => .assumption E n Γ A u hΓ.toCtxNode hA.toTyNode
  | _, _, _, .letBinding E n Γ A u v hΓ hA hv =>
      .letBinding E n Γ A u v hΓ.toCtxNode hA.toTyNode hv.toTyNode

end

end Rcic.Syn
