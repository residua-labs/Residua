import rcic.RcicConvPlus
import rcic.RcicSynAdm

/-!
# Syntactic sortRow, build step 3i — heads of a typing

`research/rcic/semantic/S3_ES_ARMS.md` §10. `sortHead` (`RcicSynSortView`) is the
case split for a typing of `.sort l`. The same split for `.app`, `.lam`, `.pi`,
`.const`, `.letE` and `.lit` is what generation and `CL` case on when the two
sides of a term carry different transport stacks (`S1` §4.3): one step of
`wk` / `esub` / `linst` / `ewk` / `cctx` / `conv`, or the rule node, or the
substituted variable whose replacement is that head.

A head is born in two places only. `lift`, `instantiate` and `instantiateLevels`
preserve these six constructors — except `instantiate` at the substituted
index, which returns the replacement. That hit is `esub_var`. A constant and a
literal are lift-invariant, so there `v` itself is the head. An application, a
λ, a Π and a `let` are not: the equation is `lift 0 j v =` the head, and
`cases` on it does not fire (`lift` is not a variable), so the view rewrites
by `▸`. On the `drop` path the erasure of that variable can be `★` even though
the term is the replacement; the view does not claim an erasure shape.

`.bvar` moves under `lift` and `instantiate`, so it is not this shape.
`bvarHead` (`RcicSynBvarView`) is that arithmetic split. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 application -/

/-- `lift c k e = app f a` names the application `e` was. -/
inductive LiftApp (c k : Nat) (e f a : Expr Nat) : Type where
  | mk (f₀ a₀ : Expr Nat) (he : e = .app f₀ a₀)
      (hf : lift c k f₀ = f) (ha : lift c k a₀ = a) : LiftApp c k e f a

def lift_eq_app {c k : Nat} {e f a : Expr Nat} (h : lift c k e = .app f a) :
    LiftApp c k e f a := by
  cases e with
  | app f₀ a₀ =>
    injection h with hf ha
    exact .mk f₀ a₀ rfl hf ha
  | bvar i =>
    unfold lift at h
    split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- `instantiate j r e = app f a` is either an application `e`, or the hit
    variable whose replacement is that application. A `Type`, so the view can
    eliminate it (`S3` §9: `Or` does not eliminate into `Type`). -/
inductive InstApp (j : Nat) (r e f a : Expr Nat) : Type where
  | under (f₀ a₀ : Expr Nat) (he : e = .app f₀ a₀)
      (hf : instantiate j r f₀ = f) (ha : instantiate j r a₀ = a) : InstApp j r e f a
  | here (he : e = .bvar j) (hr : r = .app f a) : InstApp j r e f a

def instantiate_eq_app {j : Nat} {r e f a : Expr Nat}
    (h : instantiate j r e = .app f a) : InstApp j r e f a := by
  cases e with
  | app f₀ a₀ =>
    injection h with hf ha
    exact .under f₀ a₀ rfl hf ha
  | bvar i =>
    unfold instantiate at h
    split at h
    · next hi =>
      cases hi
      exact .here rfl h
    · split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- `instantiateLevels` does not change an application's shape. -/
inductive LinstApp (ls : List Level) (e f a : Expr Nat) : Type where
  | mk (f₀ a₀ : Expr Nat) (he : e = .app f₀ a₀)
      (hf : instantiateLevels ls f₀ = f) (ha : instantiateLevels ls a₀ = a) :
      LinstApp ls e f a

def instantiateLevels_eq_app {ls : List Level} {e f a : Expr Nat}
    (h : instantiateLevels ls e = .app f a) : LinstApp ls e f a := by
  cases e with
  | app f₀ a₀ =>
    injection h with hf ha
    exact .mk f₀ a₀ rfl hf ha
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- How a derivation of `.app f a` is built. One transport, or the `app` node,
    or the variable whose replacement is that application. -/
inductive AppHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f a T : Expr Nat) : Type
  | node (A B : Expr Nat) (w : Level)
      (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
      (hT : TyP E n Γ (instantiate0 a B) (.sort w))
      (hTy : T = instantiate0 a B)
  | conv (A B : Expr Nat) (u : Level) (inner : TyP E n Γ (.app f a) A)
      (hc : CvP E n Γ A B (.sort u)) (hT : T = B)
  | wk (Γ₀ : LCtx) (A f₀ a₀ : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.app f₀ a₀) A) (hΓ : Γ = insertAt d c Γ₀)
      (hf : lift c 1 f₀ = f) (ha : lift c 1 a₀ = a) (hT : T = lift c 1 A)
  | esub_app (Γ₀ : LCtx) (A t v f₀ a₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.app f₀ a₀) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hf : instantiate j (lift 0 j v) f₀ = f)
      (ha : instantiate j (lift 0 j v) a₀ = a)
      (hT : T = instantiate j (lift 0 j v) A)
  | lsub_app (Γ₀ : LCtx) (A t v f₀ a₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.app f₀ a₀) A) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hf : instantiate j (lift 0 j v) f₀ = f)
      (ha : instantiate j (lift 0 j v) a₀ = a)
      (hT : T = instantiate j (lift 0 j v) A)
  | esub_var (Γ₀ : LCtx) (A t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.app f a) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .app f a)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.app f a) A)
  | lsub_var (Γ₀ : LCtx) (A t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) A) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (.app f a) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .app f a)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.app f a) A)
  | linst (src : Nat) (Γ₀ : LCtx) (A f₀ a₀ : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = src)
      (inner : TyP E src Γ₀ (.app f₀ a₀) A)
      (hf : instantiateLevels ls f₀ = f) (ha : instantiateLevels ls a₀ = a)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls A)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.app f a) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (A A' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption A :: Γtail) (.app f a) T)
      (hA : CvP E n Γtail A A' (.sort u)) (hΓ : Γ = .assumption A' :: Γtail)

def appHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a T : Expr Nat}
    (D : TyP E n Γ (.app f a) T) : AppHead E n Γ f a T := by
  generalize he : Expr.app f a = e at D
  cases D
  case app f' a' A B w hf ha hT =>
    cases he
    exact .node A B w hf ha hT rfl
  case conv A u inner hc =>
    cases he
    exact .conv A T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case sort => cases he
  case const => cases he
  case pi => cases he
  case lam => cases he
  case letE => cases he
  case lit => cases he
  case wk Γ₀ e₀ A d c inner =>
    cases lift_eq_app he.symm with
    | mk f₀ a₀ hs hf ha =>
      cases hs
      exact .wk Γ₀ A f₀ a₀ d c inner rfl hf ha rfl
  case esub Γ₀ e₀ A t v j u hget inner hv hvT =>
    cases instantiate_eq_app he.symm with
    | under f₀ a₀ hs hf ha =>
      cases hs
      exact .esub_app Γ₀ A t v f₀ a₀ j u inner hget hv hvT rfl hf ha rfl
    | here hs hr =>
      cases hs
      exact .esub_var Γ₀ A t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e A) hr)
  case lsub Γ₀ e₀ A t v j u hget inner hv hvT =>
    cases instantiate_eq_app he.symm with
    | under f₀ a₀ hs hf ha =>
      cases hs
      exact .lsub_app Γ₀ A t v f₀ a₀ j u inner hget hv hvT rfl hf ha rfl
    | here hs hr =>
      cases hs
      exact .lsub_var Γ₀ A t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e A) hr)
  case linst src Γ₀ e₀ A ls hlen inner hls =>
    cases instantiateLevels_eq_app he.symm with
    | mk f₀ a₀ hs hf ha =>
      cases hs
      exact .linst src Γ₀ A f₀ a₀ ls hls hlen inner hf ha rfl rfl
  case cctx Γtail A A' u hA inner =>
    cases he
    exact .cctx Γtail A A' u inner hA rfl

/-! ## §2 lambda -/

/-- `lift c k e = lam A b` names the λ `e` was. The body is lifted one cutoff deeper. -/
inductive LiftLam (c k : Nat) (e A b : Expr Nat) : Type where
  | mk (A₀ b₀ : Expr Nat) (he : e = .lam A₀ b₀)
      (hA : lift c k A₀ = A) (hb : lift (c + 1) k b₀ = b) : LiftLam c k e A b

def lift_eq_lam {c k : Nat} {e A b : Expr Nat} (h : lift c k e = .lam A b) :
    LiftLam c k e A b := by
  cases e with
  | lam A₀ b₀ =>
    injection h with hA hb
    exact .mk A₀ b₀ rfl hA hb
  | bvar i =>
    unfold lift at h
    split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- `instantiate j r e = lam A b`. Under the binder the index shifts and the
    replacement is lifted, matching `Expr.instantiate`. -/
inductive InstLam (j : Nat) (r e A b : Expr Nat) : Type where
  | under (A₀ b₀ : Expr Nat) (he : e = .lam A₀ b₀)
      (hA : instantiate j r A₀ = A)
      (hb : instantiate (j + 1) (lift 0 1 r) b₀ = b) : InstLam j r e A b
  | here (he : e = .bvar j) (hr : r = .lam A b) : InstLam j r e A b

def instantiate_eq_lam {j : Nat} {r e A b : Expr Nat}
    (h : instantiate j r e = .lam A b) : InstLam j r e A b := by
  cases e with
  | lam A₀ b₀ =>
    injection h with hA hb
    exact .under A₀ b₀ rfl hA hb
  | bvar i =>
    unfold instantiate at h
    split at h
    · next hi =>
      cases hi
      exact .here rfl h
    · split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive LinstLam (ls : List Level) (e A b : Expr Nat) : Type where
  | mk (A₀ b₀ : Expr Nat) (he : e = .lam A₀ b₀)
      (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = b) :
      LinstLam ls e A b

def instantiateLevels_eq_lam {ls : List Level} {e A b : Expr Nat}
    (h : instantiateLevels ls e = .lam A b) : LinstLam ls e A b := by
  cases e with
  | lam A₀ b₀ =>
    injection h with hA hb
    exact .mk A₀ b₀ rfl hA hb
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- How a derivation of `.lam A body` is built. The inner type is not the λ's
    domain: transports rename the ascribed type separately. -/
inductive LamHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A body T : Expr Nat) : Type
  | node (u : Level) (B : Expr Nat) (v : Level)
      (hA : TyP E n Γ A (.sort u))
      (hbody : TyP E n (.assumption A :: Γ) body B)
      (hB : TyP E n (.assumption A :: Γ) B (.sort v))
      (hT : T = .pi A B)
  | conv (Ty₀ B : Expr Nat) (u : Level) (inner : TyP E n Γ (.lam A body) Ty₀)
      (hc : CvP E n Γ Ty₀ B (.sort u)) (hT : T = B)
  | wk (Γ₀ : LCtx) (Ty₀ A₀ b₀ : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.lam A₀ b₀) Ty₀) (hΓ : Γ = insertAt d c Γ₀)
      (hA : lift c 1 A₀ = A) (hb : lift (c + 1) 1 b₀ = body) (hT : T = lift c 1 Ty₀)
  | esub_lam (Γ₀ : LCtx) (Ty₀ t v A₀ b₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.lam A₀ b₀) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hA : instantiate j (lift 0 j v) A₀ = A)
      (hb : instantiate (j + 1) (lift 0 1 (lift 0 j v)) b₀ = body)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | lsub_lam (Γ₀ : LCtx) (Ty₀ t v A₀ b₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.lam A₀ b₀) Ty₀) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hA : instantiate j (lift 0 j v) A₀ = A)
      (hb : instantiate (j + 1) (lift 0 1 (lift 0 j v)) b₀ = body)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | esub_var (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.lam A body) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .lam A body)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.lam A body) Ty₀)
  | lsub_var (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (.lam A body) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .lam A body)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.lam A body) Ty₀)
  | linst (src : Nat) (Γ₀ : LCtx) (Ty₀ A₀ b₀ : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = src)
      (inner : TyP E src Γ₀ (.lam A₀ b₀) Ty₀)
      (hA : instantiateLevels ls A₀ = A) (hb : instantiateLevels ls b₀ = body)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls Ty₀)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.lam A body) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (Dom Dom' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption Dom :: Γtail) (.lam A body) T)
      (hDom : CvP E n Γtail Dom Dom' (.sort u)) (hΓ : Γ = .assumption Dom' :: Γtail)

def lamHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body T : Expr Nat}
    (D : TyP E n Γ (.lam A body) T) : LamHead E n Γ A body T := by
  generalize he : Expr.lam A body = e at D
  cases D
  case lam A' u body' B v hA hbody hB =>
    cases he
    exact .node u B v hA hbody hB rfl
  case conv Ty₀ u inner hc =>
    cases he
    exact .conv Ty₀ T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case sort => cases he
  case const => cases he
  case pi => cases he
  case app => cases he
  case letE => cases he
  case lit => cases he
  case wk Γ₀ e₀ Ty₀ d c inner =>
    cases lift_eq_lam he.symm with
    | mk A₀ b₀ hs hA hb =>
      cases hs
      exact .wk Γ₀ Ty₀ A₀ b₀ d c inner rfl hA hb rfl
  case esub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_lam he.symm with
    | under A₀ b₀ hs hA hb =>
      cases hs
      exact .esub_lam Γ₀ Ty₀ t v A₀ b₀ j u inner hget hv hvT rfl hA hb rfl
    | here hs hr =>
      cases hs
      exact .esub_var Γ₀ Ty₀ t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e Ty₀) hr)
  case lsub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_lam he.symm with
    | under A₀ b₀ hs hA hb =>
      cases hs
      exact .lsub_lam Γ₀ Ty₀ t v A₀ b₀ j u inner hget hv hvT rfl hA hb rfl
    | here hs hr =>
      cases hs
      exact .lsub_var Γ₀ Ty₀ t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e Ty₀) hr)
  case linst src Γ₀ e₀ Ty₀ ls hlen inner hls =>
    cases instantiateLevels_eq_lam he.symm with
    | mk A₀ b₀ hs hA hb =>
      cases hs
      exact .linst src Γ₀ Ty₀ A₀ b₀ ls hls hlen inner hA hb rfl rfl
  case cctx Γtail Dom Dom' u hDom inner =>
    cases he
    exact .cctx Γtail Dom Dom' u inner hDom rfl

/-! ## §3 pi -/

/-- `lift c k e = pi A B`. The codomain is lifted one cutoff deeper. -/
inductive LiftPi (c k : Nat) (e A B : Expr Nat) : Type where
  | mk (A₀ B₀ : Expr Nat) (he : e = .pi A₀ B₀)
      (hA : lift c k A₀ = A) (hB : lift (c + 1) k B₀ = B) : LiftPi c k e A B

def lift_eq_pi {c k : Nat} {e A B : Expr Nat} (h : lift c k e = .pi A B) :
    LiftPi c k e A B := by
  cases e with
  | pi A₀ B₀ =>
    injection h with hA hB
    exact .mk A₀ B₀ rfl hA hB
  | bvar i =>
    unfold lift at h
    split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive InstPi (j : Nat) (r e A B : Expr Nat) : Type where
  | under (A₀ B₀ : Expr Nat) (he : e = .pi A₀ B₀)
      (hA : instantiate j r A₀ = A)
      (hB : instantiate (j + 1) (lift 0 1 r) B₀ = B) : InstPi j r e A B
  | here (he : e = .bvar j) (hr : r = .pi A B) : InstPi j r e A B

def instantiate_eq_pi {j : Nat} {r e A B : Expr Nat}
    (h : instantiate j r e = .pi A B) : InstPi j r e A B := by
  cases e with
  | pi A₀ B₀ =>
    injection h with hA hB
    exact .under A₀ B₀ rfl hA hB
  | bvar i =>
    unfold instantiate at h
    split at h
    · next hi =>
      cases hi
      exact .here rfl h
    · split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive LinstPi (ls : List Level) (e A B : Expr Nat) : Type where
  | mk (A₀ B₀ : Expr Nat) (he : e = .pi A₀ B₀)
      (hA : instantiateLevels ls A₀ = A) (hB : instantiateLevels ls B₀ = B) :
      LinstPi ls e A B

def instantiateLevels_eq_pi {ls : List Level} {e A B : Expr Nat}
    (h : instantiateLevels ls e = .pi A B) : LinstPi ls e A B := by
  cases e with
  | pi A₀ B₀ =>
    injection h with hA hB
    exact .mk A₀ B₀ rfl hA hB
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive PiHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B T : Expr Nat) : Type
  | node (u v : Level)
      (hA : TyP E n Γ A (.sort u))
      (hB : TyP E n (.assumption A :: Γ) B (.sort v))
      (hT : T = .sort (.imax u v))
  | conv (Ty₀ C : Expr Nat) (u : Level) (inner : TyP E n Γ (.pi A B) Ty₀)
      (hc : CvP E n Γ Ty₀ C (.sort u)) (hTy : T = C)
  | wk (Γ₀ : LCtx) (Ty₀ A₀ B₀ : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.pi A₀ B₀) Ty₀) (hΓ : Γ = insertAt d c Γ₀)
      (hA : lift c 1 A₀ = A) (hB : lift (c + 1) 1 B₀ = B) (hT : T = lift c 1 Ty₀)
  | esub_pi (Γ₀ : LCtx) (Ty₀ t v A₀ B₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.pi A₀ B₀) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hA : instantiate j (lift 0 j v) A₀ = A)
      (hB : instantiate (j + 1) (lift 0 1 (lift 0 j v)) B₀ = B)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | lsub_pi (Γ₀ : LCtx) (Ty₀ t v A₀ B₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.pi A₀ B₀) Ty₀) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hA : instantiate j (lift 0 j v) A₀ = A)
      (hB : instantiate (j + 1) (lift 0 1 (lift 0 j v)) B₀ = B)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | esub_var (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.pi A B) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .pi A B)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.pi A B) Ty₀)
  | lsub_var (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (.pi A B) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .pi A B)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.pi A B) Ty₀)
  | linst (src : Nat) (Γ₀ : LCtx) (Ty₀ A₀ B₀ : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = src)
      (inner : TyP E src Γ₀ (.pi A₀ B₀) Ty₀)
      (hA : instantiateLevels ls A₀ = A) (hB : instantiateLevels ls B₀ = B)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls Ty₀)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.pi A B) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (Dom Dom' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption Dom :: Γtail) (.pi A B) T)
      (hDom : CvP E n Γtail Dom Dom' (.sort u)) (hΓ : Γ = .assumption Dom' :: Γtail)

def piHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B T : Expr Nat}
    (D : TyP E n Γ (.pi A B) T) : PiHead E n Γ A B T := by
  generalize he : Expr.pi A B = e at D
  cases D
  case pi A' u B' v hA hB =>
    cases he
    exact .node u v hA hB rfl
  case conv Ty₀ u inner hc =>
    cases he
    exact .conv Ty₀ T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case sort => cases he
  case const => cases he
  case lam => cases he
  case app => cases he
  case letE => cases he
  case lit => cases he
  case wk Γ₀ e₀ Ty₀ d c inner =>
    cases lift_eq_pi he.symm with
    | mk A₀ B₀ hs hA hB =>
      cases hs
      exact .wk Γ₀ Ty₀ A₀ B₀ d c inner rfl hA hB rfl
  case esub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_pi he.symm with
    | under A₀ B₀ hs hA hB =>
      cases hs
      exact .esub_pi Γ₀ Ty₀ t v A₀ B₀ j u inner hget hv hvT rfl hA hB rfl
    | here hs hr =>
      cases hs
      exact .esub_var Γ₀ Ty₀ t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e Ty₀) hr)
  case lsub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_pi he.symm with
    | under A₀ B₀ hs hA hB =>
      cases hs
      exact .lsub_pi Γ₀ Ty₀ t v A₀ B₀ j u inner hget hv hvT rfl hA hB rfl
    | here hs hr =>
      cases hs
      exact .lsub_var Γ₀ Ty₀ t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e Ty₀) hr)
  case linst src Γ₀ e₀ Ty₀ ls hlen inner hls =>
    cases instantiateLevels_eq_pi he.symm with
    | mk A₀ B₀ hs hA hB =>
      cases hs
      exact .linst src Γ₀ Ty₀ A₀ B₀ ls hls hlen inner hA hB rfl rfl
  case cctx Γtail Dom Dom' u hDom inner =>
    cases he
    exact .cctx Γtail Dom Dom' u inner hDom rfl

/-! ## §4 constant

`lift` and `instantiate` off the hit variable leave a constant unchanged, so
those arms do not carry a component equation. `lift_eq_const_k` is that fact.
The hit variable rewrites `v` itself to the constant, because a constant is
lift-invariant — unlike an application, whose subterms may gain binders. -/

inductive InstConst (j : Nat) (r e : Expr Nat) (ref : Nat) (ls : List Level) : Type where
  | under (he : e = .const ref ls) : InstConst j r e ref ls
  | here (he : e = .bvar j) (hr : r = .const ref ls) : InstConst j r e ref ls

def instantiate_eq_const {j : Nat} {r e : Expr Nat} {ref : Nat} {ls : List Level}
    (h : instantiate j r e = .const ref ls) : InstConst j r e ref ls := by
  cases e with
  | const r' ms =>
    cases h
    exact .under rfl
  | bvar i =>
    unfold instantiate at h
    split at h
    · next hi =>
      cases hi
      exact .here rfl h
    · split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive LinstConst (ms : List Level) (e : Expr Nat) (ref : Nat) (ls : List Level) : Type where
  | mk (ls₀ : List Level) (he : e = .const ref ls₀) (hl : ls₀.map (instLevel ms) = ls) :
      LinstConst ms e ref ls

def instantiateLevels_eq_const {ms : List Level} {e : Expr Nat} {ref : Nat} {ls : List Level}
    (h : instantiateLevels ms e = .const ref ls) : LinstConst ms e ref ls := by
  cases e with
  | const r' ls₀ =>
    injection h with hr hl
    cases hr
    exact .mk ls₀ rfl hl
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive ConstHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls : List Level)
    (T : Expr Nat) : Type
  | node (ls₀ : List Level) (m : CheckedMember) (u : Level)
      (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
      (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u))
      (hTy : T = instantiateLevels ls₀ m.mtype)
  | conv (Ty₀ B : Expr Nat) (u : Level) (inner : TyP E n Γ (.const r ls) Ty₀)
      (hc : CvP E n Γ Ty₀ B (.sort u)) (hT : T = B)
  | wk (Γ₀ : LCtx) (Ty₀ : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.const r ls) Ty₀) (hΓ : Γ = insertAt d c Γ₀)
      (hT : T = lift c 1 Ty₀)
  | esub_const (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.const r ls) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | lsub_const (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.const r ls) Ty₀) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | esub_var (Γ₀ : LCtx) (Ty₀ t : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.const r ls) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove (.const r ls) j Γ₀)
      (hT : T = instantiate j (.const r ls) Ty₀)
  | lsub_var (Γ₀ : LCtx) (Ty₀ t : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.letBinding t (.const r ls)))
      (hv : TyP E n Γ (.const r ls) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove (.const r ls) j Γ₀)
      (hT : T = instantiate j (.const r ls) Ty₀)
  | linst (src : Nat) (Γ₀ : LCtx) (Ty₀ : Expr Nat) (ls₀ ms : List Level)
      (hls : levelsBounded n ms = true) (hlen : ms.length = src)
      (inner : TyP E src Γ₀ (.const r ls₀) Ty₀)
      (hl : ls₀.map (instLevel ms) = ls)
      (hΓ : Γ = instLvlsCtx ms Γ₀) (hT : T = instantiateLevels ms Ty₀)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.const r ls) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (Dom Dom' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption Dom :: Γtail) (.const r ls) T)
      (hDom : CvP E n Γtail Dom Dom' (.sort u)) (hΓ : Γ = .assumption Dom' :: Γtail)

def constHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level} {T : Expr Nat}
    (D : TyP E n Γ (.const r ls) T) : ConstHead E n Γ r ls T := by
  generalize he : Expr.const r ls = e at D
  cases D
  -- `cases` introduces the proofs as length, `eqNList`, resolution, boundedness, typing.
  case const r' ls' ls₀ m u hlen hls hres hwf hT =>
    cases he
    exact .node ls₀ m u hres hlen hwf hls hT rfl
  case conv Ty₀ u inner hc =>
    cases he
    exact .conv Ty₀ T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case sort => cases he
  case pi => cases he
  case lam => cases he
  case app => cases he
  case letE => cases he
  case lit => cases he
  case wk Γ₀ e₀ Ty₀ d c inner =>
    have hs : e₀ = .const r ls := lift_eq_const_k he.symm
    cases hs
    exact .wk Γ₀ Ty₀ d c inner rfl rfl
  case esub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_const he.symm with
    | under hs =>
      cases hs
      exact .esub_const Γ₀ Ty₀ t v j u inner hget hv hvT rfl rfl
    | here hs hr =>
      have hvconst : v = .const r ls := lift_eq_const_k hr
      cases hs
      cases hvconst
      exact .esub_var Γ₀ Ty₀ t j u inner hget hv hvT rfl rfl
  case lsub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_const he.symm with
    | under hs =>
      cases hs
      exact .lsub_const Γ₀ Ty₀ t v j u inner hget hv hvT rfl rfl
    | here hs hr =>
      have hvconst : v = .const r ls := lift_eq_const_k hr
      cases hs
      cases hvconst
      exact .lsub_var Γ₀ Ty₀ t j u inner hget hv hvT rfl rfl
  case linst src Γ₀ e₀ Ty₀ ms hlen inner hls =>
    cases instantiateLevels_eq_const he.symm with
    | mk ls₀ hs hl =>
      cases hs
      exact .linst src Γ₀ Ty₀ ls₀ ms hls hlen inner hl rfl rfl
  case cctx Γtail Dom Dom' u hDom inner =>
    cases he
    exact .cctx Γtail Dom Dom' u inner hDom rfl

/-! ## §5 let

The body is under the binder, so `lift` and `instantiate` shift it. The value
is not. A `let` is not lift-invariant, so `esub_var` keeps `v` and the lift
equation, as an application does. -/

inductive LiftLet (c k : Nat) (e A v b : Expr Nat) : Type where
  | mk (A₀ v₀ b₀ : Expr Nat) (he : e = .letE A₀ v₀ b₀)
      (hA : lift c k A₀ = A) (hv : lift c k v₀ = v)
      (hb : lift (c + 1) k b₀ = b) : LiftLet c k e A v b

def lift_eq_let {c k : Nat} {e A v b : Expr Nat} (h : lift c k e = .letE A v b) :
    LiftLet c k e A v b := by
  cases e with
  | letE A₀ v₀ b₀ =>
    injection h with hA hv hb
    exact .mk A₀ v₀ b₀ rfl hA hv hb
  | bvar i =>
    unfold lift at h
    split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive InstLet (j : Nat) (r e A v b : Expr Nat) : Type where
  | under (A₀ v₀ b₀ : Expr Nat) (he : e = .letE A₀ v₀ b₀)
      (hA : instantiate j r A₀ = A) (hv : instantiate j r v₀ = v)
      (hb : instantiate (j + 1) (lift 0 1 r) b₀ = b) : InstLet j r e A v b
  | here (he : e = .bvar j) (hr : r = .letE A v b) : InstLet j r e A v b

def instantiate_eq_let {j : Nat} {r e A v b : Expr Nat}
    (h : instantiate j r e = .letE A v b) : InstLet j r e A v b := by
  cases e with
  | letE A₀ v₀ b₀ =>
    injection h with hA hv hb
    exact .under A₀ v₀ b₀ rfl hA hv hb
  | bvar i =>
    unfold instantiate at h
    split at h
    · next hi =>
      cases hi
      exact .here rfl h
    · split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive LinstLet (ls : List Level) (e A v b : Expr Nat) : Type where
  | mk (A₀ v₀ b₀ : Expr Nat) (he : e = .letE A₀ v₀ b₀)
      (hA : instantiateLevels ls A₀ = A) (hv : instantiateLevels ls v₀ = v)
      (hb : instantiateLevels ls b₀ = b) : LinstLet ls e A v b

def instantiateLevels_eq_let {ls : List Level} {e A v b : Expr Nat}
    (h : instantiateLevels ls e = .letE A v b) : LinstLet ls e A v b := by
  cases e with
  | letE A₀ v₀ b₀ =>
    injection h with hA hv hb
    exact .mk A₀ v₀ b₀ rfl hA hv hb
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

inductive LetHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A value body T : Expr Nat) : Type
  | node (u : Level) (B : Expr Nat) (w : Level)
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
      (hb : TyP E n (.letBinding A value :: Γ) body B)
      (hT : TyP E n Γ (instantiate0 value B) (.sort w))
      (hTy : T = instantiate0 value B)
  | conv (Ty₀ C : Expr Nat) (u : Level)
      (inner : TyP E n Γ (.letE A value body) Ty₀)
      (hc : CvP E n Γ Ty₀ C (.sort u)) (hT : T = C)
  | wk (Γ₀ : LCtx) (Ty₀ A₀ v₀ b₀ : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.letE A₀ v₀ b₀) Ty₀) (hΓ : Γ = insertAt d c Γ₀)
      (hA : lift c 1 A₀ = A) (hv : lift c 1 v₀ = value)
      (hb : lift (c + 1) 1 b₀ = body) (hT : T = lift c 1 Ty₀)
  | esub_let (Γ₀ : LCtx) (Ty₀ t v A₀ v₀ b₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.letE A₀ v₀ b₀) Ty₀)
      (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hA : instantiate j (lift 0 j v) A₀ = A)
      (hval : instantiate j (lift 0 j v) v₀ = value)
      (hb : instantiate (j + 1) (lift 0 1 (lift 0 j v)) b₀ = body)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | lsub_let (Γ₀ : LCtx) (Ty₀ t v A₀ v₀ b₀ : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.letE A₀ v₀ b₀) Ty₀)
      (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀)
      (hA : instantiate j (lift 0 j v) A₀ = A)
      (hval : instantiate j (lift 0 j v) v₀ = value)
      (hb : instantiate (j + 1) (lift 0 1 (lift 0 j v)) b₀ = body)
      (hT : T = instantiate j (lift 0 j v) Ty₀)
  | esub_var (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.letE A value body) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .letE A value body)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.letE A value body) Ty₀)
  | lsub_var (Γ₀ : LCtx) (Ty₀ t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (.letE A value body) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlift : lift 0 j v = .letE A value body)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (.letE A value body) Ty₀)
  | linst (src : Nat) (Γ₀ : LCtx) (Ty₀ A₀ v₀ b₀ : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = src)
      (inner : TyP E src Γ₀ (.letE A₀ v₀ b₀) Ty₀)
      (hA : instantiateLevels ls A₀ = A) (hv : instantiateLevels ls v₀ = value)
      (hb : instantiateLevels ls b₀ = body)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls Ty₀)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.letE A value body) T)
      (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (Dom Dom' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption Dom :: Γtail) (.letE A value body) T)
      (hDom : CvP E n Γtail Dom Dom' (.sort u)) (hΓ : Γ = .assumption Dom' :: Γtail)

def letHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body T : Expr Nat}
    (D : TyP E n Γ (.letE A value body) T) : LetHead E n Γ A value body T := by
  generalize he : Expr.letE A value body = e at D
  cases D
  case letE A' u value' B body' w hA hv hb hT =>
    cases he
    exact .node u B w hA hv hb hT rfl
  case conv Ty₀ u inner hc =>
    cases he
    exact .conv Ty₀ T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case sort => cases he
  case const => cases he
  case pi => cases he
  case lam => cases he
  case app => cases he
  case lit => cases he
  case wk Γ₀ e₀ Ty₀ d c inner =>
    cases lift_eq_let he.symm with
    | mk A₀ v₀ b₀ hs hA hv hb =>
      cases hs
      exact .wk Γ₀ Ty₀ A₀ v₀ b₀ d c inner rfl hA hv hb rfl
  case esub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_let he.symm with
    | under A₀ v₀ b₀ hs hA hval hb =>
      cases hs
      exact .esub_let Γ₀ Ty₀ t v A₀ v₀ b₀ j u inner hget hv hvT rfl hA hval hb rfl
    | here hs hr =>
      cases hs
      exact .esub_var Γ₀ Ty₀ t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e Ty₀) hr)
  case lsub Γ₀ e₀ Ty₀ t v j u hget inner hv hvT =>
    cases instantiate_eq_let he.symm with
    | under A₀ v₀ b₀ hs hA hval hb =>
      cases hs
      exact .lsub_let Γ₀ Ty₀ t v A₀ v₀ b₀ j u inner hget hv hvT rfl hA hval hb rfl
    | here hs hr =>
      cases hs
      exact .lsub_var Γ₀ Ty₀ t v j u inner hget (hr ▸ hv) hvT hr rfl
        (congrArg (fun e => instantiate j e Ty₀) hr)
  case linst src Γ₀ e₀ Ty₀ ls hlen inner hls =>
    cases instantiateLevels_eq_let he.symm with
    | mk A₀ v₀ b₀ hs hA hv hb =>
      cases hs
      exact .linst src Γ₀ Ty₀ A₀ v₀ b₀ ls hls hlen inner hA hv hb rfl rfl
  case cctx Γtail Dom Dom' u hDom inner =>
    cases he
    exact .cctx Γtail Dom Dom' u inner hDom rfl

/-! ## §6 literal

A literal is lift-invariant, like a constant with no level vector. `esub_var`
rewrites the replacement itself to `.lit t`. -/

theorem lift_eq_lit {c k t : Nat} {e : Expr Nat} (h : lift c k e = .lit t) : e = .lit t := by
  cases e with
  | lit _ =>
    cases h
    rfl
  | bvar i =>
    unfold lift at h
    split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h

inductive InstLit (j : Nat) (r e : Expr Nat) (t : Nat) : Type where
  | under (he : e = .lit t) : InstLit j r e t
  | here (he : e = .bvar j) (hr : r = .lit t) : InstLit j r e t

def instantiate_eq_lit {j : Nat} {r e : Expr Nat} {t : Nat}
    (h : instantiate j r e = .lit t) : InstLit j r e t := by
  cases e with
  | lit _ =>
    cases h
    exact .under rfl
  | bvar i =>
    unfold instantiate at h
    split at h
    · next hi =>
      cases hi
      exact .here rfl h
    · split at h <;> exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h

theorem instantiateLevels_eq_lit {ls : List Level} {e : Expr Nat} {t : Nat}
    (h : instantiateLevels ls e = .lit t) : e = .lit t := by
  cases e with
  | lit _ =>
    cases h
    rfl
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h

inductive LitHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) (T : Expr Nat) : Type
  | node (hexp : TyP E n Γ (natExpand t) T)
  | conv (Ty₀ B : Expr Nat) (u : Level) (inner : TyP E n Γ (.lit t) Ty₀)
      (hc : CvP E n Γ Ty₀ B (.sort u)) (hT : T = B)
  | wk (Γ₀ : LCtx) (Ty₀ : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.lit t) Ty₀) (hΓ : Γ = insertAt d c Γ₀)
      (hT : T = lift c 1 Ty₀)
  | esub_lit (Γ₀ : LCtx) (Ty₀ tv repl : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.lit t) Ty₀) (hget : Γ₀[j]? = some (.assumption tv))
      (hv : TyP E n Γ (lift 0 j repl) (lift 0 j tv))
      (hvT : TyP E n Γ (lift 0 j tv) (.sort u))
      (hΓ : Γ = substRemove repl j Γ₀)
      (hT : T = instantiate j (lift 0 j repl) Ty₀)
  | lsub_lit (Γ₀ : LCtx) (Ty₀ tv repl : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.lit t) Ty₀) (hget : Γ₀[j]? = some (.letBinding tv repl))
      (hv : TyP E n Γ (lift 0 j repl) (lift 0 j tv))
      (hvT : TyP E n Γ (lift 0 j tv) (.sort u))
      (hΓ : Γ = substRemove repl j Γ₀)
      (hT : T = instantiate j (lift 0 j repl) Ty₀)
  | esub_var (Γ₀ : LCtx) (Ty₀ tv : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.assumption tv))
      (hv : TyP E n Γ (.lit t) (lift 0 j tv))
      (hvT : TyP E n Γ (lift 0 j tv) (.sort u))
      (hΓ : Γ = substRemove (.lit t) j Γ₀)
      (hT : T = instantiate j (.lit t) Ty₀)
  | lsub_var (Γ₀ : LCtx) (Ty₀ tv : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) Ty₀) (hget : Γ₀[j]? = some (.letBinding tv (.lit t)))
      (hv : TyP E n Γ (.lit t) (lift 0 j tv))
      (hvT : TyP E n Γ (lift 0 j tv) (.sort u))
      (hΓ : Γ = substRemove (.lit t) j Γ₀)
      (hT : T = instantiate j (.lit t) Ty₀)
  | linst (src : Nat) (Γ₀ : LCtx) (Ty₀ : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = src)
      (inner : TyP E src Γ₀ (.lit t) Ty₀)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls Ty₀)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.lit t) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (Dom Dom' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption Dom :: Γtail) (.lit t) T)
      (hDom : CvP E n Γtail Dom Dom' (.sort u)) (hΓ : Γ = .assumption Dom' :: Γtail)

def litHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (D : TyP E n Γ (.lit t) T) : LitHead E n Γ t T := by
  generalize he : Expr.lit t = e at D
  cases D
  case lit t' hexp =>
    cases he
    exact .node hexp
  case conv Ty₀ u inner hc =>
    cases he
    exact .conv Ty₀ T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case sort => cases he
  case const => cases he
  case pi => cases he
  case lam => cases he
  case app => cases he
  case letE => cases he
  case wk Γ₀ e₀ Ty₀ d c inner =>
    have hs : e₀ = .lit t := lift_eq_lit he.symm
    cases hs
    exact .wk Γ₀ Ty₀ d c inner rfl rfl
  case esub Γ₀ e₀ Ty₀ tv repl j u hget inner hv hvT =>
    cases instantiate_eq_lit he.symm with
    | under hs =>
      cases hs
      exact .esub_lit Γ₀ Ty₀ tv repl j u inner hget hv hvT rfl rfl
    | here hs hr =>
      have hlit : repl = .lit t := lift_eq_lit hr
      cases hs
      cases hlit
      exact .esub_var Γ₀ Ty₀ tv j u inner hget hv hvT rfl rfl
  case lsub Γ₀ e₀ Ty₀ tv repl j u hget inner hv hvT =>
    cases instantiate_eq_lit he.symm with
    | under hs =>
      cases hs
      exact .lsub_lit Γ₀ Ty₀ tv repl j u inner hget hv hvT rfl rfl
    | here hs hr =>
      have hlit : repl = .lit t := lift_eq_lit hr
      cases hs
      cases hlit
      exact .lsub_var Γ₀ Ty₀ tv j u inner hget hv hvT rfl rfl
  case linst src Γ₀ e₀ Ty₀ ls hlen inner hls =>
    have hs : e₀ = .lit t := instantiateLevels_eq_lit he.symm
    cases hs
    exact .linst src Γ₀ Ty₀ ls hls hlen inner rfl rfl
  case cctx Γtail Dom Dom' u hDom inner =>
    cases he
    exact .cctx Γtail Dom Dom' u inner hDom rfl

end Rcic.Syn

#print axioms Rcic.Syn.lift_eq_app
#print axioms Rcic.Syn.instantiate_eq_app
#print axioms Rcic.Syn.instantiateLevels_eq_app
#print axioms Rcic.Syn.appHead
#print axioms Rcic.Syn.lift_eq_lam
#print axioms Rcic.Syn.instantiate_eq_lam
#print axioms Rcic.Syn.instantiateLevels_eq_lam
#print axioms Rcic.Syn.lamHead
#print axioms Rcic.Syn.lift_eq_pi
#print axioms Rcic.Syn.instantiate_eq_pi
#print axioms Rcic.Syn.instantiateLevels_eq_pi
#print axioms Rcic.Syn.piHead
#print axioms Rcic.Syn.instantiate_eq_const
#print axioms Rcic.Syn.instantiateLevels_eq_const
#print axioms Rcic.Syn.constHead
#print axioms Rcic.Syn.lift_eq_let
#print axioms Rcic.Syn.instantiate_eq_let
#print axioms Rcic.Syn.instantiateLevels_eq_let
#print axioms Rcic.Syn.letHead
#print axioms Rcic.Syn.lift_eq_lit
#print axioms Rcic.Syn.instantiate_eq_lit
#print axioms Rcic.Syn.instantiateLevels_eq_lit
#print axioms Rcic.Syn.litHead
