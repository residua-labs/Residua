import rcic.RcicConvPlus

/-!
# Syntactic sortRow, build step 3g — the head of a typing of a sort

`research/rcic/semantic/S3_ES_ARMS.md` §9. A derivation of `.sort l` is not, in
general, a `sort` node: `conv` follows the term, and `wk` / `esub` / `linst` /
`ewk` / `cctx` rebuild it. `esub` at the substituted variable can turn a `bvar`
into the replacement, so a sort can be born there. Every other constructor's
term is a different head, and `lift` / `instantiate` / `instantiateLevels` send
a sort only to a sort.

`SortHead` is that case split. It does not say the erasure is a sort. An `esub`
on the `drop` path of a `bvar` whose replacement is a sort erases to whatever
the `bvar` erases to, which can be `★`. That equation is `SortHead.esub_var`,
and the claim "it erases to `sort (σ l)`" is an induction hypothesis on `hv`,
not a structural lemma (`S3` §8). `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 a sort is born only at a sort, or at the substituted variable -/

theorem lift_eq_sort {c k : Nat} {e : Expr Nat} {l : Level} (h : lift c k e = .sort l) :
    e = .sort l := by
  cases e with
  | bvar i =>
    simp only [lift] at h
    split at h <;> cases h
  | sort _ =>
    simp only [lift] at h
    cases h
    rfl
  | const _ _ =>
    simp only [lift] at h
    cases h
  | app _ _ =>
    simp only [lift] at h
    cases h
  | lam _ _ =>
    simp only [lift] at h
    cases h
  | pi _ _ =>
    simp only [lift] at h
    cases h
  | letE _ _ _ =>
    simp only [lift] at h
    cases h
  | lit _ =>
    simp only [lift] at h
    cases h

/-- `instantiate j r e = sort l` is either `e` already a sort, or the hit variable
    whose replacement is that sort. A `Type`, not an `Or`: the sort-head view
    eliminates it into `Type`. -/
inductive InstSort (j : Nat) (r e : Expr Nat) (l : Level) : Type where
  | under (h : e = .sort l) : InstSort j r e l
  | here (he : e = .bvar j) (hr : r = .sort l) : InstSort j r e l

def instantiate_eq_sort {j : Nat} {r e : Expr Nat} {l : Level} (h : instantiate j r e = .sort l) :
    InstSort j r e l := by
  cases e with
  | bvar i =>
    simp only [instantiate] at h
    split at h
    · next hi => exact .here (congrArg Expr.bvar hi) h
    · split at h <;> cases h
  | sort _ =>
    simp only [instantiate] at h
    cases h
    exact .under rfl
  | const _ _ =>
    simp only [instantiate] at h
    cases h
  | app _ _ =>
    simp only [instantiate] at h
    cases h
  | lam _ _ =>
    simp only [instantiate] at h
    cases h
  | pi _ _ =>
    simp only [instantiate] at h
    cases h
  | letE _ _ _ =>
    simp only [instantiate] at h
    cases h
  | lit _ =>
    simp only [instantiate] at h
    cases h

/-- `instantiateLevels ls e = sort l` names the level `e` carried. A `Type`, so the
    view can eliminate it. -/
inductive LinstSort (ls : List Level) (e : Expr Nat) (l : Level) : Type where
  | mk (l₀ : Level) (he : e = .sort l₀) (hl : instLevel ls l₀ = l) : LinstSort ls e l

def instantiateLevels_eq_sort {ls : List Level} {e : Expr Nat} {l : Level}
    (h : instantiateLevels ls e = .sort l) : LinstSort ls e l := by
  cases e with
  | bvar _ =>
    simp only [instantiateLevels] at h
    cases h
  | sort l₀ =>
    simp only [instantiateLevels] at h
    cases h
    exact .mk l₀ rfl rfl
  | const _ _ =>
    simp only [instantiateLevels] at h
    cases h
  | app _ _ =>
    simp only [instantiateLevels] at h
    cases h
  | lam _ _ =>
    simp only [instantiateLevels] at h
    cases h
  | pi _ _ =>
    simp only [instantiateLevels] at h
    cases h
  | letE _ _ _ =>
    simp only [instantiateLevels] at h
    cases h
  | lit _ =>
    simp only [instantiateLevels] at h
    cases h

/-! ## §2 the head -/

/-- How a derivation of `.sort l` is built. The subderivations are the ones the
    mutual induction recurses into. -/
inductive SortHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) (T : Expr Nat) : Type
  | node (k : Level) (h : eqN k (.succ l)) (hk : T = .sort k)
  | conv (A B : Expr Nat) (u : Level) (inner : TyP E n Γ (.sort l) A)
      (hc : CvP E n Γ A B (.sort u)) (hT : T = B)
  | wk (Γ₀ : LCtx) (A : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.sort l) A) (hΓ : Γ = insertAt d c Γ₀) (hT : T = lift c 1 A)
  | esub_sort (Γ₀ : LCtx) (A t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.sort l) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀) (hT : T = instantiate j (lift 0 j v) A)
  | lsub_sort (Γ₀ : LCtx) (A t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.sort l) A) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove v j Γ₀) (hT : T = instantiate j (lift 0 j v) A)
  | esub_var (Γ₀ : LCtx) (A t : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.sort l) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove (.sort l) j Γ₀)
      (hT : T = instantiate j (.sort l) A)
  | lsub_var (Γ₀ : LCtx) (A t : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) A) (hget : Γ₀[j]? = some (.letBinding t (.sort l)))
      (hv : TyP E n Γ (.sort l) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hΓ : Γ = substRemove (.sort l) j Γ₀)
      (hT : T = instantiate j (.sort l) A)
  | linst (a : Nat) (Γ₀ : LCtx) (A : Expr Nat) (ls : List Level) (l₀ : Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a)
      (inner : TyP E a Γ₀ (.sort l₀) A) (hl : instLevel ls l₀ = l)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls A)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.sort l) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (A A' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption A :: Γtail) (.sort l) T)
      (hA : CvP E n Γtail A A' (.sort u)) (hΓ : Γ = .assumption A' :: Γtail)

/-- Every typing of a sort has one of these heads. `SortHead` lives in `Type`, so
    this is a definition. The term is generalized first: matching `TyP` directly at
    `.sort l` cannot solve `sort l = lift c 1 e`. -/
def sortHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} {T : Expr Nat}
    (D : TyP E n Γ (.sort l) T) : SortHead E n Γ l T := by
  generalize he : Expr.sort l = e at D
  cases D
  case sort l' k h =>
    cases he
    exact .node k h rfl
  case conv A u inner hc =>
    cases he
    exact .conv A T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case bvar => cases he
  case const => cases he
  case pi => cases he
  case lam => cases he
  case app => cases he
  case letE => cases he
  case lit => cases he
  case wk Γ₀ e₀ A d c inner =>
    have hs : e₀ = .sort l := lift_eq_sort he.symm
    cases hs
    exact .wk Γ₀ A d c inner rfl rfl
  case esub Γ₀ e₀ A t v j u hget inner hv hvT =>
    cases instantiate_eq_sort he.symm with
    | under hs =>
      cases hs
      exact .esub_sort Γ₀ A t v j u inner hget hv hvT rfl rfl
    | here hs hr =>
      have hvsort : v = .sort l := lift_eq_sort hr
      cases hs
      cases hvsort
      cases hr
      exact .esub_var Γ₀ A t j u inner hget hv hvT rfl rfl
  case lsub Γ₀ e₀ A t v j u hget inner hv hvT =>
    cases instantiate_eq_sort he.symm with
    | under hs =>
      cases hs
      exact .lsub_sort Γ₀ A t v j u inner hget hv hvT rfl rfl
    | here hs hr =>
      have hvsort : v = .sort l := lift_eq_sort hr
      cases hs
      cases hvsort
      cases hr
      exact .lsub_var Γ₀ A t j u inner hget hv hvT rfl rfl
  case linst a Γ₀ e₀ A ls hlen inner hls =>
    cases instantiateLevels_eq_sort he.symm with
    | mk l₀ hs hl =>
      cases hs
      exact .linst a Γ₀ A ls l₀ hls hlen inner hl rfl rfl
  case cctx Γtail A A' u hA inner =>
    cases he
    exact .cctx Γtail A A' u inner hA rfl

end Rcic.Syn

#print axioms Rcic.Syn.lift_eq_sort
#print axioms Rcic.Syn.instantiate_eq_sort
#print axioms Rcic.Syn.instantiateLevels_eq_sort
#print axioms Rcic.Syn.sortHead
