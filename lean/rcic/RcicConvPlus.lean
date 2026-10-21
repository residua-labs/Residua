import rcic.RcicSynOrder
import rcic.RcicTypedEnv
import rcic.RcicCtxMorph
import rcic.RcicSubst
import rcic.RcicTypedLevels

/-!
# Syntactic sortRow, build step 1c — O6, the enriched judgment, and O1's weights

`research/rcic/semantic/S1_ORDER_ENRICHED_LEVELS.md` §4–§5. The mutual induction of the syntactic
route (S0 §4) runs over **enriched** derivations `TyP` / `CvP`:
* every conversion rule carries typings of both endpoints (`dl`, `dr`);
* every typing rule whose type is not a sort-by-construction carries a typing of its type at a sort:
  `bvar`'s `hA`, `const`'s `hT`, `lam`'s `hB`, `app`'s and `letE`'s `hT`. `TyP.reg` reads it off for
  every node.

The landed transports (`hasTyTWeaken`, `hasTyT_substS`, `hasTyT_instLevels`) MATERIALIZE their
result. The materialized substitution is not bounded by its parts, because the argument is
duplicated at every occurrence. So the transports are CONSTRUCTORS here: `wk` (at `insertAt`),
`esub` (at `substRemove`, plus the replacement's type typing `hvT`), `linst` (at `instLvlsCtx`),
`ewk` (environment extension). Step 3 adds the two Q7 transports (`S1` §4.4 (ii), cc's review of
#6784): `cctx` (context conversion of one binder, on typings and on conversions) and `fsub`
(substitution of convertible terms). `cctx` flattens like `wk`; `fsub` is a rule node, because its
right endpoint is typed at `S[a]` and is not the raw substitution `S[b]`. The induction views
transports lazily (`S1` §4.3).

O1's measure (`S1` §3) is the Dershowitz–Manna order of `RcicSynOrder` on the multiset of atom
weights.
* `TyP.wt A`: structural size. A `const` node also pays its admission weight `A r`, and
  `EnvWfP.admW` computes `A` from the enriched environment.
* `TyP.atoms`: transports are flattened into their parts; any other node is one atom.

This module states the objects and the weight facts every call-table row uses: endpoints,
regularity and children are lighter than the node. The translation of plain derivations into
enriched ones (O6 proper) is the next carrier. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- members of `E₀` are members of `E`, with the same checked member. -/
def EnvExt (E₀ E : ResolvedEnv) : Prop := ∀ r m, E₀.members r = some m → E.members r = some m

theorem envExt_refl (E : ResolvedEnv) : EnvExt E E := fun _ _ h => h

theorem envExt_trans {E₀ E₁ E₂ : ResolvedEnv} (h1 : EnvExt E₀ E₁) (h2 : EnvExt E₁ E₂) :
    EnvExt E₀ E₂ := fun r m h => h2 r m (h1 r m h)

/-- a fresh extension extends. -/
theorem envExt_extendEnv {E : ResolvedEnv} {r : Nat} (m : CheckedMember) (hfresh : E.members r = none) :
    EnvExt E (extendEnv E r m) := by
  intro r' m' h
  show (if r' = r then some m else E.members r') = some m'
  cases Nat.decEq r' r with
  | isTrue hr => subst hr; rw [hfresh] at h; exact Option.noConfusion h
  | isFalse hr => rw [if_neg hr]; exact h

/-! ## §1 the enriched judgment -/

mutual

/-- enriched typing: `HasTyT` with regularity fields, plus four transport constructors. -/
inductive TyP : ResolvedEnv → Nat → LCtx → Expr Nat → Expr Nat → Type
  /-- `sort l : sort k` when `k =ₙ succ l`. `HasTyT.sort` is the case `k := succ l`. The `eqN` slack
      is what lets `sorts` carry its right endpoint: `sort l₂ : sort (succ l₁)` is one node. Without
      it, that endpoint needs a conversion `sort (succ l₂) ≡ sort (succ l₁)`, whose own right
      endpoint needs the next universe up, with no end (`S1` §4.1). -/
  | sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l k : Level) (h : eqN k (.succ l)) :
      TyP E n Γ (.sort l) (.sort k)
  | bvar (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) (A : Expr Nat) (u : Level)
      (h : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u)) :
      TyP E n Γ (.bvar i) A
  /-- `const r ls : instantiateLevels ls₀ T` when `ls =ₙ ls₀`, the `consts` analogue of `sort`'s
      slack. `HasTyT.const` is the case `ls₀ := ls`. It lets `consts` carry its right endpoint
      `const r ls'` at the left type in one node (`S1` §4.1). -/
  | const (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls ls₀ : List Level)
      (m : CheckedMember) (u : Level) (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
      (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)) :
      TyP E n Γ (.const r ls) (instantiateLevels ls₀ m.mtype)
  | pi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) (B : Expr Nat) (v : Level)
      (hA : TyP E n Γ A (.sort u)) (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
      TyP E n Γ (.pi A B) (.sort (.imax u v))
  | lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) (body B : Expr Nat)
      (v : Level) (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
      (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
      TyP E n Γ (.lam A body) (.pi A B)
  | app (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f a A B : Expr Nat) (w : Level)
      (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
      (hT : TyP E n Γ (instantiate0 a B) (.sort w)) :
      TyP E n Γ (.app f a) (instantiate0 a B)
  | letE (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level)
      (value B body : Expr Nat) (w : Level)
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
      (hb : TyP E n (.letBinding A value :: Γ) body B)
      (hT : TyP E n Γ (instantiate0 value B) (.sort w)) :
      TyP E n Γ (.letE A value body) (instantiate0 value B)
  | lit (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) (T : Expr Nat)
      (hexp : TyP E n Γ (natExpand t) T) : TyP E n Γ (.lit t) T
  | conv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A B : Expr Nat) (u : Level)
      (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) : TyP E n Γ e B
  /-- transport: weakening at `insertAt` (`hasTyTWeaken`'s shape). -/
  | wk (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) (d : LocalDecl) (c : Nat)
      (D : TyP E n Γ e A) : TyP E n (insertAt d c Γ) (lift c 1 e) (lift c 1 A)
  /-- transport: explicit substitution at `substRemove` (`hasTyT_substS`'s shape), with the
      replacement's type typed at a sort (`hvT`). -/
  | esub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A t v : Expr Nat) (j : Nat) (u : Level)
      (D : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  /-- transport: substitution of a let-binding. The removed entry is `.letBinding t v`.
      Erasure inlines `hv.eps`, or drops it when that erasure is `★`, matching `letE`. -/
  | lsub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A t v : Expr Nat) (j : Nat) (u : Level)
      (D : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  /-- transport: level instantiation at `instLvlsCtx` (`hasTyT_instLevels`'s shape). -/
  | linst (E : ResolvedEnv) (a n : Nat) (Γ : LCtx) (e A : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a) (D : TyP E a Γ e A) :
      TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls e) (instantiateLevels ls A)
  /-- transport: environment extension. -/
  | ewk (E₀ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) (hext : EnvExt E₀ E)
      (D : TyP E₀ n Γ e A) : TyP E n Γ e A
  /-- transport: context conversion of the innermost binder (`S1` §4.4). The term and its type
      expression are unchanged. Both domains are converted at one sort `u`, so the binder's
      proof-bit agrees. -/
  | cctx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T A A' : Expr Nat) (u : Level)
      (D : TyP E n (.assumption A :: Γ) e T) (hA : CvP E n Γ A A' (.sort u)) :
      TyP E n (.assumption A' :: Γ) e T

/-- enriched conversion: the 18 `ConvT` rules, each carrying typings of both endpoints (`dl`, `dr`),
    plus the transports (`wk`, `esub`, `linst`, `ewk`, `cctx`) and the functionality rule `fsub`. -/
inductive CvP : ResolvedEnv → Nat → LCtx → Expr Nat → Expr Nat → Expr Nat → Type
  | refl (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a A : Expr Nat) (h : TyP E n Γ a A)
      (dl dr : TyP E n Γ a A) : CvP E n Γ a a A
  | symm (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b A : Expr Nat) (h : CvP E n Γ a b A)
      (dl : TyP E n Γ b A) (dr : TyP E n Γ a A) : CvP E n Γ b a A
  | trans (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b c A : Expr Nat) (h1 : CvP E n Γ a b A)
      (h2 : CvP E n Γ b c A) (dl : TyP E n Γ a A) (dr : TyP E n Γ c A) : CvP E n Γ a c A
  | beta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A body arg B : Expr Nat) (u : Level)
      (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
      (harg : TyP E n Γ arg A)
      (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
      (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)) :
      CvP E n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B)
  | zeta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A value body B : Expr Nat) (u : Level)
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
      (hb : TyP E n (.letBinding A value :: Γ) body B)
      (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
      (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)) :
      CvP E n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B)
  | zetaLocal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) (A v : Expr Nat)
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A) (hv : TyP E n Γ v A)
      (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A) : CvP E n Γ (.bvar i) v A
  | delta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
      (b : Expr Nat) (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
      (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
      (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
      CvP E n Γ (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype)
  | iota (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (lhs rhs T : Expr Nat) (h : DerivedIota E lhs rhs)
      (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
      (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T) : CvP E n Γ lhs rhs T
  | lit (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) (exp T : Expr Nat)
      (h : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
      (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T) : CvP E n Γ (.lit t) exp T
  | app (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f g a b A B : Expr Nat)
      (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
      (dl : TyP E n Γ (.app f a) (instantiate0 a B)) (dr : TyP E n Γ (.app g b) (instantiate0 a B)) :
      CvP E n Γ (.app f a) (.app g b) (instantiate0 a B)
  | lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' b b' B : Expr Nat) (u : Level)
      (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
      (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B)) :
      CvP E n Γ (.lam A b) (.lam A' b') (.pi A B)
  | pi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' B B' : Expr Nat) (u v : Level)
      (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
      (dl : TyP E n Γ (.pi A B) (.sort (.imax u v))) (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))) :
      CvP E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))
  | letE (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' v v' b b' B : Expr Nat) (u : Level)
      (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
      (hb : CvP E n (.letBinding A v :: Γ) b b' B)
      (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
      (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) :
      CvP E n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B)
  | sorts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂)
      (dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁))) (dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁))) :
      CvP E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))
  | consts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls ls' : List Level)
      (m : CheckedMember) (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls')
      (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
      (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)) :
      CvP E n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype)
  | eta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f A B : Expr Nat) (h : TyP E n Γ f (.pi A B))
      (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) (dr : TyP E n Γ f (.pi A B)) :
      CvP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B)
  | irr (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (P p q : Expr Nat) (hP : TyP E n Γ P (.sort .zero))
      (hp : TyP E n Γ p P) (hq : TyP E n Γ q P) (dl : TyP E n Γ p P) (dr : TyP E n Γ q P) :
      CvP E n Γ p q P
  | tyConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b A A' : Expr Nat) (u : Level)
      (h : CvP E n Γ a b A) (hA : CvP E n Γ A A' (.sort u))
      (dl : TyP E n Γ a A') (dr : TyP E n Γ b A') : CvP E n Γ a b A'
  | wk (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T : Expr Nat) (d : LocalDecl) (c : Nat)
      (h : CvP E n Γ a b T) : CvP E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | esub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T t v : Expr Nat) (j : Nat) (u : Level)
      (h : CvP E n Γ a b T) (hget : Γ[j]? = some (.assumption t))
      (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      CvP E n (substRemove v j Γ) (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
        (instantiate j (lift 0 j v) T)
  | linst (E : ResolvedEnv) (a' n : Nat) (Γ : LCtx) (a b T : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a') (h : CvP E a' Γ a b T) :
      CvP E n (instLvlsCtx ls Γ) (instantiateLevels ls a) (instantiateLevels ls b)
        (instantiateLevels ls T)
  | ewk (E₀ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T : Expr Nat) (hext : EnvExt E₀ E)
      (h : CvP E₀ n Γ a b T) : CvP E n Γ a b T
  /-- transport: context conversion of the innermost binder, on conversions. -/
  | cctx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T A A' : Expr Nat) (u : Level)
      (h : CvP E n (.assumption A :: Γ) a b T) (hA : CvP E n Γ A A' (.sort u)) :
      CvP E n (.assumption A' :: Γ) a b T
  /-- functionality: `a ≡ b : A` sends `B` under `A :: Γ` to `B[a] ≡ B[b]`, ascribed at `S[a]`
      (the right side's natural type is `S[b]`, so `dr` is a field, not a raw `esub`). -/
  | fsub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B S a b : Expr Nat) (u : Level)
      (hB : TyP E n (.assumption A :: Γ) B S) (hA : TyP E n Γ A (.sort u))
      (hab : CvP E n Γ a b A)
      (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S))
      (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S)) :
      CvP E n Γ (instantiate0 a B) (instantiate0 b B) (instantiate0 a S)

end

/-- an enriched context: every entry typed at a sort (and a let value at its type). -/
inductive CtxP : ResolvedEnv → Nat → LCtx → Type
  | nil (E : ResolvedEnv) (n : Nat) : CtxP E n []
  | assumption (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level)
      (hΓ : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) : CtxP E n (.assumption A :: Γ)
  | letBinding (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) (v : Expr Nat)
      (hΓ : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
      CtxP E n (.letBinding A v :: Γ)

/-! ## §2 weights (O1's base) -/

mutual

/-- structural size. A `const` node also pays its admission weight `A r`. -/
def TyP.wt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Nat
  | _, _, _, _, _, .sort .. => 1
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ hA => 1 + hA.wt Aw
  | _, _, _, _, _, .const _ _ _ r _ _ _ _ _ _ _ _ hT => 1 + hT.wt Aw + Aw r
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => 1 + hA.wt Aw + hB.wt Aw
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ hA hb hB => 1 + hA.wt Aw + hb.wt Aw + hB.wt Aw
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT => 1 + hf.wt Aw + ha.wt Aw + hT.wt Aw
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT =>
      1 + hA.wt Aw + hv.wt Aw + hb.wt Aw + hT.wt Aw
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => 1 + hexp.wt Aw
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h hc => 1 + h.wt Aw + hc.wt Aw
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => 1 + D.wt Aw
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT => 1 + D.wt Aw + hv.wt Aw + hvT.wt Aw
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT => 1 + D.wt Aw + hv.wt Aw + hvT.wt Aw
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => 1 + D.wt Aw
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => 1 + D.wt Aw
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => 1 + D.wt Aw + hA.wt Aw

def CvP.wt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T → Nat
  | _, _, _, _, _, _, .refl _ _ _ _ _ h dl dr => 1 + h.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ h dl dr => 1 + h.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ h1 h2 dl dr =>
      1 + h1.wt Aw + h2.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ hA hb harg dl dr =>
      1 + hA.wt Aw + hb.wt Aw + harg.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      1 + hA.wt Aw + hv.wt Aw + hb.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ hv dl dr => 1 + hv.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ hb dl dr =>
      1 + hb.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ hl hr dl dr => 1 + hl.wt Aw + hr.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ hexp dl dr => 1 + hexp.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 dl dr =>
      1 + h1.wt Aw + h2.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hA hb dl dr =>
      1 + hA.wt Aw + hb.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ hA hB dl dr =>
      1 + hA.wt Aw + hB.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      1 + hA.wt Aw + hv.wt Aw + hb.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl dr => 1 + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl dr => 1 + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ h dl dr => 1 + h.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ hP hp hq dl dr =>
      1 + hP.wt Aw + hp.wt Aw + hq.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h hA dl dr =>
      1 + h.wt Aw + hA.wt Aw + dl.wt Aw + dr.wt Aw
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => 1 + h.wt Aw
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ hv hvT => 1 + h.wt Aw + hv.wt Aw + hvT.wt Aw
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => 1 + h.wt Aw
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => 1 + h.wt Aw
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA => 1 + h.wt Aw + hA.wt Aw
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ hB hA hab dl dr =>
      1 + hB.wt Aw + hA.wt Aw + hab.wt Aw + dl.wt Aw + dr.wt Aw

end

theorem TyP.wt_pos (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : 0 < D.wt Aw := by
  cases D <;> simp only [TyP.wt] <;> omega

theorem CvP.wt_pos (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) : 0 < h.wt Aw := by
  cases h <;> simp only [CvP.wt] <;> omega

/-! ## §3 endpoints and regularity, as functions; both are lighter than the node -/

/-- the left endpoint's typing: a field at a rule node, the transported endpoint at a transport. -/
def CvP.dl : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T → TyP E n Γ a T
  | _, _, _, _, _, _, .refl _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .wk E n Γ a _ T d c h => .wk E n Γ a T d c h.dl
  | _, _, _, _, _, _, .esub E n Γ a _ T t v j u h hget hv hvT => .esub E n Γ a T t v j u h.dl hget hv hvT
  | _, _, _, _, _, _, .linst E a' n Γ a _ T ls hls hlen h => .linst E a' n Γ a T ls hls hlen h.dl
  | _, _, _, _, _, _, .ewk E₀ E n Γ a _ T hext h => .ewk E₀ E n Γ a T hext h.dl
  | _, _, _, _, _, _, .cctx E n Γ a _ T A A' u h hA => .cctx E n Γ a T A A' u h.dl hA
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl

/-- the right endpoint's typing. -/
def CvP.dr : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T → TyP E n Γ b T
  | _, _, _, _, _, _, .refl _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .wk E n Γ _ b T d c h => .wk E n Γ b T d c h.dr
  | _, _, _, _, _, _, .esub E n Γ _ b T t v j u h hget hv hvT => .esub E n Γ b T t v j u h.dr hget hv hvT
  | _, _, _, _, _, _, .linst E a' n Γ _ b T ls hls hlen h => .linst E a' n Γ b T ls hls hlen h.dr
  | _, _, _, _, _, _, .ewk E₀ E n Γ _ b T hext h => .ewk E₀ E n Γ b T hext h.dr
  | _, _, _, _, _, _, .cctx E n Γ _ b T A A' u h hA => .cctx E n Γ b T A A' u h.dr hA
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr

theorem CvP.wt_dl_lt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (h : CvP E n Γ a b T) → h.dl.wt Aw < h.wt Aw
  | _, _, _, _, _, _, .refl .. | _, _, _, _, _, _, .symm .. | _, _, _, _, _, _, .trans ..
  | _, _, _, _, _, _, .beta .. | _, _, _, _, _, _, .zeta .. | _, _, _, _, _, _, .zetaLocal ..
  | _, _, _, _, _, _, .delta .. | _, _, _, _, _, _, .iota .. | _, _, _, _, _, _, .lit ..
  | _, _, _, _, _, _, .app .. | _, _, _, _, _, _, .lam .. | _, _, _, _, _, _, .pi ..
  | _, _, _, _, _, _, .letE .. | _, _, _, _, _, _, .sorts .. | _, _, _, _, _, _, .consts ..
  | _, _, _, _, _, _, .eta .. | _, _, _, _, _, _, .irr .. | _, _, _, _, _, _, .tyConv ..
  | _, _, _, _, _, _, .fsub .. => by
      simp only [CvP.dl, CvP.wt]; omega
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => by
      have := CvP.wt_dl_lt Aw h
      simp only [CvP.dl, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ _ _ => by
      have := CvP.wt_dl_lt Aw h
      simp only [CvP.dl, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => by
      have := CvP.wt_dl_lt Aw h
      simp only [CvP.dl, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => by
      have := CvP.wt_dl_lt Aw h
      simp only [CvP.dl, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h _ => by
      have := CvP.wt_dl_lt Aw h
      simp only [CvP.dl, CvP.wt, TyP.wt]; omega

theorem CvP.wt_dr_lt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (h : CvP E n Γ a b T) → h.dr.wt Aw < h.wt Aw
  | _, _, _, _, _, _, .refl .. | _, _, _, _, _, _, .symm .. | _, _, _, _, _, _, .trans ..
  | _, _, _, _, _, _, .beta .. | _, _, _, _, _, _, .zeta .. | _, _, _, _, _, _, .zetaLocal ..
  | _, _, _, _, _, _, .delta .. | _, _, _, _, _, _, .iota .. | _, _, _, _, _, _, .lit ..
  | _, _, _, _, _, _, .app .. | _, _, _, _, _, _, .lam .. | _, _, _, _, _, _, .pi ..
  | _, _, _, _, _, _, .letE .. | _, _, _, _, _, _, .sorts .. | _, _, _, _, _, _, .consts ..
  | _, _, _, _, _, _, .eta .. | _, _, _, _, _, _, .irr .. | _, _, _, _, _, _, .tyConv ..
  | _, _, _, _, _, _, .fsub .. => by
      simp only [CvP.dr, CvP.wt]; omega
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => by
      have := CvP.wt_dr_lt Aw h
      simp only [CvP.dr, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ _ _ => by
      have := CvP.wt_dr_lt Aw h
      simp only [CvP.dr, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => by
      have := CvP.wt_dr_lt Aw h
      simp only [CvP.dr, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => by
      have := CvP.wt_dr_lt Aw h
      simp only [CvP.dr, CvP.wt, TyP.wt]; omega
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h _ => by
      have := CvP.wt_dr_lt Aw h
      simp only [CvP.dr, CvP.wt, TyP.wt]; omega

/-- regularity: a typing of the node's type at a sort. -/
def TyP.reg : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → (u : Level) × TyP E n Γ T (.sort u)
  | _, _, _, _, _, .sort E n Γ _ k _ => ⟨.succ k, .sort E n Γ k (.succ k) (eqN_refl _)⟩
  | _, _, _, _, _, .bvar _ _ _ _ _ u _ hA => ⟨u, hA⟩
  | _, _, _, _, _, .const _ _ _ _ _ _ _ u _ _ _ _ hT => ⟨u, hT⟩
  | _, _, _, _, _, .pi E n Γ _ u _ v _ _ =>
      ⟨.succ (.imax u v), .sort E n Γ (.imax u v) (.succ (.imax u v)) (eqN_refl _)⟩
  | _, _, _, _, _, .lam E n Γ A u _ B v hA _ hB => ⟨.imax u v, .pi E n Γ A u B v hA hB⟩
  | _, _, _, _, _, .app _ _ _ _ _ _ _ w _ _ hT => ⟨w, hT⟩
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ w _ _ _ hT => ⟨w, hT⟩
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.reg
  | _, _, _, _, _, .conv _ _ _ _ _ _ u _ hc => ⟨u, hc.dr⟩
  | _, _, _, _, _, .wk E n Γ _ A d c D =>
      let R := D.reg
      ⟨R.1, .wk E n Γ A (.sort R.1) d c R.2⟩
  | _, _, _, _, _, .esub E n Γ _ A t v j u D hget hv hvT =>
      let R := D.reg
      ⟨R.1, .esub E n Γ A (.sort R.1) t v j u R.2 hget hv hvT⟩
  | _, _, _, _, _, .lsub E n Γ _ A t v j u D hget hv hvT =>
      let R := D.reg
      ⟨R.1, .lsub E n Γ A (.sort R.1) t v j u R.2 hget hv hvT⟩
  | _, _, _, _, _, .linst E a n Γ _ A ls hls hlen D =>
      let R := D.reg
      ⟨instLevel ls R.1, .linst E a n Γ A (.sort R.1) ls hls hlen R.2⟩
  | _, _, _, _, _, .ewk E₀ E n Γ _ A hext D =>
      let R := D.reg
      ⟨R.1, .ewk E₀ E n Γ A (.sort R.1) hext R.2⟩
  | _, _, _, _, _, .cctx E n Γ _ T A A' u D hA =>
      let R := D.reg
      ⟨R.1, .cctx E n Γ T (.sort R.1) A A' u R.2 hA⟩

/-- regularity is never heavier than the node. It is strictly lighter except at `sort` and `pi`,
    whose regularity is a single `sort` node; the induction needs no call there. -/
theorem TyP.wt_reg_le (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → (D : TyP E n Γ e T) → D.reg.2.wt Aw ≤ D.wt Aw
  | _, _, _, _, _, .sort .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .bvar .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .const .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .pi .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .lam .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .app .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .letE .. => by simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => by
      have := TyP.wt_reg_le Aw hexp
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ _ hc => by
      have := CvP.wt_dr_lt Aw hc
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => by
      have := TyP.wt_reg_le Aw D
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _ => by
      have := TyP.wt_reg_le Aw D
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _ => by
      have := TyP.wt_reg_le Aw D
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => by
      have := TyP.wt_reg_le Aw D
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => by
      have := TyP.wt_reg_le Aw D
      simp only [TyP.reg, TyP.wt]; omega
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => by
      have := TyP.wt_reg_le Aw D
      simp only [TyP.reg, TyP.wt]; omega

/-! ## §4 atoms: the multiset O1 measures -/

mutual

/-- the atom weights of a typing: transports flatten into their parts, and any other node is one atom. -/
def TyP.atoms (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → List Nat
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.atoms Aw
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT => D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT => D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.atoms Aw
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.atoms Aw
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => D.atoms Aw ++ hA.atoms Aw
  | _, _, _, _, _, D@(.sort ..) | _, _, _, _, _, D@(.bvar ..) | _, _, _, _, _, D@(.const ..)
  | _, _, _, _, _, D@(.pi ..) | _, _, _, _, _, D@(.lam ..) | _, _, _, _, _, D@(.app ..)
  | _, _, _, _, _, D@(.letE ..) | _, _, _, _, _, D@(.lit ..) | _, _, _, _, _, D@(.conv ..) =>
      [D.wt Aw]

def CvP.atoms (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T → List Nat
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => h.atoms Aw
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ hv hvT => h.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => h.atoms Aw
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => h.atoms Aw
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA => h.atoms Aw ++ hA.atoms Aw
  | _, _, _, _, _, _, h@(.fsub ..) => [h.wt Aw]
  | _, _, _, _, _, _, h@(.refl ..) | _, _, _, _, _, _, h@(.symm ..) | _, _, _, _, _, _, h@(.trans ..)
  | _, _, _, _, _, _, h@(.beta ..) | _, _, _, _, _, _, h@(.zeta ..)
  | _, _, _, _, _, _, h@(.zetaLocal ..) | _, _, _, _, _, _, h@(.delta ..)
  | _, _, _, _, _, _, h@(.iota ..) | _, _, _, _, _, _, h@(.lit ..) | _, _, _, _, _, _, h@(.app ..)
  | _, _, _, _, _, _, h@(.lam ..) | _, _, _, _, _, _, h@(.pi ..) | _, _, _, _, _, _, h@(.letE ..)
  | _, _, _, _, _, _, h@(.sorts ..) | _, _, _, _, _, _, h@(.consts ..) | _, _, _, _, _, _, h@(.eta ..)
  | _, _, _, _, _, _, h@(.irr ..) | _, _, _, _, _, _, h@(.tyConv ..) => [h.wt Aw]

end

mutual

/-- every atom of a typing weighs at most the typing. -/
theorem TyP.atoms_le (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → (D : TyP E n Γ e T) → ∀ x ∈ D.atoms Aw, x ≤ D.wt Aw
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => fun x hx => by
      have := TyP.atoms_le Aw D x hx
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT => fun x hx => by
      simp only [TyP.atoms, List.mem_append] at hx
      simp only [TyP.wt]
      rcases hx with (hx | hx) | hx
      · have := TyP.atoms_le Aw D x hx; omega
      · have := TyP.atoms_le Aw hv x hx; omega
      · have := TyP.atoms_le Aw hvT x hx; omega
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT => fun x hx => by
      simp only [TyP.atoms, List.mem_append] at hx
      simp only [TyP.wt]
      rcases hx with (hx | hx) | hx
      · have := TyP.atoms_le Aw D x hx; omega
      · have := TyP.atoms_le Aw hv x hx; omega
      · have := TyP.atoms_le Aw hvT x hx; omega
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => fun x hx => by
      have := TyP.atoms_le Aw D x hx
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => fun x hx => by
      have := TyP.atoms_le Aw D x hx
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => fun x hx => by
      simp only [TyP.atoms, List.mem_append] at hx
      simp only [TyP.wt]
      rcases hx with hx | hx
      · have := TyP.atoms_le Aw D x hx; omega
      · have := CvP.atoms_le Aw hA x hx; omega
  | _, _, _, _, _, .sort .. | _, _, _, _, _, .bvar .. | _, _, _, _, _, .const ..
  | _, _, _, _, _, .pi .. | _, _, _, _, _, .lam .. | _, _, _, _, _, .app ..
  | _, _, _, _, _, .letE .. | _, _, _, _, _, .lit .. | _, _, _, _, _, .conv .. => fun x hx => by
      simp only [TyP.atoms, List.mem_singleton] at hx
      subst hx; exact Nat.le_refl _

theorem CvP.atoms_le (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (h : CvP E n Γ a b T) → ∀ x ∈ h.atoms Aw, x ≤ h.wt Aw
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => fun x hx => by
      have := CvP.atoms_le Aw h x hx
      simp only [CvP.wt]; omega
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ hv hvT => fun x hx => by
      simp only [CvP.atoms, List.mem_append] at hx
      simp only [CvP.wt]
      rcases hx with (hx | hx) | hx
      · have := CvP.atoms_le Aw h x hx; omega
      · have := TyP.atoms_le Aw hv x hx; omega
      · have := TyP.atoms_le Aw hvT x hx; omega
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => fun x hx => by
      have := CvP.atoms_le Aw h x hx
      simp only [CvP.wt]; omega
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => fun x hx => by
      have := CvP.atoms_le Aw h x hx
      simp only [CvP.wt]; omega
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA => fun x hx => by
      simp only [CvP.atoms, List.mem_append] at hx
      simp only [CvP.wt]
      rcases hx with hx | hx
      · have := CvP.atoms_le Aw h x hx; omega
      · have := CvP.atoms_le Aw hA x hx; omega
  | _, _, _, _, _, _, .refl .. | _, _, _, _, _, _, .symm .. | _, _, _, _, _, _, .trans ..
  | _, _, _, _, _, _, .beta .. | _, _, _, _, _, _, .zeta .. | _, _, _, _, _, _, .zetaLocal ..
  | _, _, _, _, _, _, .delta .. | _, _, _, _, _, _, .iota .. | _, _, _, _, _, _, .lit ..
  | _, _, _, _, _, _, .app .. | _, _, _, _, _, _, .lam .. | _, _, _, _, _, _, .pi ..
  | _, _, _, _, _, _, .letE .. | _, _, _, _, _, _, .sorts .. | _, _, _, _, _, _, .consts ..
  | _, _, _, _, _, _, .eta .. | _, _, _, _, _, _, .irr .. | _, _, _, _, _, _, .tyConv ..
  | _, _, _, _, _, _, .fsub .. =>
      fun x hx => by
        simp only [CvP.atoms, List.mem_singleton] at hx
        subst hx; exact Nat.le_refl _

end

/-- THE CALL RULE (`S1` §3.1). If every atom of a call's arguments lies strictly below one atom `x` of
    the caller, the call is a `DMStep`. The caller's multiset is `x :: Z`, the call's is `Y ++ Z`,
    and the rest `Z` of the caller may also be kept. -/
theorem dmStep_of_below {x : Nat} {Y Z : List Nat} (h : ∀ y ∈ Y, y < x) : DMStep (Y ++ Z) (x :: Z) :=
  ⟨[x], Y, Z, List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => ⟨x, List.mem_cons_self _ _, h y hy⟩⟩

/-- a child of a rule node is a part of it: each of the child's atoms is below the node's atom. -/
theorem atoms_lt_of_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) {w : Nat} (h : D.wt Aw < w) : ∀ y ∈ D.atoms Aw, y < w :=
  fun y hy => Nat.lt_of_le_of_lt (TyP.atoms_le Aw D y hy) h

theorem cvp_atoms_lt_of_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) {w : Nat} (hw : h.wt Aw < w) :
    ∀ y ∈ h.atoms Aw, y < w :=
  fun y hy => Nat.lt_of_le_of_lt (CvP.atoms_le Aw h y hy) hw

/-! ## §5 the enriched environment and its admission weights -/

/-- the members of one inductive group, each with its stored type typed (enriched) in the group built
    so far. This is `GroupMembersT`'s `hT`; R2 makes it the only source of ι tags. `hnobody` is
    `GroupMembersT`'s: no group member has a body, so δ never reaches one. -/
inductive GroupMembersP : ResolvedEnv → List (Nat × CheckedMember) → ResolvedEnv → Type
  | nil (E : ResolvedEnv) : GroupMembersP E [] E
  | cons (E : ResolvedEnv) (r : Nat) (m : CheckedMember) (rest : List (Nat × CheckedMember))
      (E' : ResolvedEnv) (hfresh : E.members r = none) (hnobody : m.body = none) (u : Level)
      (hT : TyP E m.arity [] m.mtype (.sort u)) (hrest : GroupMembersP (extendEnv E r m) rest E') :
      GroupMembersP E ((r, m) :: rest) E'

/-- the enriched environment: `EnvWfT`'s steps with every admission derivation enriched. -/
inductive EnvWfP : ResolvedEnv → Type
  | empty : EnvWfP emptyEnv
  | axiom (E : ResolvedEnv) (r : Nat) (A : Expr Nat) (u : Level) (hE : EnvWfP E)
      (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort u)) :
      EnvWfP (extendEnv E r ⟨.axiomM, 0, A, none⟩)
  | definition (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level) (hE : EnvWfP E)
      (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort u)) (hv : TyP E 0 [] v A) :
      EnvWfP (extendEnv E r ⟨.definitionM, 0, A, some v⟩)
  | thm (E : ResolvedEnv) (r : Nat) (A p : Expr Nat) (hE : EnvWfP E)
      (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort .zero)) (hp : TyP E 0 [] p A) :
      EnvWfP (extendEnv E r ⟨.theoremM, 0, A, some p⟩)
  | opaque (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level) (hE : EnvWfP E)
      (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort u)) (hv : TyP E 0 [] v A) :
      EnvWfP (extendEnv E r ⟨.opaqueM, 0, A, some v⟩)
  | group (E : ResolvedEnv) (ms : List (Nat × CheckedMember)) (E' : ResolvedEnv) (hE : EnvWfP E)
      (hmem : GroupMembersP E ms E') : EnvWfP E'

/-- set the weight at one fresh member. -/
def setW (Aw : Nat → Nat) (r w : Nat) : Nat → Nat := fun c => if c = r then w else Aw c

theorem setW_self (Aw : Nat → Nat) (r w : Nat) : setW Aw r w r = w := by
  unfold setW; exact if_pos rfl

theorem setW_ne (Aw : Nat → Nat) {r c : Nat} (w : Nat) (h : c ≠ r) : setW Aw r w c = Aw c := by
  unfold setW; exact if_neg h

/-- the admission weights of a group, member after member: each pays its type derivation, weighed
    with the weights before it. -/
def GroupMembersP.admW : {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    {E' : ResolvedEnv} → GroupMembersP E ms E' → (Nat → Nat) → Nat → Nat
  | _, _, _, .nil _, Aw => Aw
  | _, _, _, .cons _ r _ _ _ _ _ _ hT hrest, Aw => hrest.admW (setW Aw r (1 + hT.wt Aw))

/-- O1's admission weights, by recursion on the enriched environment. A member pays its stored type's
    derivation and, if it has one, its body's derivation. -/
def EnvWfP.admW : {E : ResolvedEnv} → EnvWfP E → Nat → Nat
  | _, .empty => fun _ => 0
  | _, .axiom _ r _ _ hE _ hA => setW hE.admW r (1 + hA.wt hE.admW)
  | _, .definition _ r _ _ _ hE _ hA hv => setW hE.admW r (1 + hA.wt hE.admW + hv.wt hE.admW)
  | _, .thm _ r _ _ hE _ hA hp => setW hE.admW r (1 + hA.wt hE.admW + hp.wt hE.admW)
  | _, .opaque _ r _ _ _ hE _ hA hv => setW hE.admW r (1 + hA.wt hE.admW + hv.wt hE.admW)
  | _, .group _ _ _ hE hmem => hmem.admW hE.admW

/-- a fresh member's admission weight exceeds its type derivation's weight, weighed before it. This is
    the inequality `S1` §3.3's const row consumes. -/
theorem admW_axiom_gt {E : ResolvedEnv} {r : Nat} {A : Expr Nat} {u : Level} (hE : EnvWfP E)
    (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort u)) :
    hA.wt hE.admW < (EnvWfP.axiom E r A u hE hfresh hA).admW r := by
  show _ < setW hE.admW r (1 + hA.wt hE.admW) r
  rw [setW_self]; omega

theorem admW_definition_gt {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level} (hE : EnvWfP E)
    (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort u)) (hv : TyP E 0 [] v A) :
    hA.wt hE.admW + hv.wt hE.admW < (EnvWfP.definition E r A v u hE hfresh hA hv).admW r := by
  show _ < setW hE.admW r (1 + hA.wt hE.admW + hv.wt hE.admW) r
  rw [setW_self]; omega

/-- an old member keeps its weight. -/
theorem admW_axiom_old {E : ResolvedEnv} {r c : Nat} {A : Expr Nat} {u : Level} (hE : EnvWfP E)
    (hfresh : E.members r = none) (hA : TyP E 0 [] A (.sort u)) (hc : c ≠ r) :
    (EnvWfP.axiom E r A u hE hfresh hA).admW c = hE.admW c :=
  setW_ne hE.admW _ hc

/-! ## §6 pins: real enriched derivations -/

/-- `sort 0 : sort 1`. -/
def pinSortP : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := .sort _ _ _ _ _ (eqN_refl _)

/-- `∀ P : Prop, P`, typed at `sort 0` through `imax 1 0 =ₙ 0`: one `sorts` conversion, and its
    right endpoint `sort 0 : sort (succ (imax 1 0))` is one `sort` node. -/
def pinForallP : TyP emptyEnv 0 [] (.pi (.sort .zero) (.bvar 0)) (.sort .zero) :=
  .conv _ _ _ _ (.sort (.imax (.succ .zero) .zero)) (.sort .zero) (.succ (.imax (.succ .zero) .zero))
    (.pi _ _ _ (.sort .zero) (.succ .zero) (.bvar 0) .zero pinSortP
      (.bvar _ _ _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ _ _ _ _ (eqN_refl _))))
    (.sorts _ _ _ (.imax (.succ .zero) .zero) .zero (fun _ => rfl)
      (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (fun _ => rfl)))

/-- S0 §5's closed instance, enriched: `X := (λ _ : Prop. Prop) (∀ P : Prop, P)`, and
    `X ≡ sort 0 : sort 1` by β. sortRow must see through this β (all 18 ES arms, cc (d)). -/
def pinBetaP : CvP emptyEnv 0 []
    (.app (.lam (.sort .zero) (.sort .zero)) (.pi (.sort .zero) (.bvar 0)))
    (.sort .zero) (.sort (.succ .zero)) :=
  .beta _ _ _ (.sort .zero) (.sort .zero) (.pi (.sort .zero) (.bvar 0)) (.sort (.succ .zero))
    (.succ .zero) pinSortP (.sort _ _ _ _ _ (eqN_refl _)) pinForallP
    (.app _ _ _ (.lam (.sort .zero) (.sort .zero)) (.pi (.sort .zero) (.bvar 0)) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (.lam _ _ _ (.sort .zero) (.succ .zero) (.sort .zero) (.sort (.succ .zero)) (.succ (.succ .zero))
        pinSortP (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (eqN_refl _)))
      pinForallP (.sort _ _ _ _ _ (eqN_refl _)))
    pinSortP

/-- PIN: the β node outweighs both endpoint typings, at every admission weight. -/
theorem pinBetaP_dl_lt (Aw : Nat → Nat) : pinBetaP.dl.wt Aw < pinBetaP.wt Aw := CvP.wt_dl_lt Aw _
theorem pinBetaP_dr_lt (Aw : Nat → Nat) : pinBetaP.dr.wt Aw < pinBetaP.wt Aw := CvP.wt_dr_lt Aw _

end Rcic.Syn

#print axioms Rcic.Syn.envExt_extendEnv
#print axioms Rcic.Syn.TyP.wt_pos
#print axioms Rcic.Syn.CvP.wt_pos
#print axioms Rcic.Syn.CvP.wt_dl_lt
#print axioms Rcic.Syn.CvP.wt_dr_lt
#print axioms Rcic.Syn.TyP.reg
#print axioms Rcic.Syn.TyP.wt_reg_le
#print axioms Rcic.Syn.TyP.atoms_le
#print axioms Rcic.Syn.CvP.atoms_le
#print axioms Rcic.Syn.dmStep_of_below
#print axioms Rcic.Syn.atoms_lt_of_wt_lt
#print axioms Rcic.Syn.cvp_atoms_lt_of_wt_lt
#print axioms Rcic.Syn.admW_axiom_gt
#print axioms Rcic.Syn.admW_definition_gt
#print axioms Rcic.Syn.admW_axiom_old
#print axioms Rcic.Syn.pinForallP
#print axioms Rcic.Syn.pinBetaP
#print axioms Rcic.Syn.pinBetaP_dl_lt
#print axioms Rcic.Syn.pinBetaP_dr_lt
