import rcic.RcicConvPlus

/-!
# Syntactic sortRow, build step 3j — the head of a typing of a bvar

`research/rcic/semantic/S3_ES_ARMS.md` §11. `lift` and `instantiate` move a
de Bruijn index, so a typing of `.bvar i` is not "one constructor, or a hit"
the way `.app` / `.sort` are (`RcicSynHeadView`, `RcicSynSortView`). The split
is the arithmetic one:

* `wk` by 1 leaves `i` when the inserted binder sits strictly above it
  (`i < c`), and sends `i₀` to `i₀ + 1` when the binder sits at or below it
  (`c ≤ i₀`);
* `instantiate` leaves `i` when the hole sits strictly above it (`i < j`),
  sends `i₀` to `i₀ - 1` when the hole sits strictly below it (`j < i₀`),
  and on the hole itself returns the replacement;
* `instantiateLevels` does not touch the index.

The hole case is a bvar only when the replacement lifts to one. At cutoff 0
every index shifts, so `lift 0 j (.bvar k) = .bvar (k + j)`. The view names
`k`. It does not claim an erasure: on the `drop` path the substituted variable
can erase to `★`.

`esub_above` types `.bvar (i + 1)` in the inner derivation. The index grew.
The derivation is the structural child; this view is not an induction on `i`.
`esub_var` recurses into `hv`, which types the resulting `.bvar i`, and that
child is smaller as a derivation. It is not the `lexDM_wf` pack.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 what `lift` and `instantiate` do to an index -/

/-- `lift c k e = .bvar i`. Below the cutoff the index is unchanged. At or
    above it, the source index shifts by `k`. -/
inductive LiftBvar (c k i : Nat) (e : Expr Nat) : Type where
  | below (hlo : i < c) (he : e = .bvar i) : LiftBvar c k i e
  | shift (i₀ : Nat) (hge : c ≤ i₀) (he : e = .bvar i₀) (hi : i = i₀ + k) :
      LiftBvar c k i e

def lift_eq_bvar {c k i : Nat} {e : Expr Nat} (h : lift c k e = .bvar i) :
    LiftBvar c k i e := by
  cases e with
  | bvar i₀ =>
    unfold lift at h
    split at h
    · next hge =>
      cases h
      exact .shift i₀ hge rfl rfl
    · next hlo =>
      cases h
      exact .below (Nat.lt_of_not_le hlo) rfl
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- `instantiate j r e = .bvar i`. `below`: the variable sat strictly under the
    hole. `above`: it sat strictly over the hole, so the source index is
    `i + 1` (`i₀`, stored, because `i₀ - 1` is not definitionally `i`).
    `here`: the variable was the hole and the replacement is this bvar. -/
inductive InstBvar (j : Nat) (r e : Expr Nat) (i : Nat) : Type where
  | below (hlo : i < j) (he : e = .bvar i) : InstBvar j r e i
  | above (i₀ : Nat) (hgt : j < i₀) (he : e = .bvar i₀) (hi : i₀ = i + 1) :
      InstBvar j r e i
  | here (he : e = .bvar j) (hr : r = .bvar i) : InstBvar j r e i

def instantiate_eq_bvar {j i : Nat} {r e : Expr Nat} (h : instantiate j r e = .bvar i) :
    InstBvar j r e i := by
  cases e with
  | bvar i₀ =>
    unfold instantiate at h
    split at h
    · next heq =>
      cases heq
      exact .here rfl h
    · next hne =>
      split at h
      · next hgt =>
        cases h
        have hone : 1 ≤ i₀ := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) hgt)
        exact .above i₀ hgt rfl (Eq.symm (Nat.sub_add_cancel hone))
      · next hngt =>
        cases h
        exact .below (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hngt) hne) rfl
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- `instantiateLevels` does not change a bvar, and nothing else becomes one. -/
theorem instantiateLevels_eq_bvar {ls : List Level} {e : Expr Nat} {i : Nat}
    (h : instantiateLevels ls e = .bvar i) : e = .bvar i := by
  cases e with
  | bvar _ =>
    cases h
    rfl
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- `lift 0 j v = .bvar i`. Cutoff 0 sits at or below every index, so `v` is
    `.bvar k` and `i = k + j`. A `Type`: the head eliminates it. -/
inductive LiftZeroBvar (j i : Nat) (v : Expr Nat) : Type where
  | mk (k : Nat) (hv : v = .bvar k) (hi : i = k + j) : LiftZeroBvar j i v

def lift_zero_eq_bvar {j i : Nat} {v : Expr Nat} (h : lift 0 j v = .bvar i) :
    LiftZeroBvar j i v := by
  cases lift_eq_bvar h with
  | below hlo _ => exact absurd hlo (Nat.not_lt_zero i)
  | shift k _ hk hi => exact .mk k hk hi

/-! ## §2 the head -/

/-- How a derivation of `.bvar i` is built. One transport, with the index
    arithmetic of that transport, or the `bvar` node, or the hole whose
    replacement lifts to this index. -/
inductive BvarHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) (T : Expr Nat) : Type
  | node (A : Expr Nat) (u : Level)
      (h : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u)) (hT : T = A)
  | conv (A B : Expr Nat) (u : Level) (inner : TyP E n Γ (.bvar i) A)
      (hc : CvP E n Γ A B (.sort u)) (hT : T = B)
  | wk_below (Γ₀ : LCtx) (A : Expr Nat) (d : LocalDecl) (c : Nat)
      (inner : TyP E n Γ₀ (.bvar i) A) (hlo : i < c)
      (hΓ : Γ = insertAt d c Γ₀) (hT : T = lift c 1 A)
  | wk_shift (Γ₀ : LCtx) (A : Expr Nat) (d : LocalDecl) (c i₀ : Nat)
      (inner : TyP E n Γ₀ (.bvar i₀) A) (hge : c ≤ i₀) (hi : i = i₀ + 1)
      (hΓ : Γ = insertAt d c Γ₀) (hT : T = lift c 1 A)
  | esub_below (Γ₀ : LCtx) (A t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar i) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlo : i < j) (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (lift 0 j v) A)
  | lsub_below (Γ₀ : LCtx) (A t v : Expr Nat) (j : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar i) A) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hlo : i < j) (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (lift 0 j v) A)
  | esub_above (Γ₀ : LCtx) (A t v : Expr Nat) (j i₀ : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar i₀) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hgt : j < i₀) (hi : i₀ = i + 1)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (lift 0 j v) A)
  | lsub_above (Γ₀ : LCtx) (A t v : Expr Nat) (j i₀ : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar i₀) A) (hget : Γ₀[j]? = some (.letBinding t v))
      (hv : TyP E n Γ (lift 0 j v) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hgt : j < i₀) (hi : i₀ = i + 1)
      (hΓ : Γ = substRemove v j Γ₀)
      (hT : T = instantiate j (lift 0 j v) A)
  | esub_var (Γ₀ : LCtx) (A t : Expr Nat) (j k : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) A) (hget : Γ₀[j]? = some (.assumption t))
      (hv : TyP E n Γ (.bvar i) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hk : i = k + j) (hΓ : Γ = substRemove (.bvar k) j Γ₀)
      (hT : T = instantiate j (.bvar i) A)
  | lsub_var (Γ₀ : LCtx) (A t : Expr Nat) (j k : Nat) (u : Level)
      (inner : TyP E n Γ₀ (.bvar j) A) (hget : Γ₀[j]? = some (.letBinding t (.bvar k)))
      (hv : TyP E n Γ (.bvar i) (lift 0 j t))
      (hvT : TyP E n Γ (lift 0 j t) (.sort u))
      (hk : i = k + j) (hΓ : Γ = substRemove (.bvar k) j Γ₀)
      (hT : T = instantiate j (.bvar i) A)
  | linst (a : Nat) (Γ₀ : LCtx) (A : Expr Nat) (ls : List Level)
      (hls : levelsBounded n ls = true) (hlen : ls.length = a)
      (inner : TyP E a Γ₀ (.bvar i) A)
      (hΓ : Γ = instLvlsCtx ls Γ₀) (hT : T = instantiateLevels ls A)
  | ewk (E₀ : ResolvedEnv) (inner : TyP E₀ n Γ (.bvar i) T) (hext : EnvExt E₀ E)
  | cctx (Γtail : LCtx) (A A' : Expr Nat) (u : Level)
      (inner : TyP E n (.assumption A :: Γtail) (.bvar i) T)
      (hA : CvP E n Γtail A A' (.sort u)) (hΓ : Γ = .assumption A' :: Γtail)

/-- Every typing of `.bvar i` has one of these heads. The term is generalized
    first: matching `TyP` directly at `.bvar i` cannot solve `bvar i = lift c 1 e`
    or `bvar i = instantiate j r e`. -/
def bvarHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {T : Expr Nat}
    (D : TyP E n Γ (.bvar i) T) : BvarHead E n Γ i T := by
  generalize he : Expr.bvar i = e at D
  cases D
  -- `A` is the motive's type index `T`: the `bvar` node ascribes the looked-up type.
  case bvar i' u h hA =>
    cases he
    exact .node T u h hA rfl
  case conv A u inner hc =>
    cases he
    exact .conv A T u inner hc rfl
  case ewk E₀ hext inner =>
    cases he
    exact .ewk E₀ inner hext
  case sort => cases he
  case const => cases he
  case pi => cases he
  case lam => cases he
  case app => cases he
  case letE => cases he
  case lit => cases he
  case wk Γ₀ e₀ A d c inner =>
    cases lift_eq_bvar he.symm with
    | below hlo hs =>
      cases hs
      exact .wk_below Γ₀ A d c inner hlo rfl rfl
    | shift i₀ hge hs hi =>
      cases hs
      exact .wk_shift Γ₀ A d c i₀ inner hge hi rfl rfl
  case esub Γ₀ e₀ A t v j u hget inner hv hvT =>
    cases instantiate_eq_bvar he.symm with
    | below hlo hs =>
      cases hs
      exact .esub_below Γ₀ A t v j u inner hget hv hvT hlo rfl rfl
    | above i₀ hgt hs hi =>
      cases hs
      exact .esub_above Γ₀ A t v j i₀ u inner hget hv hvT hgt hi rfl rfl
    | here hs hr =>
      cases hs
      cases lift_zero_eq_bvar hr with
      | mk k hvb hi =>
        cases hvb
        exact .esub_var Γ₀ A t j k u inner hget (hr ▸ hv) hvT hi rfl
          (congrArg (fun e => instantiate j e A) hr)
  case lsub Γ₀ e₀ A t v j u hget inner hv hvT =>
    cases instantiate_eq_bvar he.symm with
    | below hlo hs =>
      cases hs
      exact .lsub_below Γ₀ A t v j u inner hget hv hvT hlo rfl rfl
    | above i₀ hgt hs hi =>
      cases hs
      exact .lsub_above Γ₀ A t v j i₀ u inner hget hv hvT hgt hi rfl rfl
    | here hs hr =>
      cases hs
      cases lift_zero_eq_bvar hr with
      | mk k hvb hi =>
        cases hvb
        exact .lsub_var Γ₀ A t j k u inner hget (hr ▸ hv) hvT hi rfl
          (congrArg (fun e => instantiate j e A) hr)
  case linst a Γ₀ e₀ A ls hlen inner hls =>
    have hs : e₀ = .bvar i := instantiateLevels_eq_bvar he.symm
    cases hs
    exact .linst a Γ₀ A ls hls hlen inner rfl rfl
  case cctx Γtail A A' u hA inner =>
    cases he
    exact .cctx Γtail A A' u inner hA rfl

end Rcic.Syn

#print axioms Rcic.Syn.lift_eq_bvar
#print axioms Rcic.Syn.instantiate_eq_bvar
#print axioms Rcic.Syn.instantiateLevels_eq_bvar
#print axioms Rcic.Syn.lift_zero_eq_bvar
#print axioms Rcic.Syn.bvarHead
