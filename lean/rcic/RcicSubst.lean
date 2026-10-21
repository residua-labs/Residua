/-
RCIC substitution construction — the 1:1 mirror of RcicWeaken (#3687),
unblocking DT-005/006 and, through them, DT-008/010/011.

CORRECTION to the pushed context operations (knife-2-final branch): the
per-entry substitution is DEPTH-DEPENDENT. Removing position j, the entry
at position i < j stores its type over the context starting at i+1, where
the removed slot sits at relative index j-1-i — so the entry substitutes
at THAT index, with the replacement lifted to THAT depth:
    instDecl k v : instantiate k (lift 0 k v) ·
A uniform `instantiate0 v` substitutes the wrong variable with a
capturable replacement; the lookup commutation laws are then unprovable —
which is where the reported 27 type errors begin.

Layering: the binder cases TRANSPORT the replacement-typing premise by
`hasTyWeaken` at cutoff 0 — the weakening construction is consumed here,
which is the layering working as intended. beta/zeta ride P6
(instantiate_instantiate); eta rides lift_instantiate_high; the removed-
slot bvar case rides P5 (instantiate_lift_cancel).

Premises mirror RcicWeaken's and are named obligations: EnvSubst
(02 §6 checked members are closed, hence substitution-invariant),
IotaSubst / LitSubst (05/08-owned transports, Type-valued — never
fabricated). The construction additionally consumes RcicWeaken's three.

AXIOM-HYGIENE FINDING (recorded for the batch): a bare `by simp` inside
a sealed construction is a lottery — RcicWeaken's eta case survived it,
this file's identical-shaped eta case drew Classical.choice through the
default simp set and was REJECTED by the seal. The discipline: inside
sealed constructions, close if-goals with explicit if_pos/if_neg + omega,
and bridge getElem? shifts with the named rewrite, never `simpa`.

INFRASTRUCTURE (M-010): DT-005/006's interface statements remain the
batch's — terminal Nonempty wrappers; at j = 0 the premise collapses to
the textbook `HasTy E n Γ v t`.
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc
import rcic.RcicCtxMorph
import rcic.RcicWeaken
import rcic.RcicEnv
import rcic.RcicIota

namespace Rcic.Declarative

/-- Substitute-transport for the 08-owned literal interface. Discharged:
`natExpand` is closed under instantiate. -/
def LitSubst : Type :=
  ∀ t exp, LiteralExpansion t exp →
    ∀ v c, LiteralExpansion t (instantiate c v exp)

def litSubst : LitSubst
  | t, _, .of _, v, c => by
      change LiteralExpansion t (instantiate c v (natExpand t))
      rw [natExpand_instantiate]
      exact .of t

/-- Substitute in one stored declaration at depth k: the removed slot sits
at relative index k, and the replacement is v lifted past the k entries
between this one and the removal point. -/
def instDecl (k : Nat) (v : Expr Nat) : LocalDecl → LocalDecl
  | .assumption A => .assumption (instantiate k (lift 0 k v) A)
  | .letBinding A w =>
      .letBinding (instantiate k (lift 0 k v) A) (instantiate k (lift 0 k v) w)

/-- Remove the entry at position j, substituting in the entries below it. -/
def substRemove (v : Expr Nat) : Nat → LCtx → LCtx
  | 0, [] => []
  | 0, _ :: Γ => Γ
  | _+1, [] => []
  | j+1, x :: Γ => instDecl j v x :: substRemove v j Γ

@[simp] theorem substRemove_zero_cons (v : Expr Nat) (x : LocalDecl) (Γ : LCtx) :
    substRemove v 0 (x :: Γ) = Γ := rfl

@[simp] theorem substRemove_succ_cons (v : Expr Nat) (j : Nat) (x : LocalDecl) (Γ : LCtx) :
    substRemove v (j+1) (x :: Γ) = instDecl j v x :: substRemove v j Γ := rfl

/-! ### Lookup commutation (mirrors CtxMorph's four; rides P2/P5 and
lift_instantiate_high). -/

/-- Below the removal point: same index, looked-up type substituted. -/
theorem lookupType_substRemove_lt {v : Expr Nat} {j i : Nat} {Γ : LCtx}
    {A : Expr Nat} (hij : i < j) (h : lookupType Γ i = some A) :
    lookupType (substRemove v j Γ) i =
      some (instantiate j (lift 0 j v) A) := by
  induction j generalizing i Γ A with
  | zero => omega
  | succ j ih =>
    match Γ with
    | [] => simp [lookupType] at h
    | x :: Γ' =>
      match i with
      | 0 =>
        match x with
        | .assumption a =>
            simp only [lookupType, List.get?_cons_zero] at h
            cases h
            simp only [substRemove_succ_cons, lookupType, List.get?_cons_zero,
              instDecl, Option.some.injEq]
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega),
                show j + 1 = j + 1 from rfl]
        | .letBinding a w =>
            simp only [lookupType, List.get?_cons_zero] at h
            cases h
            simp only [substRemove_succ_cons, lookupType, List.get?_cons_zero,
              instDecl, Option.some.injEq]
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      | i' + 1 =>
        rw [lookupType_cons_succ] at h
        match h' : lookupType Γ' i' with
        | none => rw [h'] at h; simp at h
        | some A' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [substRemove_succ_cons, lookupType_cons_succ,
                ih (by omega) h', Option.map_some']
            congr 1
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega)]

/-- Above the removal point: index drops by one; the substitution on the
looked-up type is consumed by the P5 cancel (the replacement is never
consulted), leaving the plain reindexed lookup. -/
theorem lookupType_substRemove_gt {v : Expr Nat} {j i : Nat} {Γ : LCtx}
    {A : Expr Nat} (hij : j < i) (h : lookupType Γ i = some A) :
    lookupType (substRemove v j Γ) (i - 1) =
      some (instantiate j (lift 0 j v) A) := by
  induction j generalizing i Γ A with
  | zero =>
    match Γ, i with
    | [], _ => simp [lookupType] at h
    | x :: Γ', i' + 1 =>
        rw [lookupType_cons_succ] at h
        match h' : lookupType Γ' i' with
        | none => rw [h'] at h; simp at h
        | some A' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [instantiate_lift_cancel 1 0 0 (lift 0 0 v) (by omega) (by omega),
                lift_zero]
  | succ j ih =>
    match Γ, i with
    | [], _ => simp [lookupType] at h
    | x :: Γ', i' + 1 =>
        rw [lookupType_cons_succ] at h
        match h' : lookupType Γ' i' with
        | none => rw [h'] at h; simp at h
        | some A' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            have hj : j < i' := by omega
            have step := ih hj h'
            rw [substRemove_succ_cons,
                show i' + 1 - 1 = (i' - 1) + 1 from by omega,
                lookupType_cons_succ, step, Option.map_some']
            congr 1
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega)]

/-- Value analogue, below. -/
theorem lookupValue_substRemove_lt {v : Expr Nat} {j i : Nat} {Γ : LCtx}
    {w : Expr Nat} (hij : i < j) (h : lookupValue Γ i = some w) :
    lookupValue (substRemove v j Γ) i =
      some (instantiate j (lift 0 j v) w) := by
  induction j generalizing i Γ w with
  | zero => omega
  | succ j ih =>
    match Γ with
    | [] => simp [lookupValue] at h
    | x :: Γ' =>
      match i with
      | 0 =>
        match x with
        | .assumption a => simp [lookupValue, List.get?_cons_zero] at h
        | .letBinding a w' =>
            simp only [lookupValue, List.get?_cons_zero] at h
            cases h
            simp only [substRemove_succ_cons, lookupValue, List.get?_cons_zero,
              instDecl, Option.some.injEq]
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      | i' + 1 =>
        rw [lookupValue_cons_succ] at h
        match h' : lookupValue Γ' i' with
        | none => rw [h'] at h; simp at h
        | some w' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [substRemove_succ_cons, lookupValue_cons_succ,
                ih (by omega) h', Option.map_some']
            congr 1
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega)]

/-- Value analogue, above. -/
theorem lookupValue_substRemove_gt {v : Expr Nat} {j i : Nat} {Γ : LCtx}
    {w : Expr Nat} (hij : j < i) (h : lookupValue Γ i = some w) :
    lookupValue (substRemove v j Γ) (i - 1) =
      some (instantiate j (lift 0 j v) w) := by
  induction j generalizing i Γ w with
  | zero =>
    match Γ, i with
    | [], _ => simp [lookupValue] at h
    | x :: Γ', i' + 1 =>
        rw [lookupValue_cons_succ] at h
        match h' : lookupValue Γ' i' with
        | none => rw [h'] at h; simp at h
        | some w' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [instantiate_lift_cancel 1 0 0 (lift 0 0 v) (by omega) (by omega),
                lift_zero]
  | succ j ih =>
    match Γ, i with
    | [], _ => simp [lookupValue] at h
    | x :: Γ', i' + 1 =>
        rw [lookupValue_cons_succ] at h
        match h' : lookupValue Γ' i' with
        | none => rw [h'] at h; simp at h
        | some w' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            have step := ih (by omega) h'
            rw [substRemove_succ_cons,
                show i' + 1 - 1 = (i' - 1) + 1 from by omega,
                lookupValue_cons_succ, step, Option.map_some']
            congr 1
            rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
                show 1 + j = j + 1 from by omega,
                lift_lift_merge 1 j 0 0 (by omega) (by omega)]


/-! ### get?-to-lookup bridges (the removed entry is an assumption) -/

theorem lookupType_get_assumption {Γ : LCtx} {j : Nat} {t : Expr Nat}
    (h : Γ[j]? = some (.assumption t)) :
    lookupType Γ j = some (lift 0 (j+1) t) := by
  simp [lookupType, h]

theorem lookupValue_get_assumption {Γ : LCtx} {j : Nat} {t : Expr Nat}
    (h : Γ[j]? = some (.assumption t)) :
    lookupValue Γ j = none := by
  simp [lookupValue, h]

/-! ### The construction. Six transport premises (RcicWeaken's three are
CONSUMED at every binder, transporting the replacement's typing into the
extended context — the layering working as intended) plus the removal
premises: the entry at j is an assumption of stored type t, and the
replacement, lifted to the removal depth, has that type in the reduced
context. At j = 0 the typing premise collapses to the textbook
`HasTy E n Γ v t`. -/

mutual

def stepSubst {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    Step E n Γ a b →
    Γ[j]? = some (.assumption t) →
    HasTy E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    Step E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
  | j, _, _, _, .beta Γ A body arg, hget, hvty => by
      have h6 := instantiate_instantiate 0 j arg (lift 0 j v) (by omega) body
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .beta _ _ _ _
  | j, _, _, _, .zeta Γ A value body, hget, hvty => by
      have h6 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) body
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .zeta _ _ _ _
  | j, _, _, _, .zetaLocal Γ i v0 hvl, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        rw [lookupValue_get_assumption hget] at hvl
        exact Option.noConfusion hvl
      · by_cases hlt : i < j
        · have := lookupValue_substRemove_lt (v := v) hlt hvl
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .zetaLocal _ _ _ this
        · have := lookupValue_substRemove_gt (v := v) (by omega : j < i) hvl
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i)]
          exact .zetaLocal _ _ _ this
  | j, _, _, _, .delta Γ r ls m b hres hbody htr, hget, hvty => by
      -- 00 §20.6: the conclusion index is now `instantiateLevels ls b`.
      have hb := (envWf_subst_inst hE r m hres).2 b hbody ls (lift 0 j v) j
      simp only [instantiate]
      rw [hb]
      exact .delta _ r ls m b hres hbody htr
  | j, _, _, _, .iota Γ lhs rhs h, hget, hvty => by
      exact .iota _ _ _ (iotaSubst E lhs rhs h (lift 0 j v) j)
  | j, _, _, _, .lit Γ tl exp h, hget, hvty => by
      simp only [instantiate]
      exact .lit _ _ _ (litSubst tl exp h (lift 0 j v) j)

def convSubst {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    Conv E n Γ a b →
    Γ[j]? = some (.assumption t) →
    HasTy E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    Conv E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
  | j, _, _, _, .refl _ a, hget, hvty => .refl _ _
  | j, _, _, _, .symm _ _ _ h, hget, hvty =>
      .symm _ _ _ (convSubst hE v t h hget hvty)
  | j, _, _, _, .trans _ _ _ _ h1 h2, hget, hvty =>
      .trans _ _ _ _ (convSubst hE v t h1 hget hvty)
        (convSubst hE v t h2 hget hvty)
  | j, _, _, _, .step _ _ _ hs, hget, hvty =>
      .step _ _ _ (stepSubst hE v t hs hget hvty)
  | j, _, _, _, .app _ _ _ _ _ h1 h2, hget, hvty => by
      simp only [instantiate]
      exact .app _ _ _ _ _ (convSubst hE v t h1 hget hvty)
        (convSubst hE v t h2 hget hvty)
  | j, _, _, _, .lam Γ A A2 b1 b2 hA hb, hget, hvty => by
      have hvty' :
          HasTy E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j v (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convSubst hE v t
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ _ _ _ (convSubst hE v t hA hget hvty) hb'
  | j, _, _, _, .pi Γ A A2 b1 b2 hA hb, hget, hvty => by
      have hvty' :
          HasTy E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j v (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convSubst hE v t
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ _ _ _ (convSubst hE v t hA hget hvty) hb'
  | j, _, _, _, .letE Γ A A2 vv vv2 b1 b2 hA hv hb, hget, hvty => by
      have hvty' :
          HasTy E n (substRemove v (j+1) (LocalDecl.letBinding A vv :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j v (LocalDecl.letBinding A vv))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A vv :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convSubst hE v t
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ _ _ _ _ _ (convSubst hE v t hA hget hvty)
        (convSubst hE v t hv hget hvty) hb'
  | j, _, _, _, .sorts _ l1 l2 h, hget, hvty => by
      simp only [instantiate]; exact .sorts _ l1 l2 h
  | j, _, _, _, .consts _ r ls ls' h, hget, hvty => by
      simp only [instantiate]; exact .consts _ r ls ls' h
  | j, _, _, _, .eta _ f A B hh, hget, hvty => by
      have hf' := hasTySubst hE v t (j := j) hh hget hvty
      simp only [instantiate] at hf' ⊢
      have hp : instantiate (j+1) (lift 0 1 (lift 0 j v)) (lift 0 1 f) =
          lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [lift_instantiate_high 1 0 j (lift 0 j v) (by omega),
            show 1 + j = j + 1 from by omega]
      rw [show (if (0 : Nat) = j + 1 then lift 0 1 (lift 0 j v)
            else if j + 1 < 0 then Expr.bvar (0-1) else Expr.bvar 0) = Expr.bvar 0
            from by rw [if_neg (by omega : ¬ (0:Nat) = j + 1),
                        if_neg (by omega : ¬ j + 1 < 0)], hp]
      exact .eta _ _ _ _ hf'
  | j, _, _, _, .irr _ P p q hP hp hq, hget, hvty => by
      have hP' := hasTySubst hE v t hP hget hvty
      simp only [instantiate] at hP'
      exact .irr _ _ _ _ hP' (hasTySubst hE v t hp hget hvty)
        (hasTySubst hE v t hq hget hvty)

def hasTySubst {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTy E n Γ e A →
    Γ[j]? = some (.assumption t) →
    HasTy E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    HasTy E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  | j, _, _, _, .sort Γ l, hget, hvty => by
      simp only [instantiate]; exact .sort _ l
  | j, _, _, _, .bvar Γ i A h, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        rw [lookupType_get_assumption hget] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i+1) 0 i (lift 0 i v) (by omega) (by omega)]
        exact hvty
      · by_cases hlt : i < j
        · have := lookupType_substRemove_lt (v := v) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .bvar _ _ _ this
        · have := lookupType_substRemove_gt (v := v) (by omega : j < i) h
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i)]
          exact .bvar _ _ _ this
  | j, _, _, _, .const Γ r ls m hres hlen hwf, hget, hvty => by
      -- 00 §20.6: the ascribed type is now `instantiateLevels ls m.mtype`.
      have hm := (envWf_subst_inst hE r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact .const _ r ls m hres hlen hwf
  | j, _, _, _, .pi Γ A u B w hA hB, hget, hvty => by
      simp only [instantiate]
      have hvty' :
          HasTy E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j v (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hB' := hasTySubst hE v t
        (j := j + 1) hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB'
      have hA' := hasTySubst hE v t hA hget hvty
      simp only [instantiate] at hA'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ u _ w hA' hB'
  | j, _, _, _, .lam Γ A u body B hA hbody, hget, hvty => by
      simp only [instantiate]
      have hA' := hasTySubst hE v t hA hget hvty
      simp only [instantiate] at hA'
      have hvty' :
          HasTy E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j v (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTySubst hE v t
        (j := j + 1) hbody hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ u _ _ hA' hb'
  | j, _, _, _, .app Γ f a A B hf ha, hget, hvty => by
      have hf' := hasTySubst hE v t hf hget hvty
      have ha' := hasTySubst hE v t ha hget hvty
      simp only [instantiate] at hf'
      have h6 := instantiate_instantiate 0 j a (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ hf' ha'
  | j, _, _, _, .letE Γ A u value B hA hv hb, hget, hvty => by
      have hA' := hasTySubst hE v t hA hget hvty
      simp only [instantiate] at hA'
      have hv' := hasTySubst hE v t hv hget hvty
      have hvty' :
          HasTy E n (substRemove v (j+1) (LocalDecl.letBinding A value :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j v (LocalDecl.letBinding A value))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A value :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTySubst hE v t
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ u _ _ hA' hv' hb'
  | j, _, _, _, .conv Γ e A B h hc, hget, hvty => by
      exact .conv _ _ _ _ (hasTySubst hE v t h hget hvty)
        (convSubst hE v t hc hget hvty)
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvty => by
      have hexp' := hasTySubst hE v t hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      simp only [instantiate]
      exact .lit _ _ _ hexp'

end

end Rcic.Declarative
