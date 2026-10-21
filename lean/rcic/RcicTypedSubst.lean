import rcic.RcicTypedWeaken
import rcic.RcicSubst

/-!
# M3-b GLM-2 — the typed substitution theorem (DT009T's prerequisite, paid)

The raw judgment's transport lives in `RcicSubst` (`stepSubst`/`convSubst`); the
TYPED judgment had none. This module lands it, reusing the raw side's
judgment-independent machinery verbatim (`substRemove`/`instDecl`, the four
lookup commutations, `instantiate_instantiate`, `instantiate_lift_cancel`,
`lift_lift_merge`, `litSubst`, `iotaSubst`, `natExpand_instantiate`):

* `hasTyTWeaken` / `convTWeaken` (mutual): one-declaration weakening on the typed
  judgment — the typed analog of `RcicWeaken.hasTyWeaken`, same shape, EnvClosed
  premise for the const case's closed ascribed type.
* `hasTyT_subst` / `convT_subst` (mutual): THE substitution theorem on the typed
  judgment, general `j`, EnvSubst premise (discharged from EnvWf by
  `envWf_subst`); the ι constructor's DerivedIota transports by the raw side's
  own `iotaSubst` (judgment-independent), its typings by the mutual recursion.
* `hasTyT_subst0`: the `j = 0` lift-free form the β rule reads
  (`instantiate_lift_id` cancels the lifts).

DT009T (endpoint typings at ANY type) consumes `hasTyT_subst0` in
`RcicDTMetaTyped` — the next commit there. No row premises, no annotation, no
bridge; judgments stay Type-valued; no runtime data extracted.
-/

namespace Rcic.Declarative

/-- the member-level substitution stability the `const`/`delta` arms read —
    `envWf_subst_inst`'s conclusion, standalone. With `EnvClosed E`, this is ALL
    the structure the typed substitution uses; both are `EnvWf E n` facts, but
    the core below reads only the structure, so any environment entry that
    supplies these two (the typed entry included, once it does) fronts the same
    theorem. -/
def EnvMembersSubstStable (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m →
    (∀ ls s k, instantiate k s (instantiateLevels ls m.mtype)
        = instantiateLevels ls m.mtype) ∧
    (∀ b, m.body = some b →
      ∀ ls s k, instantiate k s (instantiateLevels ls b)
        = instantiateLevels ls b)

/-! ## the substitution theorem, general j (mutual) -/

mutual/-- THE TYPED SUBSTITUTION THEOREM: a typing over an assumption at `j`, plus the
    replacement's typing at the lifted domain in the substituted context, moves
    to the substituted context with term and type instantiated. -/
def hasTyT_substS {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A → Γ[j]? = some (.assumption t) →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    HasTyT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  | j, _, _, _, .sort _ _, _, _ => by
      simp only [instantiate]; exact .sort _ _
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
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          exact .bvar _ _ _ this
  | j, _, _, _, .const Γ r ls m hres hlen hwf, hget, hvty => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact .const _ r ls m hres hlen hwf
  | j, _, _, _, .pi Γ A u B w hA hB, hget, hvty => by
      simp only [instantiate]
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hB' := hasTyT_substS hcl hinst v t (j := j + 1) hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB'
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      simp only [instantiate] at hA'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ u _ w hA' hB'
  | j, _, _, _, .lam Γ A u body B hA hbody, hget, hvty => by
      simp only [instantiate]
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      simp only [instantiate] at hA'
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substS hcl hinst v t (j := j + 1) hbody hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ u _ _ hA' hb'
  | j, _, _, _, .app Γ f a A B hf ha, hget, hvty => by
      have hf' := hasTyT_substS hcl hinst v t hf hget hvty
      have ha' := hasTyT_substS hcl hinst v t ha hget hvty
      simp only [instantiate] at hf'
      have h6 := instantiate_instantiate 0 j a (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ hf' ha'
  | j, _, _, _, .letE Γ A u value B body hA hv hb, hget, hvty => by
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      simp only [instantiate] at hA'
      have hv' := hasTyT_substS hcl hinst v t hv hget hvty
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.letBinding A value :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.letBinding A value))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A value :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substS hcl hinst v t (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ u _ _ _ hA' hv' hb'
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvty => by
      have hexp' := hasTyT_substS hcl hinst v t hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      simp only [instantiate]
      exact .lit _ _ _ hexp'
  | j, _, _, _, .conv Γ e A B u h hc, hget, hvty =>
      .conv _ _ _ _ _ (hasTyT_substS hcl hinst v t h hget hvty) (convT_substS hcl hinst v t hc hget hvty)
  termination_by j Γ e A h _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- substitution on conversions at a fixed type. -/
def convT_substS {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (v t : Expr Nat) :
    {j : Nat}→ {Γ : LCtx}→ {a b T : Expr Nat}→
      ConvT E n Γ a b T → Γ[j]? = some (.assumption t) →
      HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
      ConvT E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
        (instantiate j (lift 0 j v) T)
  | j, _, _, _, _, .refl _ a A h, hget, hvty =>
      .refl _ _ _ (hasTyT_substS hcl hinst v t h hget hvty)
  | j, _, _, _, _, .symm _ _ _ _ h, hget, hvty =>
      .symm _ _ _ _ (convT_substS hcl hinst v t h hget hvty)
  | j, _, _, _, _, .trans _ _ _ _ _ h1 h2, hget, hvty =>
      .trans _ _ _ _ _ (convT_substS hcl hinst v t h1 hget hvty)
        (convT_substS hcl hinst v t h2 hget hvty)
  | j, _, _, _, _, .beta Γ A body arg B u hA hbody harg, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substS hcl hinst v t (j := j + 1) hbody hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have harg' := hasTyT_substS hcl hinst v t harg hget hvty
      simp only [instantiate] at hA' harg'
      have h6 := instantiate_instantiate 0 j arg (lift 0 j v) (by omega) body
      have h7 := instantiate_instantiate 0 j arg (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, h7]
      have hlv : lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
        lift_lift_merge (e := v) 1 j 0 0 (by omega) (by omega)
      first
        | rw [hlv]
        | skip
      exact .beta _ _ _ _ _ _ hA' hb' harg'
  | j, _, _, _, _, .zeta Γ A value body B u hA hv hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.letBinding A value :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.letBinding A value))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A value :: Γ)[j+1]? =
          some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substS hcl hinst v t (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) body
      have h7 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, h7]
      have hlv : lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
        lift_lift_merge (e := v) 1 j 0 0 (by omega) (by omega)
      first
        | rw [hlv]
        | skip
      exact .zeta _ _ _ _ _ _
        (hasTyT_substS hcl hinst v t hA hget hvty)
        (hasTyT_substS hcl hinst v t hv hget hvty) hb'
  | j, _, _, _, _, .zetaLocal Γ i A v0 hval hty hv, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        rw [lookupValue_get_assumption hget] at hval
        exact absurd hval (by simp)
      · by_cases hlt : i < j
        · have hval' := lookupValue_substRemove_lt (v := v) hlt hval
          have hty' := lookupType_substRemove_lt (v := v) hlt hty
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .zetaLocal _ _ _ _ hval' hty' (hasTyT_substS hcl hinst v t hv hget hvty)
        · have hval' := lookupValue_substRemove_gt (v := v) (by omega : j < i) hval
          have hty' := lookupType_substRemove_gt (v := v) (by omega : j < i) hty
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          exact .zetaLocal _ _ _ _ hval' hty' (hasTyT_substS hcl hinst v t hv hget hvty)
  | j, _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb, hget, hvty => by
      have hb' := hasTyT_substS hcl hinst v t hb hget hvty
      rw [(hinst r m hres).2 b hbody ls (lift 0 j v) j,
          (hinst r m hres).1 ls (lift 0 j v) j] at hb'
      rw [(hinst r m hres).2 b hbody ls (lift 0 j v) j,
          (hinst r m hres).1 ls (lift 0 j v) j]
      exact .delta _ r ls m b hres hbody htr hlen hwf hb'
  | j, _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs, hget, hvty =>
      .iota _ _ _ _ (iotaSubst E lhs rhs h (lift 0 j v) j)
        (hasTyT_substS hcl hinst v t hlhs hget hvty) (hasTyT_substS hcl hinst v t hrhs hget hvty)
  | j, _, _, _, _, .lit Γ tN exp T h hexp, hget, hvty => by
      have hexp' := hasTyT_substS hcl hinst v t hexp hget hvty
      cases h
      rw [natExpand_instantiate j (lift 0 j v) tN] at hexp'
      simp only [instantiate]
      rw [natExpand_instantiate j (lift 0 j v) tN]
      exact .lit _ _ _ _ (.of tN) hexp'
  | j, _, _, _, _, .app Γ f g a b A B h1 h2, hget, hvty => by
      have h6 := instantiate_instantiate 0 j a (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ _ _ (convT_substS hcl hinst v t h1 hget hvty)
        (convT_substS hcl hinst v t h2 hget hvty)
  | j, _, _, _, _, .lam Γ A A2 b1 b2 B u hA hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substS hcl hinst v t (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ _ _ _ _ _ (convT_substS hcl hinst v t hA hget hvty) hb'
  | j, _, _, _, _, .pi Γ A A2 b1 b2 u v' hA hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substS hcl hinst v t (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ _ _ _ _ _ (convT_substS hcl hinst v t hA hget hvty) hb'
  | j, _, _, _, _, .letE Γ A A2 vv vv2 b1 b2 B u hA hv hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove v (j+1) (LocalDecl.letBinding A vv :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (LocalDecl.letBinding A vv))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A vv :: Γ)[j+1]? = some (LocalDecl.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substS hcl hinst v t (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j vv (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ _ _ _ _ _ _ _ (convT_substS hcl hinst v t hA hget hvty)
        (convT_substS hcl hinst v t hv hget hvty) hb'
  | j, _, _, _, _, .sorts _ l1 l2 h, hget, hvty => by
      simp only [instantiate]; exact .sorts _ l1 l2 h
  | j, _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h, hget, hvty => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact .consts _ r ls ls' m hres hlen hwf hwf' h
  | j, _, _, _, _, .eta Γ f A B h, hget, hvty => by
      have hf' := hasTyT_substS hcl hinst v t h hget hvty
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
  | j, _, _, _, _, .irr _ _ _ _ hP hp hq, hget, hvty => by
      have hP' := hasTyT_substS hcl hinst v t hP hget hvty
      simp only [instantiate] at hP'
      exact .irr _ _ _ _ hP' (hasTyT_substS hcl hinst v t hp hget hvty)
        (hasTyT_substS hcl hinst v t hq hget hvty)
  | j, _, _, _, _, .tyConv _ _ _ _ _ _ h hA, hget, hvty =>
      .tyConv _ _ _ _ _ _ (convT_substS hcl hinst v t h hget hvty) (convT_substS hcl hinst v t hA hget hvty)
  termination_by j Γ a b T h _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)
end

/-! ## the `EnvWf`-fronted wrappers over the structure cores -/

/-- general-`j` substitution, fronted by the old `EnvWf` entry — one line over
    the structure core. -/
def hasTyT_subst {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A → Γ[j]? = some (.assumption t) →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    HasTyT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A) :=
  hasTyT_substS (envWf_closed hE) (envWf_subst_inst hE) v t

/-- the conversion side, `EnvWf`-fronted. -/
def convT_subst {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) (v t : Expr Nat) :
    {j : Nat}→ {Γ : LCtx}→ {a b T : Expr Nat}→
      ConvT E n Γ a b T → Γ[j]? = some (.assumption t) →
      HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
      ConvT E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
        (instantiate j (lift 0 j v) T) :=
  convT_substS (envWf_closed hE) (envWf_subst_inst hE) v t

/-! ## the j = 0 front-door specialization

Substituting the head assumption: `instantiate0 v` on both sides of a typing over
`assumption t :: Γ`, given the replacement's typing at `t`. One application of
the general theorem; the lift-0 cancel and `substRemove .. 0` are definitional. -/

/-- head substitution on the typed judgment — the STRUCTURE core. -/
def hasTyT_subst0S {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {v t : Expr Nat}
    {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT E n (LocalDecl.assumption t :: Γ) e A)
    (hv : HasTyT E n Γ v t) :
    HasTyT E n Γ (instantiate0 v e) (instantiate0 v A) := by
  have h0 := hasTyT_substS hcl hinst v t (j := 0) h (by simp)
    (by rw [lift_zero, lift_zero]; exact hv)
  rw [lift_zero] at h0
  exact h0

/-- head substitution, fronted by the old `EnvWf` entry — a one-line wrapper
    over the structure core. -/
def hasTyT_subst0 {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) {v t : Expr Nat}
    {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT E n (LocalDecl.assumption t :: Γ) e A)
    (hv : HasTyT E n Γ v t) :
    HasTyT E n Γ (instantiate0 v e) (instantiate0 v A) :=
  hasTyT_subst0S (envWf_closed hE) (envWf_subst_inst hE) h hv

/-- head substitution on typed conversions — the STRUCTURE core. -/
def convT_subst0S {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {v t : Expr Nat}
    {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n (LocalDecl.assumption t :: Γ) a b T)
    (hv : HasTyT E n Γ v t) :
    ConvT E n Γ (instantiate0 v a) (instantiate0 v b) (instantiate0 v T) := by
  have h0 := convT_substS hcl hinst v t (j := 0) h (by simp)
    (by rw [lift_zero, lift_zero]; exact hv)
  rw [lift_zero] at h0
  exact h0

/-- the conversion side, `EnvWf`-fronted wrapper over the structure core. -/
def convT_subst0 {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) {v t : Expr Nat}
    {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n (LocalDecl.assumption t :: Γ) a b T)
    (hv : HasTyT E n Γ v t) :
    ConvT E n Γ (instantiate0 v a) (instantiate0 v b) (instantiate0 v T) :=
  convT_subst0S (envWf_closed hE) (envWf_subst_inst hE) h hv

end Rcic.Declarative

