/-
RCIC let-substitution construction — the letBinding-removal mirror of
RcicSubst, unblocking DT-006 and the zeta arm of subject reduction
(DT-010). Same context operation (substRemove/instDecl are already
decl-agnostic), same six transport premises, same lookup laws (they
never inspect the removed position). The removed entry is a
letBinding t w0 and the substituted value IS the let's own stored
value w0 — forced by the zetaLocal case.

THE WRINKLE (derived before building, not discovered mid-build):
at the removed position, zetaLocal steps `bvar j → lift 0 (j+1) w0`,
and BOTH sides substitute to `lift 0 j w0` — equal, and Step has no
refl. So `stepSubstLet` returns `Step ... ⊕' Eq`, and the Conv layer
absorbs the Eq arm with `.refl` — which is exactly why Conv (not Step)
is the right consumer of substituted steps.

INFRASTRUCTURE (M-010): DT-006's interface statement remains the
batch's — at j = 0 the typing premise collapses to
`HasTy E n Γ w0 t`, the textbook let-value typing.
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc
import rcic.RcicCtxMorph
import rcic.RcicWeaken
import rcic.RcicSubst
import rcic.RcicEnv
import rcic.RcicIota

namespace Rcic.Declarative

/-- get?-to-lookup bridge: a letBinding entry yields its stored type. -/
theorem lookupType_get_letBinding {Γ : LCtx} {j : Nat} {t w0 : Expr Nat}
    (h : Γ[j]? = some (.letBinding t w0)) :
    lookupType Γ j = some (lift 0 (j+1) t) := by
  simp [lookupType, h]

/-- get?-to-lookup bridge: a letBinding entry yields its stored value. -/
theorem lookupValue_get_letBinding {Γ : LCtx} {j : Nat} {t w0 : Expr Nat}
    (h : Γ[j]? = some (.letBinding t w0)) :
    lookupValue Γ j = some (lift 0 (j+1) w0) := by
  simp [lookupValue, h]

mutual

def stepSubstLet {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    Step E n Γ a b →
    Γ[j]? = some (.letBinding t w0) →
    HasTy E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    (Step E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) a) (instantiate j (lift 0 j w0) b)) ⊕'
    (instantiate j (lift 0 j w0) a = instantiate j (lift 0 j w0) b)
  | j, _, _, _, .beta Γ A body arg, hget, hvty => by
      have h6 := instantiate_instantiate 0 j arg (lift 0 j w0) (by omega) body
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .inl (.beta _ _ _ _)
  | j, _, _, _, .zeta Γ A value body, hget, hvty => by
      have h6 := instantiate_instantiate 0 j value (lift 0 j w0) (by omega) body
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .inl (.zeta _ _ _ _)
  | j, _, _, _, .zetaLocal Γ i v0 hvl, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        rw [lookupValue_get_letBinding hget] at hvl
        injection hvl with hvl
        subst hvl
        refine .inr ?_
        simp only [instantiate, if_true]
        rw [instantiate_lift_cancel (i+1) 0 i (lift 0 i w0) (by omega) (by omega),
            Nat.add_sub_cancel]
      · by_cases hlt : i < j
        · have := lookupValue_substRemove_lt (v := w0) hlt hvl
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .inl (.zetaLocal _ _ _ this)
        · have := lookupValue_substRemove_gt (v := w0) (by omega : j < i) hvl
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i)]
          exact .inl (.zetaLocal _ _ _ this)
  | j, _, _, _, .delta Γ r ls m b hres hbody htr, hget, hvty => by
      -- 00 §20.6: the conclusion index is now `instantiateLevels ls b`.
      have hb := (envWf_subst_inst hE r m hres).2 b hbody ls (lift 0 j w0) j
      simp only [instantiate]
      rw [hb]
      exact .inl (.delta _ r ls m b hres hbody htr)
  | j, _, _, _, .iota Γ lhs rhs h, hget, hvty => by
      exact .inl (.iota _ _ _ (iotaSubst E lhs rhs h (lift 0 j w0) j))
  | j, _, _, _, .lit Γ tl exp h, hget, hvty => by
      simp only [instantiate]
      exact .inl (.lit _ _ _ (litSubst tl exp h (lift 0 j w0) j))

def convSubstLet {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    Conv E n Γ a b →
    Γ[j]? = some (.letBinding t w0) →
    HasTy E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    Conv E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) a) (instantiate j (lift 0 j w0) b)
  | j, _, _, _, .refl _ a, hget, hvty => .refl _ _
  | j, _, _, _, .symm _ _ _ h, hget, hvty =>
      .symm _ _ _ (convSubstLet hE t w0 h hget hvty)
  | j, _, _, _, .trans _ _ _ _ h1 h2, hget, hvty =>
      .trans _ _ _ _ (convSubstLet hE t w0 h1 hget hvty)
        (convSubstLet hE t w0 h2 hget hvty)
  | j, _, _, _, .step _ _ _ hs, hget, hvty =>
      match stepSubstLet hE t w0 hs hget hvty with
      | .inl s => .step _ _ _ s
      | .inr eq => by rw [← eq]; exact .refl _ _
  | j, _, _, _, .app _ _ _ _ _ h1 h2, hget, hvty => by
      simp only [instantiate]
      exact .app _ _ _ _ _ (convSubstLet hE t w0 h1 hget hvty)
        (convSubstLet hE t w0 h2 hget hvty)
  | j, _, _, _, .lam Γ A A2 b1 b2 hA hb, hget, hvty => by
      have hvty' :
          HasTy E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j w0 (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convSubstLet hE t w0
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ _ _ _ (convSubstLet hE t w0 hA hget hvty) hb'
  | j, _, _, _, .pi Γ A A2 b1 b2 hA hb, hget, hvty => by
      have hvty' :
          HasTy E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j w0 (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convSubstLet hE t w0
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ _ _ _ (convSubstLet hE t w0 hA hget hvty) hb'
  | j, _, _, _, .letE Γ A A2 vv vv2 b1 b2 hA hv hb, hget, hvty => by
      have hvty' :
          HasTy E n (substRemove w0 (j+1) (LocalDecl.letBinding A vv :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j w0 (LocalDecl.letBinding A vv))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A vv :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convSubstLet hE t w0
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ _ _ _ _ _ (convSubstLet hE t w0 hA hget hvty)
        (convSubstLet hE t w0 hv hget hvty) hb'
  | j, _, _, _, .sorts _ l1 l2 h, hget, hvty => by
      simp only [instantiate]; exact .sorts _ l1 l2 h
  | j, _, _, _, .consts _ r ls ls' h, hget, hvty => by
      simp only [instantiate]; exact .consts _ r ls ls' h
  | j, _, _, _, .eta _ f A B hh, hget, hvty => by
      have hf' := hasTySubstLet hE t w0 (j := j) hh hget hvty
      simp only [instantiate] at hf' ⊢
      have hp : instantiate (j+1) (lift 0 1 (lift 0 j w0)) (lift 0 1 f) =
          lift 0 1 (instantiate j (lift 0 j w0) f) := by
        rw [lift_instantiate_high 1 0 j (lift 0 j w0) (by omega),
            show 1 + j = j + 1 from by omega]
      rw [show (if (0 : Nat) = j + 1 then lift 0 1 (lift 0 j w0)
            else if j + 1 < 0 then Expr.bvar (0-1) else Expr.bvar 0) = Expr.bvar 0
            from by rw [if_neg (by omega : ¬ (0:Nat) = j + 1),
                        if_neg (by omega : ¬ j + 1 < 0)], hp]
      exact .eta _ _ _ _ hf'
  | j, _, _, _, .irr _ P p q hP hp hq, hget, hvty => by
      have hP' := hasTySubstLet hE t w0 hP hget hvty
      simp only [instantiate] at hP'
      exact .irr _ _ _ _ hP' (hasTySubstLet hE t w0 hp hget hvty)
        (hasTySubstLet hE t w0 hq hget hvty)

def hasTySubstLet {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n)
    (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTy E n Γ e A →
    Γ[j]? = some (.letBinding t w0) →
    HasTy E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    HasTy E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) e) (instantiate j (lift 0 j w0) A)
  | j, _, _, _, .sort Γ l, hget, hvty => by
      simp only [instantiate]; exact .sort _ l
  | j, _, _, _, .bvar Γ i A h, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        rw [lookupType_get_letBinding hget] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i+1) 0 i (lift 0 i w0) (by omega) (by omega)]
        exact hvty
      · by_cases hlt : i < j
        · have := lookupType_substRemove_lt (v := w0) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .bvar _ _ _ this
        · have := lookupType_substRemove_gt (v := w0) (by omega : j < i) h
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i)]
          exact .bvar _ _ _ this
  | j, _, _, _, .const Γ r ls m hres hlen hwf, hget, hvty => by
      -- 00 §20.6: the ascribed type is now `instantiateLevels ls m.mtype`.
      have hm := (envWf_subst_inst hE r m hres).1 ls (lift 0 j w0) j
      simp only [instantiate]
      rw [hm]
      exact .const _ r ls m hres hlen hwf
  | j, _, _, _, .pi Γ A u B w hA hB, hget, hvty => by
      simp only [instantiate]
      have hvty' :
          HasTy E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j w0 (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hB' := hasTySubstLet hE t w0
        (j := j + 1) hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB'
      have hA' := hasTySubstLet hE t w0 hA hget hvty
      simp only [instantiate] at hA'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ u _ w hA' hB'
  | j, _, _, _, .lam Γ A u body B hA hbody, hget, hvty => by
      simp only [instantiate]
      have hA' := hasTySubstLet hE t w0 hA hget hvty
      simp only [instantiate] at hA'
      have hvty' :
          HasTy E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j w0 (LocalDecl.assumption A))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTySubstLet hE t w0
        (j := j + 1) hbody hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ u _ _ hA' hb'
  | j, _, _, _, .app Γ f a A B hf ha, hget, hvty => by
      have hf' := hasTySubstLet hE t w0 hf hget hvty
      have ha' := hasTySubstLet hE t w0 ha hget hvty
      simp only [instantiate] at hf'
      have h6 := instantiate_instantiate 0 j a (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ hf' ha'
  | j, _, _, _, .letE Γ A u value B hA hv hb, hget, hvty => by
      have hA' := hasTySubstLet hE t w0 hA hget hvty
      simp only [instantiate] at hA'
      have hv' := hasTySubstLet hE t w0 hv hget hvty
      have hvty' :
          HasTy E n (substRemove w0 (j+1) (LocalDecl.letBinding A value :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyWeaken (instDecl j w0 (LocalDecl.letBinding A value))
          hE (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A value :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTySubstLet hE t w0
        (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ u _ _ hA' hv' hb'
  | j, _, _, _, .conv Γ e A B h hc, hget, hvty => by
      exact .conv _ _ _ _ (hasTySubstLet hE t w0 h hget hvty)
        (convSubstLet hE t w0 hc hget hvty)
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvty => by
      have hexp' := hasTySubstLet hE t w0 hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j w0) tl] at hexp'
      simp only [instantiate]
      exact .lit _ _ _ hexp'

end

end Rcic.Declarative
