import rcic.RcicTypedEnvEntry
import rcic.RcicSubstLet

/-!
# L1 — the letBinding-keyed typed substitution (DT-009 validity route)

`hasTyT_substS`/`convT_substS` (`RcicTypedSubst.lean:49`) substitute through a
context entry keyed `.assumption`; this module lands the sibling mutual keyed
`.letBinding` — the typed counterpart of the legacy `RcicSubstLet`
(`hasTySubstLet`/`convSubstLet`). The removed entry is `letBinding t w0` and the
substituted value IS the let's own stored `w0`, forced by the zetaLocal case.

THE TYPED WRINKLE IS SMALLER THAN THE LEGACY ONE: at the removed position,
`ConvT.zetaLocal` has `lookupValue Γ j = some v0` with `v0 = lift 0 (j+1) w0`
(the let's stored value read back through the bridge), and both sides
instantiate to `lift 0 j w0`. The legacy side paid `Step ⊕' Eq` for that
collapse because `Step` has no reflexivity; `ConvT` DOES — `ConvT.refl` carries
a `HasTyT` premise, and the premise `hvty` is exactly `lift 0 j w0 : lift 0 j t`
in the substituted context. NO `⊕'` is needed; the wall named in the L1 plan
does not exist on the typed root.

* `hasTyT_substLetS` / `convT_substLetS` (mutual): the structure cores,
  `EnvClosed` + `EnvMembersSubstStable` fronts exactly as substS — the same
  two structure properties suffice (`RcicTypedEnvEntry` docstring).
* `hasTyT_substLet_of_envWfT` / `convT_substLet_of_envWfT`: the general-`j`
  forms fronted by the FORMAL TYPED entry (`envClosed_of_envWfT`,
  `envMembersSubstStable_of_envWfT` — `RcicTypedEnvEntry.lean:133`).
* `hasTyT_substLet0_of_envWfT`: the `j = 0` head form L3 consumes —
  `HasTyT (letBinding t w0 :: Γ) e A` plus `w0 : t` in `Γ` gives
  `instantiate0 w0` on both sides (the `lift`-0 cancels are definitional).
-/

namespace Rcic.Declarative

/-! ## the letBinding substitution theorem, general j (mutual) -/

mutual/-- THE TYPED LET-SUBSTITUTION THEOREM: a typing over a `letBinding` at `j`,
    plus the stored value's typing at the lifted stored type in the substituted
    context, moves to the substituted context with term and type instantiated.
    Sibling of `hasTyT_substS`, keyed `letBinding` and substituting `w0`. -/
def hasTyT_substLetS {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A → Γ[j]? = some (.letBinding t w0) →
    HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    HasTyT E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) e) (instantiate j (lift 0 j w0) A)
  | j, _, _, _, .sort _ _, _, _ => by
      simp only [instantiate]; exact .sort _ _
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
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          exact .bvar _ _ _ this
  | j, _, _, _, .const Γ r ls m hres hlen hwf, hget, hvty => by
      have hm := (hinst r m hres).1 ls (lift 0 j w0) j
      simp only [instantiate]
      rw [hm]
      exact .const _ r ls m hres hlen hwf
  | j, _, _, _, .pi Γ A u B w hA hB, hget, hvty => by
      simp only [instantiate]
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hB' := hasTyT_substLetS hcl hinst t w0 (j := j + 1) hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB'
      have hA' := hasTyT_substLetS hcl hinst t w0 hA hget hvty
      simp only [instantiate] at hA'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ u _ w hA' hB'
  | j, _, _, _, .lam Γ A u body B hA hbody, hget, hvty => by
      simp only [instantiate]
      have hA' := hasTyT_substLetS hcl hinst t w0 hA hget hvty
      simp only [instantiate] at hA'
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? = some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substLetS hcl hinst t w0 (j := j + 1) hbody hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ u _ _ hA' hb'
  | j, _, _, _, .app Γ f a A B hf ha, hget, hvty => by
      have hf' := hasTyT_substLetS hcl hinst t w0 hf hget hvty
      have ha' := hasTyT_substLetS hcl hinst t w0 ha hget hvty
      simp only [instantiate] at hf'
      have h6 := instantiate_instantiate 0 j a (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ hf' ha'
  | j, _, _, _, .letE Γ A u value B body hA hv hb, hget, hvty => by
      have hA' := hasTyT_substLetS hcl hinst t w0 hA hget hvty
      simp only [instantiate] at hA'
      have hv' := hasTyT_substLetS hcl hinst t w0 hv hget hvty
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.letBinding A value :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.letBinding A value))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A value :: Γ)[j+1]? =
          some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substLetS hcl hinst t w0 (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ u _ _ _ hA' hv' hb'
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvty => by
      have hexp' := hasTyT_substLetS hcl hinst t w0 hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j w0) tl] at hexp'
      simp only [instantiate]
      exact .lit _ _ _ hexp'
  | j, _, _, _, .conv Γ e A B u h hc, hget, hvty =>
      .conv _ _ _ _ _ (hasTyT_substLetS hcl hinst t w0 h hget hvty)
        (convT_substLetS hcl hinst t w0 hc hget hvty)
  termination_by j Γ e A h _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- letBinding substitution on conversions at a fixed type — the zetaLocal
    `i = j` arm discharges by `ConvT.refl` on `hvty` (see module docstring). -/
def convT_substLetS {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (t w0 : Expr Nat) :
    {j : Nat}→ {Γ : LCtx}→ {a b T : Expr Nat}→
      ConvT E n Γ a b T → Γ[j]? = some (.letBinding t w0) →
      HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
      ConvT E n (substRemove w0 j Γ)
        (instantiate j (lift 0 j w0) a) (instantiate j (lift 0 j w0) b)
        (instantiate j (lift 0 j w0) T)
  | j, _, _, _, _, .refl _ a A h, hget, hvty =>
      .refl _ _ _ (hasTyT_substLetS hcl hinst t w0 h hget hvty)
  | j, _, _, _, _, .symm _ _ _ _ h, hget, hvty =>
      .symm _ _ _ _ (convT_substLetS hcl hinst t w0 h hget hvty)
  | j, _, _, _, _, .trans _ _ _ _ _ h1 h2, hget, hvty =>
      .trans _ _ _ _ _ (convT_substLetS hcl hinst t w0 h1 hget hvty)
        (convT_substLetS hcl hinst t w0 h2 hget hvty)
  | j, _, _, _, _, .beta Γ A body arg B u hA hbody harg, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? =
          some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substLetS hcl hinst t w0 (j := j + 1) hbody hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have hA' := hasTyT_substLetS hcl hinst t w0 hA hget hvty
      have harg' := hasTyT_substLetS hcl hinst t w0 harg hget hvty
      simp only [instantiate] at hA' harg'
      have h6 := instantiate_instantiate 0 j arg (lift 0 j w0) (by omega) body
      have h7 := instantiate_instantiate 0 j arg (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, h7]
      have hlv : lift 0 1 (lift 0 j w0) = lift 0 (j + 1) w0 :=
        lift_lift_merge (e := w0) 1 j 0 0 (by omega) (by omega)
      first
        | rw [hlv]
        | skip
      exact .beta _ _ _ _ _ _ hA' hb' harg'
  | j, _, _, _, _, .zeta Γ A value body B u hA hv hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.letBinding A value :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.letBinding A value))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A value :: Γ)[j+1]? =
          some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := hasTyT_substLetS hcl hinst t w0 (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j w0) (by omega) body
      have h7 := instantiate_instantiate 0 j value (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, h7]
      have hlv : lift 0 1 (lift 0 j w0) = lift 0 (j + 1) w0 :=
        lift_lift_merge (e := w0) 1 j 0 0 (by omega) (by omega)
      first
        | rw [hlv]
        | skip
      exact .zeta _ _ _ _ _ _
        (hasTyT_substLetS hcl hinst t w0 hA hget hvty)
        (hasTyT_substLetS hcl hinst t w0 hv hget hvty) hb'
  | j, _, _, _, _, .zetaLocal Γ i A v0 hval hty hv, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        rw [lookupValue_get_letBinding hget] at hval
        injection hval with hval
        subst hval
        rw [lookupType_get_letBinding hget] at hty
        injection hty with hty
        subst hty
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i+1) 0 i (lift 0 i w0) (by omega) (by omega),
            instantiate_lift_cancel (i+1) 0 i (lift 0 i w0) (by omega) (by omega)]
        exact .refl _ _ _ hvty
      · by_cases hlt : i < j
        · have hval' := lookupValue_substRemove_lt (v := w0) hlt hval
          have hty' := lookupType_substRemove_lt (v := w0) hlt hty
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .zetaLocal _ _ _ _ hval' hty'
            (hasTyT_substLetS hcl hinst t w0 hv hget hvty)
        · have hval' := lookupValue_substRemove_gt (v := w0) (by omega : j < i) hval
          have hty' := lookupType_substRemove_gt (v := w0) (by omega : j < i) hty
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          exact .zetaLocal _ _ _ _ hval' hty'
            (hasTyT_substLetS hcl hinst t w0 hv hget hvty)
  | j, _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb, hget, hvty => by
      have hb' := hasTyT_substLetS hcl hinst t w0 hb hget hvty
      rw [(hinst r m hres).2 b hbody ls (lift 0 j w0) j,
          (hinst r m hres).1 ls (lift 0 j w0) j] at hb'
      rw [(hinst r m hres).2 b hbody ls (lift 0 j w0) j,
          (hinst r m hres).1 ls (lift 0 j w0) j]
      exact .delta _ r ls m b hres hbody htr hlen hwf hb'
  | j, _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs, hget, hvty =>
      .iota _ _ _ _ (iotaSubst E lhs rhs h (lift 0 j w0) j)
        (hasTyT_substLetS hcl hinst t w0 hlhs hget hvty)
        (hasTyT_substLetS hcl hinst t w0 hrhs hget hvty)
  | j, _, _, _, _, .lit Γ tN exp T h hexp, hget, hvty => by
      have hexp' := hasTyT_substLetS hcl hinst t w0 hexp hget hvty
      cases h
      rw [natExpand_instantiate j (lift 0 j w0) tN] at hexp'
      simp only [instantiate]
      rw [natExpand_instantiate j (lift 0 j w0) tN]
      exact .lit _ _ _ _ (.of tN) hexp'
  | j, _, _, _, _, .app Γ f g a b A B h1 h2, hget, hvty => by
      have h6 := instantiate_instantiate 0 j a (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ _ _ (convT_substLetS hcl hinst t w0 h1 hget hvty)
        (convT_substLetS hcl hinst t w0 h2 hget hvty)
  | j, _, _, _, _, .lam Γ A A2 b1 b2 B u hA hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? =
          some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substLetS hcl hinst t w0 (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .lam _ _ _ _ _ _ _ (convT_substLetS hcl hinst t w0 hA hget hvty) hb'
  | j, _, _, _, _, .pi Γ A A2 b1 b2 u v' hA hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.assumption A :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.assumption A))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.assumption A :: Γ)[j+1]? =
          some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substLetS hcl hinst t w0 (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .pi _ _ _ _ _ _ _ (convT_substLetS hcl hinst t w0 hA hget hvty) hb'
  | j, _, _, _, _, .letE Γ A A2 vv vv2 b1 b2 B u hA hv hb, hget, hvty => by
      have hvty' :
          HasTyT E n (substRemove w0 (j+1) (LocalDecl.letBinding A vv :: Γ))
            (lift 0 (j+1) w0) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j w0 (LocalDecl.letBinding A vv))
          hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (LocalDecl.letBinding A vv :: Γ)[j+1]? =
          some (LocalDecl.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substLetS hcl hinst t w0 (j := j + 1) hb hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j vv (lift 0 j w0) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact .letE _ _ _ _ _ _ _ _ _ (convT_substLetS hcl hinst t w0 hA hget hvty)
        (convT_substLetS hcl hinst t w0 hv hget hvty) hb'
  | j, _, _, _, _, .sorts _ l1 l2 h, hget, hvty => by
      simp only [instantiate]; exact .sorts _ l1 l2 h
  | j, _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h, hget, hvty => by
      have hm := (hinst r m hres).1 ls (lift 0 j w0) j
      simp only [instantiate]
      rw [hm]
      exact .consts _ r ls ls' m hres hlen hwf hwf' h
  | j, _, _, _, _, .eta Γ f A B h, hget, hvty => by
      have hf' := hasTyT_substLetS hcl hinst t w0 h hget hvty
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
  | j, _, _, _, _, .irr _ _ _ _ hP hp hq, hget, hvty => by
      have hP' := hasTyT_substLetS hcl hinst t w0 hP hget hvty
      simp only [instantiate] at hP'
      exact .irr _ _ _ _ hP' (hasTyT_substLetS hcl hinst t w0 hp hget hvty)
        (hasTyT_substLetS hcl hinst t w0 hq hget hvty)
  | j, _, _, _, _, .tyConv _ _ _ _ _ _ h hA, hget, hvty =>
      .tyConv _ _ _ _ _ _ (convT_substLetS hcl hinst t w0 h hget hvty)
        (convT_substLetS hcl hinst t w0 hA hget hvty)
  termination_by j Γ a b T h _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)
end

/-! ## the `EnvWfT`-fronted wrappers over the structure cores -/

/-- general-`j` letBinding substitution, fronted by the FORMAL TYPED entry —
    one line over the structure core, fronts `envClosed_of_envWfT` /
    `envMembersSubstStable_of_envWfT`. -/
def hasTyT_substLet_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A → Γ[j]? = some (.letBinding t w0) →
    HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    HasTyT E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) e) (instantiate j (lift 0 j w0) A) :=
  hasTyT_substLetS (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) t w0

/-- the conversion side, typed-entry-fronted. -/
def convT_substLet_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (t w0 : Expr Nat) :
    {j : Nat}→ {Γ : LCtx}→ {a b T : Expr Nat}→
      ConvT E n Γ a b T → Γ[j]? = some (.letBinding t w0) →
      HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
      ConvT E n (substRemove w0 j Γ)
        (instantiate j (lift 0 j w0) a) (instantiate j (lift 0 j w0) b)
        (instantiate j (lift 0 j w0) T) :=
  convT_substLetS (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) t w0

/-- head letBinding substitution — removing `letBinding t w0` from position 0:
    `instantiate0 w0` on both sides of a typing over `letBinding t w0 :: Γ`,
    given `w0`'s typing at `t` in the smaller context. The `j = 0`
    specialization; `substRemove w0 0` and the `lift`-0s are definitional. -/
def hasTyT_substLet0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {t w0 : Expr Nat} {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT E n (LocalDecl.letBinding t w0 :: Γ) e A)
    (hv : HasTyT E n Γ w0 t) :
    HasTyT E n Γ (instantiate0 w0 e) (instantiate0 w0 A) := by
  have h0 := hasTyT_substLetS (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) t w0 (j := 0) h (by simp)
    (by rw [lift_zero, lift_zero]; exact hv)
  rw [lift_zero] at h0
  exact h0

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyT_substLetS
#print axioms Rcic.Declarative.convT_substLetS
#print axioms Rcic.Declarative.hasTyT_substLet_of_envWfT
#print axioms Rcic.Declarative.convT_substLet_of_envWfT
#print axioms Rcic.Declarative.hasTyT_substLet0_of_envWfT
