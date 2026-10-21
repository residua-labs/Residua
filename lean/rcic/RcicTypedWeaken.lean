import rcic.RcicWeaken

/-!
# M3-b GLM-2 — typed weakening (the substitution module's first half)

The typed analog of `RcicWeaken.hasTyWeaken` / `convWeaken`, on the LANDED typed
judgment (`HasTyT` / `ConvT`, single-owned in `RcicDeclarative` since the GLM-2
root landing). Every case follows the raw template verbatim (`simp only [lift]`,
`lift_instantiate_low` under app/beta/zeta conclusions, `lift_lift_permute` in eta,
`insertAt_succ_cons`/`liftDecl` under binders, `natExpand_lift` at lit); the
const/consts/delta cases read the member-type closedness from `EnvClosed` (the
lift form; `envWf_closed` discharges it from `EnvWf`).

`hasTyTWeaken` + `convTWeaken` are mutual (the `conv` typing case carries a
conversion). No row premises, no annotation, no bridge; judgments Type-valued.
The substitution pair (`hasTyT_subst`/`convT_subst`) consumes this lemma under
binders — its draft and fix list are in `research/rcic/rows-m1/drafts/`.
-/

namespace Rcic.Declarative

mutual
/-- one-declaration weakening on the typed judgment — the analog of
    `RcicWeaken.hasTyWeaken`. -/
def hasTyTWeaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) :
    {c : Nat} → {Γ : LCtx}→ {e A : Expr Nat} →
      HasTyT E n Γ e A → HasTyT E n (insertAt d c Γ) (lift c 1 e) (lift c 1 A)
  | c, _, _, _, .sort Γ l => by
      simp only [lift]; exact .sort _ l
  | c, _, _, _, .bvar Γ i A h => by
      by_cases hic : i < c
      · have hl := lookupType_insertAt_lt d hic h
        simp only [lift, if_neg (by omega : ¬ c ≤ i)]
        exact .bvar _ _ _ hl
      · have hl := lookupType_insertAt_ge d (by omega : c ≤ i) h
        simp only [lift, if_pos (by omega : c ≤ i)]
        exact .bvar _ _ _ hl
  | c, _, _, _, .const Γ r ls m hres hlen hwf => by
      have hm := (hcl r m hres).1 c
      simp only [lift, lift_instantiateLevels]
      rw [hm]
      exact .const _ r ls m hres hlen hwf
  | c, _, _, _, .pi Γ A u B v hA hB => by
      simp only [lift]
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl, lift] at hB'
      have hA' := hasTyTWeaken d hcl (c := c) hA
      simp only [lift] at hA'
      exact .pi _ _ u _ v hA' hB'
  | c, _, _, _, .lam Γ A u body B hA hbody => by
      simp only [lift]
      have hA' := hasTyTWeaken d hcl (c := c) hA
      simp only [lift] at hA'
      have hb' := hasTyTWeaken d hcl (c := c + 1) hbody
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .lam _ _ u _ _ hA' hb'
  | c, _, _, _, .app Γ f a A B hf ha => by
      have hf' := hasTyTWeaken d hcl (c := c) hf
      have ha' := hasTyTWeaken d hcl (c := c) ha
      simp only [lift] at hf'
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      simp only [lift, instantiate0]
      rw [h]
      exact .app _ _ _ _ _ hf' ha'
  | c, _, _, _, .letE Γ A u value B body hA hv hb => by
      have hA' := hasTyTWeaken d hcl (c := c) hA
      simp only [lift] at hA'
      have hv' := hasTyTWeaken d hcl (c := c) hv
      have hb' := hasTyTWeaken d hcl (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      simp only [lift, instantiate0]
      rw [h]
      exact .letE _ _ u _ _ _ hA' hv' hb'
  | c, _, _, _, .conv Γ e A B u h hA =>
      .conv _ _ _ _ u (hasTyTWeaken d hcl h) (convTWeaken d hcl hA)
  | c, _, _, _, .lit Γ t T hexp => by
      have hexp' := hasTyTWeaken d hcl (c := c) hexp
      rw [natExpand_lift c 1 t] at hexp'
      simp only [lift]
      exact .lit _ _ _ hexp'

/-- one-declaration weakening on conversions at a fixed type — the analog of
    `RcicWeaken.convWeaken`. -/
def convTWeaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) :
    {c : Nat}→ {Γ : LCtx} → {a b T : Expr Nat} →
      ConvT E n Γ a b T →
      ConvT E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | c, _, _, _, _, .refl Γ a A h => .refl _ _ _ (hasTyTWeaken d hcl h)
  | c, _, _, _, _, .symm Γ a b A h => .symm _ _ _ _ (convTWeaken d hcl h)
  | c, _, _, _, _, .trans Γ a b b' A h1 h2 =>
      .trans _ _ _ _ _ (convTWeaken d hcl h1) (convTWeaken d hcl h2)
  | c, _, _, _, _, .beta Γ A body arg B u hA hbody harg => by
      have hA' := hasTyTWeaken d hcl (c := c) hA
      simp only [lift] at hA'
      have hb' := hasTyTWeaken d hcl (c := c + 1) hbody
      simp only [insertAt_succ_cons, liftDecl] at hb'
      have hg' := hasTyTWeaken d hcl (c := c) harg
      simp only [lift] at hg'
      have h := lift_instantiate_low 1 c 0 arg (by omega) B
      have h2 := lift_instantiate_low 1 c 0 arg (by omega) body
      simp only [lift, instantiate0]
      rw [h, h2]
      exact .beta _ _ _ _ _ _ hA' hb' hg'
  | c, _, _, _, _, .zeta Γ A value body B u hA hv hb => by
      have hA' := hasTyTWeaken d hcl (c := c) hA
      simp only [lift] at hA'
      have hv' := hasTyTWeaken d hcl (c := c) hv
      simp only [lift] at hv'
      have hb' := hasTyTWeaken d hcl (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      have h2 := lift_instantiate_low 1 c 0 value (by omega) body
      simp only [lift, instantiate0]
      rw [h, h2]
      exact .zeta _ _ _ _ _ _ hA' hv' hb'
  | c, _, _, _, _, .zetaLocal Γ i A v hval hty hv => by
      by_cases hic : i < c
      · simp only [lift, if_neg (by omega : ¬ c ≤ i)]
        exact .zetaLocal _ _ _ _
          (lookupValue_insertAt_lt d hic hval) (lookupType_insertAt_lt d hic hty)
          (hasTyTWeaken d hcl hv)
      · simp only [lift, if_pos (by omega : c ≤ i)]
        exact .zetaLocal _ _ _ _
          (lookupValue_insertAt_ge d (by omega : c ≤ i) hval)
          (lookupType_insertAt_ge d (by omega : c ≤ i) hty)
          (hasTyTWeaken d hcl hv)
  | c, _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb => by
      have hbc : lift c 1 b = b := (hcl r m hres).2 b hbody c
      have hmt : lift c 1 m.mtype = m.mtype := (hcl r m hres).1 c
      have hb' := hasTyTWeaken d hcl (c := c) hb
      simp only [lift_instantiateLevels, hbc, hmt] at hb'
      simp only [lift, lift_instantiateLevels, hmt, hbc]
      exact .delta _ r ls m b hres hbody htr hlen hwf hb'
  | c, _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota _ _ _ _ (iotaLift E lhs rhs h c)
        (hasTyTWeaken d hcl hlhs) (hasTyTWeaken d hcl hrhs)
  | c, _, _, _, _, .lit Γ t exp T h hexp =>
      .lit _ _ _ _ (litLift t exp h c) (hasTyTWeaken d hcl hexp)
  | c, _, _, _, _, .app Γ f g a b A B h1 h2 => by
      have h1' := convTWeaken d hcl (c := c) h1
      simp only [lift] at h1'
      have h2' := convTWeaken d hcl (c := c) h2
      simp only [lift] at h2'
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      simp only [lift, instantiate0]
      rw [h]
      exact .app _ _ _ _ _ _ _ h1' h2'
  | c, _, _, _, _, .lam Γ A A' b b' B u hA hb => by
      simp only [lift]
      have hb' := convTWeaken d hcl (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .lam _ _ _ _ _ _ u (convTWeaken d hcl hA) hb'
  | c, _, _, _, _, .pi Γ A A' B B' u v hA hB => by
      simp only [lift]
      have hB' := convTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      exact .pi _ _ _ _ _ u v (convTWeaken d hcl hA) hB'
  | c, _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb => by
      have hb' := convTWeaken d hcl (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      have h := lift_instantiate_low 1 c 0 v (by omega) B
      simp only [lift, instantiate0]
      rw [h]
      exact .letE _ _ _ _ _ _ _ _ u (convTWeaken d hcl hA) (convTWeaken d hcl hv) hb'
  | c, _, _, _, _, .sorts Γ l1 l2 h => .sorts _ _ _ h
  | c, _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h => by
      simp only [lift, lift_instantiateLevels]
      rw [(hcl r m hres).1 c]
      exact .consts _ r ls ls' m hres hlen hwf hwf' h
  | c, _, _, _, _, .eta Γ f A B h => by
      have hf' := hasTyTWeaken d hcl (c := c) h
      simp only [lift] at hf' ⊢
      have hp : lift (c+1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [lift_lift_permute 1 1 c 0 (by omega),
            show 1 + c = c + 1 from by omega]
      rw [show (if c + 1 ≤ 0 then Expr.bvar (0+1) else Expr.bvar 0) = Expr.bvar 0
            from by simp, hp]
      exact .eta _ _ _ _ hf'
  | c, _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr _ _ _ _ (hasTyTWeaken d hcl hP) (hasTyTWeaken d hcl hp)
        (hasTyTWeaken d hcl hq)
  | c, _, _, _, _, .tyConv Γ a b A A' u h hA =>
      .tyConv _ _ _ _ _ _ (convTWeaken d hcl h) (convTWeaken d hcl hA)
end

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyTWeaken
#print axioms Rcic.Declarative.convTWeaken
