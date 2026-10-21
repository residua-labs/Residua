import rcic.RcicNativeValleyAssemble
import rcic.RcicIARecIH

/-!
# RcicNativeValleySubst — the one-step certified mixed substitution at a hole
(Wall 1, `NativeConvValleys`, piece 8: `CertSubst0`, and `CertSubstLet`)

The landed `parRedT_subst` (`RcicParRedTSubst.lean`) packages the mixed substitution
`a[v] ⇒ b[v']` as a TWO-step star (`substSame` then `subst_arg`) because the K node's reduct is
rigid in its witness. Certified steps are K-free (`Certified.noK`), so for them the classical
ONE-step lemma holds; this module is that lemma, as a recursion on the certificate:

* `csubst_arg` — the mixed step of a TERM over its typing derivation (`e[v] ⇒ e[v']` at `T[v]`),
  the certified twin of `parRedT_subst_arg`; the hole is hit by the stepping pair itself;
* `csubstMixed` — the mixed step of a certified step (`a[v] ⇒ b[v']` at `T[v]`), the arms of the
  landed `parRedT_substSame` with the value pair, `refl` leaves delegating to `csubst_arg`, the
  `peq` leaf re-formed by the leaf interface (`LeafIface.ofIrr`) at the substituted `Prop`.

Two uniformities replace the landed `hTC` (the generic back-lift) everywhere:

* every node's certificate is `convT_substS` (same value) followed by `convT_substCongr`
  (the landed `ConvT` substitution congruence, `RcicIARecIH.lean`) on the node's right-endpoint
  typing — `mixedCert`;
* every substituted right-endpoint typing `b[v'] : T[v]` is an endpoint of that congruence
  (`convEnds`, i.e. `endpoints3_of_envWfT`) — `mixedRight`.

The stepping pair is kept BELOW the hole (`hvw₀ : CStep (Γ.drop (j+1)) v v' t`), unchanged under
binders, and lifted into the substituted context on demand by the certified prefix weakening
(`subst_hvw_of_drop`, the twin of the landed `subst_hvty_of_drop`).

The hole is abstract (`Hole`): position `j` holds the hole type as an ASSUMPTION or as a `let`
storing the hole value itself. The landed same-value transports of the two kinds are read
through it (`Hole.tySubst`, `Hole.convSubst`, `Hole.tyConvSubst`), the two-value congruence
is written once over it (`Hole.substCongr`; the landed `convT_substCongr` is its `assump`
instance), and the recursion is written once: the let kind differs in exactly ONE arm, the
`bvarZeta` hit at the hole, where the let variable unfolds to a reduct of the hole value and the
output is the lifted stored value's own step.

`certSubst0_of` discharges `CertSubst0` (`RcicNativeValleyRows`) — the `beta × beta` row's
input (`row_beta_beta`) — and `certSubstLet_of` discharges `CertSubstLet` (the `let` rows'
input, `RcicNativeValleyLet`), both under `EnvWfT` and leaf weakening.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the hole -/

/-- The substitution hole: position `j` of `Γ` holds the hole type `t`, as an assumption or as
    a `let` whose stored value is the hole value `v` itself. The landed same-value transports of
    both kinds (`hasTyT_substS` / `hasTyT_substLetS`, `convT_substS` / `convT_substLetS`,
    `tyConvT_substS` / `tyConvT_substLetS`) are read through it, so the mixed-substitution
    recursion below is written once. -/
inductive Hole (t v : Expr Nat) : Nat → LCtx → Type
  | assump {j : Nat} {Γ : LCtx} (h : Γ[j]? = some (.assumption t)) : Hole t v j Γ
  | letB {j : Nat} {Γ : LCtx} (h : Γ[j]? = some (.letBinding t v)) : Hole t v j Γ

namespace Hole
variable {t v : Expr Nat}

/-- The hole is inside the context. -/
theorem lt : {j : Nat} → {Γ : LCtx} → Hole t v j Γ → j < Γ.length
  | _, _, .assump h => (List.getElem?_eq_some_iff.mp h).1
  | _, _, .letB h => (List.getElem?_eq_some_iff.mp h).1

/-- The hole variable's type is the lifted hole type. -/
theorem lookupTy : {j : Nat} → {Γ : LCtx} → Hole t v j Γ →
    lookupType Γ j = some (lift 0 (j + 1) t)
  | _, _, .assump h => lookupType_get_assumption h
  | _, _, .letB h => lookupType_get_letBinding h

/-- The hole under one more binder. -/
def succ (d : LocalDecl) : {j : Nat} → {Γ : LCtx} → Hole t v j Γ → Hole t v (j + 1) (d :: Γ)
  | _, _, .assump h => .assump (by rw [List.getElem?_cons_succ]; exact h)
  | _, _, .letB h => .letB (by rw [List.getElem?_cons_succ]; exact h)

/-- The hole seen from below a prefix of `k ≤ j` declarations. -/
def drop {j : Nat} {Γ : LCtx} (k : Nat) (hk : k ≤ j) : Hole t v j Γ → Hole t v (j - k) (Γ.drop k)
  | .assump h => .assump (by
      rw [← List.get?_eq_getElem?, get?_drop, show j - k + k = j from by omega,
        List.get?_eq_getElem?]
      exact h)
  | .letB h => .letB (by
      rw [← List.get?_eq_getElem?, get?_drop, show j - k + k = j from by omega,
        List.get?_eq_getElem?]
      exact h)

/-- Same-value substitution of a typing through the hole (`hasTyT_substS` /
    `hasTyT_substLetS`). -/
def tySubst (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {j : Nat} → {Γ : LCtx} → Hole t v j Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    HasTyT E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)
  | _, _, .assump h, _, _, he, hvty => hasTyT_substS hcl hinst v t he h hvty
  | _, _, .letB h, _, _, he, hvty => hasTyT_substLetS hcl hinst t v he h hvty

/-- Same-value substitution of a conversion through the hole (`convT_substS` /
    `convT_substLetS`). -/
def convSubst (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {j : Nat} → {Γ : LCtx} → Hole t v j Γ → {a b T : Expr Nat} → ConvT E n Γ a b T →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T)
  | _, _, .assump h, _, _, _, c, hvty => convT_substS hcl hinst v t c h hvty
  | _, _, .letB h, _, _, _, c, hvty => convT_substLetS hcl hinst t v c h hvty

/-- Same-value substitution of a type-conversion chain through the hole (`tyConvT_substS` /
    `tyConvT_substLetS`). -/
def tyConvSubst (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {j : Nat} → {Γ : LCtx} → Hole t v j Γ → {A A' : Expr Nat} → TyConvT E n Γ A A' →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    TyConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (instantiate j (lift 0 j v) A')
  | _, _, .assump h, _, _, c, hvty => tyConvT_substS hcl hinst v t c h hvty
  | _, _, .letB h, _, _, c, hvty => tyConvT_substLetS hcl hinst t v c h hvty

/-- The substituted context stays well-formed under a pushed assumption (the landed
    `subst_arg_wf_assump`, through the hole). -/
def wfAssump (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {j : Nat} {Γ : LCtx}
    (H : Hole t v j Γ) {A : Expr Nat} {u : Level}
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) (hA : HasTyT E n Γ A (.sort u)) :
    CtxWfT E n (substRemove v (j + 1) (.assumption A :: Γ)) := by
  have hA' := H.tySubst hcl hinst hA hvty
  rw [substRemove_succ_cons, instDecl]
  exact .assumption _ _ _ hΓ'wf hA'

/-- The substituted context stays well-formed under a pushed `let` (the landed
    `subst_arg_wf_let`, through the hole). -/
def wfLet (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {j : Nat} {Γ : LCtx}
    (H : Hole t v j Γ) {A w : Expr Nat} {u : Level}
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) (hA : HasTyT E n Γ A (.sort u))
    (hw : HasTyT E n Γ w A) :
    CtxWfT E n (substRemove v (j + 1) (.letBinding A w :: Γ)) := by
  have hA' := H.tySubst hcl hinst hA hvty
  have hw' := H.tySubst hcl hinst hw hvty
  rw [substRemove_succ_cons, instDecl]
  exact .letBinding _ _ _ _ hΓ'wf hA' hw'

/-- The two-value substitution congruence through the hole: `e[v] ~ e[v']` at `T[v]` from
    `v ~ v'`, for every typing derivation of `e`. The landed `convT_substCongr`
    (`RcicIARecIH.lean`) is the `assump` instance; the recursion is written once over the hole
    (the hit reads `lookupTy`, the binders push the hole by `succ`). -/
def substCongr (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {v' : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → Hole t v j Γ → {e T : Expr Nat} → HasTyT E n Γ e T →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    ConvT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j v') (lift 0 j t) →
    ConvT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v') e)
      (instantiate j (lift 0 j v) T)
  | _, _, _, _, _, .sort _ _, _, _ => by
      simp only [instantiate]; exact .refl _ _ _ (.sort _ _)
  | j, _, H, _, _, .bvar _ i A h, _, hcv => by
      by_cases hij : i = j
      · subst hij
        rw [H.lookupTy] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i v) (by omega) (by omega)]
        exact hcv
      · by_cases hlt : i < j
        · have hl := lookupType_substRemove_lt (v := v) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .refl _ _ _ (.bvar _ _ _ hl)
        · have hg := lookupType_substRemove_gt (v := v) (by omega : j < i) h
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          exact .refl _ _ _ (.bvar _ _ _ hg)
  | j, _, _, _, _, .const _ r ls m hres hlen hwf, _, _ => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact .refl _ _ _ (.const _ _ _ _ hres hlen hwf)
  | j, Γ₀, H, _, _, .pi _ A u B w hA hB, hvty, hcv => by
      simp only [instantiate]
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hcv' :
          ConvT E n (substRemove v (j + 1) (.assumption A :: Γ₀))
            (lift 0 (j + 1) v) (lift 0 (j + 1) v') (lift 0 (j + 1) t) := by
        have h0 := convTWeaken (instDecl j v (.assumption A)) hcl (c := 0) hcv
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hB' := substCongr hcl hinst (H.succ (.assumption A)) hB hvty' hcv'
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB'
      have hA' := substCongr hcl hinst H hA hvty hcv
      simp only [instantiate] at hA'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v),
          lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v')]
      exact .pi _ _ _ _ _ u w hA' hB'
  | j, Γ₀, H, _, _, .lam _ A u body B hA hbody, hvty, hcv => by
      simp only [instantiate]
      have hA' := substCongr hcl hinst H hA hvty hcv
      simp only [instantiate] at hA'
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hcv' :
          ConvT E n (substRemove v (j + 1) (.assumption A :: Γ₀))
            (lift 0 (j + 1) v) (lift 0 (j + 1) v') (lift 0 (j + 1) t) := by
        have h0 := convTWeaken (instDecl j v (.assumption A)) hcl (c := 0) hcv
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hb' := substCongr hcl hinst (H.succ (.assumption A)) hbody hvty' hcv'
      simp only [substRemove_succ_cons, instDecl] at hb'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v),
          lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v')]
      exact .lam _ _ _ _ _ _ u hA' hb'
  | j, _, H, _, _, .app _ f a A B hf ha, hvty, hcv => by
      have hf' := substCongr hcl hinst H hf hvty hcv
      have ha' := substCongr hcl hinst H ha hvty hcv
      simp only [instantiate] at hf'
      have h6 := instantiate_instantiate 0 j a (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ _ _ hf' ha'
  | j, Γ₀, H, _, _, .letE _ A u value B body hA hv hb, hvty, hcv => by
      have hA' := substCongr hcl hinst H hA hvty hcv
      simp only [instantiate] at hA'
      have hv' := substCongr hcl hinst H hv hvty hcv
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hcv' :
          ConvT E n (substRemove v (j + 1) (.letBinding A value :: Γ₀))
            (lift 0 (j + 1) v) (lift 0 (j + 1) v') (lift 0 (j + 1) t) := by
        have h0 := convTWeaken (instDecl j v (.letBinding A value)) hcl (c := 0) hcv
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hb' := substCongr hcl hinst (H.succ (.letBinding A value)) hb hvty' hcv'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v),
          lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v')]
      exact .letE _ _ _ _ _ _ _ _ u hA' hv' hb'
  | j, _, H, _, _, .lit _ tl _ hexp, hvty, _ => by
      have hexp' := H.tySubst hcl hinst hexp hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      simp only [instantiate]
      exact .refl _ _ _ (.lit _ _ _ hexp')
  | _, _, H, _, _, .conv _ e A B u h hc, hvty, hcv =>
      .tyConv _ _ _ _ _ u (substCongr hcl hinst H h hvty hcv) (H.convSubst hcl hinst hc hvty)
  termination_by j Γ _ e T he _ _ => sizeOf he
  decreasing_by all_goals (simp; omega)

end Hole

/-! ### the pair below the hole, lifted on demand -/

/-- The stepping pair, typed below the hole, lifted into the substituted context (the
    certified twin of `subst_hvty_of_drop`). -/
def subst_hvw_of_drop (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    {v v' t : Expr Nat} {j : Nat} {Γ : LCtx} (H : Hole t v j Γ)
    (hvw₀ : CStep E n PEq (Γ.drop (j + 1)) v v' t) :
    CStep E n PEq (substRemove v j Γ) (lift 0 j v) (lift 0 j v') (lift 0 j t) := by
  have hlt : j < Γ.length := H.lt
  have h1 : (substRemove v j Γ).drop j = Γ.drop (j + 1) := by
    rw [substRemove_drop, if_pos (Nat.le_refl j), Nat.sub_self]
    have hd : substRemove v 0 (Γ.drop j) = (Γ.drop j).drop 1 := by
      cases Γ.drop j <;> simp [substRemove]
    rw [hd, List.drop_drop]
  have hsplit : substRemove v j Γ =
      (substRemove v j Γ).take j ++ Γ.drop (j + 1) := by
    have hs := (List.take_append_drop j (substRemove v j Γ)).symm
    rw [h1] at hs
    exact hs
  have htake : ((substRemove v j Γ).take j).length = j := by
    rw [List.length_take, substRemove_length, if_pos hlt]
    omega
  have hwk := cstep_lift_lctx hcl hPEqL ((substRemove v j Γ).take j) hvw₀
  rw [htake] at hwk
  rw [hsplit]
  exact hwk

/-! ### the two uniformities -/

/-- The certificate of a mixed-substituted node: same-value substitution of the node's own
    certificate, then the `ConvT` substitution congruence on its right endpoint. -/
def mixedCert (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) {v v' t : Expr Nat}
    {j : Nat} {Γ : LCtx} {a b T : Expr Nat} (c₀ : ConvT E n Γ a b T) (hb : HasTyT E n Γ b T)
    (H : Hole t v j Γ)
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvc : ConvT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j v') (lift 0 j t)) :
    ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v') b) (instantiate j (lift 0 j v) T) :=
  .trans _ _ _ _ _ (H.convSubst hcl hinst c₀ hvty) (H.substCongr hcl hinst hb hvty hvc)

/-- The substituted right endpoint is typed at the left-substituted index: it is an endpoint
    of the substitution congruence. -/
def mixedRight (hW : EnvWfT E) {v v' t : Expr Nat} {j : Nat} {Γ : LCtx} {b T : Expr Nat}
    (hb : HasTyT E n Γ b T) (H : Hole t v j Γ)
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvc : ConvT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j v') (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) :
    HasTyT E n (substRemove v j Γ) (instantiate j (lift 0 j v') b)
      (instantiate j (lift 0 j v) T) :=
  (convEnds hW hΓ'wf
    (H.substCongr (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hb hvty
      hvc)).2.1

/-! ### the mixed step of a term, over its typing derivation -/

/-- `e[v] ⇒ e[v']` at `T[v]`, certified: the twin of the landed `parRedT_subst_arg`, the hole
    hit by the stepping pair, binders moved by `ConvT` (`convT_substCongr`), every right
    endpoint typed by `mixedRight`, every certificate `convT_substCongr` on the node. -/
def csubst_arg (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    {v v' t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T →
    (H : Hole t v j Γ) →
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) →
    (hvw₀ : CStep E n PEq (Γ.drop (j + 1)) v v' t) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) → (hΓwf : CtxWfT E n Γ) →
    CStep E n PEq (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v') e)
      (instantiate j (lift 0 j v) T)
  | _, _, _, _, .sort _Γ l, _, _, _, _, _ => by
      simp only [instantiate]
      exact ⟨.refl _ _ _ (.sort _ _), .refl (.refl _ _ _ (.sort _ _))⟩
  | j, Γ, _, _, .bvar _ i A h, H, hvt, hvw₀, _, _ => by
      have hcl := envClosed_of_envWfT hW
      by_cases hij : i = j
      · subst i
        rw [H.lookupTy] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (j + 1) 0 j (lift 0 j v)
          (Nat.zero_le j) (Nat.lt_succ_self j)]
        exact subst_hvw_of_drop hcl hPEqL H hvw₀
      · by_cases hlt : i < j
        · have hl := lookupType_substRemove_lt (v := v) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact ⟨.refl _ _ _ (.bvar _ _ _ hl), .refl (.refl _ _ _ (.bvar _ _ _ hl))⟩
        · have hgt : j < i := by omega
          have hl := lookupType_substRemove_gt (v := v) hgt h
          simp only [instantiate, if_neg hij, if_pos hgt]
          exact ⟨.refl _ _ _ (.bvar _ _ _ hl), .refl (.refl _ _ _ (.bvar _ _ _ hl))⟩
  | j, _, _, _, .const _ r ls m hres hlen hwf, _, _, _, _, _ => by
      have hinst := envMembersSubstStable_of_envWfT hW
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact ⟨.refl _ _ _ (.const _ r ls m hres hlen hwf),
        .refl (.refl _ _ _ (.const _ r ls m hres hlen hwf))⟩
  | j, Γ, _, _, .pi _ A u B w hA hB, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hwf' := H.wfAssump hcl hinst hvty hΓ'wf hA
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hvw' := subst_hvw_of_drop hcl hPEqL hget' hvw₀
      have hvc' := hvw'.toConvT
      have hA' := H.tySubst hcl hinst hA hvty
      have hcA := H.substCongr hcl hinst hA hvty hvc
      have hB' := hget'.tySubst hcl hinst hB hvty'
      have hcB := hget'.substCongr hcl hinst hB hvty' hvc'
      simp only [substRemove_succ_cons, instDecl] at hB' hcB
      have hrt' := mixedRight hW (.pi Γ A u B w hA hB) H hvty hvc hΓ'wf
      have hc₀ := H.substCongr hcl hinst (.pi Γ A u B w hA hB) hvty hvc
      simp only [instantiate] at hrt' hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hrt' hc₀ ⊢
      exact ⟨.pi _ _ _ _ _ _ _ hA' hcA hB' hcB hrt', .pi hc₀⟩
  | j, Γ, _, _, .lam _ A u body B hA hbody, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hwf' := H.wfAssump hcl hinst hvty hΓ'wf hA
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hΓwfA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓwf hA
      have ⟨w, hBw⟩ := tySort hW hΓwfA hbody
      have hA' := H.tySubst hcl hinst hA hvty
      have hcA := H.substCongr hcl hinst hA hvty hvc
      have hB' := hget'.tySubst hcl hinst hBw hvty'
      have hbody' := csubst_arg hW L hPEqL hbody hget' hvt hvw₀ hwf' hΓwfA
      simp only [substRemove_succ_cons, instDecl] at hB' hbody'
      have hrt' := mixedRight hW (.lam Γ A u body B hA hbody) H hvty hvc hΓ'wf
      have hc₀ := H.substCongr hcl hinst (.lam Γ A u body B hA hbody) hvty hvc
      simp only [instantiate] at hrt' hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hrt' hc₀ ⊢
      exact ⟨.lam _ _ _ _ _ _ _ _ hcA hA' hB' hbody'.step hrt', .lam hc₀ hbody'.cert⟩
  | j, Γ, _, _, .app _ f a A B hf ha, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have ⟨u, w, hAu, hBw, _⟩ := hasTyTInv_pi (tySort hW hΓwf hf).2 rfl
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hf' := csubst_arg hW L hPEqL hf H hvt hvw₀ hΓ'wf hΓwf
      have ha' := csubst_arg hW L hPEqL ha H hvt hvw₀ hΓ'wf hΓwf
      have hB' := hget'.tySubst hcl hinst hBw hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw ha
      have hTy := H.tySubst hcl hinst hTy0 hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      have hr := mixedRight hW (.app Γ f a A B hf ha) H hvty hvc hΓ'wf
      have hc₀ := H.substCongr hcl hinst (.app Γ f a A B hf ha) hvty hvc
      simp only [instantiate] at hTy hr hc₀ hf' ⊢
      rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy hr hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hf'
      exact ⟨.app _ _ _ _ _ _ _ _ _ _ hf'.step (.refl _ _) hB' hTy ha'.step hr,
        .app hc₀ hf'.cert ha'.cert⟩
  | j, Γ, _, _, .letE _ A u value B body hA hv hb, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hwf' := H.wfLet hcl hinst hvty hΓ'wf hA hv
      have hget' := H.succ (.letBinding A value)
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hΓwfL : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓwf hA hv
      have ⟨w, hBw⟩ := tySort hW hΓwfL hb
      have hA' := H.tySubst hcl hinst hA hvty
      have hcA := H.substCongr hcl hinst hA hvty hvc
      have hv' := csubst_arg hW L hPEqL hv H hvt hvw₀ hΓ'wf hΓwf
      have hb' := csubst_arg hW L hPEqL hb hget' hvt hvw₀ hwf' hΓwfL
      have hB' := hget'.tySubst hcl hinst hBw hvty'
      simp only [substRemove_succ_cons, instDecl] at hB' hb'
      have hTy0 := hasTyT_substLetS hcl hinst A value hBw
        List.getElem?_cons_zero (by simp only [lift_zero_idx]; exact hv)
      have hTy := H.tySubst hcl hinst hTy0 hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate 0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B
      have hrt := mixedRight hW (.letE Γ A u value B body hA hv hb) H hvty hvc hΓ'wf
      have hc₀ := H.substCongr hcl hinst (.letE Γ A u value B body hA hv hb) hvty hvc
      simp only [instantiate0, instantiate, lift_zero_idx] at hTy hrt hc₀ ⊢
      rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy hrt hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hrt hc₀ ⊢
      exact ⟨.letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv'.step hB' hTy hb'.step hrt,
        .letE hc₀ hv'.cert hb'.cert⟩
  | j, Γ, _, _, .lit _ tl T hexp, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hexp' := H.tySubst hcl hinst hexp hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      simp only [instantiate]
      exact ⟨.refl _ _ _ (.lit _ _ _ hexp'), .refl (.refl _ _ _ (.lit _ _ _ hexp'))⟩
  | j, Γ, _, _, .conv _ e A B u h hc, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have h' := csubst_arg hW L hPEqL h H hvt hvw₀ hΓ'wf hΓwf
      have hc' := H.convSubst hcl hinst hc hvty
      have hc₀ := H.substCongr hcl hinst (.conv Γ e A B u h hc) hvty hvc
      exact ⟨.conv _ _ _ _ _ h'.step (.of _ _ _ u hc'), .conv hc₀ h'.cert⟩
  termination_by j Γ e T h _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-! ### the mixed step of a certified step -/

/-- `a[v] ⇒ b[v']` at `T[v]`, certified, for every K-free certified step: the arms of the
    landed `parRedT_substSame` with the value pair, `refl` leaves by `csubst_arg`, the `peq`
    leaf re-formed by the leaf interface at the substituted `Prop`; certificates by
    `mixedCert`, right endpoints by `mixedRight`. -/
def csubstMixed (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    {v v' t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → {p : ParRedT PEq E n Γ a b T} → Certified p →
    (H : Hole t v j Γ) →
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) →
    (hvw₀ : CStep E n PEq (Γ.drop (j + 1)) v v' t) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) → (hΓwf : CtxWfT E n Γ) →
    CStep E n PEq (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v') b)
      (instantiate j (lift 0 j v) T)
  | _, _, _, _, _, _, @Certified.refl _ _ _ _ _ _ h _, H, hvt, hvw₀, hΓ'wf, hΓwf =>
      csubst_arg hW L hPEqL h H hvt hvw₀ hΓ'wf hΓwf
  | j, Γ, _, _, _, _, @Certified.sortEq _ _ _ _ _ _ _ h hl hr c₀, H, hvt, hvw₀, hΓ'wf, _ => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hc₀ := mixedCert hcl hinst c₀ hr H hvty hvc
      simp only [instantiate] at hc₀ ⊢
      exact ⟨.sortEq _ _ _ _ h (H.tySubst hcl hinst hl hvty)
        (H.tySubst hcl hinst hr hvty), .sortEq hc₀⟩
  | j, Γ, _, _, _, _, @Certified.consts _ _ _ _ _ _ _ _ h hl hr c₀, H, hvt, hvw₀, hΓ'wf, _ => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hc₀ := mixedCert hcl hinst c₀ hr H hvty hvc
      simp only [instantiate] at hc₀ ⊢
      exact ⟨.consts _ _ _ _ _ h (H.tySubst hcl hinst hl hvty)
        (H.tySubst hcl hinst hr hvty), .consts hc₀⟩
  | j, Γ, _, _, _, _, @Certified.delta _ _ _ _ r ls m b _ hres hbody htr hlen hwf hl hr c₀,
      H, hvt, hvw₀, hΓ'wf, _ => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hid := (hinst r m hres).2 b hbody ls (lift 0 j v) j
      have hid' := (hinst r m hres).2 b hbody ls (lift 0 j v') j
      have hr' := H.tySubst hcl hinst hr hvty
      have hc₀ := mixedCert hcl hinst c₀ hr H hvty hvc
      simp only [instantiate] at hr' hc₀ ⊢
      rw [hid] at hr'
      rw [hid'] at hc₀ ⊢
      exact ⟨.delta _ _ _ _ _ _ hres hbody htr hlen hwf
        (H.tySubst hcl hinst hl hvty) hr', .delta hc₀⟩
  | j, Γ, _, _, _, _, @Certified.conv _ _ _ _ a b A A' h hc c₀ ch, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have h' := csubstMixed hW L hPEqL ch H hvt hvw₀ hΓ'wf hΓwf
      have hc' := H.tyConvSubst hcl hinst hc hvty
      have hc₀ := mixedCert hcl hinst c₀
        (parRedT_hasTy_right L.typed hΓwf (ParRedT.conv Γ a b A A' h hc)) H hvty hvc
      exact ⟨.conv _ _ _ _ _ h'.step hc', .conv hc₀ h'.cert⟩
  | j, Γ, _, _, _, _, @Certified.lit _ _ _ _ tl _ hexp c₀, H, hvt, hvw₀, hΓ'wf, _ => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hexp' := H.tySubst hcl hinst hexp hvty
      have hc₀ := mixedCert hcl hinst c₀ hexp H hvty hvc
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      rw [natExpand_instantiate j (lift 0 j v') tl] at hc₀ ⊢
      simp only [instantiate] at hc₀ ⊢
      exact ⟨.lit _ _ _ hexp', .lit hc₀⟩
  | j, Γ, _, _, _, _, @Certified.eta _ _ _ _ f f' A B hf hl c₀ cf, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hf' := csubstMixed hW L hPEqL cf H hvt hvw₀ hΓ'wf hΓwf
      have hl' := H.tySubst hcl hinst hl hvty
      have hc₀ := mixedCert hcl hinst c₀ (parRedT_hasTy_right L.typed hΓwf hf) H hvty hvc
      simp only [instantiate,
        if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
        if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
        at hf' hl' hc₀ ⊢
      have e2 : instantiate (j + 1) (lift 0 1 (lift 0 j v)) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      rw [e2] at hl' hc₀ ⊢
      exact ⟨.eta _ _ _ _ _ hf'.step hl', .eta hc₀ hf'.cert⟩
  | j, Γ, _, _, _, _, @Certified.peq _ _ _ _ p q T h c₀, H, hvt, hvw₀, hΓ'wf, _ => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hP' := H.tySubst hcl hinst (L.prop h) hvty
      have hp' := H.tySubst hcl hinst (L.typed h).1 hvty
      have hq' := mixedRight hW (L.typed h).2 H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ (L.typed h).2 H hvty hvc
      simp only [instantiate] at hP'
      exact ⟨.peq _ _ _ _ (L.ofIrr hP' hp' hq'), .peq hc₀⟩
  | j, Γ, _, _, _, _, @Certified.iotaSpine _ _ _ _ lhs lhs' rhs T hstep hI hred hrhs c₀ cs,
      H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hstep' := csubstMixed hW L hPEqL cs H hvt hvw₀ hΓ'wf hΓwf
      have hI' := derivedIotaU_subst j (lift 0 j v') hI
      have hred' := mixedRight hW hred H hvty hvc hΓ'wf
      have hrhs' := mixedRight hW hrhs H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hrhs H hvty hvc
      exact ⟨.iotaSpine _ _ _ _ _ hstep'.step hI' hred' hrhs', .iotaSpine hc₀ hstep'.cert⟩
  | j, Γ, _, _, _, _, @Certified.app _ _ _ _ f f' a a' A B T₀ u w hf hc hB hTy ha hr c₀ cf ca,
      H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hf' := csubstMixed hW L hPEqL cf H hvt hvw₀ hΓ'wf hΓwf
      have ha' := csubstMixed hW L hPEqL ca H hvt hvw₀ hΓ'wf hΓwf
      have hpi := (tySort hW hΓwf (hasTyT_of_tyConvT
        (parRedT_hasTy_left L.typed hΓwf hf) hc)).2
      have ⟨u₀, w₀, hAu, hBw, _⟩ := hasTyTInv_pi hpi rfl
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hB' := hget'.tySubst hcl hinst hB hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw (parRedT_hasTy_left L.typed hΓwf ha)
      have hTy' := H.tySubst hcl hinst hTy0 hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      have hr' := mixedRight hW hr H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hr H hvty hvc
      simp only [instantiate] at hTy' hr' hc₀ ⊢
      rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy' hr' hc₀ ⊢
      have hcc : TyConvT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) T₀)
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) := by
        have h0 := H.tyConvSubst hcl hinst hc hvty
        simp only [instantiate] at h0 ⊢
        rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at h0
        exact h0
      exact ⟨.app _ _ _ _ _ _ _ _ _ _ hf'.step hcc hB' hTy' ha'.step hr', .app hc₀ hf'.cert ha'.cert⟩
  | j, Γ, _, _, _, _, @Certified.beta _ _ _ _ A body body' arg arg' B u v₁ w hA hB hTy hb ha hred
      c₀ cb ca, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hwf' := H.wfAssump hcl hinst hvty hΓ'wf hA
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hΓwfA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓwf hA
      have hA' := H.tySubst hcl hinst hA hvty
      have hB' := hget'.tySubst hcl hinst hB hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := csubstMixed hW L hPEqL cb hget' hvt hvw₀ hwf' hΓwfA
      simp only [substRemove_succ_cons, instDecl] at hb'
      have ha' := csubstMixed hW L hPEqL ca H hvt hvw₀ hΓ'wf hΓwf
      have hTy' := H.tySubst hcl hinst hTy hvty
      have hred' := mixedRight hW hred H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hred H hvty hvc
      have hcommB : instantiate j (lift 0 j v) (instantiate0 arg B) =
          instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg (lift 0 j v) (Nat.zero_le j) B
      have hcommBody : instantiate j (lift 0 j v') (instantiate0 arg' body') =
          instantiate0 (instantiate j (lift 0 j v') arg')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v')) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg' (lift 0 j v') (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' hc₀ ⊢
      rw [hcommB, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hred' hc₀ ⊢
      exact ⟨.beta _ _ _ _ _ _ _ _ _ _ hA' hB' hTy' hb'.step ha'.step hred',
        .beta hc₀ hb'.cert ha'.cert⟩
  | j, Γ, _, _, _, _, @Certified.lam _ _ _ _ A A' body body' B u v₁ hc hA hB hb hrt c₀ cb,
      H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hwf' := H.wfAssump hcl hinst hvty hΓ'wf hA
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hΓwfA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓwf hA
      have hA' := H.tySubst hcl hinst hA hvty
      have hA'ty : HasTyT E n Γ A' (.sort u) := (convEnds hW hΓwf hc).2.1
      have hcA : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v') A') (.sort u) :=
        .trans _ _ _ _ _ (H.convSubst hcl hinst hc hvty)
          (H.substCongr hcl hinst hA'ty hvty hvc)
      have hB' := hget'.tySubst hcl hinst hB hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := csubstMixed hW L hPEqL cb hget' hvt hvw₀ hwf' hΓwfA
      simp only [substRemove_succ_cons, instDecl] at hb'
      have hrt' := mixedRight hW hrt H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hrt H hvty hvc
      simp only [instantiate] at hrt' hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hrt' hc₀ ⊢
      exact ⟨.lam _ _ _ _ _ _ _ _ hcA hA' hB' hb'.step hrt', .lam hc₀ hb'.cert⟩
  | j, Γ, _, _, _, _, @Certified.pi _ _ _ _ A A' B B' u v₁ hA hc hB hcB hrt c₀,
      H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hget' := H.succ (.assumption A)
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hvw' := subst_hvw_of_drop hcl hPEqL hget' hvw₀
      have hvc' := hvw'.toConvT
      have hΓwfA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓwf hA
      have hA' := H.tySubst hcl hinst hA hvty
      have hA'ty : HasTyT E n Γ A' (.sort u) := (convEnds hW hΓwf hc).2.1
      have hcA : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v') A') (.sort u) :=
        .trans _ _ _ _ _ (H.convSubst hcl hinst hc hvty)
          (H.substCongr hcl hinst hA'ty hvty hvc)
      have hB' := hget'.tySubst hcl hinst hB hvty'
      have hB'ty : HasTyT E n (.assumption A :: Γ) B' (.sort v₁) := (convEnds hW hΓwfA hcB).2.1
      have hcB' := ConvT.trans _ _ _ _ _ (hget'.convSubst hcl hinst hcB hvty')
        (hget'.substCongr hcl hinst hB'ty hvty' hvc')
      simp only [substRemove_succ_cons, instDecl] at hB' hcB'
      have hrt' := mixedRight hW hrt H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hrt H hvty hvc
      simp only [instantiate] at hrt' hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hrt' hc₀ ⊢
      exact ⟨.pi _ _ _ _ _ _ _ hA' hcA hB' hcB' hrt', .pi hc₀⟩
  | j, Γ, _, _, _, _, @Certified.letE _ _ _ _ A A' value value' body body' B u w hc hA hv hB hTy hb
      hrt c₀ cv cb, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hvl := parRedT_hasTy_left L.typed hΓwf hv
      have hwf' := H.wfLet hcl hinst hvty hΓ'wf hA hvl
      have hget' := H.succ (.letBinding A value)
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hΓwfL : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓwf hA hvl
      have hA' := H.tySubst hcl hinst hA hvty
      have hA'ty : HasTyT E n Γ A' (.sort u) := (convEnds hW hΓwf hc).2.1
      have hcA : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v') A') (.sort u) :=
        .trans _ _ _ _ _ (H.convSubst hcl hinst hc hvty)
          (H.substCongr hcl hinst hA'ty hvty hvc)
      have hv' := csubstMixed hW L hPEqL cv H hvt hvw₀ hΓ'wf hΓwf
      have hB' := hget'.tySubst hcl hinst hB hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := csubstMixed hW L hPEqL cb hget' hvt hvw₀ hwf' hΓwfL
      simp only [substRemove_succ_cons, instDecl] at hb'
      have hTy' := H.tySubst hcl hinst hTy hvty
      have hrt' := mixedRight hW hrt H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hrt H hvty hvc
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate] at hTy' hrt' hc₀ ⊢
      rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy' hrt' hc₀ ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hrt' hc₀ ⊢
      exact ⟨.letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv'.step hB' hTy' hb'.step hrt',
        .letE hc₀ hv'.cert hb'.cert⟩
  | j, Γ, _, _, _, _, @Certified.zeta _ _ _ _ A value value' body body' B u w hA hv hB hTy hb hred
      c₀ cv cb, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      have hvl := parRedT_hasTy_left L.typed hΓwf hv
      have hwf' := H.wfLet hcl hinst hvty hΓ'wf hA hvl
      have hget' := H.succ (.letBinding A value)
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hΓwfL : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓwf hA hvl
      have hA' := H.tySubst hcl hinst hA hvty
      have hv' := csubstMixed hW L hPEqL cv H hvt hvw₀ hΓ'wf hΓwf
      have hB' := hget'.tySubst hcl hinst hB hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := csubstMixed hW L hPEqL cb hget' hvt hvw₀ hwf' hΓwfL
      simp only [substRemove_succ_cons, instDecl] at hb'
      have hTy' := H.tySubst hcl hinst hTy hvty
      have hred' := mixedRight hW hred H hvty hvc hΓ'wf
      have hc₀ := mixedCert hcl hinst c₀ hred H hvty hvc
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B
      have hcomm' : instantiate j (lift 0 j v') (instantiate0 value' body') =
          instantiate0 (instantiate j (lift 0 j v') value')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v')) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value' (lift 0 j v') (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' hc₀ ⊢
      rw [hcomm, lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'] at hred' hc₀ ⊢
      exact ⟨.zeta _ _ _ _ _ _ _ _ _ hA' hv'.step hB' hTy' hb'.step hred',
        .zeta hc₀ hv'.cert hb'.cert⟩
  | j, Γ, _, _, _, _, @Certified.bvarZeta _ _ _ _ i A val val' T h hv hl hr c₀ cv,
      H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hvw := subst_hvw_of_drop hcl hPEqL H hvw₀
      have hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) :=
        hvw.leftTyped L hΓ'wf
      have hvc := hvw.toConvT
      by_cases hij : i = j
      · subst hij
        have h' : Γ[i]? = some (.letBinding A val) :=
          (List.get?_eq_getElem? Γ i).symm ▸ h
        cases H with
        | assump H => rw [h'] at H; exact nomatch H
        | letB H =>
          have e : LocalDecl.letBinding t v = .letBinding A val :=
            Option.some.inj (H.symm.trans h')
          injection e with eA ev
          subst eA
          subst ev
          simp only [instantiate, if_pos rfl]
          rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i v') (Nat.zero_le i)
            (Nat.lt_succ_self i)]
          have hvs := subst_hvw_of_drop hcl hPEqL (Hole.letB H) ⟨hv, cv⟩
          obtain ⟨A₀, hlk, hcT⟩ := hasTyTInv_bvar hl rfl
          rw [lookupType_get_letBinding H] at hlk
          cases Option.some.inj hlk
          have hcT' := (Hole.letB H).tyConvSubst hcl hinst hcT hvty
          rw [instantiate_lift_cancel (i + 1) 0 i _ (Nat.zero_le i) (Nat.lt_succ_self i)] at hcT'
          exact hvs.reindex hcT'
      · by_cases hlt : i < j
        · simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_lt (v := v) hlt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hsΓ : lift 0 (i + 1) (lift 0 (j - i - 1) v) = lift 0 j v := by
            have hc := lift_zero_comp (i + 1) (j - i - 1) v
            rw [show i + 1 + (j - i - 1) = j from by omega] at hc
            exact hc
          have hsΓ' : lift 0 (i + 1) (lift 0 (j - i - 1) v') = lift 0 j v' := by
            have hc := lift_zero_comp (i + 1) (j - i - 1) v'
            rw [show i + 1 + (j - i - 1) = j from by omega] at hc
            exact hc
          have hcomm (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 (i + 1) (instantiate (j - i - 1) (lift 0 (j - i - 1) v) e) := by
            have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1) (lift 0 (j - i - 1) v)
              (Nat.zero_le _) e
            rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ] at h1
            exact h1.symm
          have hcomm' (e : Expr Nat) :
              instantiate j (lift 0 j v') (lift 0 (i + 1) e) =
                lift 0 (i + 1) (instantiate (j - i - 1) (lift 0 (j - i - 1) v') e) := by
            have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1) (lift 0 (j - i - 1) v')
              (Nat.zero_le _) e
            rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ'] at h1
            exact h1.symm
          have hstored : stored = instantiate (j - i - 1) (lift 0 (j - i - 1) v) val :=
            lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm val))
          have hdrop : (substRemove v j Γ).drop (i + 1) =
              substRemove v (j - i - 1) (Γ.drop (i + 1)) := by
            rw [substRemove_drop, if_pos (by omega : i + 1 ≤ j)]
            congr 1
          have HD : Hole t v (j - i - 1) (Γ.drop (i + 1)) := H.drop (i + 1) (by omega)
          have hd : (Γ.drop (i + 1)).drop (j - i - 1 + 1) = Γ.drop (j + 1) := by
            rw [List.drop_drop]
            congr 1
            omega
          have hvtD : HasTyT E n ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) v t := by
            rw [hd]; exact hvt
          have hvw₀D : CStep E n PEq ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) v v' t := by
            rw [hd]; exact hvw₀
          have hΓwfD := ctxWfT_drop hΓwf (i + 1)
          have hΓ'wfD : CtxWfT E n (substRemove v (j - i - 1) (Γ.drop (i + 1))) :=
            hdrop ▸ ctxWfT_drop hΓ'wf (i + 1)
          have hv' := csubstMixed hW L hPEqL cv HD hvtD hvw₀D hΓ'wfD hΓwfD
          rw [← hdrop] at hv'
          have hA' : A' = instantiate (j - i - 1) (lift 0 (j - i - 1) v) A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_lt (v := v) hlt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) i = some (lift 0 (i + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            exact lift_zero_amount_inj (i + 1) (hinj.trans (hcomm A))
          rw [← hstored, ← hA'] at hv'
          have hl' := H.tySubst hcl hinst hl hvty
          have hr' := mixedRight hW hr H hvty hvc hΓ'wf
          have hc₀ := mixedCert hcl hinst c₀ hr H hvty hvc
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)] at hl' hr' hc₀
          rw [hcomm' val'] at hr' hc₀ ⊢
          exact ⟨.bvarZeta _ i A' stored (instantiate (j - i - 1) (lift 0 (j - i - 1) v') val') _
            hg' hv'.step hl' hr', .bvarZeta hc₀ hv'.cert⟩
        · have hgt : j < i := by omega
          simp only [instantiate, if_neg hij, if_pos hgt]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_gt (v := v) hgt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) = lift 0 i e :=
            instantiate_lift_cancel (i + 1) 0 j (lift 0 j v) (Nat.zero_le j) (by omega) e
          have hcan' (e : Expr Nat) :
              instantiate j (lift 0 j v') (lift 0 (i + 1) e) = lift 0 i e :=
            instantiate_lift_cancel (i + 1) 0 j (lift 0 j v') (Nat.zero_le j) (by omega) e
          have hi1 : i - 1 + 1 = i := by omega
          have hstored : stored = val := by
            have heq' : lift 0 i stored = lift 0 i val := by
              have h1 := heq.symm.trans (hcan val)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hA' : A' = A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_gt (v := v) hgt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) (i - 1) =
                some (lift 0 ((i - 1) + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            have heq' : lift 0 i A' = lift 0 i A := by
              have h1 := hinj.trans (hcan A)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hdrop : (substRemove v j Γ).drop i = Γ.drop (i + 1) := by
            rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
          have hv' : CStep E n PEq ((substRemove v j Γ).drop (i - 1 + 1)) val val' A := by
            rw [hi1]; exact hdrop ▸ ⟨hv, cv⟩
          have hl' := H.tySubst hcl hinst hl hvty
          have hr' := mixedRight hW hr H hvty hvc hΓ'wf
          have hc₀ := mixedCert hcl hinst c₀ hr H hvty hvc
          simp only [instantiate, if_neg hij, if_pos hgt] at hl' hr' hc₀
          rw [hcan' val'] at hr' hc₀ ⊢
          have hr'' : HasTyT E n (substRemove v j Γ) (lift 0 (i - 1 + 1) val')
              (instantiate j (lift 0 j v) T) := by
            rw [hi1]; exact hr'
          have hc'' : ConvT E n (substRemove v j Γ) (.bvar (i - 1)) (lift 0 (i - 1 + 1) val')
              (instantiate j (lift 0 j v) T) := by
            rw [hi1]; exact hc₀
          rw [← hstored, ← hA'] at hv'
          have step : CStep E n PEq (substRemove v j Γ) (.bvar (i - 1)) (lift 0 (i - 1 + 1) val')
              (instantiate j (lift 0 j v) T) :=
            ⟨.bvarZeta _ (i - 1) A' stored val' _ hg' hv'.step hl' hr'', .bvarZeta hc'' hv'.cert⟩
          rw [hi1] at step
          exact step
  termination_by _ _ _ _ _ _ cp _ _ _ _ _ => sizeOf cp
  decreasing_by all_goals (simp; omega)

/-! ### `CertSubst0` discharged -/

/-- The one-step certified mixed substitution of `RcicNativeValleyRows` (`CertSubst0`), at the
    head hole, under `EnvWfT` and leaf weakening. -/
def certSubst0_of (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    CertSubst0 E n PEq :=
  fun {Γ} hΓ {A v v' body body' B} {u} hA pb pv => by
    have h := csubstMixed hW L hPEqL (j := 0) (Γ := .assumption A :: Γ) pb.cert
      (.assump List.getElem?_cons_zero) (pv.leftTyped L hΓ) pv hΓ (.assumption Γ A u hΓ hA)
    simp only [substRemove_zero_cons, lift_zero] at h
    exact h

/-- The one-step certified mixed substitution at a `let` hole (`CertSubstLet`,
    `RcicNativeValleyRows`): the same recursion at `Hole.letB`. -/
def certSubstLet_of (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    CertSubstLet E n PEq :=
  fun {Γ} hΓ {A v v' body body' B} {u} hA hv pb pv => by
    have h := csubstMixed hW L hPEqL (j := 0) (Γ := .letBinding A v :: Γ) pb.cert
      (.letB List.getElem?_cons_zero) (pv.leftTyped L hΓ) pv hΓ (.letBinding Γ A u v hΓ hA hv)
    simp only [substRemove_zero_cons, lift_zero] at h
    exact h

end Rcic.Declarative.NativeValleys
