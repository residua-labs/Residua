import rcic.RcicCtxConvT
import rcic.RcicPEqT
import rcic.RcicTypedSubst
import rcic.RcicTypedSubstLet
import rcic.RcicTypedInvert

/-!
# `RcicPEqTSubst` — the Seg-B substitution/context kit for `PEqT`

Plain (`*T`) twin of `RcicAnnPEqSubst` for the PiRow ATR route (#6293, plain
ruling), built on irrpost's `PEqT` core (`RcicPEqT.lean`, #6468): `PEqT` is
preserved by lift / instantiation / substitution (F-ι★-9) and transports
across `CtxConvT`-related contexts (F-ι★-7), all on the plain typed
judgment. The kit is design-independent of the measure (F-ι★-8, irrpost).

Design notes:

- `proof` leaf is the loose leaf: two proofs with NO common proposition —
  `p : P`, `q : Q`, `P Q : sort 0` — raw `HasTyT` fields (Type-valued), not
  `Nonempty` (a `Prop` ctx relation cannot eliminate into `Type`; the
  `CtxConvT` stack is Type-valued for exactly this reason).
- Binder cases extend by the LEFT declaration (`lam`/`pi` push
  `.assumption A`, `letE` pushes `.letBinding A v`), so `symm`/`trans`
  (structural,structural) are NOT kit-freebies — same boundary as Ann.
- Substitution is expressed in `substRemove`/`instantiate` form (the
  `hasTyT_substS` shape), not via a `SubstT` record — the plain layer works
  directly on `instantiate`. `instantiate_pair` is the twin of
  `hasTyA_func` + `PEq.substA_pair` fused: two related replacements
  (`v ≈P v'`, both typed at `t`, convertible at `t`) instantiate one
  skeleton pairwise.
- The `proof` leaf under a pair needs its right-side typings at the v-ctx:
  `ctxConvT_substRemove` builds `CtxConvT (substRemove v' j Γ)
  (substRemove v j Γ)` — decl-wise conversion of the two instantiated
  contexts — and `hasTyT_ctx` moves the typings. `ConvT.iota` carries a
  `DerivedIota` witness reading only `E`, so the bridge needs no
  iota-interface premise; `CtxWfT Γ` supplies the decl typings.
- Gates: `EnvClosed E` + `EnvMembersSubstStable E`; `envClosed_of_envWfT` /
  `envMembersSubstStable_of_envWfT` supply both at `EnvWfT` call sites.
-/

namespace Rcic.Declarative

/-! The relation (`PEqT`), `PEqT.refl`, and the proof-leaf projections live
in `RcicPEqT.lean` (irrpost's core, #6468) — this module is kit-only.

## (2) F-ι★-9, lift half: `≈P` is preserved by `lift` -/

/-- lifting preserves `≈P`; the binder cases insert the declaration at `c + 1`,
    so the LEFT (pushed) declaration is `liftDecl`-consistent, and the `proof`
    leaf's typings weaken by `hasTyTWeaken`. -/
def PEqT.liftT (hcl : EnvClosed E) (d : LocalDecl) :
    {c : Nat} → {Γ : LCtx} → {e e' : Expr Nat} → PEqT E n Γ e e' →
    PEqT E n (insertAt d c Γ) (lift c 1 e) (lift c 1 e')
  | c, _, _, _, .bvar _ i => by
      by_cases hle : c ≤ i
      · simp only [lift, if_pos hle]; exact .bvar _ _
      · simp only [lift, if_neg hle]; exact .bvar _ _
  | _, _, _, _, .sort _ l l' h => .sort _ _ _ h
  | _, _, _, _, .const _ r ls ls' h => .const _ _ _ _ h
  | _, _, _, _, .lit _ t => .lit _ t
  | _, _, _, _, .app _ f f' a a' hf ha =>
      .app _ _ _ _ _ (PEqT.liftT hcl d hf) (PEqT.liftT hcl d ha)
  | c, _, _, _, .lam _ A A' b b' hA hb =>
      .lam _ _ _ _ _ (PEqT.liftT hcl d hA)
        (PEqT.liftT hcl d (c := c + 1) hb)
  | c, _, _, _, .pi _ A A' B B' hA hB =>
      .pi _ _ _ _ _ (PEqT.liftT hcl d hA)
        (PEqT.liftT hcl d (c := c + 1) hB)
  | c, _, _, _, .letE _ A A' v v' b b' hA hv hb =>
      .letE _ _ _ _ _ _ _ (PEqT.liftT hcl d hA) (PEqT.liftT hcl d hv)
        (PEqT.liftT hcl d (c := c + 1) hb)
  | c, _, _, _, .proof _ p q P Q hP hQ hp hq =>
      .proof _ _ _ _ _
        (hasTyTWeaken d hcl (c := c) hP) (hasTyTWeaken d hcl (c := c) hQ)
        (hasTyTWeaken d hcl (c := c) hp) (hasTyTWeaken d hcl (c := c) hq)

/-! ## (3) tail-local evidence → `substRemove`-form

The substitution premises the kit takes are stated at the TAIL
`drop (j+1) Γ` — where a caller's `v : t` lives — while `hasTyT_substS`
consumes the weakened `substRemove`-form `lift 0 j v : lift 0 j t` at
`substRemove v j Γ`. These three fold the weakening through the removal. -/

def hasTyT_substRemove_weaken (hcl : EnvClosed E) (v : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {t : Expr Nat} → {d : LocalDecl} →
    Γ[j]? = some d → HasTyT E n (List.drop (j + 1) Γ) v t →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)
  | _, [], _, _, hget, _ => by cases hget
  | 0, _ :: Γ, _, _, _, h => by simpa [lift_zero] using h
  | j + 1, x :: Γ, _, d, hget, h => by
      have hget' : Γ[j]? = some d := by rwa [List.getElem?_cons_succ] at hget
      have ih := hasTyT_substRemove_weaken hcl v hget' h
      have h0 := hasTyTWeaken (instDecl j v x) hcl (c := 0) ih
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at h0
      rw [substRemove_succ_cons]
      exact h0

def convT_substRemove_weaken (hcl : EnvClosed E) (v : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → {d : LocalDecl} →
    Γ[j]? = some d → ConvT E n (List.drop (j + 1) Γ) a b T →
    ConvT E n (substRemove v j Γ) (lift 0 j a) (lift 0 j b) (lift 0 j T)
  | _, [], _, _, _, _, hget, _ => by cases hget
  | 0, _ :: Γ, _, _, _, _, _, h => by simpa [lift_zero] using h
  | j + 1, x :: Γ, _, _, _, d, hget, h => by
      have hget' : Γ[j]? = some d := by rwa [List.getElem?_cons_succ] at hget
      have ih := convT_substRemove_weaken hcl v hget' h
      have h0 := convTWeaken (instDecl j v x) hcl (c := 0) ih
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at h0
      rw [substRemove_succ_cons]
      exact h0

def peqT_substRemove_weaken (hcl : EnvClosed E) (v : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b : Expr Nat} → {d : LocalDecl} →
    Γ[j]? = some d → PEqT E n (List.drop (j + 1) Γ) a b →
    PEqT E n (substRemove v j Γ) (lift 0 j a) (lift 0 j b)
  | _, [], _, _, _, hget, _ => by cases hget
  | 0, _ :: Γ, _, _, _, _, h => by simpa [lift_zero] using h
  | j + 1, x :: Γ, _, _, d, hget, h => by
      have hget' : Γ[j]? = some d := by rwa [List.getElem?_cons_succ] at hget
      have ih := peqT_substRemove_weaken hcl v hget' h
      have h0 := PEqT.liftT hcl (instDecl j v x) (c := 0) ih
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at h0
      rw [substRemove_succ_cons]
      exact h0

/-! ## (4) `hasTyT_inst_pair` — pairwise instantiation, `ConvT`-valued

The `*T` twin of `hasTyA_func`: instantiating a typing by two convertible
replacements converts the results. `v`-side evidence lands in
`substRemove v j Γ` by the weaken-chain; the `v'`-side is only ever used at
`i = j` (as the pair's right endpoint) — every other arm is single-sided and
delegates to `hasTyT_substS`/`convT_substS`. -/

def hasTyT_inst_pair (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A →
    {j : Nat} → {t v v' : Expr Nat} → Γ[j]? = some (.assumption t) →
    HasTyT E n (List.drop (j + 1) Γ) v t →
    HasTyT E n (List.drop (j + 1) Γ) v' t →
    ConvT E n (List.drop (j + 1) Γ) v v' t →
    ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) e)
      (instantiate j (lift 0 j v') e) (instantiate j (lift 0 j v) A)
  | _, _, _, .sort _ l, _, _, _, _, _, _, _, _ => by
      simp only [instantiate]; exact .refl _ _ _ (.sort _ _)
  | _, _, _, .bvar Γ i A h, j, t, v, v', hget, hv, _, hc => by
      by_cases hij : i = j
      · subst hij
        rw [lookupType_get_assumption hget] at h
        injection h with h; subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i v) (by omega) (by omega)]
        exact convT_substRemove_weaken hcl v hget hc
      · simp only [instantiate, if_neg hij]
        exact .refl _ _ _ (by
          simpa only [instantiate, if_neg hij] using
            hasTyT_substS hcl hinst v t (.bvar Γ i A h) hget
              (hasTyT_substRemove_weaken hcl v hget hv))
  | _, _, _, .const _ r ls m hres hlen hwf, j, _, v, _, _, _, _, _ => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact .refl _ _ _ (.const _ r ls m hres hlen hwf)
  | _, _, _, .pi Γ A u B w hA hB, j, t, v, v', hget, hv, hv', hc => by
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hA' := hasTyT_inst_pair hcl hinst hA hget hv hv' hc
      have hB' := hasTyT_inst_pair hcl hinst hB hget' hv hv' hc
      simp only [substRemove_succ_cons, instDecl] at hB'
      simp only [instantiate,
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at hB' ⊢
      exact .pi _ _ _ _ _ u w hA' hB'
  | _, _, _, .lam Γ A u body B hA hbody, j, t, v, v', hget, hv, hv', hc => by
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hA' := hasTyT_inst_pair hcl hinst hA hget hv hv' hc
      have hbody' := hasTyT_inst_pair hcl hinst hbody hget' hv hv' hc
      simp only [substRemove_succ_cons, instDecl] at hbody'
      simp only [instantiate,
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at hbody' ⊢
      exact .lam _ _ _ _ _ _ u hA' hbody'
  | _, _, _, .app Γ f a A B hf ha, j, t, v, v', hget, hv, hv', hc => by
      have hf' := hasTyT_inst_pair hcl hinst hf hget hv hv' hc
      have ha' := hasTyT_inst_pair hcl hinst ha hget hv hv' hc
      simp only [instantiate, instantiate0] at hf' ha' ⊢
      rw [instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B]
      simp only [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at hf' ⊢
      exact .app _ _ _ _ _ _ _ hf' ha'
  | _, _, _, .letE Γ A u value B body hA hv hb, j, t, v, v', hget, hv0, hv'0, hc => by
      have hget' : (LocalDecl.letBinding A value :: Γ)[j + 1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hA' := hasTyT_inst_pair hcl hinst hA hget hv0 hv'0 hc
      have hv' := hasTyT_inst_pair hcl hinst hv hget hv0 hv'0 hc
      have hb' := hasTyT_inst_pair hcl hinst hb hget' hv0 hv'0 hc
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate, instantiate0,
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)] at hA' hv' ⊢
      rw [instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B]
      simp only [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .letE _ _ _ _ _ _ _ _ u hA' hv' hb'
  | _, _, _, .lit Γ t T hexp, j, t0, v, v', hget, hv, _, _ => by
      have he' : HasTyT E n (substRemove v j Γ) (natExpand t)
          (instantiate j (lift 0 j v) T) := by
        have h := hasTyT_substS hcl hinst v t0 hexp hget
          (hasTyT_substRemove_weaken hcl v hget hv)
        rwa [natExpand_instantiate] at h
      exact .refl _ _ _ (.lit _ _ _ he')
  | _, _, _, .conv Γ e A B u h hc0, j, t, v, v', hget, hv, hv', hc => by
      have h' := hasTyT_inst_pair hcl hinst h hget hv hv' hc
      have hc' : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v) B) (.sort u) := by
        have hs := convT_substS hcl hinst v t hc0 hget
          (hasTyT_substRemove_weaken hcl v hget hv)
        simpa only [instantiate] using hs
      exact .tyConv _ _ _ _ _ _ h' hc'
  termination_by _ _ _ h _ _ _ _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-! ## (5) the instantiated-context bridge -/

/-- the two instantiated contexts are decl-wise convertible: the bridge that
    carries the `proof` leaf's right-side typings from `substRemove v' j Γ`
    into `substRemove v j Γ`. Decl typings come from `CtxWfT`; decl pairwise
    conversions from `hasTyT_inst_pair`. -/
def ctxConvT_substRemove (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → CtxWfT E n Γ →
    {j : Nat} → {t v v' : Expr Nat} → Γ[j]? = some (.assumption t) →
    HasTyT E n (List.drop (j + 1) Γ) v t →
    HasTyT E n (List.drop (j + 1) Γ) v' t →
    ConvT E n (List.drop (j + 1) Γ) v v' t →
    CtxConvT E n (substRemove v' j Γ) (substRemove v j Γ)
  | _, .nil, _, _, _, _, hget, _, _, _ => by cases hget
  | _, .assumption _ _ _ _ _, 0, _, _, _, _, _, _, _ => ctxConvT_refl _
  | _, .assumption Γ A₀ u hΓ hA₀, j + 1, t, v, v', hget, hv, hv', hc => by
      have hget' : Γ[j]? = some (.assumption t) := by
        rwa [List.getElem?_cons_succ] at hget
      have ih := ctxConvT_substRemove hcl hinst hΓ hget' hv hv' hc
      have hvsub := hasTyT_substRemove_weaken hcl v hget' hv
      have hv'sub := hasTyT_substRemove_weaken hcl v' hget' hv'
      have hA_v : HasTyT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) A₀) (.sort u) :=
        hasTyT_substS hcl hinst v t hA₀ hget' hvsub
      have hA_v' : HasTyT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v') A₀) (.sort u) :=
        hasTyT_ctx hcl ih (hasTyT_substS hcl hinst v' t hA₀ hget' hv'sub)
      have hcA : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v') A₀)
          (instantiate j (lift 0 j v) A₀) (.sort u) :=
        .symm _ _ _ _ (hasTyT_inst_pair hcl hinst hA₀ hget' hv hv' hc)
      rw [substRemove_succ_cons, substRemove_succ_cons]
      exact .assumption ih hA_v' hA_v hcA
  | _, .letBinding _ _ _ _ _ _ _, 0, _, _, _, _, _, _, _ => ctxConvT_refl _
  | _, .letBinding Γ A₀ u w₀ hΓ hA₀ hw₀, j + 1, t, v, v', hget, hv, hv', hc => by
      have hget' : Γ[j]? = some (.assumption t) := by
        rwa [List.getElem?_cons_succ] at hget
      have ih := ctxConvT_substRemove hcl hinst hΓ hget' hv hv' hc
      have hvsub := hasTyT_substRemove_weaken hcl v hget' hv
      have hv'sub := hasTyT_substRemove_weaken hcl v' hget' hv'
      have hA_v : HasTyT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) A₀) (.sort u) :=
        hasTyT_substS hcl hinst v t hA₀ hget' hvsub
      have hA_v' : HasTyT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v') A₀) (.sort u) :=
        hasTyT_ctx hcl ih (hasTyT_substS hcl hinst v' t hA₀ hget' hv'sub)
      have hcA : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v') A₀)
          (instantiate j (lift 0 j v) A₀) (.sort u) :=
        .symm _ _ _ _ (hasTyT_inst_pair hcl hinst hA₀ hget' hv hv' hc)
      have hw_v : HasTyT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) w₀) (instantiate j (lift 0 j v) A₀) :=
        hasTyT_substS hcl hinst v t hw₀ hget' hvsub
      have hpw : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) w₀)
          (instantiate j (lift 0 j v') w₀) (instantiate j (lift 0 j v) A₀) :=
        hasTyT_inst_pair hcl hinst hw₀ hget' hv hv' hc
      have hpA : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A₀)
          (instantiate j (lift 0 j v') A₀) (.sort u) :=
        hasTyT_inst_pair hcl hinst hA₀ hget' hv hv' hc
      have hcv : ConvT E n (substRemove v j Γ) (instantiate j (lift 0 j v') w₀)
          (instantiate j (lift 0 j v) w₀) (instantiate j (lift 0 j v') A₀) :=
        .tyConv _ _ _ _ _ _ (.symm _ _ _ _ hpw) hpA
      rw [substRemove_succ_cons, substRemove_succ_cons]
      exact .letBinding ih hA_v' hA_v hcA hw_v hcv

/-! ## (6) F-ι★-9, subst half: `≈P` under pairwise instantiation -/

/-- `≈P` under pairwise instantiation of one context entry — the `*T` twin of
    `PEq.substA_pair`, in `substRemove`/`instantiate` form. Evidence is
    tail-local (`drop (j+1) Γ`): `v ≈P v'`, both typed at `t`, convertible at
    `t`. `hB`/`he` supply the typings the binder cases and the `proof` leaf
    consume; `hΓ` supplies the ctx bridge's decl typings. -/
def PEqT.instantiate_pair (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e e' T : Expr Nat} → CtxWfT E n Γ →
    PEqT E n Γ e e' → HasTyT E n Γ e T →
    {j : Nat} → {t v v' : Expr Nat} → Γ[j]? = some (.assumption t) →
    HasTyT E n (List.drop (j + 1) Γ) v t →
    HasTyT E n (List.drop (j + 1) Γ) v' t →
    ConvT E n (List.drop (j + 1) Γ) v v' t →
    PEqT E n (List.drop (j + 1) Γ) v v' →
    PEqT E n (substRemove v j Γ) (instantiate j (lift 0 j v) e)
      (instantiate j (lift 0 j v') e')
  | _, _, _, _, _, .bvar _ i, _, j, _, v, _, hget, _, _, _, hvv => by
      by_cases hij : i = j
      · subst hij
        simp only [instantiate, if_pos rfl]
        exact peqT_substRemove_weaken hcl v hget hvv
      · by_cases hlt : j < i
        · simp only [instantiate, if_neg hij, if_pos hlt]; exact .bvar _ _
        · simp only [instantiate, if_neg hij, if_neg hlt]; exact .bvar _ _
  | _, _, _, _, _, .sort _ l l' h, _, _, _, _, _, _, _, _, _, _ =>
      .sort _ _ _ h
  | _, _, _, _, _, .const _ r ls ls' h, _, _, _, _, _, _, _, _, _, _ =>
      .const _ _ _ _ h
  | _, _, _, _, _, .lit _ t, _, _, _, _, _, _, _, _, _, _ => .lit _ t
  | _, _, _, _, hΓ, .app _ _ _ _ _ hf ha, he, j, t, v, v', hget, hv, hv', hc, hvv => by
      obtain ⟨A₀, B₀, hfty, haty, _⟩ := hasTyTInv_app he rfl
      exact .app _ _ _ _ _
        (PEqT.instantiate_pair hcl hinst hΓ hf hfty hget hv hv' hc hvv)
        (PEqT.instantiate_pair hcl hinst hΓ ha haty hget hv hv' hc hvv)
  | Γ, _, _, _, hΓ, .lam _ A A' b b' hA hb, he, j, t, v, v', hget, hv, hv', hc, hvv => by
      obtain ⟨u, B₀, hAty, hbody, _⟩ := hasTyTInv_lam he rfl
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hA' := PEqT.instantiate_pair hcl hinst hΓ hA hAty hget hv hv' hc hvv
      have hb' := PEqT.instantiate_pair hcl hinst (.assumption _ _ _ hΓ hAty) hb hbody
        hget' hv hv' hc hvv
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .lam _ _ _ _ _ hA' hb'
  | Γ, _, _, _, hΓ, .pi _ A A' B B' hA hB, he, j, t, v, v', hget, hv, hv', hc, hvv => by
      obtain ⟨u, w, hAty, hBty, _⟩ := hasTyTInv_pi he rfl
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hA' := PEqT.instantiate_pair hcl hinst hΓ hA hAty hget hv hv' hc hvv
      have hB' := PEqT.instantiate_pair hcl hinst (.assumption _ _ _ hΓ hAty) hB hBty
        hget' hv hv' hc hvv
      simp only [substRemove_succ_cons, instDecl] at hB'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .pi _ _ _ _ _ hA' hB'
  | Γ, _, _, _, hΓ, .letE _ A A' v0 v0' b b' hA hv0 hb, he, j, t, v, v',
      hget, hv, hv', hc, hvv => by
      obtain ⟨u, B₀, hAty, hvty, hbty, _⟩ := hasTyTInv_letE he rfl
      have hget' : (LocalDecl.letBinding A v0 :: Γ)[j + 1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hA' := PEqT.instantiate_pair hcl hinst hΓ hA hAty hget hv hv' hc hvv
      have hv0' := PEqT.instantiate_pair hcl hinst hΓ hv0 hvty hget hv hv' hc hvv
      have hb' := PEqT.instantiate_pair hcl hinst
        (.letBinding _ _ _ _ hΓ hAty hvty) hb hbty hget' hv hv' hc hvv
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j),
          lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .letE _ _ _ _ _ _ _ hA' hv0' hb'
  | _, _, _, _, hΓ, .proof _ p q P Q hP hQ hp hq, _, j, t, v, v',
      hget, hv, hv', hc, _ => by
      have hvsub := hasTyT_substRemove_weaken hcl v hget hv
      have hv'sub := hasTyT_substRemove_weaken hcl v' hget hv'
      have hbr := ctxConvT_substRemove hcl hinst hΓ hget hv hv' hc
      exact .proof _ _ _ _ _
        (hasTyT_substS hcl hinst v t hP hget hvsub)
        (hasTyT_ctx hcl hbr (hasTyT_substS hcl hinst v' t hQ hget hv'sub))
        (hasTyT_substS hcl hinst v t hp hget hvsub)
        (hasTyT_ctx hcl hbr (hasTyT_substS hcl hinst v' t hq hget hv'sub))
  termination_by _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- head instantiation, `assumption` shape: `B ≈P B'` under `x : A` descends to
    `B[b] ≈P B'[b']` when `b ≈P b'`, both typed at `A`, convertible at `A` —
    the `*T` twin of `PEq.instantiate0` (which went through `convSubstA_cons`;
    here `instantiate_pair` at `j = 0` is the same pair, directly). -/
def PEqT.instantiate0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A b b' B B' T : Expr Nat}
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hb : HasTyT E n Γ b A) (hb' : HasTyT E n Γ b' A)
    (hc : ConvT E n Γ b b' A)
    (hB : HasTyT E n (.assumption A :: Γ) B T)
    (hpeq : PEqT E n (.assumption A :: Γ) B B')
    (hbb : PEqT E n Γ b b') :
    PEqT E n Γ (_root_.Rcic.Declarative.instantiate0 b B) (_root_.Rcic.Declarative.instantiate0 b' B') := by
  have h := PEqT.instantiate_pair hcl hinst hΓ hpeq hB (j := 0)
    (by simp) hb hb' hc hbb
  simpa [_root_.Rcic.Declarative.instantiate0, lift_zero] using h

/-- `≈P` under a `letBinding` removal — single-sided (the same `w` is removed
    from both sides), so no pair evidence and no ctx bridge: the `proof`
    leaf's typings substitute by `hasTyT_substLetS` on both sides, and
    `i = j` closes by `PEqT.refl`. -/
def PEqT.instantiateLet (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e e' : Expr Nat} → PEqT E n Γ e e' →
    {j : Nat} → {t w : Expr Nat} → Γ[j]? = some (.letBinding t w) →
    HasTyT E n (List.drop (j + 1) Γ) w t →
    PEqT E n (substRemove w j Γ) (instantiate j (lift 0 j w) e)
      (instantiate j (lift 0 j w) e')
  | _, _, _, .bvar _ i, j, _, w, _, _ => by
      by_cases hij : i = j
      · subst hij
        simp only [instantiate, if_pos rfl]
        exact PEqT.refl _
      · by_cases hlt : j < i
        · simp only [instantiate, if_neg hij, if_pos hlt]; exact .bvar _ _
        · simp only [instantiate, if_neg hij, if_neg hlt]; exact .bvar _ _
  | _, _, _, .sort _ l l' h, _, _, _, _, _ => .sort _ _ _ h
  | _, _, _, .const _ r ls ls' h, _, _, _, _, _ => .const _ _ _ _ h
  | _, _, _, .lit _ t, _, _, _, _, _ => .lit _ t
  | _, _, _, .app _ _ _ _ _ hf ha, j, t, w, hget, hw =>
      .app _ _ _ _ _
        (PEqT.instantiateLet hcl hinst hf hget hw)
        (PEqT.instantiateLet hcl hinst ha hget hw)
  | Γ, _, _, .lam _ A A' b b' hA hb, j, t, w, hget, hw => by
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.letBinding t w) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := PEqT.instantiateLet hcl hinst hb hget' hw
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .lam _ _ _ _ _ (PEqT.instantiateLet hcl hinst hA hget hw) hb'
  | Γ, _, _, .pi _ A A' B B' hA hB, j, t, w, hget, hw => by
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.letBinding t w) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hB' := PEqT.instantiateLet hcl hinst hB hget' hw
      simp only [substRemove_succ_cons, instDecl] at hB'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .pi _ _ _ _ _ (PEqT.instantiateLet hcl hinst hA hget hw) hB'
  | Γ, _, _, .letE _ A A' v0 v0' b b' hA hv hb, j, t, w, hget, hw => by
      have hget' : (LocalDecl.letBinding A v0 :: Γ)[j + 1]? = some (.letBinding t w) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := PEqT.instantiateLet hcl hinst hb hget' hw
      simp only [substRemove_succ_cons, instDecl] at hb'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j)]
      exact .letE _ _ _ _ _ _ _
        (PEqT.instantiateLet hcl hinst hA hget hw)
        (PEqT.instantiateLet hcl hinst hv hget hw) hb'
  | _, _, _, .proof _ p q P Q hP hQ hp hq, j, t, w, hget, hw => by
      have hwty := hasTyT_substRemove_weaken hcl w hget hw
      exact .proof _ _ _ _ _
        (hasTyT_substLetS hcl hinst t w hP hget hwty)
        (hasTyT_substLetS hcl hinst t w hQ hget hwty)
        (hasTyT_substLetS hcl hinst t w hp hget hwty)
        (hasTyT_substLetS hcl hinst t w hq hget hwty)
  termination_by _ _ _ h _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- head let-binding removal: `B ≈P B'` under `x := w : A` descends to
    `B[w] ≈P B'[w]`. -/
def PEqT.instantiate0Let (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A w B B' : Expr Nat}
    (hpeq : PEqT E n (.letBinding A w :: Γ) B B')
    (hw : HasTyT E n Γ w A) :
    PEqT E n Γ (_root_.Rcic.Declarative.instantiate0 w B) (_root_.Rcic.Declarative.instantiate0 w B') := by
  have h := PEqT.instantiateLet hcl hinst hpeq (j := 0) (by simp) hw
  simpa [_root_.Rcic.Declarative.instantiate0, lift_zero] using h

/-! ## (7) F-ι★-7: `≈P` across `CtxConvT`-related contexts -/

/-- `≈P` transports across pointwise-convertible contexts. Binder cases ride
    `CtxConvT.same` (both sides extend by the SAME left declaration); the
    `proof` leaf's four typings move by `hasTyT_ctx` — raw `HasTyT` data, no
    `Nonempty` barrier. -/
def PEqT.ctx_conv (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → {e e' : Expr Nat} →
    PEqT E n Γ e e' → PEqT E n Γ' e e'
  | _, _, _, _, _, .bvar _ i => .bvar _ _
  | _, _, _, _, _, .sort _ l l' h => .sort _ _ _ h
  | _, _, _, _, _, .const _ r ls ls' h => .const _ _ _ _ h
  | _, _, _, _, _, .lit _ t => .lit _ t
  | _, _, hcc, _, _, .app _ _ _ _ _ hf ha =>
      .app _ _ _ _ _ (PEqT.ctx_conv hcl hcc hf) (PEqT.ctx_conv hcl hcc ha)
  | _, _, hcc, _, _, .lam _ A A' b b' hA hb =>
      .lam _ _ _ _ _ (PEqT.ctx_conv hcl hcc hA)
        (PEqT.ctx_conv hcl (.same (.assumption A) hcc) hb)
  | _, _, hcc, _, _, .pi _ A A' B B' hA hB =>
      .pi _ _ _ _ _ (PEqT.ctx_conv hcl hcc hA)
        (PEqT.ctx_conv hcl (.same (.assumption A) hcc) hB)
  | _, _, hcc, _, _, .letE _ A A' v v' b b' hA hv hb =>
      .letE _ _ _ _ _ _ _ (PEqT.ctx_conv hcl hcc hA) (PEqT.ctx_conv hcl hcc hv)
        (PEqT.ctx_conv hcl (.same (.letBinding A v) hcc) hb)
  | _, _, hcc, _, _, .proof _ p q _ _ hP hQ hp hq =>
      .proof _ _ _ _ _
        (hasTyT_ctx hcl hcc hP) (hasTyT_ctx hcl hcc hQ)
        (hasTyT_ctx hcl hcc hp) (hasTyT_ctx hcl hcc hq)

/-- the design's `ctx_red`, `assumption` shape: one convertible declaration
    swaps the ambient context. Raw `HasTyT`/`ConvT` fields (the `*T` ctx
    relation is Type-valued — no `Nonempty` wrappers). -/
def PEqT.ctx_red (hcl : EnvClosed E) {Γ : LCtx} {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hA' : HasTyT E n Γ A' (.sort u))
    (hc : ConvT E n Γ A A' (.sort u)) {b b' : Expr Nat}
    (h : PEqT E n (.assumption A :: Γ) b b') :
    PEqT E n (.assumption A' :: Γ) b b' :=
  PEqT.ctx_conv hcl (.assumption (ctxConvT_refl Γ) hA hA' hc) h

/-- `ctx_red`, `letBinding` shape. -/
def PEqT.ctx_red_let (hcl : EnvClosed E) {Γ : LCtx} {A A' v v' : Expr Nat}
    {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hA' : HasTyT E n Γ A' (.sort u))
    (hc : ConvT E n Γ A A' (.sort u))
    (hv' : HasTyT E n Γ v' A') (hcv : ConvT E n Γ v v' A)
    {b b' : Expr Nat} (h : PEqT E n (.letBinding A v :: Γ) b b') :
    PEqT E n (.letBinding A' v' :: Γ) b b' :=
  PEqT.ctx_conv hcl (.letBinding (ctxConvT_refl Γ) hA hA' hc hv' hcv) h

/-! ## (8) the free fragment of transitivity -/

/-- leaf×leaf transitivity — the design's "endpoints' own Props": two proof
    leaves compose using only the outer endpoints' evidence. -/
def PEqT.trans_pp {Γ : LCtx} {p q r P Q Q' R : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (_hQ : HasTyT E n Γ Q (.sort .zero))
    (_hQ' : HasTyT E n Γ Q' (.sort .zero)) (hR : HasTyT E n Γ R (.sort .zero))
    (hp : HasTyT E n Γ p P) (_hq : HasTyT E n Γ q Q)
    (_hq' : HasTyT E n Γ q Q') (hr : HasTyT E n Γ r R) :
    PEqT E n Γ p r := .proof Γ p r P R hP hR hp hr

/-! ## (9) pins -/

/-- consumption pin: `liftT` under a binder — `insertAt` at `0` is the pushed
    declaration, the domain and body lift at `0`/`1`. -/
def pin_PEqT_liftT_pi (hcl : EnvClosed E)
    {Γ : LCtx} {A A' B B' : Expr Nat} (d : LocalDecl)
    (hA : PEqT E n Γ A A') (hB : PEqT E n (.assumption A :: Γ) B B') :
    PEqT E n (d :: Γ) (.pi (lift 0 1 A) (lift 1 1 B))
      (.pi (lift 0 1 A') (lift 1 1 B')) :=
  PEqT.liftT hcl d (c := 0) (.pi _ _ _ _ _ hA hB)

/-- consumption pin: `ctx_red` at `assumption` — a `ConvT`-related domain
    swaps the ambient context of an `≈P`. -/
def pin_PEqT_ctx_assumption (hcl : EnvClosed E)
    {Γ : LCtx} {A A' : Expr Nat} {u : Level} {b b' : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u)) (hA' : HasTyT E n Γ A' (.sort u))
    (hc : ConvT E n Γ A A' (.sort u))
    (h : PEqT E n (.assumption A :: Γ) b b') :
    PEqT E n (.assumption A' :: Γ) b b' :=
  PEqT.ctx_red hcl hA hA' hc h

/-- consumption pin: `instantiate0` at `bvar 0` — the removed entry IS the
    bound variable, so `B = bvar 0` instantiates to the replacements and the
    pair evidence `b ≈P b'` lands directly. -/
def pin_PEqT_instantiate0_bvar (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A b b' T : Expr Nat}
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hb : HasTyT E n Γ b A) (hb' : HasTyT E n Γ b' A)
    (hc : ConvT E n Γ b b' A)
    (hB : HasTyT E n (.assumption A :: Γ) (.bvar 0) T)
    (hbb : PEqT E n Γ b b') :
    PEqT E n Γ b b' := by
  have h := PEqT.instantiate0 hcl hinst hΓ hb hb' hc hB (.bvar _ 0) hbb
  simpa [instantiate0, instantiate, if_pos rfl] using h

#print axioms PEqT.liftT
#print axioms hasTyT_substRemove_weaken
#print axioms convT_substRemove_weaken
#print axioms peqT_substRemove_weaken
#print axioms hasTyT_inst_pair
#print axioms ctxConvT_substRemove
#print axioms PEqT.instantiate_pair
#print axioms PEqT.instantiate0
#print axioms PEqT.instantiateLet
#print axioms PEqT.instantiate0Let
#print axioms PEqT.ctx_conv
#print axioms PEqT.ctx_red
#print axioms PEqT.ctx_red_let
#print axioms PEqT.trans_pp
#print axioms pin_PEqT_liftT_pi
#print axioms pin_PEqT_ctx_assumption
#print axioms pin_PEqT_instantiate0_bvar

end Rcic.Declarative
