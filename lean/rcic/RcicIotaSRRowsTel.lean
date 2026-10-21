import rcic.RcicIotaSRRowsLemmas
import rcic.RcicIotaShapeAdapter
import rcic.RcicIATypedMinor
import rcic.RcicAnnEnvBridgeGroup

/-!
# DT-019 S1 — telescope and instantiation algebra for the direct ι-SR route

Pure term-level facts, no judgment: how `instPrefix`/`instTelK` move through
`policyPi`, how a lift over the middle binders cancels, the bvar-spine slices
the recursor's body and major domain reduce to, the level-instantiation
congruence on level-bounded terms, and the `ConvArgsT`-to-`instPrefix` bridge.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) `peelPis` ↔ `policyPi`, `instantiateLevels` through `policyPi` -/

theorem policyPi_of_peelPis : (k : Nat) → (T : Expr Nat) → {ds : List (Expr Nat)} →
    {b : Expr Nat} → peelPis k T = some (ds, b) → T = policyPi ds b
  | 0, T, ds, b, h => by
      simp only [peelPis] at h
      injection h with hp
      injection hp with hds hb
      subst hds; subst hb; rfl
  | k + 1, T, ds, b, h => by
      cases T with
      | pi A B =>
          cases hpeel : peelPis k B with
          | none => simp only [peelPis, hpeel] at h; exact Option.noConfusion h
          | some pr =>
              simp only [peelPis, hpeel] at h
              injection h with hpair
              injection hpair with hds hb
              cases pr with
              | mk ds' b' =>
                  subst hds; subst hb
                  simp only [policyPi]
                  rw [← policyPi_of_peelPis k B hpeel]
      | bvar _ => simp only [peelPis] at h; exact Option.noConfusion h
      | sort _ => simp only [peelPis] at h; exact Option.noConfusion h
      | const _ _ => simp only [peelPis] at h; exact Option.noConfusion h
      | app _ _ => simp only [peelPis] at h; exact Option.noConfusion h
      | lam _ _ => simp only [peelPis] at h; exact Option.noConfusion h
      | letE _ _ _ => simp only [peelPis] at h; exact Option.noConfusion h
      | lit _ => simp only [peelPis] at h; exact Option.noConfusion h

theorem instantiateLevels_policyPi (ls : List Level) :
    (ds : List (Expr Nat)) → (b : Expr Nat) →
    instantiateLevels ls (policyPi ds b) =
      policyPi (ds.map (instantiateLevels ls)) (instantiateLevels ls b)
  | [], _ => rfl
  | d :: ds, b => by
      simp only [policyPi, List.map_cons, instantiateLevels]
      rw [instantiateLevels_policyPi ls ds b]

/-! ## (2) `instTelK` through binders and telescopes -/

theorem instTelK_pi (k : Nat) : (as : List (Expr Nat)) → (A B : Expr Nat) →
    instTelK k as (.pi A B) = .pi (instTelK k as A) (instTelK (k + 1) as B)
  | [], _, _ => rfl
  | a :: as, A, B => by
      have hmerge : lift 0 1 (lift 0 (k + as.length) a) = lift 0 (k + as.length + 1) a :=
        lift_lift_merge 1 (k + as.length) 0 0 (Nat.le_refl 0) (by omega) a
      show instTelK k as (instantiate (k + as.length) (lift 0 (k + as.length) a) (.pi A B)) =
        .pi (instTelK k as (instantiate (k + as.length) (lift 0 (k + as.length) a) A))
          (instTelK (k + 1) as (instantiate (k + 1 + as.length) (lift 0 (k + 1 + as.length) a) B))
      simp only [instantiate]
      rw [hmerge, instTelK_pi k as, show k + as.length + 1 = k + 1 + as.length by omega]

theorem instTelK_sort (k : Nat) (u : Level) : (as : List (Expr Nat)) →
    instTelK k as (.sort u) = .sort u
  | [] => rfl
  | a :: as => by rw [instTelK_cons]; simp only [instantiate]; exact instTelK_sort k u as

/-- the domains of a telescope under `instTelK`: domain `j` at offset `k + j`. -/
def instDomsK (k : Nat) (as : List (Expr Nat)) : List (Expr Nat) → List (Expr Nat)
  | [] => []
  | d :: ds => instTelK k as d :: instDomsK (k + 1) as ds

theorem instDomsK_length (k : Nat) (as : List (Expr Nat)) :
    (ds : List (Expr Nat)) → (instDomsK k as ds).length = ds.length
  | [] => rfl
  | _ :: ds => by simp only [instDomsK, List.length_cons, instDomsK_length (k + 1) as ds]

theorem instDomsK_getElem? (k : Nat) (as : List (Expr Nat)) :
    (ds : List (Expr Nat)) → (i : Nat) →
    (instDomsK k as ds)[i]? = (ds[i]?).map (instTelK (k + i) as)
  | [], i => by simp [instDomsK]
  | d :: ds, 0 => by simp [instDomsK]
  | d :: ds, i + 1 => by
      simp only [instDomsK, List.getElem?_cons_succ]
      rw [instDomsK_getElem? (k + 1) as ds i, show k + 1 + i = k + (i + 1) by omega]

theorem instTelK_policyPi (as : List (Expr Nat)) (U : Expr Nat) :
    (ds : List (Expr Nat)) → (k : Nat) →
    instTelK k as (policyPi ds U) =
      policyPi (instDomsK k as ds) (instTelK (k + ds.length) as U)
  | [], k => by simp only [policyPi, instDomsK, List.length_nil, Nat.add_zero]
  | d :: ds, k => by
      simp only [policyPi, instDomsK, List.length_cons]
      rw [instTelK_pi, instTelK_policyPi as U ds (k + 1),
        show k + 1 + ds.length = k + (ds.length + 1) by omega]

theorem instPrefix_policyPi (as : List (Expr Nat)) (ds : List (Expr Nat)) (U : Expr Nat) :
    instPrefix as (policyPi ds U) =
      policyPi (instDomsK 0 as ds) (instTelK ds.length as U) := by
  rw [instPrefix_eq_instTelK, instTelK_policyPi, Nat.zero_add]

/-! ## (3) lifts over the middle binders cancel -/

theorem instTelK_lift_cancel (k : Nat) : (as : List (Expr Nat)) → (e : Expr Nat) →
    instTelK k as (lift k as.length e) = e
  | [], e => by simp only [instTelK, List.length_nil, lift_zero]
  | a :: as, e => by
      rw [instTelK_cons, List.length_cons]
      have hc := instantiate_lift_cancel (as.length + 1) k (k + as.length)
        (lift 0 (k + as.length) a) (Nat.le_add_right k as.length) (by omega) e
      rw [hc, show as.length + 1 - 1 = as.length by omega]
      exact instTelK_lift_cancel k as e

theorem instTelK_lift_mid (m k : Nat) : (as : List (Expr Nat)) → (F : Expr Nat) →
    instTelK (m + k) as (lift k m F) = lift k m (instTelK k as F)
  | [], _ => rfl
  | a :: as, F => by
      rw [instTelK_cons, instTelK_cons]
      have hh := lift_instantiate_high m k (k + as.length) (lift 0 (k + as.length) a)
        (Nat.le_add_right k as.length) F
      have hmerge : lift k m (lift 0 (k + as.length) a) = lift 0 (k + as.length + m) a :=
        lift_lift_merge m (k + as.length) 0 k (Nat.zero_le k) (by omega) a
      rw [hmerge] at hh
      rw [show m + k + as.length = m + (k + as.length) by omega,
        show k + as.length + m = m + (k + as.length) by omega] at *
      rw [← hh]
      exact instTelK_lift_mid m k as _

/-- a term under the middle binders, lifted over them, instantiated by the whole
    outer list, is the term instantiated by the outer list without the middle. -/
theorem instPrefix_lift_mid (p mid fs : List (Expr Nat)) (F : Expr Nat) :
    instPrefix (p ++ mid ++ fs) (lift fs.length mid.length F) = instPrefix (p ++ fs) F := by
  rw [List.append_assoc, instPrefix_append_instTelK (mid ++ fs) p,
    instPrefix_append_instTelK fs mid, instPrefix_append_instTelK fs p,
    List.length_append, instTelK_lift_mid, instTelK_lift_cancel]

/-! ## (4) bvar spine slices -/

theorem bvarSpine_getElem? (n i : Nat) (hi : i < n) :
    (bvarSpine n)[i]? = some (.bvar (n - 1 - i)) := by
  simp only [bvarSpine, List.getElem?_map, List.getElem?_reverse (by simpa using hi : i < (List.range n).length),
    List.length_range, List.getElem?_range (by omega : n - 1 - i < n), Option.map_some']

theorem bvarSpine_drop (a b : Nat) : (bvarSpine (a + b)).drop a = bvarSpine b := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases hi : i < b
  · rw [bvarSpine_getElem? (a + b) (a + i) (by omega), bvarSpine_getElem? b i hi]
    congr 2
    omega
  · have h1 : (bvarSpine (a + b))[a + i]? = none := by
      rw [List.getElem?_eq_none]
      simp only [bvarSpine, List.length_map, List.length_reverse, List.length_range]
      omega
    have h2 : (bvarSpine b)[i]? = none := by
      rw [List.getElem?_eq_none]
      simp only [bvarSpine, List.length_map, List.length_reverse, List.length_range]
      omega
    rw [h1, h2]

/-- `(List.range n).reverse.map (fun i => .bvar (i + off))` is the bvar spine shifted by
    `off`: the form `policyParameterLocals` / the recursor index locals take. -/
theorem shiftedSpine_getElem? (n off i : Nat) (hi : i < n) :
    ((List.range n).reverse.map (fun i => (Expr.bvar (i + off) : Expr Nat)))[i]? =
      some (.bvar (n - 1 - i + off)) := by
  simp only [List.getElem?_map, List.getElem?_reverse (by simpa using hi : i < (List.range n).length),
    List.length_range, List.getElem?_range (by omega : n - 1 - i < n), Option.map_some']

/-- the shifted spine of length `n` at offset `off`, instantiated by `args` of length
    `off' + n + off`: the slice `(args.drop off').take n`. -/
theorem instPrefix_shiftedSpine (args : List (Expr Nat)) (n off off' : Nat)
    (hlen : args.length = off' + n + off) :
    ((List.range n).reverse.map (fun i => (Expr.bvar (i + off) : Expr Nat))).map (instPrefix args) =
      (args.drop off').take n := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [List.getElem?_map, shiftedSpine_getElem? n off i hi, Option.map_some']
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop]
    have hget : args[args.length - 1 - (n - 1 - i + off)]? = args[off' + i]? := by
      congr 1; omega
    have hidx : off' + i < args.length := by omega
    rw [List.getElem?_eq_getElem hidx]
    congr 1
    apply instPrefix_bvar_lt (by omega)
    rw [hget, List.getElem?_eq_getElem hidx]
  · have h1 : ((List.range n).reverse.map (fun i => (Expr.bvar (i + off) : Expr Nat)))[i]? = none := by
      rw [List.getElem?_eq_none]; simp only [List.length_map, List.length_reverse, List.length_range]; omega
    rw [List.getElem?_map, h1, Option.map_none']
    symm
    rw [List.getElem?_eq_none]
    simp only [List.length_take, List.length_drop]
    omega

/-! ## (5) level instantiation on level-bounded terms is determined below the bound -/

theorem instLevel_congr_bounded {L L' : List Level} {k : Nat}
    (h : ∀ i, i < k → instLevel L (.param i) = instLevel L' (.param i)) :
    (l : Level) → levelBounded k l = true → instLevel L l = instLevel L' l
  | .zero, _ => rfl
  | .succ l, hb => by
      simp only [instLevel, lvlSubst]
      have := instLevel_congr_bounded h l hb
      simp only [instLevel] at this
      rw [this]
  | .max a b, hb => by
      simp only [levelBounded, Bool.and_eq_true] at hb
      have ha := instLevel_congr_bounded h a hb.1
      have hb' := instLevel_congr_bounded h b hb.2
      simp only [instLevel, lvlSubst] at ha hb' ⊢
      rw [ha, hb']
  | .imax a b, hb => by
      simp only [levelBounded, Bool.and_eq_true] at hb
      have ha := instLevel_congr_bounded h a hb.1
      have hb' := instLevel_congr_bounded h b hb.2
      simp only [instLevel, lvlSubst] at ha hb' ⊢
      rw [ha, hb']
  | .param i, hb => by
      simp only [levelBounded, decide_eq_true_eq] at hb
      exact h i hb

theorem levels_map_congr_bounded {L L' : List Level} {k : Nat}
    (h : ∀ i, i < k → instLevel L (.param i) = instLevel L' (.param i)) :
    (ms : List Level) → levelsBounded k ms = true →
    ms.map (instLevel L) = ms.map (instLevel L')
  | [], _ => rfl
  | l :: ms, hb => by
      simp only [levelsBounded, Bool.and_eq_true] at hb
      simp only [List.map_cons, instLevel_congr_bounded h l hb.1,
        levels_map_congr_bounded h ms hb.2]

theorem instantiateLevels_congr_bounded {L L' : List Level} {k : Nat}
    (h : ∀ i, i < k → instLevel L (.param i) = instLevel L' (.param i)) :
    (e : Expr Nat) → exprLevelsBounded k e = true →
    instantiateLevels L e = instantiateLevels L' e
  | .bvar _, _ => rfl
  | .sort l, hb => by
      simp only [instantiateLevels, instLevel_congr_bounded h l hb]
  | .const r ms, hb => by
      simp only [instantiateLevels, levels_map_congr_bounded h ms hb]
  | .app f a, hb => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      simp only [instantiateLevels, instantiateLevels_congr_bounded h f hb.1,
        instantiateLevels_congr_bounded h a hb.2]
  | .lam A b, hb => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      simp only [instantiateLevels, instantiateLevels_congr_bounded h A hb.1,
        instantiateLevels_congr_bounded h b hb.2]
  | .pi A b, hb => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      simp only [instantiateLevels, instantiateLevels_congr_bounded h A hb.1,
        instantiateLevels_congr_bounded h b hb.2]
  | .letE A v b, hb => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at hb
      simp only [instantiateLevels, instantiateLevels_congr_bounded h A hb.1.1,
        instantiateLevels_congr_bounded h v hb.1.2, instantiateLevels_congr_bounded h b hb.2]
  | .lit _, _ => rfl

/-- the canonical family vector instantiated at `ls` agrees with `ls` on every parameter
    below the family arity. -/
theorem famLevels_instLevel_param (ls : List Level) (k : Nat) (hk : k ≤ ls.length) :
    ∀ i, i < k → instLevel (((List.range k).map Level.param).map (instLevel ls)) (.param i) =
      instLevel ls (.param i) := by
  intro i hi
  rw [instLevel_param_lt _ i (by simp only [List.length_map, List.length_range]; exact hi)]
  simp only [List.getElem_map, List.getElem_range]

/-! ## (6) contexts: level instantiation of a prefix context, well-formedness of a prefix -/

theorem instLvlsCtx_policyPrefixContext (ls : List Level) (ds : List (Expr Nat)) (i : Nat) :
    instLvlsCtx ls (policyPrefixContext ds i) =
      policyPrefixContext (ds.map (instantiateLevels ls)) i := by
  simp only [instLvlsCtx, policyPrefixContext, List.map_map, List.map_take, List.map_reverse]
  rfl

theorem instLvlsCtx_append (ls : List Level) (Δ Γ : LCtx) :
    instLvlsCtx ls (Δ ++ Γ) = instLvlsCtx ls Δ ++ instLvlsCtx ls Γ := by
  simp only [instLvlsCtx, List.map_append]

theorem instLvlsCtx_nil (ls : List Level) : instLvlsCtx ls [] = [] := rfl

theorem policyPrefixContext_length (ds : List (Expr Nat)) (k : Nat) (hk : k ≤ ds.length) :
    (policyPrefixContext ds k).length = k := by
  simp only [policyPrefixContext, List.length_map, List.length_reverse, List.length_take]
  omega

/-- `outerDom` of the reversed prefix: the `i`-th outermost binder of
    `(ds.take k).reverse` is `ds[i]`. -/
theorem outerDom_take_reverse (ds : List (Expr Nat)) (k i : Nat) (hk : k ≤ ds.length)
    (hi : i < k) : outerDom (ds.take k).reverse i = ds[i]'(by omega) := by
  have hlen : (ds.take k).length = k := by
    simp only [List.length_take]; omega
  have hlenr : (ds.take k).reverse.length = k := by rw [List.length_reverse, hlen]
  simp only [outerDom, List.getD_eq_getElem?_getD, hlenr]
  rw [List.getElem?_reverse (by rw [hlen]; omega), hlen,
    show k - 1 - (k - 1 - i) = i by omega, List.getElem?_take_of_lt hi,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- a prefix context under `Γ` is well-formed when every domain is sort-typed in its own
    prefix context under `Γ`. -/
def ctxWfT_prefix {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (ds : List (Expr Nat)) :
    (k : Nat) → (hk : k ≤ ds.length) →
    (∀ i (hi : i < k), ∃ u, Nonempty (HasTyT E n (policyPrefixContext ds i ++ Γ)
      (ds[i]'(by omega)) (.sort u))) →
    Nonempty (CtxWfT E n (policyPrefixContext ds k ++ Γ))
  | 0, _, _ => ⟨by simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
      List.map_nil, List.nil_append] using hΓ⟩
  | k + 1, hk, h => by
      obtain ⟨hprev⟩ := ctxWfT_prefix hΓ ds k (Nat.le_of_succ_le hk)
        (fun i hi => h i (Nat.lt_succ_of_lt hi))
      obtain ⟨u, ⟨hd⟩⟩ := h k (Nat.lt_succ_self k)
      rw [policyPrefixContext_succ ds k (by omega), List.cons_append]
      exact ⟨.assumption _ _ u hprev hd⟩

/-! ## (7) the `ConvArgsT` → `instPrefix` bridge -/

/-- pointwise argument conversions along a telescope, re-indexed at the
    `instPrefix`-instantiated domains. -/
theorem convArgsT_instPrefix {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {T : Expr Nat} → {xs xs' : List (Expr Nat)} → ConvArgsT E n Γ T xs xs' →
    (ds : List (Expr Nat)) → (U : Expr Nat) → T = policyPi ds U →
    ∀ i x x' d, xs[i]? = some x → xs'[i]? = some x' → ds[i]? = some d →
      Nonempty (ConvT E n Γ x x' (instPrefix (xs.take i) d))
  | _, _, _, .nil _, _, _, _, i, x, _, _, hx, _, _ => by simp at hx
  | _, _, _, .cons A B f f' fs fs' h hs, ds, U, hT, i, x, x', d, hx, hx', hd => by
      cases ds with
      | nil => simp at hd
      | cons d₀ ds' =>
          simp only [policyPi] at hT
          injection hT with hA hB
          subst hA; subst hB
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx' hd
              subst hx; subst hx'; subst hd
              obtain ⟨c⟩ := h
              exact ⟨by simpa only [List.take_zero, instPrefix_nil] using c⟩
          | succ j =>
              simp only [List.getElem?_cons_succ] at hx hx' hd
              have hs' : ConvArgsT E n Γ (policyPi (instDomsT 0 f ds')
                  (instantiate (0 + ds'.length) (lift 0 ds'.length f) U)) fs fs' := by
                rw [instantiate0, instantiate_policyPi] at hs; exact hs
              have hj : j < fs.length := by
                have := List.getElem?_eq_some_iff.mp hx
                exact this.1
              have hjd : j < ds'.length := by
                have := List.getElem?_eq_some_iff.mp hd
                exact this.1
              have hget : (instDomsT 0 f ds')[j]? =
                  some (instantiate (0 + j) (lift 0 j f) (ds'[j]'hjd)) := by
                rw [List.getElem?_eq_getElem (by rw [length_instDomsT]; exact hjd),
                  getElem_instDomsT]
              obtain ⟨c⟩ := convArgsT_instPrefix hs' (instDomsT 0 f ds') _ rfl j x x' _ hx hx' hget
              refine ⟨?_⟩
              rw [List.take_succ_cons, instPrefix_cons, List.length_take,
                Nat.min_eq_left (Nat.le_of_lt hj)]
              have hd' : d = ds'[j]'hjd := by
                rw [List.getElem?_eq_getElem hjd] at hd
                exact (Option.some.inj hd).symm
              rw [hd']
              rw [Nat.zero_add] at c
              exact c

end Rcic.Declarative
