import rcic.RcicIARecMotive
import rcic.RcicIARecUnique
import rcic.RcicIATypedMinor
import rcic.RcicSubstT
import rcic.RcicParRedSRTyped
import rcic.RcicTypedInstPrefix
import rcic.RcicTypedConvTerm
import rcic.RcicAnnSemPrefixRows
import rcic.RcicTypedValidity
import rcic.RcicAdmit

namespace Rcic.Declarative

/-- a telescope's domains instantiated at their own depths. -/
def instDomsT : Nat → Expr Nat → List (Expr Nat) → List (Expr Nat)
  | _, _, [] => []
  | k, s, D :: ds => instantiate k s D :: instDomsT (k + 1) (lift 0 1 s) ds

theorem length_instDomsT : (k : Nat) → (s : Expr Nat) → (ds : List (Expr Nat)) →
    (instDomsT k s ds).length = ds.length
  | _, _, [] => rfl
  | k, s, _ :: ds => congrArg Nat.succ (length_instDomsT (k + 1) (lift 0 1 s) ds)

/-- an instantiation moves under a telescope: the domains at their depths, the body past all of them. -/
theorem instantiate_policyPi : (ds : List (Expr Nat)) → (k : Nat) → (s body : Expr Nat) →
    instantiate k s (policyPi ds body) =
      policyPi (instDomsT k s ds) (instantiate (k + ds.length) (lift 0 ds.length s) body)
  | [], k, s, body => by simp only [policyPi, instDomsT, List.length_nil, Nat.add_zero, lift_zero]
  | D :: ds, k, s, body => by
      show Expr.pi (instantiate k s D) (instantiate (k + 1) (lift 0 1 s) (policyPi ds body)) = _
      rw [instantiate_policyPi ds (k + 1) (lift 0 1 s) body,
        lift_lift_merge ds.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _)]
      simp only [policyPi, instDomsT, List.length_cons, Nat.add_assoc, Nat.add_comm 1 ds.length]

/-- a head typed at `policyPi Is Body`, applied to arguments typed along `policyPi Is (Sort l)` (the same
    domains), is typed at `Body` with the arguments substituted (`instPrefix`). -/
def hasTyT_foldApps_args {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (Is : List (Expr Nat)) → (args : List (Expr Nat)) → args.length = Is.length →
    (Body h : Expr Nat) → {T : Expr Nat} → T = policyPi Is (.sort l) →
    ArgsTyT E n Γ T args → HasTyT E n Γ h (policyPi Is Body) →
    HasTyT E n Γ (foldApps h args) (instPrefix args Body)
  | [], [], _, Body, h, _, _, _, hh => hh
  | I :: Is, a :: as, hlen, Body, h, T, hT, hargs, hh =>
      match hargs, hT with
      | .cons A B _ _ ha tl, hT' => by
          simp only [policyPi] at hT'
          injection hT' with hA hB
          subst hA hB
          have happ := HasTyT.app _ _ _ _ _ hh ha
          rw [instantiate0, instantiate_policyPi] at happ
          have htl : instantiate0 a (policyPi Is (.sort l)) =
              policyPi (instDomsT 0 a Is) (.sort l) := by
            rw [instantiate0, instantiate_policyPi]; rfl
          have hlen' : as.length = Is.length := Nat.succ.inj hlen
          have ih := hasTyT_foldApps_args (instDomsT 0 a Is) as (by rw [length_instDomsT, hlen'])
            (instantiate (0 + Is.length) (lift 0 Is.length a) Body) (.app h a) htl tl happ
          rw [instPrefix_cons, hlen']
          show HasTyT E n Γ (foldApps (.app h a) as) _
          simpa only [Nat.zero_add] using ih
  | [], _ :: _, hlen, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hlen).elim
  | _ :: _, [], hlen, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hlen.symm).elim

theorem instTel_sort (l : Level) : (args : List (Expr Nat)) → instTel args (.sort l) = .sort l
  | [] => rfl
  | a :: as => by simp only [instTel_cons, instantiate]; exact instTel_sort l as

/-- `instDomsT`'s `i`-th output is `ds[i]` instantiated at index `k + i` by the `i`-lifted
    substitution. -/
theorem getElem_instDomsT (k : Nat) (s : Expr Nat) (ds : List (Expr Nat)) (i : Nat)
    (hi : i < ds.length) :
    (instDomsT k s ds)[i]'(by rw [length_instDomsT]; exact hi) =
      instantiate (k + i) (lift 0 i s) ds[i] := by
  induction ds generalizing k s i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons D ds ih =>
      cases i with
      | zero => simp [instDomsT, lift_zero]
      | succ i' =>
          show (instDomsT (k + 1) (lift 0 1 s) ds)[i']'(
            by rw [length_instDomsT]; exact Nat.lt_of_succ_lt_succ hi) = _
          rw [ih (k + 1) (lift 0 1 s) i' (Nat.lt_of_succ_lt_succ hi)]
          have h1 : k + 1 + i' = k + (i' + 1) := by omega
          have h2 : lift 0 i' (lift 0 1 s) = lift 0 (i' + 1) s := by
            rw [lift_lift_merge i' 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]
          rw [h1, h2, List.getElem_cons_succ]

/-- per-argument typing along a `policyPi` telescope: `args[j]` is typed against
    `doms[j]` with the earlier arguments `instPrefix`-instantiated. -/
def argsTyT_getElem {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (doms args : List (Expr Nat)) → (hl : args.length = doms.length) →
    (T : Expr Nat) → T = policyPi doms (.sort l) →
    ArgsTyT E n Γ T args →
    ∀ j (hj : j < args.length),
      HasTyT E n Γ args[j] (instPrefix (args.take j) (doms[j]'(by omega)))
  | [], args, hl, _, _, _, j, hj => absurd hj (by simp only [List.length_nil] at hl; omega)
  | D :: doms, [], hl, _, _, _, _, _ => absurd hl (by simp)
  | D :: doms, a :: as, hl, T, hT, h, j, hj =>
      match h, hT with
      | .cons A B _ _ ha tl, hT' => by
          have hT'' : Expr.pi A B = Expr.pi D (policyPi doms (.sort l)) := hT'
          injection hT'' with hA hB
          subst hA hB
          cases j with
          | zero => exact ha
          | succ j' =>
              have hlen : as.length = doms.length := by
                simp only [List.length_cons] at hl; omega
              have hl' : as.length = (instDomsT 0 a doms).length := by
                rw [length_instDomsT]; exact hlen
              have htl : ArgsTyT E n Γ (policyPi (instDomsT 0 a doms) (.sort l)) as := by
                have := tl
                rw [instantiate0, instantiate_policyPi] at this
                exact this
              have hstep := argsTyT_getElem (instDomsT 0 a doms) as hl' _ rfl htl j'
                (Nat.lt_of_succ_lt_succ hj)
              rw [getElem_instDomsT, Nat.zero_add] at hstep
              show HasTyT E n Γ (as[j']'(by simp only [List.length_cons] at hj; omega))
                (instPrefix (a :: as.take j')
                  (doms[j']'(by simp only [List.length_cons] at hl hj; omega)))
              rw [instPrefix_cons, List.length_take,
                Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_succ_lt_succ hj))]
              exact hstep

/-- building an `ArgsTyT` from per-argument `instPrefix`-domain evidence — the inverse
    direction of `argsTyT_getElem`. -/
def argsTyT_mk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (doms args : List (Expr Nat)) → (hl : args.length = doms.length) →
    (∀ j (hj : j < args.length),
      HasTyT E n Γ args[j] (instPrefix (args.take j) (doms[j]'(by omega)))) →
    ArgsTyT E n Γ (policyPi doms (.sort l)) args
  | [], [], _, _ => .nil l
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | D :: doms, a :: as, hl, h =>
      .cons D (policyPi doms (.sort l)) a as (h 0 (Nat.zero_lt_succ _))
        (by
          have hl' : as.length = (instDomsT 0 a doms).length := by
            rw [length_instDomsT]; simp only [List.length_cons] at hl; omega
          show ArgsTyT E n Γ (instantiate0 a (policyPi doms (.sort l))) as
          rw [instantiate0, instantiate_policyPi]
          exact argsTyT_mk (instDomsT 0 a doms) as hl' (fun j hj => by
            have hstep := h (j + 1) (Nat.succ_lt_succ hj)
            rw [List.take_succ_cons, List.getElem_cons_succ, instPrefix_cons,
              List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hstep
            rw [getElem_instDomsT, Nat.zero_add]
            exact hstep))

/-- `argsTyT_mk` with `Nonempty`-paid per-argument evidence — for `Prop`-sourced
    typings (e.g. `endpoints3` of `ConvArgsT` spine conversions, the `.drecD`
    route).  Every `Nonempty` elimination happens at `Nonempty`-valued goals, so
    the assembled `ArgsTyT` data stays choice-free. -/
def argsTyT_mk_ne {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (doms args : List (Expr Nat)) → (hl : args.length = doms.length) →
    (∀ j (hj : j < args.length),
      Nonempty (HasTyT E n Γ args[j]
        (instPrefix (args.take j) (doms[j]'(by omega))))) →
    Nonempty (ArgsTyT E n Γ (policyPi doms (.sort l)) args)
  | [], [], _, _ => ⟨.nil l⟩
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | D :: doms, a :: as, hl, h => by
      obtain ⟨ha⟩ := h 0 (Nat.zero_lt_succ _)
      obtain ⟨tl⟩ := argsTyT_mk_ne (instDomsT 0 a doms) as (by
          rw [length_instDomsT]; simp only [List.length_cons] at hl; omega)
        (fun j hj => by
          obtain ⟨hstep⟩ := h (j + 1) (Nat.succ_lt_succ hj)
          rw [List.take_succ_cons, List.getElem_cons_succ, instPrefix_cons,
            List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hstep
          rw [getElem_instDomsT, Nat.zero_add]
          exact ⟨hstep⟩)
      refine ⟨.cons D (policyPi doms (.sort l)) a as ha ?_⟩
      show ArgsTyT E n Γ (instantiate0 a (policyPi doms (.sort l))) as
      rw [instantiate0, instantiate_policyPi]
      exact tl

/-- `instPrefix` splits at an argument append: the head group runs as the `instTelK`
    offset chain for the tail. -/
theorem instPrefix_append_instTelK (bs : List (Expr Nat)) : (as : List (Expr Nat)) →
    (e : Expr Nat) →
    instPrefix (as ++ bs) e = instPrefix bs (instTelK bs.length as e)
  | [], e => rfl
  | a :: as, e => by
      show instPrefix (as ++ bs)
          (instantiate (as ++ bs).length (lift 0 (as ++ bs).length a) e) = _
      rw [List.length_append, Nat.add_comm as.length bs.length]
      show instPrefix (as ++ bs)
          (instantiate (bs.length + as.length) (lift 0 (bs.length + as.length) a) e) = _
      rw [instPrefix_append_instTelK bs as]
      rfl

/-- `instPrefix` on a sort is the identity. -/
theorem instPrefix_sort (args : List (Expr Nat)) (l : Level) :
    instPrefix args (.sort l) = .sort l := by
  induction args with
  | nil => rfl
  | cons a as ih =>
      show instPrefix as (instantiate as.length (lift 0 as.length a) (.sort l)) = _
      exact ih

/-- `descSpine` IS `policyParameterLocals` (pointwise `B + t`/`t + B`). -/
theorem descSpine_eq_ppL (B i : Nat) : descSpine B i = policyParameterLocals i B := by
  simp only [descSpine, policyParameterLocals]
  apply List.map_congr_left
  intro t _
  congr 1; omega

theorem getElem_descSpine (B n j : Nat) (hj : j < n) :
    (descSpine B n)[j]'(by simp [descSpine]; omega) = .bvar (B + (n - 1 - j)) := by
  simp only [descSpine, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range, List.length_map]

/-- `descSpine`'s `i`-prefix is a `descSpine` at a shifted base. -/
theorem descSpine_take (B n i : Nat) (hi : i ≤ n) :
    (descSpine B n).take i = descSpine (B + n - i) i := by
  apply List.ext_getElem (by simp [descSpine, List.length_take, descSpine_length]; omega)
  intro j hj1 hj2
  have hl1 : j < n := by
    simp only [List.length_take, descSpine_length] at hj1; omega
  have hl2 : j < i := by
    simp only [descSpine_length] at hj2; exact hj2
  rw [List.getElem_take, getElem_descSpine B n j hl1,
    getElem_descSpine (B + n - i) i j hl2]
  exact congrArg Expr.bvar (by omega)

/-- a `plainCtxT` lookup past the plain prefix reaches the tail context. -/
theorem plainCtxT_getElem?_ge : (pre : List FieldT) → (Γ : LCtx) → (v : Nat) →
    (hv : plainIdxT pre 0 ≤ v) →
    (plainCtxT pre Γ).get? v = Γ.get? (v - plainIdxT pre 0)
  | [], Γ, v, _ => by simp [plainCtxT, plainIdxT]
  | .plain D u :: fs, Γ, v, hv => by
      have hpc : plainIdxT (FieldT.plain D u :: fs) 0 = plainIdxT fs 0 + 1 := by
        show plainIdxT fs 1 = _; rw [show (1 : Nat) = 0 + 1 from rfl, plainIdxT_add]
      show (plainCtxT fs (.assumption D :: Γ)).get? v =
        Γ.get? (v - plainIdxT (FieldT.plain D u :: fs) 0)
      rw [hpc, plainCtxT_getElem?_ge fs (.assumption D :: Γ) v (by omega)]
      have hw : v - plainIdxT fs 0 = (v - (plainIdxT fs 0 + 1)) + 1 := by omega
      rw [hw, List.get?_cons_succ]
  | .drec _ :: fs, Γ, v, hv => plainCtxT_getElem?_ge fs Γ v hv
  | .drecD _ _ :: fs, Γ, v, hv => plainCtxT_getElem?_ge fs Γ v hv

/-- `telCtxT`'s `np - 1 - j`-th entry is `params[j]`'s assumption decl. -/
theorem telCtxT_getElem?_rev (params : List (Expr Nat × Level)) (j : Nat)
    (hj : j < params.length) :
    (telCtxT params).get? (params.length - 1 - j) =
      some (.assumption params[j].1) := by
  rw [telCtxT, List.get?_eq_getElem?,
    List.getElem?_reverse (by rw [List.length_map]; omega), List.length_map,
    show params.length - 1 - (params.length - 1 - j) = j from by omega]
  rw [List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

/-- the parameter local `bvar (np-1-j+pc)`'s lookup in `plainCtxT pre (telCtxT params)`:
    `params[j]`'s domain lifted past `np - j + pc` binders. -/
theorem lookupType_plainCtxT_param (pre : List FieldT)
    (params : List (Expr Nat × Level)) (np j pc : Nat)
    (hnp : params.length = np) (hpc : plainIdxT pre 0 = pc) (hj : j < np) :
    lookupType (plainCtxT pre (telCtxT params)) (np - 1 - j + pc) =
      some (lift 0 (np - j + pc) params[j].1) := by
  have hget : (plainCtxT pre (telCtxT params)).get? (np - 1 - j + pc) =
      some (.assumption params[j].1) := by
    rw [plainCtxT_getElem?_ge pre _ _ (by omega)]
    have hsub : np - 1 - j + pc - plainIdxT pre 0 = np - 1 - j := by omega
    simp only [hsub]
    have hrev := telCtxT_getElem?_rev params j (by rw [hnp]; exact hj)
    simp only [hnp] at hrev
    exact hrev
  simp only [lookupType, hget]
  congr 2; omega

/-- `policyPi`-telescopes ending in sorts are injective in the domain list. -/
theorem policyPi_sort_inj : (ds ds' : List (Expr Nat)) → (l l' : Level) →
    policyPi ds (.sort l) = policyPi ds' (.sort l') → ds = ds'
  | [], [], _, _, _ => rfl
  | [], _ :: _, l, l', h => by
      have h' : Expr.sort l = Expr.pi _ _ := h
      exact Expr.noConfusion h'
  | _ :: _, [], l, l', h => by
      have h' : Expr.pi _ _ = Expr.sort l' := h
      exact Expr.noConfusion h
  | D :: ds, D' :: ds', l, l', h => by
      have h' : Expr.pi D (policyPi ds (.sort l)) =
          Expr.pi D' (policyPi ds' (.sort l')) := h
      injection h' with hD hB
      rw [hD, policyPi_sort_inj ds ds' l l' hB]

/-- `liftDomsT c 1 ds = ds` reads off per-domain fixity `lift (c + j) 1 ds[j] = ds[j]`. -/
theorem liftDomsT_one_dom_lift (c : Nat) : (ds : List (Expr Nat)) →
    liftDomsT c 1 ds = ds →
    ∀ j (hj : j < ds.length), lift (c + j) 1 ds[j] = ds[j]
  | [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | D :: ds, h, j, hj => by
      have h' : lift c 1 D :: liftDomsT (c + 1) 1 ds = D :: ds := h
      injection h' with hD hds
      cases j with
      | zero => exact hD
      | succ j' =>
          have := liftDomsT_one_dom_lift (c + 1) ds hds j' (by
            simp only [List.length_cons] at hj; omega)
          show lift (c + (j' + 1)) 1 (ds[j']'(by simp only [List.length_cons] at hj; omega)) =
            ds[j']'(by simp only [List.length_cons] at hj; omega)
          rw [show c + (j' + 1) = c + 1 + j' from by omega]
          exact this

/-- the parameter-locals spine `ppL np pc` plus index arguments, typed along the family's
    `params ++ indices` telescope in the plain context `plainCtxT pre (telCtxT params)`:
    each parameter local is the telescope's own binder (`lookupType`), each index argument's
    residual domain is `instPrefix`-of-`descSpine` = `lift k pc`, read back through
    `argsTyT_getElem` on `hidx`. `hbnd` is the family's stored-type closedness, per domain. -/
def argsTyT_paramLocals {E : ResolvedEnv} {n : Nat} {l : Level}
    (pre : List FieldT) (params : List (Expr Nat × Level)) (indicesF idx : List (Expr Nat))
    (np pc : Nat) (hnp : params.length = np) (hpc : plainIdxT pre 0 = pc)
    (hl : idx.length = indicesF.length)
    (hbnd : ∀ j (hj : j < (params.map Prod.fst ++ indicesF).length),
      lift j 1 (params.map Prod.fst ++ indicesF)[j] =
        (params.map Prod.fst ++ indicesF)[j])
    (hidx : ArgsTyT E n (plainCtxT pre (telCtxT params))
      (policyPi (liftDomsT 0 pc indicesF) (.sort l)) idx) :
    ArgsTyT E n (plainCtxT pre (telCtxT params))
      (policyPi (params.map Prod.fst ++ indicesF) (.sort l))
      (policyParameterLocals np pc ++ idx) := by
  have hpplen : (policyParameterLocals np pc).length = np := policyParameterLocals_length _ _
  have hpmlen : (params.map Prod.fst).length = np := by rw [List.length_map, hnp]
  refine argsTyT_mk (params.map Prod.fst ++ indicesF) (policyParameterLocals np pc ++ idx)
    (by rw [List.length_append, hpplen, List.length_append, hpmlen, hl]) ?_
  intro j hj
  by_cases hjp : j < np
  · have hlook : lookupType (plainCtxT pre (telCtxT params)) (np - 1 - j + pc) =
        some (lift 0 (np - j + pc) params[j].1) :=
      lookupType_plainCtxT_param pre params np j pc hnp hpc hjp
    have hb : lift j 1 params[j].1 = params[j].1 := by
      have hb0 := hbnd j (by simp only [List.length_append, hpmlen]; omega)
      rwa [List.getElem_append_left (by rw [hpmlen]; exact hjp), List.getElem_map] at hb0
    rw [List.getElem_append_left (by rw [hpplen]; exact hjp)]
    have htk : (policyParameterLocals np pc ++ idx).take j = descSpine (pc + np - j) j := by
      apply List.ext_getElem (by
        rw [List.length_take, List.length_append, hpplen, descSpine_length]; omega)
      intro j' hj1 hj2
      rw [List.getElem_take]
      have hj'l : j' < (policyParameterLocals np pc).length := by
        rw [List.length_take] at hj1; omega
      have hj2j : j' < j := by rw [descSpine_length] at hj2; exact hj2
      rw [List.getElem_append_left hj'l]
      simp only [← descSpine_eq_ppL,
        getElem_descSpine pc np j' (by rw [← hpplen]; exact hj'l),
        getElem_descSpine (pc + np - j) j j' hj2j]
      exact congrArg Expr.bvar (by omega)
    rw [htk]
    simp only [← descSpine_eq_ppL]
    rw [getElem_descSpine pc np j hjp]
    rw [List.getElem_append_left (by rw [hpmlen]; exact hjp), List.getElem_map,
      instPrefix_descSpine (pc + np - j) j params[j].1 hb,
      show pc + (np - 1 - j) = np - 1 - j + pc from by omega,
      show pc + np - j = np - j + pc from by omega]
    exact HasTyT.bvar _ _ _ hlook
  · have hjp' : np ≤ j := by omega
    simp only [List.length_append, hpplen] at hj
    have hjl : j - np < idx.length := by omega
    have hj'' : j < np + indicesF.length := by omega
    rw [List.getElem_append_right (by rw [hpplen]; omega)]
    simp only [hpplen]
    have htk : (policyParameterLocals np pc ++ idx).take j =
        policyParameterLocals np pc ++ idx.take (j - np) := by
      rw [show j = (policyParameterLocals np pc).length +
            (j - (policyParameterLocals np pc).length) from by
            rw [hpplen]; omega,
        List.take_append, hpplen, Nat.add_sub_cancel_left]
    rw [htk, List.getElem_append_right (by rw [hpmlen]; omega)]
    simp only [hpmlen]
    have hbk : lift (j - np + np) 1 indicesF[j - np] = indicesF[j - np] := by
      rw [Nat.sub_add_cancel hjp']
      have hb0 := hbnd j (by simp only [List.length_append, hpmlen]; omega)
      rw [List.getElem_append_right (by rw [hpmlen]; omega)] at hb0
      simp only [hpmlen] at hb0
      exact hb0
    simp only [← descSpine_eq_ppL]
    rw [instPrefix_append_instTelK (idx.take (j - np)) (descSpine pc np) indicesF[j - np],
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hjl),
      instTelK_descSpine (j - np) pc np indicesF[j - np] hbk]
    have hx : lift (j - np) pc indicesF[j - np] =
        (liftDomsT 0 pc indicesF)[j - np]'(by rw [length_liftDomsT]; omega) := by
      rw [getElem_liftDomsT, Nat.zero_add]
    rw [hx]
    exact argsTyT_getElem (liftDomsT 0 pc indicesF) idx
      (by rw [length_liftDomsT]; omega) _ rfl hidx (j - np) hjl

/-- **the family application, typed.** `foldApps (F ls) (ppL np pc ++ idx)` at `Sort fv.sort` in
    the plain field context `plainCtxT pre (telCtxT fv.params)`: the const head typed at the
    family's stored telescope (extendEnv-member `fm`, canonical levels, closed by `EnvClosed`),
    the parameter-locals-plus-indices spine via `argsTyT_paramLocals`. -/
def famApp_typed_drec {E : ResolvedEnv} {n : Nat} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} (hcl : EnvClosed E) (hres : E.members f = some fm)
    (pre : List FieldT) (idx : List (Expr Nat))
    (np pc : Nat) (hnp : fv.params.length = np) (hn : fm.arity ≤ n)
    (hpc : plainIdxT pre 0 = pc)
    (hl : idx.length = (fv.indices.map Prod.fst).length)
    (hidx : ArgsTyT E n (plainCtxT pre (telCtxT fv.params))
      (policyPi (liftDomsT 0 pc (fv.indices.map Prod.fst)) (.sort fv.sort)) idx) :
    HasTyT E n (plainCtxT pre (telCtxT fv.params))
      (foldApps (.const f (canonLevels fm.arity))
        (policyParameterLocals np pc ++ idx)) (.sort fv.sort) := by
  have hd0 := (hcl f fm hres).1 0
  rw [fv.stored, List.map_append, lift_policyPi, Nat.zero_add] at hd0
  have hdoms : liftDomsT 0 1 (fv.params.map Prod.fst ++ fv.indices.map Prod.fst) =
      fv.params.map Prod.fst ++ fv.indices.map Prod.fst :=
    policyPi_sort_inj _ _ _ _ hd0
  have hbnd : ∀ j (hj : j < (fv.params.map Prod.fst ++ fv.indices.map Prod.fst).length),
      lift j 1 (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)[j] =
        (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)[j] := by
    intro j hj
    have hge := getElem_liftDomsT 1 (fv.params.map Prod.fst ++ fv.indices.map Prod.fst) 0 j hj
    simp only [hdoms] at hge
    rw [Nat.zero_add] at hge
    exact hge.symm
  have hhead : HasTyT E n (plainCtxT pre (telCtxT fv.params))
      (.const f (canonLevels fm.arity))
      (policyPi (fv.params.map Prod.fst ++ fv.indices.map Prod.fst) (.sort fv.sort)) := by
    have hc := HasTyT.const (plainCtxT pre (telCtxT fv.params)) f
      (canonLevels fm.arity) fm hres (by simp [canonLevels])
      (levelsBounded_mono hn _ (levelsBounded_canon fm.arity))
    rw [instantiateLevels_canon, fv.stored, List.map_append] at hc
    exact hc
  have hargs := argsTyT_paramLocals pre fv.params (fv.indices.map Prod.fst) idx np pc
    hnp hpc hl hbnd hidx
  have happ := hasTyT_foldApps_args
    (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)
    (policyParameterLocals np pc ++ idx) (by
      rw [List.length_append, policyParameterLocals_length, List.length_append,
        List.length_map, hnp, hl])
    (.sort fv.sort) _ rfl hargs hhead
  rwa [instPrefix_sort] at happ

/-- **the IH, locally.** A motive `M` typed at `Π Is, I (P0 ++ locals) → Sort uM` (the parameters `P0`
    seen past the index binders), index arguments typed along `Is` (W1's data property), and a term `x`
    typed at the family application `I (P0 ++ idx)`: the induction hypothesis `M idx x` is typed at
    `Sort uM`. No environment premise. -/
def hasTyT_ih_local {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (M : Expr Nat) (Is : List (Expr Nat))
    (f : Nat) (ls : List Level) (P0 : List (Expr Nat)) (uM l : Level) (idx : List (Expr Nat))
    (hlen : idx.length = Is.length)
    (hM : HasTyT E n Γ M (policyPi Is (.pi (foldApps (.const f ls)
      (P0.map (lift 0 Is.length) ++ policyLocals Is.length)) (.sort uM))))
    (hidx : ArgsTyT E n Γ (policyPi Is (.sort l)) idx)
    (x : Expr Nat) (hx : HasTyT E n Γ x (foldApps (.const f ls) (P0 ++ idx))) :
    HasTyT E n Γ (foldApps M (idx ++ [x])) (.sort uM) := by
  have hpre := hasTyT_foldApps_args Is idx hlen _ M rfl hidx hM
  have hbody : instPrefix idx (.pi (foldApps (.const f ls)
      (P0.map (lift 0 Is.length) ++ policyLocals Is.length)) (.sort uM)) =
      .pi (foldApps (.const f ls) (P0 ++ idx)) (.sort uM) := by
    rw [instPrefix_pi, instPrefix_foldApps, instPrefix_const, List.map_append, List.map_map]
    have h1 : P0.map (instPrefix idx ∘ lift 0 Is.length) = P0 := by
      rw [← hlen]
      conv => rhs; rw [← List.map_id P0]
      exact List.map_congr_left (fun p _ => instPrefix_lift idx p)
    have h2 : (policyLocals Is.length).map (instPrefix idx) = idx := by
      rw [← hlen]; exact instPrefix_bvarSpine idx
    rw [h1, h2, instTel_sort]
  rw [hbody] at hpre
  rw [foldApps_snoc]
  exact HasTyT.app _ _ _ _ _ hpre hx

mutual
def tyConvT_levelMono {E : ResolvedEnv} {n n' : Nat} (hn : n ≤ n') :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → TyConvT E n' Γ A B
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B u c => .of Γ A B u (convT_levelMono hn c)
  | _, _, _, .trans Γ A B C c₁ c₂ => .trans Γ A B C (tyConvT_levelMono hn c₁) (tyConvT_levelMono hn c₂)
end

/-- one assumption converted along a type-conversion chain (new type to old), anywhere in a context:
    `hasTyTConvAssumpAt` (`RcicParRedSRTyped.lean:999`) once per link. -/
def hasTyTTyConvAssumpAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hcl : EnvClosed E) :
    {A' A : Expr Nat} → TyConvT E n Γ A' A → (Δ : LCtx) → {e T : Expr Nat} →
    HasTyT E n (Δ ++ LocalDecl.assumption A :: Γ) e T →
    HasTyT E n (Δ ++ LocalDecl.assumption A' :: Γ) e T
  | _, _, .refl _ _, _, _, _, h => h
  | _, _, .of _ _ _ _ c, Δ, _, _, h => hasTyTConvAssumpAt hcl c Δ h
  | _, _, .trans _ _ _ _ c₁ c₂, Δ, _, _, h =>
      hasTyTTyConvAssumpAt hcl c₁ Δ (hasTyTTyConvAssumpAt hcl c₂ Δ h)

/-- a telescope's binders converted, innermost first: each new domain converts to the old one in the
    old telescope's prefix, so no conversion has to be moved. -/
theorem hasTyT_telConv {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (ms ps : List (Expr Nat))
    (hlen : ps.length = ms.length)
    (hc : ∀ (i : Nat) (hi : i < ms.length), Nonempty (TyConvT E n (policyPrefixContext ms i)
      (ps[i]'(by rw [hlen]; exact hi)) ms[i])) :
    (N : Nat) → N ≤ ms.length → (Δ : LCtx) → {e T : Expr Nat} →
    Nonempty (HasTyT E n (Δ ++ policyPrefixContext ms N) e T) →
    Nonempty (HasTyT E n (Δ ++ policyPrefixContext ps N) e T)
  | 0, _, Δ, _, _, h => by simpa only [policyPrefixContext, List.take_zero] using h
  | N + 1, hN, Δ, e, T, ⟨h⟩ => by
      have hNm : N < ms.length := hN
      have hNp : N < ps.length := by rw [hlen]; exact hNm
      rw [policyPrefixContext_succ ms N hNm] at h
      obtain ⟨c⟩ := hc N hNm
      have h1 := hasTyTTyConvAssumpAt hcl c Δ h
      have h2 : HasTyT E n ((Δ ++ [LocalDecl.assumption (ps[N]'hNp)]) ++ policyPrefixContext ms N) e T := by
        simpa only [List.append_assoc, List.singleton_append] using h1
      obtain ⟨h3⟩ := hasTyT_telConv hcl ms ps hlen hc N (Nat.le_of_lt hNm) _ ⟨h2⟩
      rw [policyPrefixContext_succ ps N hNp]
      exact ⟨by simpa only [List.append_assoc, List.singleton_append] using h3⟩

/-- **M3 at a constructor.** A typing over a constructor's parameter mirrors moves to the family's
    parameters, by `CtorTypedT`'s mirror conversions (05 §6.1), at any arity at least the family's. -/
theorem hasTyT_mirrorsToParams {E : ResolvedEnv} (hcl : EnvClosed E) {fam : PolicyFamilyView E}
    {m : CheckedMember} (c : PolicyConstructorView E fam m) (hct : CtorTypedT c) {n : Nat}
    (hn : fam.member.arity ≤ n) (Δ : LCtx) {e T : Expr Nat}
    (h : Nonempty (HasTyT E n (Δ ++ policyPrefixContext c.parameters c.parameters.length) e T)) :
    Nonempty (HasTyT E n (Δ ++ policyPrefixContext fam.parameters fam.parameters.length) e T) := by
  have hlen : fam.parameters.length = c.parameters.length := c.parameterCount.symm
  have := hasTyT_telConv hcl c.parameters fam.parameters hlen
    (fun i hi => by
      obtain ⟨cv⟩ := hct.2 ⟨i, hi⟩
      exact ⟨tyConvT_levelMono hn cv.symmT⟩)
    c.parameters.length (Nat.le_refl _) Δ h
  rw [hlen]; exact this

/-- admission reads a syntactic family-headed telescope as itself. -/
theorem piTelescopeFuel_policyPi_famApp {E : ResolvedEnv} {f : Nat} {ls : List Level}
    (hf : transparentBody E f ls = none) :
    (doms args : List (Expr Nat)) → {fuel : Nat} → doms.length + 2 ≤ fuel →
    piTelescopeFuel E fuel (policyPi doms (foldApps (.const f ls) args)) =
      some (doms, foldApps (.const f ls) args)
  | [], args, _, h => piTelescopeFuel_famApp args hf h
  | D :: doms, args, fuel, h => by
      have h' : doms.length + 3 ≤ fuel := by simp only [List.length_cons] at h; omega
      obtain ⟨k', rfl⟩ : ∃ k', fuel = k' + 1 + 1 := ⟨fuel - 2, by omega⟩
      have hw : whnfFuel E (k' + 1) (Expr.pi D (policyPi doms (foldApps (.const f ls) args))) =
          some (Expr.pi D (policyPi doms (foldApps (.const f ls) args))) := by
        simp only [whnfFuel, appsSpine]
      have ih := piTelescopeFuel_policyPi_famApp hf doms args (fuel := k' + 1) (by omega)
      show piTelescopeFuel E (k' + 1 + 1) (Expr.pi D (policyPi doms (foldApps (.const f ls) args))) = _
      rw [piTelescopeFuel.eq_2, hw]
      simp only [ih]

/-- parameter locals past a cutoff at or below their base move up together. -/
theorem policyParameterLocals_lift_le (np x c a : Nat) (h : c ≤ x) :
    (policyParameterLocals np x).map (lift c a) = policyParameterLocals np (x + a) := by
  simp only [policyParameterLocals, List.map_map]
  exact List.map_congr_left (fun i _ => by
    show lift c a (Expr.bvar (i + x)) = Expr.bvar (i + (x + a))
    simp only [lift, if_pos (Nat.le_trans h (Nat.le_add_left x i))]
    congr 1; omega)

theorem liftDomsT_liftDomsT_le (a : Nat) : (ds : List (Expr Nat)) → (c k x : Nat) → c ≤ x →
    liftDomsT (c + k) a (liftDomsT k x ds) = liftDomsT k (x + a) ds
  | [], _, _, _, _ => rfl
  | D :: ds, c, k, x, h => by
      simp only [liftDomsT]
      rw [lift_lift_merge a x k (c + k) (Nat.le_add_left k c) (by omega),
        show c + k + 1 = c + (k + 1) from by omega, liftDomsT_liftDomsT_le a ds c (k + 1) x h]

theorem liftDomsT_append (c a : Nat) : (xs ys : List (Expr Nat)) →
    liftDomsT c a (xs ++ ys) = liftDomsT c a xs ++ liftDomsT (c + xs.length) a ys
  | [], ys => by simp only [List.nil_append, liftDomsT, List.length_nil, Nat.add_zero]
  | x :: xs, ys => by
      show lift c a x :: liftDomsT (c + 1) a (xs ++ ys) = _
      rw [liftDomsT_append (c + 1) a xs ys]
      simp only [liftDomsT, List.length_cons, List.cons_append, Nat.add_assoc, Nat.add_comm 1 xs.length]

/-- the index telescope at distance `d` from the parameters. -/
def idxTelAt (Is : List (Expr Nat)) (l : Level) (d : Nat) : Expr Nat :=
  policyPi (liftDomsT 0 d Is) (.sort l)

/-- the motive's type at distance `d` from the parameters. -/
def motTyAt (f : Nat) (ls : List Level) (np : Nat) (Is : List (Expr Nat)) (uM : Level) (d : Nat) :
    Expr Nat :=
  policyPi (liftDomsT 0 d Is) (.pi (foldApps (.const f ls)
    ((policyParameterLocals np d).map (lift 0 Is.length) ++ policyLocals Is.length)) (.sort uM))

theorem idxTelAt_lift (Is : List (Expr Nat)) (l : Level) (d c a : Nat) (h : c ≤ d) :
    lift c a (idxTelAt Is l d) = idxTelAt Is l (d + a) := by
  rw [idxTelAt, lift_policyPi, ← Nat.add_zero c, liftDomsT_liftDomsT_le a Is c 0 d h]
  rfl

theorem motTyAt_lift (f : Nat) (ls : List Level) (np : Nat) (Is : List (Expr Nat)) (uM : Level)
    (d a : Nat) : lift 0 a (motTyAt f ls np Is uM d) = motTyAt f ls np Is uM (d + a) := by
  rw [motTyAt, lift_policyPi, ← Nat.add_zero 0, liftDomsT_liftDomsT_le a Is 0 0 d (Nat.zero_le _),
    length_liftDomsT]
  simp only [motTyAt, lift, Nat.zero_add, foldApps_lift, List.map_append, List.map_map]
  have h1 : (policyParameterLocals np d).map (lift Is.length a ∘ lift 0 Is.length) =
      (policyParameterLocals np (d + a)).map (lift 0 Is.length) := by
    rw [← policyParameterLocals_lift_le np d 0 a (Nat.zero_le _), List.map_map]
    apply List.map_congr_left
    intro p _
    show lift Is.length a (lift 0 Is.length p) = lift 0 Is.length (lift 0 a p)
    rw [lift_lift_merge a Is.length 0 Is.length (Nat.zero_le _) (by omega),
      lift_lift_merge Is.length a 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]
  rw [h1, policyLocals_map_lift_above Is.length Is.length a (Nat.le_refl _)]

/-- `motTyAt` at distance zero is the plain motive type (`motTyT`-shaped, `Is` unlifted). -/
theorem motTyAt_zero (f : Nat) (ls : List Level) (np : Nat)
    (Is : List (Expr Nat)) (uM : Level) :
    motTyAt f ls np Is uM 0 =
      policyPi Is (.pi (foldApps (.const f ls)
        ((policyLocals np).map (lift 0 Is.length) ++ policyLocals Is.length))
        (.sort uM)) := by
  rw [motTyAt, liftDomsT_zero]
  simp only [policyParameterLocals, Nat.add_zero]
  rfl


/-- the motive hypothesis at the minor's context: `bvar i` resolves to the motive
    declaration `i` minors down, typed at `motTyAt` of distance `i + 1` —
    `lookupType` on `ppc mins i ++ (assumption Mot :: Γp)` plus `motTyAt_lift`. -/
theorem hM_minCtx {E : ResolvedEnv} {n : Nat} {f np i : Nat} {ls : List Level}
    {Is : List (Expr Nat)} {uM : Level}
    (mins : List (Expr Nat)) (hm : i ≤ mins.length) (Mot : Expr Nat) (Γp : LCtx)
    (hMot : Mot = motTyAt f ls np Is uM 0) :
    Nonempty (HasTyT E n
      (policyPrefixContext mins i ++ (.assumption Mot :: Γp))
      (.bvar i) (motTyAt f ls np Is uM (0 + i + 1))) := by
  have hL : (policyPrefixContext mins i).length = i := by
    simp only [policyPrefixContext, List.length_map, List.length_reverse,
      List.length_take, Nat.min_eq_left hm]
  have hlook := lookupType_append_assumption (policyPrefixContext mins i) Mot Γp
  rw [hL] at hlook
  exact ⟨.bvar _ _ _ (by
    rw [hlook, hMot, motTyAt_lift, Nat.zero_add]
    congr 2; omega)⟩

/-- the full-prefix context of a pair telescope is its `telCtxT`: the minor
    context's parameter tail is presented as `policyPrefixContext`, the typed
    view's as `telCtxT` — same list. -/
theorem policyPrefixContext_telCtxT (ds : List (Expr Nat × Level)) :
    policyPrefixContext (ds.map Prod.fst) ds.length = telCtxT ds := by
  rw [policyPrefixContext,
    List.take_of_length_le (by simp)]
  simp only [telCtxT, List.map_reverse, List.map_map]
  congr 1

/-- `motTyAt` at distance zero IS `motTyT`: the `Is`-indexed index telescope
    with the motive's family application at the parameter locals. -/
theorem motTyAt_eq_motTyT (f : Nat) (ls : List Level)
    (params indices : List (Expr Nat × Level)) (uM : Level) :
    motTyAt f ls params.length (indices.map Prod.fst) uM 0 =
      motTyT f ls params indices uM := by
  rw [motTyAt_zero, motTyT, famLocalsT, List.length_map]

/-! ## telescope inversion -/

/-- the level-vector-packaged telescope inversion: `hasTyT_policyPi_inv`
    (#6287) returns per-domain `∃ w`, which cannot be gathered into a `Fin`-indexed
    level function without `Classical.choice` (outside the axiom budget).  Where the
    sort function is needed as data (`piSortT`, `hasTyT_policyPi_build`), this shape
    is used instead. -/
theorem hasTyT_policyPi_invT {E : ResolvedEnv} {n : Nat} :
    (ds : List (Expr Nat)) → {Γ : LCtx} → {body : Expr Nat} → {u : Level} →
    HasTyT E n Γ (policyPi ds body) (.sort u) →
    ∃ lv : Fin ds.length → Level, ∀ i : Fin ds.length,
      Nonempty (HasTyT E n (policyPrefixContext ds i.val ++ Γ) ds[i.val] (.sort (lv i)))
  | [], _, _, _, _ => ⟨fun i => i.elim0, fun i => i.elim0⟩
  | A :: ds, Γ, body, u, h => by
      obtain ⟨uA, v, hA, hB, _⟩ := hasTyTInv_pi h rfl
      obtain ⟨lv, hlv⟩ := hasTyT_policyPi_invT ds hB
      refine ⟨fun i => i.cases uA lv, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨by simpa [policyPrefixContext] using hA⟩
      · obtain ⟨hj⟩ := hlv j
        have hj' : HasTyT E n (policyPrefixContext (A :: ds) (j.val + 1) ++ Γ) ds[j.val] (.sort (lv j)) := by
          rw [policyPrefixContext_cons_succ]; exact hj
        exact ⟨by simpa using hj'⟩

/-- the `Type`-valued twin of `hasTyT_policyPi_invT`: per-domain sort typings as
    data (a `Σ'`-level function and plain `HasTyT`s, no `Nonempty`), for
    consumers that build `Type`-valued evidence (`ArgsTyT`/`CtxWfT`) where
    `Nonempty` cannot eliminate.  No `Classical.choice` — `hasTyTInv_pi` is
    already `Σ'`-valued. -/
def hasTyT_policyPi_invTS {E : ResolvedEnv} {n : Nat} :
    (ds : List (Expr Nat)) → {Γ : LCtx} → {body : Expr Nat} → {u : Level} →
    HasTyT E n Γ (policyPi ds body) (.sort u) →
    Σ' lv : Nat → Level, ∀ j (hj : j < ds.length),
      HasTyT E n (policyPrefixContext ds j ++ Γ) ds[j] (.sort (lv j))
  | [], _, _, _, _ => ⟨fun _ => .zero, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | A :: ds, Γ, body, u, h =>
      let ⟨uA, _, hA, hB, _⟩ := hasTyTInv_pi h rfl
      let ⟨lv, hlv⟩ := hasTyT_policyPi_invTS ds hB
      ⟨fun j => match j with | 0 => uA | j + 1 => lv j, fun j hj => by
        cases j with
        | zero =>
            simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
              List.map_nil, List.nil_append, List.getElem_cons_zero] using hA
        | succ j =>
            have hstep := hlv j (Nat.lt_of_succ_lt_succ hj)
            rw [policyPrefixContext_cons_succ, List.getElem_cons_succ]
            exact hstep⟩

/-! ## arguments along a telescope, transported -/

/-- a block of binders under a telescope prefix, for arguments typed along a telescope. -/
def argsTyT_weakenUnderTel {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (ds : List (Expr Nat))
    (j : Nat) (hj : j ≤ ds.length) {Γ : LCtx} (Δ : LCtx) :
    {T : Expr Nat} → {as : List (Expr Nat)} → ArgsTyT E n (policyPrefixContext ds j ++ Γ) T as →
    ArgsTyT E n (policyPrefixContext (liftDomsT 0 Δ.length ds) j ++ (Δ ++ Γ))
      (lift j Δ.length T) (as.map (lift j Δ.length))
  | _, _, .nil l => .nil l
  | _, _, .cons A B a as ha tl => by
      have ha' := hasTyT_weakenUnderTel hcl ds j hj Δ ha
      have tl' := argsTyT_weakenUnderTel hcl ds j hj Δ tl
      rw [instantiate0, lift_instantiate_low Δ.length j 0 a (Nat.zero_le _)] at tl'
      exact .cons (lift j Δ.length A) (lift (j + 1) Δ.length B) (lift j Δ.length a) _ ha' tl'

/-- one-declaration `insertAt` weakening on `ArgsTyT` — the `ArgsTyT` analog of
    `hasTyTWeaken`, and the per-step building block of `argsTyT_liftChain`. -/
def argsTyT_insertAt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (d : LocalDecl) (c : Nat) :
    {Γ : LCtx} → {T : Expr Nat} → {as : List (Expr Nat)} →
      ArgsTyT E n Γ T as →
      ArgsTyT E n (insertAt d c Γ) (lift c 1 T) (as.map (lift c 1))
  | _, _, _, .nil l => .nil l
  | _, _, _, .cons A B a as ha tl => by
      have ha' := hasTyTWeaken d hcl (c := c) ha
      have tl' := argsTyT_insertAt hcl d c tl
      rw [instantiate0, lift_instantiate_low 1 c 0 a (Nat.zero_le _)] at tl'
      exact .cons (lift c 1 A) (lift (c + 1) 1 B) (lift c 1 a) _ ha' tl'

/-- a context extended by a list of `(decl, cutoff)` insertions, applied
    innermost-first (matching `liftChain`'s fold order on expressions). -/
def insertChain : List (LocalDecl × Nat) → LCtx → LCtx
  | [], Γ => Γ
  | (d, c) :: rest, Γ => insertChain rest (insertAt d c Γ)

/-- `ArgsTyT` transported along an insertion chain — the judgment-side analog of
    `RcicSubstT.liftChain`. Every step is a `.letE`-safe `insertAt` weakening, so
    this is the transport route for the ctor renaming σ where a general
    substitution morphism is unavailable (see `RcicSubstT`'s header). -/
def argsTyT_liftChain {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    (ds : List (LocalDecl × Nat)) → (Γ : LCtx) → (T : Expr Nat) → (as : List (Expr Nat)) →
      ArgsTyT E n Γ T as →
      ArgsTyT E n (insertChain ds Γ) (liftChain (ds.map Prod.snd) T)
        (as.map (liftChain (ds.map Prod.snd)))
  | [], Γ, T, as, h => by
      rw [List.map_nil, show (liftChain ([] : List Nat)) = id from rfl, List.map_id]
      exact h
  | (d, c) :: rest, Γ, T, as, h => by
      have h'' := argsTyT_liftChain hcl rest (insertAt d c Γ) (lift c 1 T)
        (as.map (lift c 1)) (argsTyT_insertAt hcl d c h)
      simpa [insertChain, liftChain, List.map_map] using h''

/-- the domain a ctor field contributes in PLAIN-context discipline (`pc` plain fields
    before it): plain and δ-annotated fields keep their surface `D`; a direct recursive
    field is the family application at the plain parameter locals. -/
def ctorPlainDom (f : Nat) (ls : List Level) (np pc : Nat) : FieldT → Expr Nat
  | .plain D _ => D
  | .drec idx => foldApps (.const f ls) (policyParameterLocals np pc ++ idx)
  | .drecD D _ => D

/-- the recursive fields' insertion pairs for the constructor prefix, innermost first:
    each recursive field contributes `(assumption (plain-form domain), #fields after it)`.
    `insertAt`'s `liftDecl` accumulation turns the plain form into the emitted domain —
    `substT (ctorSub skips)` of the plain form, by the renaming bridge. -/
def ctorInsPairs (f : Nat) (ls : List Level) (np : Nat) :
    (fs : List FieldT) → (pc : Nat) → List (LocalDecl × Nat)
  | .plain _ _ :: fs, pc => ctorInsPairs f ls np fs (pc + 1)
  | .drec idx :: fs, pc =>
      ctorInsPairs f ls np fs pc ++
        [(.assumption (ctorPlainDom f ls np pc (.drec idx)), fs.length)]
  | .drecD D idx :: fs, pc =>
      ctorInsPairs f ls np fs pc ++ [(.assumption (ctorPlainDom f ls np pc (.drecD D idx)),
        fs.length)]
  | [], _ => []

private theorem ctorInsPairs_snds (f : Nat) (ls : List Level) (np : Nat) :
    (fs : List FieldT) → (pc : Nat) →
      (ctorInsPairs f ls np fs pc).map Prod.snd = ctorInsCutoffs fs
  | .plain _ _ :: fs, pc => ctorInsPairs_snds f ls np fs (pc + 1)
  | .drec _ :: fs, pc => by
      simp only [ctorInsPairs, List.map_append, List.map_cons, List.map_nil,
        ctorInsCutoffs]
      rw [ctorInsPairs_snds f ls np fs pc]
  | .drecD _ _ :: fs, pc => by
      simp only [ctorInsPairs, List.map_append, List.map_cons, List.map_nil,
        ctorInsCutoffs]
      rw [ctorInsPairs_snds f ls np fs pc]
  | [], _ => rfl

/-- pointwise congruence for `List.mapIdx` (absent from this environment's List API). -/
private theorem mapIdx_congr' {α β : Type} {f g : Nat → α → β} (l : List α)
    (h : ∀ i (hi : i < l.length), f i l[i] = g i l[i]) :
    l.mapIdx f = l.mapIdx g := by
  apply List.ext_getElem
  · rw [List.length_mapIdx, List.length_mapIdx]
  · intro i hi1 hi2
    rw [List.getElem_mapIdx, List.getElem_mapIdx]
    exact h i (by rwa [List.length_mapIdx] at hi1)

/-- `List.mapIdx` composed with `List.mapIdx` — the outer index function sees the
    already-mapped elements. -/
private theorem mapIdx_mapIdx {α β γ : Type} (l : List α) (f : Nat → β → γ) (g : Nat → α → β) :
    (l.mapIdx g).mapIdx f = l.mapIdx (fun i a => f i (g i a)) := by
  apply List.ext_getElem
  · simp only [List.length_mapIdx]
  · intro i hi1 hi2
    rw [List.getElem_mapIdx, List.getElem_mapIdx, List.getElem_mapIdx]

/-- the emitted constructor prefix's domain list: field `i`'s domain is its plain-form
    `ctorPlainDom` pushed along the σ of the fields before it. `pc` counts plain fields
    in a wider enclosing prefix. -/
def ctorEmittedDoms (f : Nat) (ls : List Level) (np pc : Nat) (fs : List FieldT) :
    List (Expr Nat) :=
  fs.mapIdx (fun i fᵢ =>
    substT (ctorSub ((fs.take i).map FieldT.ctorSkip))
      (ctorPlainDom f ls np (pc + plainIdxT (fs.take i) 0) fᵢ))

private theorem ctorEmittedDoms_length (f : Nat) (ls : List Level) (np pc : Nat)
    (fs : List FieldT) : (ctorEmittedDoms f ls np pc fs).length = fs.length := by
  simp [ctorEmittedDoms]

/-- the head field of a `plain :: fs` prefix is emitted verbatim (`ctorSub [] = id`),
    and the tail is the emitted list of `fs` at one more plain. -/
private theorem ctorEmittedDoms_cons_plain (f : Nat) (ls : List Level) (np pc : Nat)
    (D : Expr Nat) (u : Level) (fs : List FieldT) :
    ctorEmittedDoms f ls np pc (.plain D u :: fs) =
      D :: ctorEmittedDoms f ls np (pc + 1) fs := by
  simp only [ctorEmittedDoms, List.mapIdx_cons]
  congr 1
  · simp only [List.take_zero, List.map_nil, ctorSub, List.foldl_nil, substT_id,
      plainIdxT, Nat.add_zero, ctorPlainDom]
  · apply mapIdx_congr'
    intro i hi
    simp only [List.take_succ_cons, List.map_cons, FieldT.ctorSkip, plainIdxT]
    rw [substT_ctorSub_cons_zero, plainIdxT_add,
      show pc + (plainIdxT (fs.take i) 0 + 1) = pc + 1 + plainIdxT (fs.take i) 0 from by omega]

/-- the head field of a `drec :: fs` / `drecD :: fs` prefix is emitted verbatim, and
    the tail is `fs`'s emitted list with every entry lifted once at its own depth —
    `ctorSub (1 :: rest)` is `lift (binderCount rest) 1` after `ctorSub rest`. -/
private theorem ctorEmittedDoms_cons_drec (f : Nat) (ls : List Level) (np pc : Nat)
    (idx : List (Expr Nat)) (fs : List FieldT) :
    ctorEmittedDoms f ls np pc (.drec idx :: fs) =
      ctorPlainDom f ls np pc (.drec idx) ::
        (ctorEmittedDoms f ls np pc fs).mapIdx (fun i D => lift i 1 D) := by
  simp only [ctorEmittedDoms, List.mapIdx_cons]
  congr 1
  · simp only [List.take_zero, List.map_nil, ctorSub, List.foldl_nil, substT_id,
      plainIdxT, Nat.add_zero]
  · rw [mapIdx_mapIdx]
    apply mapIdx_congr'
    intro i hi
    simp only [List.take_succ_cons, List.map_cons, FieldT.ctorSkip, plainIdxT]
    rw [substT_ctorSub_cons_one, binderCount_map_ctorSkip, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hi)]

private theorem ctorEmittedDoms_cons_drecD (f : Nat) (ls : List Level) (np pc : Nat)
    (D : Expr Nat) (idx : List (Expr Nat)) (fs : List FieldT) :
    ctorEmittedDoms f ls np pc (.drecD D idx :: fs) =
      D :: (ctorEmittedDoms f ls np pc fs).mapIdx (fun i D => lift i 1 D) := by
  simp only [ctorEmittedDoms, List.mapIdx_cons]
  congr 1
  · simp only [List.take_zero, List.map_nil, ctorSub, List.foldl_nil, substT_id,
      plainIdxT, Nat.add_zero, ctorPlainDom]
  · rw [mapIdx_mapIdx]
    apply mapIdx_congr'
    intro i hi
    simp only [List.take_succ_cons, List.map_cons, FieldT.ctorSkip, plainIdxT]
    rw [substT_ctorSub_cons_one, binderCount_map_ctorSkip, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hi)]

/-- `HasTyT` transported along an insertion chain — the judgment-side analog, used
    for the boundary insert that lifts the constructor's domain typings into the
    minor's context (`liftDomsT`-of-the-telescope side). -/
def hasTyT_liftChain {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    (ds : List (LocalDecl × Nat)) → (Γ : LCtx) → (e T : Expr Nat) →
      HasTyT E n Γ e T →
      HasTyT E n (insertChain ds Γ) (liftChain (ds.map Prod.snd) e)
        (liftChain (ds.map Prod.snd) T)
  | [], _, _, _, h => h
  | (d, _) :: rest, _, _, _, h =>
      hasTyT_liftChain hcl rest _ _ _ (hasTyTWeaken d hcl h)

/-- `ConvT` transported along an insertion chain — the conversion analog of
    `hasTyT_liftChain` (the `.drecD` route: the surface domain's conversion to
    the family application must ride the same ctor-renaming liftChain as the
    argument typings). -/
def convT_liftChain {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    (ds : List (LocalDecl × Nat)) → (Γ : LCtx) → (a b T : Expr Nat) →
      ConvT E n Γ a b T →
      ConvT E n (insertChain ds Γ) (liftChain (ds.map Prod.snd) a)
        (liftChain (ds.map Prod.snd) b) (liftChain (ds.map Prod.snd) T)
  | [], _, _, _, _, c => c
  | (d, _) :: rest, _, _, _, _, h =>
      convT_liftChain hcl rest _ _ _ _ (convTWeaken d hcl h)

/-- congruence under head substitution for `ConvT`: a conversion between two
    replacements at the lifted domain, in the context with the binder removed,
    transports through instantiation of any typed derivation — `inst j v e`
    converts to `inst j v' e` at the LEFT-instantiated type. Dual to
    `hasTyT_substS`/`convT_substS` (which move ONE replacement through); this
    is the engine under `convT_instTelK` for the `.drecD` whnf'd indices. The
    type position carries the left instantiation, matching `ConvT`'s
    constructor conventions (`.pi`/`.lam`/`.letE` bind under the left domain,
    `.app`/`.letE` result types instantiate the left value). -/
def convT_substCongr {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (v v' t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T → Γ[j]? = some (.assumption t) →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    ConvT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j v') (lift 0 j t) →
    ConvT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v') e)
      (instantiate j (lift 0 j v) T)
  | j, _, _, _, .sort _ _, _, _, _ => by
      simp only [instantiate]; exact .refl _ _ _ (.sort _ _)
  | j, _, _, _, .bvar Γ i A h, hget, hvty, hcv => by
      by_cases hij : i = j
      · subst hij
        rw [lookupType_get_assumption hget] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i+1) 0 i (lift 0 i v) (by omega) (by omega)]
        exact hcv
      · by_cases hlt : i < j
        · have hl := lookupType_substRemove_lt (v := v) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .refl _ _ _ (.bvar _ _ _ hl)
        · have hg := lookupType_substRemove_gt (v := v) (by omega : j < i) h
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          exact .refl _ _ _ (.bvar _ _ _ hg)
  | j, _, _, _, .const Γ r ls m hres hlen hwf, _, _, _ => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      simp only [instantiate]
      rw [hm]
      exact .refl _ _ _ (.const _ _ _ _ hres hlen hwf)
  | j, _, _, _, .pi Γ A u B w hA hB, hget, hvty, hcv => by
      simp only [instantiate]
      have hvty' :
          HasTyT E n (substRemove v (j+1) (.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (.assumption A)) hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hcv' :
          ConvT E n (substRemove v (j+1) (.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) v') (lift 0 (j+1) t) := by
        have h0 := convTWeaken (instDecl j v (.assumption A)) hcl (c := 0) hcv
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (.assumption A :: Γ)[j+1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hB' := convT_substCongr hcl hinst v v' t hB hget' hvty' hcv'
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB'
      have hA' := convT_substCongr hcl hinst v v' t hA hget hvty hcv
      simp only [instantiate] at hA'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v),
          lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v')]
      exact .pi _ _ _ _ _ u w hA' hB'
  | j, _, _, _, .lam Γ A u body B hA hbody, hget, hvty, hcv => by
      simp only [instantiate]
      have hA' := convT_substCongr hcl hinst v v' t hA hget hvty hcv
      simp only [instantiate] at hA'
      have hvty' :
          HasTyT E n (substRemove v (j+1) (.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (.assumption A)) hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hcv' :
          ConvT E n (substRemove v (j+1) (.assumption A :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) v') (lift 0 (j+1) t) := by
        have h0 := convTWeaken (instDecl j v (.assumption A)) hcl (c := 0) hcv
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (.assumption A :: Γ)[j+1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substCongr hcl hinst v v' t hbody hget' hvty' hcv'
      simp only [substRemove_succ_cons, instDecl] at hb'
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v),
          lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v')]
      exact .lam _ _ _ _ _ _ u hA' hb'
  | j, _, _, _, .app Γ f a A B hf ha, hget, hvty, hcv => by
      have hf' := convT_substCongr hcl hinst v v' t hf hget hvty hcv
      have ha' := convT_substCongr hcl hinst v v' t ha hget hvty hcv
      simp only [instantiate] at hf'
      have h6 := instantiate_instantiate 0 j a (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6]
      exact .app _ _ _ _ _ _ _ hf' ha'
  | j, _, _, _, .letE Γ A u value B body hA hv hb, hget, hvty, hcv => by
      have hA' := convT_substCongr hcl hinst v v' t hA hget hvty hcv
      simp only [instantiate] at hA'
      have hv' := convT_substCongr hcl hinst v v' t hv hget hvty hcv
      have hvty' :
          HasTyT E n (substRemove v (j+1) (.letBinding A value :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) t) := by
        have h0 := hasTyTWeaken (instDecl j v (.letBinding A value)) hcl (c := 0) hvty
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hcv' :
          ConvT E n (substRemove v (j+1) (.letBinding A value :: Γ))
            (lift 0 (j+1) v) (lift 0 (j+1) v') (lift 0 (j+1) t) := by
        have h0 := convTWeaken (instDecl j v (.letBinding A value)) hcl (c := 0) hcv
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hget' : (.letBinding A value :: Γ)[j+1]? = some (.assumption t) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hb' := convT_substCongr hcl hinst v v' t hb hget' hvty' hcv'
      simp only [substRemove_succ_cons, instDecl] at hb'
      have h6 := instantiate_instantiate 0 j value (lift 0 j v) (by omega) B
      simp only [instantiate, instantiate0]
      rw [h6, lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v),
          lift_lift_merge 1 j 0 0 (by omega) (by omega) (e := v')]
      exact .letE _ _ _ _ _ _ _ _ u hA' hv' hb'
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvty, _ => by
      have hexp' := hasTyT_substS hcl hinst v t hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      simp only [instantiate]
      exact .refl _ _ _ (.lit _ _ _ hexp')
  | j, _, _, _, .conv Γ e A B u h hc, hget, hvty, hcv =>
      .tyConv _ _ _ _ _ u (convT_substCongr hcl hinst v v' t h hget hvty hcv)
        (convT_substS hcl hinst v t hc hget hvty)
  termination_by j Γ e T h _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- `CtxWfT` of a substRemoved assumption telescope: removing the outermost
    domain `D` at `|ΔT|` instantiates each remaining stored type (`telSubstLast`);
    every instantiated domain stays a sort via `hasTyT_substS`, with the
    replacement typing supplied per-level by `hasTyTLiftPrefix` of `v : D`. -/
def ctxWfT_telSubstLast {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (ΔT : List (Expr Nat)) → {Γ : LCtx} → {v D : Expr Nat} →
    CtxWfT E n (ΔT.map LocalDecl.assumption ++ .assumption D :: Γ) →
    HasTyT E n Γ v D →
    CtxWfT E n ((telSubstLast v ΔT).map LocalDecl.assumption ++ Γ)
  | [], Γ, v, D, hΓ, _hv => by
      simp only [List.map_nil, List.nil_append, telSubstLast] at *
      cases hΓ with
      | assumption _ _ _ hΓ' _ => exact hΓ'
  | D₀ :: ΔT, Γ, v, D, hΓ, hv => by
      simp only [List.map_cons, List.cons_append, telSubstLast]
      rw [List.map_cons, List.cons_append] at hΓ
      cases hΓ with
      | assumption _ _ u₀ hΓ0 hD0 =>
          have hIH := ctxWfT_telSubstLast hcl hinst ΔT hΓ0 hv
          have hget :
              (ΔT.map LocalDecl.assumption ++ .assumption D :: Γ)[ΔT.length]? =
                some (.assumption D) := by
            rw [List.getElem?_append_right
              (by simp : (ΔT.map LocalDecl.assumption).length ≤ ΔT.length)]
            simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero]
          have hvty : HasTyT E n
              (substRemove v ΔT.length
                (ΔT.map LocalDecl.assumption ++ .assumption D :: Γ))
              (lift 0 ΔT.length v) (lift 0 ΔT.length D) := by
            rw [substRemove_tel_assumption]
            have hw := hasTyTLiftPrefix hcl
              ((telSubstLast v ΔT).map LocalDecl.assumption) hv
            rwa [List.length_map, telSubstLast_length] at hw
          have hD0' := hasTyT_substS hcl hinst v D (j := ΔT.length)
            hD0 hget hvty
          rw [substRemove_tel_assumption] at hD0'
          simp only [instantiate] at hD0'
          exact CtxWfT.assumption _ _ u₀ hIH hD0'

/-- conversion-side two-endpoint substitution congruence: a `ConvT a b T`
    derivation moves through instantiation of the same assumption binder by
    two convertible replacements — left endpoint instantiated at `v`, right at
    `v'`, type at the left instantiation. `hb` is the right endpoint's typing,
    supplied at each step (at the top level by `endpoints3`-family). -/
def convT_substCongrC {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (v v' t : Expr Nat)
    {j : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (hb : HasTyT E n Γ b T)
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hcv : ConvT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j v')
      (lift 0 j t)) :
    ConvT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v') b)
      (instantiate j (lift 0 j v) T) :=
  .trans _ _ _ _ _ (convT_substS hcl hinst v t h hget hvty)
    (convT_substCongr hcl hinst v v' t hb hget hvty hcv)

/-- telescope-instantiation congruence for `ConvT` — the `convT_substCongrC`
    iteration, mirroring `hasTyT_instPrefix`'s structure: `ΔT` assumption
    domains over `Γ`, a conversion `a ≡ b` under the telescope (plus the right
    endpoint's typing `hb`, carried forward per step by `endpoints3`), the
    telescope context's wellformedness (for the `ctxWfT_telSubstLast` /
    `endpoints3` chain), per-argument conversions `args[i] ≡ args'[i]` at the
    LEFT-instantiated `i`-th outermost domain, and the left arguments' typings
    at those domains. Produces `instPrefix args a ≡ instPrefix args' b` at
    `instPrefix args T` — the `.drecD` transport: whnf-derived indices convert
    against the declared indices pointwise, and this carries the conversion
    through the telescope instantiation. Debts: `SubstLetT`/`ConstsRightDataT`
    (for `endpoints3`'s right-endpoint typing). -/
def convT_instPrefix {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) :
    (args args' : List (Expr Nat)) → {Γ : LCtx} → {ΔT : List (Expr Nat)} →
    {a b T : Expr Nat} →
    (hlen : ΔT.length = args.length) →
    (hlen' : args'.length = args.length) →
    CtxWfT E n (ΔT.map LocalDecl.assumption ++ Γ) →
    ConvT E n (ΔT.map LocalDecl.assumption ++ Γ) a b T →
    HasTyT E n (ΔT.map LocalDecl.assumption ++ Γ) b T →
    (∀ i (hi : i < args.length),
      ConvT E n Γ args[i] args'[i]
        (instPrefix (args.take i) (outerDom ΔT i))) →
    (∀ i (hi : i < args.length),
      HasTyT E n Γ args[i]
        (instPrefix (args.take i) (outerDom ΔT i))) →
    ConvT E n Γ (instPrefix args a) (instPrefix args' b) (instPrefix args T)
  | [], args', _, ΔT, _, _, _, hlen, hlen', _, h, _, _, _ => by
      cases ΔT with
      | nil =>
          cases args' with
          | nil =>
              simpa only [List.map_nil, List.nil_append, instPrefix] using h
          | cons a' as' =>
              simp only [List.length_cons, List.length_nil] at hlen'
              exact absurd hlen' (Nat.succ_ne_zero _)
      | cons => simp only [List.length_cons, List.length_nil] at hlen
                omega
  | a :: as, [], _, _, _, _, _, _, hlen', _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen'; omega
  | a :: as, a' :: as', Γ, ΔT, x, y, T, hlen, hlen', hΓΔ, h, hb,
    hargs, htyped => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hnn : ΔT ≠ [] := by
        intro hnil
        rw [hnil, List.length_nil] at hlen
        exact Nat.noConfusion hlen
      generalize hΔT' : ΔT.dropLast = ΔT'
      generalize hD : ΔT.getLast hnn = D
      have hΔ : ΔT = ΔT' ++ [D] := by
        rw [← hΔT', ← hD]
        exact (List.dropLast_concat_getLast hnn).symm
      clear hΔT' hD
      subst hΔ
      have hlenT : ΔT'.length = as.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hlen
        omega
      have hlenas : as'.length = as.length := by
        simp only [List.length_cons] at hlen'; omega
      have hctx : (ΔT' ++ [D]).map LocalDecl.assumption ++ Γ =
          ΔT'.map LocalDecl.assumption ++ (.assumption D :: Γ) := by
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append]
      rw [hctx] at hΓΔ h hb
      have hget :
          (ΔT'.map LocalDecl.assumption ++ .assumption D :: Γ)[ΔT'.length]? =
            some (.assumption D) := by
        rw [List.getElem?_append_right
          (by simp : (ΔT'.map LocalDecl.assumption).length ≤ ΔT'.length)]
        simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero]
      have hlast : outerDom (ΔT' ++ [D]) 0 = D := by
        have hidx : (ΔT' ++ [D]).length - 1 - 0 = ΔT'.length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [outerDom, List.getD_eq_getElem?_getD, hidx]
        rw [List.getElem?_append_right (Nat.le_refl ΔT'.length)]
        simp
      have ha0 : HasTyT E n Γ a D := by
        have h0 := htyped 0 (Nat.succ_pos _)
        rw [hlast] at h0
        simpa only [List.getElem_cons_zero, List.take_zero, instPrefix]
          using h0
      have hc0 : ConvT E n Γ a a' D := by
        have h0 := hargs 0 (Nat.succ_pos _)
        rw [hlast] at h0
        simpa only [List.getElem_cons_zero, List.take_zero, instPrefix]
          using h0
      have hvty : HasTyT E n
          (substRemove a ΔT'.length
            (ΔT'.map LocalDecl.assumption ++ .assumption D :: Γ))
          (lift 0 ΔT'.length a) (lift 0 ΔT'.length D) := by
        rw [substRemove_tel_assumption]
        have hw := hasTyTLiftPrefix hcl
          ((telSubstLast a ΔT').map LocalDecl.assumption) ha0
        rwa [List.length_map, telSubstLast_length] at hw
      have hcv : ConvT E n
          (substRemove a ΔT'.length
            (ΔT'.map LocalDecl.assumption ++ .assumption D :: Γ))
          (lift 0 ΔT'.length a) (lift 0 ΔT'.length a')
          (lift 0 ΔT'.length D) := by
        rw [substRemove_tel_assumption]
        have hw := convTLiftPrefix hcl
          ((telSubstLast a ΔT').map LocalDecl.assumption) hc0
        rwa [List.length_map, telSubstLast_length] at hw
      have hstep := convT_substCongrC hcl hinst a a' D (j := ΔT'.length)
        h hb hget hvty hcv
      rw [substRemove_tel_assumption] at hstep
      have hΓΔ' : CtxWfT E n
          ((telSubstLast a ΔT').map LocalDecl.assumption ++ Γ) :=
        ctxWfT_telSubstLast hcl hinst ΔT' hΓΔ ha0
      have hb' := (endpoints3_of_envWfT hW hSL hconst hΓΔ' hstep).2.1
      rw [hlenT] at hstep hb'
      simp only [instPrefix]
      rw [hlenas]
      refine convT_instPrefix hW hSL hconst as as'
        (ΔT := telSubstLast a ΔT')
        (a := instantiate as.length (lift 0 as.length a) x)
        (b := instantiate as.length (lift 0 as.length a') y)
        (T := instantiate as.length (lift 0 as.length a) T) ?_ hlenas
        hΓΔ' hstep hb' ?_ ?_
      · exact (telSubstLast_length a ΔT').trans hlenT
      · intro i hi
        have hb : as.length - 1 - i < ΔT'.length := by rw [hlenT]; omega
        have hdom : outerDom (ΔT' ++ [D]) (i + 1) =
            (ΔT'[as.length - 1 - i]'(hb)) := by
          have hidx : (ΔT' ++ [D]).length - 1 - (i + 1) =
              as.length - 1 - i := by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega
          simp only [outerDom, List.getD_eq_getElem?_getD, hidx,
            List.getElem?_append_left hb, List.getElem?_eq_getElem hb,
            Option.getD_some]
        have hsrc := hargs (i + 1) (Nat.succ_lt_succ hi)
        rw [hdom] at hsrc
        simp only [List.getElem_cons_succ, List.take_succ_cons, instPrefix,
          List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hsrc
        have hdom' : outerDom (telSubstLast a ΔT') i =
            instantiate i (lift 0 i a) (ΔT'[as.length - 1 - i]'(hb)) := by
          have hb' : ΔT'.length - 1 - i < ΔT'.length := by
            rw [hlenT]; omega
          have hlt2 : (telSubstLast a ΔT').length - 1 - i =
              ΔT'.length - 1 - i := by rw [telSubstLast_length]
          simp only [outerDom, List.getD_eq_getElem?_getD, hlt2]
          rw [telSubstLast_getElem? a ΔT' (ΔT'.length - 1 - i) hb']
          have hidx' : ΔT'.length - 1 - i = as.length - 1 - i := by
            rw [hlenT]
          rw [getElem_idx_congr hidx' hb' hb]
          have hsub : ΔT'.length - 1 - (ΔT'.length - 1 - i) = i := by
            omega
          rw [hsub, Option.getD_some]
        rw [hdom']
        exact hsrc
      · intro i hi
        have hb : as.length - 1 - i < ΔT'.length := by rw [hlenT]; omega
        have hdom : outerDom (ΔT' ++ [D]) (i + 1) =
            (ΔT'[as.length - 1 - i]'(hb)) := by
          have hidx : (ΔT' ++ [D]).length - 1 - (i + 1) =
              as.length - 1 - i := by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega
          simp only [outerDom, List.getD_eq_getElem?_getD, hidx,
            List.getElem?_append_left hb, List.getElem?_eq_getElem hb,
            Option.getD_some]
        have hsrc := htyped (i + 1) (Nat.succ_lt_succ hi)
        rw [hdom] at hsrc
        simp only [List.getElem_cons_succ, List.take_succ_cons, instPrefix,
          List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hsrc
        have hdom' : outerDom (telSubstLast a ΔT') i =
            instantiate i (lift 0 i a) (ΔT'[as.length - 1 - i]'(hb)) := by
          have hb' : ΔT'.length - 1 - i < ΔT'.length := by
            rw [hlenT]; omega
          have hlt2 : (telSubstLast a ΔT').length - 1 - i =
              ΔT'.length - 1 - i := by rw [telSubstLast_length]
          simp only [outerDom, List.getD_eq_getElem?_getD, hlt2]
          rw [telSubstLast_getElem? a ΔT' (ΔT'.length - 1 - i) hb']
          have hidx' : ΔT'.length - 1 - i = as.length - 1 - i := by
            rw [hlenT]
          rw [getElem_idx_congr hidx' hb' hb]
          have hsub : ΔT'.length - 1 - (ΔT'.length - 1 - i) = i := by
            omega
          rw [hsub, Option.getD_some]
        rw [hdom']
        exact hsrc

/-- `(l.take j).reverse[j-1-i] = l[i]` for `i < j ≤ l.length` — the
    outermost-first lookup for a reversed prefix telescope (`outerDom`
    arithmetic, shared by the `convT_instPrefix` premises). -/
theorem getElem_reverse_take {α : Type} (l : List α) {j i : Nat}
    (hj : j ≤ l.length) (hi : i < j) :
    (l.take j).reverse[j - 1 - i]'(by
      simp only [List.length_reverse, List.length_take]; omega) =
      l[i]'(by omega) := by
  rw [List.getElem_reverse]
  simp only [List.length_take, Nat.min_eq_left hj, List.getElem_take]
  congr 1; omega

/-- `CtxWfT` of a telescope's prefix context from per-domain sort typings —
    builds the `policyPrefixContext` chain bottom-up, each domain a fresh
    assumption over the prefix below it. -/
def ctxWfT_of_doms {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {lv : Nat → Level} : (doms : List (Expr Nat)) →
    (∀ j (hj : j < doms.length),
      HasTyT E n (policyPrefixContext doms j ++ Γ)
        (doms[j]'hj) (.sort (lv j))) →
    CtxWfT E n (policyPrefixContext doms doms.length ++ Γ)
  | [], _ => by
      simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
        List.map_nil, List.nil_append] using hΓ
  | D :: doms, h => by
      have hD : HasTyT E n Γ D (.sort (lv 0)) := by
        simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
          List.map_nil, List.nil_append, List.getElem_cons_zero]
          using h 0 (Nat.succ_pos _)
      have hΓD : CtxWfT E n (.assumption D :: Γ) := .assumption _ _ _ hΓ hD
      have hIH := ctxWfT_of_doms (Γ := .assumption D :: Γ)
          (lv := fun j => lv (j + 1)) hΓD doms (fun j hj => by
        have hstep := h (j + 1) (Nat.succ_lt_succ hj)
        rwa [policyPrefixContext_cons_succ, List.getElem_cons_succ] at hstep)
      simpa only [policyPrefixContext, List.length_cons, List.take_succ_cons,
        List.take_length, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
        using hIH

/-- `ArgsTyT` under pointwise argument conversion: `args[j] ≡ args'[j]` at
    the LEFT-instantiated `j`-th domain transports the whole spine. Each step
    types the left endpoint of the conversion by `endpoints3`, then converts
    the left-instantiated domain to the right-instantiated one by
    `convT_instPrefix` (the `.drecD` whnf'd-index payment). Debts:
    `SubstLetT`/`ConstsRightDataT`; per-domain sort typings `hdoms` come from
    `hasTyT_policyPi_invT` at the callsite. -/
def argsTyT_conv {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {doms args args' : List (Expr Nat)} {l : Level} (lv : Nat → Level)
    (hl : args.length = doms.length) (hl' : args'.length = args.length)
    (hargs0 : ArgsTyT E n Γ (policyPi doms (.sort l)) args)
    (hdoms : ∀ j (hj : j < doms.length),
      HasTyT E n (policyPrefixContext doms j ++ Γ)
        (doms[j]'hj) (.sort (lv j)))
    (hconvs : ∀ j (hj : j < doms.length),
      ConvT E n Γ (args'[j]'(by rw [hl', hl]; exact hj)) (args[j]'(by omega))
        (instPrefix (args.take j) (doms[j]'hj))) :
    ArgsTyT E n Γ (policyPi doms (.sort l)) args' := by
  refine argsTyT_mk doms args' (hl'.trans hl) (fun j hj => ?_)
  have hjargs : j < args.length := by rw [← hl']; exact hj
  have hjdoms : j < doms.length := by rw [← hl]; exact hjargs
  have hc := hconvs j hjdoms
  have hbj := (endpoints3_of_envWfT hW hSL hconst hΓ hc).1
  have hdomj := hdoms j hjdoms
  have hΓΔ : CtxWfT E n (policyPrefixContext doms j ++ Γ) := by
    have h0 := ctxWfT_of_doms hΓ (lv := lv) (doms.take j) (fun k hk => by
      have hkj : k < j := by rw [List.length_take] at hk; omega
      have hppc' : policyPrefixContext (doms.take j) k =
          policyPrefixContext doms k := by
        simp only [policyPrefixContext, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt hkj)]
      have hstep := hdoms k (by rw [List.length_take] at hk; omega)
      rwa [hppc', List.getElem_take])
    simpa only [policyPrefixContext, List.take_length] using h0
  have hconvj : ConvT E n Γ
      (instPrefix (args.take j) (doms[j]'hjdoms))
      (instPrefix (args'.take j) (doms[j]'hjdoms)) (.sort (lv j)) := by
    have hrfl : ConvT E n (((doms.take j).reverse).map .assumption ++ Γ)
        (doms[j]'hjdoms) (doms[j]'hjdoms) (.sort (lv j)) :=
      .refl _ _ _ (by simpa only [policyPrefixContext] using hdomj)
    have hΔlen : ((doms.take j).reverse).length = (args.take j).length := by
      simp only [List.length_reverse, List.length_take]; omega
    have halen : (args'.take j).length = (args.take j).length := by
      simp only [List.length_take]; omega
    have hod : ∀ i, i < j → (hid : i < doms.length) →
        outerDom ((doms.take j).reverse) i = doms[i]'hid := fun i hij hid => by
      have hΔlen' : ((doms.take j).reverse).length = j := by
        simp only [List.length_reverse, List.length_take]; omega
      rw [outerDom_eq_getElem _ _ (by rw [hΔlen']; omega)]
      simp only [hΔlen', List.getElem_reverse, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hjdoms), List.getElem_take]
      congr 1; omega
    have hcj := convT_instPrefix hW hSL hconst (args.take j) (args'.take j)
      (ΔT := (doms.take j).reverse) (Γ := Γ)
      (a := (doms[j]'hjdoms)) (b := (doms[j]'hjdoms)) (T := .sort (lv j))
      hΔlen halen hΓΔ hrfl
      (by simpa only [policyPrefixContext] using hdomj)
      (fun i hi => by
        have hij : i < j := by
          rw [List.length_take] at hi; omega
        have hi' : i < args.length := by omega
        have hid : i < doms.length := by omega
        have htk : (args.take j).take i = args.take i := by
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
        have hconv0 := hconvs i hid
        have hconv0' : ConvT E n Γ (args[i]'hi') (args'[i]'(by omega))
            (instPrefix (args.take i) (doms[i]'hid)) :=
          .symm _ _ _ _ hconv0
        simpa only [List.getElem_take, htk, hod i hij hid] using hconv0')
      (fun i hi => by
        have hij : i < j := by
          rw [List.length_take] at hi; omega
        have hi' : i < args.length := by omega
        have hid : i < doms.length := by omega
        have htk : (args.take j).take i = args.take i := by
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
        have hty0 := argsTyT_getElem doms args hl _ rfl hargs0 i hi'
        simpa only [List.getElem_take, htk, hod i hij hid] using hty0)
    simpa only [instPrefix_sort] using hcj
  exact HasTyT.conv _ _ _ _ _ hbj hconvj

/-- `ConvArgsT` preserves argument-list length. -/
def convArgsT_length {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {xs xs' : List (Expr Nat)}
    (h : ConvArgsT E n Γ T xs xs') : xs.length = xs'.length := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

/-- per-argument conversion along a `policyPi` telescope — the `ConvArgsT` analog of
    `argsTyT_getElem`: `xs[j] ≡ xs'[j]` at the `instPrefix`-instantiated domain. -/
def convArgsT_getElem {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (doms xs : List (Expr Nat)) → (hl : xs.length = doms.length) →
    (T : Expr Nat) → T = policyPi doms (.sort l) →
    {ys : List (Expr Nat)} → (h : ConvArgsT E n Γ T xs ys) →
    ∀ j (hj : j < xs.length),
      Nonempty (ConvT E n Γ xs[j]
        (ys.get ⟨j, by have := convArgsT_length h; omega⟩)
        (instPrefix (xs.take j) (doms[j]'(by omega))))
  | [], args, hl, _, _, _, _, j, hj => absurd hj (by simp only [List.length_nil] at hl; omega)
  | D :: doms, [], hl, _, _, _, _, _, _ => absurd hl (by simp)
  | D :: doms, a :: as, hl, T, hT, _, h, j, hj =>
      match h, hT with
      | .cons A B _ _ _ fs' hf hfs, hT' => by
          have hT'' : Expr.pi A B = Expr.pi D (policyPi doms (.sort l)) := hT'
          injection hT'' with hA hB
          subst hA hB
          cases j with
          | zero => exact hf
          | succ j' =>
              have hlen : as.length = doms.length := by
                simp only [List.length_cons] at hl; omega
              have hl' : as.length = (instDomsT 0 a doms).length := by
                rw [length_instDomsT]; exact hlen
              have htl : ConvArgsT E n Γ (policyPi (instDomsT 0 a doms) (.sort l)) as fs' := by
                have := hfs
                rw [instantiate0, instantiate_policyPi] at this
                exact this
              have hstep := convArgsT_getElem (instDomsT 0 a doms) as hl' _ rfl htl j'
                (Nat.lt_of_succ_lt_succ hj)
              rw [getElem_instDomsT, Nat.zero_add] at hstep
              show Nonempty (ConvT E n Γ (as[j']'(by simp only [List.length_cons] at hj; omega))
                _
                (instPrefix (a :: as.take j')
                  (doms[j']'(by simp only [List.length_cons] at hl hj; omega))))
              rw [instPrefix_cons, List.length_take,
                Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_succ_lt_succ hj))]
              exact hstep

/-- dropping a matched prefix from a `ConvArgsT` spine — the residual `T` is the
    `inst0`-walked tail telescope. -/
def convArgsT_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} :
    (as as' : List (Expr Nat)) → as.length = as'.length → {xs bs : List (Expr Nat)} →
    ConvArgsT E n Γ T (as ++ xs) (as' ++ bs) →
    ∃ T', ConvArgsT E n Γ T' xs bs
  | [], [], _, xs, bs, h => ⟨T, by simpa only [List.nil_append] using h⟩
  | a :: rest, a' :: rest', hl, xs, bs, h => by
      rw [List.cons_append, List.cons_append] at h
      cases h with
      | cons A B f f' fs fs' hf hs =>
          exact convArgsT_drop rest rest' (by simpa using hl) hs
  | [], _ :: _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _, _ => absurd hl (by simp)

/-- reflexive argument conversion — every typed argument spine converts to itself. -/
def convArgsT_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {T : Expr Nat} → {xs : List (Expr Nat)} →
    ArgsTyT E n Γ T xs → ConvArgsT E n Γ T xs xs
  | _, _, .nil l => .nil _
  | _, _, .cons A B a as ha tl =>
      .cons A B a a as as ⟨.refl _ _ _ ha⟩ (convArgsT_refl tl)

/-- restating a `ConvArgsT` at a definitionally-stated equal telescope. -/
def convArgsT_cast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T T' : Expr Nat} {xs xs' : List (Expr Nat)}
    (h : ConvArgsT E n Γ T xs xs') (hT : T = T') : ConvArgsT E n Γ T' xs xs' :=
  hT ▸ h

/-- `instPrefix` is `instTelK` at offset `0` — the same recursion. -/
theorem instPrefix_eq_instTelK (as : List (Expr Nat)) (e : Expr Nat) :
    instPrefix as e = instTelK 0 as e := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
      show instPrefix as (instantiate as.length (lift 0 as.length a) e) = _
      rw [ih, instTelK_cons, Nat.zero_add]

/-- a `liftDomsT` whose per-domain lift fixes every element is the identity. -/
theorem liftDomsT_self (c a : Nat) : (ds : List (Expr Nat)) →
    (∀ i (hi : i < ds.length), lift (c + i) a (ds[i]'hi) = ds[i]) →
    liftDomsT c a ds = ds
  | [], _ => rfl
  | D :: ds, h => by
      show lift c a D :: liftDomsT (c + 1) a ds = D :: ds
      have h0 : lift c a D = D := by
        have := h 0 (Nat.zero_lt_succ _)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using this
      have htl : liftDomsT (c + 1) a ds = ds :=
        liftDomsT_self (c + 1) a ds (fun i hi => by
          have := h (i + 1) (Nat.succ_lt_succ hi)
          rwa [List.getElem_cons_succ,
            show c + (i + 1) = c + 1 + i from by omega] at this)
      rw [h0, htl]

/-- parameter-local instantiation of an index telescope — the `descSpine`/`ppL`
    transport lands at the `idxTelAt`-shifted form. -/
private theorem instPrefix_ppL_policyPi (np k : Nat) (Is : List (Expr Nat)) (l : Level)
    (hbnd : ∀ i (hi : i < Is.length), lift (i + np) 1 (Is[i]'hi) = Is[i]) :
    instPrefix (policyParameterLocals np k) (policyPi Is (.sort l)) =
      policyPi (liftDomsT 0 k Is) (.sort l) := by
  have hcl : lift (0 + np) 1 (policyPi Is (.sort l)) = policyPi Is (.sort l) := by
    rw [lift_policyPi]
    have hd : liftDomsT np 1 Is = Is := liftDomsT_self np 1 Is (fun i hi => by
      have := hbnd i hi
      rwa [Nat.add_comm] at this)
    rw [Nat.zero_add, hd]
    rfl
  rw [instPrefix_eq_instTelK, ← descSpine_eq_ppL k np, instTelK_descSpine 0 k np _ hcl]
  rw [lift_policyPi]
  rfl

/-- argument conversions assembled under `foldApps` — the head converts at the
    full telescope, each argument converts at its instantiated domain. -/
def convT_foldApps_args {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (doms xs : List (Expr Nat)) → (hl : xs.length = doms.length) →
    {xs' : List (Expr Nat)} → (hl' : xs'.length = xs.length) →
    (h h' U : Expr Nat) →
    Nonempty (ConvT E n Γ h h' (policyPi doms U)) →
    (∀ i (hi : i < xs.length),
      Nonempty (ConvT E n Γ xs[i]
        xs'[i]
        (instPrefix (xs.take i) (doms[i]'(by omega))))) →
    Nonempty (ConvT E n Γ (foldApps h xs) (foldApps h' xs') (instPrefix xs U))
  | [], xs, hl, xs', hl', h, h', U, hhead, _ => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp only [List.length_cons, List.length_nil] at hl; omega
      subst hxs
      have hxs' : xs' = [] := by
        cases xs' with
        | nil => rfl
        | cons _ _ => simp only [List.length_cons, List.length_nil] at hl'; omega
      subst hxs'
      simpa only [foldApps, instPrefix] using hhead
  | _ :: _, [], hl, _, _, _, _, _, _, _ => absurd hl (by simp)
  | D :: doms, a :: as, hl, [], hl', _, _, _, _, _ => absurd hl' (by simp)
  | D :: doms, a :: as, hl, a' :: as', hl', h, h', U, hhead, hper => by
      obtain ⟨ch⟩ := hhead
      obtain ⟨ca⟩ := hper 0 (Nat.zero_lt_succ _)
      have hstep0 : ConvT E n Γ (.app h a) (.app h' a')
          (instantiate0 a (policyPi doms U)) :=
        .app _ _ _ _ _ _ _ ch ca
      rw [instantiate0, instantiate_policyPi, Nat.zero_add] at hstep0
      have hlas : as.length = doms.length := by
        simp only [List.length_cons] at hl; omega
      have hlas' : as'.length = as.length := by
        simp only [List.length_cons] at hl'; omega
      have hrec := convT_foldApps_args (instDomsT 0 a doms) as
        (by rw [length_instDomsT]; exact hlas) hlas'
        (.app h a) (.app h' a')
        (instantiate doms.length (lift 0 doms.length a) U)
        ⟨hstep0⟩ (fun i hi => by
          have hlt : i < doms.length := by omega
          have hperi := hper (i + 1) (Nat.succ_lt_succ hi)
          rw [getElem_instDomsT _ _ _ _ hlt]
          simpa only [List.getElem_cons_succ, List.take_succ_cons, instPrefix_cons,
            List.length_take, Nat.min_eq_left (Nat.le_of_lt hi),
            Nat.zero_add] using hperi)
      rw [instPrefix_cons, hlas]
      exact hrec

/-- congruence under `policyPi` domains: a body conversion inside the telescope's
    full prefix context extends to a conversion of the whole telescopes. -/
def convT_policyPi_body {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (doms : List (Expr Nat)) → (lv : Fin doms.length → Level) →
    (∀ i : Fin doms.length,
      HasTyT E n (policyPrefixContext doms i ++ Γ) doms[i] (.sort (lv i))) →
    (B B' : Expr Nat) → (uB : Level) →
    ConvT E n (policyPrefixContext doms doms.length ++ Γ) B B' (.sort uB) →
    Nonempty (ConvT E n Γ (policyPi doms B) (policyPi doms B')
      (.sort (piSortT doms.length lv uB)))
  | [], _, _, B, B', _, hc =>
      ⟨by simpa only [policyPrefixContext, List.take_nil, List.reverse_nil, List.map_nil,
        List.nil_append, List.length_nil, policyPi, piSortT] using hc⟩
  | D :: doms, lv, hlv, B, B', uB, hc => by
      have hD0 : HasTyT E n Γ D (.sort (lv ⟨0, Nat.succ_pos _⟩)) := by
        have := hlv ⟨0, Nat.succ_pos _⟩
        simpa only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
          List.nil_append] using this
      have hppc : ∀ j, policyPrefixContext (D :: doms) (j + 1) ++ Γ =
          policyPrefixContext doms j ++ (.assumption D :: Γ) := by
        intro j
        simp only [policyPrefixContext, List.take_succ_cons, List.reverse_cons,
          List.map_append, List.map_cons, List.map_nil, List.singleton_append,
          List.append_assoc]
      have hlv' : ∀ i : Fin doms.length,
          HasTyT E n (policyPrefixContext doms i ++ (.assumption D :: Γ)) doms[i]
            (.sort (lv ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) := by
        intro i
        have := hlv ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        rwa [hppc i.val] at this
      have hc' : ConvT E n (policyPrefixContext doms doms.length ++ (.assumption D :: Γ))
          B B' (.sort uB) := by
        have := hc
        rw [List.length_cons, hppc doms.length] at this
        exact this
      obtain ⟨ct⟩ := convT_policyPi_body doms
        (fun i => lv ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) hlv' B B' uB hc'
      exact ⟨by
        have hpi := ConvT.pi _ D D (policyPi doms B) (policyPi doms B')
          (lv ⟨0, Nat.succ_pos _⟩)
          (piSortT doms.length (fun i => lv ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) uB)
          (.refl _ _ _ hD0) ct
        simpa only [policyPi, piSortT, Fin.val_zero, Fin.succ] using hpi⟩

/-- `liftDomsT c a` is the position-indexed lift — `ds.mapIdx (lift (c + ·) a)`. -/
private theorem liftDomsT_eq_mapIdx (c a : Nat) :
    (ds : List (Expr Nat)) →
      liftDomsT c a ds = ds.mapIdx (fun i D => lift (c + i) a D)
  | [] => rfl
  | D :: ds => by
      show lift c a D :: liftDomsT (c + 1) a ds = _
      rw [List.mapIdx_cons, liftDomsT_eq_mapIdx]
      congr 1
      apply mapIdx_congr'
      intro i hi
      show lift (c + 1 + i) a ds[i] = lift (c + (i + 1)) a ds[i]
      rw [show c + 1 + i = c + (i + 1) from by omega]

/-- `insertChain` with a trailing pair inserts it last — the innermost-first fold. -/
theorem insertChain_append_one (xs : List (LocalDecl × Nat)) (p : LocalDecl × Nat)
    (Γ : LCtx) :
    insertChain (xs ++ [p]) Γ = insertAt p.1 p.2 (insertChain xs Γ) := by
  induction xs generalizing Γ with
  | nil => rfl
  | cons q xs ih => simp only [List.cons_append, insertChain]
                    exact ih _

/-- the decl-wise lift an `insertAt` at a prefix boundary applies: each decl is
    `liftDecl`-ed at its distance to the boundary (the innermost gets the highest
    cutoff — matching `insertAt`'s shrinking cutoff). -/
def liftDeclChain : LCtx → LCtx
  | [] => []
  | x :: xs => liftDecl xs.length x :: liftDeclChain xs

/-- `insertAt` at the boundary of a prefix block: the new decl lands directly on the
    tail, and each prefix decl is `liftDecl`-ed at its distance to the boundary. -/
theorem insertAt_append_boundary (d : LocalDecl) :
    (Γ₁ : LCtx) → (Γ₂ : LCtx) →
      insertAt d Γ₁.length (Γ₁ ++ Γ₂) = liftDeclChain Γ₁ ++ (d :: Γ₂)
  | [], _ => rfl
  | x :: xs, Γ₂ => by
      simp only [List.length_cons, List.cons_append, insertAt_succ_cons]
      rw [insertAt_append_boundary d xs Γ₂]
      rfl

/-- `liftDeclChain` preserves length. -/
theorem length_liftDeclChain : (Γ : LCtx) → (liftDeclChain Γ).length = Γ.length
  | [] => rfl
  | _ :: xs => by
      simp only [liftDeclChain, List.length_cons]
      rw [length_liftDeclChain xs]

/-- the `i`-th entry of `liftDeclChain Γ` is `Γ[i]` lifted at its distance to the
    tail of the context. -/
theorem getElem_liftDeclChain : (Γ : LCtx) → (i : Nat) → (hi : i < Γ.length) →
    (liftDeclChain Γ)[i]'(by rw [length_liftDeclChain]; exact hi) =
      liftDecl (Γ.length - 1 - i) Γ[i]
  | _ :: xs, 0, _ => by
      simp only [liftDeclChain, List.getElem_cons_zero, List.length_cons]
      congr 1
  | _ :: xs, i + 1, hi => by
      simp only [liftDeclChain, List.getElem_cons_succ, List.length_cons]
      rw [getElem_liftDeclChain xs i (Nat.lt_of_succ_lt_succ hi)]
      congr 1; omega

/-- a full prefix context entry: `policyPrefixContext ds ds.length` at `i` is the
    assumption of `ds[ds.length - 1 - i]`. -/
private theorem getElem_ppc_full (ds : List (Expr Nat)) (i : Nat) (hi : i < ds.length) :
    (policyPrefixContext ds ds.length)[i]'(by
      simp only [policyPrefixContext, List.length_map, List.length_reverse,
        List.take_length]; exact hi) =
      .assumption ds[ds.length - 1 - i] := by
  simp only [policyPrefixContext, List.take_length, List.getElem_map,
    List.getElem_reverse]

/-- `insertAt`'s `liftDecl` accumulation on a full prefix context equals emitting each
    domain lifted once at its own position — the `ctorSub (1 :: _)` tail step. -/
private theorem liftDeclChain_ppc (ds : List (Expr Nat)) :
    liftDeclChain (policyPrefixContext ds ds.length) =
      policyPrefixContext (ds.mapIdx fun i D => lift i 1 D) ds.length := by
  have hL : (policyPrefixContext ds ds.length).length = ds.length := by
    simp only [policyPrefixContext, List.length_map, List.length_reverse,
      List.take_length]
  apply List.ext_getElem
  · rw [length_liftDeclChain, hL]
    simp only [policyPrefixContext, List.length_map, List.length_reverse,
      List.length_take, List.length_mapIdx, Nat.min_eq_left (Nat.le_refl _)]
  · intro i hi1 hi2
    have hi : i < ds.length := by rwa [length_liftDeclChain, hL] at hi1
    have ht : (ds.mapIdx fun i D => lift i 1 D).take ds.length =
        ds.mapIdx fun i D => lift i 1 D :=
      List.take_of_length_le (by simp)
    simp only [getElem_liftDeclChain _ i (by rwa [hL]), hL,
      getElem_ppc_full ds i hi]
    simp only [policyPrefixContext, ht, List.getElem_map,
      List.getElem_reverse, List.length_mapIdx, List.getElem_mapIdx, liftDecl]

/-- `insertAt` at a full-prefix boundary: the prefix re-emits `lift i 1`-ed, the decl
    lands innermost of the tail. -/
private theorem insertAt_ppc_mapIdx (d : LocalDecl) (ds : List (Expr Nat)) (Γ : LCtx) :
    insertAt d ds.length (policyPrefixContext ds ds.length ++ Γ) =
      policyPrefixContext (ds.mapIdx fun i D => lift i 1 D) ds.length ++ (d :: Γ) := by
  have hL : (policyPrefixContext ds ds.length).length = ds.length := by
    simp only [policyPrefixContext, List.length_map, List.length_reverse,
      List.take_length]
  have hb := insertAt_append_boundary d (policyPrefixContext ds ds.length) Γ
  rw [hL] at hb
  rw [hb, liftDeclChain_ppc]

/-- `insertChain` on a concatenated pair list: the left block applies first. -/
theorem insertChain_append (xs ys : List (LocalDecl × Nat)) (Γ : LCtx) :
    insertChain (xs ++ ys) Γ = insertChain ys (insertChain xs Γ) := by
  induction xs generalizing Γ with
  | nil => rfl
  | cons p xs ih => simp only [List.cons_append, insertChain]; exact ih _

/-- iterated `liftDecl c`, `k` times — the boundary-insert's accumulated lifting. -/
def liftDeclN (c k : Nat) : LocalDecl → LocalDecl
  | .assumption A => .assumption (lift c k A)
  | .letBinding A v => .letBinding (lift c k A) (lift c k v)

private theorem liftDecl_liftDeclN (c k : Nat) (d : LocalDecl) :
    liftDecl c (liftDeclN c k d) = liftDeclN c (k + 1) d := by
  cases d with
  | assumption A =>
      show LocalDecl.assumption (lift c 1 (lift c k A)) = .assumption (lift c (k + 1) A)
      rw [lift_lift_merge 1 k c c (Nat.le_refl c) (Nat.le_add_left c k)]
  | letBinding A v =>
      show LocalDecl.letBinding (lift c 1 (lift c k A)) (lift c 1 (lift c k v)) =
          .letBinding (lift c (k + 1) A) (lift c (k + 1) v)
      rw [lift_lift_merge 1 k c c (Nat.le_refl c) (Nat.le_add_left c k),
          lift_lift_merge 1 k c c (Nat.le_refl c) (Nat.le_add_left c k)]

/-- `liftDeclChain` distributes over `mapIdx`. -/
private theorem liftDeclChain_mapIdx (g : Nat → LocalDecl → LocalDecl) (X : LCtx) :
    liftDeclChain (X.mapIdx g) =
      X.mapIdx (fun i d => liftDecl (X.length - 1 - i) (g i d)) := by
  apply List.ext_getElem
  · rw [length_liftDeclChain, List.length_mapIdx, List.length_mapIdx]
  · intro i h1 h2
    have h1' : i < (X.mapIdx g).length := by
      rw [length_liftDeclChain] at h1; exact h1
    exact (getElem_liftDeclChain _ _ h1').trans (by
      rw [List.length_mapIdx, List.getElem_mapIdx, List.getElem_mapIdx])

private theorem mapIdx_id' : (l : List LocalDecl) → l.mapIdx (fun _ d => d) = l
  | [] => rfl
  | x :: xs => by rw [List.mapIdx_cons, mapIdx_id' xs]

/-- `liftDeclChain` iterated `k` times = pointwise `liftDeclN`. -/
private theorem liftDeclChain_iter : (X : LCtx) → (k : Nat) →
    (List.range k).foldl (fun Γ _ => liftDeclChain Γ) X =
      X.mapIdx (fun i d => liftDeclN (X.length - 1 - i) k d) := by
  intro X k; induction k generalizing X with
  | zero =>
      show X = _
      have h : X.mapIdx (fun i d => liftDeclN (X.length - 1 - i) 0 d) =
          X.mapIdx (fun _ d => d) := mapIdx_congr' X fun i hi => by
        cases h' : X[i] with
        | assumption A =>
            show liftDeclN _ 0 (LocalDecl.assumption A) = _
            show LocalDecl.assumption (lift _ 0 A) = _; rw [lift_zero_idx]
        | letBinding A v =>
            show liftDeclN _ 0 (LocalDecl.letBinding A v) = _
            show LocalDecl.letBinding (lift _ 0 A) (lift _ 0 v) = _
            rw [lift_zero_idx, lift_zero_idx]
      rw [h, mapIdx_id']
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      show liftDeclChain ((List.range k).foldl _ X) = _
      rw [ih, liftDeclChain_mapIdx]
      apply mapIdx_congr'
      intro i hi
      exact liftDecl_liftDeclN _ _ _

/-- `foldl` over a mapped list when the step ignores the elements. -/
theorem foldl_map_ignore (g : Nat → Nat) (l : List Nat) (X : LCtx) :
    (l.map g).foldl (fun Γ _ => liftDeclChain Γ) X =
      l.foldl (fun Γ _ => liftDeclChain Γ) X := by
  induction l generalizing X with
  | nil => rfl
  | cons a as ih =>
      show (as.map g).foldl _ (liftDeclChain X) = as.foldl _ (liftDeclChain X)
      exact ih _

/-- `range (k+1)` unfolds to `0 :: map succ (range k)` for the fold. -/
theorem foldl_range_succ_liftDeclChain (k : Nat) (X : LCtx) :
    (List.range (k + 1)).foldl (fun Γ _ => liftDeclChain Γ) X =
      (List.range k).foldl (fun Γ _ => liftDeclChain Γ) (liftDeclChain X) := by
  rw [List.range_succ_eq_map]; show ((List.range k).map Nat.succ).foldl _ (liftDeclChain X) = _
  exact foldl_map_ignore _ _ _

/-- **the boundary insert**: `|Δ₁|` decls inserted at position `|X|` land between
    `X` and `Γ` (innermost pair-list head deepest), each `X`-decl `liftDecl`-iterated
    at its distance to the boundary — the `d`-past-parameters ctx layer. -/
private theorem insertChain_boundary :
    (Δ₁ : LCtx) → ∀ (X Γ : LCtx),
      insertChain (Δ₁.map (fun d => (d, X.length))) (X ++ Γ) =
        ((List.range Δ₁.length).foldl (fun Γ _ => liftDeclChain Γ) X) ++ Δ₁.reverse ++ Γ
  | [], X, Γ => by simp [insertChain]
  | d :: Δ₁', X, Γ => by
      show insertChain ((d, X.length) :: _) (X ++ Γ) = _
      rw [insertChain, insertAt_append_boundary]
      have hlen : (liftDeclChain X).length = X.length := length_liftDeclChain X
      show insertChain (Δ₁'.map (fun d => (d, X.length))) (liftDeclChain X ++ d :: Γ) = _
      rw [← hlen, insertChain_boundary Δ₁' (liftDeclChain X) (d :: Γ)]
      rw [List.length_cons, foldl_range_succ_liftDeclChain, List.reverse_cons,
        List.append_assoc, ← List.singleton_append, ← List.append_assoc,
        ← List.append_assoc, ← List.append_assoc]

/-- iterated `liftDeclChain` on a full prefix context: the emitted `liftDomsT`
    domains — `liftDeclChainᵏ (ppc ds |ds|) = ppc (ds.mapIdx (lift · k)) |ds|`. -/
private theorem liftDeclChainIter_ppc (ds : List (Expr Nat)) (k : Nat) :
    (List.range k).foldl (fun Γ _ => liftDeclChain Γ)
        (policyPrefixContext ds ds.length) =
      policyPrefixContext (ds.mapIdx fun i D => lift i k D) ds.length := by
  rw [liftDeclChain_iter]
  apply List.ext_getElem
  · rw [List.length_mapIdx]; simp only [policyPrefixContext, List.length_map,
      List.length_reverse, List.length_take, List.length_mapIdx,
      Nat.min_eq_left (Nat.le_refl _), List.take_length]
  · intro i h1 h2
    have hlen : (policyPrefixContext ds ds.length).length = ds.length := by
      simp only [policyPrefixContext, List.length_map, List.length_reverse,
        List.take_length]
    rw [List.getElem_mapIdx]
    have hi : i < ds.length := by rwa [List.length_mapIdx, hlen] at h1
    rw [getElem_ppc_full ds i hi]
    have ht : (ds.mapIdx fun i D => lift i k D).take ds.length =
        ds.mapIdx fun i D => lift i k D :=
      List.take_of_length_le (by simp)
    simp only [policyPrefixContext, ht, List.getElem_map, List.getElem_reverse,
      List.length_mapIdx, List.getElem_mapIdx, liftDeclN, hlen,
      List.length_map, List.length_reverse, List.take_length]

/-- **the ctx identity**: inserting the recursive fields' plain-form decls at their
    after-counts into the plain prefix context rebuilds the full emitted prefix
    context — `insertAt`'s `liftDecl` mechanics implement the `ctorSub` renaming. -/
private theorem insertChain_ctorInsPairs (f : Nat) (ls : List Level) (np : Nat) :
    (fs : List FieldT) → (pc : Nat) → (Γ : LCtx) →
    insertChain (ctorInsPairs f ls np fs pc) (plainCtxT fs Γ) =
      policyPrefixContext (ctorEmittedDoms f ls np pc fs) fs.length ++ Γ
  | [], _, _ => rfl
  | .plain D u :: fs, pc, Γ => by
      simp only [ctorInsPairs, plainCtxT, ctorEmittedDoms_cons_plain,
        List.length_cons]
      rw [insertChain_ctorInsPairs f ls np fs (pc + 1) (.assumption D :: Γ),
        policyPrefixContext_cons_succ]
  | .drec idx :: fs, pc, Γ => by
      simp only [ctorInsPairs, plainCtxT, ctorEmittedDoms_cons_drec,
        List.length_cons]
      rw [insertChain_append_one, insertChain_ctorInsPairs f ls np fs pc Γ]
      dsimp only
      rw [← ctorEmittedDoms_length, insertAt_ppc_mapIdx,
        policyPrefixContext_cons_succ]
  | .drecD D idx :: fs, pc, Γ => by
      simp only [ctorInsPairs, plainCtxT, ctorEmittedDoms_cons_drecD,
        List.length_cons]
      rw [insertChain_append_one, insertChain_ctorInsPairs f ls np fs pc Γ]
      dsimp only
      rw [← ctorEmittedDoms_length, insertAt_ppc_mapIdx,
        policyPrefixContext_cons_succ, ctorPlainDom]

/-- the σ-image of the parameter locals at plain depth `m`: every local's variable
    is at or past the insertion cutoffs' bound, so the chain adds the recursive
    count — the locals land at `m + #recs`. -/
private theorem map_policyParameterLocals_ctorSub (np m : Nat) (fs : List FieldT)
    (hb : ∀ i (hi : i < (ctorInsCutoffs fs).length),
      (ctorInsCutoffs fs)[i] ≤ m + i) :
    (policyParameterLocals np m).map
        (substT (ctorSub (fs.map FieldT.ctorSkip))) =
      policyParameterLocals np (m + (ctorInsCutoffs fs).length) := by
  simp only [policyParameterLocals, List.map_map]
  apply List.map_congr_left
  intro i _
  show substT (ctorSub (fs.map FieldT.ctorSkip)) (.bvar (i + m)) =
    .bvar (i + (m + (ctorInsCutoffs fs).length))
  rw [substT_ctorSub_bvar, liftChain_bvar, insCutoffs_map_ctorSkip,
    foldl_liftChainStep_add _ (i + m) (fun k hk => by
      have := hb k hk; omega)]
  congr 1; omega

/-- the emitted domain at a `.drec` field position `j`: the family application at
    the σ-transported parameter locals and indices — the `RecFieldAtT` shape
    (`doms = []`, `inner = 0`, offset `pc + j`). -/
private theorem ctorEmittedDoms_getElem_drec (f : Nat) (ls : List Level) (np pc : Nat)
    (fs : List FieldT) {j : Nat} {idx : List (Expr Nat)}
    (hj : j < fs.length) (hfj : fs[j] = .drec idx) :
    (ctorEmittedDoms f ls np pc fs)[j]'(by
      rw [ctorEmittedDoms_length]; exact hj) =
      foldApps (.const f ls)
        (policyParameterLocals np (pc + j) ++
          idx.map (substT (ctorSub ((fs.take j).map FieldT.ctorSkip)))) := by
  have hR := plainIdxT_add_ctorInsCutoffs_length (fs.take j)
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hR
  simp only [ctorEmittedDoms, List.getElem_mapIdx, hfj, ctorPlainDom]
  rw [substT_foldApps, List.map_append,
    map_policyParameterLocals_ctorSub np _ (fs.take j) (fun i hi => by
      have := ctorInsCutoffs_le (fs.take j) i hi; omega)]
  show foldApps (substT (ctorSub ((fs.take j).map FieldT.ctorSkip)) (.const f ls))
      (policyParameterLocals np (pc + plainIdxT (fs.take j) 0 +
        (ctorInsCutoffs (fs.take j)).length) ++ _) = _
  simp only [substT]
  rw [show pc + plainIdxT (fs.take j) 0 + (ctorInsCutoffs (fs.take j)).length =
    pc + j from by omega]

/-- the emitted domain at a `.plain` field position `j`: the σ-transported stored
    domain — `ctorPlainDom` is `D` verbatim on `.plain`. -/
private theorem ctorEmittedDoms_getElem_plain (f : Nat) (ls : List Level) (np pc : Nat)
    (fs : List FieldT) {j : Nat} {D : Expr Nat} {u : Level}
    (hj : j < fs.length) (hfj : fs[j] = .plain D u) :
    (ctorEmittedDoms f ls np pc fs)[j]'(by
      rw [ctorEmittedDoms_length]; exact hj) =
      substT (ctorSub ((fs.take j).map FieldT.ctorSkip)) D := by
  simp only [ctorEmittedDoms, List.getElem_mapIdx, hfj, ctorPlainDom]

/-- the emitted domain at a `.drecD` field position `j`: the σ-transported stored
    domain — `ctorPlainDom` is `D` verbatim on `.drecD`, the δ-annotated field's
    surface form (its conversion evidence lives in `DrecDTypedT`). -/
private theorem ctorEmittedDoms_getElem_drecD (f : Nat) (ls : List Level) (np pc : Nat)
    (fs : List FieldT) {j : Nat} {D : Expr Nat} {idx : List (Expr Nat)}
    (hj : j < fs.length) (hfj : fs[j] = .drecD D idx) :
    (ctorEmittedDoms f ls np pc fs)[j]'(by
      rw [ctorEmittedDoms_length]; exact hj) =
      substT (ctorSub ((fs.take j).map FieldT.ctorSkip)) D := by
  simp only [ctorEmittedDoms, List.getElem_mapIdx, hfj, ctorPlainDom]

/-- lifting the whole parameter-locals block by one binder. -/
private theorem policyParameterLocals_lift_zero (np m : Nat) :
    (policyParameterLocals np m).map (lift 0 1) = policyParameterLocals np (m + 1) := by
  simp only [policyParameterLocals, List.map_map]
  apply List.map_congr_left
  intro i _
  show lift 0 1 (Expr.bvar (i + m)) = Expr.bvar (i + (m + 1))
  simp only [lift]
  rw [if_pos (Nat.zero_le _)]
  congr 1

/-- the tree's constructor-domain list `ctorDomsT`, entered after a field prefix `pre`
    (parameter locals at `pc + pre.length`, substitution the prefix's `ctorSub`), is the
    `mapIdx` formula `ctorEmittedDoms` generalises: element `j` is the `ctorSub` of the
    skips before it applied to its plain-form domain.  `pc` counts the binders below
    `pre`, so `ctorPlainDom`'s offset is `pc +` the plain fields in `pre ++ fs.take j`. -/
private theorem ctorDomsT_eq_mapIdx (f : Nat) (ls : List Level) (np pc : Nat) :
    (pre fs : List FieldT) →
    ctorDomsT f ls (policyParameterLocals np (pc + pre.length))
        (ctorSub (pre.map FieldT.ctorSkip)) fs =
      fs.mapIdx (fun j fᵢ =>
        substT (ctorSub ((pre ++ fs.take j).map FieldT.ctorSkip))
          (ctorPlainDom f ls np (pc + plainIdxT (pre ++ fs.take j) 0) fᵢ))
  | _, [] => rfl
  | pre, f₀ :: fs => by
      cases f₀ with
      | plain D u =>
          simp only [ctorDomsT, List.mapIdx_cons]
          congr 1
          · simp only [List.take_zero, List.append_nil, ctorPlainDom]
          · have hσ : (ctorSub (pre.map FieldT.ctorSkip)).up =
                ctorSub ((pre ++ [FieldT.plain D u]).map FieldT.ctorSkip) := by
              rw [List.map_append]
              show _ = ctorSub (pre.map FieldT.ctorSkip ++ [0])
              rw [ctorSub_append_one]
              rfl
            rw [policyParameterLocals_lift_zero, hσ,
              show pc + pre.length + 1 =
                pc + (pre ++ [FieldT.plain D u]).length from by simp; omega]
            rw [ctorDomsT_eq_mapIdx f ls np pc (pre ++ [FieldT.plain D u]) fs]
            apply mapIdx_congr'
            intro j _
            rw [List.take_succ_cons, ← List.append_cons]
      | drec idx =>
          simp only [ctorDomsT, List.mapIdx_cons]
          congr 1
          · simp only [List.take_zero, List.append_nil, ctorPlainDom]
            rw [substT_foldApps, List.map_append,
              map_policyParameterLocals_ctorSub np _ pre (fun i hi => by
                have := ctorInsCutoffs_le pre i hi; omega)]
            simp only [substT]
            rw [show pc + plainIdxT pre 0 + (ctorInsCutoffs pre).length =
              pc + pre.length from
              by have := plainIdxT_add_ctorInsCutoffs_length pre; omega]
          · have hσ : (ctorSub (pre.map FieldT.ctorSkip)).shift1 =
                ctorSub ((pre ++ [FieldT.drec idx]).map FieldT.ctorSkip) := by
              rw [List.map_append]
              show _ = ctorSub (pre.map FieldT.ctorSkip ++ [1])
              rw [ctorSub_append_one]
              rfl
            rw [policyParameterLocals_lift_zero, hσ,
              show pc + pre.length + 1 =
                pc + (pre ++ [FieldT.drec idx]).length from by simp; omega]
            rw [ctorDomsT_eq_mapIdx f ls np pc (pre ++ [FieldT.drec idx]) fs]
            apply mapIdx_congr'
            intro j _
            rw [List.take_succ_cons, ← List.append_cons]
      | drecD D idx =>
          simp only [ctorDomsT, List.mapIdx_cons]
          congr 1
          · simp only [List.take_zero, List.append_nil, ctorPlainDom]
          · have hσ : (ctorSub (pre.map FieldT.ctorSkip)).shift1 =
                ctorSub ((pre ++ [FieldT.drecD D idx]).map FieldT.ctorSkip) := by
              rw [List.map_append]
              show _ = ctorSub (pre.map FieldT.ctorSkip ++ [1])
              rw [ctorSub_append_one]
              rfl
            rw [policyParameterLocals_lift_zero, hσ,
              show pc + pre.length + 1 =
                pc + (pre ++ [FieldT.drecD D idx]).length from by simp; omega]
            rw [ctorDomsT_eq_mapIdx f ls np pc (pre ++ [FieldT.drecD D idx]) fs]
            apply mapIdx_congr'
            intro j _
            rw [List.take_succ_cons, ← List.append_cons]

/-- entered at the identity substitution with `pc` below-binders, `ctorDomsT` is exactly
    the emitted-domain list — `ds` at the cell's `minorTyped_go` call. -/
private theorem ctorDomsT_eq_emitted (f : Nat) (ls : List Level) (np pc : Nat)
    (fs : List FieldT) :
    ctorDomsT f ls (policyParameterLocals np pc) SubstT.id fs =
      ctorEmittedDoms f ls np pc fs := by
  have h := ctorDomsT_eq_mapIdx f ls np pc [] fs
  simp only [List.map_nil, List.length_nil, Nat.add_zero, List.nil_append] at h
  show ctorDomsT f ls (policyParameterLocals np pc)
      (ctorSub ([] : List Nat)) fs = _
  rw [h, ctorEmittedDoms]

/-- a uniform lift of the parameter locals and the substitution commutes with the
    constructor-domain builder: each emitted domain moves up by `d` at its own
    telescope depth `c + i`.  The cell's `ds` — the constructor telescope lifted
    `1 + i` past the motive and earlier minors — is thereby `liftDomsT` of the
    emitted-domain list, which is what `hI1`/`hI3` index into. -/
private theorem ctorDomsT_liftDomsT (f : Nat) (ls : List Level) :
    (fs : List FieldT) → (pl : List (Expr Nat)) → (σ : SubstT) → (c d : Nat) →
    ctorDomsT f ls (pl.map (lift c d)) (fun i => lift c d (σ i)) fs =
      liftDomsT c d (ctorDomsT f ls pl σ fs)
  | [], _, _, _, _ => rfl
  | .plain D _ :: fs, pl, σ, c, d => by
      simp only [ctorDomsT, liftDomsT]
      rw [← lift_substT d D c σ]
      congr 1
      rw [← map_lift_succ_lift_one c d pl, ← SubstT.lift_up c d σ]
      exact ctorDomsT_liftDomsT f ls fs (pl.map (lift 0 1)) σ.up (c + 1) d
  | .drec idx :: fs, pl, σ, c, d => by
      simp only [ctorDomsT, liftDomsT]
      have hhead : foldApps (.const f ls)
          (pl.map (lift c d) ++ idx.map (substT fun i => lift c d (σ i))) =
          lift c d (foldApps (.const f ls) (pl ++ idx.map (substT σ))) := by
        rw [foldApps_lift, List.map_append, List.map_map]
        congr 2
        exact List.map_congr_left (fun x _ => (lift_substT d x c σ).symm)
      rw [hhead]
      congr 1
      rw [← map_lift_succ_lift_one c d pl, ← SubstT.lift_shift1 c d σ]
      exact ctorDomsT_liftDomsT f ls fs (pl.map (lift 0 1)) σ.shift1 (c + 1) d
  | .drecD D _ :: fs, pl, σ, c, d => by
      simp only [ctorDomsT, liftDomsT]
      rw [← lift_substT d D c σ]
      congr 1
      rw [← map_lift_succ_lift_one c d pl, ← SubstT.lift_shift1 c d σ]
      exact ctorDomsT_liftDomsT f ls fs (pl.map (lift 0 1)) σ.shift1 (c + 1) d

/-- `ctorDomsT` entered `d` binders up — at the `pc`-shifted parameter locals and the
    `pc`-shifted identity — is the emitted-domain list lifted domainwise.  At the
    cell `pc = 0`, `d = 1 + i`: `ds = liftDomsT 0 (1+i) (ctorEmittedDoms …)`. -/
private theorem ctorDomsT_eq_emitted_lift (f : Nat) (ls : List Level) (np pc d : Nat)
    (fs : List FieldT) :
    ctorDomsT f ls (policyParameterLocals np (pc + d))
        (fun i => lift pc d (SubstT.id i)) fs =
      liftDomsT pc d (ctorEmittedDoms f ls np pc fs) := by
  rw [show pc + d = d + pc from Nat.add_comm pc d, ← policyParameterLocals_lift np pc d,
    ctorDomsT_liftDomsT, ctorDomsT_eq_emitted]

/-- the cell's minor expression IS the views' stored minor lifted past the `i`
    earlier minors: the `minorFromTelescope_ctorFieldsT` result at `fl = []`,
    `M = .bvar i`, `pl = ppL np (1+i)`, `σ = lift (1+i) ∘ id` is
    `lift 0 i (minorTyT …)`.  The `derivedMinor_eq` tail, factored out for the
    `MinorTypedT`→stored-minor identification. -/
private theorem minorFieldsT_eq_lift_minorTyT (f k : Nat) (ls : List Level) (np i : Nat)
    (fs : List FieldT) (res : List (Expr Nat)) :
    minorFieldsT f k ls (policyParameterLocals np (1 + i)) (.bvar i) []
        (fun j => lift 0 (1 + i) (SubstT.id j)) fs res =
      lift 0 i (minorTyT f ls np (k, fs, res)) := by
  simp only [minorTyT]
  rw [lift_minorFieldsT, map_lift_succ_merge, policyLocals_map_lift, List.map_nil,
    Nat.add_comm i 1]
  have hσ : (fun j => lift 0 i (SubstT.id.shift1 j)) =
      (fun j => lift 0 (1 + i) (SubstT.id j)) := by
    funext j
    show lift 0 i (lift 0 1 (Expr.bvar j)) = lift 0 (1 + i) (Expr.bvar j)
    rw [lift_lift_merge i 1 0 0 (Nat.le_refl 0) (Nat.zero_le _)]
  have hM : lift 0 i (Expr.bvar 0 : Expr Nat) = .bvar i := by
    simp only [lift, Nat.zero_le, if_true, Nat.zero_add]
  rw [hσ, hM]

/-- `take` distributes over the emitted-domain list: the `j`-field prefix the
    recursive-field cell's context needs is itself an emitted list. -/
private theorem ctorEmittedDoms_take (f : Nat) (ls : List Level) (np pc : Nat)
    (fs : List FieldT) (j : Nat) :
    (ctorEmittedDoms f ls np pc fs).take j = ctorEmittedDoms f ls np pc (fs.take j) := by
  apply List.ext_getElem (by simp [ctorEmittedDoms_length])
  intro i h1 h2
  simp only [ctorEmittedDoms_length, List.length_take, List.length_mapIdx] at h2
  have hi : i < j := Nat.lt_of_lt_of_le h2 (Nat.min_le_left _ _)
  simp only [List.getElem_take, ctorEmittedDoms, List.getElem_mapIdx, List.take_take]
  rw [Nat.min_eq_left (Nat.le_of_lt hi)]

/-- `policyPrefixContext ds j` is already the prefix context of `ds.take j`. -/
theorem policyPrefixContext_take' (ds : List (Expr Nat)) (j : Nat) :
    policyPrefixContext ds j = policyPrefixContext (ds.take j) j := by
  simp only [policyPrefixContext, List.take_take, Nat.min_self]

/-- the index typing a `FieldsTyT` derivation locates at a `drec` field position `j`:
    the `hidx` the view carries, read off in the plain context of the fields before it —
    the `plainIdxT`-counted index telescope (the W1 data for the cell's `hI3`). -/
def fieldsTyT_drecAt {E : ResolvedEnv} {n : Nat} {idxTel : Nat → Expr Nat}
    {Γ : LCtx} {k : Nat} {res : List (Expr Nat)} :
    (fs : List FieldT) → FieldsTyT E n idxTel Γ k fs res →
    (j : Nat) → fs.get? j = some (.drec idx) →
    ArgsTyT E n (plainCtxT (fs.take j) Γ) (idxTel (k + plainIdxT (fs.take j) 0)) idx
  | .plain D _ :: fs, .plain _ _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_drecAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT, plainIdxT_cons_plain,
        show k + (plainIdxT (List.take j fs) 0 + 1) =
          k + 1 + plainIdxT (List.take j fs) 0 from by omega]
  | .drec _ :: fs, .drec _ _ _ _ _ hidx _, 0, hj => by
      cases hj
      simpa only [List.take_zero, plainCtxT, plainIdxT, Nat.add_zero] using hidx
  | .drec _ :: fs, .drec _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_drecAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT, plainIdxT]
  | .drecD _ _ :: fs, .drecD _ _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_drecAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT, plainIdxT]
  | .plain _ _ :: _, .plain _ _ _ _ _ _ _ _, 0, hj => by
      simp at hj
  | .drecD _ _ :: _, .drecD _ _ _ _ _ _ _ _, 0, hj => by
      simp at hj
  | [], .nil _ _ _ _, _, hj => by
      simp at hj

/-- the domain typing a `FieldsTyT` derivation locates at a `plain` field position
    `j`: the `hD` the view carries, in the plain context of the fields before it —
    the W1 data for the cell's `hI1` at `.plain`. -/
def fieldsTyT_domainAt {E : ResolvedEnv} {n : Nat} {idxTel : Nat → Expr Nat}
    {Γ : LCtx} {k : Nat} {res : List (Expr Nat)} :
    (fs : List FieldT) → FieldsTyT E n idxTel Γ k fs res →
    (j : Nat) → fs.get? j = some (.plain D u) →
    Nonempty (HasTyT E n (plainCtxT (fs.take j) Γ) D (.sort u))
  | .plain D' _ :: fs, .plain _ _ _ _ _ _ hD tl, j + 1, hj => by
      have tl' := fieldsTyT_domainAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT]
  | .drec _ :: fs, .drec _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_domainAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT]
  | .drecD _ _ :: fs, .drecD _ _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_domainAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT]
  | .plain D' _ :: _, .plain _ _ _ _ _ _ hD _, 0, hj => by
      cases hj
      exact ⟨by simpa only [List.take_zero, plainCtxT] using hD⟩
  | .drec _ :: _, .drec _ _ _ _ _ _ _, 0, hj => by
      simp at hj
  | .drecD _ _ :: _, .drecD _ _ _ _ _ _ _ _, 0, hj => by
      simp at hj
  | [], .nil _ _ _ _, _, hj => by
      simp at hj

/-- the same, at a `drecD` field position (the δ-annotated recursive field carries the
    same `hidx` payload). -/
def fieldsTyT_drecDAt {E : ResolvedEnv} {n : Nat} {idxTel : Nat → Expr Nat}
    {Γ : LCtx} {k : Nat} {res : List (Expr Nat)} :
    (fs : List FieldT) → FieldsTyT E n idxTel Γ k fs res →
    (j : Nat) → fs.get? j = some (.drecD D idx) →
    ArgsTyT E n (plainCtxT (fs.take j) Γ) (idxTel (k + plainIdxT (fs.take j) 0)) idx
  | .plain D' _ :: fs, .plain _ _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_drecDAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT, plainIdxT_cons_plain,
        show k + (plainIdxT (List.take j fs) 0 + 1) =
          k + 1 + plainIdxT (List.take j fs) 0 from by omega]
  | .drec _ :: fs, .drec _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_drecDAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT, plainIdxT]
  | .drecD _ _ :: fs, .drecD _ _ _ _ _ _ hidx _, 0, hj => by
      cases hj
      simpa only [List.take_zero, plainCtxT, plainIdxT, Nat.add_zero] using hidx
  | .drecD _ _ :: fs, .drecD _ _ _ _ _ _ _ tl, j + 1, hj => by
      have tl' := fieldsTyT_drecDAt fs tl j (by simpa using hj)
      rwa [List.take_succ_cons, plainCtxT, plainIdxT]
  | .plain _ _ :: _, .plain _ _ _ _ _ _ _ _, 0, hj => by
      simp at hj
  | .drec _ :: _, .drec _ _ _ _ _ _ _, 0, hj => by
      simp at hj
  | [], .nil _ _ _ _, _, hj => by
      simp at hj

/-- arguments typed along a telescope move with any transport of typings between two contexts. -/
theorem argsTyT_map {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    (F : ∀ {e T : Expr Nat}, Nonempty (HasTyT E n Γ e T) → Nonempty (HasTyT E n Γ' e T)) :
    {T : Expr Nat} → {as : List (Expr Nat)} → ArgsTyT E n Γ T as → Nonempty (ArgsTyT E n Γ' T as)
  | _, _, .nil l => ⟨.nil l⟩
  | _, _, .cons A B a as ha tl => by
      obtain ⟨ha'⟩ := F ⟨ha⟩
      obtain ⟨tl'⟩ := argsTyT_map F tl
      exact ⟨.cons A B a as ha' tl'⟩

/-! ## the function induction hypothesis, locally -/

/-- **a function IH (05 §12).** A recursive field `A` whose reading under its binder is the family-headed
    telescope `Π doms, I (P ++ idx)` with the parameters at their locals, a motive typed at its type,
    and the index arguments typed along the index telescope (W1's data property): the IH
    `Π doms, M idx (f doms)` is typed at the imax of the inner sorts with the motive's universe. A
    direct field is `doms = []`, at `Sort uM`. -/
theorem hasTyT_ih_fun {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) {Δ : LCtx} (A : Expr Nat) {u : Level}
    (hA : Nonempty (HasTyT E n Δ A (.sort u)))
    (f : Nat) (ls : List Level) (np : Nat) (Is : List (Expr Nat)) (uM l : Level) (d : Nat)
    (doms idx : List (Expr Nat)) (inner : Nat) (hdl : doms.length = inner)
    (hshape : lift 0 1 A = policyPi doms (foldApps (.const f ls)
      (policyParameterLocals np (inner + (d + 1)) ++ idx)))
    (hidxlen : idx.length = Is.length)
    (hidx : Nonempty (ArgsTyT E n (policyPrefixContext doms inner ++ (.assumption A :: Δ))
      (idxTelAt Is l (inner + (d + 1))) idx))
    (M : Expr Nat) (hM : Nonempty (HasTyT E n Δ M (motTyAt f ls np Is uM d))) :
    ∃ lv : Fin inner → Level, Nonempty (HasTyT E n (.assumption A :: Δ)
      (policyPi doms (foldApps (lift 0 inner (lift 0 1 M))
        (idx ++ [foldApps (.bvar inner) (policyLocals inner)])))
      (.sort (piSortT inner lv uM))) := by
  subst hdl
  obtain ⟨hA⟩ := hA
  obtain ⟨hM⟩ := hM
  obtain ⟨hidx⟩ := hidx
  let Pd := policyPrefixContext doms doms.length
  -- the motive past the field and its inner binders
  have hMw := hasTyTLiftPrefix (n := n) hcl (Pd ++ [LocalDecl.assumption A]) hM
  have hlenPd : (Pd ++ [LocalDecl.assumption A]).length = doms.length + 1 := by
    simp only [Pd, policyPrefixContext, List.length_append, List.length_map, List.length_reverse,
      List.length_take, Nat.min_self, List.length_singleton]
  have hsw : ∀ e : Expr Nat, lift 0 (doms.length + 1) e = lift 0 doms.length (lift 0 1 e) := fun e => by
    rw [lift_lift_merge doms.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]
  rw [hlenPd, motTyAt_lift, List.append_assoc, List.singleton_append, hsw M] at hMw
  -- the field applied to the inner locals is typed at the family application
  have hlook : lookupType (Pd ++ (.assumption A :: Δ)) doms.length =
      some (lift 0 doms.length (policyPi doms (foldApps (.const f ls)
        (policyParameterLocals np (doms.length + (d + 1)) ++ idx)))) := by
    have h := lookupType_append_assumption Pd A Δ
    have hl : Pd.length = doms.length := by
      simp only [Pd, policyPrefixContext, List.length_map, List.length_reverse, List.length_take, Nat.min_self]
    rw [hl, hsw A, hshape] at h
    exact h
  have hx := hasTyT_foldApps_policyLocals (E := E) (n := n) doms (.assumption A :: Δ) _ (.bvar doms.length)
    (.bvar _ _ _ hlook)
  -- the body, by the local IH
  have hbody := hasTyT_ih_local (lift 0 doms.length (lift 0 1 M)) (liftDomsT 0 (d + (doms.length + 1)) Is)
    f ls (policyParameterLocals np (d + (doms.length + 1))) uM l idx
    (by rw [length_liftDomsT]; exact hidxlen)
    (by rw [length_liftDomsT]; exact hMw)
    (by have : idxTelAt Is l (doms.length + (d + 1)) = policyPi (liftDomsT 0 (d + (doms.length + 1)) Is) (.sort l) := by
          rw [idxTelAt]; congr 2; omega
        rw [← this]; exact hidx)
    _ (by rw [show d + (doms.length + 1) = doms.length + (d + 1) by omega]; exact hx)
  -- the inner binders, read off the field's own typing
  have hAw := hasTyTWeaken (LocalDecl.assumption A) hcl (c := 0) hA
  simp only [insertAt_zero, lift] at hAw
  rw [hshape] at hAw
  obtain ⟨lv, hlv⟩ := hasTyT_policyPi_invT doms hAw
  exact ⟨lv, hasTyT_policyPi_build doms lv hlv ⟨hbody⟩⟩

/-- the conv-aware twin of `hasTyT_ih_fun` for `.drecD`: the recursive-field
    shape is a CONVERSION `lift 0 1 A ≡ policyPi wdoms (famApp)` (the whnf
    path through `DrecDTypedT`) rather than a syntactic equality.  The
    converted endpoint's own typing comes from `endpoints3` (debts
    `SubstLetT`/`ConstsRightDataT`), the local-IH variable's conversion
    travels under the inner binders by `convTLiftPrefix`, and the domain
    inversion is the `Type`-valued `hasTyT_policyPi_invTS`. -/
def hasTyT_ih_drecD {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) (hcl : EnvClosed E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n)
    {Δ : LCtx} (hΔ : CtxWfT E n Δ) (A : Expr Nat) {u : Level}
    (hA : Nonempty (HasTyT E n Δ A (.sort u)))
    (f : Nat) (ls : List Level) (np : Nat) (Is : List (Expr Nat)) (uM l : Level) (d : Nat)
    (wdoms widx : List (Expr Nat)) (inner : Nat) (hdl : wdoms.length = inner) (u' : Level)
    (hbc : Nonempty (ConvT E n (.assumption A :: Δ) (lift 0 1 A)
      (policyPi wdoms (foldApps (.const f ls)
        (policyParameterLocals np (inner + (d + 1)) ++ widx))) (.sort u')))
    (hidxlen : widx.length = Is.length)
    (hidx : Nonempty (ArgsTyT E n (policyPrefixContext wdoms inner ++ (.assumption A :: Δ))
      (idxTelAt Is l (inner + (d + 1))) widx))
    (M : Expr Nat) (hM : Nonempty (HasTyT E n Δ M (motTyAt f ls np Is uM d))) :
    ∃ lv : Fin inner → Level, Nonempty (HasTyT E n (.assumption A :: Δ)
      (policyPi wdoms (foldApps (lift 0 inner (lift 0 1 M))
        (widx ++ [foldApps (.bvar inner) (policyLocals inner)])))
      (.sort (piSortT inner lv uM))) := by
  subst hdl
  obtain ⟨hA⟩ := hA
  obtain ⟨hbc⟩ := hbc
  obtain ⟨hM⟩ := hM
  obtain ⟨hidx⟩ := hidx
  let Pd := policyPrefixContext wdoms wdoms.length
  -- the motive past the field and its inner binders
  have hMw := hasTyTLiftPrefix (n := n) hcl (Pd ++ [LocalDecl.assumption A]) hM
  have hlenPd : (Pd ++ [LocalDecl.assumption A]).length = wdoms.length + 1 := by
    simp only [Pd, policyPrefixContext, List.length_append, List.length_map, List.length_reverse,
      List.length_take, Nat.min_self, List.length_singleton]
  have hsw : ∀ e : Expr Nat, lift 0 (wdoms.length + 1) e = lift 0 wdoms.length (lift 0 1 e) := fun e => by
    rw [lift_lift_merge wdoms.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]
  rw [hlenPd, motTyAt_lift, List.append_assoc, List.singleton_append, hsw M] at hMw
  -- the field's binder lookup is the same literal `lift` shape as the `.drec` path
  have hlook : lookupType (Pd ++ (.assumption A :: Δ)) wdoms.length =
      some (lift 0 wdoms.length (lift 0 1 A)) := by
    have h := lookupType_append_assumption Pd A Δ
    have hl : Pd.length = wdoms.length := by
      simp only [Pd, policyPrefixContext, List.length_map, List.length_reverse, List.length_take, Nat.min_self]
    rw [hl, hsw A] at h
    exact h
  -- the binder's own type, converted to the whnf'd Π — `hbc` lifted under `Pd`
  have hΓA : CtxWfT E n (.assumption A :: Δ) := .assumption _ _ _ hΔ hA
  have hbc' := convTLiftPrefix hcl Pd hbc
  have hlenPd' : Pd.length = wdoms.length := by
    simp only [Pd, policyPrefixContext, List.length_map, List.length_reverse,
      List.length_take, Nat.min_self]
  rw [hlenPd'] at hbc'
  have hx0 := HasTyT.conv _ _ _ _ _ (.bvar _ _ _ hlook) hbc'
  have hx := hasTyT_foldApps_policyLocals wdoms (.assumption A :: Δ) _ (.bvar wdoms.length) hx0
  -- the body, by the local IH
  have hbody := hasTyT_ih_local (lift 0 wdoms.length (lift 0 1 M)) (liftDomsT 0 (d + (wdoms.length + 1)) Is)
    f ls (policyParameterLocals np (d + (wdoms.length + 1))) uM l widx
    (by rw [length_liftDomsT]; exact hidxlen)
    (by rw [length_liftDomsT]; exact hMw)
    (by have : idxTelAt Is l (wdoms.length + (d + 1)) = policyPi (liftDomsT 0 (d + (wdoms.length + 1)) Is) (.sort l) := by
          rw [idxTelAt]; congr 2; omega
        rw [← this]; exact hidx)
    _ (by rw [show d + (wdoms.length + 1) = wdoms.length + (d + 1) by omega]; exact hx)
  -- the inner binders, read off the converted endpoint
  obtain ⟨_, hBty, _⟩ := endpoints3_of_envWfT hW hSL hconst hΓA hbc
  obtain ⟨lvn, hlvn⟩ := hasTyT_policyPi_invTS wdoms hBty
  exact ⟨fun i => lvn i.val, hasTyT_policyPi_build wdoms (fun i => lvn i.val)
    (fun i => ⟨hlvn i.val i.isLt⟩) ⟨hbody⟩⟩

/-! ## the minor builder, typed -/

theorem policyPrefixContext_take (ds : List (Expr Nat)) (j : Nat) :
    policyPrefixContext (ds.take j) j = policyPrefixContext ds j := by
  simp only [policyPrefixContext, List.take_take, Nat.min_self]

theorem liftDomsT_take (c a : Nat) : (ds : List (Expr Nat)) → (j : Nat) →
    (liftDomsT c a ds).take j = liftDomsT c a (ds.take j)
  | [], _ => by simp [liftDomsT]
  | _ :: _, 0 => rfl
  | D :: ds, j + 1 => by
      simp only [liftDomsT, List.take_succ_cons]
      rw [liftDomsT_take (c + 1) a ds j]

/-- what admission's minor builder (`minorFromTelescope`, 05 §12) emits, typed: each field binder, and
    after a recursive field its induction hypothesis at the motive's universe (past the field's inner
    binders, `piSortT`). -/
def MinorTypedT (E : ResolvedEnv) (n : Nat) (uM : Level) : LCtx → List FieldShape → Expr Nat → Prop
  | _, [], _ => True
  | Δ, .nonrecursive :: ss, .pi A R =>
      (∃ u, Nonempty (HasTyT E n Δ A (.sort u))) ∧ MinorTypedT E n uM (.assumption A :: Δ) ss R
  | Δ, .recursive inner :: ss, .pi A (.pi ih R) =>
      (∃ u, Nonempty (HasTyT E n Δ A (.sort u))) ∧
        (∃ lv : Fin inner → Level,
          Nonempty (HasTyT E n (.assumption A :: Δ) ih (.sort (piSortT inner lv uM)))) ∧
        MinorTypedT E n uM (.assumption ih :: .assumption A :: Δ) ss R
  | _, _, _ => False

/-- a recursive field at position `j` of the remaining telescope, `d` binders past the parameters: it
    is literally `Π doms, I (params at their locals ++ idx)`, and its index arguments are typed along the
    index telescope (W1's data property) in its own context. -/
def RecFieldAtT (E : ResolvedEnv) (n : Nat) (f : Nat) (ls : List Level) (np : Nat) (Is : List (Expr Nat))
    (l : Level) (fuel : Nat) (ds : List (Expr Nat)) (Δ : LCtx) (d j inner : Nat) : Prop :=
  ∃ (hj : j < ds.length) (doms idx : List (Expr Nat)), doms.length = inner ∧ idx.length = Is.length ∧
    inner + 2 ≤ fuel ∧
    ds[j] = policyPi doms (foldApps (.const f ls) (policyParameterLocals np (inner + j + d) ++ idx)) ∧
    Nonempty (ArgsTyT E n (policyPrefixContext doms inner ++ (policyPrefixContext ds j ++ Δ))
      (idxTelAt Is l (inner + j + d)) idx)

/-- the conv-aware twin of `RecFieldAtT` for `.drecD`: the recursive field's `ds[j]`
    need not be syntactically `Π doms, I (P ++ idx)` — it CONVERTS to the analyzed
    form (`hbc`), with the analysis's own `piTelescopeFuel` reading (`hpit`) pinned
    to the canonical spine, and the index typing transported onto the analyzed
    arguments (`hW1`).  Both `hbc` and `hW1` sit one binder under `ds[j]` — the
    `lift 0 1` position `funIHType` analyzes — so `hasTyT_ih_drecD` consumes them
    directly at `j = 0`. -/
def RecFieldConvAtT (E : ResolvedEnv) (n : Nat) (f : Nat) (ls : List Level) (np : Nat)
    (Is : List (Expr Nat)) (l : Level) (fuel : Nat) (ds : List (Expr Nat)) (Δ : LCtx)
    (d j inner : Nat) : Prop :=
  ∃ (hj : j < ds.length) (wdoms widx : List (Expr Nat)) (u' : Level),
    wdoms.length = inner ∧ widx.length = Is.length ∧ inner + 2 ≤ fuel ∧
    piTelescopeFuel E fuel (lift 0 1 ds[j]) =
      some (wdoms, foldApps (.const f ls)
        (policyParameterLocals np (inner + j + d + 1) ++ widx)) ∧
    Nonempty (ConvT E n (.assumption ds[j] :: (policyPrefixContext ds j ++ Δ))
      (lift 0 1 ds[j])
      (policyPi wdoms (foldApps (.const f ls)
        (policyParameterLocals np (inner + j + d + 1) ++ widx))) (.sort u')) ∧
    Nonempty (ArgsTyT E n
      (policyPrefixContext wdoms inner ++
        (.assumption ds[j] :: (policyPrefixContext ds j ++ Δ)))
      (idxTelAt Is l (inner + j + d + 1)) widx)

/-- a syntactic `RecFieldAtT` witness is a `RecFieldConvAtT`: the shape equality
    lifts under the field binder into a reflexive conversion, and the index
    typing weakens into the `assumption ds[j]`-extended context. -/
private theorem recFieldAtT_toConv {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {f np : Nat} {ls : List Level} {Is : List (Expr Nat)} {l : Level}
    {fuel : Nat} {ds : List (Expr Nat)} {Δ : LCtx} {d j inner : Nat}
    (hf : transparentBody E f ls = none)
    (h : RecFieldAtT E n f ls np Is l fuel ds Δ d j inner)
    (hI1 : ∀ j (hj : j < ds.length), ∃ u,
      Nonempty (HasTyT E n (policyPrefixContext ds j ++ Δ) ds[j] (.sort u))) :
    RecFieldConvAtT E n f ls np Is l fuel ds Δ d j inner := by
  obtain ⟨hj, doms, idx, hdl, hil, hfuel, hA, hW1⟩ := h
  obtain ⟨u, hAty⟩ := hI1 j hj
  -- the shape lifted one binder deep — the `funIHType` analysis position
  have hshape : lift 0 1 ds[j] = policyPi (liftDomsT 0 1 doms)
      (foldApps (.const f ls)
        (policyParameterLocals np (inner + j + d + 1) ++ idx.map (lift inner 1))) := by
    rw [hA, lift_policyPi, foldApps_lift, List.map_append, hdl, Nat.zero_add,
      policyParameterLocals_lift_le np (inner + j + d) inner 1 (by omega)]
    rfl
  refine ⟨hj, liftDomsT 0 1 doms, idx.map (lift inner 1), u, ?_, ?_, hfuel, ?_, ?_, ?_⟩
  · rw [length_liftDomsT]; exact hdl
  · rw [List.length_map]; exact hil
  · simp only [hshape]
    exact piTelescopeFuel_policyPi_famApp hf _ _
      (by rw [length_liftDomsT, hdl]; exact hfuel)
  · exact hAty.elim (fun hAty => ⟨by
      have hw := hasTyTWeaken (LocalDecl.assumption ds[j]) hcl (c := 0) hAty
      simp only [insertAt_zero, lift] at hw
      rw [hshape]
      exact ConvT.refl _ _ _ (by rw [hshape] at hw; exact hw)⟩)
  · exact hW1.elim (fun hw => ⟨by
      have hw' := argsTyT_weakenUnderTel hcl doms inner (Nat.le_of_eq hdl.symm)
        [LocalDecl.assumption ds[j]] hw
      rw [List.length_singleton, idxTelAt_lift Is l (inner + j + d) inner 1
        (by omega), List.singleton_append] at hw'
      exact hw'⟩)

/-- the `hI3` cell at a `.drec` field position `j`: the recursive field's `ds[j]`-shape
    and transported index typing, assembled into `RecFieldAtT` over the emitted-domain
    list — `doms = []`, `inner = 0`, `d = 0` (the params context is the floor). -/
private theorem recFieldAtT_drec {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {f np : Nat} {ls : List Level} {Is : List (Expr Nat)} {l : Level} {X : Expr Nat}
    {Γ : LCtx} {res : List (Expr Nat)} {fuel j : Nat} {idx : List (Expr Nat)}
    (fs : List FieldT) (hfs : FieldsTyT E n (fun k => lift 0 k X) Γ 0 fs res)
    (hj : j < fs.length) (hfj : fs[j] = .drec idx)
    (hX : X = idxTelAt Is l 0) (hil : idx.length = Is.length) (hfuel : 2 ≤ fuel) :
    RecFieldAtT E n f ls np Is l fuel (ctorEmittedDoms f ls np 0 fs) Γ 0 j 0 := by
  have hlen : j < (ctorEmittedDoms f ls np 0 fs).length := by
    rw [ctorEmittedDoms_length]; exact hj
  refine ⟨hlen, [], idx.map (substT (ctorSub ((fs.take j).map FieldT.ctorSkip))),
    rfl, ?_, hfuel, ?_, ?_⟩
  · rw [List.length_map]; exact hil
  · have h := ctorEmittedDoms_getElem_drec f ls np 0 fs hj hfj
    simp only [policyPi, Nat.zero_add] at h ⊢
    exact h
  · -- the transported index typing
    have hidx := fieldsTyT_drecAt fs hfs j
      (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hj, hfj])
    simp only [Nat.zero_add] at hidx
    have hw := argsTyT_liftChain hcl (ctorInsPairs f ls np (fs.take j) 0)
      (plainCtxT (fs.take j) Γ) (lift 0 (plainIdxT (fs.take j) 0) X) idx hidx
    -- context: insertChain = ppc (emitted take-j) j ++ Γ = ppc ds j ++ Γ
    rw [ctorInsPairs_snds] at hw
    rw [insertChain_ctorInsPairs] at hw
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hw
    rw [← ctorEmittedDoms_take, ← policyPrefixContext_take'] at hw
    -- telescope: liftChain cs (lift 0 piT X) = lift 0 j X = idxTelAt Is l j
    rw [liftChain_lift_zero _ _ (fun i hi => by
      have := ctorInsCutoffs_le (fs.take j) i hi; omega)] at hw
    have hR := plainIdxT_add_ctorInsCutoffs_length (fs.take j)
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hR
    rw [show plainIdxT (fs.take j) 0 + (ctorInsCutoffs (fs.take j)).length = j
      from by omega] at hw
    rw [hX, idxTelAt_lift Is l 0 0 j (Nat.le_refl 0), Nat.zero_add] at hw
    -- idx.map liftChain = idx.map substT pointwise
    have himg : idx.map (liftChain (ctorInsCutoffs (fs.take j))) =
        idx.map (substT (ctorSub ((fs.take j).map FieldT.ctorSkip))) := by
      apply List.map_congr_left
      intro x _
      rw [← insCutoffs_map_ctorSkip, ← substT_ctorSub]
    rw [himg] at hw
    simp only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
      List.nil_append, Nat.zero_add, Nat.add_zero]
    exact ⟨hw⟩

-- generalized .drec cell at boundary-shift d, to splice after recFieldAtT_drec

/-- the `.drec` cell under `shift` boundary binders: inserting `Δd` at the
    parameter boundary lifts the emitted telescope (`liftDomsT`), and the
    index typing survives the `cIP ++ Δd` insertion chain.  `recFieldAtT_drec`
    is the `Δd = []` case. -/
private theorem recFieldAtT_drec_at {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {f np : Nat} {ls : List Level} {Is : List (Expr Nat)} {l : Level} {X : Expr Nat}
    {Γ : LCtx} {res : List (Expr Nat)} {fuel j : Nat} {idx : List (Expr Nat)}
    (fs : List FieldT) (hfs : FieldsTyT E n (fun k => lift 0 k X) Γ 0 fs res)
    (hj : j < fs.length) (hfj : fs[j] = .drec idx)
    (hX : X = idxTelAt Is l 0) (hil : idx.length = Is.length) (hfuel : 2 ≤ fuel)
    (Δd : LCtx) :
    RecFieldAtT E n f ls np Is l fuel
      (liftDomsT 0 Δd.length (ctorEmittedDoms f ls np 0 fs))
      (Δd.reverse ++ Γ) Δd.length j 0 := by
  have hlen : j < (liftDomsT 0 Δd.length (ctorEmittedDoms f ls np 0 fs)).length := by
    rw [length_liftDomsT, ctorEmittedDoms_length]; exact hj
  refine ⟨hlen, [], idx.map (liftChain
      (ctorInsCutoffs (fs.take j) ++ List.replicate Δd.length j)), rfl, ?_, hfuel, ?_, ?_⟩
  · rw [List.length_map]; exact hil
  · -- ds[j] = lift j shift ds₀[j] = the family app at ppL np (j + shift)
    have hget : (liftDomsT 0 Δd.length (ctorEmittedDoms f ls np 0 fs))[j]'hlen =
        lift j Δd.length
        ((ctorEmittedDoms f ls np 0 fs)[j]'(by rw [ctorEmittedDoms_length]; exact hj)) := by
      rw [getElem_liftDomsT Δd.length _ 0 j (by rw [ctorEmittedDoms_length]; exact hj),
        Nat.zero_add]
    rw [hget, ctorEmittedDoms_getElem_drec f ls np 0 fs hj hfj, foldApps_lift,
      List.map_append, Nat.zero_add,
      policyParameterLocals_lift_le np j j Δd.length (Nat.le_refl _)]
    simp only [policyPi, Nat.zero_add]
    congr 1
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    show lift j (List.length Δd) (substT (ctorSub (List.map FieldT.ctorSkip (List.take j fs))) x) = _
    rw [substT_ctorSub, ← liftChain_replicate, ← liftChain_append,
      insCutoffs_map_ctorSkip]
  · -- the transported index typing over cIP ++ Δd
    have hidx := fieldsTyT_drecAt fs hfs j
      (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hj, hfj])
    simp only [Nat.zero_add] at hidx
    have hw := argsTyT_liftChain hcl
      (ctorInsPairs f ls np (fs.take j) 0 ++ Δd.map (fun d => (d, j)))
      (plainCtxT (fs.take j) Γ) (lift 0 (plainIdxT (fs.take j) 0) X) idx hidx
    -- snds = ctorInsCutoffs ++ replicate shift j
    have hsnd : (ctorInsPairs f ls np (fs.take j) 0 ++
        Δd.map (fun d => (d, j))).map Prod.snd =
        ctorInsCutoffs (fs.take j) ++ List.replicate Δd.length j := by
      rw [List.map_append, ctorInsPairs_snds]
      congr 1
      rw [List.map_map]
      exact List.map_const' Δd j
    rw [hsnd] at hw
    -- ctx: insertChain (cIP ++ Δd) base = ppc ds j ++ (Δd.reverse ++ Γ)
    have hctx : insertChain (ctorInsPairs f ls np (fs.take j) 0 ++
        Δd.map (fun d => (d, j))) (plainCtxT (fs.take j) Γ) =
        policyPrefixContext (liftDomsT 0 Δd.length (ctorEmittedDoms f ls np 0 fs)) j ++
          (Δd.reverse ++ Γ) := by
      rw [insertChain_append, insertChain_ctorInsPairs]
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hXlen : (policyPrefixContext
          (ctorEmittedDoms f ls np 0 (fs.take j)) j).length = j := by
        simp only [policyPrefixContext, List.length_map, List.length_reverse,
          List.length_take, List.length_mapIdx, Nat.min_eq_left (Nat.le_of_lt hj),
          List.length_take, ctorEmittedDoms_length, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj)]
        omega
      have hmap : Δd.map (fun d => (d, j)) =
          Δd.map (fun d =>
            (d, (policyPrefixContext (ctorEmittedDoms f ls np 0 (fs.take j)) j).length)) := by
        rw [hXlen]
      have hfull : policyPrefixContext (ctorEmittedDoms f ls np 0 (fs.take j)) j =
          policyPrefixContext (ctorEmittedDoms f ls np 0 (fs.take j))
            (ctorEmittedDoms f ls np 0 (fs.take j)).length := by
        rw [ctorEmittedDoms_length, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj)]
      rw [hmap, insertChain_boundary, hfull, liftDeclChainIter_ppc]
      rw [show (ctorEmittedDoms f ls np 0 (fs.take j)).length = j from by
        rw [ctorEmittedDoms_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]]
      rw [← ctorEmittedDoms_take]
      have hmi : ((ctorEmittedDoms f ls np 0 fs).take j).mapIdx
          (fun i D => lift i Δd.length D) =
          liftDomsT 0 Δd.length ((ctorEmittedDoms f ls np 0 fs).take j) := by
        rw [liftDomsT_eq_mapIdx]
        apply mapIdx_congr'
        intro i _
        rw [Nat.zero_add]
      rw [hmi, ← liftDomsT_take, ← policyPrefixContext_take', List.append_assoc]
    rw [hctx] at hw
    -- telescope: liftChain (cs ++ rep) (lift 0 piT X) = lift 0 (j + shift) X
    rw [liftChain_append, liftChain_lift_zero _ _ (fun i hi => by
      have := ctorInsCutoffs_le (fs.take j) i hi; omega)] at hw
    rw [liftChain_replicate] at hw
    have hR := plainIdxT_add_ctorInsCutoffs_length (fs.take j)
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hR
    rw [hR, lift_lift_merge Δd.length j 0 j (Nat.zero_le _) (by omega)] at hw
    rw [hX, idxTelAt_lift Is l 0 0 (j + Δd.length) (Nat.zero_le _), Nat.zero_add] at hw
    -- ppc [] 0 = []
    simp only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
      List.nil_append, Nat.zero_add] at hw ⊢
    exact ⟨hw⟩

/-- the binders `MinorTypedT` pushes onto `Δ` while walking `ss` — one per
    `.nonrecursive`, two (field + ih) per `.recursive`.  The leaf's context. -/
def minorBinders : List FieldShape → Expr Nat → LCtx
  | .nonrecursive :: ss, .pi A R => minorBinders ss R ++ [.assumption A]
  | .recursive _ :: ss, .pi A (.pi ih R) =>
      minorBinders ss R ++ [.assumption ih, .assumption A]
  | _, _ => []

/-- the leaf expression `MinorTypedT` ends at — `R` with its `ss`-many `.pi`
    shells peeled (two per `.recursive`). -/
def minorLeaf : List FieldShape → Expr Nat → Expr Nat
  | .nonrecursive :: ss, .pi _ R => minorLeaf ss R
  | .recursive _ :: ss, .pi _ (.pi _ R) => minorLeaf ss R
  | _, R => R

/-- the Π-peels `minorBinders`/`minorLeaf` walk: one binder per nonrecursive
    field, two (the field's domain and its induction hypothesis) per recursive. -/
def shapeBinders : List FieldShape → Nat
  | [] => 0
  | .nonrecursive :: ss => shapeBinders ss + 1
  | .recursive _ :: ss => shapeBinders ss + 2

/-- a `minorFromTelescope` output carries exactly the binders its shape list
    reads: the tail is a `.app`, each `.nonrecursive` wraps one `.pi`, each
    `.recursive` wraps two (the domain and `funIHType`'s induction hypothesis). -/
theorem piDomsOf_minorFromTelescope (E : ResolvedEnv) (fuel np : Nat) :
    (M acc : Expr Nat) → (ss : List FieldShape) → (T R : Expr Nat) →
    minorFromTelescope E fuel np M acc ss T = some R →
    (piDomsOf R).length = shapeBinders ss
  | _, _, [], _, _, h => by
      simp only [minorFromTelescope] at h
      injection h with h
      subst h
      rfl
  | M, acc, .nonrecursive :: ss, T, _, h => by
      cases T <;> simp only [minorFromTelescope] at h
      case pi A B =>
          cases hr : minorFromTelescope E fuel np (lift 0 1 M)
              (.app (lift 0 1 acc) (.bvar 0)) ss B with
          | none => rw [hr] at h; exact Option.noConfusion h
          | some R' =>
              rw [hr] at h
              injection h with h
              subst h
              simp only [piDomsOf, List.length_cons, shapeBinders]
              rw [piDomsOf_minorFromTelescope E fuel np _ _ ss _ _ hr]
      all_goals exact Option.noConfusion h
  | M, acc, .recursive inner :: ss, T, _, h => by
      cases T <;> simp only [minorFromTelescope] at h
      case pi A B =>
          cases hih : funIHType E fuel np A M inner with
          | none => rw [hih] at h; exact Option.noConfusion h
          | some ih =>
              rw [hih] at h
              cases hr : minorFromTelescope E fuel np (lift 0 2 M)
                  (.app (lift 0 2 acc) (.bvar 1)) ss (lift 0 1 B) with
              | none => rw [hr] at h; exact Option.noConfusion h
              | some R' =>
                  rw [hr] at h
                  injection h with h
                  subst h
                  simp only [piDomsOf, List.length_cons, shapeBinders]
                  rw [piDomsOf_minorFromTelescope E fuel np _ _ ss _ _ hr]
      all_goals exact Option.noConfusion h

/-- the context `minorBinders` produces is the prefix context of the target's
    domain list at the walk's count — the `hb` side of `minorTypedT_hasTyT`
    consumes `IA020`'s `ppc (piDomsOf M)` context through this identification. -/
theorem minorBinders_eq_ppc : (ss : List FieldShape) → (R : Expr Nat) →
    shapeBinders ss ≤ (piDomsOf R).length →
    minorBinders ss R = policyPrefixContext (piDomsOf R) (shapeBinders ss)
  | [], _, _ => rfl
  | .nonrecursive :: ss, R, h => by
      cases R <;> simp only [piDomsOf, List.length_cons, List.length_nil] at h
      case pi A B =>
          simp only [minorBinders]
          have h' : shapeBinders ss ≤ (piDomsOf B).length := by
            simp only [shapeBinders] at h; omega
          rw [minorBinders_eq_ppc ss B h']
          have hppc := policyPrefixContext_cons_succ A (piDomsOf B)
            (shapeBinders ss) []
          rw [List.append_nil] at hppc
          simp only [piDomsOf, shapeBinders]
          exact hppc.symm
      all_goals simp only [shapeBinders] at h; omega
  | .recursive _ :: ss, R, h => by
      cases R <;> simp only [piDomsOf, List.length_cons, List.length_nil] at h
      case pi A R' =>
          cases R' <;> simp only [piDomsOf, List.length_cons, List.length_nil] at h
          case pi ih R'' =>
              simp only [minorBinders]
              have h' : shapeBinders ss ≤ (piDomsOf R'').length := by
                simp only [shapeBinders] at h; omega
              rw [minorBinders_eq_ppc ss R'' h']
              have hppc1 := policyPrefixContext_cons_succ A (ih :: piDomsOf R'')
                (shapeBinders ss + 1) []
              have hppc2 := policyPrefixContext_cons_succ ih (piDomsOf R'')
                (shapeBinders ss) []
              rw [List.append_nil] at hppc1 hppc2
              rw [hppc2] at hppc1
              simp only [piDomsOf, shapeBinders]
              rw [List.append_assoc] at hppc1
              exact hppc1.symm
          all_goals simp only [shapeBinders] at h; omega
      all_goals simp only [shapeBinders] at h; omega

/-- at full depth the walk's leaf is the target's non-Π tail. -/
theorem minorLeaf_eq_piTailOf : (ss : List FieldShape) → (R : Expr Nat) →
    shapeBinders ss = (piDomsOf R).length →
    minorLeaf ss R = piTailOf R
  | [], R, h => by
      cases R <;> simp only [piDomsOf, List.length_cons, List.length_nil, shapeBinders] at h
      case pi A B => omega
      all_goals rfl
  | .nonrecursive :: ss, R, h => by
      cases R <;> simp only [piDomsOf, List.length_cons, List.length_nil] at h
      case pi A B =>
          simp only [minorLeaf, piTailOf]
          exact minorLeaf_eq_piTailOf ss B (by simp only [shapeBinders] at h; omega)
      all_goals simp only [shapeBinders] at h; omega
  | .recursive _ :: ss, R, h => by
      cases R <;> simp only [piDomsOf, List.length_cons, List.length_nil] at h
      case pi A R' =>
          cases R' <;> simp only [piDomsOf, List.length_cons, List.length_nil] at h
          case pi ih R'' =>
              simp only [minorLeaf, piTailOf]
              exact minorLeaf_eq_piTailOf ss R'' (by simp only [shapeBinders] at h; omega)
          all_goals simp only [shapeBinders] at h; omega
      all_goals simp only [shapeBinders] at h; omega

/-- the binders a field list contributes to a minor's context: one domain per
    field, plus one induction hypothesis per recursive field. -/
def minorBinderCount : List FieldT → Nat
  | [] => 0
  | .plain _ _ :: fs => 1 + minorBinderCount fs
  | .drec _ :: fs => 2 + minorBinderCount fs
  | .drecD _ _ :: fs => 2 + minorBinderCount fs

/-- the substitution `minorFieldsT` threads to its conclusion: `σ.up` under each
    plain domain, `σ.shift1.shift1` under each recursive field's domain and IH. -/
def minorEndSubst (σ : SubstT) : List FieldT → SubstT
  | [] => σ
  | .plain _ _ :: fs => minorEndSubst σ.up fs
  | .drec _ :: fs => minorEndSubst σ.shift1.shift1 fs
  | .drecD _ _ :: fs => minorEndSubst σ.shift1.shift1 fs

/-- the field-local spine `minorFieldsT` accumulates: each field's variable at
    its distance to the conclusion — past the tail's binders, and past its own
    induction hypothesis for a recursive field. -/
def minorFieldLocals : List FieldT → List (Expr Nat)
  | [] => []
  | .plain _ _ :: fs => .bvar (minorBinderCount fs) :: minorFieldLocals fs
  | .drec _ :: fs => .bvar (1 + minorBinderCount fs) :: minorFieldLocals fs
  | .drecD _ _ :: fs => .bvar (1 + minorBinderCount fs) :: minorFieldLocals fs

/-- the binders `minorBinders` reads off `minorFieldsT`'s output, as a context:
    the domain (and for a recursive field the induction hypothesis `mot idx x`)
    with the parameters, motive and σ threaded exactly as the builder does. -/
def minorBinderList (f : Nat) (ls : List Level) :
    List (Expr Nat) → Expr Nat → List FieldT → SubstT → LCtx
  | _, _, [], _ => []
  | pl, mot, .plain D _ :: fs, σ =>
      minorBinderList f ls (pl.map (lift 0 1)) (lift 0 1 mot) fs σ.up ++
        [.assumption (substT σ D)]
  | pl, mot, .drec idx :: fs, σ =>
      minorBinderList f ls (pl.map (lift 0 2)) (lift 0 2 mot) fs σ.shift1.shift1 ++
        [.assumption (foldApps (lift 0 1 mot)
          ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0])),
         .assumption (foldApps (.const f ls) (pl ++ idx.map (substT σ)))]
  | pl, mot, .drecD D idx :: fs, σ =>
      minorBinderList f ls (pl.map (lift 0 2)) (lift 0 2 mot) fs σ.shift1.shift1 ++
        [.assumption (foldApps (lift 0 1 mot)
          ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0])),
         .assumption (substT σ D)]

theorem minorBinderList_length (f : Nat) (ls : List Level) :
    (fs : List FieldT) → (pl : List (Expr Nat)) → (mot : Expr Nat) → (σ : SubstT) →
    (minorBinderList f ls pl mot fs σ).length = minorBinderCount fs
  | [], _, _, _ => rfl
  | .plain _ _ :: fs, pl, mot, σ => by
      simp only [minorBinderList, List.length_append, List.length_cons,
        List.length_nil, minorBinderCount]
      rw [minorBinderList_length f ls fs]; omega
  | .drec _ :: fs, pl, mot, σ => by
      simp only [minorBinderList, List.length_append, List.length_cons,
        List.length_nil, minorBinderCount]
      rw [minorBinderList_length f ls fs]; omega
  | .drecD _ _ :: fs, pl, mot, σ => by
      simp only [minorBinderList, List.length_append, List.length_cons,
        List.length_nil, minorBinderCount]
      rw [minorBinderList_length f ls fs]; omega

theorem map_lift_zero : (xs : List (Expr Nat)) → xs.map (lift 0 0) = xs
  | [] => rfl
  | x :: xs => by rw [List.map_cons, lift_zero, map_lift_zero xs]

theorem map_lift_bvar (a i : Nat) :
    ([.bvar i] : List (Expr Nat)).map (lift 0 a) = [.bvar (i + a)] := by
  simp [lift]

theorem map_lift_merge (a b : Nat) (xs : List (Expr Nat)) :
    (xs.map (lift 0 a)).map (lift 0 b) = xs.map (lift 0 (a + b)) := by
  rw [List.map_map]
  exact List.map_congr_left
    (fun x _ => lift_lift_merge b a 0 0 (Nat.le_refl 0) (Nat.zero_le _) x)

/-- `minorBinders` on `minorFieldsT`'s output is exactly the threaded binder
    list — the minor's field-plus-IH context, named. -/
theorem minorBinders_minorFieldsT (f c : Nat) (ls : List Level) (res : List (Expr Nat)) :
    (fs : List FieldT) → (pl fl : List (Expr Nat)) → (mot : Expr Nat) → (σ : SubstT) →
    minorBinders (fs.map FieldT.shapeT) (minorFieldsT f c ls pl mot fl σ fs res) =
      minorBinderList f ls pl mot fs σ
  | [], _, _, _, _ => rfl
  | .plain _ _ :: fs, pl, fl, mot, σ => by
      simp only [List.map_cons, FieldT.shapeT, minorFieldsT, minorBinders,
        minorBinderList]
      rw [minorBinders_minorFieldsT f c ls res fs]
  | .drec _ :: fs, pl, fl, mot, σ => by
      simp only [List.map_cons, FieldT.shapeT, minorFieldsT, minorBinders,
        minorBinderList]
      rw [minorBinders_minorFieldsT f c ls res fs]
  | .drecD _ _ :: fs, pl, fl, mot, σ => by
      simp only [List.map_cons, FieldT.shapeT, minorFieldsT, minorBinders,
        minorBinderList]
      rw [minorBinders_minorFieldsT f c ls res fs]

/-- `minorLeaf` on `minorFieldsT`'s output: the motive lifted past all binders
    applied to the σ-threaded result indices and the constructor applied to the
    parameters and the field-local spine. -/
theorem minorLeaf_minorFieldsT (f c : Nat) (ls : List Level) (res : List (Expr Nat)) :
    (fs : List FieldT) → (pl fl : List (Expr Nat)) → (mot : Expr Nat) → (σ : SubstT) →
    minorLeaf (fs.map FieldT.shapeT) (minorFieldsT f c ls pl mot fl σ fs res) =
      foldApps (lift 0 (minorBinderCount fs) mot)
        (res.map (substT (minorEndSubst σ fs)) ++
          [foldApps (.const c ls)
            (pl.map (lift 0 (minorBinderCount fs)) ++
              (fl.map (lift 0 (minorBinderCount fs)) ++ minorFieldLocals fs))])
  | [], pl, fl, mot, σ => by
      simp only [List.map_nil, minorFieldsT, minorLeaf, minorBinderCount,
        minorEndSubst, minorFieldLocals, lift_zero, List.append_nil]
      rw [map_lift_zero pl, map_lift_zero fl]
  | .plain _ _ :: fs, pl, fl, mot, σ => by
      simp only [List.map_cons, FieldT.shapeT, minorFieldsT, minorLeaf,
        minorBinderCount, minorEndSubst, minorFieldLocals]
      rw [minorLeaf_minorFieldsT f c ls res fs,
        lift_lift_merge _ _ _ _ (Nat.le_refl 0) (Nat.zero_le _),
        map_lift_merge, List.map_append, map_lift_merge, map_lift_bvar,
        Nat.zero_add, List.append_assoc]
      rfl
  | .drec _ :: fs, pl, fl, mot, σ => by
      simp only [List.map_cons, FieldT.shapeT, minorFieldsT, minorLeaf,
        minorBinderCount, minorEndSubst, minorFieldLocals]
      rw [minorLeaf_minorFieldsT f c ls res fs,
        lift_lift_merge _ _ _ _ (Nat.le_refl 0) (Nat.zero_le _),
        map_lift_merge, List.map_append, map_lift_merge, map_lift_bvar,
        List.append_assoc]
      rfl
  | .drecD _ _ :: fs, pl, fl, mot, σ => by
      simp only [List.map_cons, FieldT.shapeT, minorFieldsT, minorLeaf,
        minorBinderCount, minorEndSubst, minorFieldLocals]
      rw [minorLeaf_minorFieldsT f c ls res fs,
        lift_lift_merge _ _ _ _ (Nat.le_refl 0) (Nat.zero_le _),
        map_lift_merge, List.map_append, map_lift_merge, map_lift_bvar,
        List.append_assoc]
      rfl

/-- `MinorTypedT` folded into a judgment: the domains' sort typings give the
    `.pi` chain; the leaf (the motive applied to the result indices and the
    constructor application) is the caller's `hbody`. -/
theorem minorTypedT_hasTyT {E : ResolvedEnv} {n : Nat} {uM : Level}
    {Δ : LCtx} {ss : List FieldShape} {R : Expr Nat}
    (h : MinorTypedT E n uM Δ ss R)
    (hb : ∀ {Γ' : LCtx} {T : Expr Nat},
      Γ' = minorBinders ss R ++ Δ → T = minorLeaf ss R →
      ∃ u, Nonempty (HasTyT E n Γ' T (.sort u))) :
    ∃ u, Nonempty (HasTyT E n Δ R (.sort u)) := by
  induction ss generalizing Δ R with
  | nil => exact hb rfl rfl
  | cons s ss ih =>
      cases s with
      | nonrecursive =>
          cases R <;> simp only [MinorTypedT] at h
          obtain ⟨⟨u, hA⟩, hrest⟩ := h
          obtain ⟨v, hR⟩ := ih hrest
            (fun {Γ' T} hΓ hT => hb (hΓ.trans (by
              simp only [minorBinders, List.append_assoc, List.cons_append,
                List.nil_append])) hT)
          obtain ⟨hA'⟩ := hA
          obtain ⟨hR'⟩ := hR
          exact ⟨.imax u v, ⟨.pi _ _ _ _ _ hA' hR'⟩⟩
      | recursive inner =>
          cases R with
          | pi A R' =>
              cases R' <;> simp only [MinorTypedT] at h
              obtain ⟨⟨u, hA⟩, ⟨lv, hih⟩, hrest⟩ := h
              obtain ⟨v, hR⟩ := ih hrest
                (fun {Γ' T} hΓ hT => hb (hΓ.trans (by
                  simp only [minorBinders, List.append_assoc, List.cons_append,
                    List.nil_append])) hT)
              obtain ⟨hA'⟩ := hA
              obtain ⟨hih'⟩ := hih
              obtain ⟨hR'⟩ := hR
              exact ⟨.imax u (.imax (piSortT inner lv uM) v),
                ⟨.pi _ _ _ _ _ hA' (.pi _ _ _ _ _ hih' hR')⟩⟩
          | bvar v => simp only [MinorTypedT] at h
          | sort l' => simp only [MinorTypedT] at h
          | const r' ls' => simp only [MinorTypedT] at h
          | app f' x' => simp only [MinorTypedT] at h
          | lam a' b' => simp only [MinorTypedT] at h
          | letE a' v' b' => simp only [MinorTypedT] at h
          | lit m => simp only [MinorTypedT] at h

/-- **the R-NoDeltaRec remainder, named on the typed root.** No `.drecD` field occurs in
    `fs`.  Under it every `ss[j]? = .recursive inner` is a `.drec` position with
    `inner = 0`, so the `hI3` discharger closes without the surface-domain conversion —
    the `.drecD` conv-aware witness plus a parallel `minorTyped_go_conv` is the separate
    payment (the (b) step of the ruling).  Today's views discharge it vacuously via
    `drecDTypedT_of_absent`. -/
def NoDrecDT (fs : List FieldT) : Prop :=
  ∀ i (hi : i < fs.length) (D : Expr Nat) (idx : List (Expr Nat)),
    fs[i] ≠ .drecD D idx

/-- the named remainder implies the decidable absence `minorFromTelescope_ctorFieldsT`
    and `derivedMinor_eq` take: no field is `.drecD`. -/
theorem noDrecDT_isDrecD {fs : List FieldT} (h : NoDrecDT fs) :
    ∀ d ∈ fs, d.isDrecD = false := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.get_of_mem hd
  cases hdi : fs.get i with
  | plain _ _ => rfl
  | drec _ => rfl
  | drecD D idx => exact absurd hdi (h i.val i.isLt D idx)

/-- an `ArgsTyT` over a closed telescope ending in a sort consumes exactly the domains. -/
def argsTyT_policyPi_sort_length {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} :
    (doms args : List (Expr Nat)) → (T : Expr Nat) → T = policyPi doms (.sort l) →
    ArgsTyT E n Γ T args → args.length = doms.length
  | [], args, _, hT, h =>
      match h, hT with
      | .nil _, _ => rfl
      | .cons A B _ _ _ _, hT' => by
          have hT'' : Expr.pi A B = Expr.sort l := hT'
          exact Expr.noConfusion hT''
  | D :: doms, [], _, hT, h =>
      match h, hT with
      | .nil l'', hT' => by
          have hT'' : Expr.sort l'' = Expr.pi D (policyPi doms (.sort l)) := hT'
          exact Expr.noConfusion hT''
  | D :: doms, a :: as, _, hT, h =>
      match h, hT with
      | .cons A B _ _ _ tl, hT' => by
          have hT'' : Expr.pi A B = Expr.pi D (policyPi doms (.sort l)) := hT'
          injection hT'' with hA hB
          subst hA hB
          show as.length + 1 = doms.length + 1
          congr 1
          rw [instantiate0, instantiate_policyPi] at tl
          have := argsTyT_policyPi_sort_length (instDomsT 0 a doms) as _ rfl tl
          rw [length_instDomsT] at this
          exact this

/-- the `hI3` discharger under `NoDrecDT`: a `.recursive` shape cell is a `.drec` field
    (`inner = 0`), and `recFieldAtT_drec` assembles its `RecFieldAtT` from the
    `FieldsTyT` index typing. -/
private theorem hI3_drec_at {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {f np : Nat} {ls : List Level} {Is : List (Expr Nat)} {l : Level} {X : Expr Nat}
    {Γ : LCtx} {res : List (Expr Nat)} {fuel : Nat}
    (fs : List FieldT) (hfs : FieldsTyT E n (fun k => lift 0 k X) Γ 0 fs res)
    (hX : X = idxTelAt Is l 0) (hnd : NoDrecDT fs) (hfuel : 2 ≤ fuel) (Δd : LCtx) :
    ∀ j inner, (fs.map FieldT.shapeT)[j]? = some (.recursive inner) →
      RecFieldAtT E n f ls np Is l fuel
        (liftDomsT 0 Δd.length (ctorEmittedDoms f ls np 0 fs))
        (Δd.reverse ++ Γ) Δd.length j inner := by
  intro j inner hj
  rw [List.getElem?_map] at hj
  cases hfj : fs[j]? with
  | none => rw [hfj] at hj; exact Option.noConfusion hj
  | some fj =>
      rw [hfj] at hj
      obtain ⟨hjlt, hfj'⟩ := List.getElem?_eq_some_iff.mp hfj
      cases fj with
      | plain D u =>
          simp only [FieldT.shapeT, Option.map, Option.some.injEq] at hj
          exact FieldShape.noConfusion hj
      | drec idx =>
          simp only [FieldT.shapeT, Option.map, Option.some.injEq] at hj
          obtain ⟨rfl⟩ := hj
          have hidx := fieldsTyT_drecAt fs hfs j
            (by rw [List.get?_eq_getElem?]; exact hfj)
          have hil : idx.length = Is.length := by
            simp only [Nat.zero_add] at hidx
            rw [hX, idxTelAt_lift Is l 0 0 (plainIdxT (fs.take j) 0) (Nat.le_refl 0),
              Nat.zero_add] at hidx
            have := argsTyT_policyPi_sort_length _ _ _ rfl hidx
            rw [length_liftDomsT] at this
            exact this
          exact recFieldAtT_drec_at hcl fs hfs hjlt hfj' hX hil hfuel Δd
      | drecD D idx =>
          exact absurd hfj' (hnd j hjlt D idx)

/-- the `hI1` discharger: every domain of the constructor's field telescope is typed at
    its prefix context, read straight off the constructor's `hT` by `policyPi` inversion —
    no context transport needed, `ds` IS `ctorDomsT`. -/
private theorem hI1_ctorFieldsT {E : ResolvedEnv} {n : Nat}
    {f : Nat} {ls : List Level} {pl : List (Expr Nat)} {σ : SubstT}
    {Γ : LCtx} {res : List (Expr Nat)} {u : Level}
    (fs : List FieldT)
    (hT : HasTyT E n Γ (ctorFieldsT f ls pl σ fs res) (.sort u)) :
    ∀ j (hj : j < (ctorDomsT f ls pl σ fs).length),
      ∃ v, Nonempty (HasTyT E n (policyPrefixContext (ctorDomsT f ls pl σ fs) j ++ Γ)
        (ctorDomsT f ls pl σ fs)[j] (.sort v)) := by
  rw [ctorFieldsT_policyPi] at hT
  obtain ⟨lv, hlv⟩ := hasTyT_policyPi_invT _ hT
  exact fun j hj => ⟨lv ⟨j, hj⟩, hlv ⟨j, hj⟩⟩

/-- the `hI1` transport under `shift` boundary binders, generic over the domain
    list: a pointwise source `ds₀[j]` sort-typed at `ppc ds₀ j ++ Γ` lifts to
    `liftDomsT 0 |Δd| ds₀` at the prefix past `Δd.reverse` — `hasTyT_liftChain`
    over the boundary pairs. -/
private theorem hI1_at_of_pointwise {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {ds₀ : List (Expr Nat)} {Γ : LCtx} (Δd : LCtx)
    (h : ∀ j (hj : j < ds₀.length), ∃ v,
      Nonempty (HasTyT E n (policyPrefixContext ds₀ j ++ Γ) ds₀[j] (.sort v))) :
    ∀ j (hj : j < (liftDomsT 0 Δd.length ds₀).length),
      ∃ v, Nonempty (HasTyT E n
        (policyPrefixContext (liftDomsT 0 Δd.length ds₀) j ++ (Δd.reverse ++ Γ))
        (liftDomsT 0 Δd.length ds₀)[j] (.sort v)) := by
  intro j hj
  have hj0 : j < ds₀.length := by
    rw [length_liftDomsT] at hj; exact hj
  obtain ⟨v, hv⟩ := h j hj0
  obtain ⟨hv⟩ := hv
  have hw := hasTyT_liftChain hcl (Δd.map (fun d => (d, j)))
    (policyPrefixContext ds₀ j ++ Γ) ds₀[j] (.sort v) hv
  -- snds = replicate shift j
  have hsnd : (Δd.map (fun d => (d, j))).map Prod.snd =
      List.replicate Δd.length j := by
    rw [List.map_map]
    exact List.map_const' Δd j
  rw [hsnd, liftChain_replicate, liftChain_replicate] at hw
  -- ctx: insertChain Δdpairs (ppc ds₀ j ++ Γ) = ppc ds j ++ (Δd.reverse ++ Γ)
  have hctx : insertChain (Δd.map (fun d => (d, j)))
      (policyPrefixContext ds₀ j ++ Γ) =
      policyPrefixContext (liftDomsT 0 Δd.length ds₀) j ++
        (Δd.reverse ++ Γ) := by
    have hXlen : (policyPrefixContext ds₀ j).length = j := by
      simp only [policyPrefixContext, List.length_map, List.length_reverse,
        List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0)]
    have hmap : Δd.map (fun d => (d, j)) =
        Δd.map (fun d => (d, (policyPrefixContext ds₀ j).length)) := by
      rw [hXlen]
    rw [hmap, insertChain_boundary]
    -- boundary X is a FULL prefix ctx: ppc ds₀ j = ppc (ds₀.take j) (take j).length
    have hfull : policyPrefixContext ds₀ j =
        policyPrefixContext (ds₀.take j) (ds₀.take j).length := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0),
        ← policyPrefixContext_take']
    rw [hfull, liftDeclChainIter_ppc]
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj0)]
    have hmi : (ds₀.take j).mapIdx (fun i D => lift i Δd.length D) =
        liftDomsT 0 Δd.length (ds₀.take j) := by
      rw [liftDomsT_eq_mapIdx]
      apply mapIdx_congr'
      intro i _
      rw [Nat.zero_add]
    rw [hmi, ← liftDomsT_take, ← policyPrefixContext_take', List.append_assoc]
  rw [hctx] at hw
  have hget : (liftDomsT 0 Δd.length ds₀)[j]'(by
      rw [length_liftDomsT]; exact hj0) =
      lift (0 + j) Δd.length ds₀[j] := by
    rw [getElem_liftDomsT Δd.length ds₀ 0 j hj0]
  rw [Nat.zero_add] at hget
  exact ⟨v, by rw [hget]; exact ⟨hw⟩⟩

/-- `hI1` under `shift` boundary binders: each lifted domain `ds[j] = lift j shift ds₀[j]`
    is typed at the lifted prefix past `Δd` — `hasTyT_liftChain` over the boundary pairs. -/
private theorem hI1_ctorFieldsT_at {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {f : Nat} {ls : List Level} {pl : List (Expr Nat)} {σ : SubstT}
    {Γ : LCtx} {res : List (Expr Nat)} {u : Level}
    (fs : List FieldT)
    (hT : HasTyT E n Γ (ctorFieldsT f ls pl σ fs res) (.sort u))
    (Δd : LCtx) :
    ∀ j (hj : j < (liftDomsT 0 Δd.length (ctorDomsT f ls pl σ fs)).length),
      ∃ v, Nonempty (HasTyT E n
        (policyPrefixContext (liftDomsT 0 Δd.length (ctorDomsT f ls pl σ fs)) j ++
          (Δd.reverse ++ Γ))
        (liftDomsT 0 Δd.length (ctorDomsT f ls pl σ fs))[j] (.sort v)) :=
  hI1_at_of_pointwise hcl Δd (hI1_ctorFieldsT fs hT)

/-- `hI1` for `minorTyped_go`, sourced from `FieldsTyT` at the family-parameter
    context `telCtxT fv.params` (the context `hI3` lands in): each emitted domain
    `ds₀[j]` is a sort there. `.plain` lifts the stored domain typing
    (`fieldsTyT_domainAt`) through the `ctorInsPairs` insertion; `.drec` types the
    family application (`famApp_typed_drec`, at the canonical level vector — the
    `ls` the recursor emission uses, `policyFamilyLevels`) the same way.
    `.drecD` is ruled out by the named `NoDrecDT` remainder. -/
private theorem hI1_fieldsT {E : ResolvedEnv} {n : Nat} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} (hcl : EnvClosed E) (hres : E.members f = some fm)
    {np : Nat} {res : List (Expr Nat)} {X : Expr Nat}
    (fs : List FieldT)
    (hfs : FieldsTyT E fm.arity (fun k => lift 0 k X)
      (telCtxT fv.params) 0 fs res)
    (hX : X = policyPi (fv.indices.map Prod.fst) (.sort fv.sort))
    (hnp : fv.params.length = np) (hnd : NoDrecDT fs)
    (hn : fm.arity ≤ n) :
    ∀ j (hj : j < (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs).length),
      ∃ u, Nonempty (HasTyT E n
        (policyPrefixContext (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs) j ++
          telCtxT fv.params)
        ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by exact hj))
        (.sort u)) := by
  intro j hj
  have hjf : j < fs.length := by rw [ctorEmittedDoms_length] at hj; exact hj
  cases hfj : fs[j] with
  | plain D u =>
      obtain ⟨hD⟩ := fieldsTyT_domainAt fs hfs j
        (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hjf, hfj])
      have hD' := hasTyT_levelMono hn hD
      have hw := hasTyT_liftChain hcl (ctorInsPairs f (canonLevels fm.arity) np
        (fs.take j) 0) (plainCtxT (fs.take j) (telCtxT fv.params)) D (.sort u) hD'
      rw [ctorInsPairs_snds, insertChain_ctorInsPairs, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hjf), ← ctorEmittedDoms_take,
        ← policyPrefixContext_take'] at hw
      rw [liftChain_closed (.sort u) (fun _ => rfl) _] at hw
      have hdom : liftChain (ctorInsCutoffs (fs.take j)) D =
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
            rw [ctorEmittedDoms_length]; exact hjf) := by
        rw [ctorEmittedDoms_getElem_plain f (canonLevels fm.arity) np 0 fs hjf hfj,
          ← insCutoffs_map_ctorSkip, ← substT_ctorSub]
      rw [hdom] at hw
      exact ⟨u, ⟨hw⟩⟩
  | drec idx =>
      have hidx := fieldsTyT_drecAt fs hfs j
        (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hjf, hfj])
      simp only [Nat.zero_add] at hidx
      have h0 := argsTyT_levelMono hn hidx
      rw [hX, lift_policyPi] at h0
      simp only [Nat.zero_add] at h0
      have hlen : idx.length = (fv.indices.map Prod.fst).length := by
        have := argsTyT_policyPi_sort_length _ _ _ rfl h0
        rwa [length_liftDomsT] at this
      have hfa := famApp_typed_drec hcl hres (fs.take j) idx np
        (plainIdxT (fs.take j) 0) hnp hn rfl hlen h0
      have hw := hasTyT_liftChain hcl (ctorInsPairs f (canonLevels fm.arity) np
        (fs.take j) 0) (plainCtxT (fs.take j) (telCtxT fv.params)) _ _ hfa
      rw [ctorInsPairs_snds, insertChain_ctorInsPairs, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hjf), ← ctorEmittedDoms_take,
        ← policyPrefixContext_take'] at hw
      rw [liftChain_closed (.sort fv.sort) (fun _ => rfl) _] at hw
      have hR := plainIdxT_add_ctorInsCutoffs_length (fs.take j)
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjf)] at hR
      have hdom : liftChain (ctorInsCutoffs (fs.take j))
          (foldApps (.const f (canonLevels fm.arity))
            (policyParameterLocals np (plainIdxT (fs.take j) 0) ++ idx)) =
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
            rw [ctorEmittedDoms_length]; exact hjf) := by
        rw [ctorEmittedDoms_getElem_drec f (canonLevels fm.arity) np 0 fs hjf hfj,
          ← insCutoffs_map_ctorSkip, ← substT_ctorSub, substT_foldApps, List.map_append,
          map_policyParameterLocals_ctorSub np _ (fs.take j)
            (fun i hi => ctorInsCutoffs_le (fs.take j) i hi)]
        simp only [substT]
        rw [show plainIdxT (fs.take j) 0 + (ctorInsCutoffs (fs.take j)).length =
          0 + j from by omega]
      rw [hdom] at hw
      exact ⟨fv.sort, ⟨hw⟩⟩
  | drecD D idx =>
      exact absurd hfj (hnd j hjf D idx)

/-- `hI1_fieldsT` under `shift` boundary binders (`Δd` = the motive plus the
    earlier minors): the lifted emitted domains typed at the lifted prefix. -/
private theorem hI1_fieldsT_at {E : ResolvedEnv} {n : Nat} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} (hcl : EnvClosed E) (hres : E.members f = some fm)
    {np : Nat} {res : List (Expr Nat)} {X : Expr Nat}
    (fs : List FieldT)
    (hfs : FieldsTyT E fm.arity (fun k => lift 0 k X)
      (telCtxT fv.params) 0 fs res)
    (hX : X = policyPi (fv.indices.map Prod.fst) (.sort fv.sort))
    (hnp : fv.params.length = np) (hnd : NoDrecDT fs)
    (hn : fm.arity ≤ n) (Δd : LCtx) :
    ∀ j (hj : j < (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).length),
      ∃ u, Nonempty (HasTyT E n
        (policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
          (Δd.reverse ++ telCtxT fv.params))
        ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'(by exact hj))
        (.sort u)) :=
  hI1_at_of_pointwise hcl Δd (hI1_fieldsT hcl hres fs hfs hX hnp hnd hn)


/-- `transparentBody` results are lift-stable: member bodies are closed
    (`EnvClosed`), and `instantiateLevels` does not touch `bvar`s. The
    `whnfFuel` δ-step needs this to push `lift` past an unfolded body. -/
theorem transparentBody_lift (E : ResolvedEnv) (hcl : EnvClosed E)
    {r : Nat} {ls : List Level} {body : Expr Nat}
    (hb : transparentBody E r ls = some body) (c a : Nat) :
    lift c a body = body := by
  unfold transparentBody at hb
  cases hmem : E.members r with
  | none => rw [hmem] at hb; cases hb
  | some m =>
      rw [hmem] at hb
      by_cases ht : transparent m.mclass = true
      · simp only [ht, ite_true] at hb
        cases hm : m.body with
        | none => rw [hm] at hb; cases hb
        | some b =>
            rw [hm] at hb
            obtain ⟨rfl⟩ := hb
            exact lift_of_closed _
              (instantiateLevels_closed0 ((hcl r m hmem).2 b hm 0) ls) c a
      · simp only [ht, ite_false] at hb; cases hb

/-- `whnfFuel` commutes with `lift`: its steps are δ (level-parameterized
    heads) and β/ζ (substitutions), all rename-stable. The conv-aware
    traversal's `hI3`-shift needs the `piTelescopeFuel` corollary. -/
theorem whnfFuel_lift (E : ResolvedEnv) (hcl : EnvClosed E) (c a : Nat) :
    (fuel : Nat) → (e : Expr Nat) →
      whnfFuel E fuel (lift c a e) = (whnfFuel E fuel e).map (lift c a)
  | 0, e => rfl
  | fuel + 1, e => by
      simp only [whnfFuel]
      rw [appsSpine_lift]
      cases hsp : appsSpine e with
      | mk head args =>
        cases head with
        | lam A B =>
            cases args with
            | nil => rfl
            | cons x args =>
                simp only [List.map_cons, lift, instantiate0]
                show whnfFuel E fuel (foldApps (instantiate 0 (lift c a x) (lift (c + 1) a B))
                      (args.map (lift c a))) =
                    Option.map (lift c a) (whnfFuel E fuel (foldApps (instantiate 0 x B) args))
                rw [← lift_instantiate_low a c 0 x (Nat.zero_le c) B]
                rw [← foldApps_lift]
                exact whnfFuel_lift E hcl c a fuel _
        | letE A v B =>
            simp only [lift, instantiate0]
            show whnfFuel E fuel (foldApps (instantiate 0 (lift c a v) (lift (c + 1) a B))
                  (args.map (lift c a))) =
                Option.map (lift c a) (whnfFuel E fuel (foldApps (instantiate 0 v B) args))
            rw [← lift_instantiate_low a c 0 v (Nat.zero_le c) B]
            rw [← foldApps_lift]
            exact whnfFuel_lift E hcl c a fuel _
        | const r ls =>
            show (match transparentBody E r ls with
                | some body => whnfFuel E fuel (foldApps body (args.map (lift c a)))
                | none => some (lift c a e)) =
              Option.map (lift c a) (match transparentBody E r ls with
                | some body => whnfFuel E fuel (foldApps body args)
                | none => some e)
            cases hb : transparentBody E r ls with
            | none => rfl
            | some body =>
                show whnfFuel E fuel (foldApps body (args.map (lift c a))) =
                    Option.map (lift c a) (whnfFuel E fuel (foldApps body args))
                conv => lhs; rw [← transparentBody_lift E hcl hb c a]
                rw [← foldApps_lift]
                exact whnfFuel_lift E hcl c a fuel _
        | bvar i =>
            simp only [lift]
            by_cases hci : c ≤ i
            · simp only [if_pos hci, Option.map_some']
            · simp only [if_neg hci, Option.map_some']
        | _ => rfl

/-- `piTelescopeFuel` commutes with `lift`: the telescope's domains lift at
    growing cutoffs, the body past all of them. -/
private theorem piTelescopeFuel_lift (E : ResolvedEnv) (hcl : EnvClosed E) (c a : Nat) :
    (fuel : Nat) → (e : Expr Nat) →
      piTelescopeFuel E fuel (lift c a e) =
        (piTelescopeFuel E fuel e).map fun p =>
          (p.1.mapIdx fun i D => lift (c + i) a D, lift (c + p.1.length) a p.2)
  | 0, e => rfl
  | fuel + 1, e => by
      simp only [piTelescopeFuel]
      rw [whnfFuel_lift E hcl c a fuel e]
      cases hw : whnfFuel E fuel e with
      | none => rfl
      | some w =>
          cases w with
          | pi A B =>
              simp only [lift, Option.map_some']
              rw [piTelescopeFuel_lift E hcl (c + 1) a fuel B]
              cases hp : piTelescopeFuel E fuel B with
              | none => rfl
              | some p =>
                  obtain ⟨doms, body⟩ := p
                  have hfn : (fun i (D : Expr Nat) => lift (c + 1 + i) a D) =
                      fun i D => lift (c + (i + 1)) a D := by
                    funext i D
                    exact congrArg (fun k => lift k a D) (by omega)
                  simp only [Option.map_some', List.mapIdx_cons, List.length_cons]
                  rw [hfn, show c + 0 = c by omega,
                    show c + 1 + doms.length = c + (doms.length + 1) by omega]
          | bvar i =>
              by_cases hci : c ≤ i
              · simp only [lift, Option.map_some', List.mapIdx_nil, List.length_nil,
                  Nat.add_zero, if_pos hci]
              · simp only [lift, Option.map_some', List.mapIdx_nil, List.length_nil,
                  Nat.add_zero, if_neg hci]
          | _ =>
              simp only [lift, Option.map_some', List.mapIdx_nil, List.length_nil,
                Nat.add_zero]

/-! ## the `.drecD` conv path: env restriction

`DrecDTypedT` carries its conversion in `extendEnv E f fm`; at the cell the
family is already admitted (`E.members f = some fm`), so the extension is the
identity on lookups and every derivation restricts back to `E`. This is the
reverse direction of `hasTyT_extendEnv`/`convT_extendEnv`/`tyConvT_extendEnv`
(`RcicTypedGroup`). -/

/-- a member lookup in an already-present extension collapses to `E`. -/
theorem members_restrictExt {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (h : E.members r = some m) {r' m'} :
    (extendEnv E r m).members r' = some m' → E.members r' = some m' := by
  intro hm
  simp only [extendEnv] at hm
  by_cases hr : r' = r
  · subst hr
    rw [if_pos rfl] at hm
    cases hm
    exact h
  · rw [if_neg hr] at hm
    exact hm

/-- the `extendEnv`-transported iota witness restricts back when the extension
    is already present. -/
def iotaWitness_restrictExt {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (h : E.members r = some m) (w : IotaWitness (extendEnv E r m)) : IotaWitness E :=
  { w with
    hrec := members_restrictExt h w.hrec
    hctor := members_restrictExt h w.hctor
    hfam := members_restrictExt h w.hfam }

/-- the restricted witness computes the same redex/contractum. -/
def derivedIota_restrictExt {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (h : E.members r = some m) {lhs rhs : Expr Nat} :
    DerivedIota (extendEnv E r m) lhs rhs → DerivedIota E lhs rhs
  | .of w => .of (iotaWitness_restrictExt h w)

mutual

/-- the tree's typing restricts from an already-present extension (the reverse
    of `hasTyT_extendEnv`): every member read is identical to `E`'s. -/
def hasTyT_restrictExt {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (h : E.members r = some m) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT (extendEnv E r m) n Γ e A →
      HasTyT E n Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A h' => .bvar Γ i A h'
  | _, _, _, .const Γ r' ls m' hres hlen hwf =>
      .const Γ r' ls m' (members_restrictExt h hres) hlen hwf
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi Γ A u B v (hasTyT_restrictExt h hA) (hasTyT_restrictExt h hB)
  | _, _, _, .lam Γ A u body B hA hbody =>
      .lam Γ A u body B (hasTyT_restrictExt h hA) (hasTyT_restrictExt h hbody)
  | _, _, _, .app Γ f a A B hf ha =>
      .app Γ f a A B (hasTyT_restrictExt h hf) (hasTyT_restrictExt h ha)
  | _, _, _, .letE Γ A u value B body hA hv hb =>
      .letE Γ A u value B body (hasTyT_restrictExt h hA) (hasTyT_restrictExt h hv)
        (hasTyT_restrictExt h hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyT_restrictExt h hexp)
  | _, _, _, .conv Γ e A B u h' hc =>
      .conv Γ e A B u (hasTyT_restrictExt h h') (convT_restrictExt h hc)

def convT_restrictExt {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (h : E.members r = some m) :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT (extendEnv E r m) n Γ a b A →
      ConvT E n Γ a b A
  | _, _, _, _, .refl Γ a A h' => .refl Γ a A (hasTyT_restrictExt h h')
  | _, _, _, _, .symm Γ a b A h' => .symm Γ a b A (convT_restrictExt h h')
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      .trans Γ a b c A (convT_restrictExt h h1) (convT_restrictExt h h2)
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg =>
      .beta Γ A body arg B u (hasTyT_restrictExt h hA) (hasTyT_restrictExt h hbody)
        (hasTyT_restrictExt h harg)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb =>
      .zeta Γ A value body B u (hasTyT_restrictExt h hA) (hasTyT_restrictExt h hv)
        (hasTyT_restrictExt h hb)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (hasTyT_restrictExt h hv)
  | _, _, _, _, .delta Γ r' ls m' b hres hbody htr hlen hwf hb =>
      .delta Γ r' ls m' b (members_restrictExt h hres) hbody htr hlen hwf
        (hasTyT_restrictExt h hb)
  | _, _, _, _, .iota Γ lhs rhs T hd hlhs hrhs =>
      .iota Γ lhs rhs T (derivedIota_restrictExt h hd) (hasTyT_restrictExt h hlhs)
        (hasTyT_restrictExt h hrhs)
  | _, _, _, _, .lit Γ t exp T hl hexp =>
      .lit Γ t exp T hl (hasTyT_restrictExt h hexp)
  | _, _, _, _, .app Γ f g a b A B h1 h2 =>
      .app Γ f g a b A B (convT_restrictExt h h1) (convT_restrictExt h h2)
  | _, _, _, _, .lam Γ A A' b b' B u hA hb =>
      .lam Γ A A' b b' B u (convT_restrictExt h hA) (convT_restrictExt h hb)
  | _, _, _, _, .pi Γ A A' B B' u v hA hB =>
      .pi Γ A A' B B' u v (convT_restrictExt h hA) (convT_restrictExt h hB)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb =>
      .letE Γ A A' v v' b b' B u (convT_restrictExt h hA) (convT_restrictExt h hv)
        (convT_restrictExt h hb)
  | _, _, _, _, .sorts Γ l₁ l₂ he => .sorts Γ l₁ l₂ he
  | _, _, _, _, .consts Γ r' ls ls' m' hres hlen hwf hwf' he =>
      .consts Γ r' ls ls' m' (members_restrictExt h hres) hlen hwf hwf' he
  | _, _, _, _, .eta Γ f A B h' => .eta Γ f A B (hasTyT_restrictExt h h')
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (hasTyT_restrictExt h hP) (hasTyT_restrictExt h hp)
        (hasTyT_restrictExt h hq)
  | _, _, _, _, .tyConv Γ a b A A' u h' hA =>
      .tyConv Γ a b A A' u (convT_restrictExt h h') (convT_restrictExt h hA)

end

/-- `TyConvT` restricts from an already-present extension. -/
def tyConvT_restrictExt {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (h : E.members r = some m) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT (extendEnv E r m) n Γ A B →
      TyConvT E n Γ A B
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B u c => .of Γ A B u (convT_restrictExt h c)
  | _, _, _, .trans Γ A B C c₁ c₂ =>
      .trans Γ A B C (tyConvT_restrictExt h c₁) (tyConvT_restrictExt h c₂)

/-- the `hI1` discharger with `.drecD` admitted (the conv path): a δ-reached
    field's emitted domain is its σ'd surface `D`, typed via the view's
    `DrecDTypedT` evidence — restricted back to `E` (`hres`), level-lifted, and
    pushed along the same `ctorInsPairs` insertion chain as `.plain`. -/
private theorem hI1_fieldsT_conv {E : ResolvedEnv} {n : Nat} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} (hcl : EnvClosed E) (hres : E.members f = some fm)
    {np : Nat} {res : List (Expr Nat)} {X : Expr Nat}
    (fs : List FieldT)
    (hfs : FieldsTyT E fm.arity (fun k => lift 0 k X)
      (telCtxT fv.params) 0 fs res)
    (hX : X = policyPi (fv.indices.map Prod.fst) (.sort fv.sort))
    (hnp : fv.params.length = np)
    (hdd : DrecDTypedT E f fm fv fs)
    (hn : fm.arity ≤ n) :
    ∀ j (hj : j < (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs).length),
      ∃ u, Nonempty (HasTyT E n
        (policyPrefixContext (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs) j ++
          telCtxT fv.params)
        ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by exact hj))
        (.sort u)) := by
  intro j hj
  have hjf : j < fs.length := by rw [ctorEmittedDoms_length] at hj; exact hj
  cases hfj : fs[j] with
  | plain D u =>
      obtain ⟨hD⟩ := fieldsTyT_domainAt fs hfs j
        (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hjf, hfj])
      have hD' := hasTyT_levelMono hn hD
      have hw := hasTyT_liftChain hcl (ctorInsPairs f (canonLevels fm.arity) np
        (fs.take j) 0) (plainCtxT (fs.take j) (telCtxT fv.params)) D (.sort u) hD'
      rw [ctorInsPairs_snds, insertChain_ctorInsPairs, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hjf), ← ctorEmittedDoms_take,
        ← policyPrefixContext_take'] at hw
      rw [liftChain_closed (.sort u) (fun _ => rfl) _] at hw
      have hdom : liftChain (ctorInsCutoffs (fs.take j)) D =
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
            rw [ctorEmittedDoms_length]; exact hjf) := by
        rw [ctorEmittedDoms_getElem_plain f (canonLevels fm.arity) np 0 fs hjf hfj,
          ← insCutoffs_map_ctorSkip, ← substT_ctorSub]
      rw [hdom] at hw
      exact ⟨u, ⟨hw⟩⟩
  | drec idx =>
      have hidx := fieldsTyT_drecAt fs hfs j
        (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hjf, hfj])
      simp only [Nat.zero_add] at hidx
      have h0 := argsTyT_levelMono hn hidx
      rw [hX, lift_policyPi] at h0
      simp only [Nat.zero_add] at h0
      have hlen : idx.length = (fv.indices.map Prod.fst).length := by
        have := argsTyT_policyPi_sort_length _ _ _ rfl h0
        rwa [length_liftDomsT] at this
      have hfa := famApp_typed_drec hcl hres (fs.take j) idx np
        (plainIdxT (fs.take j) 0) hnp hn rfl hlen h0
      have hw := hasTyT_liftChain hcl (ctorInsPairs f (canonLevels fm.arity) np
        (fs.take j) 0) (plainCtxT (fs.take j) (telCtxT fv.params)) _ _ hfa
      rw [ctorInsPairs_snds, insertChain_ctorInsPairs, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hjf), ← ctorEmittedDoms_take,
        ← policyPrefixContext_take'] at hw
      rw [liftChain_closed (.sort fv.sort) (fun _ => rfl) _] at hw
      have hR := plainIdxT_add_ctorInsCutoffs_length (fs.take j)
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjf)] at hR
      have hdom : liftChain (ctorInsCutoffs (fs.take j))
          (foldApps (.const f (canonLevels fm.arity))
            (policyParameterLocals np (plainIdxT (fs.take j) 0) ++ idx)) =
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
            rw [ctorEmittedDoms_length]; exact hjf) := by
        rw [ctorEmittedDoms_getElem_drec f (canonLevels fm.arity) np 0 fs hjf hfj,
          ← insCutoffs_map_ctorSkip, ← substT_ctorSub, substT_foldApps, List.map_append,
          map_policyParameterLocals_ctorSub np _ (fs.take j)
            (fun i hi => ctorInsCutoffs_le (fs.take j) i hi)]
        simp only [substT]
        rw [show plainIdxT (fs.take j) 0 + (ctorInsCutoffs (fs.take j)).length =
          0 + j from by omega]
      rw [hdom] at hw
      exact ⟨fv.sort, ⟨hw⟩⟩
  | drecD D idx =>
      -- the δ-reached field's surface domain types at the family's sort in
      -- `extendEnv`; restrict back to `E`, level-lift, then the same chain
      have hsplit : fs = fs.take j ++ .drecD D idx :: fs.drop (j + 1) := by
        have hd : fs.drop j = .drecD D idx :: fs.drop (j + 1) := by
          rw [List.drop_eq_getElem_cons hjf, hfj]
        rw [← hd]
        exact (List.take_append_drop j fs).symm
      obtain ⟨hD⟩ := (hdd (fs.take j) D idx (fs.drop (j + 1)) hsplit).1
      have hD' := hasTyT_levelMono hn (hasTyT_restrictExt hres hD)
      have hw := hasTyT_liftChain hcl (ctorInsPairs f (canonLevels fm.arity) np
        (fs.take j) 0) (plainCtxT (fs.take j) (telCtxT fv.params)) D
        (.sort fv.sort) hD'
      rw [ctorInsPairs_snds, insertChain_ctorInsPairs, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hjf), ← ctorEmittedDoms_take,
        ← policyPrefixContext_take'] at hw
      rw [liftChain_closed (.sort fv.sort) (fun _ => rfl) _] at hw
      have hdom : liftChain (ctorInsCutoffs (fs.take j)) D =
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
            rw [ctorEmittedDoms_length]; exact hjf) := by
        rw [ctorEmittedDoms_getElem_drecD f (canonLevels fm.arity) np 0 fs hjf hfj,
          ← insCutoffs_map_ctorSkip, ← substT_ctorSub]
      rw [hdom] at hw
      exact ⟨fv.sort, ⟨hw⟩⟩

/-- `hI1_fieldsT_conv` under `shift` boundary binders: the conv path's `hI1`. -/
private theorem hI1_fieldsT_conv_at {E : ResolvedEnv} {n : Nat} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} (hcl : EnvClosed E) (hres : E.members f = some fm)
    {np : Nat} {res : List (Expr Nat)} {X : Expr Nat}
    (fs : List FieldT)
    (hfs : FieldsTyT E fm.arity (fun k => lift 0 k X)
      (telCtxT fv.params) 0 fs res)
    (hX : X = policyPi (fv.indices.map Prod.fst) (.sort fv.sort))
    (hnp : fv.params.length = np)
    (hdd : DrecDTypedT E f fm fv fs)
    (hn : fm.arity ≤ n) (Δd : LCtx) :
    ∀ j (hj : j < (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).length),
      ∃ u, Nonempty (HasTyT E n
        (policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
          (Δd.reverse ++ telCtxT fv.params))
        ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'(by exact hj))
        (.sort u)) :=
  hI1_at_of_pointwise hcl Δd (hI1_fieldsT_conv hcl hres fs hfs hX hnp hdd hn)

/-- a sort-sort `TyConvT` is `eqN` — row 1 of the `TypedRowsWf` supply at the
    semantic-prefix front. -/
theorem tyConvT_eqN {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) (hP : hW.InScope)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (h : TyConvT E n Γ (.sort u) (.sort v)) : eqN u v :=
  (Ann.typedRowsWf_of_envWfT_semPrefix hW hP n).sortRow hΓ h

/-- the T-side chain adapter (the `convT_of_tyConvT_sort` shape at `E` itself):
    a `TyConvT` to `B` collapses to one `ConvT` at any sort `B` is typed at.
    Midpoints recover their sort typing through `endpoints3_of_envWfT` (debts
    `SubstLetT`/`ConstsRightDataT`); sort-sort links close by `tyConvT_eqN` on
    `DT012T_type_uniqueness`. -/
theorem tyConvT_convT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) (hP : hW.InScope)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {v : Level}
    (h : TyConvT E n Γ A B) (hB : HasTyT E n Γ B (.sort v)) :
    Nonempty (ConvT E n Γ A B (.sort v)) := by
  induction h generalizing v with
  | refl _ => exact ⟨.refl _ _ _ hB⟩
  | of A B u c =>
      obtain ⟨_, hBu, _⟩ := endpoints3_of_envWfT hW hSL hconst hΓ c
      obtain ⟨tc⟩ := DT012T_type_uniqueness hW hP hΓ hBu hB
      exact ⟨.tyConv _ _ _ _ _ _ c (.sorts _ _ _ (tyConvT_eqN hW hP hΓ tc))⟩
  | trans A X C _ _ ih1 ih2 =>
      obtain ⟨c2⟩ := ih2 hB
      obtain ⟨hB2, _, _⟩ := endpoints3_of_envWfT hW hSL hconst hΓ c2
      obtain ⟨c1⟩ := ih1 hB2
      exact ⟨.trans _ _ _ _ _ c1 c2⟩

/-- `whnfFuel`'s steps as the machine's spine chain: each fuel step is a
    `headBeta`, `headZeta`, or `headDelta` at the `appsSpine` head, a stuck
    head is `refl`. Structural only — carries no typing. -/
def whnfFuel_machineRed {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    (fuel : Nat) → (e w : Expr Nat) → whnfFuel E fuel e = some w →
      Machine.MachineRed E n Γ e w
  | 0, _, _, h => by cases h
  | fuel + 1, e, w, h => by
      unfold whnfFuel at h
      cases hsp : appsSpine e with
      | mk head args =>
          rw [hsp] at h
          have he : e = foldApps head args := (Machine.machineSpineEq hsp).symm
          cases head with
          | bvar i => injection h with h; subst h; exact .refl Γ e
          | sort l => injection h with h; subst h; exact .refl Γ e
          | const r ls =>
              cases htb : transparentBody E r ls with
              | none =>
                  simp only [htb] at h
                  injection h with h; subst h; exact .refl Γ e
              | some body =>
                  simp only [htb] at h
                  unfold transparentBody at htb
                  cases hres : E.members r with
                  | none => simp only [hres] at htb; cases htb
                  | some m =>
                      simp only [hres] at htb
                      by_cases htr : transparent m.mclass = true
                      · rw [if_pos htr] at htb
                        cases hb : m.body with
                        | none => simp only [hb] at htb; cases htb
                        | some b =>
                            simp only [hb] at htb
                            injection htb with htb
                            subst htb
                            exact he ▸ Machine.MachineRed.headDelta Γ r ls m b args
                              hres hb htr (whnfFuel_machineRed Γ fuel _ _ h)
                      · rw [if_neg htr] at htb; cases htb
          | app f x => injection h with h; subst h; exact .refl Γ e
          | lam A b =>
              cases args with
              | nil => injection h with h; subst h; exact .refl Γ e
              | cons a rest =>
                  exact he ▸ Machine.MachineRed.headBeta Γ A b a rest
                    (whnfFuel_machineRed Γ fuel _ _ h)
          | pi A B => injection h with h; subst h; exact .refl Γ e
          | letE A v b =>
              exact he ▸ Machine.MachineRed.headZeta Γ A v b args
                (whnfFuel_machineRed Γ fuel _ _ h)
          | lit t => injection h with h; subst h; exact .refl Γ e

/-- whnf-soundness at a typed term: a `whnfFuel` run is a `MachineRed` chain,
    hence a `ConvT` at the term's own type. -/
private theorem whnfFuel_convT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e w T : Expr Nat} (fuel : Nat)
    (hw : whnfFuel E fuel e = some w) (hty : HasTyT E n Γ e T) :
    Nonempty (ConvT E n Γ e w T) :=
  Machine.machineRed_toConvT hW hP hΓ (whnfFuel_machineRed Γ fuel e w hw) hty

/-- the `RecFieldConvAtT` tail shift: a conv-aware witness at position `j + 1` of
    `A :: ds` (the field's own ctx `Δ` at distance `d`) transports to position `j` of
    the lifted tail `liftDomsT 0 1 ds`, in the context extended by the field's binder
    `A` and its emitted induction hypothesis `ih`, at `d + 2`.  `hpit` rides
    `piTelescopeFuel_lift` through `lift 0 1 ∘ lift j 1 = lift (j+1) 1 ∘ lift 0 1`;
    `hbc` rides `convTWeaken` through the one-decl `insertAt` at the `ds`-prefix
    boundary; `hW1` rides `argsTyT_weakenUnderTel` over the combined
    `ds.take (j+1) ++ wdoms` prefix — each element lifts at its own depth, matching
    `liftDomsT`. -/
private theorem recFieldConvAtT_succ {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {f np : Nat} {ls : List Level} {Is : List (Expr Nat)} {l : Level}
    {fuel : Nat} {A : Expr Nat} {ds : List (Expr Nat)} {Δ : LCtx} {d j inner : Nat}
    (ih : Expr Nat)
    (h : RecFieldConvAtT E n f ls np Is l fuel (A :: ds) Δ d (j + 1) inner) :
    RecFieldConvAtT E n f ls np Is l fuel (liftDomsT 0 1 ds)
      (.assumption ih :: .assumption A :: Δ) (d + 2) j inner := by
  obtain ⟨hj, wdoms, widx, u', hdl, hil, hfuel, hpit, hbc, hW1⟩ := h
  have hj' : j < ds.length := Nat.lt_of_succ_lt_succ hj
  have hjL : j < (liftDomsT 0 1 ds).length := by
    rw [length_liftDomsT]; exact hj'
  have htj : (ds.take (j + 1)).length = j + 1 := List.length_take_of_le hj'
  have hget : ((liftDomsT 0 1 ds)[j]'hjL) = lift j 1 (ds[j]'hj') := by
    rw [getElem_liftDomsT 1 ds 0 j hj', Nat.zero_add]
  -- the lifted famApp read: parameters shift, index args lift at the whole prefix
  have hbody : lift (j + 1 + wdoms.length) 1
      (foldApps (.const f ls)
        (policyParameterLocals np (inner + (j + 1) + d + 1) ++ widx)) =
      foldApps (.const f ls)
        (policyParameterLocals np (inner + j + (d + 2) + 1) ++
          widx.map (lift (j + 1 + inner) 1)) := by
    rw [hdl, foldApps_lift, List.map_append,
      policyParameterLocals_lift_le np _ (j + 1 + inner) 1 (by omega),
      show inner + (j + 1) + d + 1 + 1 = inner + j + (d + 2) + 1 from by omega]
    rfl
  refine ⟨hjL, liftDomsT (j + 1) 1 wdoms, widx.map (lift (j + 1 + inner) 1), u',
    by rw [length_liftDomsT]; exact hdl, by rw [List.length_map]; exact hil, hfuel,
    ?_, ?_, ?_⟩
  · -- hpit: the lifted read
    have hpit' : piTelescopeFuel E fuel (lift 0 1 (ds[j]'hj')) = some (wdoms,
        foldApps (.const f ls)
          (policyParameterLocals np (inner + (j + 1) + d + 1) ++ widx)) := hpit
    rw [hget]
    show piTelescopeFuel E fuel (lift 0 1 (lift j 1 (ds[j]'hj'))) =
      some (liftDomsT (j + 1) 1 wdoms, foldApps (.const f ls)
        (policyParameterLocals np (inner + j + (d + 2) + 1) ++
          widx.map (lift (j + 1 + inner) 1)))
    rw [lift_lift_permute 1 1 j 0 (Nat.zero_le j), Nat.add_comm 1 j]
    have hpt := piTelescopeFuel_lift E hcl (j + 1) 1 fuel (lift 0 1 (ds[j]'hj'))
    rw [hpit'] at hpt
    rw [hpt]
    show some (wdoms.mapIdx (fun i D => lift (j + 1 + i) 1 D),
        lift (j + 1 + wdoms.length) 1 (foldApps (.const f ls)
          (policyParameterLocals np (inner + (j + 1) + d + 1) ++ widx))) = _
    rw [hbody, ← liftDomsT_eq_mapIdx (j + 1) 1 wdoms]
  · -- hbc: convTWeaken at the `ppc ds (j+1)` boundary inserts the ih binder
    obtain ⟨hbc⟩ := hbc
    have hbc' : ConvT E n
        (.assumption (ds[j]'hj') :: (policyPrefixContext (A :: ds) (j + 1) ++ Δ))
        (lift 0 1 (ds[j]'hj'))
        (policyPi wdoms (foldApps (.const f ls)
          (policyParameterLocals np (inner + (j + 1) + d + 1) ++ widx)))
        (.sort u') := hbc
    have hctx0 : .assumption (ds[j]'hj') ::
        (policyPrefixContext (A :: ds) (j + 1) ++ Δ) =
        policyPrefixContext ds (j + 1) ++ (.assumption A :: Δ) := by
      rw [policyPrefixContext_cons_succ A ds j Δ, ← List.cons_append,
        ← policyPrefixContext_succ ds j hj']
    rw [hctx0] at hbc'
    have hwk := convTWeaken (.assumption ih) hcl (c := j + 1) hbc'
    have hb := insertAt_ppc_mapIdx (.assumption ih) (ds.take (j + 1)) (.assumption A :: Δ)
    rw [htj, policyPrefixContext_take] at hb
    have hmap : (ds.take (j + 1)).mapIdx (fun i D => lift i 1 D) =
        (liftDomsT 0 1 ds).take (j + 1) := by
      rw [liftDomsT_take, liftDomsT_eq_mapIdx]
      apply mapIdx_congr'
      intro i hi
      rw [Nat.zero_add]
    rw [hmap, policyPrefixContext_take] at hb
    rw [hb] at hwk
    have hr1 := policyPrefixContext_succ (liftDomsT 0 1 ds) j hjL
    rw [hr1, List.cons_append] at hwk
    have haa : lift (j + 1) 1 (lift 0 1 (ds[j]'hj')) =
        lift 0 1 ((liftDomsT 0 1 ds)[j]'hjL) := by
      rw [getElem_liftDomsT 1 ds 0 j hj', Nat.zero_add,
        lift_lift_permute 1 1 j 0 (Nat.zero_le j), Nat.add_comm 1 j]
    have hbb : lift (j + 1) 1 (policyPi wdoms (foldApps (.const f ls)
        (policyParameterLocals np (inner + (j + 1) + d + 1) ++ widx))) =
        policyPi (liftDomsT (j + 1) 1 wdoms) (foldApps (.const f ls)
          (policyParameterLocals np (inner + j + (d + 2) + 1) ++
            widx.map (lift (j + 1 + inner) 1))) := by
      rw [lift_policyPi]
      exact congrArg (policyPi (liftDomsT (j + 1) 1 wdoms)) hbody
    have hsort : lift (j + 1) 1 (Expr.sort u' : Expr Nat) = (Expr.sort u' : Expr Nat) := rfl
    rw [haa, hbb, hsort] at hwk
    exact ⟨hwk⟩
  · -- hW1: weakenUnderTel over the combined ds-prefix ++ wdoms telescope
    obtain ⟨hW1⟩ := hW1
    have hW1' : ArgsTyT E n
        (policyPrefixContext wdoms inner ++
          (.assumption (ds[j]'hj') :: (policyPrefixContext (A :: ds) (j + 1) ++ Δ)))
        (idxTelAt Is l (inner + (j + 1) + d + 1)) widx := hW1
    have hcomb1 : (ds.take (j + 1) ++ wdoms).length = j + 1 + inner := by
      rw [List.length_append, htj, hdl]
    have hctx1 : policyPrefixContext wdoms inner ++
        (.assumption (ds[j]'hj') :: (policyPrefixContext (A :: ds) (j + 1) ++ Δ)) =
        policyPrefixContext (ds.take (j + 1) ++ wdoms) (j + 1 + inner) ++
          (.assumption A :: Δ) := by
      have hap := policyPrefixContext_append (ds.take (j + 1)) wdoms inner
      rw [htj, policyPrefixContext_take] at hap
      rw [policyPrefixContext_cons_succ A ds j Δ, ← List.cons_append,
        ← policyPrefixContext_succ ds j hj', ← List.append_assoc, ← hap]
    rw [hctx1] at hW1'
    have hwk := argsTyT_weakenUnderTel hcl (ds.take (j + 1) ++ wdoms) (j + 1 + inner)
      (Nat.le_of_eq hcomb1.symm) [.assumption ih] hW1'
    rw [List.length_singleton, liftDomsT_append, htj, Nat.zero_add,
      ← liftDomsT_take] at hwk
    have hsplit : policyPrefixContext ((liftDomsT 0 1 ds).take (j + 1) ++
        liftDomsT (j + 1) 1 wdoms) (j + 1 + inner) =
        policyPrefixContext (liftDomsT (j + 1) 1 wdoms) inner ++
          policyPrefixContext (liftDomsT 0 1 ds) (j + 1) := by
      have hap := policyPrefixContext_append ((liftDomsT 0 1 ds).take (j + 1))
        (liftDomsT (j + 1) 1 wdoms) inner
      rw [List.length_take, Nat.min_eq_left
        (by rw [length_liftDomsT]; exact hj'), policyPrefixContext_take] at hap
      exact hap
    have hr1 := policyPrefixContext_succ (liftDomsT 0 1 ds) j hjL
    rw [hsplit, hr1, List.cons_append] at hwk
    have hidx : lift (j + 1 + inner) 1 (idxTelAt Is l (inner + (j + 1) + d + 1)) =
        idxTelAt Is l (inner + j + (d + 2) + 1) := by
      rw [idxTelAt_lift Is l (inner + (j + 1) + d + 1) (j + 1 + inner) 1 (by omega)]
      exact congrArg (idxTelAt Is l) (by omega)
    rw [hidx] at hwk
    exact ⟨by simpa only [List.singleton_append, List.append_assoc] using hwk⟩


/-- **the minor builder, typed (forward).** The remaining field telescope's domains typed, the motive
    typed at its type, and each remaining recursive field literal with its index arguments typed: every
    binder `minorFromTelescope` emits is typed, each induction hypothesis at the
    motive's universe. -/
private theorem minorTyped_go {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (fuel np f : Nat) (ls : List Level)
    (Is : List (Expr Nat)) (uM l : Level) (hf : transparentBody E f ls = none) :
    (ss : List FieldShape) → (Δ : LCtx) → (d : Nat) → (M acc : Expr Nat) → (ds : List (Expr Nat)) →
    (B R : Expr Nat) → ss.length = ds.length →
    Nonempty (HasTyT E n Δ M (motTyAt f ls np Is uM d)) →
    (∀ j (hj : j < ds.length), ∃ u, Nonempty (HasTyT E n (policyPrefixContext ds j ++ Δ) ds[j] (.sort u))) →
    (∀ j inner, ss[j]? = some (.recursive inner) → RecFieldAtT E n f ls np Is l fuel ds Δ d j inner) →
    minorFromTelescope E fuel np M acc ss (policyPi ds B) = some R →
    MinorTypedT E n uM Δ ss R
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, _, _, _, _, [], _, _, hlen, _, _, _, _ => (Nat.succ_ne_zero _ hlen).elim
  | .nonrecursive :: ss, Δ, d, M, acc, A :: ds, B, R, hlen, hM, hI1, hI3, hmin => by
      simp only [policyPi, minorFromTelescope] at hmin
      cases hr : minorFromTelescope E fuel np (lift 0 1 M) (.app (lift 0 1 acc) (.bvar 0)) ss
          (policyPi ds B) with
      | none => rw [hr] at hmin; exact Option.noConfusion hmin
      | some R' =>
          rw [hr] at hmin
          injection hmin with hmin
          subst hmin
          refine ⟨?_, ?_⟩
          · obtain ⟨u, hu⟩ := hI1 0 (Nat.succ_pos _)
            exact ⟨u, by simpa only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
              List.nil_append] using hu⟩
          · refine minorTyped_go hcl fuel np f ls Is uM l hf ss (.assumption A :: Δ) (d + 1) (lift 0 1 M) _
              ds B R' (Nat.succ.inj hlen) ?_ ?_ ?_ hr
            · obtain ⟨hM⟩ := hM
              have hw := hasTyTWeaken (LocalDecl.assumption A) hcl (c := 0) hM
              rw [insertAt_zero, motTyAt_lift] at hw
              exact ⟨hw⟩
            · intro j hj
              obtain ⟨u, hu⟩ := hI1 (j + 1) (Nat.succ_lt_succ hj)
              rw [policyPrefixContext_cons_succ] at hu
              exact ⟨u, hu⟩
            · intro j inner hss
              obtain ⟨hj, doms, idx, h1, h2, h3, h4, h5⟩ := hI3 (j + 1) inner
                (by rw [List.getElem?_cons_succ]; exact hss)
              have harith : inner + (j + 1) + d = inner + j + (d + 1) := by omega
              rw [policyPrefixContext_cons_succ, harith] at h5
              rw [harith] at h4
              exact ⟨Nat.lt_of_succ_lt_succ hj, doms, idx, h1, h2, h3, h4, h5⟩
  | .recursive inner :: ss, Δ, d, M, acc, A :: ds, B, R, hlen, hM, hI1, hI3, hmin => by
      obtain ⟨_, doms, idx, hdl, hil, hfuel, hA, hW1⟩ := hI3 0 inner List.getElem?_cons_zero
      have hA' : A = policyPi doms (foldApps (.const f ls)
          (policyParameterLocals np (inner + d) ++ idx)) := by
        simpa only [Nat.add_zero] using hA
      have hdoms' : (liftDomsT 0 1 doms).length = inner := by rw [length_liftDomsT, hdl]
      have hshape : lift 0 1 A = policyPi (liftDomsT 0 1 doms) (foldApps (.const f ls)
          (policyParameterLocals np (inner + (d + 1)) ++ idx.map (lift inner 1))) := by
        rw [hA', lift_policyPi, foldApps_lift, List.map_append, hdl, Nat.zero_add,
          policyParameterLocals_lift_le np (inner + d) inner 1 (Nat.le_add_right _ _)]
        rfl
      have hih : funIHType E fuel np A M inner = some (policyPi (liftDomsT 0 1 doms)
          (foldApps (lift 0 inner (lift 0 1 M))
            (idx.map (lift inner 1) ++ [foldApps (.bvar inner) (policyLocals inner)]))) := by
        unfold funIHType
        rw [hshape, piTelescopeFuel_policyPi_famApp hf _ _ (by rw [hdoms']; exact hfuel)]
        simp only [hdoms', ↓reduceIte,
          familyIdx_foldApps_const (policyParameterLocals_length np (inner + (d + 1)))]
        rfl
      let ihT := policyPi (liftDomsT 0 1 doms) (foldApps (lift 0 inner (lift 0 1 M))
        (idx.map (lift inner 1) ++ [foldApps (.bvar inner) (policyLocals inner)]))
      simp only [policyPi, minorFromTelescope, hih] at hmin
      cases hr : minorFromTelescope E fuel np (lift 0 2 M) (.app (lift 0 2 acc) (.bvar 1)) ss
          (lift 0 1 (policyPi ds B)) with
      | none => rw [hr] at hmin; exact Option.noConfusion hmin
      | some R' =>
          rw [hr] at hmin
          injection hmin with hmin
          subst hmin
          obtain ⟨uA, hAty⟩ := hI1 0 (Nat.succ_pos _)
          have hAty' : Nonempty (HasTyT E n Δ A (.sort uA)) := by
            simpa only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
              List.nil_append] using hAty
          refine ⟨⟨uA, hAty'⟩, ?_, ?_⟩
          · -- the induction hypothesis
            have hW1' : Nonempty (ArgsTyT E n (policyPrefixContext (liftDomsT 0 1 doms)
                inner ++ (.assumption A :: Δ))
                (idxTelAt Is l (inner + (d + 1))) (idx.map (lift inner 1))) := by
              obtain ⟨hw⟩ := hW1
              have h0 : policyPrefixContext doms inner ++ (policyPrefixContext (A :: ds) 0 ++ Δ) =
                  policyPrefixContext doms inner ++ Δ := by
                simp only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil, List.nil_append]
              rw [h0] at hw
              have hw' := argsTyT_weakenUnderTel hcl doms inner (Nat.le_of_eq hdl.symm) [LocalDecl.assumption A] hw
              rw [List.length_singleton, idxTelAt_lift Is l (inner + 0 + d) inner 1 (by omega)] at hw'
              exact ⟨by simpa only [List.singleton_append, show inner + 0 + d + 1 = inner + (d + 1) by omega]
                using hw'⟩
            exact hasTyT_ih_fun hcl A hAty' f ls np Is uM l d (liftDomsT 0 1 doms)
              (idx.map (lift inner 1)) inner hdoms' hshape (by rw [List.length_map, hil]) hW1' M hM
          · -- the rest, past the field and its induction hypothesis
            rw [lift_policyPi, Nat.zero_add] at hr
            refine minorTyped_go hcl fuel np f ls Is uM l hf ss _ (d + 2) (lift 0 2 M) _
              (liftDomsT 0 1 ds) _ R' (by rw [length_liftDomsT]; exact Nat.succ.inj hlen) ?_ ?_ ?_ hr
            · obtain ⟨hM⟩ := hM
              have hw := hasTyTLiftPrefix (n := n) hcl
                [LocalDecl.assumption (policyPi (liftDomsT 0 1 doms) (foldApps (lift 0 inner (lift 0 1 M))
                  (idx.map (lift inner 1) ++ [foldApps (.bvar inner) (policyLocals inner)]))),
                 LocalDecl.assumption A] hM
              rw [motTyAt_lift] at hw
              exact ⟨by simpa only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] using hw⟩
            · intro j hj
              have hj' : j < ds.length := by rw [length_liftDomsT] at hj; exact hj
              obtain ⟨u, hu⟩ := hI1 (j + 1) (Nat.succ_lt_succ hj')
              rw [policyPrefixContext_cons_succ] at hu
              obtain ⟨hu⟩ := hu
              have hw := hasTyT_weakenUnderTel hcl ds j (Nat.le_of_lt hj') [LocalDecl.assumption ihT] hu
              simp only [List.length_singleton, List.singleton_append, lift] at hw
              refine ⟨u, ?_⟩
              rw [getElem_liftDomsT 1 ds 0 j hj', Nat.zero_add]
              exact ⟨hw⟩
            · intro j inner' hss
              obtain ⟨hj, doms2, idx2, h1, h2, h3, h4, h5⟩ := hI3 (j + 1) inner'
                (by rw [List.getElem?_cons_succ]; exact hss)
              have hj' : j < ds.length := Nat.lt_of_succ_lt_succ hj
              refine ⟨by rw [length_liftDomsT]; exact hj', liftDomsT j 1 doms2,
                idx2.map (lift (j + inner') 1), by rw [length_liftDomsT, h1],
                by rw [List.length_map, h2], h3, ?_, ?_⟩
              · rw [getElem_liftDomsT 1 ds 0 j hj', Nat.zero_add]
                have h4' : ds[j] = policyPi doms2 (foldApps (.const f ls)
                    (policyParameterLocals np (inner' + (j + 1) + d) ++ idx2)) := h4
                rw [h4', lift_policyPi, foldApps_lift, List.map_append, h1,
                  policyParameterLocals_lift_le np _ (j + inner') 1 (by omega)]
                simp only [lift, show inner' + (j + 1) + d + 1 = inner' + j + (d + 2) by omega]
              · obtain ⟨hw⟩ := h5
                rw [policyPrefixContext_cons_succ, ← policyPrefixContext_take ds j] at hw
                have hlt : (ds.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj')
                have hctx : policyPrefixContext doms2 inner' ++ (policyPrefixContext (ds.take j) j ++
                    (LocalDecl.assumption A :: Δ)) = policyPrefixContext (ds.take j ++ doms2) (j + inner') ++
                    (LocalDecl.assumption A :: Δ) := by
                  have hap := policyPrefixContext_append (ds.take j) doms2 inner'
                  rw [hlt] at hap
                  rw [hap, List.append_assoc]
                rw [hctx] at hw
                have hw' := argsTyT_weakenUnderTel hcl (ds.take j ++ doms2) (j + inner')
                  (by rw [List.length_append, hlt, h1]; exact Nat.le_refl _) [LocalDecl.assumption ihT] hw
                rw [List.length_singleton, liftDomsT_append, hlt, Nat.zero_add, ← liftDomsT_take,
                  idxTelAt_lift Is l _ (j + inner') 1 (by omega)] at hw'
                have hlt2 : ((liftDomsT 0 1 ds).take j).length = j := by
                  rw [List.length_take_of_le (by rw [length_liftDomsT]; exact Nat.le_of_lt hj')]
                have hctx2 : policyPrefixContext ((liftDomsT 0 1 ds).take j ++ liftDomsT j 1 doms2) (j + inner') =
                    policyPrefixContext (liftDomsT j 1 doms2) inner' ++ policyPrefixContext (liftDomsT 0 1 ds) j := by
                  have hap := policyPrefixContext_append ((liftDomsT 0 1 ds).take j) (liftDomsT j 1 doms2) inner'
                  rw [hlt2, policyPrefixContext_take] at hap
                  exact hap
                rw [hctx2, show inner' + (j + 1) + d + 1 = inner' + j + (d + 2) by omega] at hw'
                exact ⟨by simpa only [List.singleton_append, List.append_assoc, length_liftDomsT, h1] using hw'⟩

/-- **the minor builder, typed (forward, conv-aware).** The `.drecD` twin of
    `minorTyped_go`: each remaining recursive field carries a `RecFieldConvAtT`
    witness — the field's stored domain need only CONVERT to the analyzed
    `Π wdoms, I (P ++ widx)` form (the `DrecDTypedT` / whnf route), not be it
    syntactically.  `hΔ` is threaded for `endpoints3` (the conversion's endpoint
    typings, inside `hasTyT_ih_drecD`); `recFieldConvAtT_succ` shifts each
    witness past an emitted `.pi A (.pi ih ·)` pair. -/
private theorem minorTyped_go_conv {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hcl : EnvClosed E) (hSL : SubstLetT E n)
    (hconst : ConstsRightDataT E n) (fuel np f : Nat) (ls : List Level)
    (Is : List (Expr Nat)) (uM l : Level) (hf : transparentBody E f ls = none) :
    (ss : List FieldShape) → (Δ : LCtx) → CtxWfT E n Δ → (d : Nat) →
    (M acc : Expr Nat) → (ds : List (Expr Nat)) → (B R : Expr Nat) →
    ss.length = ds.length →
    Nonempty (HasTyT E n Δ M (motTyAt f ls np Is uM d)) →
    (∀ j (hj : j < ds.length), ∃ u,
      Nonempty (HasTyT E n (policyPrefixContext ds j ++ Δ) ds[j] (.sort u))) →
    (∀ j inner, ss[j]? = some (.recursive inner) →
      RecFieldConvAtT E n f ls np Is l fuel ds Δ d j inner) →
    minorFromTelescope E fuel np M acc ss (policyPi ds B) = some R →
    MinorTypedT E n uM Δ ss R
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, _, _, _, _, _, [], _, _, hlen, _, _, _, _ => (Nat.succ_ne_zero _ hlen).elim
  | .nonrecursive :: ss, Δ, hΔ, d, M, acc, A :: ds, B, R, hlen, hM, hI1, hI3, hmin => by
      simp only [policyPi, minorFromTelescope] at hmin
      cases hr : minorFromTelescope E fuel np (lift 0 1 M) (.app (lift 0 1 acc) (.bvar 0)) ss
          (policyPi ds B) with
      | none => rw [hr] at hmin; exact Option.noConfusion hmin
      | some R' =>
          rw [hr] at hmin
          injection hmin with hmin
          subst hmin
          refine ⟨?_, ?_⟩
          · obtain ⟨u, hu⟩ := hI1 0 (Nat.succ_pos _)
            exact ⟨u, by simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
              List.map_nil, List.nil_append] using hu⟩
          · obtain ⟨uA, ⟨hAty⟩⟩ := hI1 0 (Nat.succ_pos _)
            have hA0 : HasTyT E n Δ A (.sort uA) := by
              simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
                List.map_nil, List.nil_append] using hAty
            refine minorTyped_go_conv hW hcl hSL hconst fuel np f ls Is uM l hf ss
              (.assumption A :: Δ) (.assumption _ _ _ hΔ hA0) (d + 1) (lift 0 1 M) _
              ds B R' (Nat.succ.inj hlen) ?_ ?_ ?_ hr
            · obtain ⟨hM⟩ := hM
              have hw := hasTyTWeaken (LocalDecl.assumption A) hcl (c := 0) hM
              rw [insertAt_zero, motTyAt_lift] at hw
              exact ⟨hw⟩
            · intro j hj
              obtain ⟨u, hu⟩ := hI1 (j + 1) (Nat.succ_lt_succ hj)
              rw [policyPrefixContext_cons_succ] at hu
              exact ⟨u, hu⟩
            · -- the conv witness survives one plain binder: context reassociation,
              -- the `d ↦ d+1` shift is numeral arithmetic inside the analyzed spine
              intro j inner hss
              obtain ⟨hj, wdoms, widx, u', hdl, hil, hfu, hpit, hbc, hW1⟩ := hI3
                (j + 1) inner (by rw [List.getElem?_cons_succ]; exact hss)
              have harith : inner + (j + 1) + d + 1 = inner + j + (d + 1) + 1 := by omega
              refine ⟨Nat.lt_of_succ_lt_succ hj, wdoms, widx, u', hdl, hil, hfu, ?_, ?_, ?_⟩
              · rw [harith] at hpit
                exact hpit
              · obtain ⟨hbc⟩ := hbc
                rw [policyPrefixContext_cons_succ A ds j Δ, harith] at hbc
                exact ⟨hbc⟩
              · obtain ⟨hW1⟩ := hW1
                rw [policyPrefixContext_cons_succ A ds j Δ, harith] at hW1
                exact ⟨hW1⟩
  | .recursive inner :: ss, Δ, hΔ, d, M, acc, A :: ds, B, R, hlen, hM, hI1, hI3, hmin => by
      obtain ⟨_, wdoms, widx, u', hdl, hil, hfu, hpit, hbc, hW1⟩ :=
        hI3 0 inner List.getElem?_cons_zero
      -- `funIHType` reads `lift 0 1 A` — at `j = 0` the witness's `hpit` is exactly
      -- that read (the field binder `(A :: ds)[0]` reduces to `A` definitionally)
      have hpit0 : piTelescopeFuel E fuel (lift 0 1 A) = some (wdoms,
          foldApps (.const f ls)
            (policyParameterLocals np (inner + (d + 1)) ++ widx)) := hpit
      have hih : funIHType E fuel np A M inner = some (policyPi wdoms
          (foldApps (lift 0 inner (lift 0 1 M))
            (widx ++ [foldApps (.bvar inner) (policyLocals inner)]))) := by
        unfold funIHType
        rw [hpit0]
        simp only [hdl, ↓reduceIte,
          familyIdx_foldApps_const (policyParameterLocals_length np (inner + (d + 1)))]
        rfl
      let ihT := policyPi wdoms (foldApps (lift 0 inner (lift 0 1 M))
        (widx ++ [foldApps (.bvar inner) (policyLocals inner)]))
      simp only [policyPi, minorFromTelescope, hih] at hmin
      cases hr : minorFromTelescope E fuel np (lift 0 2 M) (.app (lift 0 2 acc) (.bvar 1)) ss
          (lift 0 1 (policyPi ds B)) with
      | none => rw [hr] at hmin; exact Option.noConfusion hmin
      | some R' =>
          rw [hr] at hmin
          injection hmin with hmin
          subst hmin
          obtain ⟨uA, ⟨hAty⟩⟩ := hI1 0 (Nat.succ_pos _)
          have hA0 : HasTyT E n Δ A (.sort uA) := by
            simpa only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
              List.nil_append] using hAty
          -- at `j = 0` the witness's `(A :: ds)[0]`/`policyPrefixContext _ 0` reduce
          -- to `A`/`[]` definitionally, and `inner + 0 + d + 1` to `inner + (d + 1)`
          have hih_res : ∃ lv : Fin inner → Level, Nonempty (HasTyT E n (.assumption A :: Δ)
              ihT (.sort (piSortT inner lv uM))) :=
            hasTyT_ih_drecD hW hcl hSL hconst hΔ A ⟨hA0⟩ f ls np Is uM l d
              wdoms widx inner hdl u' hbc hil hW1 M hM
          refine ⟨⟨uA, ⟨hA0⟩⟩, hih_res, ?_⟩
          obtain ⟨lv, ⟨hihT⟩⟩ := hih_res
          have hΔ' : CtxWfT E n (.assumption ihT :: .assumption A :: Δ) :=
            .assumption _ _ _ (.assumption _ _ _ hΔ hA0) hihT
          rw [lift_policyPi, Nat.zero_add] at hr
          refine minorTyped_go_conv hW hcl hSL hconst fuel np f ls Is uM l hf ss _ hΔ'
            (d + 2) (lift 0 2 M) _ (liftDomsT 0 1 ds) _ R'
            (by rw [length_liftDomsT]; exact Nat.succ.inj hlen) ?_ ?_ ?_ hr
          · obtain ⟨hM⟩ := hM
            have hw := hasTyTLiftPrefix (n := n) hcl
              [LocalDecl.assumption ihT, LocalDecl.assumption A] hM
            rw [motTyAt_lift] at hw
            exact ⟨by simpa only [List.length_cons, List.length_nil, List.cons_append,
              List.nil_append] using hw⟩
          · intro j hj
            have hj' : j < ds.length := by rw [length_liftDomsT] at hj; exact hj
            obtain ⟨u, hu⟩ := hI1 (j + 1) (Nat.succ_lt_succ hj')
            rw [policyPrefixContext_cons_succ] at hu
            obtain ⟨hu⟩ := hu
            have hw := hasTyT_weakenUnderTel hcl ds j (Nat.le_of_lt hj')
              [LocalDecl.assumption ihT] hu
            simp only [List.length_singleton, List.singleton_append, lift] at hw
            refine ⟨u, ?_⟩
            rw [getElem_liftDomsT 1 ds 0 j hj', Nat.zero_add]
            exact ⟨hw⟩
          · intro j inner' hss
            exact recFieldConvAtT_succ hcl ihT (hI3 (j + 1) inner'
              (by rw [List.getElem?_cons_succ]; exact hss))


/-! ## what admission's field analysis gives at a literal recursive field -/

/-- a successful telescope read needs enough bound: one head step per binder, plus two. -/
theorem piTelescopeFuel_some_lower (E : ResolvedEnv) :
    (fuel : Nat) → {e : Expr Nat} → {doms : List (Expr Nat)} → {body : Expr Nat} →
    piTelescopeFuel E fuel e = some (doms, body) → doms.length + 2 ≤ fuel
  | 0, _, _, _, h => by simp only [piTelescopeFuel] at h; exact Option.noConfusion h
  | fuel + 1, e, doms, body, h => by
      simp only [piTelescopeFuel] at h
      cases hw : whnfFuel E fuel e with
      | none => rw [hw] at h; exact Option.noConfusion h
      | some w =>
          cases fuel with
          | zero => simp only [whnfFuel] at hw; exact Option.noConfusion hw
          | succ fuel'' =>
          rw [hw] at h
          cases w with
          | pi A B =>
              simp only at h
              cases hr : piTelescopeFuel E (fuel'' + 1) B with
              | none => rw [hr] at h; exact Option.noConfusion h
              | some p =>
                  rw [hr] at h
                  obtain ⟨ds, b⟩ := p
                  injection h with h
                  injection h with h1 h2
                  subst h1 h2
                  have ih := piTelescopeFuel_some_lower E (fuel'' + 1) hr
                  simp only [List.length_cons]
                  omega
          | _ =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨h1, h2⟩ := h
              subst h1 h2
              show (0 : Nat) + 2 ≤ fuel'' + 1 + 1
              omega

/-- the fields' shape list has the fields' length. -/
theorem fieldShapesFuel_length (E : ResolvedEnv) {fuel fam nuniv nparams nindices depth : Nat} :
    (Ts : List (Expr Nat)) → {shapes : List FieldShape} →
    fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts = some shapes →
    shapes.length = Ts.length
  | [], _, h => by simp only [fieldShapesFuel] at h; injection h with h; subst h; rfl
  | T :: Ts, shapes, h => by
      simp only [fieldShapesFuel] at h
      cases ha : fieldAnalyze E fuel fam nuniv nparams nindices depth T with
      | permitted shape indices =>
          rw [ha] at h
          cases hr : fieldShapesFuel E fuel fam nuniv nparams nindices (depth + 1) Ts with
          | none => rw [hr] at h; exact Option.noConfusion h
          | some rest =>
              rw [hr] at h
              simp only [Option.map_some', Option.some.injEq] at h
              rw [← h, List.length_cons]
              exact congrArg Nat.succ (fieldShapesFuel_length E Ts hr)
      | _ => rw [ha] at h; exact Option.noConfusion h
/-- each field's analysis is the permitted verdict its shape records. -/
theorem fieldShapesFuel_getElem (E : ResolvedEnv) {fuel fam nuniv nparams nindices depth : Nat} :
    (Ts : List (Expr Nat)) → {shapes : List FieldShape} →
    fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts = some shapes →
    ∀ j (hj : j < shapes.length), ∃ (hjT : j < Ts.length) (idx : List (Expr Nat)),
      fieldAnalyze E fuel fam nuniv nparams nindices (depth + j) Ts[j] =
        .permitted shapes[j] idx
  | T :: Ts, shapes, h, j, hj => by
      simp only [fieldShapesFuel] at h
      cases ha : fieldAnalyze E fuel fam nuniv nparams nindices depth T with
      | permitted shape indices =>
          rw [ha] at h
          cases hr : fieldShapesFuel E fuel fam nuniv nparams nindices (depth + 1) Ts with
          | none => rw [hr] at h; exact Option.noConfusion h
          | some rest =>
              rw [hr] at h
              simp only [Option.map_some', Option.some.injEq] at h
              subst h
              have hlen := fieldShapesFuel_length E Ts hr
              cases j with
              | zero => exact ⟨Nat.zero_lt_succ _, _, ha⟩
              | succ j =>
                  have hj2 : j < rest.length := by
                    simp only [List.length_cons] at hj; omega
                  obtain ⟨hjT, idx, hjA⟩ := fieldShapesFuel_getElem E Ts hr j hj2
                  exact ⟨Nat.succ_lt_succ hjT, idx, by
                    rw [List.getElem_cons_succ]
                    have heq : depth + (j + 1) = depth + 1 + j := by omega
                    rw [heq]; exact hjA⟩
      | _ => rw [ha] at h; exact Option.noConfusion h

/-- the i-th entry checked by `exactParamLocals` is `bvar (top - i)`. -/
theorem exactParamLocals_getElem (xs : List (Expr Nat)) (top : Nat)
    (h : exactParamLocals xs top = true) :
    ∀ i (hi : i < xs.length), xs[i] = .bvar (top - i) := by
  induction xs generalizing top with
  | nil => intro i hi; simp only [List.length_nil, Nat.not_lt_zero] at hi
  | cons e es ih =>
      simp only [exactParamLocals, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨he, hrest⟩ := h
      subst he
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < es.length := by
            simp only [List.length_cons] at hi; omega
          have hge := ih (top - 1) hrest i hi'
          rw [List.getElem_cons_succ, hge]
          congr 1; omega

theorem exactParamLocals_eq_PL (xs : List (Expr Nat)) (top : Nat)
    (hlen : xs.length ≤ top + 1) (h : exactParamLocals xs top = true) :
    xs = policyParameterLocals xs.length (top + 1 - xs.length) := by
  apply List.ext_getElem
  · simp only [policyParameterLocals, List.length_map, List.length_reverse, List.length_range]
  · intro i hi1 hi2
    rw [exactParamLocals_getElem xs top h i hi1]
    simp only [policyParameterLocals, List.getElem_map]
    rw [List.getElem_reverse, List.getElem_range, List.length_range]
    show Expr.bvar (top - i) =
      Expr.bvar (xs.length - 1 - i + (top + 1 - xs.length))
    congr 1; omega

/-- `properFamilyFuel` positive: the body is the canonical saturated family application at `top`. -/
theorem properFamilyFuel_true {E : ResolvedEnv} {fuel fam nuniv nparams nindices top : Nat}
    {body : Expr Nat} (hnpt : nparams ≤ top + 1)
    (h : properFamilyFuel E fuel fam nuniv nparams nindices top body = some true) :
    ∃ ls args, body = foldApps (.const fam ls) args ∧ ls = (List.range nuniv).map Level.param ∧
      args.length = nparams + nindices ∧
      args.take nparams = policyParameterLocals nparams (top + 1 - nparams) := by
  have he := foldApps_appsSpine body
  simp only [properFamilyFuel] at h
  generalize hsp : appsSpine body = sp at h
  obtain ⟨hd, args⟩ := sp
  cases hd with
  | const r ls =>
      simp only at h
      split at h
      · rename_i hcond
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨hrf, harglen⟩, hexact⟩, hls⟩ := hcond
        revert h
        cases hc : indicesCleanFuel E fam fuel (args.drop nparams) with
        | none => intro h; exact Option.noConfusion h
        | some b =>
            cases b <;> intro h
            · refine ⟨ls, args, ?_, of_decide_eq_true hls, of_decide_eq_true harglen, ?_⟩
              · rw [← he, hsp]
                simp only [hrf]
              · have htake : (args.take nparams).length = nparams := by
                    rw [List.length_take, of_decide_eq_true harglen]
                    exact Nat.min_eq_left (Nat.le_add_right _ _)
                have hp := exactParamLocals_eq_PL (args.take nparams) top
                  (by rw [htake]; exact hnpt) hexact
                rw [htake] at hp
                exact hp
            · exact absurd h (by decide)
      · exact absurd h (by decide)
  | _ => simp only at h; exact absurd h (by decide)

/-- one literal `Expr.pi` layer costs one unit of bound; a direct rewrite avoids
    `simp` unfolding the inner call. -/
theorem piTelescopeFuel_cons_pi (E : ResolvedEnv) (f : Nat) (D B : Expr Nat) :
    piTelescopeFuel E (f + 1 + 1) (Expr.pi D B) =
      match piTelescopeFuel E (f + 1) B with
      | none => none
      | some (ds, b) => some (D :: ds, b) := by
  simp only [piTelescopeFuel]
  rw [show whnfFuel E (f + 1) (Expr.pi D B) = some (Expr.pi D B) from rfl]
  rfl

/-- a successful read of a literal `policyPi` telescope needs bound for every binder, plus two. -/
theorem piTelescopeFuel_policyPi_bound (E : ResolvedEnv) :
    (doms : List (Expr Nat)) → {f : Nat} → {B : Expr Nat} → {ds : List (Expr Nat)} →
    {b : Expr Nat} →
    piTelescopeFuel E f (policyPi doms B) = some (ds, b) → doms.length + 2 ≤ f
  | [], _, _, _, _, h => by
      have hb := piTelescopeFuel_some_lower E _ h
      simp only [List.length_nil]; omega
  | D :: doms, f, B, ds, b, h => by
      cases f with
      | zero => simp only [piTelescopeFuel] at h; exact Option.noConfusion h
      | succ f =>
          cases f with
          | zero =>
              simp only [piTelescopeFuel, whnfFuel] at h; exact Option.noConfusion h
          | succ f' =>
              rw [show policyPi (D :: doms) B = Expr.pi D (policyPi doms B) from rfl,
                piTelescopeFuel_cons_pi] at h
              revert h
              generalize hr : piTelescopeFuel E (f' + 1) (policyPi doms B) = r
              cases r <;> intro h
              · exact Option.noConfusion h
              · rename_i p
                obtain ⟨ds', b'⟩ := p
                simp only at h
                injection h with h2
                injection h2 with h3 h4
                subst h3 h4
                have ih := piTelescopeFuel_policyPi_bound E doms hr
                simp only [List.length_cons]; omega

/-- a recursive verdict at a literal field: the field's domains, levels and index arguments,
    with the parameters at their locals and the canonical level vector. -/
theorem fieldAnalyze_recursive_facts {E : ResolvedEnv} {fuel fam nuniv nparams nindices depth inner : Nat}
    {T : Expr Nat} {idxR doms args : List (Expr Nat)}
    (hf : transparentBody E fam ((List.range nuniv).map Level.param) = none)
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth T =
      .permitted (.recursive inner) idxR)
    (hsyn : T = policyPi doms
      (foldApps (.const fam ((List.range nuniv).map Level.param)) args))
    (hdepth : nparams ≤ depth) :
    doms.length = inner ∧ args.length = nparams + nindices ∧
      args.take nparams = policyParameterLocals nparams (inner + depth - 1 + 1 - nparams) ∧
      idxR = args.drop nparams ∧ inner + 3 ≤ fuel := by
  cases fuel with
  | zero => simp only [fieldAnalyze] at h; exact FieldAnalyze.noConfusion h
  | succ fuel' =>
      simp only [fieldAnalyze] at h
      revert h
      generalize hread : piTelescopeFuel E fuel' T = r
      cases r <;> intro h
      · simp only at h
        exact FieldAnalyze.noConfusion h
      · rename_i p
        obtain ⟨ds, body⟩ := p
        simp only at h
        revert h
        generalize hdc : domainsContainFuel E fam fuel' ds = r
        cases r <;> intro h
        · simp only at h
          exact FieldAnalyze.noConfusion h
        · rename_i b
          cases b <;> simp only at h
          · -- domainsContain = false → properFamilyFuel path
            revert h
            generalize hp : properFamilyFuel E fuel' fam nuniv nparams nindices
                (ds.length + depth - 1) body = r
            cases r <;> intro h
            · simp only at h
              exact FieldAnalyze.noConfusion h
            · rename_i b2
              cases b2 <;> simp only at h
              · -- properFamily = false → containsFamilyFuel path
                revert h
                generalize hc : containsFamilyFuel E fam fuel' T = r
                cases r <;> intro h
                · simp only at h
                  exact FieldAnalyze.noConfusion h
                · rename_i b3
                  cases b3 <;> simp only at h
                  · exact FieldAnalyze.noConfusion h
                      (fun h1 _ => FieldShape.noConfusion h1)
                  · revert h
                    generalize hsp : appsSpine body = sp
                    obtain ⟨hd, aargs⟩ := sp
                    intro h
                    cases hd <;> simp only at h
                    all_goals (first
                      | exact FieldAnalyze.noConfusion h
                      | exact FieldAnalyze.noConfusion h
                          (fun h1 _ => FieldShape.noConfusion h1)
                      | (split at h <;> (first
                          | exact FieldAnalyze.noConfusion h
                          | exact FieldAnalyze.noConfusion h
                              (fun h1 _ => FieldShape.noConfusion h1)
                          | (split at h <;> first
                              | exact FieldAnalyze.noConfusion h
                              | exact FieldAnalyze.noConfusion h
                                  (fun h1 _ => FieldShape.noConfusion h1)))))
              · -- properFamily = true → the recursive verdict
                injection h with h1 h2
                injection h1 with h1
                rw [hsyn] at hread
                have hbnd := piTelescopeFuel_policyPi_bound E doms hread
                have hsynread := piTelescopeFuel_policyPi_famApp hf doms args hbnd
                rw [hsynread] at hread
                injection hread with he
                injection he with h3 h4
                subst ds inner idxR body
                obtain ⟨ls', args', hbody, hls', hlen', hpar'⟩ :=
                  properFamilyFuel_true (by omega) hp
                have hpair : (Expr.const fam ((List.range nuniv).map Level.param), args) =
                    (Expr.const fam ls', args') := by
                  have hc := congrArg appsSpine hbody
                  simp only [appsSpine_foldApps_const] at hc
                  exact hc
                injection hpair with h5 h6
                injection h5 with h5a h5b
                subst args'
                have htake2 : (args.take nparams).length = nparams := by
                  rw [List.length_take]
                  exact Nat.min_eq_left (by omega)
                have hidx : familyIdx nparams
                    (foldApps (.const fam ((List.range nuniv).map Level.param)) args) =
                    args.drop nparams := by
                  have e := familyIdx_foldApps_const (r := fam)
                      (ls := (List.range nuniv).map Level.param)
                      (ps := args.take nparams) (idx := args.drop nparams) htake2
                  rwa [List.take_append_drop] at e
                exact ⟨rfl, hlen', hpar', hidx, by omega⟩
          · -- domainsContain = true → refused
            exact FieldAnalyze.noConfusion h

/-- a `.recursive` verdict at an ARBITRARY field (the `.drecD` reading, where the
    stored domain is not a literal `policyPi`): the analysis's own telescope
    output, its length, the canonical-body check, and the recorded indices. -/
theorem fieldAnalyze_recursive_out {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth inner : Nat} {T : Expr Nat}
    {idxR : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth T =
      .permitted (.recursive inner) idxR) :
    ∃ doms body, piTelescopeFuel E (fuel - 1) T = some (doms, body) ∧
      doms.length = inner ∧ idxR = familyIdx nparams body ∧
      properFamilyFuel E (fuel - 1) fam nuniv nparams nindices
        (doms.length + depth - 1) body = some true := by
  cases fuel with
  | zero => simp only [fieldAnalyze] at h; exact FieldAnalyze.noConfusion h
  | succ fuel' =>
      simp only [fieldAnalyze] at h
      cases hread : piTelescopeFuel E fuel' T with
      | none => simp [hread] at h
      | some p =>
          obtain ⟨ds, body⟩ := p
          simp only [hread] at h
          cases hdc : domainsContainFuel E fam fuel' ds with
          | none => simp [hdc] at h
          | some b =>
              simp only [hdc] at h
              cases b
              · cases hp : properFamilyFuel E fuel' fam nuniv nparams nindices
                    (ds.length + depth - 1) body with
                | none => simp [hp] at h
                | some b2 =>
                    simp only [hp] at h
                    cases b2
                    · -- properFamily = false → nonrecursive/refused paths only
                      cases hc : containsFamilyFuel E fam fuel' T with
                      | none => simp [hc] at h
                      | some b3 =>
                          simp only [hc] at h
                          cases b3
                          · exact FieldAnalyze.noConfusion h
                              (fun h1 _ => FieldShape.noConfusion h1)
                          · cases hsp : appsSpine body with
                            | mk hd aargs =>
                                simp only [hsp] at h
                                cases hd <;> simp only at h
                                all_goals (first
                                  | exact FieldAnalyze.noConfusion h
                                  | (split at h <;> (first
                                      | exact FieldAnalyze.noConfusion h
                                      | (split at h <;> exact
                                          FieldAnalyze.noConfusion h))))
                    · -- the recursive verdict
                      injection h with h1 h2
                      injection h1 with h1
                      exact ⟨ds, body, hread, h1, h2.symm, hp⟩
              · exact FieldAnalyze.noConfusion h

/-- an empty-telescope read is one `whnfFuel` step: the fuel is nonzero and the
    whnf is the returned body. -/
private theorem piTelescopeFuel_nil (E : ResolvedEnv) {fuel : Nat} {e w : Expr Nat}
    (h : piTelescopeFuel E fuel e = some ([], w)) :
    ∃ f, fuel = f + 1 ∧ whnfFuel E f e = some w := by
  cases fuel with
  | zero => simp only [piTelescopeFuel] at h; exact Option.noConfusion h
  | succ f =>
      refine ⟨f, rfl, ?_⟩
      simp only [piTelescopeFuel] at h
      revert h
      cases hw : whnfFuel E f e with
      | none => intro h; exact Option.noConfusion h
      | some w' =>
          intro h
          cases w' <;> simp only at h
          case pi A B =>
              revert h
              cases hp : piTelescopeFuel E f B with
              | none => intro h; simp only [hp] at h; exact Option.noConfusion h
              | some p =>
                  obtain ⟨ds', b'⟩ := p
                  intro h
                  simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
                  exact absurd h.1 (List.cons_ne_nil _ _)
          all_goals simp_all

/-- the `.drecD` analysis read, pushed through the emitted domain's lifts: the
    field's `piTelescopeFuel` verdict at `fuel₂ - 1` (an `inner = 0` read) and its
    canonical-body check together give, one binder under `lift j d ds₀`, the
    whnf'd canonical family application at the conv-cell's parameters depth. -/
private theorem drecD_pit {E : ResolvedEnv} (hcl : EnvClosed E)
    {fuel fuel₂ f np nuniv nindices j d : Nat} {ds₀ body : Expr Nat}
    (hpt : piTelescopeFuel E (fuel₂ - 1) ds₀ = some ([], body))
    (hproper : properFamilyFuel E (fuel₂ - 1) f nuniv np nindices
      (np + j - 1) body = some true)
    (hfuel : fuel₂ - 1 ≤ fuel) :
    ∃ widx, widx.length = nindices ∧
      piTelescopeFuel E fuel (lift 0 1 (lift j d ds₀)) =
        some ([], foldApps (.const f ((List.range nuniv).map Level.param))
          (policyParameterLocals np (j + d + 1) ++ widx)) ∧
      ∃ F, fuel = F + 1 ∧ whnfFuel E F (lift 0 1 (lift j d ds₀)) =
        some (foldApps (.const f ((List.range nuniv).map Level.param))
          (policyParameterLocals np (j + d + 1) ++ widx)) := by
  obtain ⟨ls', args, hbody, hls, harglen, htake⟩ :=
    properFamilyFuel_true (by show np ≤ np + j - 1 + 1; omega) hproper
  -- the lifted telescope read at fuel₂ - 1, then monotonicity to fuel
  have hpit : piTelescopeFuel E fuel (lift 0 1 (lift j d ds₀)) =
      some ([], foldApps (.const f ((List.range nuniv).map Level.param))
        (policyParameterLocals np (j + d + 1) ++
          (args.drop np).map (lift (j + 1) d ∘ lift 0 1))) := by
    have h1 := piTelescopeFuel_lift E hcl 0 1 (fuel₂ - 1) ds₀
    rw [hpt] at h1
    simp only [Option.map_some', List.mapIdx_nil, List.length_nil,
      Nat.add_zero, Nat.zero_add] at h1
    have h2 := piTelescopeFuel_lift E hcl (j + 1) d (fuel₂ - 1) (lift 0 1 ds₀)
    rw [h1] at h2
    simp only [Option.map_some', List.mapIdx_nil, List.length_nil,
      Nat.add_zero, Nat.zero_add] at h2
    have hswap : lift 0 1 (lift j d ds₀) = lift (j + 1) d (lift 0 1 ds₀) := by
      rw [lift_lift_permute 1 d j 0 (Nat.zero_le j), Nat.add_comm 1 j]
    rw [hswap]
    have hm := piTelescopeFuel_mono E hfuel h2
    rw [hm]
    congr 1
    generalize hidxB : args.drop np = idxB
    have hpi : policyParameterLocals np (np + j - 1 + 1 - np) =
        policyParameterLocals np j := by
      cases hpj : np + j with
      | zero =>
          have h0 : np = 0 := by omega
          rw [h0]
          rfl
      | succ _ => exact congrArg _ (by omega)
    have hargs : args = policyParameterLocals np j ++ idxB := by
      rw [← hpi, ← htake, ← hidxB, List.take_append_drop]
    rw [hbody, hls, hargs]
    simp only [foldApps_lift, lift, List.map_append]
    rw [policyParameterLocals_lift_le np j 0 1 (Nat.zero_le j)]
    rw [policyParameterLocals_lift_le np (j + 1) (j + 1) d (Nat.le_refl (j + 1)),
      show j + 1 + d = j + d + 1 from by omega, List.map_map]
  refine ⟨(args.drop np).map (lift (j + 1) d ∘ lift 0 1), ?_, hpit, ?_⟩
  · rw [List.length_map, List.length_drop, harglen]; omega
  · exact piTelescopeFuel_nil E hpit

/-- the `hI3` cell at a `.drecD` field position `j` — the conv path.  `D`'s
    whnf-analysis (`hpt`/`hproper`, through `drecD_pit`) supplies the analyzed
    family spine `widx` and the whnf-step for `hbc`; `DrecDTypedT`'s `TyConvT`
    (restricted to `E`, level-lifted, transported along the
    `ctorInsPairs ++ Δd ++ field-binder` insertion chain) supplies the conversion
    to the declared indices — `famAppConvInjT_scopeCheck` splits the spine
    conversion into the pointwise `widx ≡ idx`-transported evidence that
    `argsTyT_conv` consumes for `hW1`.  `hTm`/`hDoms`/`hΓΔ`/`hΓpre` are the
    `Type`-valued well-formedness data the conv transports need (`Nonempty`
    cannot eliminate into `Type`-valued `HasTyT`/`CtxWfT` goals). -/
private theorem recFieldConvAtT_drecD_at {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hP : hW.InScope) (hC : hW.ScopeCheck)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) (hcl : EnvClosed E)
    {f np : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (hres : E.members f = some fm) (hind : fm.mclass = .inductiveM)
    {res : List (Expr Nat)} {fuel fuel₂ : Nat} {body : Expr Nat}
    (fs : List FieldT) (hfs : FieldsTyT E fm.arity (fun k => lift 0 k fv.idxTel)
      (telCtxT fv.params) 0 fs res)
    (hnp : fv.params.length = np) (hdd : DrecDTypedT E f fm fv fs)
    (hn : fm.arity ≤ n) (Δd : LCtx)
    {j : Nat} {D : Expr Nat} {idx : List (Expr Nat)}
    (hj : j < fs.length) (hfj : fs[j] = .drecD D idx)
    (hpt : piTelescopeFuel E (fuel₂ - 1)
      ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
        rw [ctorEmittedDoms_length]; exact hj)) = some ([], body))
    (hproper : properFamilyFuel E (fuel₂ - 1) f fm.arity np
      (fv.indices.map Prod.fst).length (np + j - 1) body = some true)
    (hfuelf : fuel₂ - 1 ≤ fuel) (hfuel : 2 ≤ fuel)
    (hΓΔ : CtxWfT E n (Δd.reverse ++ telCtxT fv.params))
    (hΓpre : CtxWfT E n (plainCtxT (fs.take j) (telCtxT fv.params)))
    {lvD : Nat → Level}
    (hDoms : ∀ i (hi : i < (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).length),
      HasTyT E n (policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) i ++
          (Δd.reverse ++ telCtxT fv.params))
        ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[i]'hi)
        (.sort (lvD i))) :
    RecFieldConvAtT E n f (canonLevels fm.arity) np (fv.indices.map Prod.fst)
      fv.sort fuel
      (liftDomsT 0 Δd.length (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))
      (Δd.reverse ++ telCtxT fv.params) Δd.length j 0 := by
  have hlen : j < (liftDomsT 0 Δd.length
      (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).length := by
    rw [length_liftDomsT, ctorEmittedDoms_length]; exact hj
  have hlen0 : j < (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs).length := by
    rw [ctorEmittedDoms_length]; exact hj
  -- the analysis: `D`'s whnf yields the canonical family spine `widx`
  obtain ⟨widx, hwlen, hpit, F, hFe, hwhnf⟩ :=
    drecD_pit hcl (j := j) (d := Δd.length) (fuel := fuel) hpt hproper hfuelf
  have hget : lift j Δd.length
      ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'hlen0) =
      (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen := by
    rw [getElem_liftDomsT Δd.length _ 0 j hlen0, Nat.zero_add]
  rw [hget] at hpit hwhnf
  -- the declared index typing at the plain context (FieldsTyT data)
  have hfs' := fieldsTyT_levelMono hn hfs
  have hidx0 := fieldsTyT_drecDAt fs hfs' j
    (by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hj, hfj])
  simp only [Nat.zero_add] at hidx0
  have hidxT : ArgsTyT E n (plainCtxT (fs.take j) (telCtxT fv.params))
      (policyPi (liftDomsT 0 (plainIdxT (fs.take j) 0)
        (fv.indices.map Prod.fst)) (.sort fv.sort)) idx := by
    simpa only [FamViewT.idxTel, lift_policyPi, lift] using hidx0
  have hidxlen : idx.length = (fv.indices.map Prod.fst).length := by
    have := argsTyT_policyPi_sort_length _ _ _ rfl hidxT
    rwa [length_liftDomsT] at this
  -- the family application's typing at the plain ctx (the TyConvT endpoint)
  have hfa : HasTyT E n (plainCtxT (fs.take j) (telCtxT fv.params))
      (foldApps (.const f (canonLevels fm.arity))
        ((policyLocals fv.params.length).map (lift 0 (plainIdxT (fs.take j) 0)) ++
          idx)) (.sort fv.sort) := by
    have hpp : (policyLocals fv.params.length).map (lift 0 (plainIdxT (fs.take j) 0)) =
        policyParameterLocals np (plainIdxT (fs.take j) 0) := by
      rw [← hnp]
      show (policyParameterLocals fv.params.length 0).map
        (lift 0 (plainIdxT (fs.take j) 0)) = _
      rw [policyParameterLocals_lift_le fv.params.length 0 0
        (plainIdxT (fs.take j) 0) (Nat.zero_le _), Nat.zero_add]
    rw [hpp]
    exact famApp_typed_drec hcl hres (fs.take j) idx np (plainIdxT (fs.take j) 0)
      hnp hn rfl hidxlen hidxT
  -- the conversion evidence: TyConvT restricted, lifted, realized
  have hsplit : fs = fs.take j ++ .drecD D idx :: fs.drop (j + 1) := by
    have hd : fs.drop j = .drecD D idx :: fs.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj, hfj]
    rw [← hd]
    exact (List.take_append_drop j fs).symm
  obtain ⟨tc⟩ := (hdd (fs.take j) D idx (fs.drop (j + 1)) hsplit).2.1
  have tc' := tyConvT_levelMono hn (tyConvT_restrictExt hres tc)
  obtain ⟨c0⟩ := tyConvT_convT hW hP hSL hconst hΓpre tc' hfa
  -- the insertion chain's snds and its landing context Γ'ext
  have hsnd : (ctorInsPairs f (canonLevels fm.arity) np (fs.take j) 0 ++
      Δd.map (fun d => (d, j)) ++
      [(LocalDecl.assumption
        ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen),
        (0 : Nat))]).map Prod.snd =
      ctorInsCutoffs (fs.take j) ++ List.replicate Δd.length j ++ [0] := by
    rw [List.map_append, List.map_append, ctorInsPairs_snds]
    congr 1; congr 1
    rw [List.map_map]; exact List.map_const' Δd j
  have hctx : insertChain (ctorInsPairs f (canonLevels fm.arity) np (fs.take j) 0 ++
      Δd.map (fun d => (d, j)) ++
      [(LocalDecl.assumption ((liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen), 0)])
      (plainCtxT (fs.take j) (telCtxT fv.params)) =
      .assumption ((liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen) ::
        (policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
          (Δd.reverse ++ telCtxT fv.params)) := by
    rw [insertChain_append_one]
    have hctx' : insertChain (ctorInsPairs f (canonLevels fm.arity) np (fs.take j) 0 ++
        Δd.map (fun d => (d, j))) (plainCtxT (fs.take j) (telCtxT fv.params)) =
        policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
          (Δd.reverse ++ telCtxT fv.params) := by
      rw [insertChain_append, insertChain_ctorInsPairs]
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hXlen : (policyPrefixContext
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 (fs.take j)) j).length = j := by
        simp only [policyPrefixContext, List.length_map, List.length_reverse,
          List.length_take, List.length_mapIdx, Nat.min_eq_left (Nat.le_of_lt hj),
          ctorEmittedDoms_length, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj), Nat.min_self]
      have hmap : Δd.map (fun d => (d, j)) =
          Δd.map (fun d =>
            (d, (policyPrefixContext (ctorEmittedDoms f (canonLevels fm.arity) np 0
              (fs.take j)) j).length)) := by
        rw [hXlen]
      have hfull : policyPrefixContext (ctorEmittedDoms f (canonLevels fm.arity) np 0
          (fs.take j)) j =
          policyPrefixContext (ctorEmittedDoms f (canonLevels fm.arity) np 0
            (fs.take j)) (ctorEmittedDoms f (canonLevels fm.arity) np 0
              (fs.take j)).length := by
        rw [ctorEmittedDoms_length, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj)]
      rw [hmap, insertChain_boundary, hfull, liftDeclChainIter_ppc]
      rw [show (ctorEmittedDoms f (canonLevels fm.arity) np 0 (fs.take j)).length = j
        from by rw [ctorEmittedDoms_length, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj)]]
      rw [← ctorEmittedDoms_take]
      have hmi : ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs).take j).mapIdx
          (fun i D => lift i Δd.length D) =
          liftDomsT 0 Δd.length
            ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs).take j) := by
        rw [liftDomsT_eq_mapIdx]
        apply mapIdx_congr'
        intro i _
        rw [Nat.zero_add]
      rw [hmi, ← liftDomsT_take, ← policyPrefixContext_take', List.append_assoc]
    rw [hctx']
    rfl
  -- the ctx is well-formed (`Type`-valued, from hDoms)
  have hΓ' : CtxWfT E n (.assumption ((liftDomsT 0 Δd.length
      (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen) ::
      (policyPrefixContext (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
        (Δd.reverse ++ telCtxT fv.params))) := by
    have hΓd' : CtxWfT E n (policyPrefixContext (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
        (Δd.reverse ++ telCtxT fv.params)) := by
      have h0 := ctxWfT_of_doms (Γ := Δd.reverse ++ telCtxT fv.params) (lv := lvD) hΓΔ
        ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).take j) (fun k hk => by
          have hkj : k < j := by
            rw [List.length_take, length_liftDomsT, ctorEmittedDoms_length] at hk; omega
          have hppc' : policyPrefixContext (liftDomsT 0 Δd.length
                (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) k =
              policyPrefixContext ((liftDomsT 0 Δd.length
                (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).take j) k := by
            simp only [policyPrefixContext, List.take_take,
              Nat.min_eq_left (Nat.le_of_lt hkj)]
          have hge : ∀ (h' : k < (liftDomsT 0 Δd.length
              (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).length),
              (liftDomsT 0 Δd.length
                (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[k]'h' =
                ((liftDomsT 0 Δd.length
                  (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).take j)[k]'(by
                    rw [List.length_take, length_liftDomsT,
                      ctorEmittedDoms_length]; omega) := fun h' => by
            rw [List.getElem_take]
          have hstep := hDoms k (by
            rw [length_liftDomsT, ctorEmittedDoms_length]; omega)
          simp only [hppc', hge] at hstep
          exact hstep)
      simpa only [policyPrefixContext, List.take_length] using h0
    exact .assumption _ _ _ hΓd' (hDoms j hlen)
  -- `liftChain snds D` is `lift 0 1 ds'[j]`
  have hdom0 : liftChain (ctorInsCutoffs (fs.take j)) D =
      (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'hlen0 := by
    rw [ctorEmittedDoms_getElem_drecD f (canonLevels fm.arity) np 0 fs hj hfj,
      ← insCutoffs_map_ctorSkip, ← substT_ctorSub]
  have hR : plainIdxT (fs.take j) 0 + (ctorInsCutoffs (fs.take j)).length = j := by
    have hR := plainIdxT_add_ctorInsCutoffs_length (fs.take j)
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hR
    exact hR
  have hL : liftChain (ctorInsCutoffs (fs.take j) ++ List.replicate Δd.length j ++ [0])
        D = lift 0 1 ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen) := by
    rw [liftChain_append, liftChain_append, liftChain_replicate]
    show lift 0 1 (lift j Δd.length (liftChain (ctorInsCutoffs (fs.take j)) D)) = _
    rw [hdom0, ← hget]
  -- `liftChain snds famApp'` is the family app at the declared indices
  have hRfam : liftChain (ctorInsCutoffs (fs.take j) ++ List.replicate Δd.length j ++ [0])
        (foldApps (.const f (canonLevels fm.arity))
          ((policyLocals fv.params.length).map (lift 0 (plainIdxT (fs.take j) 0)) ++
            idx)) =
      foldApps (.const f (canonLevels fm.arity))
        (policyParameterLocals np (j + Δd.length + 1) ++
          idx.map (liftChain (ctorInsCutoffs (fs.take j) ++
            List.replicate Δd.length j ++ [0]))) := by
    rw [liftChain_append, liftChain_append, liftChain_replicate]
    show lift 0 1 (lift j Δd.length (liftChain (ctorInsCutoffs (fs.take j))
      (foldApps (.const f (canonLevels fm.arity))
        ((policyLocals fv.params.length).map (lift 0 (plainIdxT (fs.take j) 0)) ++
          idx)))) = _
    rw [← insCutoffs_map_ctorSkip, ← substT_ctorSub, substT_foldApps,
      List.map_append]
    have hpp' : ((policyLocals fv.params.length).map (lift 0 (plainIdxT (fs.take j) 0))).map
        (substT (ctorSub ((fs.take j).map FieldT.ctorSkip))) =
        policyParameterLocals np j := by
      rw [show (policyLocals fv.params.length).map (lift 0 (plainIdxT (fs.take j) 0)) =
          policyParameterLocals np (plainIdxT (fs.take j) 0) from by
        rw [← hnp]
        show (policyParameterLocals fv.params.length 0).map
          (lift 0 (plainIdxT (fs.take j) 0)) = _
        rw [policyParameterLocals_lift_le fv.params.length 0 0
          (plainIdxT (fs.take j) 0) (Nat.zero_le _), Nat.zero_add]]
      rw [map_policyParameterLocals_ctorSub np _ (fs.take j) (fun i hi => by
        have := ctorInsCutoffs_le (fs.take j) i hi; omega), hR]
    rw [hpp', show substT (ctorSub ((fs.take j).map FieldT.ctorSkip))
        (.const f (canonLevels fm.arity)) = .const f (canonLevels fm.arity) from rfl]
    rw [foldApps_lift, List.map_append, List.map_map,
      show lift j Δd.length (.const f (canonLevels fm.arity)) =
        .const f (canonLevels fm.arity) from rfl,
      policyParameterLocals_lift_le np j j Δd.length (Nat.le_refl _)]
    rw [foldApps_lift, List.map_append, List.map_map,
      show lift 0 1 (.const f (canonLevels fm.arity)) =
        .const f (canonLevels fm.arity) from rfl,
      policyParameterLocals_lift_le np (j + Δd.length) 0 1 (Nat.zero_le _)]
    congr 1; congr 1
    apply List.map_congr_left
    intro x _
    rw [liftChain_append, liftChain_append, liftChain_replicate,
      ← substT_ctorSub]
    rfl
  -- the transported conversion: `lift 0 1 ds'[j] ≡ F (ppL ++ args₃)` at `sort fv.sort`
  have cTr : ConvT E n (.assumption ((liftDomsT 0 Δd.length
      (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen) ::
      (policyPrefixContext (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
        (Δd.reverse ++ telCtxT fv.params)))
      (lift 0 1 ((liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen))
      (foldApps (.const f (canonLevels fm.arity))
        (policyParameterLocals np (j + Δd.length + 1) ++
          idx.map (liftChain (ctorInsCutoffs (fs.take j) ++
            List.replicate Δd.length j ++ [0]))))
      (.sort fv.sort) := by
    have cw := convT_liftChain hcl
      (ctorInsPairs f (canonLevels fm.arity) np (fs.take j) 0 ++
        Δd.map (fun d => (d, j)) ++
        [(LocalDecl.assumption ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen), 0)])
      (plainCtxT (fs.take j) (telCtxT fv.params)) _ _ _ c0
    rw [hsnd, hctx, liftChain_closed (.sort fv.sort) (fun _ => rfl) _] at cw
    rw [hL, hRfam] at cw
    exact cw
  -- the whnf conversion `lift 0 1 ds'[j] ≡ F (ppL ++ widx)` at the same sort
  obtain ⟨htyL, _, _⟩ := endpoints3_of_envWfT hW hSL hconst hΓ' cTr
  obtain ⟨cW⟩ := whnfFuel_convT hW hP hΓ' F hwhnf htyL
  refine ⟨hlen, [], widx, fv.sort, rfl, hwlen, ?_, ?_, ?_, ?_⟩
  · exact hfuel
  · simpa only [Nat.zero_add, canonLevels] using hpit
  · exact ⟨by
      simpa only [policyPi, Nat.zero_add, canonLevels] using cW⟩
  · -- hW1: `widx`'s typing, paid per-argument.  The FLIPPED whole-application
    --   conversion `famAppW ≡ F (ppL ++ args₃)` feeds `famAppConvInjT_scopeCheck`,
    --   whose `ConvArgsT` walks the LEFT (widx) spine: `convArgsT_getElem` at
    --   `np + k` hands back `widx[k] ≡ args₃[k]` at the `widx`-prefixed
    --   instantiated domain, and `endpoints3` then types `widx[k]` at exactly
    --   the domain `argsTyT_mk_ne` consumes — no cross-spine domain transport
    --   (`convT_instPrefix`) is needed, and every `Nonempty` elimination stays
    --   inside `Prop`-valued goals.
    have hpdomlen : (fv.params.map Prod.fst).length = np := by
      rw [List.length_map, hnp]
    -- index domains are closed under lift past the parameter boundary
    have hbndI : ∀ k (hk : k < (fv.indices.map Prod.fst).length),
        lift (k + np) 1 ((fv.indices.map Prod.fst)[k]'hk) =
          (fv.indices.map Prod.fst)[k] := by
      intro k hk
      have hd0 := (hcl f fm hres).1 0
      rw [fv.stored, List.map_append, lift_policyPi, Nat.zero_add] at hd0
      have hdoms0 : liftDomsT 0 1
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst) =
          fv.params.map Prod.fst ++ fv.indices.map Prod.fst :=
        policyPi_sort_inj _ _ _ _ hd0
      have hge := getElem_liftDomsT 1
        (fv.params.map Prod.fst ++ fv.indices.map Prod.fst) 0 (np + k)
        (by rw [List.length_append, hpdomlen]; omega)
      simp only [hdoms0] at hge
      rw [Nat.zero_add] at hge
      have hx : ∀ (h : np + k <
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst).length),
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)[np + k]'h =
            (fv.indices.map Prod.fst)[k]'hk := fun h => by
        rw [List.getElem_append_right (by rw [hpdomlen]; omega)]
        simp only [hpdomlen, Nat.add_sub_cancel_left]
      simp only [hx] at hge
      rw [Nat.add_comm k np]
      exact hge.symm
    -- the flipped conversion `F (ppL ++ widx) ≡ F (ppL ++ args₃)` at the sort
    have cArgR : ConvT E n (.assumption ((liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen) ::
        (policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
          (Δd.reverse ++ telCtxT fv.params)))
        (foldApps (.const f (canonLevels fm.arity))
          (policyParameterLocals np (j + Δd.length + 1) ++ widx))
        (foldApps (.const f (canonLevels fm.arity))
          (policyParameterLocals np (j + Δd.length + 1) ++
            idx.map (liftChain (ctorInsCutoffs (fs.take j) ++
              List.replicate Δd.length j ++ [0]))))
        (.sort fv.sort) := .trans _ _ _ _ _ (.symm _ _ _ _ cW) cTr
    obtain ⟨_, _, hspine⟩ := famAppConvInjT_scopeCheck hW hC hΓ' hres hind cArgR
    have hT' : instantiateLevels (canonLevels fm.arity) fm.mtype =
        policyPi (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)
          (.sort fv.sort) := by
      rw [instantiateLevels_canon, fv.stored, List.map_append]
    rw [hT'] at hspine
    have hwl : widx.length = (liftDomsT 0 (j + Δd.length + 1)
        (fv.indices.map Prod.fst)).length := by
      rw [length_liftDomsT]; exact hwlen
    have key : ∀ k (hk : k < widx.length), Nonempty (HasTyT E n
        (.assumption ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[j]'hlen) ::
          (policyPrefixContext (liftDomsT 0 Δd.length
            (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) j ++
            (Δd.reverse ++ telCtxT fv.params)))
        (widx[k]'hk)
        (instPrefix (widx.take k)
          ((liftDomsT 0 (j + Δd.length + 1) (fv.indices.map Prod.fst))[k]'
            (by rw [length_liftDomsT]; rw [hwlen] at hk; exact hk)))) := by
      intro k hk
      have hkI : k < (fv.indices.map Prod.fst).length := by
        rw [hwlen] at hk; exact hk
      have hnpk : np + k <
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst).length := by
        rw [List.length_append, hpdomlen]; omega
      have hxlen : (policyParameterLocals np (j + Δd.length + 1) ++ widx).length =
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst).length := by
        rw [List.length_append, List.length_append,
          policyParameterLocals_length, List.length_map, hwlen, hnp]
      obtain ⟨ck⟩ := convArgsT_getElem
        (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)
        (policyParameterLocals np (j + Δd.length + 1) ++ widx)
        hxlen _ rfl hspine (np + k) (by rw [hxlen]; exact hnpk)
      -- `endpoints3` types the left endpoint at its prefix-instantiated domain;
      -- the position/domain normalizations rewrite it into `widx`-indexed form
      have hty := (endpoints3_of_envWfT hW hSL hconst hΓ' ck).1
      have hlft : ∀ (h : np + k <
          (policyParameterLocals np (j + Δd.length + 1) ++ widx).length),
          (policyParameterLocals np (j + Δd.length + 1) ++ widx)[np + k]'h =
            widx[k]'hk := fun h => by
        rw [List.getElem_append_right
          (by rw [policyParameterLocals_length]; omega)]
        simp only [policyParameterLocals_length, Nat.add_sub_cancel_left]
      have hdme : ∀ (h : np + k <
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst).length),
          (fv.params.map Prod.fst ++ fv.indices.map Prod.fst)[np + k]'h =
            (fv.indices.map Prod.fst)[k]'hkI := fun h => by
        rw [List.getElem_append_right (by rw [hpdomlen]; omega)]
        simp only [hpdomlen, Nat.add_sub_cancel_left]
      have htk : (policyParameterLocals np (j + Δd.length + 1) ++ widx).take
          (np + k) =
          policyParameterLocals np (j + Δd.length + 1) ++ widx.take k := by
        rw [List.take_append_eq_append_take, policyParameterLocals_length,
          List.take_of_length_le
            (by rw [policyParameterLocals_length]; omega),
          Nat.add_sub_cancel_left]
      have htklen : (widx.take k).length = k := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
      have hid : lift k (j + Δd.length + 1) ((fv.indices.map Prod.fst)[k]'hkI) =
          (liftDomsT 0 (j + Δd.length + 1) (fv.indices.map Prod.fst))[k]'(by
            rw [length_liftDomsT]; exact hkI) := by
        rw [getElem_liftDomsT (j + Δd.length + 1) _ 0 k hkI, Nat.zero_add]
      simp only [hlft, htk, hdme] at hty
      simp only [instPrefix_append_instTelK, htklen,
        ← descSpine_eq_ppL (j + Δd.length + 1) np,
        instTelK_descSpine k (j + Δd.length + 1) np _ (hbndI k hkI),
        hid] at hty
      exact ⟨hty⟩
    obtain ⟨hmk⟩ := argsTyT_mk_ne (l := fv.sort)
      (liftDomsT 0 (j + Δd.length + 1) (fv.indices.map Prod.fst)) widx hwl key
    exact ⟨by
      simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
        List.map_nil, List.nil_append, Nat.zero_add, idxTelAt] using hmk⟩


/-- the `hI3` dispatcher with `.drecD` admitted: a `.drec` field is a syntactic
    recursive field — `recFieldAtT_drec_at` + `recFieldAtT_toConv` — while a
    `.drecD` field goes through `recFieldConvAtT_drecD_at`, whose conversion
    evidence comes from `DrecDTypedT` and whose analysis (`han`, discharged from
    `fieldShapesFuel` on the views at the cell) supplies the canonical spine.
    `hΓΔ`/`hΓpre`/`hDoms` are the `Type`-valued well-formedness data the conv
    transports consume — `Nonempty` cannot eliminate into `CtxWfT`/`HasTyT`
    goals, so they cannot be sourced from `hdd` here. -/
private theorem hI3_conv_at {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hP : hW.InScope) (hC : hW.ScopeCheck)
    (hcl : EnvClosed E) (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n)
    {f np : Nat} {fm : CheckedMember} {fv : FamViewT fm}
    (hres : E.members f = some fm) (hind : fm.mclass = .inductiveM)
    {res : List (Expr Nat)} {fuel fuel₂ : Nat}
    (fs : List FieldT)
    (hfs : FieldsTyT E fm.arity (fun k => lift 0 k fv.idxTel) (telCtxT fv.params)
      0 fs res)
    (hnp : fv.params.length = np) (hdd : DrecDTypedT E f fm fv fs)
    (hn : fm.arity ≤ n) (hfuel : 2 ≤ fuel) (hfuelf : fuel₂ - 1 ≤ fuel)
    (hf : transparentBody E f (canonLevels fm.arity) = none)
    (Δd : LCtx) (hΓΔ : CtxWfT E n (Δd.reverse ++ telCtxT fv.params))
    (hΓpre : ∀ j, CtxWfT E n (plainCtxT (fs.take j) (telCtxT fv.params)))
    {lvD : Nat → Level}
    (hDoms : ∀ i (hi : i < (liftDomsT 0 Δd.length
        (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)).length),
      HasTyT E n (policyPrefixContext (liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)) i ++
          (Δd.reverse ++ telCtxT fv.params))
        ((liftDomsT 0 Δd.length
          (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))[i]'hi)
        (.sort (lvD i)))
    (han : ∀ j (hj : j < fs.length) {D : Expr Nat} {idx : List (Expr Nat)},
        fs[j] = .drecD D idx →
      ∃ body : Expr Nat,
        piTelescopeFuel E (fuel₂ - 1)
          ((ctorEmittedDoms f (canonLevels fm.arity) np 0 fs)[j]'(by
            rw [ctorEmittedDoms_length]; exact hj)) = some ([], body) ∧
        properFamilyFuel E (fuel₂ - 1) f fm.arity np
          (fv.indices.map Prod.fst).length (np + j - 1) body = some true) :
    ∀ j inner, (fs.map FieldT.shapeT)[j]? = some (.recursive inner) →
      RecFieldConvAtT E n f (canonLevels fm.arity) np (fv.indices.map Prod.fst)
        fv.sort fuel
        (liftDomsT 0 Δd.length (ctorEmittedDoms f (canonLevels fm.arity) np 0 fs))
        (Δd.reverse ++ telCtxT fv.params) Δd.length j inner := by
  intro j inner hj
  rw [List.getElem?_map] at hj
  cases hfj : fs[j]? with
  | none => rw [hfj] at hj; exact Option.noConfusion hj
  | some fj =>
      rw [hfj] at hj
      obtain ⟨hjlt, hfj'⟩ := List.getElem?_eq_some_iff.mp hfj
      cases fj with
      | plain D u =>
          simp only [FieldT.shapeT, Option.map, Option.some.injEq] at hj
          exact FieldShape.noConfusion hj
      | drec idx =>
          simp only [FieldT.shapeT, Option.map, Option.some.injEq] at hj
          obtain ⟨rfl⟩ := hj
          have hfs' := fieldsTyT_levelMono hn hfs
          have hidx := fieldsTyT_drecAt fs hfs' j
            (by rw [List.get?_eq_getElem?]; exact hfj)
          have hX : fv.idxTel = idxTelAt (fv.indices.map Prod.fst) fv.sort 0 := by
            show fv.idxTel = policyPi (liftDomsT 0 0 (fv.indices.map Prod.fst))
              (.sort fv.sort)
            rw [liftDomsT_zero]
            rfl
          have hil : idx.length = (fv.indices.map Prod.fst).length := by
            simp only [Nat.zero_add] at hidx
            rw [hX, idxTelAt_lift (fv.indices.map Prod.fst) fv.sort 0 0
              (plainIdxT (fs.take j) 0) (Nat.le_refl 0), Nat.zero_add] at hidx
            have := argsTyT_policyPi_sort_length _ _ _ rfl hidx
            rw [length_liftDomsT] at this
            exact this
          have hAt := recFieldAtT_drec_at (f := f) (np := np)
            (ls := canonLevels fm.arity) hcl fs hfs' hjlt hfj' hX hil hfuel Δd
          exact recFieldAtT_toConv hcl hf hAt (fun i hi => ⟨lvD i, ⟨hDoms i hi⟩⟩)
      | drecD D idx =>
          simp only [FieldT.shapeT, Option.map, Option.some.injEq] at hj
          obtain ⟨rfl⟩ := hj
          obtain ⟨body, hpt, hproper⟩ := han j hjlt hfj'
          exact recFieldConvAtT_drecD_at hW hP hC hSL hconst hcl hres hind fs
            hfs hnp hdd hn Δd hjlt hfj' hpt hproper hfuelf hfuel hΓΔ (hΓpre j)
            hDoms


/-! ## the cell: `minorTyped_go` at an admitted constructor, under `NoDrecDT` -/

/-- the `minorTyped_go` call at an admitted constructor's cell, under the named
    `NoDrecDT` remainder.  The context is the recursor's minor context `minorCtxT`:
    `Δd` (the motive over the earlier minors) reversed in front of the parameter
    context `telCtxT fv.params`.  `hI1`/`hI3` come off the views' `FieldsTyT`
    through `hI1_fieldsT_at`/`hI3_drec_at`; `hmin` is `minorFromTelescope_ctorFieldsT`
    moved into `policyPi ds B` form by `ctorDomsT_eq_emitted_lift`. -/
private theorem minorTyped_at_cell {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (hcl : EnvClosed E) {fv : FamViewT a.family.member}
    {fs : List FieldT} {res : List (Expr Nat)} {fuel : Nat}
    (hfs : FieldsTyT E a.family.member.arity (fun k => lift 0 k fv.idxTel)
      (telCtxT fv.params) 0 fs res)
    (hpar : a.family.parameters = fv.params.map Prod.fst)
    (hidx : a.family.indices = fv.indices.map Prod.fst)
    (hnd : NoDrecDT fs) (hfuel : 2 ≤ fuel) :
    MinorTypedT E m.arity (policyMotiveLevel a.family.member.arity a.policy)
      (minorCtxT a i.val) (fs.map FieldT.shapeT)
      (minorFieldsT a.family.ref (a.family.ref + 1 + i.val)
        (canonLevels a.family.member.arity)
        (policyParameterLocals a.family.parameters.length (1 + i.val)) (.bvar i.val) []
        (fun j => lift 0 (1 + i.val) (SubstT.id j)) fs res) := by
  -- the cell runs at the recursor member's arity: `AnySort` admits one motive
  -- level over the family's (05 §11); the field typings lift.
  have har : a.family.member.arity ≤ m.arity := by
    rw [a.recursorArity]
    cases a.policy <;> simp only [policyRecursorArity] <;> omega
  have hfs' := fieldsTyT_levelMono har hfs
  obtain ⟨Δd, hΔd⟩ : ∃ Δd : LCtx, Δd =
      LocalDecl.assumption (policyMotiveType a.family a.policy) ::
        (policyPrefixContext a.minorTypes i.val).reverse := ⟨_, rfl⟩
  have hm : i.val ≤ a.minorTypes.length := by
    rw [a.minorCount]; omega
  have hd : Δd.length = 1 + i.val := by
    rw [hΔd, List.length_cons, List.length_reverse]
    simp only [policyPrefixContext, List.length_map, List.length_reverse,
      List.length_take]
    rw [Nat.min_eq_left hm]
    omega
  -- Δd.reverse ++ Γp is the prefix form of the minor context
  have hrev : Δd.reverse ++ telCtxT fv.params =
      policyPrefixContext a.minorTypes i.val ++
        (.assumption (policyMotiveType a.family a.policy) :: telCtxT fv.params) := by
    rw [hΔd, List.reverse_cons, List.reverse_reverse, List.append_assoc]
    rfl
  have hctx : Δd.reverse ++ telCtxT fv.params = minorCtxT a i.val := by
    rw [hrev]
    show _ = policyPrefixContext a.minorTypes i.val ++
      (.assumption (policyMotiveType a.family a.policy) ::
        (policyPrefixContext a.family.parameters a.family.parameters.length ++ []))
    rw [hpar, List.length_map, policyPrefixContext_telCtxT, List.append_nil]
  have hnp : fv.params.length = a.family.parameters.length := by
    rw [hpar, List.length_map]
  have hnp' : a.family.parameters.length = fv.params.length := hnp.symm
  -- the motive: policyMotiveType is motTyT is motTyAt at distance 0
  have hMot : policyMotiveType a.family a.policy =
      motTyAt a.family.ref (canonLevels a.family.member.arity) a.family.parameters.length
        (fv.indices.map Prod.fst) (policyMotiveLevel a.family.member.arity a.policy) 0 := by
    rw [policyMotiveType_eq a.family (ls := canonLevels a.family.member.arity) a.policy
      rfl rfl hpar hidx, ← motTyAt_eq_motTyT, ← hnp']
  have hM : Nonempty (HasTyT E m.arity
      (Δd.reverse ++ telCtxT fv.params) (.bvar i.val)
      (motTyAt a.family.ref (canonLevels a.family.member.arity) a.family.parameters.length
        (fv.indices.map Prod.fst) (policyMotiveLevel a.family.member.arity a.policy)
        Δd.length)) := by
    have h0 : Nonempty (HasTyT E m.arity
        (policyPrefixContext a.minorTypes i.val ++
          (.assumption (policyMotiveType a.family a.policy) :: telCtxT fv.params))
        (.bvar i.val)
        (motTyAt a.family.ref (canonLevels a.family.member.arity) a.family.parameters.length
          (fv.indices.map Prod.fst) (policyMotiveLevel a.family.member.arity a.policy)
          (0 + i.val + 1))) := hM_minCtx a.minorTypes hm
        (policyMotiveType a.family a.policy) (telCtxT fv.params) hMot
    rw [hrev, hd]
    have hs : (0 + i.val + 1) = 1 + i.val := by omega
    rw [← hs]
    exact h0
  -- hI1: the lifted emitted domains, typed at the lifted prefix
  have hI1 := hI1_fieldsT_at (f := a.family.ref) (np := a.family.parameters.length)
    hcl a.family.present fs hfs rfl hnp hnd har Δd
  -- hI3: the recursive fields under NoDrecDT
  have hX3 : fv.idxTel = idxTelAt (fv.indices.map Prod.fst) fv.sort 0 := by
    show fv.idxTel = policyPi (liftDomsT 0 0 (fv.indices.map Prod.fst)) (.sort fv.sort)
    rw [liftDomsT_zero]
    rfl
  have hI3 := hI3_drec_at (f := a.family.ref) (np := a.family.parameters.length)
    (ls := canonLevels a.family.member.arity) hcl fs hfs' hX3 hnd hfuel Δd
  have hf : transparentBody E a.family.ref (canonLevels a.family.member.arity) = none :=
    transparentBody_family a.family _
  have hlen : (fs.map FieldT.shapeT).length =
      (liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
        (canonLevels a.family.member.arity) a.family.parameters.length 0 fs)).length := by
    rw [List.length_map, length_liftDomsT, ctorEmittedDoms_length]
  -- hmin: the admission-derived minor read off the views' telescope
  have hds : ctorDomsT a.family.ref (canonLevels a.family.member.arity)
      (policyParameterLocals a.family.parameters.length Δd.length)
      (fun j => lift 0 Δd.length (SubstT.id j)) fs =
      liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
        (canonLevels a.family.member.arity) a.family.parameters.length 0 fs) := by
    have h := ctorDomsT_eq_emitted_lift a.family.ref (canonLevels a.family.member.arity)
      a.family.parameters.length 0 Δd.length fs
    rwa [Nat.zero_add] at h
  have hpi : ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
      (policyParameterLocals a.family.parameters.length Δd.length)
      (fun j => lift 0 Δd.length (SubstT.id j)) fs res =
      policyPi (liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
        (canonLevels a.family.member.arity) a.family.parameters.length 0 fs))
        (foldApps (.const a.family.ref (canonLevels a.family.member.arity))
          ((policyParameterLocals a.family.parameters.length Δd.length).map
            (lift 0 fs.length) ++
            res.map (substT (ctorEndSubstT (fun j => lift 0 Δd.length (SubstT.id j)) fs)))) := by
    rw [ctorFieldsT_policyPi, hds]
  have hmin0 := minorFromTelescope_ctorFieldsT a.family.ref (a.family.ref + 1 + i.val)
    (canonLevels a.family.member.arity) a.family.parameters.length res hf hfuel fs
    (noDrecDT_isDrecD hnd)
    (policyParameterLocals a.family.parameters.length Δd.length)
    (policyParameterLocals_length _ _) (.bvar i.val) []
    (fun j => lift 0 Δd.length (SubstT.id j))
  rw [List.append_nil, hpi] at hmin0
  have gores := minorTyped_go hcl fuel a.family.parameters.length a.family.ref
    (canonLevels a.family.member.arity) (fv.indices.map Prod.fst)
    (policyMotiveLevel a.family.member.arity a.policy) fv.sort hf
    (fs.map FieldT.shapeT) (Δd.reverse ++ telCtxT fv.params) Δd.length (.bvar i.val)
    (foldApps (.const (a.family.ref + 1 + i.val) (canonLevels a.family.member.arity))
      (policyParameterLocals a.family.parameters.length Δd.length))
    (liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
      (canonLevels a.family.member.arity) a.family.parameters.length 0 fs))
    (foldApps (.const a.family.ref (canonLevels a.family.member.arity))
      ((policyParameterLocals a.family.parameters.length Δd.length).map
        (lift 0 fs.length) ++
        res.map (substT (ctorEndSubstT (fun j => lift 0 Δd.length (SubstT.id j)) fs))))
    (minorFieldsT a.family.ref (a.family.ref + 1 + i.val)
      (canonLevels a.family.member.arity)
      (policyParameterLocals a.family.parameters.length Δd.length) (.bvar i.val) []
      (fun j => lift 0 Δd.length (SubstT.id j)) fs res)
    hlen hM hI1 hI3 hmin0
  rw [hctx, hd] at gores
  exact gores

/-- the conversion-aware cell: `minorTyped_go_conv` at an admitted constructor, dropping
    `NoDrecDT`.  `.drecD` fields' witnesses come from `hI3_conv_at` — `DrecDTypedT`'s
    admitted conversion plus the shape analysis `hsh` (through `fieldShapesFuel_getElem`
    and `fieldAnalyze_recursive_out`, bridged to the emitted domains by `htel`); `.drec`
    fields take the syntactic route through `recFieldAtT_toConv`.  `hmin` is a hypothesis
    rather than `minorFromTelescope_ctorFieldsT`: a `.drecD` field's `funIHType` records
    the ANALYZED indices `widx`, not the declared `idx`, so the walked `R` is not the
    `minorFieldsT` expression — `MinorPremisesMatch`/`derivedMinor` tie `R` to the stored
    minor at the consumer.  `hΓmin`/`hΓpre`/`hDoms`/`hΔ` are the Type-valued context debts
    the checker-paid route (`MinorDomainsTyped` + pins) supplies: `Nonempty` evidence in
    `DrecDTypedT`/`hI1` cannot manufacture `CtxWfT`/`HasTyT`. -/
private theorem minorTyped_at_cell_conv {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (hW : EnvWfT E) (hP : hW.InScope) (hC : hW.ScopeCheck)
    (hcl : EnvClosed E) (hSL : SubstLetT E m.arity)
    (hconst : ConstsRightDataT E m.arity)
    {fv : FamViewT a.family.member}
    {fs : List FieldT} {res : List (Expr Nat)} {fuel fuel₂ : Nat} {R : Expr Nat}
    (hfs : FieldsTyT E a.family.member.arity (fun k => lift 0 k fv.idxTel)
      (telCtxT fv.params) 0 fs res)
    (hpar : a.family.parameters = fv.params.map Prod.fst)
    (hidx : a.family.indices = fv.indices.map Prod.fst)
    (hdd : DrecDTypedT E a.family.ref a.family.member fv fs)
    (hfuel : 2 ≤ fuel) (hfuelf : fuel₂ - 1 ≤ fuel)
    (hΓmin : CtxWfT E m.arity (minorCtxT a i.val))
    (hΓpre : ∀ j, CtxWfT E m.arity (plainCtxT (fs.take j) (telCtxT fv.params)))
    {lvD : Nat → Level}
    (hDoms : ∀ k (hk : k < (liftDomsT 0 (1 + i.val)
        (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
          a.family.parameters.length 0 fs)).length),
      HasTyT E m.arity (policyPrefixContext (liftDomsT 0 (1 + i.val)
          (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
            a.family.parameters.length 0 fs)) k ++ minorCtxT a i.val)
        ((liftDomsT 0 (1 + i.val)
          (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
            a.family.parameters.length 0 fs))[k]'hk)
        (.sort (lvD k)))
    (hsh : fieldShapesFuel E fuel₂ a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length
      a.family.parameters.length (a.constructorViews i).fields =
        some (fs.map FieldT.shapeT))
    (htel : ctorFieldTelescope (a.constructorViews i) =
      ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
        (policyLocals a.family.parameters.length) SubstT.id fs res)
    (hmin : minorFromTelescope E fuel a.family.parameters.length (.bvar i.val)
      (foldApps (.const (a.family.ref + 1 + i.val) (canonLevels a.family.member.arity))
        (policyParameterLocals a.family.parameters.length (1 + i.val)))
      (fs.map FieldT.shapeT)
      (ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
        (policyParameterLocals a.family.parameters.length (1 + i.val))
        (fun j => lift 0 (1 + i.val) (SubstT.id j)) fs res) = some R) :
    MinorTypedT E m.arity (policyMotiveLevel a.family.member.arity a.policy)
      (minorCtxT a i.val) (fs.map FieldT.shapeT) R := by
  have har : a.family.member.arity ≤ m.arity := by
    rw [a.recursorArity]
    cases a.policy <;> simp only [policyRecursorArity] <;> omega
  obtain ⟨Δd, hΔd⟩ : ∃ Δd : LCtx, Δd =
      LocalDecl.assumption (policyMotiveType a.family a.policy) ::
        (policyPrefixContext a.minorTypes i.val).reverse := ⟨_, rfl⟩
  have hm : i.val ≤ a.minorTypes.length := by
    rw [a.minorCount]; omega
  have hd : Δd.length = 1 + i.val := by
    rw [hΔd, List.length_cons, List.length_reverse]
    simp only [policyPrefixContext, List.length_map, List.length_reverse,
      List.length_take]
    rw [Nat.min_eq_left hm]
    omega
  have hrev : Δd.reverse ++ telCtxT fv.params =
      policyPrefixContext a.minorTypes i.val ++
        (.assumption (policyMotiveType a.family a.policy) :: telCtxT fv.params) := by
    rw [hΔd, List.reverse_cons, List.reverse_reverse, List.append_assoc]
    rfl
  have hctx : Δd.reverse ++ telCtxT fv.params = minorCtxT a i.val := by
    rw [hrev]
    show _ = policyPrefixContext a.minorTypes i.val ++
      (.assumption (policyMotiveType a.family a.policy) ::
        (policyPrefixContext a.family.parameters a.family.parameters.length ++ []))
    rw [hpar, List.length_map, policyPrefixContext_telCtxT, List.append_nil]
  have hnp : fv.params.length = a.family.parameters.length := by
    rw [hpar, List.length_map]
  have hnp' : a.family.parameters.length = fv.params.length := hnp.symm
  have hMot : policyMotiveType a.family a.policy =
      motTyAt a.family.ref (canonLevels a.family.member.arity) a.family.parameters.length
        (fv.indices.map Prod.fst) (policyMotiveLevel a.family.member.arity a.policy) 0 := by
    rw [policyMotiveType_eq a.family (ls := canonLevels a.family.member.arity) a.policy
      rfl rfl hpar hidx, ← motTyAt_eq_motTyT, ← hnp']
  have hM : Nonempty (HasTyT E m.arity
      (Δd.reverse ++ telCtxT fv.params) (.bvar i.val)
      (motTyAt a.family.ref (canonLevels a.family.member.arity) a.family.parameters.length
        (fv.indices.map Prod.fst) (policyMotiveLevel a.family.member.arity a.policy)
        Δd.length)) := by
    have h0 : Nonempty (HasTyT E m.arity
        (policyPrefixContext a.minorTypes i.val ++
          (.assumption (policyMotiveType a.family a.policy) :: telCtxT fv.params))
        (.bvar i.val)
        (motTyAt a.family.ref (canonLevels a.family.member.arity) a.family.parameters.length
          (fv.indices.map Prod.fst) (policyMotiveLevel a.family.member.arity a.policy)
          (0 + i.val + 1))) := hM_minCtx a.minorTypes hm
        (policyMotiveType a.family a.policy) (telCtxT fv.params) hMot
    rw [hrev, hd]
    have hs : (0 + i.val + 1) = 1 + i.val := by omega
    rw [← hs]
    exact h0
  have hΓΔ : CtxWfT E m.arity (Δd.reverse ++ telCtxT fv.params) := by
    rw [hctx]; exact hΓmin
  have hI1 := hI1_fieldsT_conv_at (f := a.family.ref) (np := a.family.parameters.length)
    hcl a.family.present fs hfs rfl hnp hdd har Δd
  -- the views' field list is the emitted list: `htel` injectivity plus
  -- `ctorDomsT_eq_emitted` at `pc = 0`.
  have hvf : (a.constructorViews i).fields =
      ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
        a.family.parameters.length 0 fs := by
    have hteq := htel
    unfold ctorFieldTelescope at hteq
    rw [ctorFieldsT_policyPi] at hteq
    have hlen' : (a.constructorViews i).fields.length =
        (ctorDomsT a.family.ref (canonLevels a.family.member.arity)
          (policyLocals a.family.parameters.length) SubstT.id fs).length := by
      rw [ctorDomsT_length]
      have hlf := fieldShapesFuel_length E _ hsh
      rw [List.length_map] at hlf
      omega
    obtain ⟨hfd, _⟩ := policyPi_inj_length _ _ hlen' hteq
    rw [hfd]
    have h := ctorDomsT_eq_emitted a.family.ref (canonLevels a.family.member.arity)
      a.family.parameters.length 0 fs
    have hpl : policyParameterLocals a.family.parameters.length 0 =
        policyLocals a.family.parameters.length := by
      simp only [policyParameterLocals, policyLocals, Nat.add_zero]
    rw [← h, hpl]
  -- the analysis oracle `hI3_conv_at` consumes: `hsh`'s `.drecD` verdicts read out
  -- through `fieldAnalyze_recursive_out`, domain's telescope collapsed to `[]`.
  have han : ∀ j (hj : j < fs.length) {D : Expr Nat} {idx : List (Expr Nat)},
      fs[j] = .drecD D idx →
      ∃ body : Expr Nat,
        piTelescopeFuel E (fuel₂ - 1)
          ((ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
            a.family.parameters.length 0 fs)[j]'(by
              rw [ctorEmittedDoms_length]; exact hj)) = some ([], body) ∧
        properFamilyFuel E (fuel₂ - 1) a.family.ref a.family.member.arity
          a.family.parameters.length (fv.indices.map Prod.fst).length
          (a.family.parameters.length + j - 1) body = some true := by
    intro j hj D idx hfj
    have hsh' : fieldShapesFuel E fuel₂ a.family.ref a.family.member.arity
        a.family.parameters.length a.family.indices.length a.family.parameters.length
        (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
          a.family.parameters.length 0 fs) = some (fs.map FieldT.shapeT) := by
      rwa [hvf] at hsh
    obtain ⟨hjT, idxR, hAn⟩ := fieldShapesFuel_getElem E _ hsh' j
      (by rw [List.length_map]; exact hj)
    have hshape : (fs.map FieldT.shapeT)[j]'(by rw [List.length_map]; exact hj) =
        .recursive 0 := by
      rw [List.getElem_map, hfj]; rfl
    rw [hshape] at hAn
    obtain ⟨doms, body, hpt', hdomslen, _hidxR, hproper'⟩ := fieldAnalyze_recursive_out hAn
    have hdn : doms = [] := List.eq_nil_of_length_eq_zero hdomslen
    subst hdn
    refine ⟨body, hpt', ?_⟩
    simp only [List.length_nil, Nat.zero_add] at hproper'
    rwa [hidx] at hproper'
  have hfs' := fieldsTyT_levelMono har hfs
  have hf : transparentBody E a.family.ref (canonLevels a.family.member.arity) = none :=
    transparentBody_family a.family _
  have hI3 := hI3_conv_at (f := a.family.ref) (np := a.family.parameters.length)
    (fm := a.family.member) (fv := fv) hW hP hC hcl hSL hconst
    a.family.present a.family.hasClass fs hfs hnp hdd har hfuel hfuelf hf Δd hΓΔ hΓpre
    (lvD := lvD) (fun k hk => by
      rw [hd] at hk
      have h := hDoms k hk
      simpa only [← hd, ← hctx] using h) han
  have hlen : (fs.map FieldT.shapeT).length =
      (liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
        (canonLevels a.family.member.arity) a.family.parameters.length 0 fs)).length := by
    rw [List.length_map, length_liftDomsT, ctorEmittedDoms_length]
  have hds : ctorDomsT a.family.ref (canonLevels a.family.member.arity)
      (policyParameterLocals a.family.parameters.length Δd.length)
      (fun j => lift 0 Δd.length (SubstT.id j)) fs =
      liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
        (canonLevels a.family.member.arity) a.family.parameters.length 0 fs) := by
    have h := ctorDomsT_eq_emitted_lift a.family.ref (canonLevels a.family.member.arity)
      a.family.parameters.length 0 Δd.length fs
    rwa [Nat.zero_add] at h
  have hpi : ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
      (policyParameterLocals a.family.parameters.length Δd.length)
      (fun j => lift 0 Δd.length (SubstT.id j)) fs res =
      policyPi (liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
        (canonLevels a.family.member.arity) a.family.parameters.length 0 fs))
        (foldApps (.const a.family.ref (canonLevels a.family.member.arity))
          ((policyParameterLocals a.family.parameters.length Δd.length).map
            (lift 0 fs.length) ++
            res.map (substT (ctorEndSubstT (fun j => lift 0 Δd.length (SubstT.id j)) fs)))) := by
    rw [ctorFieldsT_policyPi, hds]
  rw [← hd] at hmin
  rw [hpi] at hmin
  have gores := minorTyped_go_conv hW hcl hSL hconst fuel a.family.parameters.length
    a.family.ref (canonLevels a.family.member.arity) (fv.indices.map Prod.fst)
    (policyMotiveLevel a.family.member.arity a.policy) fv.sort hf
    (fs.map FieldT.shapeT) (Δd.reverse ++ telCtxT fv.params) hΓΔ Δd.length (.bvar i.val)
    (foldApps (.const (a.family.ref + 1 + i.val) (canonLevels a.family.member.arity))
      (policyParameterLocals a.family.parameters.length Δd.length))
    (liftDomsT 0 Δd.length (ctorEmittedDoms a.family.ref
      (canonLevels a.family.member.arity) a.family.parameters.length 0 fs))
    (foldApps (.const a.family.ref (canonLevels a.family.member.arity))
      ((policyParameterLocals a.family.parameters.length Δd.length).map
        (lift 0 fs.length) ++
        res.map (substT (ctorEndSubstT (fun j => lift 0 Δd.length (SubstT.id j)) fs))))
    R hlen hM hI1 hI3 hmin
  rw [hctx] at gores
  exact gores

/-- **IA-019T, the admitted cell.** At an admitted recursor whose constructor
    telescope is the typed-builder's (`htel`, the views' content), whose shape
    analysis agrees with the typed field list (`hsh`, the (c) wall's second
    named premise alongside `NoDrecDT`), and whose minor premises match
    (`h12`), minor `i`'s stored type is typed in its minor context at the
    recursor's arity.

    The fields and IH binders come from `minorTyped_at_cell`. The leaf — the
    motive applied to the result indices and the constructor application — is
    IA-020's conclusion at the same stored minor: `derivedMinor_agree` reads
    the derived minor off `derivedMinor_eq` and `h12`'s premise, the shapes
    off `fieldShapesFuel_agree`, and `minorBinders`/`minorLeaf` land on
    `piDomsOf`/`piTailOf` by the structural lemmas. -/
private theorem IA019T_admitted_minor_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (hcl : EnvClosed E) {fv : FamViewT a.family.member}
    {fs : List FieldT} {res : List (Expr Nat)} {fuel : Nat}
    (hfs : FieldsTyT E a.family.member.arity (fun k => lift 0 k fv.idxTel)
      (telCtxT fv.params) 0 fs res)
    (hpar : a.family.parameters = fv.params.map Prod.fst)
    (hidx : a.family.indices = fv.indices.map Prod.fst)
    (hnd : NoDrecDT fs) (hfuel : 2 ≤ fuel)
    (h12 : MinorPremisesMatch a) {u : Level}
    (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (htel : ctorFieldTelescope (a.constructorViews i) =
      ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
        (policyLocals a.family.parameters.length) SubstT.id fs res)
    {fuel₂ : Nat}
    (hsh : fieldShapesFuel E fuel₂ a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length a.family.parameters.length
      (a.constructorViews i).fields = some (fs.map FieldT.shapeT)) :
    ∃ v, Nonempty (HasTyT E m.arity (minorCtxT a i.val) (a.minorTypes[i.val]'(
      by rw [a.minorCount]; exact i.isLt)) (.sort v)) := by
  have hi : i.val < a.minorTypes.length := by rw [a.minorCount]; exact i.isLt
  have hcell := minorTyped_at_cell a i hcl hfs hpar hidx hnd hfuel
  -- the stored minor is the cell's, lifted past the earlier minors
  obtain ⟨shapes', fuel', hsh', hd'⟩ := h12 i
  rw [List.getElem?_eq_getElem hi] at hd'
  have hsseq : shapes' = fs.map FieldT.shapeT :=
    fieldShapesFuel_agree E hsh' hsh
  rw [hsseq] at hd'
  have hder : derivedMinor a i fuel (fs.map FieldT.shapeT) =
      some (lift 0 i.val (minorTyT a.family.ref (canonLevels a.family.member.arity)
        a.family.parameters.length (a.family.ref + 1 + i.val, fs, res))) :=
    derivedMinor_eq a i hfuel rfl rfl rfl htel (noDrecDT_isDrecD hnd)
  have hRL : lift 0 i.val (minorTyT a.family.ref (canonLevels a.family.member.arity)
      a.family.parameters.length (a.family.ref + 1 + i.val, fs, res)) =
      a.minorTypes[i.val]'hi :=
    derivedMinor_agree a i hder hd'
  have hR : minorFieldsT a.family.ref (a.family.ref + 1 + i.val)
      (canonLevels a.family.member.arity)
      (policyParameterLocals a.family.parameters.length (1 + i.val)) (.bvar i.val) []
      (fun j => lift 0 (1 + i.val) (SubstT.id j)) fs res =
      a.minorTypes[i.val]'hi :=
    (minorFieldsT_eq_lift_minorTyT a.family.ref (a.family.ref + 1 + i.val)
      (canonLevels a.family.member.arity) a.family.parameters.length i.val fs res).trans hRL
  -- the leaf is IA-020's conclusion, taken at the concrete stored minor so the
  -- `piDomsOf`/`piTailOf` rewrites land on the same term `hcell` proves
  obtain ⟨w₂, ⟨hMt⟩⟩ := recursor_minorType_typed a hT i.val hi
  have hMt' : HasTyT E m.arity (minorCtxT a i.val)
      (policyPi (piDomsOf (a.minorTypes[i.val]'hi)) (piTailOf (a.minorTypes[i.val]'hi)))
      (.sort w₂) := by
    rw [policyPi_piDomsOf_piTailOf]
    exact hMt
  obtain ⟨v, hconcl⟩ := (hasTyT_policyPi_inv _ hMt').2
  have hcount : (piDomsOf (a.minorTypes[i.val]'hi)).length =
      shapeBinders (fs.map FieldT.shapeT) := by
    simp only [derivedMinor] at hd'
    exact piDomsOf_minorFromTelescope E fuel' _ _ _ _ _ _ hd'
  have hbind : minorBinders (fs.map FieldT.shapeT) (a.minorTypes[i.val]'hi) =
      policyPrefixContext (piDomsOf (a.minorTypes[i.val]'hi))
        (piDomsOf (a.minorTypes[i.val]'hi)).length := by
    rw [hcount]
    exact minorBinders_eq_ppc _ _ (Nat.le_of_eq hcount.symm)
  have hleaf : minorLeaf (fs.map FieldT.shapeT) (a.minorTypes[i.val]'hi) =
      piTailOf (a.minorTypes[i.val]'hi) :=
    minorLeaf_eq_piTailOf _ _ hcount.symm
  obtain ⟨w, hw⟩ := minorTypedT_hasTyT hcell (fun {Γ' T} hΓ hTe => by
    rw [hR] at hΓ hTe
    rw [hbind] at hΓ
    rw [hleaf] at hTe
    subst hΓ
    subst hTe
    exact ⟨v, hconcl⟩)
  rw [hR] at hw
  exact ⟨w, hw⟩

/-- **IA-019T, conversion-aware admitted cell.**  The `NoDrecDT`-free twin of
    `IA019T_admitted_minor_typed`: `.drecD` fields' typing comes through
    `DrecDTypedT` (`hdd`) and the shape analysis `hsh`; the stored minor is read
    off `h12` (`MinorPremisesMatch`) at `fuel'` raised to the walk's fuel —
    `derivedMinor_eq`'s `isDrecD`-freeness this path cannot pay, so the walked
    `R` is the stored minor directly.  `hΓmin`/`hΓpre`/`hDoms` remain genuine
    Type-valued debts: the checker-paid route (`MinorDomainsTyped` and the
    `sortTyAtC` pins) discharges them at the consumer; `DrecDTypedT`/`hI1` are
    `Nonempty`-level and cannot manufacture them. -/
private theorem IA019T_admitted_minor_typed_conv {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (hW : EnvWfT E) (hP : hW.InScope) (hC : hW.ScopeCheck)
    (hcl : EnvClosed E) (hSL : SubstLetT E m.arity)
    (hconst : ConstsRightDataT E m.arity)
    {fv : FamViewT a.family.member}
    {fs : List FieldT} {res : List (Expr Nat)} {fuel₂ : Nat}
    (hfs : FieldsTyT E a.family.member.arity (fun k => lift 0 k fv.idxTel)
      (telCtxT fv.params) 0 fs res)
    (hpar : a.family.parameters = fv.params.map Prod.fst)
    (hidx : a.family.indices = fv.indices.map Prod.fst)
    (hdd : DrecDTypedT E a.family.ref a.family.member fv fs)
    (hΓmin : CtxWfT E m.arity (minorCtxT a i.val))
    (hΓpre : ∀ j, CtxWfT E m.arity (plainCtxT (fs.take j) (telCtxT fv.params)))
    {lvD : Nat → Level}
    (hDoms : ∀ k (hk : k < (liftDomsT 0 (1 + i.val)
        (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
          a.family.parameters.length 0 fs)).length),
      HasTyT E m.arity (policyPrefixContext (liftDomsT 0 (1 + i.val)
          (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
            a.family.parameters.length 0 fs)) k ++ minorCtxT a i.val)
        ((liftDomsT 0 (1 + i.val)
          (ctorEmittedDoms a.family.ref (canonLevels a.family.member.arity)
            a.family.parameters.length 0 fs))[k]'hk)
        (.sort (lvD k)))
    (h12 : MinorPremisesMatch a) {u : Level}
    (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (htel : ctorFieldTelescope (a.constructorViews i) =
      ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
        (policyLocals a.family.parameters.length) SubstT.id fs res)
    (hsh : fieldShapesFuel E fuel₂ a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length a.family.parameters.length
      (a.constructorViews i).fields = some (fs.map FieldT.shapeT)) :
    ∃ v, Nonempty (HasTyT E m.arity (minorCtxT a i.val) (a.minorTypes[i.val]'(
      by rw [a.minorCount]; exact i.isLt)) (.sort v)) := by
  have hi : i.val < a.minorTypes.length := by rw [a.minorCount]; exact i.isLt
  obtain ⟨shapes', fuel', hsh', hd'⟩ := h12 i
  rw [List.getElem?_eq_getElem hi] at hd'
  have hsseq : shapes' = fs.map FieldT.shapeT := fieldShapesFuel_agree E hsh' hsh
  rw [hsseq] at hd'
  simp only [derivedMinor] at hd'
  rw [htel, lift_ctorFieldsT, policyLocals_map_lift] at hd'
  -- the stored minor is the walked `R`, at `fuel'` raised past the analysis bound
  have hmin : minorFromTelescope E (fuel' + fuel₂ + 2) a.family.parameters.length
      (.bvar i.val)
      (foldApps (.const (a.family.ref + 1 + i.val) (canonLevels a.family.member.arity))
        (policyParameterLocals a.family.parameters.length (1 + i.val)))
      (fs.map FieldT.shapeT)
      (ctorFieldsT a.family.ref (canonLevels a.family.member.arity)
        (policyParameterLocals a.family.parameters.length (1 + i.val))
        (fun j => lift 0 (1 + i.val) (SubstT.id j)) fs res) =
      some (a.minorTypes[i.val]'hi) :=
    minorFromTelescope_mono E (show fuel' ≤ fuel' + fuel₂ + 2 by omega)
      _ _ hd'
  have hcell := minorTyped_at_cell_conv a i hW hP hC hcl hSL hconst hfs hpar hidx hdd
    (fuel := fuel' + fuel₂ + 2) (fuel₂ := fuel₂) (R := a.minorTypes[i.val]'hi)
    (by omega) (by omega) hΓmin hΓpre (lvD := lvD) hDoms hsh htel hmin
  -- the leaf is IA-020's conclusion at the stored minor: `piDomsOf`/`piTailOf`
  -- land on it directly, no `minorFieldsT` bridge
  obtain ⟨w₂, ⟨hMt⟩⟩ := recursor_minorType_typed a hT i.val hi
  have hMt' : HasTyT E m.arity (minorCtxT a i.val)
      (policyPi (piDomsOf (a.minorTypes[i.val]'hi)) (piTailOf (a.minorTypes[i.val]'hi)))
      (.sort w₂) := by
    rw [policyPi_piDomsOf_piTailOf]
    exact hMt
  obtain ⟨v, hconcl⟩ := (hasTyT_policyPi_inv _ hMt').2
  have hcount : (piDomsOf (a.minorTypes[i.val]'hi)).length =
      shapeBinders (fs.map FieldT.shapeT) :=
    piDomsOf_minorFromTelescope E _ _ _ _ _ _ _ hmin
  have hbind : minorBinders (fs.map FieldT.shapeT) (a.minorTypes[i.val]'hi) =
      policyPrefixContext (piDomsOf (a.minorTypes[i.val]'hi))
        (piDomsOf (a.minorTypes[i.val]'hi)).length := by
    rw [hcount]
    exact minorBinders_eq_ppc _ _ (Nat.le_of_eq hcount.symm)
  have hleaf : minorLeaf (fs.map FieldT.shapeT) (a.minorTypes[i.val]'hi) =
      piTailOf (a.minorTypes[i.val]'hi) :=
    minorLeaf_eq_piTailOf _ _ hcount.symm
  obtain ⟨w, hw⟩ := minorTypedT_hasTyT hcell (fun {Γ' T} hΓ hTe => by
    rw [hbind] at hΓ
    rw [hleaf] at hTe
    subst hΓ
    subst hTe
    exact ⟨v, hconcl⟩)
  exact ⟨w, hw⟩
