import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedLevels
import rcic.RcicTypedConv
import rcic.RcicTypedInstPrefix
import rcic.RcicIARecIH

/-!
# DT-019 S1 — the generic pieces of the direct ι-SR route

Three transports the direct route (`RcicIotaSRRows`) rides, none of which
existed at the level or shape it needs:

* `hasTyT_relocateN` / `convT_relocateN` / `tyConvT_relocateN` — a derivation
  over a context `Δ` relocates under any tail `Γ` at the SAME level bound `n`.
  `hasTyT_relocate` (`RcicDTMetaTypedSR`) does this only from level `0`
  (its `const` arm re-derives the level bound from `levelsBounded_zero_any`);
  here the bound is passed through unchanged.
* `tyConvT_instLevels` — the chain form of `convT_instLevels`.
* `convT_instPrefixSame` / `tyConvT_instPrefixSame` — the `ConvT`/`TyConvT`
  twins of DT-019 package A (`hasTyT_instPrefix`): the SAME argument list
  substituted on both sides, so no endpoint typing and no debt is needed
  (`convT_substS` reads only the replacement typing).
* `famLevels_instLevel` — the canonical family level vector instantiated at a
  list of its own length is that list.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) relocation under a tail at a fixed level bound -/

mutual
  def hasTyT_relocateN {E : ResolvedEnv} {n : Nat} :
      {Δ : LCtx} → {e A : Expr Nat} → HasTyT E n Δ e A →
      {Γ : LCtx} → HasTyT E n (Δ ++ Γ) e A
    | _, _, _, .sort _ _, _ => .sort _ _
    | _, _, _, .bvar _ _ _ h, _ =>
        .bvar _ _ _ (by rw [lookupType_append_lt (lookupType_lt_length h)]; exact h)
    | _, _, _, .const _ _ _ m hres hlen hwf, _ => .const _ _ _ m hres hlen hwf
    | _, _, _, .pi _ _ _ _ _ hA hB, _ =>
        .pi _ _ _ _ _ (hasTyT_relocateN hA) (hasTyT_relocateN hB)
    | _, _, _, .lam _ _ _ _ _ hA hb, _ =>
        .lam _ _ _ _ _ (hasTyT_relocateN hA) (hasTyT_relocateN hb)
    | _, _, _, .app _ _ _ _ _ hf ha, _ =>
        .app _ _ _ _ _ (hasTyT_relocateN hf) (hasTyT_relocateN ha)
    | _, _, _, .letE _ _ _ _ _ _ hA hv hb, _ =>
        .letE _ _ _ _ _ _ (hasTyT_relocateN hA) (hasTyT_relocateN hv) (hasTyT_relocateN hb)
    | _, _, _, .lit _ _ _ h, _ => .lit _ _ _ (hasTyT_relocateN h)
    | _, _, _, .conv _ _ _ _ _ h hc, _ =>
        .conv _ _ _ _ _ (hasTyT_relocateN h) (convT_relocateN hc)

  def convT_relocateN {E : ResolvedEnv} {n : Nat} :
      {Δ : LCtx} → {a b T : Expr Nat} → ConvT E n Δ a b T →
      {Γ : LCtx} → ConvT E n (Δ ++ Γ) a b T
    | _, _, _, _, .refl _ _ _ hA, _ => .refl _ _ _ (hasTyT_relocateN hA)
    | _, _, _, _, .symm _ _ _ _ h, _ => .symm _ _ _ _ (convT_relocateN h)
    | _, _, _, _, .trans _ _ _ _ _ h1 h2, _ =>
        .trans _ _ _ _ _ (convT_relocateN h1) (convT_relocateN h2)
    | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg, _ =>
        .beta _ _ _ _ _ _ (hasTyT_relocateN hA) (hasTyT_relocateN hbody)
          (hasTyT_relocateN harg)
    | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, _ =>
        .zeta _ _ _ _ _ _ (hasTyT_relocateN hA) (hasTyT_relocateN hv)
          (hasTyT_relocateN hb)
    | _, _, _, _, .zetaLocal _ _ _ _ hval hty hv, _ =>
        .zetaLocal _ _ _ _
          (by rw [lookupValue_append_lt (lookupValue_lt_length hval)]; exact hval)
          (by rw [lookupType_append_lt (lookupType_lt_length hty)]; exact hty)
          (hasTyT_relocateN hv)
    | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb, _ =>
        .delta _ r ls m b hres hbody htr hlen hwf (hasTyT_relocateN hb)
    | _, _, _, _, .iota _ _ _ _ h hl hr, _ =>
        .iota _ _ _ _ h (hasTyT_relocateN hl) (hasTyT_relocateN hr)
    | _, _, _, _, .lit _ _ _ _ h hexp, _ =>
        .lit _ _ _ _ h (hasTyT_relocateN hexp)
    | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, _ =>
        .app _ _ _ _ _ _ _ (convT_relocateN h1) (convT_relocateN h2)
    | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, _ =>
        .lam _ _ _ _ _ _ _ (convT_relocateN hA) (convT_relocateN hb)
    | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, _ =>
        .pi _ _ _ _ _ _ _ (convT_relocateN hA) (convT_relocateN hB)
    | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, _ =>
        .letE _ _ _ _ _ _ _ _ _ (convT_relocateN hA) (convT_relocateN hv)
          (convT_relocateN hb)
    | _, _, _, _, .sorts _ _ _ h, _ => .sorts _ _ _ h
    | _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h, _ =>
        .consts _ _ _ _ _ hres hlen hwf hwf' h
    | _, _, _, _, .eta _ _ _ _ h, _ => .eta _ _ _ _ (hasTyT_relocateN h)
    | _, _, _, _, .irr _ _ _ _ hP hp hq, _ =>
        .irr _ _ _ _ (hasTyT_relocateN hP) (hasTyT_relocateN hp) (hasTyT_relocateN hq)
    | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, _ =>
        .tyConv _ _ _ _ _ _ (convT_relocateN h) (convT_relocateN hA)
end

def tyConvT_relocateN {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {Δ : LCtx} → {A B : Expr Nat} → TyConvT E n Δ A B → TyConvT E n (Δ ++ Γ) A B
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .of _ _ _ u c => .of _ _ _ u (convT_relocateN c)
  | _, _, _, .trans _ _ _ _ c₁ c₂ =>
      .trans _ _ _ _ (tyConvT_relocateN c₁) (tyConvT_relocateN c₂)

/-! ## (2) the chain form of level instantiation -/

def tyConvT_instLevels {E : ResolvedEnv} (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E a Γ A B →
    TyConvT E n (instLvlsCtx ls Γ) (instantiateLevels ls A) (instantiateLevels ls B)
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .of _ _ _ u c =>
      .of _ _ _ (instLevel ls u) (convT_instLevels hEL hIL hls hlen c)
  | _, _, _, .trans _ _ _ _ c₁ c₂ =>
      .trans _ _ _ _ (tyConvT_instLevels hEL hIL hls hlen c₁)
        (tyConvT_instLevels hEL hIL hls hlen c₂)

/-! ## (3) the canonical level vector instantiated at its own length -/

theorem instLevel_param_lt (ls : List Level) (i : Nat) (hi : i < ls.length) :
    instLevel ls (.param i) = ls[i] := by
  simp only [instLevel, lvlSubst, levelParamSubst, List.getElem?_eq_getElem hi,
    Option.getD_some]

theorem famLevels_instLevel (ls : List Level) {k : Nat} (hk : ls.length = k) :
    ((List.range k).map Level.param).map (instLevel ls) = ls := by
  subst hk
  refine List.ext_getElem ?_ ?_
  · simp only [List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact instLevel_param_lt ls i h2

/-! ## (4) the `ConvT` twin of DT-019 package A (same arguments both sides) -/

/-- `hasTyT_instPrefix`'s shape on a conversion: one `convT_substS` per outermost
    binder, the replacement typing from `hasTyTLiftPrefix`. No endpoint typing
    and no debt: the substitution theorem reads only the replacement's typing. -/
def convT_instPrefixSame {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (args : List (Expr Nat)) → {Γ : LCtx} → {ΔT : List (Expr Nat)} →
    {a b T : Expr Nat} →
    (hlen : ΔT.length = args.length) →
    ConvT E n (ΔT.map LocalDecl.assumption ++ Γ) a b T →
    (∀ i (hi : i < args.length),
      HasTyT E n Γ args[i]
        (instPrefix (args.take i) (outerDom ΔT i))) →
    ConvT E n Γ (instPrefix args a) (instPrefix args b) (instPrefix args T)
  | [], _, ΔT, a, b, T, hlen, h, _ => by
      cases ΔT with
      | nil => simpa only [List.map_nil, List.nil_append, instPrefix] using h
      | cons => simp only [List.length_cons, List.length_nil] at hlen
                omega
  | x :: as, Γ, ΔT, a, b, T, hlen, h, hargs => by
      have hnn : ΔT ≠ [] := by
        intro hnil
        rw [hnil, List.length_nil] at hlen
        exact Nat.noConfusion hlen
      generalize hΔT' : ΔT.dropLast = ΔT'
      generalize hD : ΔT.getLast hnn = D
      have hΔ : ΔT = ΔT' ++ [D] := by
        rw [← hΔT', ← hD]; exact (List.dropLast_concat_getLast hnn).symm
      clear hΔT' hD
      subst hΔ
      have hlen' : ΔT'.length = as.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hlen
        omega
      have hctx : (ΔT' ++ [D]).map LocalDecl.assumption ++ Γ =
          ΔT'.map LocalDecl.assumption ++ (.assumption D :: Γ) := by
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append]
      rw [hctx] at h
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
      have ha0 : HasTyT E n Γ x D := by
        have h0 := hargs 0 (Nat.succ_pos _)
        rw [hlast] at h0
        simpa only [List.getElem_cons_zero, List.take_zero, instPrefix]
          using h0
      have hvty : HasTyT E n
          (substRemove x ΔT'.length
            (ΔT'.map LocalDecl.assumption ++ .assumption D :: Γ))
          (lift 0 ΔT'.length x) (lift 0 ΔT'.length D) := by
        rw [substRemove_tel_assumption]
        have hw := hasTyTLiftPrefix hcl
          ((telSubstLast x ΔT').map LocalDecl.assumption) ha0
        rwa [List.length_map, telSubstLast_length] at hw
      have hstep := convT_substS hcl hinst x D (j := ΔT'.length)
        h hget hvty
      rw [substRemove_tel_assumption, hlen'] at hstep
      simp only [instPrefix]
      refine convT_instPrefixSame hcl hinst as (ΔT := telSubstLast x ΔT')
        (a := instantiate as.length (lift 0 as.length x) a)
        (b := instantiate as.length (lift 0 as.length x) b)
        (T := instantiate as.length (lift 0 as.length x) T) ?_ hstep ?_
      · exact (telSubstLast_length x ΔT').trans hlen'
      · intro i hi
        have hb : as.length - 1 - i < ΔT'.length := by rw [hlen']; omega
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
        have hdom' : outerDom (telSubstLast x ΔT') i =
            instantiate i (lift 0 i x) (ΔT'[as.length - 1 - i]'(hb)) := by
          have hb' : ΔT'.length - 1 - i < ΔT'.length := by
            rw [hlen']; omega
          have hlt2 : (telSubstLast x ΔT').length - 1 - i =
              ΔT'.length - 1 - i := by rw [telSubstLast_length]
          simp only [outerDom, List.getD_eq_getElem?_getD, hlt2]
          rw [telSubstLast_getElem? x ΔT' (ΔT'.length - 1 - i) hb']
          have hidx' : ΔT'.length - 1 - i = as.length - 1 - i := by
            rw [hlen']
          rw [getElem_idx_congr hidx' hb' hb]
          have hsub : ΔT'.length - 1 - (ΔT'.length - 1 - i) = i := by
            omega
          rw [hsub, Option.getD_some]
        rw [hdom']
        exact hsrc

def convT_instPrefixSame_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} {ΔT : List (Expr Nat)} {args : List (Expr Nat)}
    {a b T : Expr Nat} (hlen : ΔT.length = args.length)
    (h : ConvT E n (ΔT.map LocalDecl.assumption ++ Γ) a b T)
    (hargs : ∀ i (hi : i < args.length),
      HasTyT E n Γ args[i]
        (instPrefix (args.take i) (outerDom ΔT i))) :
    ConvT E n Γ (instPrefix args a) (instPrefix args b) (instPrefix args T) :=
  convT_instPrefixSame (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) args hlen h hargs

/-- the chain form: every `.of` link at its own sort (`instPrefix args (.sort u)`
    is `.sort u`, `instPrefix_sort`). -/
def tyConvT_instPrefixSame_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} {ΔT : List (Expr Nat)} {args : List (Expr Nat)}
    (hlen : ΔT.length = args.length)
    (hargs : ∀ i (hi : i < args.length),
      HasTyT E n Γ args[i]
        (instPrefix (args.take i) (outerDom ΔT i))) :
    {A B : Expr Nat} → TyConvT E n (ΔT.map LocalDecl.assumption ++ Γ) A B →
    TyConvT E n Γ (instPrefix args A) (instPrefix args B)
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ u c => by
      have hc := convT_instPrefixSame_of_envWfT hW hlen c hargs
      rw [instPrefix_sort] at hc
      exact .of _ _ _ u hc
  | _, _, .trans _ _ _ _ c₁ c₂ =>
      .trans _ _ _ _ (tyConvT_instPrefixSame_of_envWfT hW hlen hargs c₁)
        (tyConvT_instPrefixSame_of_envWfT hW hlen hargs c₂)

/-! ## (5) `instPrefix` snoc: the last argument is a head substitution -/

theorem instTel_eq_instTelK_one : (as : List (Expr Nat)) → (e : Expr Nat) →
    instTel as e = instTelK 1 as e
  | [], _ => rfl
  | a :: as, e => by
      rw [instTel_cons, instTelK_cons, Nat.add_comm 1 as.length]
      exact instTel_eq_instTelK_one as _

theorem instPrefix_snoc (as : List (Expr Nat)) (a e : Expr Nat) :
    instPrefix (as ++ [a]) e = instantiate0 a (instTel as e) := by
  rw [instPrefix_append_instTelK]
  simp only [List.length_singleton]
  rw [← instTel_eq_instTelK_one]
  simp only [instPrefix_cons, instPrefix_nil, List.length_nil, lift_zero, instantiate0]

/-! ## (6) the spine inversion at the Π row -/

/-- A constant-headed application spine typed at `T`: every argument is typed at
    the stored telescope's domain instantiated by the earlier arguments, and `T`
    is convertible with the stored body instantiated by all of them. The Π row
    (`TypedRowsWf.piRow`) peels one binder per argument; `hasTyTInv_const` reads
    the head. Right-to-left induction on the spine (`rxs` is the reversed
    argument list, `rds` the reversed domain list). -/
def spineInvAux {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hprow : PiRowField E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : E.members r = some m) {U : Expr Nat} :
    (rxs rds : List (Expr Nat)) → rds.length = rxs.length →
    instantiateLevels ls m.mtype = policyPi rds.reverse U → {T : Expr Nat} →
    HasTyT E n Γ (foldApps (.const r ls) rxs.reverse) T →
    Nonempty ((ls.length = m.arity) ×' (levelsBounded n ls = true) ×'
      (∀ i x d, rxs.reverse[i]? = some x → rds.reverse[i]? = some d →
        HasTyT E n Γ x (instPrefix (rxs.reverse.take i) d)) ×'
      TyConvT E n Γ (instPrefix rxs.reverse U) T)
  | [], [], _, hpi, T, hT => by
      obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const (r := r) (ls := ls) hT rfl
      have hmeq : m = m' := Option.some.inj (hres.symm.trans hres')
      subst hmeq
      simp only [List.reverse_nil, policyPi] at hpi
      rw [hpi] at hcv
      exact ⟨⟨hlen, hwf, fun i x d hx _ => by
        rw [List.reverse_nil, List.getElem?_nil] at hx; exact Option.noConfusion hx,
        by simpa only [instPrefix_nil] using hcv⟩⟩
  | [], _ :: _, hlen, _, _, _ => by
      rw [List.length_nil, List.length_cons] at hlen; exact Nat.noConfusion hlen
  | _ :: _, [], hlen, _, _, _ => by
      rw [List.length_nil, List.length_cons] at hlen; exact Nat.noConfusion hlen
  | y :: rys, D :: rds, hlen, hpi, T, hT => by
      have hlen' : rds.length = rys.length := Nat.succ.inj hlen
      rw [List.reverse_cons, foldApps_snoc] at hT
      obtain ⟨A, B, hf, hy, hc⟩ := hasTyTInv_app hT rfl
      have hpi' : instantiateLevels ls m.mtype = policyPi rds.reverse (.pi D U) := by
        rw [hpi, List.reverse_cons, policyPi_append]; rfl
      obtain ⟨hlsl, hwf, hargs, hconv⟩ := spineInvAux hW hprow hΓ hres rys rds hlen' hpi' hf
      rw [instPrefix_pi] at hconv
      obtain ⟨⟨cD⟩, ⟨cU⟩⟩ := hprow hΓ hconv
      have hy' : HasTyT E n Γ y (instPrefix rys.reverse D) :=
        hasTyT_of_tyConv hy (TyConvT.symmT cD)
      have hsub := tyConvT_subst0_of_envWfT hW hy' cU
      refine ⟨⟨hlsl, hwf, ?_, ?_⟩⟩
      · intro i x d hx hd
        rw [List.reverse_cons] at hx hd ⊢
        by_cases hi : i < rys.reverse.length
        · rw [List.getElem?_append_left hi] at hx
          have hi' : i < rds.reverse.length := by
            rw [List.length_reverse] at hi ⊢; omega
          rw [List.getElem?_append_left hi'] at hd
          rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
          exact hargs i x d hx hd
        · have hge : rys.reverse.length ≤ i := Nat.le_of_not_lt hi
          rw [List.getElem?_append_right hge] at hx
          have hge' : rds.reverse.length ≤ i := by
            rw [List.length_reverse] at hge ⊢; omega
          rw [List.getElem?_append_right hge'] at hd
          have hi0 : i - rys.reverse.length = 0 := by
            cases hlt : i - rys.reverse.length with
            | zero => rfl
            | succ k =>
                rw [hlt, List.getElem?_cons_succ, List.getElem?_nil] at hx
                exact Option.noConfusion hx
          have hi0' : i - rds.reverse.length = 0 := by
            rw [List.length_reverse] at hi0 ⊢; rw [hlen']; exact hi0
          rw [hi0] at hx
          rw [hi0'] at hd
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hd
          subst hx; subst hd
          have hieq : i = rys.reverse.length := by omega
          rw [hieq, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          exact hy'
      · rw [List.reverse_cons, instPrefix_snoc]
        exact .trans _ _ _ _ hsub hc

/-- the spine inversion at the Π row, forward form. -/
def hasTyT_spineInv_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hprow : PiRowField E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : E.members r = some m) {doms : List (Expr Nat)} {U : Expr Nat}
    (hpi : instantiateLevels ls m.mtype = policyPi doms U) (xs : List (Expr Nat))
    (hlen : doms.length = xs.length) {T : Expr Nat}
    (hT : HasTyT E n Γ (foldApps (.const r ls) xs) T) :
    Nonempty ((ls.length = m.arity) ×' (levelsBounded n ls = true) ×'
      (∀ i x d, xs[i]? = some x → doms[i]? = some d →
        HasTyT E n Γ x (instPrefix (xs.take i) d)) ×'
      TyConvT E n Γ (instPrefix xs U) T) := by
  have h := spineInvAux hW hprow hΓ hres xs.reverse doms.reverse
    (by simp only [List.length_reverse]; exact hlen)
    (by rw [List.reverse_reverse]; exact hpi)
    (by rw [List.reverse_reverse]; exact hT)
  rw [List.reverse_reverse, List.reverse_reverse] at h
  exact h

end Rcic.Declarative
