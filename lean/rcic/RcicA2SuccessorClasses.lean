import Lean
import rcic.RcicA2SortSupport
import rcic.RcicEtaKHeadInvariant

/-!
A-2: complete conditional successor-class proof for the UNMODIFIED ParRedT.
Base: bc734a23c6cb317a40b9ddc988f4fbf21efac61e.
Native-checked continuation; exact commands and source hashes are in
research/rcic/irr-postponement/F8_A2_SORT_NATIVE_VALIDATION_2026_10_14.txt.
Explicit premise: F8A2Support.SortUnique eqEnvT 2.
Left class: const-65 spines, same arity (<6), universes =n [1], arbitrary args.
Right class: lambda with body bvar 1, arbitrary domain annotation.
Both DerivedIotaU constructors are checked at iotaSpine's intermediate.
No original rule, measure, producer or EvPar constructor is changed.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.F8A2Successors
open F8A2Support

/-- The legacy arity result, with cc's extra `exact hr` removed. -/
theorem rec65_K_arity (w : IotaWitness eqEnvT) (href : w.recRef = 65) :
    w.preMajor.length + 1 = 6 := by
  have hmem := w.hrec
  rw [href] at hmem
  change some eqRecT = some w.recMember at hmem
  have hm : w.recMember = eqRecT := (Option.some.inj hmem).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  have hp := w.hpre
  omega

/-- The SAME arity guard for the schema half of DerivedIotaU. -/
theorem rec65_S_arity (w : IotaWitnessS eqEnvT) (href : w.recRef = 65) :
    w.preMajor.length + 1 = 6 := by
  have hmem := w.hrec
  rw [href] at hmem
  change some eqRecT = some w.recMember at hmem
  have hm : w.recMember = eqRecT := (Option.some.inj hmem).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  have hp := w.hpre
  omega

/-- Pure syntax: a short const-65 spine cannot be a legacy K source. -/
theorem short_not_K (ls : List Level) (xs : List (Expr Nat))
    (hshort : xs.length < 6) (w : IotaWitness eqEnvT) (major : Expr Nat) :
    recCall (.const w.recRef w.ls) w.preMajor major ≠
      foldApps (.const 65 ls) xs := by
  intro heq
  have hs := congrArg appsSpine heq
  change appsSpine (foldApps (.const w.recRef w.ls)
    (w.preMajor ++ [major])) = appsSpine (foldApps (.const 65 ls) xs) at hs
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
  have hh : Expr.const w.recRef w.ls = Expr.const 65 ls := congrArg Prod.fst hs
  have href : w.recRef = 65 := by injection hh with hr hls
  have hl := congrArg (fun z : Expr Nat × List (Expr Nat) => z.2.length) hs
  have hlen : w.preMajor.length + 1 = xs.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add] using hl
  have hfull := rec65_K_arity w href
  omega

theorem short_not_S (ls : List Level) (xs : List (Expr Nat))
    (hshort : xs.length < 6) (w : IotaWitnessS eqEnvT) (major : Expr Nat) :
    recCall (.const w.recRef w.ls) w.preMajor major ≠
      foldApps (.const 65 ls) xs := by
  intro heq
  have hs := congrArg appsSpine heq
  change appsSpine (foldApps (.const w.recRef w.ls)
    (w.preMajor ++ [major])) = appsSpine (foldApps (.const 65 ls) xs) at hs
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
  have hh : Expr.const w.recRef w.ls = Expr.const 65 ls := congrArg Prod.fst hs
  have href : w.recRef = 65 := by injection hh with hr hls
  have hl := congrArg (fun z : Expr Nat × List (Expr Nat) => z.2.length) hs
  have hlen : w.preMajor.length + 1 = xs.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add] using hl
  have hfull := rec65_S_arity w href
  omega

/-- Both union arms, not merely the particular Eq witness used by the peak. -/
theorem iotaU_not_short {a b : Expr Nat} (hi : DerivedIotaU eqEnvT a b)
    (ls : List Level) (xs : List (Expr Nat)) (hshort : xs.length < 6) :
    a ≠ foldApps (.const 65 ls) xs := by
  cases hi with
  | ofU w => exact short_not_K ls xs hshort w (ctorMajor w)
  | ofUS w =>
      exact short_not_S ls xs hshort w
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))

/-- Every ordinary union-iota source is an application. -/
theorem iotaU_source_app {a b : Expr Nat} (hi : DerivedIotaU eqEnvT a b) :
    ∃ f x : Expr Nat, a = .app f x := by
  cases hi with
  | ofU w =>
      refine ⟨foldApps (.const w.recRef w.ls) w.preMajor, ctorMajor w, ?_⟩
      exact foldApps_snoc _ _ _
  | ofUS w =>
      refine ⟨foldApps (.const w.recRef w.ls) w.preMajor,
        foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields), ?_⟩
      exact foldApps_snoc _ _ _

/-- Application-spine decomposition, retaining the final argument syntactically. -/
theorem app_spine_inv {f x : Expr Nat} {ls : List Level} {xs : List (Expr Nat)}
    (heq : Expr.app f x = foldApps (.const 65 ls) xs) :
    f = foldApps (.const 65 ls) (appsSpine f).2 ∧
      (appsSpine f).2 ++ [x] = xs := by
  have hs := congrArg appsSpine heq
  have happ : appsSpine (.app f x) =
      ((appsSpine f).1, (appsSpine f).2 ++ [x]) := rfl
  rw [happ, appsSpine_foldApps_const] at hs
  have hh : (appsSpine f).1 = .const 65 ls := congrArg Prod.fst hs
  refine ⟨?_, congrArg Prod.snd hs⟩
  rw [← hh]
  exact (foldApps_appsSpine f).symm

/-- Complete raw spine preservation. The function-prefix proof cases are
explicitly excluded using proof_app_function, not ignored as internal roots. -/
theorem raw_rec_spine (su : SortUnique eqEnvT 2)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT 2 Γ) :
    {e t : Expr Nat} → PEqT eqEnvT 2 Γ e t →
    (ls : List Level) → (xs : List (Expr Nat)) → eqNList [one] ls →
    e = foldApps (.const 65 ls) xs →
    ∃ ls' xs', t = foldApps (.const 65 ls') xs' ∧
      xs'.length = xs.length ∧ eqNList [one] ls'
  | _, _, .bvar .., _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, .sort .., _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, .const _ r0 ls0 ls1 hc, ls, xs, hls, heq => by
      have hs := congrArg appsSpine heq
      have hh0 : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      rw [hh0, appsSpine_foldApps_const] at hs
      have hh : Expr.const r0 ls0 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      injection hh with hr hl
      subst r0
      subst ls0
      subst xs
      exact ⟨ls1, [], rfl, rfl, eqNList_trans_local hls hc⟩
  | _, _, .app _ f f' a a' hf _ha, ls, xs, hls, heq => by
      obtain ⟨hhead, hargs⟩ := app_spine_inv heq
      obtain ⟨ls', ys', hf', hlen, hls'⟩ :=
        raw_rec_spine su hΓ hf ls (appsSpine f).2 hls hhead
      refine ⟨ls', ys' ++ [a'], ?_, ?_, hls'⟩
      · rw [hf']
        exact (foldApps_snoc _ _ _).symm
      · have hcount := congrArg List.length hargs
        simp only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add] at hcount ⊢
        omega
  | _, _, .lam .., _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, .pi .., _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, .letE .., _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, .lit .., _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, .proof _ _ _ P _ hP _ hp _, ls, xs, hls, heq => by
      apply False.elim
      apply rec_spine_not_proof su hΓ ls hls xs
      exact ⟨P, ⟨hP⟩, ⟨heq ▸ hp⟩⟩

/-- Complete one-step left-class invariant, at arbitrary carried type T.
This also covers every proper application prefix, so the top-level commonIndex
is never silently assigned to an internal occurrence. -/
theorem step_rec_spine (su : SortUnique eqEnvT 2)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT 2 Γ) :
    {e t T : Expr Nat} →
    (h : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 Γ e t T) →
    F8EtaK.NoEtaKStep h →
    (ls : List Level) → (xs : List (Expr Nat)) → eqNList [one] ls →
    xs.length < 6 → e = foldApps (.const 65 ls) xs →
    ∃ ls' xs', t = foldApps (.const 65 ls') xs' ∧
      xs'.length = xs.length ∧ eqNList [one] ls'
  | _, _, _, .refl .., _, ls, xs, hls, _, heq => ⟨ls, xs, heq, rfl, hls⟩
  | _, _, _, .sortEq .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .consts _ r0 ls0 ls1 _ hc _ _, _, ls, xs, hls, _, heq => by
      have hs := congrArg appsSpine heq
      have hh0 : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      rw [hh0, appsSpine_foldApps_const] at hs
      have hh : Expr.const r0 ls0 = Expr.const 65 ls := congrArg Prod.fst hs
      have hx : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      injection hh with hr hl
      subst r0
      subst ls0
      subst xs
      exact ⟨ls1, [], rfl, rfl, eqNList_trans_local hls hc⟩
  | _, _, _, .bvarZeta .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .delta _ r0 ls0 m _ _ hres hbody _ _ _ _ _, _, ls, _, _, _, heq => by
      have hs := congrArg appsSpine heq
      have hh0 : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      rw [hh0, appsSpine_foldApps_const] at hs
      have hh : Expr.const r0 ls0 = Expr.const 65 ls := congrArg Prod.fst hs
      have hr : r0 = 65 := by injection hh with hr hl
      subst r0
      change some eqRecT = some m at hres
      have hm : m = eqRecT := (Option.some.inj hres).symm
      subst m
      cases hbody
  | _, _, _, .app _ f f' a a' _ _ _ _ _ hf _ _ _ _ha _, hno, ls, xs, hls, hs, heq => by
      obtain ⟨hhead, hargs⟩ := app_spine_inv heq
      have hcount := congrArg List.length hargs
      simp only [List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add] at hcount
      have hsmall : (appsSpine f).2.length < 6 := by omega
      obtain ⟨ls', ys', hf', hlen, hls'⟩ :=
        step_rec_spine su hΓ hf hno.1 ls (appsSpine f).2 hls hsmall hhead
      refine ⟨ls', ys' ++ [a'], ?_, ?_, hls'⟩
      · rw [hf']
        exact (foldApps_snoc _ _ _).symm
      · simp only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add]
        omega
  | _, _, _, .beta .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .lam .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .pi .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .letE .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .zeta .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hi _ _, hno, ls, xs, hls, hs, heq => by
      obtain ⟨ls', xs', hx, hlen, _⟩ :=
        step_rec_spine su hΓ hstep hno ls xs hls hs heq
      exact False.elim (iotaU_not_short hi ls' xs' (by omega) hx)
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _,
      ls, xs, _, hs, heq => False.elim (short_not_K ls xs hs w major heq)
  | _, _, _, .iotaStarKEta .., hno, _, _, _, _, _ => nomatch hno
  | _, _, _, .lit .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .eta .., _, _, _, _, _, heq =>
      by
        have hs := congrArg appsSpine heq
        rw [appsSpine_foldApps_const] at hs
        have hh := congrArg Prod.fst hs
        cases hh
  | _, _, _, .peq _ _ _ _ leaf, _, ls, xs, hls, _, heq =>
      raw_rec_spine su hΓ leaf.1 ls xs hls heq
  | _, _, _, .conv _ _ _ _ _ h _, hno, ls, xs, hls, hs, heq =>
      step_rec_spine su hΓ h hno ls xs hls hs heq

/-- Raw minor-variable preservation under an arbitrary well-formed binder. -/
theorem raw_minor (su : SortUnique eqEnvT 2) (A : Expr Nat)
    (hΓ : CtxWfT eqEnvT 2 (.assumption A :: positiveContext)) :
    {e t : Expr Nat} → PEqT eqEnvT 2 (.assumption A :: positiveContext) e t →
    e = .bvar 1 → t = .bvar 1
  | _, _, .bvar .., heq => heq
  | _, _, .sort .., heq => nomatch heq
  | _, _, .const .., heq => nomatch heq
  | _, _, .app .., heq => nomatch heq
  | _, _, .lam .., heq => nomatch heq
  | _, _, .pi .., heq => nomatch heq
  | _, _, .letE .., heq => nomatch heq
  | _, _, .lit .., heq => nomatch heq
  | _, _, .proof _ _ _ P _ hP _ hp _, heq =>
      False.elim (minor_not_proof su A hΓ ⟨P, ⟨hP⟩, ⟨heq ▸ hp⟩⟩)

/-- Typed variable preservation; conv may change its local index, but cannot
turn the original assumption slot into a let or an ordinary iota source. -/
theorem step_minor (su : SortUnique eqEnvT 2) (A : Expr Nat)
    (hΓ : CtxWfT eqEnvT 2 (.assumption A :: positiveContext)) :
    {e t T : Expr Nat} →
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (.assumption A :: positiveContext) e t T →
    e = .bvar 1 → t = .bvar 1
  | _, _, _, .refl .., heq => heq
  | _, _, _, .sortEq .., heq => nomatch heq
  | _, _, _, .consts .., heq => nomatch heq
  | _, _, _, .bvarZeta _ i _ _ _ _ hg _ _ _, heq => by
      have hi : i = 1 := by injection heq with hi
      subst i
      cases hg
  | _, _, _, .delta .., heq => nomatch heq
  | _, _, _, .app .., heq => nomatch heq
  | _, _, _, .beta .., heq => nomatch heq
  | _, _, _, .lam .., heq => nomatch heq
  | _, _, _, .pi .., heq => nomatch heq
  | _, _, _, .letE .., heq => nomatch heq
  | _, _, _, .zeta .., heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hi _ _, heq => by
      have hm := step_minor su A hΓ hstep heq
      obtain ⟨f, x, hh⟩ := iotaU_source_app hi
      rw [hm] at hh
      cases hh
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq => by
      have hh := heq
      change foldApps (.const w.recRef w.ls) (w.preMajor ++ [major]) = .bvar 1 at hh
      rw [foldApps_snoc] at hh
      cases hh
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., heq => by
      obtain ⟨_, _, happ0⟩ := iotaStarKEta_appParts happ
      nomatch heq.symm.trans happ0
  | _, _, _, .lit .., heq => nomatch heq
  | _, _, _, .eta .., heq => nomatch heq
  | _, _, _, .peq _ _ _ _ leaf, heq => raw_minor su A hΓ leaf.1 heq
  | _, _, _, .conv _ _ _ _ _ h _, heq => step_minor su A hΓ h heq

/-- Loose raw lambdas keep the minor body. The source typing provides the
well-formed LEFT binder context for the raw body comparison. -/
theorem raw_lambda_minor (su : SortUnique eqEnvT 2) :
    {e t T : Expr Nat} → PEqT eqEnvT 2 positiveContext e t →
    HasTyT eqEnvT 2 positiveContext e T → (A : Expr Nat) →
    e = .lam A (.bvar 1) → ∃ A', t = .lam A' (.bvar 1)
  | _, _, _, .bvar .., _, _, heq => nomatch heq
  | _, _, _, .sort .., _, _, heq => nomatch heq
  | _, _, _, .const .., _, _, heq => nomatch heq
  | _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, .lam _ A0 A' b b' _hA hb, hty, A, heq => by
      injection heq with hd hbody
      subst A0
      subst b
      obtain ⟨u, B, hAty, _hbty, _c⟩ := hasTyTInv_lam hty rfl
      have hΓA := CtxWfT.assumption positiveContext A u positiveContextWf hAty
      have he := raw_minor su A hΓA hb rfl
      exact ⟨A', congrArg (Expr.lam A') he⟩
  | _, _, _, .pi .., _, _, heq => nomatch heq
  | _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, .lit .., _, _, heq => nomatch heq
  | _, _, _, .proof _ _ _ P _ hP _ hp _, _, A, heq =>
      False.elim (lambda_minor_not_proof su A ⟨P, ⟨hP⟩, ⟨heq ▸ hp⟩⟩)

/-- Complete right-class invariant. The body stays bvar 1, so the eta source
shape cannot appear later; tracking only the lambda head would not suffice. -/
theorem step_lambda_minor (su : SortUnique eqEnvT 2) :
    {e t T : Expr Nat} →
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext e t T →
    (A : Expr Nat) → e = .lam A (.bvar 1) → ∃ A', t = .lam A' (.bvar 1)
  | _, _, _, .refl .., A, heq => ⟨A, heq⟩
  | _, _, _, .sortEq .., _, heq => nomatch heq
  | _, _, _, .consts .., _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app .., _, heq => nomatch heq
  | _, _, _, .beta .., _, heq => nomatch heq
  | _, _, _, .lam _ A0 A' b b' _ u _ _hc hA _hB hb _hrt, A, heq => by
      injection heq with hd hbody
      subst A0
      subst b
      have hΓA := CtxWfT.assumption positiveContext A u positiveContextWf hA
      have he := step_minor su A hΓA hb rfl
      exact ⟨A', congrArg (Expr.lam A') he⟩
  | _, _, _, .pi .., _, heq => nomatch heq
  | _, _, _, .letE .., _, heq => nomatch heq
  | _, _, _, .zeta .., _, heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hi _ _, A, heq => by
      obtain ⟨A', hm⟩ := step_lambda_minor su hstep A heq
      obtain ⟨f, x, hh⟩ := iotaU_source_app hi
      rw [hm] at hh
      cases hh
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, A, heq => by
      have hh := heq
      change foldApps (.const w.recRef w.ls) (w.preMajor ++ [major]) =
        .lam A (.bvar 1) at hh
      rw [foldApps_snoc] at hh
      cases hh
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, heq => by
      obtain ⟨_, _, happ0⟩ := iotaStarKEta_appParts happ
      nomatch heq.symm.trans happ0
  | _, _, _, .lit .., _, heq => nomatch heq
  | _, _, _, .eta .., _, heq => nomatch heq
  | _, _, _, .peq _ _ _ _ leaf, A, heq =>
      raw_lambda_minor su leaf.1 leaf.2.1 A heq
  | _, _, _, .conv _ _ _ _ _ h _, A, heq => step_lambda_minor su h A heq

/-- Arbitrarily long finite left paths, not a search bound. -/
theorem star_rec_spine (su : SortUnique eqEnvT 2)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT 2 Γ) :
    {e t T : Expr Nat} →
    (hs : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 Γ e t T) →
    F8EtaK.NoEtaKStar hs →
    (ls : List Level) → (xs : List (Expr Nat)) → eqNList [one] ls →
    xs.length < 6 → e = foldApps (.const 65 ls) xs →
    ∃ ls' xs', t = foldApps (.const 65 ls') xs' ∧
      xs'.length = xs.length ∧ eqNList [one] ls'
  | _, _, _, .refl .., _, ls, xs, hls, _, heq => ⟨ls, xs, heq, rfl, hls⟩
  | _, _, _, .tail h hs, hno, ls, xs, hls, hshort, heq => by
      rcases hno with ⟨hno1, hno2⟩
      obtain ⟨ls1, xs1, h1, hn1, hu1⟩ :=
        step_rec_spine su hΓ h hno1 ls xs hls hshort heq
      obtain ⟨ls2, xs2, h2, hn2, hu2⟩ :=
        star_rec_spine su hΓ hs hno2 ls1 xs1 hu1 (by omega) h1
      exact ⟨ls2, xs2, h2, hn2.trans hn1, hu2⟩

/-- Arbitrarily long finite right paths, including changing domain annotations. -/
theorem star_lambda_minor (su : SortUnique eqEnvT 2) :
    {e t T : Expr Nat} →
    ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext e t T →
    (A : Expr Nat) → e = .lam A (.bvar 1) → ∃ A', t = .lam A' (.bvar 1)
  | _, _, _, .refl .., A, heq => ⟨A, heq⟩
  | _, _, _, .tail h hs, A, heq => by
      obtain ⟨A1, h1⟩ := step_lambda_minor su h A heq
      exact star_lambda_minor su hs A1 h1

/-- The exact KEta-free positive A-2 peak's common-reduct proposition. -/
def PositiveJoin : Prop :=
  ∃ z : Expr Nat,
    (∃ hf : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (F8EtaK.partialRec one) z F8EtaK.commonIndex, F8EtaK.NoEtaKStar hf) ∧
    (∃ hg : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      F8EtaK.contracted z F8EtaK.commonIndex, F8EtaK.NoEtaKStar hg)

/-- Specialized form of the future sortRow-lane theorem, with the well-formed
context and environment hypotheses retained verbatim. No instance is supplied. -/
abbrev SortUniquenessOnWfContexts : Prop := SortUnique eqEnvT 2

/-- The premise is sort uniqueness, not SeparationOnWfContexts. -/
def ConditionalNonJoin : Prop := SortUniquenessOnWfContexts → ¬ PositiveJoin

/-- Full conditional non-joinability theorem, using the two disjoint successor
classes. The SU premise is still unprovided; no unconditional non-join is claimed. -/
theorem conditional_nonjoin : ConditionalNonJoin := by
  intro su
  rintro ⟨z, ⟨hf, hno⟩, ⟨hg, _hnoR⟩⟩
  obtain ⟨ls, xs, hz, _hlen, _hu⟩ :=
    star_rec_spine su positiveContextWf hf hno [one]
      [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2]
      ⟨fun _ => rfl, True.intro⟩ (by decide) rfl
  obtain ⟨A, hz'⟩ := star_lambda_minor su hg F8EtaK.domain rfl
  have impossible : Expr.lam A (.bvar 1) = foldApps (.const 65 ls) xs :=
    hz'.symm.trans hz
  have hs := congrArg appsSpine impossible
  rw [appsSpine_foldApps_const] at hs
  have hh := congrArg Prod.fst hs
  cases hh

/-- Repackaging of cc-checked File 2's direct conversion bridge. This is
still NOT a ParRedTStar join; its role here is to refute the CR bridge below. -/
def positive_conversion :
    ConvT eqEnvT 2 positiveContext (F8EtaK.partialRec one)
      F8EtaK.contracted F8EtaK.commonIndex :=
  let hbody : ConvT eqEnvT 2 (.assumption F8EtaK.domain :: positiveContext)
      (.app (lift 0 1 (F8EtaK.partialRec one)) (.bvar 0))
      (.bvar 1) F8EtaK.codomain :=
    convT_instLevels (envWfT_levels F8EtaK.envWf)
      (iotaLevelsT_of_envWfT F8EtaK.envWf) F8EtaK.positive_levels rfl
      (ConvT.trans _ _ _ _ _ eqAppCong eqIotaAtP)
  let hexp : ConvT eqEnvT 2 positiveContext (F8EtaK.expanded one)
      F8EtaK.contracted F8EtaK.commonIndex :=
    .lam positiveContext F8EtaK.domain F8EtaK.domain
      (.app (lift 0 1 (F8EtaK.partialRec one)) (.bvar 0)) (.bvar 1)
      F8EtaK.codomain .zero
      (.refl positiveContext F8EtaK.domain (.sort .zero)
        (F8EtaK.domainTy one F8EtaK.positive_levels)) hbody
  .trans positiveContext (F8EtaK.partialRec one) (F8EtaK.expanded one)
    F8EtaK.contracted F8EtaK.commonIndex
    (.symm positiveContext (F8EtaK.expanded one) (F8EtaK.partialRec one)
      F8EtaK.commonIndex
      (.eta positiveContext (F8EtaK.partialRec one) F8EtaK.domain F8EtaK.codomain
        (F8EtaK.partialRecTy one F8EtaK.positive_levels))) hexp

/-- The exact fixed-context KEta-free conversion-to-common-reduct interface. -/
def ConvToJoinAtPositiveContext : Prop :=
  ∀ {a b T : Expr Nat}, ConvT eqEnvT 2 positiveContext a b T →
    ∃ z : Expr Nat,
      (∃ hf : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext a z T,
        F8EtaK.NoEtaKStar hf) ∧
      (∃ hg : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext b z T,
        F8EtaK.NoEtaKStar hg)

/-- SU rules out the unchanged CR bridge.
That forces a relation repair; it does not license parking A-2 and proceeding. -/
theorem no_unchanged_conversion_join_bridge (su : SortUniquenessOnWfContexts) :
    ¬ ConvToJoinAtPositiveContext :=
  fun cr => conditional_nonjoin su (cr positive_conversion)

end Rcic.Declarative.F8A2Successors

/-! Native audit: every explicit public declaration, including all helpers.
An elaboration placeholder is forbidden; a declared conditional premise is not
an axiom and must remain visible in the theorem's type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [
    ``Rcic.Declarative.F8A2Successors.rec65_K_arity,
    ``Rcic.Declarative.F8A2Successors.rec65_S_arity,
    ``Rcic.Declarative.F8A2Successors.short_not_K,
    ``Rcic.Declarative.F8A2Successors.short_not_S,
    ``Rcic.Declarative.F8A2Successors.iotaU_not_short,
    ``Rcic.Declarative.F8A2Successors.iotaU_source_app,
    ``Rcic.Declarative.F8A2Successors.app_spine_inv,
    ``Rcic.Declarative.F8A2Successors.raw_rec_spine,
    ``Rcic.Declarative.F8A2Successors.step_rec_spine,
    ``Rcic.Declarative.F8A2Successors.raw_minor,
    ``Rcic.Declarative.F8A2Successors.step_minor,
    ``Rcic.Declarative.F8A2Successors.raw_lambda_minor,
    ``Rcic.Declarative.F8A2Successors.step_lambda_minor,
    ``Rcic.Declarative.F8A2Successors.star_rec_spine,
    ``Rcic.Declarative.F8A2Successors.star_lambda_minor,
    ``Rcic.Declarative.F8A2Successors.PositiveJoin,
    ``Rcic.Declarative.F8A2Successors.SortUniquenessOnWfContexts,
    ``Rcic.Declarative.F8A2Successors.ConditionalNonJoin,
    ``Rcic.Declarative.F8A2Successors.conditional_nonjoin,
    ``Rcic.Declarative.F8A2Successors.positive_conversion,
    ``Rcic.Declarative.F8A2Successors.ConvToJoinAtPositiveContext,
    ``Rcic.Declarative.F8A2Successors.no_unchanged_conversion_join_bridge]
  for t in targets do
    unless env.contains t do throwError "Missing declaration {t}"
    let (_, st) := ((CollectAxioms.collect t).run env).run {}
    for ax in st.axioms do
      unless [``propext, ``Quot.sound].contains ax do
        throwError "Forbidden axiom {ax} in {t}"
    for c in st.visited.toList do
      if [`Rcic.Declarative.TypedRowsWf, `Rcic.Declarative.PiRowInjT,
          `Rcic.Declarative.DT012T_type_uniqueness,
          `Rcic.Declarative.DT012T_type_uniqueness_of_typedRowsWf].contains c then
        throwError "Unexpected global row/type-uniqueness dependency {c} in {t}"
    logInfo m!"{t}: {st.axioms}"
  logInfo m!"A2_CONDITIONAL_AUDIT: {targets.length} names; premise remains explicit"
