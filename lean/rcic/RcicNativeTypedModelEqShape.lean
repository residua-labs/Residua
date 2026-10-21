import rcic.RcicNativeTypedModelEqArity
import rcic.RcicNativeValleyDecoTransfer
import rcic.RcicNativeWallProducer

/-!
# The Eq-gap shape-disjointness rows from the named CR package

`EqGapArityRows` (`RcicNativeTypedModelEqArity`) asks for three premises:
`piRow` (Π-injectivity of `TyConvT`) and the two shape-disjointness
directions `pi_famApp` / `famApp_pi` between `.pi` and `const 63`-headed
family applications.  This module discharges all three from **one**
confluence package

    EqGapShapeCR = { leaf : LeafIface, diamond : CDiamond,
                     sortUniq : SortUniq }

— exactly the input `PiRowField` itself consumes
(`piRow_of_diamond_sortUniq`), so `EqGapArityRows` depends on `piRow`'s
own wall and nothing more.

The famApp head-inversion is the audit's (Gemini lane 4, #7772)
kernel-checked construction:

* `peq` is dead on `const 63`-headed sources.  Every partial or
  saturated `Eq` application `foldApps (.const 63 ls) ys`
  (`ys.length ≤ 3`) types at a Π-telescope or sort whose sort-index is
  ≥ 1 — the innermost codomain `.sort .zero` of `eqFamT.mtype` is itself
  `Sort 1`-sorted, so `Eq α`, `Eq α a`, … never inhabit a `Prop`-index —
  and over-applications are ill-typed (the residual `sort 0` cannot
  convert to a `pi`).  `peq_famApp_source_false` discharges the leaf by
  spine inversion plus the level arithmetic of
  `eval_imax_ne_zero_of_right`.
* With `peq` fenced, every `ParRedT`/`ParRedTStar` step out of a
  `const 63`-headed spine preserves the head: `delta` dies on
  `eqFamT.body = none`, the `iotaStarK`/`DerivedIotaU` majors need a
  recursor-headed spine while `eqFamT.mclass = .inductiveM`, and the
  congruence cases keep the head pointwise
  (`parRedT_famApp_head_inv`, `parRedTStar_famApp_head_inv`).
* Both disjointness rows then collapse `TyConvT` to a `CValley` at a
  sort index and clash: the `.pi` leg's centre is `.pi`-headed
  (`cstar_pi_inv_of_zsc`), the famApp leg's is `const 63`-headed
  (`parRedTStar_famApp_head_inv`) — impossible at one centre
  (`eqGapArityRows_of_shapeCR`).

`closure_claim = 0`; nothing is fabricated.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelEqShapeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit TypedModelKFailureAudit
open TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2InputsAudit ReadbackCK2GapAudit
open PiProbeRelIotaAudit
open TypedModelEqArityAudit

variable {n : Nat} {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The named discharge package for all three `EqGapArityRows` rows:
    the same `{LeafIface, CDiamond, SortUniq}` confluence input
    `PiRowField` consumes (`piRow_of_diamond_sortUniq`). -/
structure EqGapShapeCR (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type where
  /-- The leaf interface `valleyOf_diamond` and the inversions consume. -/
  leaf : LeafIface eqEnvT n PEq
  /-- The same-index certified diamond — the CR input proper. -/
  diamond : CDiamond eqEnvT n PEq
  /-- Sort uniqueness of one term's two sortings. -/
  sortUniq : SortUniq eqEnvT n

/-- `SortUniq` specializes to `ZeroSortCoherence` at `eqEnvT`. -/
def EqGapShapeCR.zsc (cr : EqGapShapeCR n PEq) : HostPropAudit.ZeroSortCoherence eqEnvT n :=
  zsc_of_sortUniq cr.sortUniq

/-- `SortUniq` yields `SortRetype` at `eqEnvT`. -/
def EqGapShapeCR.sr (cr : EqGapShapeCR n PEq) : SortRetype eqEnvT n :=
  sortRetype_of_sortUniq cr.sortUniq

/-- The package yields full `PiInj` at `eqEnvT`. -/
def EqGapShapeCR.piInj (cr : EqGapShapeCR n PEq) : PiInj eqEnvT n :=
  piInj_of_diamond_sortUniq pinEqGroupWfT cr.leaf cr.diamond cr.sortUniq

/-- The package yields `SortCoh` at `eqEnvT`. -/
theorem EqGapShapeCR.sortCoh (cr : EqGapShapeCR n PEq) : SortCoh eqEnvT n :=
  sortCoh_of_diamond_sortUniq pinEqGroupWfT cr.leaf cr.diamond cr.sortUniq

/-- The package yields typing uniqueness `Uniq` at `eqEnvT`. -/
noncomputable def EqGapShapeCR.uniq (cr : EqGapShapeCR n PEq) : Uniq eqEnvT n :=
  uniq_of_piInj_sortUniq pinEqGroupWfT cr.piInj cr.sortUniq

/-- The package discharges `EqGapArityRows.piRow` — literally the same
    derivation `piRow_of_diamond_sortUniq`, instantiated at `eqEnvT`. -/
theorem EqGapShapeCR.piRowD (cr : EqGapShapeCR n PEq) : PiRowField eqEnvT n :=
  piRow_of_diamond_sortUniq pinEqGroupWfT cr.leaf cr.diamond cr.sortUniq

/-! ### sort↔Π disjointness (clean pair, CR package only) -/

/-- `.pi` and `.sort` sources have airtight `ParRedT` head-inversions
    (`peq` is dead on both), so the valley's common centre cannot be
    both headed. -/
theorem not_tyConvT_pi_sort_of_shapeCR (cr : EqGapShapeCR n PEq)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {A B : Expr Nat} {u : Level} :
    ¬ Nonempty (TyConvT eqEnvT n Γ (.pi A B) (.sort u)) := by
  intro ⟨h⟩
  match tyConvT_firstOf_data h with
  | .inl heq => exact Expr.noConfusion heq
  | .inr ⟨_, w, hc₀, _⟩ =>
      let hPi : HasTyT eqEnvT n Γ (.pi A B) (.sort w) :=
        (convEnds pinEqGroupWfT hΓ hc₀).1
      let V := cvalley_of_tyConvT_of_sortUniq pinEqGroupWfT cr.leaf
        cr.diamond cr.sortUniq hΓ hPi h
      let ⟨_, _, hhead, _, _⟩ := cstar_pi_inv_of_zsc pinEqGroupWfT cr.leaf
        cr.zsc hΓ V.left
      let ⟨_, hhead', _⟩ := cstar_sort_inv_of_zsc pinEqGroupWfT cr.leaf
        cr.zsc hΓ V.right
      rw [hhead] at hhead'
      exact Expr.noConfusion hhead'

/-- The mirror of `not_tyConvT_pi_sort_of_shapeCR`. -/
theorem not_tyConvT_sort_pi_of_shapeCR (cr : EqGapShapeCR n PEq)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {A B : Expr Nat} {u : Level} :
    ¬ Nonempty (TyConvT eqEnvT n Γ (.sort u) (.pi A B)) := by
  intro ⟨h⟩
  match tyConvT_firstOf_data h with
  | .inl heq => exact Expr.noConfusion heq
  | .inr ⟨_, w, hc₀, _⟩ =>
      let hS : HasTyT eqEnvT n Γ (.sort u) (.sort w) :=
        (convEnds pinEqGroupWfT hΓ hc₀).1
      let V := cvalley_of_tyConvT_of_sortUniq pinEqGroupWfT cr.leaf
        cr.diamond cr.sortUniq hΓ hS h
      let ⟨_, hhead, _⟩ := cstar_sort_inv_of_zsc pinEqGroupWfT cr.leaf
        cr.zsc hΓ V.left
      let ⟨_, _, hhead', _, _⟩ := cstar_pi_inv_of_zsc pinEqGroupWfT cr.leaf
        cr.zsc hΓ V.right
      rw [hhead] at hhead'
      exact Expr.noConfusion hhead'

/-! ### `peq` is dead on `const 63` sources (audit lane 4, kernel-checked) -/

theorem eval_imax_ne_zero_of_right {u v w : Level}
    (hv : eval (fun _ => none) v ≠ some 0)
    (heqw : eqN (.imax u v) w) :
    eval (fun _ => none) w ≠ some 0 := by
  intro hw0
  have hρ := heqw (fun _ => none)
  rw [hw0] at hρ
  dsimp [eval] at hρ
  cases hu : eval (fun _ => none) u <;> cases hv' : eval (fun _ => none) v
  · simp [hu, hv'] at hρ
  · rename_i b
    cases b with
    | zero => exact hv hv'
    | succ b' => simp [hu, hv'] at hρ
  · simp [hu, hv'] at hρ
  · rename_i a b
    cases b with
    | zero => exact hv hv'
    | succ b' =>
      simp [hu, hv'] at hρ
      omega

theorem hasTyT_sort_not_sort0
    (sc : SortCoh eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {u : Level}
    (h : HasTyT eqEnvT n Γ (.sort u) (.sort .zero)) : False := by
  have c := hasTyTInv_sortT h rfl
  have heq : eqN (.succ u) .zero := sc hΓ c
  have hρ := heq (fun _ => none)
  change (eval (fun _ => none) u).map (fun k => k + 1) = some 0 at hρ
  cases hu : eval (fun _ => none) u <;> simp [hu] at hρ

theorem hasTyT_pi1_level_ne_zero
    (sc : SortCoh eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {A : Expr Nat} {w : Level}
    (h : HasTyT eqEnvT n Γ (.pi A (.sort .zero)) (.sort w)) :
    eval (fun _ => none) w ≠ some 0 := by
  obtain ⟨u, v, hA, hB, c⟩ := hasTyTInv_pi h rfl
  have hΓA : CtxWfT eqEnvT n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
  have heqv : eqN (.succ .zero) v := sc hΓA (hasTyTInv_sortT hB rfl)
  have hv1 : eval (fun _ => none) v ≠ some 0 := by
    have hρ := heqv (fun _ => none)
    intro h0; rw [h0] at hρ; contradiction
  exact eval_imax_ne_zero_of_right hv1 (sc hΓ c)

theorem hasTyT_pi2_level_ne_zero
    (sc : SortCoh eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {A B : Expr Nat} {w : Level}
    (h : HasTyT eqEnvT n Γ (.pi A (.pi B (.sort .zero))) (.sort w)) :
    eval (fun _ => none) w ≠ some 0 := by
  obtain ⟨u, v, hA, hB, c⟩ := hasTyTInv_pi h rfl
  have hΓA : CtxWfT eqEnvT n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
  have hv1 := hasTyT_pi1_level_ne_zero sc hΓA hB
  exact eval_imax_ne_zero_of_right hv1 (sc hΓ c)

theorem hasTyT_pi3_level_ne_zero
    (sc : SortCoh eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {A B C : Expr Nat} {w : Level}
    (h : HasTyT eqEnvT n Γ (.pi A (.pi B (.pi C (.sort .zero)))) (.sort w)) :
    eval (fun _ => none) w ≠ some 0 := by
  obtain ⟨u, v, hA, hB, c⟩ := hasTyTInv_pi h rfl
  have hΓA : CtxWfT eqEnvT n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
  have hv1 := hasTyT_pi2_level_ne_zero sc hΓA hB
  exact eval_imax_ne_zero_of_right hv1 (sc hΓ c)

theorem eqEnvT_mem_63 : eqEnvT.members 63 = some eqFamT := by
  simp [eqEnvT, eqPrefixT, eqFamEnvT, extendEnv, emptyEnv]

/-- No `PEq` leaf can have a `const 63`-headed source at `eqEnvT`:
    the family's type `Π (α : Sort 1)(a b : α), Prop` sorts every
    saturated/partial application at level ≥ 1 (the codomain `.sort .zero`
    is itself `Sort 1`-sorted), contradicting `L.prop : HasTyT T (.sort .zero)`;
    over-applications are ill-typed by sort↔Π disjointness. -/
theorem peq_famApp_source_false
    (L : LeafIface eqEnvT n PEq) (D : CDiamond eqEnvT n PEq) (su : SortUniq eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ)
    {ls : List Level} {ys : List (Expr Nat)} {q T : Expr Nat}
    (h : PEq Γ (foldApps (.const 63 ls) ys) q T) : False := by
  have hty := (L.typed h).1
  have hT0 := L.prop h
  have zsc : HostPropAudit.ZeroSortCoherence eqEnvT n := zsc_of_sortUniq su
  have sc : SortCoh eqEnvT n := sortCoh_of_diamond_sortUniq pinEqGroupWfT L D su
  have piRow : PiRowField eqEnvT n := piRow_of_diamond_sortUniq pinEqGroupWfT L D su
  match ys with
  | [] =>
      have ⟨⟨_, _, _, hc⟩⟩ := hasTyT_spineInv_rows pinEqGroupWfT piRow hΓ eqEnvT_mem_63
        (doms := []) (U := eqFamT.mtype) rfl [] rfl hty
      have h0 := HostPropAudit.sort_transport0_data pinEqGroupWfT zsc hΓ hc.symmT hT0
      exact hasTyT_pi3_level_ne_zero sc hΓ h0 rfl
  | [x0] =>
      have ⟨⟨_, _, _, hc⟩⟩ := hasTyT_spineInv_rows pinEqGroupWfT piRow hΓ eqEnvT_mem_63
        (doms := [.sort (.succ .zero)])
        (U := .pi (.bvar 0) (.pi (.bvar 1) (.sort .zero))) rfl [x0] rfl hty
      have h0 := HostPropAudit.sort_transport0_data pinEqGroupWfT zsc hΓ hc.symmT hT0
      exact hasTyT_pi2_level_ne_zero sc hΓ h0 rfl
  | [x0, x1] =>
      have ⟨⟨_, _, _, hc⟩⟩ := hasTyT_spineInv_rows pinEqGroupWfT piRow hΓ eqEnvT_mem_63
        (doms := [.sort (.succ .zero), .bvar 0])
        (U := .pi (.bvar 1) (.sort .zero)) rfl [x0, x1] rfl hty
      have h0 := HostPropAudit.sort_transport0_data pinEqGroupWfT zsc hΓ hc.symmT hT0
      exact hasTyT_pi1_level_ne_zero sc hΓ h0 rfl
  | [x0, x1, x2] =>
      have ⟨⟨_, _, _, hc⟩⟩ := hasTyT_spineInv_rows pinEqGroupWfT piRow hΓ eqEnvT_mem_63
        (doms := [.sort (.succ .zero), .bvar 0, .bvar 1])
        (U := .sort .zero) rfl [x0, x1, x2] rfl hty
      have h0 := HostPropAudit.sort_transport0_data pinEqGroupWfT zsc hΓ hc.symmT hT0
      exact hasTyT_sort_not_sort0 sc hΓ h0
  | x0 :: x1 :: x2 :: x3 :: rest =>
      have hsplit : foldApps (.const 63 ls) (x0 :: x1 :: x2 :: x3 :: rest) =
          foldApps (foldApps (.const 63 ls) [x0, x1, x2]) (x3 :: rest) := rfl
      obtain ⟨A, B, ⟨hf⟩⟩ := Rcic.Syn.hasTyT_foldApps_prefix_pi
        (f := foldApps (.const 63 ls) [x0, x1, x2]) (hsplit ▸ hty) rfl
      have ⟨⟨_, _, _, hc⟩⟩ := hasTyT_spineInv_rows pinEqGroupWfT piRow hΓ eqEnvT_mem_63
        (doms := [.sort (.succ .zero), .bvar 0, .bvar 1])
        (U := .sort .zero) rfl [x0, x1, x2] rfl hf
      exact not_tyConvT_sort_pi_of_shapeCR ⟨L, D, su⟩ hΓ ⟨hc⟩

/-! ### the famApp head-inversions (audit lane 4, kernel-checked) -/

/-- `DerivedIotaU` cannot have a `const 63`-headed source: the redex's
    head is a *recursor* member while `eqEnvT.members 63 = eqFamT` is
    `.inductiveM`. -/
theorem derivedIotaU_famApp_head_false {lhs rhs : Expr Nat} {ls : List Level}
    (h : DerivedIotaU eqEnvT lhs rhs) (hhd : (appsSpine lhs).1 = .const 63 ls) : False := by
  cases h with
  | ofU w =>
      change (appsSpine (foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]))).1 = .const 63 ls at hhd
      rw [appsSpine_foldApps_const] at hhd
      injection hhd with hr _
      have hm := w.hrec
      rw [hr, eqEnvT_mem_63] at hm
      injection hm with hm'
      have hmc := w.hrecK
      rw [← hm'] at hmc
      exact nomatch hmc
  | ofUS w =>
      change (appsSpine (foldApps (.const w.recRef w.ls)
        (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]))).1 = .const 63 ls at hhd
      rw [appsSpine_foldApps_const] at hhd
      injection hhd with hr _
      have hm := w.hrec
      rw [hr, eqEnvT_mem_63] at hm
      injection hm with hm'
      have hmc := w.hrecK
      rw [← hm'] at hmc
      exact nomatch hmc

/-- Every `ParRedT` step out of a `const 63`-headed spine preserves the
    `const 63` head at `eqEnvT` (under the CR package). -/
theorem parRedT_famApp_head_inv
    (L : LeafIface eqEnvT n PEq) (D : CDiamond eqEnvT n PEq) (su : SortUniq eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ)
    {a b T : Expr Nat} (p : ParRedT PEq eqEnvT n Γ a b T) :
    ∀ {ls : List Level},
      (appsSpine a).1 = .const 63 ls →
      ∃ ls', (appsSpine b).1 = .const 63 ls' := by
  induction p with
  | refl _ _ _ _ =>
      intro ls heq; exact ⟨ls, heq⟩
  | sortEq _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | consts _ r ls₀ ls' _ _ _ _ =>
      intro ls heq
      change Expr.const r ls₀ = Expr.const 63 ls at heq
      injection heq with hr _
      subst hr
      exact ⟨ls', rfl⟩
  | bvarZeta _ _ _ _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | delta _ r ls₀ m b₀ _ hres hbody _ _ _ _ _ =>
      intro ls heq
      change Expr.const r ls₀ = Expr.const 63 ls at heq
      injection heq with hr _
      rw [hr, eqEnvT_mem_63] at hres
      injection hres with hm
      subst hm
      exact nomatch hbody
  | app _ f f' x x' _ _ _ _ _ _ _ _ _ _ _ ihf _ =>
      intro ls heq
      change (appsSpine f).1 = .const 63 ls at heq
      change ∃ ls', (appsSpine f').1 = .const 63 ls'
      exact ihf hΓ heq
  | beta _ A body _ arg _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro ls heq
      change (appsSpine (.lam A body)).1 = .const 63 ls at heq
      exact nomatch heq
  | lam _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | pi _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | iotaSpine _ _ _ _ _ _ hI _ _ ih =>
      intro ls heq
      obtain ⟨ls', hlhs'⟩ := ih hΓ heq
      exact (derivedIotaU_famApp_head_false hI hlhs').elim
  | iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro ls heq
      change (appsSpine (foldApps (.const w.recRef w.ls) (w.preMajor ++ [major]))).1 = .const 63 ls at heq
      rw [appsSpine_foldApps_const] at heq
      injection heq with hr _
      have hm := w.hrec
      rw [hr, eqEnvT_mem_63] at hm
      injection hm with hm'
      have hmc := w.hrecK
      rw [← hm'] at hmc
      exact nomatch hmc
  | iotaStarKEta _ w _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro ls heq
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      injection hhd with hr _
      have hm := w.hrec
      rw [← hr, eqEnvT_mem_63] at hm
      injection hm with hm'
      have hmc := w.hrecK
      rw [← hm'] at hmc
      exact nomatch hmc
  | lit _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | eta _ _ _ _ _ _ _ =>
      intro _ heq; exact nomatch heq
  | peq _ p _ _ h =>
      intro ls heq
      have hp : p = foldApps (.const 63 ls) (appsSpine p).2 := by
        have hsp := (foldApps_appsSpine p).symm
        rw [heq] at hsp
        exact hsp
      rw [hp] at h
      exact (peq_famApp_source_false L D su hΓ h).elim
  | conv _ _ _ _ _ _ _ ih =>
      intro ls heq
      exact ih hΓ heq

/-- The star version: every `ParRedTStar` out of a `const 63`-headed
    spine preserves the `const 63` head. -/
theorem parRedTStar_famApp_head_inv
    (L : LeafIface eqEnvT n PEq) (D : CDiamond eqEnvT n PEq) (su : SortUniq eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ)
    {a b T : Expr Nat} (s : ParRedTStar PEq eqEnvT n Γ a b T) :
    ∀ {ls : List Level},
      (appsSpine a).1 = .const 63 ls →
      ∃ ls', (appsSpine b).1 = .const 63 ls' := by
  induction s with
  | refl _ _ _ =>
      intro ls heq; exact ⟨ls, heq⟩
  | tail step _ ih =>
      intro ls heq
      obtain ⟨ls₁, hmid⟩ := parRedT_famApp_head_inv L D su hΓ step heq
      exact ih hmid

/-- No `ConvT` at `eqEnvT` (any index) steps a `const 63`-headed family
    application onto a `.pi`: the valley's famApp leg keeps the
    `const 63` head while the `.pi` leg keeps `.pi`. -/
theorem eqFamConvShape_of_triple
    (L : LeafIface eqEnvT n PEq) (D : CDiamond eqEnvT n PEq) (su : SortUniq eqEnvT n)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) {ls : List Level}
    {ys : List (Expr Nat)} {b T : Expr Nat}
    (hc : ConvT eqEnvT n Γ (foldApps (.const 63 ls) ys) b T)
    {A B : Expr Nat} : b ≠ .pi A B := by
  intro hpi
  have V := valleyOf_diamond pinEqGroupWfT L D hΓ hc
  have hhd_a : (appsSpine (foldApps (.const 63 ls) ys)).1 = .const 63 ls := by
    rw [appsSpine_foldApps_const]
  obtain ⟨ls', hhd_c⟩ := parRedTStar_famApp_head_inv L D su hΓ V.left.forget hhd_a
  subst hpi
  let ⟨A', B', hpi_c, _, _⟩ := cstar_pi_inv_of_zsc pinEqGroupWfT L (zsc_of_sortUniq su) hΓ V.right
  rw [hpi_c] at hhd_c
  exact nomatch hhd_c

/-- Kernel-checked reduction (audit lane 4): `EqGapArityRows n` follows
    from the 3-field CR package `{LeafIface, CDiamond, SortUniq}` alone —
    `piRow`'s own wall and nothing more. -/
theorem eqGapArityRows_of_shapeCR (cr : EqGapShapeCR n PEq) :
    EqGapArityRows n where
  piRow := cr.piRowD
  pi_famApp := fun {Γ} hΓ {A B ls ys} ⟨h⟩ => by
    match tyConvT_firstOf_data h with
    | .inl heq =>
        exact (TypedModelAudit.foldApps_const_ne_pi ys A B) heq.symm
    | .inr ⟨_, u, hc₀, _⟩ =>
        let hPi : HasTyT eqEnvT n Γ (.pi A B) (.sort u) :=
          (convEnds pinEqGroupWfT hΓ hc₀).1
        let V := cvalley_of_tyConvT_of_sortUniq pinEqGroupWfT cr.leaf
          cr.diamond cr.sortUniq hΓ hPi h
        let ⟨_, _, hpi_c, _, _⟩ := cstar_pi_inv_of_zsc pinEqGroupWfT cr.leaf
          cr.zsc hΓ V.left
        have hhd : (appsSpine (foldApps (.const 63 ls) ys)).1 = .const 63 ls := by
          rw [appsSpine_foldApps_const]
        obtain ⟨ls', hhd_c⟩ := parRedTStar_famApp_head_inv cr.leaf cr.diamond
          cr.sortUniq hΓ V.right.forget hhd
        rw [hpi_c] at hhd_c
        exact nomatch hhd_c
  famApp_pi := fun {Γ} hΓ {A B ls ys} ⟨h⟩ => by
    match tyConvT_firstOf_data h with
    | .inl heq =>
        exact (TypedModelAudit.foldApps_const_ne_pi ys A B) heq
    | .inr ⟨_, u, hc₀, _⟩ =>
        let hF : HasTyT eqEnvT n Γ (foldApps (.const 63 ls) ys) (.sort u) :=
          (convEnds pinEqGroupWfT hΓ hc₀).1
        let V := cvalley_of_tyConvT_of_sortUniq pinEqGroupWfT cr.leaf
          cr.diamond cr.sortUniq hΓ hF h
        have hhd : (appsSpine (foldApps (.const 63 ls) ys)).1 = .const 63 ls := by
          rw [appsSpine_foldApps_const]
        obtain ⟨ls', hhd_c⟩ := parRedTStar_famApp_head_inv cr.leaf cr.diamond
          cr.sortUniq hΓ V.left.forget hhd
        let ⟨_, _, hpi_c, _, _⟩ := cstar_pi_inv_of_zsc pinEqGroupWfT cr.leaf
          cr.zsc hΓ V.right
        rw [hpi_c] at hhd_c
        exact nomatch hhd_c

#print axioms EqGapShapeCR
#print axioms EqGapShapeCR.zsc
#print axioms EqGapShapeCR.sr
#print axioms EqGapShapeCR.piInj
#print axioms EqGapShapeCR.sortCoh
#print axioms EqGapShapeCR.uniq
#print axioms EqGapShapeCR.piRowD
#print axioms not_tyConvT_pi_sort_of_shapeCR
#print axioms not_tyConvT_sort_pi_of_shapeCR
#print axioms eval_imax_ne_zero_of_right
#print axioms hasTyT_sort_not_sort0
#print axioms hasTyT_pi1_level_ne_zero
#print axioms hasTyT_pi2_level_ne_zero
#print axioms hasTyT_pi3_level_ne_zero
#print axioms eqEnvT_mem_63
#print axioms peq_famApp_source_false
#print axioms derivedIotaU_famApp_head_false
#print axioms parRedT_famApp_head_inv
#print axioms parRedTStar_famApp_head_inv
#print axioms eqFamConvShape_of_triple
#print axioms eqGapArityRows_of_shapeCR

end Rcic.Declarative.NativeValleys.TypedModelEqShapeAudit
