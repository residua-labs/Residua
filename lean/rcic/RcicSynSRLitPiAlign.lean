import rcic.RcicSynSRLitPiCLW
import rcic.RcicSynYes
import rcic.RcicSynClosedZeta
import rcic.RcicTypedStrengthen

/-!
# `RcicSynSRLitPiAlign` — row 4 slot alignment: the per-arm `RoutedDisp` induction

cc-SR2 handoff item: finish the decomposition of `ClwBvarValueConeW` so that
every remaining piece is either an issued IH edge, an already-landed `eps_*`
equation, or ONE named `Prop`.

The old `ZetaSlotAlignW` (∃ `hvR` whose `epsW` matches `resolve ρ i`) hides
two distinct debts. Splitting them:

* **`ZetaSlotAlignEW`** (§1): `resolve ρ i` is the **old `eps`** of SOME
  routing-carried derivation of the stored value — proved by induction on
  `RoutedDisp`. `canon` is the landed tower equation
  `resolve_ctxP_disp_lookupValue`; `assumption`/`letDrop`/`letInline`/`cctx`
  are structural (cons lookup inversion + `wkAtZero`/`wkLetAtZero` + the
  landed `eps_wk_*`/`wkLetAtZero_eps_*`/`eps_tyCast*` transport equations);
  `wk`/`esub`/`linst`/`ewk` are the named inverse-transport residuals —
  the `RoutedDisp` spine runs premise→conclusion opposite to `TyP`'s
  transports (`TyP.wk` sends Γ → `insertAt d c Γ`; `RoutedDisp.wk` routes a
  display at `Γ` from one at `insertAt d c Γ`), so the produced derivation
  must be transported BACK along each spine step. `ZetaSlotEwkArmW` is the
  display side of the row-1 (B) environment-strengthening obstacle.
* **`EpsEpsWPairW`** (§2): the one named Prop left after the alignment —
  `eps` of the carried derivation vs `epsW` of the supplied one, same
  subject, same routed display. It fuses the `eps`-side same-subject
  coherence with the `eps`↔`epsW` wedge leg; the ∀-form is refuted off-cone
  (the `wkZetaNode` wedge), so its inhabited demand is exactly the
  on-cone instances the wall consumes.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 the canon tower's `eps` IS `resolve` at the slot -/

/-- The `ctxP_lookupValue_ty` tower (a `wkAtZero`/`wkLetAtZero` chain over the
    `CtxP`-carried value typing) erases, at the canonical display, to exactly
    `resolve` of the slot: each cons step either passes through a non-`keep`
    head entry (`drop`/`inline`) or re-lands the `keep` lift that `resolve`
    applies at a kept slot. Structural — no uniqueness input. -/
theorem resolve_ctxP_disp_lookupValue {E : ResolvedEnv} {n : Nat} (σ : Level → Level) :
    ∀ {Γ : LCtx} (C : CtxP E n Γ) {i : Nat} {v A : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A),
      resolve (C.disp σ) i = (ctxP_lookupValue_ty C hval hty).eps σ (C.disp σ)
  | _, .nil _ _, _, _, _, hval, _ => by
      simp [lookupValue] at hval
  | _, .assumption _ _ _ _ _ _ _, 0, _, _, hval, _ => by
      simp [lookupValue] at hval
  | _, .assumption _ _ _ A₀ u₀ hC hA₀, i + 1, v, A, hval, hty => by
      dsimp only [ctxP_lookupValue_ty]
      cases lookupValue_cons_succ_inv hval with
      | mk v₀ hlv hv_eq =>
      cases lookupType_cons_succ_inv hty with
      | mk A₀' hlt hA_eq =>
      rw [eps_tyCast]
      cases hb : levelIsZero (σ u₀) with
      | true =>
          rw [disp_assumption_drop hb]
          show resolve (hC.disp σ) i =
            (wkAtZero (ctxP_lookupValue_ty hC hlv hlt)).eps σ (.drop :: hC.disp σ)
          rw [wkAtZero, eps_tyCastCtx,
            eps_wk_not_keep (hk := Or.inr (Or.inl (by simp [List.get?_cons_zero]))),
            removeAt_zero]
          exact resolve_ctxP_disp_lookupValue σ hC hlv hlt
      | false =>
          rw [disp_assumption_keep hb]
          show (resolve (hC.disp σ) i).lift 0 1 =
            (wkAtZero (ctxP_lookupValue_ty hC hlv hlt)).eps σ (.keep :: hC.disp σ)
          rw [wkAtZero, eps_tyCastCtx, eps_wk_keep (hk := by simp), removeAt_zero]
          show (resolve (hC.disp σ) i).lift 0 1 =
            ((ctxP_lookupValue_ty hC hlv hlt).eps σ (hC.disp σ)).lift 0 1
          rw [resolve_ctxP_disp_lookupValue σ hC hlv hlt]
  | _, .letBinding _ _ _ A₀ _ v₀ hC hA₀ hv₀, 0, v, A, hval, hty => by
      dsimp only [ctxP_lookupValue_ty]
      show hv₀.eps σ (hC.disp σ) =
        (tyCast (lookupValue_cons_zero_letBinding hval)
          (lookupType_cons_zero_letBinding hty) (wkLetAtZero hv₀)).eps σ
          (.inline (hv₀.eps σ (hC.disp σ)) :: hC.disp σ)
      rw [eps_tyCast, wkLetAtZero_eps_inline]
  | _, .letBinding _ _ _ A₀ _ v₀ hC hA₀ hv₀, i + 1, v, A, hval, hty => by
      dsimp only [ctxP_lookupValue_ty]
      cases lookupValue_cons_succ_inv hval with
      | mk v₀' hlv hv_eq =>
      cases lookupType_cons_succ_inv hty with
      | mk A₀' hlt hA_eq =>
      rw [eps_tyCast]
      show resolve (hC.disp σ) i =
        (wkLetAtZero (ctxP_lookupValue_ty hC hlv hlt)).eps σ
          (.inline (hv₀.eps σ (hC.disp σ)) :: hC.disp σ)
      rw [wkLetAtZero, eps_tyCastCtx,
        eps_wk_not_keep (hk := Or.inr (Or.inr
          ⟨TyP.eps σ (hC.disp σ) hv₀, by simp [List.get?_cons_zero]⟩)),
        removeAt_zero]
      exact resolve_ctxP_disp_lookupValue σ hC hlv hlt

/-! ## §1 the eps-side alignment and its five named residuals -/

/-- Head-slot weakening inversion: a `lift 0 1`-image subject typed under a
    cons'd head decl descends to a typing of the un-lifted subject in the
    tail. Needed to feed the induction hypothesis at the binder arms
    (`assumption`/`letDrop`/`letInline` at `i+1`): the wall's own `hv` lives
    at the cons context, the IH at the tail. -/
def ZetaSlotHeadUnwkW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (d : LocalDecl) {e T : Expr Nat},
    TyP E n (d :: Γ) (lift 0 1 e) T → ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T')

/-- The eps-side slot alignment, conditioned on the wall's own value typing
    (the `∃` would be vacuously refutable at an untypeable stored value —
    the wall's `hv` is exactly what rules that out). -/
def ZetaSlotAlignEW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {v A : Expr Nat},
    lookupValue Γ i = some v → lookupType Γ i = some A →
    ∀ {T : Expr Nat}, TyP E n Γ v T →
    ∀ {σ : Level → Level} {ρ : List Disp}, RoutedDisp σ E n Γ ρ →
    ∃ (A' : Expr Nat) (hvR : TyP E n Γ v A'),
      resolve ρ i = hvR.eps σ ρ

/-- `wk`-arm residual: the `RoutedDisp` premise is a display at the weakened
    context `insertAt d c Γ`; the slot obligation at `Γ` demands a derivation
    BACK at `Γ` whose `eps` still matches the lifted-resolve — the
    `wk`-inversion content. -/
def ZetaSlotWkArmW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ' : List Disp}
    (d : LocalDecl) (c : Nat), RoutedDisp σ E n (insertAt d c Γ) ρ' →
    ∀ {i : Nat} {v A : Expr Nat}, lookupValue Γ i = some v →
      lookupType Γ i = some A → ∀ {T : Expr Nat}, TyP E n Γ v T →
      ∃ (A' : Expr Nat) (hvR : TyP E n Γ v A'),
        resolve (removeAt ρ' c) i = hvR.eps σ (removeAt ρ' c)

/-- `esub`-arm residual: premise display at `substRemove vₛ j Γ`; slot
    obligation back at `Γ` under the inserted `binderDisp`. The arm carries
    the replacement typings `hvS`/`hvT` (so the inner side is
    forward-constructible via `TyP.esub`); what remains is the
    un-substitution of the produced derivation plus the `insertDisp`
    bookkeeping. -/
def ZetaSlotEsubArmW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ' : List Disp}
    {t vₛ : Expr Nat} {j : Nat} {u : Level}
    (hget : Γ[j]? = some (.assumption t))
    (hvS : TyP E n (substRemove vₛ j Γ) (lift 0 j vₛ) (lift 0 j t))
    (hvT : TyP E n (substRemove vₛ j Γ) (lift 0 j t) (.sort u)),
    RoutedDisp σ E n (substRemove vₛ j Γ) ρ' →
    ∀ {i : Nat} {v A : Expr Nat}, lookupValue Γ i = some v →
      lookupType Γ i = some A → ∀ {T : Expr Nat}, TyP E n Γ v T →
      ∃ (A' : Expr Nat) (hvR : TyP E n Γ v A'),
        resolve (insertDisp (binderDisp (levelIsZero (σ u))) j ρ') i =
          hvR.eps σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ')

/-- `linst`-arm residual: premise display at `instLvlsCtx ls Γ` and arity `n`;
    slot obligation back at arity `a'` under the composite level map — the
    un-instantiation content. -/
def ZetaSlotLinstArmW : Prop :=
  ∀ {E : ResolvedEnv} {n a' : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a'),
    RoutedDisp σ E n (instLvlsCtx ls Γ) ρ →
    ∀ {i : Nat} {v A : Expr Nat}, lookupValue Γ i = some v →
      lookupType Γ i = some A → ∀ {T : Expr Nat}, TyP E a' Γ v T →
      ∃ (A' : Expr Nat) (hvR : TyP E a' Γ v A'),
        resolve ρ i = hvR.eps (fun l => σ (instLevel ls l)) ρ

/-- `ewk`-arm residual: premise display routed through the extension `E`;
    slot obligation demands a derivation at the SOURCE env `E₀` — the
    environment-strengthening content (the (B) obstacle, display side). -/
def ZetaSlotEwkArmW : Prop :=
  ∀ {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    (hext : EnvExt E₀ E), RoutedDisp σ E n Γ ρ →
    ∀ {i : Nat} {v A : Expr Nat}, lookupValue Γ i = some v →
      lookupType Γ i = some A → ∀ {T : Expr Nat}, TyP E₀ n Γ v T →
      ∃ (A' : Expr Nat) (hvR : TyP E₀ n Γ v A'),
        resolve ρ i = hvR.eps σ ρ

/-- The alignment, by `RoutedDisp` induction: `canon` is the §0 tower
    equation; the cons arms (`assumption`, `letDrop`, `letInline`) consume
    `ZetaSlotHeadUnwkW` to feed the IH and re-land the `keep`-lift via
    `eps_wk_*`; `cctx` transports both directions through `TyP.cctx` +
    `CvP.symm`; the four transport arms are discharged by their named
    residuals. -/
theorem zetaSlotAlignEW_of_residuals
    (hHead : ZetaSlotHeadUnwkW) (hWk : ZetaSlotWkArmW) (hEsub : ZetaSlotEsubArmW)
    (hLinst : ZetaSlotLinstArmW) (hEwk : ZetaSlotEwkArmW) : ZetaSlotAlignEW := by
  intro E n Γ i v A hval hty T hv σ ρ hρ
  induction hρ generalizing i v A T with
  | canon C =>
      exact ⟨A, ctxP_lookupValue_ty C hval hty,
        resolve_ctxP_disp_lookupValue _ C hval hty⟩
  | assumption hρ' hA₀ ih =>
      rename_i σ' E' n' Δ ρ' A₀' u₀
      cases i with
      | zero => simp [lookupValue] at hval
      | succ i' =>
          obtain ⟨v₀, hval', hv_eq⟩ := lookupValue_cons_succ_inv hval
          obtain ⟨A₀, hty', hA_eq⟩ := lookupType_cons_succ_inv hty
          obtain ⟨T', ⟨hvΔ⟩⟩ := hHead (.assumption A₀') (tyCast hv_eq.symm rfl hv)
          obtain ⟨A'', hvR', hEq⟩ := ih hval' hty' hvΔ
          refine ⟨lift 0 1 A'', tyCast hv_eq rfl (wkAtZero hvR'), ?_⟩
          cases hb : levelIsZero (σ' u₀) with
          | true =>
              rw [binderDisp_drop]
              show resolve ρ' i' =
                (tyCast hv_eq rfl (wkAtZero hvR')).eps σ' (.drop :: ρ')
              rw [eps_tyCast, wkAtZero, eps_tyCastCtx,
                eps_wk_not_keep (hk := Or.inr (Or.inl (by simp))), removeAt_zero]
              exact hEq
          | false =>
              rw [binderDisp_keep]
              show (resolve ρ' i').lift 0 1 =
                (tyCast hv_eq rfl (wkAtZero hvR')).eps σ' (.keep :: ρ')
              rw [eps_tyCast, wkAtZero, eps_tyCastCtx,
                eps_wk_keep (hk := by simp), removeAt_zero]
              show (resolve ρ' i').lift 0 1 = (hvR'.eps σ' ρ').lift 0 1
              rw [hEq]
  | letDrop hρ' hA₀ hv₀ hstar ih =>
      rename_i σ' E' n' Δ ρ' A₀ v₀ u₀
      cases i with
      | zero =>
          have hv_eq := lookupValue_cons_zero_letBinding hval
          refine ⟨lift 0 1 A₀, tyCast hv_eq rfl (wkLetAtZero hv₀), ?_⟩
          show .star = (tyCast hv_eq rfl (wkLetAtZero hv₀)).eps σ' (.drop :: ρ')
          rw [eps_tyCast, wkLetAtZero_eps_drop, hstar]
      | succ i' =>
          obtain ⟨v₀', hval', hv_eq⟩ := lookupValue_cons_succ_inv hval
          obtain ⟨A₀', hty', hA_eq⟩ := lookupType_cons_succ_inv hty
          obtain ⟨T', ⟨hvΔ⟩⟩ := hHead (.letBinding A₀ v₀) (tyCast hv_eq.symm rfl hv)
          obtain ⟨A'', hvR', hEq⟩ := ih hval' hty' hvΔ
          refine ⟨lift 0 1 A'', tyCast hv_eq rfl (wkLetAtZero hvR'), ?_⟩
          show resolve ρ' i' =
            (tyCast hv_eq rfl (wkLetAtZero hvR')).eps σ' (.drop :: ρ')
          rw [eps_tyCast, wkLetAtZero_eps_drop]
          exact hEq
  | letInline hρ' hA₀ hv₀ ih =>
      rename_i σ' E' n' Δ ρ' A₀ v₀ u₀
      cases i with
      | zero =>
          have hv_eq := lookupValue_cons_zero_letBinding hval
          refine ⟨lift 0 1 A₀, tyCast hv_eq rfl (wkLetAtZero hv₀), ?_⟩
          show hv₀.eps σ' ρ' =
            (tyCast hv_eq rfl (wkLetAtZero hv₀)).eps σ'
              (.inline (TyP.eps σ' ρ' hv₀) :: ρ')
          rw [eps_tyCast, wkLetAtZero_eps_inline]
      | succ i' =>
          obtain ⟨v₀', hval', hv_eq⟩ := lookupValue_cons_succ_inv hval
          obtain ⟨A₀', hty', hA_eq⟩ := lookupType_cons_succ_inv hty
          obtain ⟨T', ⟨hvΔ⟩⟩ := hHead (.letBinding A₀ v₀) (tyCast hv_eq.symm rfl hv)
          obtain ⟨A'', hvR', hEq⟩ := ih hval' hty' hvΔ
          refine ⟨lift 0 1 A'', tyCast hv_eq rfl (wkLetAtZero hvR'), ?_⟩
          show resolve ρ' i' =
            (tyCast hv_eq rfl (wkLetAtZero hvR')).eps σ'
              (.inline (TyP.eps σ' ρ' hv₀) :: ρ')
          rw [eps_tyCast, wkLetAtZero, eps_tyCastCtx,
            eps_wk_not_keep (hk := Or.inr (Or.inr
              ⟨TyP.eps σ' ρ' hv₀, by simp⟩)), removeAt_zero]
          exact hEq
  | wk d c hρ' ih =>
      exact hWk d c hρ' hval hty hv
  | esub hget hvS hvT hρ' ih =>
      exact hEsub hget hvS hvT hρ' hval hty hv
  | linst ls hls hlen hρ' ih =>
      exact hLinst ls hls hlen hρ' hval hty hv
  | ewk hext hρ' ih =>
      exact hEwk hext hρ' hval hty hv
  | cctx hA hρ' ih =>
      rename_i σ' E' n' Δ ρ' A₀ A' u₀
      cases i with
      | zero => simp [lookupValue] at hval
      | succ i' =>
          obtain ⟨v₀', hvalΓ, hv_eq⟩ := lookupValue_cons_succ_inv hval
          obtain ⟨A₀', htyΓ, hA_eq⟩ := lookupType_cons_succ_inv hty
          have hval' : lookupValue (.assumption A' :: Δ) (i' + 1) = some v := by
            rw [lookupValue_cons_succ, hvalΓ, Option.map_some', hv_eq]
          have hty' : lookupType (.assumption A' :: Δ) (i' + 1) = some A := by
            rw [lookupType_cons_succ, htyΓ, Option.map_some', hA_eq]
          obtain ⟨A'', hvR', hEq⟩ :=
            ih hval' hty' (TyP.cctx _ _ _ _ _ _ _ _ hv hA)
          refine ⟨A'', TyP.cctx _ _ _ _ _ _ _ _ hvR'
            (CvP.symm _ _ _ _ _ _ hA hA.dr hA.dl), ?_⟩
          rw [eps_cctx]
          exact hEq

/-! ## §2 the one named Prop left: the `eps`/`epsW` pair -/

/-- **The row-4 residual after alignment**: the carried derivation's old
    `eps` and the supplied derivation's `epsW` agree on the same subject at
    a routed display. This is `TypingEpsCoherenceW` with the left side
    evaluated under the OLD erasure — the `eps`↔`epsW` wedge leg fused with
    same-subject coherence. (The ∀-form is refuted off-cone at a
    `wk`-over-`keep` display with an `inline` below the `keep` — the
    `wkZetaNode` wedge; the consumed instances are the ones the routed cone
    actually produces.) -/
def EpsEpsWPairW (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    {σ : Level → Level} (_hσ : LevelHom σ) {ρ : List Disp},
    RoutedDisp σ E n Γ ρ →
    ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ) (D₂.epsW σ ρ)

/-- Row 4, fully decomposed: the structural `eps`-side alignment (§1, five
    structural arms + five named transport residuals) plus ONE named pair
    Prop. Each remaining piece is an issued edge, a landed `eps_*` equation,
    or a named residual. -/
theorem clwBvarValueConeW_of_alignE_pair {E : ResolvedEnv} (hW : EnvWfT E)
    (align : ZetaSlotAlignEW) (pair : EpsEpsWPairW (tableOfI hW)) :
    ClwBvarValueConeW (tableOfI hW) := by
  intro E' n Γ i A v hval hty hv dl dr σ hσ ρ hρ hu
  obtain ⟨A', hvR, hres⟩ := align hval hty hv hρ
  have hc : ConvMod (EStep (tableOfI hW)) LvlEq
      (hvR.eps σ ρ) (hv.epsW σ ρ) := pair hvR hv hσ hρ
  have hs : (zetaLocalBvarSurface hty dl).epsW σ ρ = resolve ρ i :=
    zetaLocalBvarSurface_epsW_resolve hty dl hu
  unfold CLWx
  rw [hs, hres]
  exact hc

#print axioms Rcic.Syn.resolve_ctxP_disp_lookupValue
#print axioms Rcic.Syn.zetaSlotAlignEW_of_residuals
#print axioms Rcic.Syn.clwBvarValueConeW_of_alignE_pair

/-! ## §3 (B) the env-position alternative — ONE erased-side Prop

cc's row-1 internal alternative: extend the closer's rank by an
environment-position component, so a query on a member's declared type at
its admission prefix `E₀` becomes a strictly smaller ordinary IH edge of
the SAME closer (lexicographic on member index, then the derivation key).
What that leaves on the erasure side is exactly ONE proposition: an
`epsW` computed from a derivation at the ambient env `E'`, whose subject
mentions only constants the prefix `E₀` already carries (`constsBelow k`),
is `ConvMod`-equal to the `epsW` of SOME derivation at the prefix.

`EpsWPrefixNormW` is that Prop. It is NOT a special case of
`TypingEpsCoherenceW` — that wall quantifies both derivations at the SAME
env; here the two sides live at `E'` and `E₀` with `EnvExt E₀ E'`. It is
also the typing-level face of `ZetaSlotEwkArmW` (§1): the `RoutedDisp.ewk`
arm needs the produced derivation to live at the source env. At
`tableOfI` the Prop is measured neither proved nor refuted; the inhabited
on-cone instance below pins the statement to a real cone point (the
diagonal prefix `E₀ = E'` is honest: `k = 0` makes `constsBelow` vacuous on
a const-free subject). -/

/-- **(B) the env-prefix erasure-normalization obligation, as ONE Prop.** -/
def EpsWPrefixNormW : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) {E₀ E' : ResolvedEnv} (hext : EnvExt E₀ E')
    {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP E' n Γ e T) {k : Nat}
    (_hb : Rcic.Scm.SrcG.constsBelow k e = true)
    (_hk : ∀ {r : Nat}, r < k → (E₀.members r).isSome = true)
    {σ : Level → Level} (_hσ : LevelHom σ) {ρ : List Disp}
    (_hρ : RoutedDisp σ E' n Γ ρ),
    ∃ (T₀ : Expr Nat) (D₀ : TyP E₀ n Γ e T₀),
      ConvMod (EStep (tableOfI hW)) LvlEq (D.epsW σ ρ) (D₀.epsW σ ρ)

/-- The inhabited on-cone instance of `EpsWPrefixNormW`'s conclusion shape:
    premises inhabited at `E₀ = E' = emptyEnv`, `Γ = []`, `e = .sort .zero`
    (const-free), `σ = id` (a `LevelHom`), `ρ = []` routed by `canon` of
    `CtxP.nil`; the conclusion is a `ConvMod.refl`. -/
theorem epsWPrefixNormW_onCone_inst :
    ∃ (T₀ : Expr Nat) (D₀ : TyP emptyEnv 0 [] (.sort .zero) T₀),
      ConvMod (EStep (tableOfI EnvWfT.empty)) LvlEq
        ((TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)).epsW id [])
        (D₀.epsW id []) :=
  ⟨_, TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _), ConvMod.refl _⟩

#print axioms Rcic.Syn.EpsWPrefixNormW
#print axioms Rcic.Syn.epsWPrefixNormW_onCone_inst

/-! ## §4 (cc 11:30Z) on-cone instances of the six residuals

Search result, per cc's order, before writing anything new: the only landed
strengthening is `hasTyT_strengthen` for the TYPED judgment `HasTyT`
(`RcicTypedStrengthen`), and the `TyP → HasTyT` bridge is itself the named
unlanded wall `TyPEraseW` (RcicSynSRLitPiCLW §B1). No `TyP`-level weakening
inversion (`ZetaSlotHeadUnwkW`), substitution/level-instantiation/env
inversion exists on the tree; the per-constructor eps transport lemmas that
WOULD compose with them (`eps_wk_rel_*` at arbitrary position,
`eps_esub_keep`/`eps_esub_drop`, `eps_linst`, `eps_ewk`, `resolve_removeAt_*`,
`resolve_insertDisp_*`, `eps_dropStarEq`) are landed but pair a transported
derivation with a transported display — the missing half is always the
inverse-typed derivation, i.e. the same (B)-cluster strengthening obstacle.

So each of the five residuals is pinned below by an inhabited ON-CONE
instance: `σ = id` (a `LevelHom` by `levelHom_id`), `RoutedDisp` by `canon`
of a real `CtxP` (a `Demand` root — `Demand.rootCl`/`rootEs` sit exactly at
`S.can σ`), and all slot premises inhabited. Every measurement point uses
`Γ₁ := [let x := .sort 0 : .sort 1]` so `lookupValue/lookupType 0` return
`some (.sort .zero)/some (.sort (.succ .zero))` by `rfl`. -/

/-- (1a) `ZetaSlotHeadUnwkW` on-cone: head `letBinding`, `e = .sort .zero`
    (lift-invariant), `D` the sort rule — inhabited at every sort leaf, no
    ctx-wf premise needed. -/
theorem zetaSlotHeadUnwkW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (d : LocalDecl) (e T : Expr Nat)
      (_ : TyP E n (d :: Γ) (lift 0 1 e) T),
      ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T') :=
  ⟨emptyEnv, 0, [], .letBinding (.sort (.succ .zero)) (.sort .zero),
    .sort .zero, .sort (.succ .zero),
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-- (1b) `ZetaSlotWkArmW` on-cone: `Γ₁` weakened at `c = 1` by
    `.assumption (.sort .zero)`; the premise display is the canon display of
    the weakened context (`[.inline (.sort .zero), .keep]`); `removeAt _ 1`
    re-reads slot 0's inline payload `.sort .zero`, matched by the sort
    rule's `eps`. -/
theorem zetaSlotWkArmW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (σ : Level → Level) (ρ' : List Disp)
      (d : LocalDecl) (c : Nat) (_ : LevelHom σ)
      (_ : RoutedDisp σ E n (insertAt d c Γ) ρ')
      (i : Nat) (v A T : Expr Nat) (_ : lookupValue Γ i = some v)
      (_ : lookupType Γ i = some A) (_ : TyP E n Γ v T),
      ∃ (A' : Expr Nat) (hvR : TyP E n Γ v A'),
        resolve (removeAt ρ' c) i = hvR.eps σ (removeAt ρ' c) :=
  ⟨emptyEnv, 0, [.letBinding (.sort (.succ .zero)) (.sort .zero)], id,
    (CtxP.letBinding emptyEnv 0 [.assumption (.sort .zero)]
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      (CtxP.assumption emptyEnv 0 [] (.sort .zero) (.succ .zero)
        (CtxP.nil emptyEnv 0)
        (TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)))
      (TyP.sort emptyEnv 0 [.assumption (.sort .zero)]
        (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
      (TyP.sort emptyEnv 0 [.assumption (.sort .zero)]
        .zero (.succ .zero) (eqN_refl _))).disp id,
    .assumption (.sort .zero), 1, levelHom_id,
    RoutedDisp.canon _,
    0, .sort .zero, .sort (.succ .zero), .sort (.succ .zero),
    rfl, rfl, TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _), rfl⟩

/-- (1c) `ZetaSlotEsubArmW` on-cone: `Γ₂ = [.assumption s1, let x := s0 : s1]`,
    `j = 0` removes the head assumption (`substRemove` drops index 0);
    `insertDisp .keep 0` re-adds a keep head, slot 1 resolves through it to
    the let-inline payload `.sort .zero`. -/
theorem zetaSlotEsubArmW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (σ : Level → Level) (ρ' : List Disp)
      (t vₛ : Expr Nat) (j : Nat) (u : Level)
      (_ : Γ[j]? = some (.assumption t))
      (_ : TyP E n (substRemove vₛ j Γ) (lift 0 j vₛ) (lift 0 j t))
      (_ : TyP E n (substRemove vₛ j Γ) (lift 0 j t) (.sort u))
      (_ : LevelHom σ) (_ : RoutedDisp σ E n (substRemove vₛ j Γ) ρ')
      (i : Nat) (v A T : Expr Nat) (_ : lookupValue Γ i = some v)
      (_ : lookupType Γ i = some A) (_ : TyP E n Γ v T),
      ∃ (A' : Expr Nat) (hvR : TyP E n Γ v A'),
        resolve (insertDisp (binderDisp (levelIsZero (σ u))) j ρ') i =
          hvR.eps σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ') :=
  ⟨emptyEnv, 0, [.assumption (.sort (.succ .zero)),
      .letBinding (.sort (.succ .zero)) (.sort .zero)], id,
    (CtxP.letBinding emptyEnv 0 []
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      (CtxP.nil emptyEnv 0)
      (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
      (TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _))).disp id,
    .sort (.succ .zero), .sort .zero, 0, .succ (.succ .zero),
    rfl,
    TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _),
    TyP.sort emptyEnv 0 _ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _),
    levelHom_id, RoutedDisp.canon _,
    1, .sort .zero, .sort (.succ .zero), .sort (.succ .zero),
    rfl, rfl, TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _), rfl⟩

/-- (1d) `ZetaSlotLinstArmW` on-cone: `n = a' = 1`, `ls = [.zero]`
    (`levelsBounded` trivially true on a const level), `instLvlsCtx` leaves
    the const-level context untouched; the composite `σ ∘ instLevel ls`
    maps `.zero` to `.zero`. -/
theorem zetaSlotLinstArmW_onCone :
    ∃ (E : ResolvedEnv) (n a' : Nat) (Γ : LCtx) (σ : Level → Level) (ρ : List Disp)
      (ls : List Level) (_ : levelsBounded n ls = true) (_ : ls.length = a')
      (_ : RoutedDisp σ E n (instLvlsCtx ls Γ) ρ)
      (i : Nat) (v A T : Expr Nat) (_ : lookupValue Γ i = some v)
      (_ : lookupType Γ i = some A) (_ : TyP E a' Γ v T),
      ∃ (A' : Expr Nat) (hvR : TyP E a' Γ v A'),
        resolve ρ i = hvR.eps (fun l => σ (instLevel ls l)) ρ :=
  ⟨emptyEnv, 1, 1, [.letBinding (.sort (.succ .zero)) (.sort .zero)], id,
    (CtxP.letBinding emptyEnv 1 []
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      (CtxP.nil emptyEnv 1)
      (TyP.sort emptyEnv 1 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
      (TyP.sort emptyEnv 1 [] .zero (.succ .zero) (eqN_refl _))).disp id,
    [.zero], rfl, rfl, RoutedDisp.canon _,
    0, .sort .zero, .sort (.succ .zero), .sort (.succ .zero),
    rfl, rfl, TyP.sort emptyEnv 1 _ .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    TyP.sort emptyEnv 1 _ .zero (.succ .zero) (eqN_refl _), rfl⟩

/-- (1e) `ZetaSlotEwkArmW` on-cone: the diagonal `E₀ = E = emptyEnv`
    (`envExt_refl`); the real content is OFF-diagonal and is exactly the
    (B) `EpsWPrefixNormW` wall. -/
theorem zetaSlotEwkArmW_onCone :
    ∃ (E₀ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (σ : Level → Level) (ρ : List Disp)
      (_ : EnvExt E₀ E) (_ : RoutedDisp σ E n Γ ρ)
      (i : Nat) (v A T : Expr Nat) (_ : lookupValue Γ i = some v)
      (_ : lookupType Γ i = some A) (_ : TyP E₀ n Γ v T),
      ∃ (A' : Expr Nat) (hvR : TyP E₀ n Γ v A'),
        resolve ρ i = hvR.eps σ ρ :=
  ⟨emptyEnv, emptyEnv, 0, [.letBinding (.sort (.succ .zero)) (.sort .zero)], id,
    (CtxP.letBinding emptyEnv 0 []
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      (CtxP.nil emptyEnv 0)
      (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
      (TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _))).disp id,
    envExt_refl emptyEnv, RoutedDisp.canon _,
    0, .sort .zero, .sort (.succ .zero), .sort (.succ .zero),
    rfl, rfl, TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _), rfl⟩

/-- (2) `EpsEpsWPairW` on-cone: identical sort derivations at the empty
    canon display. The ∀-form is NOT the canon-display erasure agreement
    `clwBvarValueConeW_canon` generalised — the landed canon results are for
    the SPECIFIC ctxP-carried derivation pair (`zl_res_convW_canon`), not an
    arbitrary same-subject pair; a `RoutedDisp` induction on the pair would
    hit the same four inverse-transport arms plus an eps↔epsW commutation on
    `wk` nodes. On-cone instance: `D₁ = D₂ = sort`, `ρ = []` (canon `nil`),
    `σ = id`, `ConvMod.refl`. -/
theorem epsEpsWPairW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T₁ T₂ : Expr Nat)
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
      (σ : Level → Level) (_ : LevelHom σ) (ρ : List Disp)
      (_ : RoutedDisp σ E n Γ ρ),
      ConvMod (EStep (tableOfI EnvWfT.empty)) LvlEq
        (D₁.eps σ ρ) (D₂.epsW σ ρ) :=
  ⟨emptyEnv, 0, [], .sort .zero, .sort (.succ .zero), .sort (.succ .zero),
    TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _),
    TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _),
    id, levelHom_id, [], RoutedDisp.canon (CtxP.nil emptyEnv 0),
    ConvMod.refl _⟩

#print axioms Rcic.Syn.zetaSlotHeadUnwkW_onCone
#print axioms Rcic.Syn.zetaSlotWkArmW_onCone
#print axioms Rcic.Syn.zetaSlotEsubArmW_onCone
#print axioms Rcic.Syn.zetaSlotLinstArmW_onCone
#print axioms Rcic.Syn.zetaSlotEwkArmW_onCone
#print axioms Rcic.Syn.epsEpsWPairW_onCone
