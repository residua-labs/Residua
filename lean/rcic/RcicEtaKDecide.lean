import rcic.RcicEtaKHeadInvariant
import rcic.RcicDT0709EnvWf
import rcic.RcicProofOccurrences
import rcic.RcicHeadStepT
import rcic.RcicPEqLeafTIntro
import rcic.RcicParRedDiamond
import rcic.RcicF8OMA1
import rcic.RcicF8OMEtaKAnnot

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# A-2 Steps 2 & 3 — Proof-root exclusion from sort uniqueness and the A-2 decision

Given uniqueness of the sort of a type (`EnvWfT E → CtxWfT E n Γ →
HasTyT E n Γ T (.sort u) → HasTyT E n Γ T (.sort v) → eqN u v`, passed as an
explicit named premise in theorem signatures and never hidden inside a
definition):
1. `TyConvT` preserves sort levels up to `eqN` (`tyConvT_sort_transfer`,
   `tyConvT_sort_eqN_of_sortUniq`), which immediately discharges
   `separationAt_of_sortUniq` and excludes root `PEqT.proof` steps at
   `commonIndex` (`no_proof_root_commonIndex_of_sortUniq`).
2. Pulling `.sort .zero` back across `HasTyT.app` (`hasTyT_app_sort_zero_inv`,
   `hasTyT_foldApps_sort_zero_inv`) without `piRow` shows that any application
   spine `foldApps f xs` typed at a `Prop` forces `f` itself to have a type
   whose sort evaluates to `0`. Since `eqRecT.mtype` instantiated at `[one]`
   has sort evaluating to `2 ≠ 0`, `HasConst65ProofRoot eqEnvT 2 Γ [one] k` is
   impossible at every spine length `k` (`no_const65_proof_root_of_sortUniq`).
3. Symmetrically, `.bvar 1` under `.assumption A :: positiveContext` has lookup
   type `lift 0 2 (instantiateLevels [one] eqMinorT) : .sort one`, whose sort
   evaluates to `1 ≠ 0`, excluding `HasContractedProofRoot`
   (`no_contracted_proof_root_of_sortUniq`).
4. Combining with `RcicEtaKHeadInvariant` yields `conditionalNonJoin` and
   `conditionalNonModuloJoin`, while `positive_conversion` exhibits
   `ConvT eqEnvT 2 positiveContext (partialRec one) contracted commonIndex`.

No `ParRedT` rule is changed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8EtaK

abbrev one : Level := .succ .zero
abbrev oneAlt : Level := .max (.succ .zero) .zero
abbrev positiveContext : LCtx := ctx one

/-! ## Step 2a: Sort transfer across `TyConvT` from sort uniqueness -/

/-- Forward sort transfer across a `TyConvT` chain from sort uniqueness and
    `convT_endpoints` (DT-009 at `EnvWfT`). -/
theorem tyConvT_sort_transfer {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ →
      HasTyT E n Γ T (.sort u) →
      HasTyT E n Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat}
    (hc : TyConvT E n Γ A B) {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) :
    ∃ w : Level, eqN u w ∧ Nonempty (HasTyT E n Γ B (.sort w)) := by
  induction hc generalizing u with
  | refl _ =>
      exact ⟨u, eqN_refl u, ⟨hA⟩⟩
  | of _ _ w hconv =>
      obtain ⟨⟨hAw⟩, ⟨hBw⟩⟩ := convT_endpoints hW hΓ hconv
      exact ⟨w, hSortUniq hΓ hA hAw, ⟨hBw⟩⟩
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨w₁, huw₁, ⟨hBw₁⟩⟩ := ih1 hA
      obtain ⟨w₂, hw₁w₂, hCw₂⟩ := ih2 hBw₁
      exact ⟨w₂, eqN_trans huw₁ hw₁w₂, hCw₂⟩

/-- Two sort-typed endpoints of a `TyConvT` chain have `=ₙ` sorts under sort
    uniqueness. -/
theorem tyConvT_sort_eqN_of_sortUniq {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ →
      HasTyT E n Γ T (.sort u) →
      HasTyT E n Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n Γ B (.sort v))
    (hc : TyConvT E n Γ A B) : eqN u v := by
  obtain ⟨w, huw, ⟨hBw⟩⟩ := tyConvT_sort_transfer hW hSortUniq hΓ hc hA
  exact eqN_trans huw (hSortUniq hΓ hBw hB)

/-- Sort-vs-Prop separation (`SeparationAt`) derived from sort uniqueness:
    no `.sort l` can be `TyConvT` to a `Prop` (`P : .sort .zero`). -/
theorem separationAt_of_sortUniq {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ →
      HasTyT E n Γ T (.sort u) →
      HasTyT E n Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hc : TyConvT E n Γ (.sort l) P) : False := by
  have heq : eqN (.succ l) .zero :=
    tyConvT_sort_eqN_of_sortUniq hW hSortUniq hΓ (.sort Γ l) hP hc
  have h0 := heq (fun _ => some 0)
  cases h : eval (fun _ => some 0) l with
  | none =>
      simp [eval, h, Option.map] at h0
  | some k =>
      simp [eval, h, Option.map] at h0

/-- Root proof-root exclusion at `commonIndex` in `positiveContext`:
    `commonIndex` cannot be typed at `.sort .zero` because `positive_index_sort`
    types `commonIndex` at `.sort (.imax .zero (.succ .zero))` (sort value 1). -/
theorem no_proof_root_commonIndex_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    (h0 : HasTyT eqEnvT 2 positiveContext commonIndex (.sort .zero)) : False := by
  have heq := hSortUniq (contextWf one positive_levels) positive_index_sort h0
  have hval := heq (fun _ => some 0)
  cases hval

/-! ## Step 2b: Pulling `.sort .zero` back across `HasTyT.app` and `foldApps` -/

theorem eval_imax_of_eq_zero {ρ : Nat → Option Nat} {u v : Level}
    (hv : eval ρ v = some 0) : eval ρ (.imax u v) = some 0 := by
  simp [eval, hv]

/-- If `.app f a : T` and `T : .sort w` with `eval ρ w = some 0`, then `f` has a
    Π-type `T_f` with `T_f : .sort w_f` and `eval ρ w_f = some 0`.
    Uses only `hasTyTInv_app`, `DT007T_typing_regularity_of_envWfT`,
    `hasTyTInv_pi`, `hasTyT_subst0_of_envWfT`, and `tyConvT_sort_eqN_of_sortUniq`
    (no `piRow`). -/
theorem hasTyT_app_sort_zero_inv {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ →
      HasTyT E n Γ T (.sort u) →
      HasTyT E n Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ : Nat → Option Nat}
    {f a T : Expr Nat} {w : Level}
    (happ : HasTyT E n Γ (.app f a) T)
    (hT : HasTyT E n Γ T (.sort w))
    (hw : eval ρ w = some 0) :
    ∃ (T_f : Expr Nat) (w_f : Level),
      eval ρ w_f = some 0 ∧
      Nonempty (HasTyT E n Γ T_f (.sort w_f)) ∧
      Nonempty (HasTyT E n Γ f T_f) := by
  obtain ⟨A, B, hf, ha, hc⟩ := hasTyTInv_app happ rfl
  obtain ⟨w_pi, ⟨hpi⟩⟩ := DT007T_typing_regularity_of_envWfT hW hΓ hf
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
  have hinst : HasTyT E n Γ (instantiate0 a B) (.sort v) :=
    hasTyT_subst0_of_envWfT hW hB ha
  have hvw : eqN v w :=
    tyConvT_sort_eqN_of_sortUniq hW hSortUniq hΓ hinst hT hc
  have hv0 : eval ρ v = some 0 := (hvw ρ).trans hw
  exact ⟨.pi A B, .imax u v, eval_imax_of_eq_zero hv0,
    ⟨.pi Γ A u B v hA hB⟩, ⟨hf⟩⟩

/-- Iterating `hasTyT_app_sort_zero_inv` along any spine `foldApps f xs`: if the
    applied spine has a type whose sort evaluates to `0`, then the head `f`
    itself has a type whose sort evaluates to `0`. -/
theorem hasTyT_foldApps_sort_zero_inv {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ →
      HasTyT E n Γ T (.sort u) →
      HasTyT E n Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ : Nat → Option Nat}
    (xs : List (Expr Nat)) {f T : Expr Nat} {w : Level}
    (h : HasTyT E n Γ (foldApps f xs) T)
    (hT : HasTyT E n Γ T (.sort w))
    (hw : eval ρ w = some 0) :
    ∃ (T₀ : Expr Nat) (w₀ : Level),
      eval ρ w₀ = some 0 ∧
      Nonempty (HasTyT E n Γ T₀ (.sort w₀)) ∧
      Nonempty (HasTyT E n Γ f T₀) := by
  induction xs generalizing f T w with
  | nil =>
      exact ⟨T, w, hw, ⟨hT⟩, ⟨h⟩⟩
  | cons x ys ih =>
      obtain ⟨T₁, w₁, hw₁, ⟨hT₁⟩, ⟨hfx⟩⟩ :=
        ih (f := .app f x) h hT hw
      exact hasTyT_app_sort_zero_inv hW hSortUniq hΓ hfx hT₁ hw₁

/-! ## Step 2c: Explicit sort-typing of `eqRecT.mtype` and left-side proof-root exclusion -/

private abbrev eqRecCtx5 : LCtx :=
  .assumption (.bvar 3) :: eqJoinCtx.tail

private abbrev eqRecDom5 : Expr Nat :=
  foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]

private abbrev eqRecCtx6 : LCtx :=
  .assumption eqRecDom5 :: eqRecCtx5

private def eqRecDom5Ty : HasTyT eqEnvT 1 eqRecCtx5 eqRecDom5 (.sort .zero) :=
  let h0 := HasTyT.const (E := eqEnvT) (n := 1) eqRecCtx5 63 [] eqFamT rfl rfl rfl
  let h1 := HasTyT.app _ _ _ _ _ h0 (.bvar eqRecCtx5 4 _ rfl)
  let h2 := HasTyT.app _ _ _ _ _ h1 (.bvar eqRecCtx5 3 _ rfl)
  HasTyT.app _ _ _ _ _ h2 (.bvar eqRecCtx5 0 _ rfl)

private def eqRecBody6Ty :
    HasTyT eqEnvT 1 eqRecCtx6
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
      (.sort (.param 0)) :=
  let hM : HasTyT eqEnvT 1 eqRecCtx6 (.bvar 3)
      (.pi (.bvar 5)
        (.pi (foldApps (.const 63 []) [.bvar 6, .bvar 5, .bvar 0])
          (.sort (.param 0)))) :=
    .bvar eqRecCtx6 3 _ rfl
  let hb : HasTyT eqEnvT 1 eqRecCtx6 (.bvar 1) (.bvar 5) :=
    .bvar eqRecCtx6 1 _ rfl
  let hp : HasTyT eqEnvT 1 eqRecCtx6 (.bvar 0)
      (foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 1]) :=
    .bvar eqRecCtx6 0 _ rfl
  let hMb := HasTyT.app _ _ _ _ _ hM hb
  HasTyT.app _ _ _ _ _ hMb hp

/-- The explicit sort of `eqRecT.mtype` at `n = 1` in `[]`. -/
abbrev eqRecSort : Level :=
  .imax (.succ (.succ .zero))
    (.imax (.succ .zero)
      (.imax (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))
        (.imax (.param 0)
          (.imax (.succ .zero) (.imax .zero (.param 0))))))

/-- Explicit sort-typing derivation for `eqRecT.mtype` in the empty context. -/
def eqRecMtypeTy : HasTyT eqEnvT 1 [] eqRecT.mtype (.sort eqRecSort) :=
  .pi [] (.sort (.succ .zero)) (.succ (.succ .zero)) _ _
    (.sort [] (.succ .zero))
    (.pi _ (.bvar 0) (.succ .zero) _ _
      Rcic.kgATy
      (.pi _ eqMotT _ _ _
        Rcic.kgMotTy
        (.pi _ eqMinorT (.param 0) _ _
          Rcic.kgMinorTy
          (.pi _ (.bvar 3) (.succ .zero) _ _
            (.bvar eqJoinCtx.tail 3 _ rfl)
            (.pi _ eqRecDom5 .zero _ (.param 0)
              eqRecDom5Ty eqRecBody6Ty)))))

theorem eval_instLevel_eqRecSort_of_eqN_one {ls : List Level}
    (hls : eqNList ls [one]) :
    eval (fun _ => some 0) (instLevel ls eqRecSort) = some 2 := by
  cases ls with
  | nil => cases hls
  | cons l₀ rest =>
      cases rest with
      | cons _ _ => cases hls.2
      | nil =>
          have hl₀ : eval (fun _ => some 0) l₀ = some 1 := hls.1 (fun _ => some 0)
          simp [instLevel, lvlSubst, levelParamSubst, eqRecSort, eval, hl₀,
            Option.bind, Option.map] <;> rfl

/-- Left-side proof-root exclusion: in any well-formed context `Γ` and at any
    spine bound `k`, no `const 65` spine with `eqNList ls [one]` can be typed at
    a `Prop`. -/
theorem no_const65_proof_root_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT 2 Γ) (k : Nat) :
    ¬ HasConst65ProofRoot eqEnvT 2 Γ [one] k := by
  rintro ⟨ls, xs, P, _, hls, ⟨hP⟩, ⟨hp⟩⟩
  obtain ⟨T₀, w₀, hw₀, ⟨hT₀⟩, ⟨hc65⟩⟩ :=
    hasTyT_foldApps_sort_zero_inv envWf hSortUniq hΓ xs hp hP
      (ρ := fun _ => some 0) rfl
  obtain ⟨m, hres, hlen, hwf, hcv⟩ := hasTyTInv_const hc65 rfl
  change some eqRecT = some m at hres
  have hm : m = eqRecT := (Option.some.inj hres).symm
  subst hm
  have hcl := envClosed_of_envWfT envWf
  have hclm := (hcl 65 eqRecT rfl).1
  have hti := hasTyT_instLevels (envWfT_levels envWf) (iotaLevelsT_of_envWfT envWf)
    hwf hlen eqRecMtypeTy
  have hw := hasTyTLiftPrefix hcl Γ hti
  rw [lift_instantiateLevels, lift_of_closed _ (hclm 0)] at hw
  simp only [List.append_nil, instLvlsCtx, List.map_nil,
    instantiateLevels, lift] at hw
  have heq : eqN (instLevel ls eqRecSort) w₀ :=
    tyConvT_sort_eqN_of_sortUniq envWf hSortUniq hΓ hw hT₀ hcv
  have h2 := eval_instLevel_eqRecSort_of_eqN_one hls
  have h20 : some 2 = some 0 := h2.symm.trans ((heq (fun _ => some 0)).trans hw₀)
  cases h20

/-! ## Step 2d: Right-side proof-root exclusion (`HasContractedProofRoot`) -/

/-- Under `.assumption A :: ctx u`, the lookup type of `.bvar 1` is typed at
    `.sort u`. -/
def minorLookupSortTy (u : Level) (hu : levelsBounded 2 [u] = true)
    (A : Expr Nat) :
    HasTyT eqEnvT 2 (.assumption A :: ctx u)
      (lift 0 2 (instantiateLevels [u] eqMinorT)) (.sort u) :=
  have hMinor0 : HasTyT eqEnvT 2 (ctx u).tail
      (instantiateLevels [u] eqMinorT) (.sort u) :=
    hasTyT_instLevels (envWfT_levels envWf) (iotaLevelsT_of_envWfT envWf)
      hu rfl Rcic.kgMinorTy
  hasTyTLiftPrefix (envClosed_of_envWfT envWf)
    [.assumption A, .assumption (instantiateLevels [u] eqMinorT)] hMinor0

/-- Any typing of `.bvar 1` at `B` with `B : .sort w` in `.assumption A :: ctx u`
    forces `eqN u w` under sort uniqueness. -/
theorem bvar1_type_sort_eqN_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    {u : Level} (hu : levelsBounded 2 [u] = true)
    {A B : Expr Nat} {w : Level}
    (hΓA : CtxWfT eqEnvT 2 (.assumption A :: ctx u))
    (hb : HasTyT eqEnvT 2 (.assumption A :: ctx u) (.bvar 1) B)
    (hB : HasTyT eqEnvT 2 (.assumption A :: ctx u) B (.sort w)) :
    eqN u w := by
  obtain ⟨T_lk, hlk, hcv⟩ := hasTyTInv_bvar hb rfl
  change some (lift 0 2 (instantiateLevels [u] eqMinorT)) = some T_lk at hlk
  have hTeq : T_lk = lift 0 2 (instantiateLevels [u] eqMinorT) :=
    (Option.some.inj hlk).symm
  subst hTeq
  exact tyConvT_sort_eqN_of_sortUniq envWf hSortUniq hΓA
    (minorLookupSortTy u hu A) hB hcv

/-- Right-side proof-root exclusion: `HasContractedProofRoot eqEnvT 2 positiveContext`
    is impossible under sort uniqueness. -/
theorem no_contracted_proof_root_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ¬ HasContractedProofRoot eqEnvT 2 positiveContext := by
  rintro (⟨A, P, ⟨hP⟩, ⟨hlam⟩⟩ | ⟨A, P, ⟨hΓA⟩, ⟨hP⟩, ⟨hb⟩⟩)
  · obtain ⟨u_dom, B, hA, hb, hc⟩ := hasTyTInv_lam hlam rfl
    have hΓA : CtxWfT eqEnvT 2 (.assumption A :: positiveContext) :=
      .assumption positiveContext A u_dom (contextWf one positive_levels) hA
    obtain ⟨w_B, ⟨hB⟩⟩ := DT007T_typing_regularity_of_envWfT envWf hΓA hb
    have hpi : HasTyT eqEnvT 2 positiveContext (.pi A B) (.sort (.imax u_dom w_B)) :=
      .pi positiveContext A u_dom B w_B hA hB
    have himax : eqN (.imax u_dom w_B) .zero :=
      tyConvT_sort_eqN_of_sortUniq envWf hSortUniq
        (contextWf one positive_levels) hpi hP hc
    have hwB : eqN one w_B :=
      bvar1_type_sort_eqN_of_sortUniq hSortUniq positive_levels hΓA hb hB
    have hwB1 : eval (fun _ => some 0) w_B = some 1 :=
      (hwB (fun _ => some 0)).symm
    have himax0 : eval (fun _ => some 0) (.imax u_dom w_B) = some 0 :=
      himax (fun _ => some 0)
    cases hdom : eval (fun _ => some 0) u_dom with
    | none =>
        simp [eval, hwB1, hdom, Option.bind, Option.map] at himax0
    | some k =>
        simp [eval, hwB1, hdom, Option.bind, Option.map] at himax0
        omega
  · have heq : eqN one .zero :=
      bvar1_type_sort_eqN_of_sortUniq hSortUniq positive_levels hΓA hb hP
    have h10 := heq (fun _ => some 0)
    cases h10

/-! ## Step 3: A-2 Decision (`conditionalNonJoin`, `conditionalNonModuloJoin`, and `positive_conversion`) -/

/-- Direct `ParRedTStar` joinability of the positive A-2 peak. -/
def PositiveJoin : Prop :=
  ∃ z : Expr Nat,
    Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) z commonIndex) ∧
    Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      contracted z commonIndex)

/-- Modulo-`PEqLeafT` joinability of the positive A-2 peak. -/
def PositiveModuloJoin : Prop :=
  ∃ u' v' : Expr Nat,
    Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) u' commonIndex) ∧
    Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      contracted v' commonIndex) ∧
    Nonempty (PEqLeafT eqEnvT 2 positiveContext u' v' commonIndex)

/-- A-2 Decision (direct join, pre-repair 17-constructor subsystem): under sort
    uniqueness, `partialRec one` and `contracted` have no common `NoEtaKStar`
    (`KEtaFreeStar`) reduct at `commonIndex`. -/
theorem conditionalNonJoin
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ¬ ∃ (z : Expr Nat)
        (hsL : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
          (partialRec one) z commonIndex)
        (hsR : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
          contracted z commonIndex),
        NoEtaKStar hsL ∧ NoEtaKStar hsR :=
  partialRec_not_joinable_of_no_proof one positive_levels
    (no_const65_proof_root_of_sortUniq hSortUniq
      (contextWf one positive_levels) 5)
    (no_contracted_proof_root_of_sortUniq hSortUniq)

/-- A-2 Decision (modulo `PEqLeafT`, pre-repair 17-constructor subsystem): under
    sort uniqueness, `partialRec one` and `contracted` also have no
    `PEqLeafT`-related `NoEtaKStar` (`KEtaFreeStar`) reducts at `commonIndex`. -/
theorem conditionalNonModuloJoin
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ¬ ∃ (u' v' : Expr Nat)
        (hsL : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
          (partialRec one) u' commonIndex)
        (hsR : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
          contracted v' commonIndex),
        NoEtaKStar hsL ∧ NoEtaKStar hsR ∧
        Nonempty (PEqLeafT eqEnvT 2 positiveContext u' v' commonIndex) :=
  partialRec_not_modulo_joinable_of_no_proof one positive_levels
    (no_const65_proof_root_of_sortUniq hSortUniq
      (contextWf one positive_levels) 5)
    (no_contracted_proof_root_of_sortUniq hSortUniq)

/-- The `ConvT` bridge under the binder: `(.app (lift 0 1 (partialRec one)) (.bvar 0)) ≡ .bvar 1`. -/
def positive_body_conversion :
    ConvT eqEnvT 2 (.assumption domain :: positiveContext)
      (.app (lift 0 1 (partialRec one)) (.bvar 0)) (.bvar 1) codomain :=
  convT_instLevels (envWfT_levels envWf) (iotaLevelsT_of_envWfT envWf)
    positive_levels rfl
    (ConvT.trans _ _ _ _ _ eqAppCong eqIotaAtP)

/-- The `ConvT` bridge on `expanded one ≡ contracted`. -/
def positive_expanded_conversion :
    ConvT eqEnvT 2 positiveContext (expanded one) contracted commonIndex :=
  .lam positiveContext domain domain
    (.app (lift 0 1 (partialRec one)) (.bvar 0)) (.bvar 1)
    codomain .zero
    (.refl positiveContext domain (.sort .zero)
      (domainTy one positive_levels))
    positive_body_conversion

/-- `ConvT` holds between `partialRec one` and `contracted` at `commonIndex`
    (via `symm eta` + `lam` + `irr` + `iota`), showing that non-joinability of
    `positive_peak` breaks Church–Rosser completeness unless `ParRedT.iotaStarK`
    is repaired. -/
def positive_conversion :
    ConvT eqEnvT 2 positiveContext (partialRec one) contracted commonIndex :=
  .trans positiveContext (partialRec one) (expanded one) contracted commonIndex
    (.symm positiveContext (expanded one) (partialRec one) commonIndex
      (.eta positiveContext (partialRec one) domain codomain
        (partialRecTy one positive_levels)))
    positive_expanded_conversion

/-! ## Direct-arm exclusions and universe-variant step on `partialRec one` -/

theorem partial_rec_not_direct_K (w : IotaWitness eqEnvT) (major : Expr Nat) :
    recCall (.const w.recRef w.ls) w.preMajor major ≠ partialRec one := by
  change recCall (.const w.recRef w.ls) w.preMajor major ≠
    foldApps (.const 65 [one])
      [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2]
  exact short_rec65_not_K_source (by decide) w major

theorem contracted_not_direct_eta (A f : Expr Nat) :
    contracted ≠ .lam A (.app (lift 0 1 f) (.bvar 0)) := by
  intro h
  change Expr.lam domain (Expr.bvar 1) =
    Expr.lam A (Expr.app (lift 0 1 f) (Expr.bvar 0)) at h
  cases h

def oneAlt_eq : eqN one oneAlt := fun _ => rfl

def alternate_constant_typing :
    HasTyT eqEnvT 2 positiveContext (.const 65 [oneAlt])
      (instantiateLevels [one] eqRecT.mtype) :=
  constsRightDataT_of_envWfT (n := 2) envWf
    (contextWf one positive_levels)
    (r := 65) (m := eqRecT) (ls := [one]) (ls' := [oneAlt])
    rfl rfl rfl rfl ⟨oneAlt_eq, True.intro⟩

def alternate_partial_typing :
    HasTyT eqEnvT 2 positiveContext (partialRec oneAlt) commonIndex :=
  let h0 := alternate_constant_typing
  let h1 := HasTyT.app _ _ _ _ _ h0 (.bvar positiveContext 3 _ rfl)
  let h2 := HasTyT.app _ _ _ _ _ h1 (.bvar positiveContext 2 _ rfl)
  let h3 := HasTyT.app _ _ _ _ _ h2 (.bvar positiveContext 1 _ rfl)
  let h4 := HasTyT.app _ _ _ _ _ h3 (.bvar positiveContext 0 _ rfl)
  HasTyT.app _ _ _ _ _ h4 (.bvar positiveContext 2 _ rfl)

def alternate_partial_raw :
    PEqT eqEnvT 2 positiveContext (partialRec one) (partialRec oneAlt) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.const positiveContext 65 [one] [oneAlt]
              ⟨oneAlt_eq, True.intro⟩)
            (.bvar positiveContext 3))
          (.bvar positiveContext 2))
        (.bvar positiveContext 1))
      (.bvar positiveContext 0))
    (.bvar positiveContext 2)

def alternate_partial_step :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) (partialRec oneAlt) commonIndex :=
  .peq positiveContext (partialRec one) (partialRec oneAlt) commonIndex
    ⟨alternate_partial_raw, partialRecTy one positive_levels,
      alternate_partial_typing⟩

theorem alternate_partial_ne : partialRec oneAlt ≠ partialRec one := by
  decide

theorem alternate_partial_no_proof_roots :
    (F8Occurrences.occurrences alternate_partial_step).length = 0 := rfl

theorem positive_partial_not_literally_normal :
    ∃ z : Expr Nat, z ≠ partialRec one ∧
      Nonempty (ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (partialRec one) z commonIndex) :=
  ⟨partialRec oneAlt, alternate_partial_ne, ⟨alternate_partial_step⟩⟩

/-! ## Step 4: Level-instantiation transport for `ParRedT` (including `iotaStarKEta`) -/

/-- `appsSpine`'s head commutes with `instantiateLevels`. -/
theorem appsSpine_fst_instantiateLevels (ls : List Level) :
    (e : Expr Nat) →
    (appsSpine (instantiateLevels ls e)).1 = instantiateLevels ls (appsSpine e).1
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .pi _ _ | .letE _ _ _ | .lit _ => rfl
  | .app f _ => appsSpine_fst_instantiateLevels ls f

/-- Level-instantiation transport for `TyConvT`. -/
def tyConvT_instLevels {E : ResolvedEnv} (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E a Γ A B →
    TyConvT E n (instLvlsCtx ls Γ) (instantiateLevels ls A)
      (instantiateLevels ls B)
  | _, _, _, .refl _ A => .refl (instLvlsCtx ls _) (instantiateLevels ls A)
  | _, _, _, .of _ A B u hc =>
      .of (instLvlsCtx ls _) (instantiateLevels ls A) (instantiateLevels ls B)
        (instLevel ls u) (convT_instLevels hEL hIL hls hlen hc)
  | _, _, _, .trans _ A B C h1 h2 =>
      .trans (instLvlsCtx ls _) (instantiateLevels ls A) (instantiateLevels ls B)
        (instantiateLevels ls C)
        (tyConvT_instLevels hEL hIL hls hlen h1)
        (tyConvT_instLevels hEL hIL hls hlen h2)

/-- Level-instantiation transport for `DerivedIotaU` (both `.ofU` and `.ofUS`). -/
def derivedIotaU_instLevels {E : ResolvedEnv} (hIL : IotaLevelsT E)
    {lhs rhs : Expr Nat} (h : DerivedIotaU E lhs rhs) (lvls : List Level) :
    DerivedIotaU E (instantiateLevels lvls lhs) (instantiateLevels lvls rhs) := by
  cases h with
  | ofU w =>
      rw [← iotaLhsOf_instLevels lvls w (hIL.2 w),
        ← iotaRhsOf_instLevels lvls w (hIL.2 w)]
      exact .ofU (lvlsWitness lvls w (hIL.2 w))
  | ofUS w =>
      rw [← iotaLhsOfS_instLevels lvls w,
        ← iotaRhsOfS_instLevels hIL lvls w]
      exact .ofUS (lvlsWitnessS lvls w)

/-- Level-instantiation transport for `PEqT`. -/
def peqT_instLevels {E : ResolvedEnv} (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtx} → {p q : Expr Nat} → PEqT E a Γ p q →
    PEqT E n (instLvlsCtx ls Γ) (instantiateLevels ls p) (instantiateLevels ls q)
  | _, _, _, .bvar Γ i => .bvar (instLvlsCtx ls Γ) i
  | _, _, _, .sort Γ u v huv =>
      .sort (instLvlsCtx ls Γ) (instLevel ls u) (instLevel ls v)
        (eqN_instLevel huv ls)
  | _, _, _, .const Γ r ls1 ls2 hc =>
      .const (instLvlsCtx ls Γ) r (ls1.map (instLevel ls))
        (ls2.map (instLevel ls)) (eqNList_map_instLevel ls ls1 ls2 hc)
  | _, _, _, .app Γ _ _ _ _ hf hx =>
      .app (instLvlsCtx ls Γ) _ _ _ _
        (peqT_instLevels hEL hIL hls hlen hf)
        (peqT_instLevels hEL hIL hls hlen hx)
  | _, _, _, .lam Γ _ _ _ _ hA hb =>
      .lam (instLvlsCtx ls Γ) _ _ _ _
        (peqT_instLevels hEL hIL hls hlen hA)
        (peqT_instLevels hEL hIL hls hlen hb)
  | _, _, _, .pi Γ _ _ _ _ hA hB =>
      .pi (instLvlsCtx ls Γ) _ _ _ _
        (peqT_instLevels hEL hIL hls hlen hA)
        (peqT_instLevels hEL hIL hls hlen hB)
  | _, _, _, .letE Γ _ _ _ _ _ _ hA hv hb =>
      .letE (instLvlsCtx ls Γ) _ _ _ _ _ _
        (peqT_instLevels hEL hIL hls hlen hA)
        (peqT_instLevels hEL hIL hls hlen hv)
        (peqT_instLevels hEL hIL hls hlen hb)
  | _, _, _, .lit Γ t => .lit (instLvlsCtx ls Γ) t
  | _, _, _, .proof Γ _ _ P Q hP hQ hp hq =>
      .proof (instLvlsCtx ls Γ) _ _
        (instantiateLevels ls P) (instantiateLevels ls Q)
        (hasTyT_instLevels hEL hIL hls hlen hP)
        (hasTyT_instLevels hEL hIL hls hlen hQ)
        (hasTyT_instLevels hEL hIL hls hlen hp)
        (hasTyT_instLevels hEL hIL hls hlen hq)

/-- Level-instantiation transport for `PEqLeafT`. -/
def peqLeafT_instLevels {E : ResolvedEnv} (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    {Γ : LCtx} {p q T : Expr Nat}
    (h : PEqLeafT E a Γ p q T) :
    PEqLeafT E n (instLvlsCtx ls Γ) (instantiateLevels ls p)
      (instantiateLevels ls q) (instantiateLevels ls T) :=
  ⟨peqT_instLevels hEL hIL hls hlen h.1,
    hasTyT_instLevels hEL hIL hls hlen h.2.1,
    hasTyT_instLevels hEL hIL hls hlen h.2.2⟩

private theorem instLvlsCtx_drop (ls : List Level) :
    (Γ : LCtx) → (k : Nat) →
    (instLvlsCtx ls Γ).drop k = instLvlsCtx ls (Γ.drop k)
  | [], _ => by simp [instLvlsCtx]
  | _ :: _, 0 => rfl
  | _ :: Γ, k + 1 => instLvlsCtx_drop ls Γ k

/-- Level-instantiation transport for all 18 constructors of `ParRedT`
    (including `iotaStarK` and `iotaStarKEta`). -/
def parRedT_instLevels {E : ResolvedEnv}
    {PEq PEq' : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat},
      PEq Γ p q T →
      PEq' (instLvlsCtx ls Γ) (instantiateLevels ls p)
        (instantiateLevels ls q) (instantiateLevels ls T)) :
    {Γ : LCtx} → {x y T : Expr Nat} → ParRedT PEq E a Γ x y T →
    ParRedT PEq' E n (instLvlsCtx ls Γ) (instantiateLevels ls x)
      (instantiateLevels ls y) (instantiateLevels ls T)
  | _, _, _, _, .refl Γ e A he =>
      .refl (instLvlsCtx ls Γ) (instantiateLevels ls e)
        (instantiateLevels ls A) (hasTyT_instLevels hEL hIL hls hlen he)
  | _, _, _, _, .sortEq Γ u v T heq hlhs hrhs =>
      .sortEq (instLvlsCtx ls Γ) (instLevel ls u) (instLevel ls v)
        (instantiateLevels ls T) (eqN_instLevel heq ls)
        (hasTyT_instLevels hEL hIL hls hlen hlhs)
        (hasTyT_instLevels hEL hIL hls hlen hrhs)
  | _, _, _, _, .consts Γ r ls1 ls2 T hc hlhs hrhs =>
      .consts (instLvlsCtx ls Γ) r (ls1.map (instLevel ls))
        (ls2.map (instLevel ls)) (instantiateLevels ls T)
        (eqNList_map_instLevel ls ls1 ls2 hc)
        (hasTyT_instLevels hEL hIL hls hlen hlhs)
        (hasTyT_instLevels hEL hIL hls hlen hrhs)
  | _, _, _, _, .bvarZeta Γ i A v v' T₀ hget hv hlhs hrhs => by
      have hget' : (instLvlsCtx ls Γ).get? i =
          some (.letBinding (instantiateLevels ls A) (instantiateLevels ls v)) := by
        unfold instLvlsCtx
        rw [List.get?_map, hget]
        rfl
      have hv' : ParRedT PEq' E n ((instLvlsCtx ls Γ).drop (i + 1))
          (instantiateLevels ls v) (instantiateLevels ls v')
          (instantiateLevels ls A) := by
        rw [instLvlsCtx_drop]
        exact parRedT_instLevels hEL hIL hls hlen hPEqL hv
      have hlhs' := hasTyT_instLevels hEL hIL hls hlen hlhs
      have hrhs' := hasTyT_instLevels hEL hIL hls hlen hrhs
      rw [← lift_instantiateLevels] at hrhs' ⊢
      exact .bvarZeta (instLvlsCtx ls Γ) i
        (instantiateLevels ls A) (instantiateLevels ls v) (instantiateLevels ls v')
        (instantiateLevels ls T₀) hget' hv' hlhs' hrhs'
  | _, _, _, _, .delta Γ r ms m b T₀ hres hbody htr hlen' hwf hlhs hrhs => by
      have hlhs' := hasTyT_instLevels hEL hIL hls hlen hlhs
      have hrhs' := hasTyT_instLevels hEL hIL hls hlen hrhs
      rw [instLevels_mbody hEL hres hbody hlen' ls] at hrhs' ⊢
      exact .delta (instLvlsCtx ls Γ) r (ms.map (instLevel ls)) m b
        (instantiateLevels ls T₀) hres hbody htr (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf) hlhs' hrhs'
  | _, _, _, _, .app Γ f f' x x' A B T₀ v w hf hc hB hTy ha hr => by
      have hTy' := hasTyT_instLevels hEL hIL hls hlen hTy
      have hr' := hasTyT_instLevels hEL hIL hls hlen hr
      rw [instantiateLevels_instantiate0] at hTy' hr' ⊢
      exact .app (instLvlsCtx ls Γ)
        (instantiateLevels ls f) (instantiateLevels ls f')
        (instantiateLevels ls x) (instantiateLevels ls x')
        (instantiateLevels ls A) (instantiateLevels ls B)
        (instantiateLevels ls T₀) (instLevel ls v) (instLevel ls w)
        (parRedT_instLevels hEL hIL hls hlen hPEqL hf)
        (tyConvT_instLevels hEL hIL hls hlen hc)
        (hasTyT_instLevels hEL hIL hls hlen hB) hTy'
        (parRedT_instLevels hEL hIL hls hlen hPEqL ha) hr'
  | _, _, _, _, .beta Γ A body body' arg arg' B u v w hA hB hTy hb ha hred => by
      have hTy' := hasTyT_instLevels hEL hIL hls hlen hTy
      have hred' := hasTyT_instLevels hEL hIL hls hlen hred
      simp only [instantiateLevels_instantiate0] at hTy' hred' ⊢
      exact .beta (instLvlsCtx ls Γ)
        (instantiateLevels ls A) (instantiateLevels ls body)
        (instantiateLevels ls body') (instantiateLevels ls arg)
        (instantiateLevels ls arg') (instantiateLevels ls B)
        (instLevel ls u) (instLevel ls v) (instLevel ls w)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hB) hTy'
        (parRedT_instLevels hEL hIL hls hlen hPEqL hb)
        (parRedT_instLevels hEL hIL hls hlen hPEqL ha) hred'
  | _, _, _, _, .lam Γ A A' body body' B u v hc hA hB hb hrt =>
      .lam (instLvlsCtx ls Γ)
        (instantiateLevels ls A) (instantiateLevels ls A')
        (instantiateLevels ls body) (instantiateLevels ls body')
        (instantiateLevels ls B) (instLevel ls u) (instLevel ls v)
        (convT_instLevels hEL hIL hls hlen hc)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hB)
        (parRedT_instLevels hEL hIL hls hlen hPEqL hb)
        (hasTyT_instLevels hEL hIL hls hlen hrt)
  | _, _, _, _, .pi Γ A A' B B' u v hA hc hB hcB hrt =>
      .pi (instLvlsCtx ls Γ)
        (instantiateLevels ls A) (instantiateLevels ls A')
        (instantiateLevels ls B) (instantiateLevels ls B')
        (instLevel ls u) (instLevel ls v)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (convT_instLevels hEL hIL hls hlen hc)
        (hasTyT_instLevels hEL hIL hls hlen hB)
        (convT_instLevels hEL hIL hls hlen hcB)
        (hasTyT_instLevels hEL hIL hls hlen hrt)
  | _, _, _, _, .letE Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt => by
      have hTy' := hasTyT_instLevels hEL hIL hls hlen hTy
      have hrt' := hasTyT_instLevels hEL hIL hls hlen hrt
      rw [instantiateLevels_instantiate0] at hTy' hrt' ⊢
      exact .letE (instLvlsCtx ls Γ)
        (instantiateLevels ls A) (instantiateLevels ls A')
        (instantiateLevels ls value) (instantiateLevels ls value')
        (instantiateLevels ls body) (instantiateLevels ls body')
        (instantiateLevels ls B) (instLevel ls u) (instLevel ls w)
        (convT_instLevels hEL hIL hls hlen hc)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (parRedT_instLevels hEL hIL hls hlen hPEqL hv)
        (hasTyT_instLevels hEL hIL hls hlen hB) hTy'
        (parRedT_instLevels hEL hIL hls hlen hPEqL hb) hrt'
  | _, _, _, _, .zeta Γ A value value' body body' B u w hA hv hB hTy hb hred => by
      have hTy' := hasTyT_instLevels hEL hIL hls hlen hTy
      have hred' := hasTyT_instLevels hEL hIL hls hlen hred
      simp only [instantiateLevels_instantiate0] at hTy' hred' ⊢
      exact .zeta (instLvlsCtx ls Γ)
        (instantiateLevels ls A) (instantiateLevels ls value)
        (instantiateLevels ls value') (instantiateLevels ls body)
        (instantiateLevels ls body') (instantiateLevels ls B)
        (instLevel ls u) (instLevel ls w)
        (hasTyT_instLevels hEL hIL hls hlen hA)
        (parRedT_instLevels hEL hIL hls hlen hPEqL hv)
        (hasTyT_instLevels hEL hIL hls hlen hB) hTy'
        (parRedT_instLevels hEL hIL hls hlen hPEqL hb) hred'
  | _, _, _, _, .iotaSpine Γ lhs lhs' rhs T hstep hI hred hrhs =>
      .iotaSpine (instLvlsCtx ls Γ)
        (instantiateLevels ls lhs) (instantiateLevels ls lhs')
        (instantiateLevels ls rhs) (instantiateLevels ls T)
        (parRedT_instLevels hEL hIL hls hlen hPEqL hstep)
        (derivedIotaU_instLevels hIL hI ls)
        (hasTyT_instLevels hEL hIL hls hlen hred)
        (hasTyT_instLevels hEL hIL hls hlen hrhs)
  | _, _, _, _, .iotaStarK Γ w major Tm rhs T rl afs
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs => by
      let w' := lvlsWitness ls w (hIL.2 w)
      have hfam' : ∃ lsF, (appsSpine (instantiateLevels ls Tm)).1 =
          .const w'.familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        refine ⟨lsF.map (instLevel ls), ?_⟩
        rw [appsSpine_fst_instantiateLevels, hlsF]
        rfl
      have hmajor' := hasTyT_instLevels hEL hIL hls hlen hmajor
      have hmk' := hasTyT_instLevels hEL hIL hls hlen hmk
      have hTm0' := hasTyT_instLevels hEL hIL hls hlen hTm0
      have hι' := derivedIotaU_instLevels hIL hι ls
      have hlι' := hasTyT_instLevels hEL hIL hls hlen hlι
      have hlhs' := hasTyT_instLevels hEL hIL hls hlen hlhs
      have hrhs' := hasTyT_instLevels hEL hIL hls hlen hrhs
      rw [← ctorMajor_instLevels ls w (hIL.2 w)] at hmk'
      rw [← iotaLhsOf_instLevels ls w (hIL.2 w)] at hι' hlι'
      rw [recCall_instLevels] at hlhs' ⊢
      exact .iotaStarK (instLvlsCtx ls Γ) w'
        (instantiateLevels ls major) (instantiateLevels ls Tm)
        (instantiateLevels ls rhs) (instantiateLevels ls T)
        rl afs hrl hsel hfam' hmajor' hmk' hTm0' hι' hlι' hlhs' hrhs'
  | _, _, _, _, .iotaStarKEta Γ w f A B Tm rhs u rl afs
      happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs => by
      let w' := lvlsWitness ls w (hIL.2 w)
      have happ' :
          recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
          .app (lift 0 1 (instantiateLevels ls f)) (.bvar 0) := by
        have h1 := congrArg (instantiateLevels ls) happ
        rw [recCall_instLevels] at h1
        change recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
          Expr.app (instantiateLevels ls (lift 0 1 f)) (.bvar 0) at h1
        rw [← lift_instantiateLevels] at h1
        exact h1
      have hfam' : ∃ lsF, (appsSpine (instantiateLevels ls Tm)).1 =
          .const w'.familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        refine ⟨lsF.map (instLevel ls), ?_⟩
        rw [appsSpine_fst_instantiateLevels, hlsF]
        rfl
      have hmajor' := hasTyT_instLevels hEL hIL hls hlen hmajor
      have hmk' := hasTyT_instLevels hEL hIL hls hlen hmk
      have hTm0' := hasTyT_instLevels hEL hIL hls hlen hTm0
      have hι' := derivedIotaU_instLevels hIL hι ls
      have hlι' := hasTyT_instLevels hEL hIL hls hlen hlι
      have hlhs' := hasTyT_instLevels hEL hIL hls hlen hlhs
      have hrhs' := hasTyT_instLevels hEL hIL hls hlen hrhs
      rw [← ctorMajor_instLevels ls w (hIL.2 w)] at hmk'
      rw [← iotaLhsOf_instLevels ls w (hIL.2 w)] at hι' hlι'
      rw [recCall_instLevels] at hlhs'
      exact .iotaStarKEta (instLvlsCtx ls Γ) w'
        (instantiateLevels ls f) (instantiateLevels ls A)
        (instantiateLevels ls B) (instantiateLevels ls Tm)
        (instantiateLevels ls rhs) (instLevel ls u) rl afs
        happ' (hasTyT_instLevels hEL hIL hls hlen hA)
        (hasTyT_instLevels hEL hIL hls hlen hf)
        hrl hsel hfam' hmajor' hmk' hTm0' hι' hlι' hlhs' hrhs'
  | _, _, _, _, .lit Γ t T hexp => by
      have hexp' := hasTyT_instLevels hEL hIL hls hlen hexp
      rw [instantiateLevels_natExpand] at hexp' ⊢
      exact .lit (instLvlsCtx ls Γ) t (instantiateLevels ls T) hexp'
  | _, _, _, _, .eta Γ f f' A B hf hl => by
      have hl' := hasTyT_instLevels hEL hIL hls hlen hl
      have h'' : instantiateLevels ls (.lam A (.app (lift 0 1 f) (.bvar 0))) =
          .lam (instantiateLevels ls A)
            (.app (lift 0 1 (instantiateLevels ls f)) (.bvar 0)) := by
        simp only [instantiateLevels, lift_instantiateLevels]
      rw [h''] at hl' ⊢
      exact .eta (instLvlsCtx ls Γ)
        (instantiateLevels ls f) (instantiateLevels ls f')
        (instantiateLevels ls A) (instantiateLevels ls B)
        (parRedT_instLevels hEL hIL hls hlen hPEqL hf) hl'
  | _, _, _, _, .peq Γ p q T hp =>
      .peq (instLvlsCtx ls Γ) (instantiateLevels ls p)
        (instantiateLevels ls q) (instantiateLevels ls T) (hPEqL hp)
  | _, _, _, _, .conv Γ a b A A' h hc =>
      .conv (instLvlsCtx ls Γ) (instantiateLevels ls a)
        (instantiateLevels ls b) (instantiateLevels ls A)
        (instantiateLevels ls A')
        (parRedT_instLevels hEL hIL hls hlen hPEqL h)
        (tyConvT_instLevels hEL hIL hls hlen hc)

/-! ## Step 5: `ParRedT.iotaStarKEta` on the A-2 positive peak (`positive_peak_joined`, `positive_join`) -/

private def el' : EnvLevelsT eqEnvT := envWfT_levels envWf
private def il' : IotaLevelsT eqEnvT := iotaLevelsT_of_envWfT envWf

private def instTy' (u : Level) (hu : levelsBounded 2 [u] = true)
    {Γ : LCtx} {e T : Expr Nat} (h : HasTyT eqEnvT 1 Γ e T) :
    HasTyT eqEnvT 2 (instLvlsCtx [u] Γ)
      (instantiateLevels [u] e) (instantiateLevels [u] T) :=
  hasTyT_instLevels el' il' hu rfl h

private def instCv' (u : Level) (hu : levelsBounded 2 [u] = true)
    {Γ : LCtx} {e e' T : Expr Nat} (h : ConvT eqEnvT 1 Γ e e' T) :
    ConvT eqEnvT 2 (instLvlsCtx [u] Γ)
      (instantiateLevels [u] e) (instantiateLevels [u] e') (instantiateLevels [u] T) :=
  convT_instLevels el' il' hu rfl h

private def bodyTy' (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (.assumption domain :: ctx u)
      (.app (lift 0 1 (partialRec u)) (.bvar 0)) codomain :=
  instTy' u hu (.app _ _ _ _ _ eqRecTy5 pinEqGate_met)

private def atP' (u : Level) (hu : levelsBounded 2 [u] = true)
    {e : Expr Nat} (h : HasTyT eqEnvT 1 eqJoinCtx e eqEqLhs) :
    HasTyT eqEnvT 2 (.assumption domain :: ctx u)
      (instantiateLevels [u] e) codomain :=
  .conv _ _ _ _ u (instTy' u hu h) (.symm _ _ _ _ (instCv' u hu eqTyX))

/-- For any bounded level `u`, `partialRec u` steps in one `ParRedT.iotaStarKEta`
    step to `contracted` at `commonIndex`. -/
def partialRec_to_contracted_at (u : Level) (hu : levelsBounded 2 [u] = true) :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx u)
      (partialRec u) contracted commonIndex :=
  .iotaStarKEta (ctx u) (witness u)
    (partialRec u) domain codomain eqPTyAt0 (.bvar 1) .zero .zero True
    rfl (domainTy u hu) (partialRecTy u hu)
    rfl (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ (instTy' u hu pinEqGate_met) (instTy' u hu eqReflTy2)
    (instTy' u hu eqFamTy3) (.ofU (witness u))
    (atP' u hu eqRecLhsTy) (bodyTy' u hu) (atP' u hu eqTym)

/-- At `u = one`, `partialRec one` steps in one `ParRedT.iotaStarKEta` step to
    `contracted` at `commonIndex`. -/
def partialRec_to_contracted :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) contracted commonIndex :=
  partialRec_to_contracted_at one positive_levels

/-- The positive A-2 peak `positive_peak` joins directly in one step via
    `ParRedT.iotaStarKEta` on the left and `.refl` on the right, matching the
    `prop_peak_joined` package shape. -/
def positive_peak_joined :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) contracted commonIndex ×'
      (ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted contracted commonIndex ×'
        ConvT eqEnvT 2 positiveContext (partialRec one) contracted commonIndex) :=
  ⟨partialRec_to_contracted,
    ⟨.refl positiveContext contracted commonIndex
        (contractedTy one positive_levels),
      positive_conversion⟩⟩

/-- `PositiveJoin` holds for the repaired 18-constructor `ParRedT`. -/
theorem positive_join : PositiveJoin :=
  ⟨contracted,
    ⟨.tail partialRec_to_contracted
      (.refl positiveContext contracted commonIndex
        (contractedTy one positive_levels))⟩,
    ⟨.refl positiveContext contracted commonIndex
      (contractedTy one positive_levels)⟩⟩

/-- `PositiveModuloJoin` also holds for the repaired 18-constructor `ParRedT`. -/
theorem positive_modulo_join : PositiveModuloJoin :=
  ⟨contracted, contracted,
    ⟨.tail partialRec_to_contracted
      (.refl positiveContext contracted commonIndex
        (contractedTy one positive_levels))⟩,
    ⟨.refl positiveContext contracted commonIndex
      (contractedTy one positive_levels)⟩,
    ⟨⟨.lam positiveContext domain domain (.bvar 1) (.bvar 1)
        (.app positiveContext _ _ (.bvar 2) (.bvar 2)
          (.app positiveContext _ _ (.bvar 2) (.bvar 2)
            (.app positiveContext _ _ (.bvar 3) (.bvar 3)
              (.const positiveContext 63 [] [] trivial)
              (.bvar positiveContext 3))
            (.bvar positiveContext 2))
          (.bvar positiveContext 2))
        (.bvar _ 1),
      contractedTy one positive_levels,
      contractedTy one positive_levels⟩⟩⟩

/-! ## Step 6: General `eta` × `lam (iotaStarK)` peak join -/

/-- General single-step `ParRedT.iotaStarKEta` (transported along `hc : TyConvT E n Γ (.pi A B) T`)
    closing the left side `f` of any `eta` × `lam (iotaStarK)` peak to `.lam A rhs`. -/
def eta_lamK_step
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B Tm rhs T : Expr Nat} {u rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u))
    (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ)
      (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T) :
    ParRedT PEq E n Γ f (.lam A rhs) T :=
  .conv Γ f (.lam A rhs) (.pi A B) T
    (.iotaStarKEta Γ w f A B Tm rhs u rl afs
      happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs)
    hc

/-- General 1-step/0-step diamond for any `eta` × `lam (iotaStarK)` peak with
    reflexive `hf` and reflexive domain `A`. -/
def eta_lamK_peak_refl_data
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B Tm rhs T : Expr Nat} {u rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u))
    (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ)
      (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T) :
    ParRedT PEq E n Γ f (.lam A rhs) T ×'
      ParRedT PEq E n Γ (.lam A rhs) (.lam A rhs) T :=
  ⟨eta_lamK_step w happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs hc,
    .conv Γ (.lam A rhs) (.lam A rhs) (.pi A B) T
      (.refl Γ (.lam A rhs) (.pi A B) (.lam Γ A u rhs B hA hrhs)) hc⟩

/-- General `ParRedTStar` join data for any `eta` × `lam (iotaStarK)` peak with
    arbitrary domain conversion `hcA : ConvT E n Γ A A' (.sort u)`:
    `f` steps to `.lam A rhs` via `iotaStarKEta` and then to `.lam A' rhs` via
    `ParRedT.lam`, joining `.lam A' rhs` at `T`. -/
def eta_lamK_peak_star_data
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ)
      (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hrt' : HasTyT E n Γ (.lam A' rhs) (.pi A B))
    (hc : TyConvT E n Γ (.pi A B) T) :
    ParRedTStar PEq E n Γ f (.lam A' rhs) T ×'
      ParRedTStar PEq E n Γ (.lam A' rhs) (.lam A' rhs) T :=
  let step1 : ParRedT PEq E n Γ f (.lam A rhs) T :=
    eta_lamK_step w happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs hc
  let step2 : ParRedT PEq E n Γ (.lam A rhs) (.lam A' rhs) T :=
    .conv Γ (.lam A rhs) (.lam A' rhs) (.pi A B) T
      (.lam Γ A A' rhs rhs B u v hcA hA hB
        (.refl (.assumption A :: Γ) rhs B hrhs) hrt')
      hc
  let hrtT : HasTyT E n Γ (.lam A' rhs) T :=
    hasTyT_of_tyConvT hrt' hc
  ⟨.tail step1 (.tail step2 (.refl Γ (.lam A' rhs) T hrtT)),
    .refl Γ (.lam A' rhs) T hrtT⟩

/-- Existential `ParRedTStar` join theorem for any `eta` × `lam (iotaStarK)` peak. -/
theorem eta_lamK_peak_joins
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ)
      (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hrt' : HasTyT E n Γ (.lam A' rhs) (.pi A B))
    (hc : TyConvT E n Γ (.pi A B) T) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ f z T) ∧
      Nonempty (ParRedTStar PEq E n Γ (.lam A' rhs) z T) :=
  let d := eta_lamK_peak_star_data w happ hcA hA hB hf hrl hsel hfam
    hmajor hmk hTm0 hι hlι hlhs hrhs hrt' hc
  ⟨.lam A' rhs, ⟨d.1⟩, ⟨d.2⟩⟩

/-- In a general `eta` × `lam (iotaStarK)` peak, the non-reflexive sub-step
    `hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B)` is an actual
    immediate `Child` of the original `.eta` branch (never a synthesized
    `iotaStarKEta` node). -/
theorem eta_child_hf_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' A B : Expr Nat}
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) :
    Rcic.Declarative.F8Measure.Child (.pr hf_step)
      (.pr (.eta Γ f f' A B hf_step hl)) :=
  .head _

/-- Weakening transport for raw `PEqT` under `insertAt`. -/
def peqTWeaken {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (d : LocalDecl) :
    {c : Nat} → {Γ : LCtx} → {p q : Expr Nat} →
    PEqT E n Γ p q → PEqT E n (insertAt d c Γ) (lift c 1 p) (lift c 1 q)
  | c, _, _, _, .bvar _ i => by
      simp only [lift]
      split <;> exact .bvar _ _
  | _, _, _, _, .sort _ l l' h => .sort _ l l' h
  | _, _, _, _, .const _ r ls ls' h => .const _ r ls ls' h
  | c, _, _, _, .app _ f f' a a' hf ha =>
      .app _ _ _ _ _ (peqTWeaken hcl d hf) (peqTWeaken hcl d ha)
  | c, _, _, _, .lam _ A A' b b' hA hb => by
      have hb' := peqTWeaken hcl d (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .lam _ _ _ _ _ (peqTWeaken hcl d hA) hb'
  | c, _, _, _, .pi _ A A' B B' hA hB => by
      have hB' := peqTWeaken hcl d (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      exact .pi _ _ _ _ _ (peqTWeaken hcl d hA) hB'
  | c, _, _, _, .letE _ A A' v v' b b' hA hv hb => by
      have hb' := peqTWeaken hcl d (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .letE _ _ _ _ _ _ _ (peqTWeaken hcl d hA) (peqTWeaken hcl d hv) hb'
  | _, _, _, _, .lit _ t => .lit _ t
  | c, _, _, _, .proof _ _ _ _ _ hP hQ hp hq =>
      .proof _ _ _ _ _
        (hasTyTWeaken d hcl (c := c) hP)
        (hasTyTWeaken d hcl (c := c) hQ)
        (hasTyTWeaken d hcl (c := c) hp)
        (hasTyTWeaken d hcl (c := c) hq)

/-- Weakening transport for `PEqLeafT` under `insertAt`. -/
def peqLeafTWeaken {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {p q T : Expr Nat} {d : LocalDecl} {c : Nat}
    (h : PEqLeafT E n Γ p q T) :
    PEqLeafT E n (insertAt d c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T) :=
  ⟨peqTWeaken hcl d h.1, hasTyTWeaken d hcl h.2.1, hasTyTWeaken d hcl h.2.2⟩

/-- Context transport for `TyConvT` along `CtxConvT`. -/
def tyConvT_ctx {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ Γ' : LCtx} (hcc : CtxConvT E n Γ Γ') :
    {A B : Expr Nat} → TyConvT E n Γ A B → TyConvT E n Γ' A B
  | _, _, .refl _ A => .refl Γ' A
  | _, _, .of _ A B u hc => .of Γ' A B u (convT_ctx hcl hcc hc)
  | _, _, .trans _ A B C h1 h2 =>
      .trans Γ' A B C (tyConvT_ctx hcl hcc h1) (tyConvT_ctx hcl hcc h2)

/-- Pointwise context conversion that only modifies `.assumption` declarations
    (preserving all `.letBinding` declarations identically so `ParRedT.bvarZeta`
    transports directly). -/
inductive AssumpCtxConvT (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type where
  | nil : AssumpCtxConvT E n [] []
  | same {Γ Γ' : LCtx} (d : LocalDecl) (h : AssumpCtxConvT E n Γ Γ') :
      AssumpCtxConvT E n (d :: Γ) (d :: Γ')
  | assumption {Γ Γ' : LCtx} {A A' : Expr Nat} {u : Level}
      (h : AssumpCtxConvT E n Γ Γ')
      (hA : HasTyT E n Γ' A (.sort u))
      (hA' : HasTyT E n Γ' A' (.sort u))
      (hc : ConvT E n Γ' A A' (.sort u)) :
      AssumpCtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ')

def assumpCtxConvT_refl {E : ResolvedEnv} {n : Nat} :
    (Γ : LCtx) → AssumpCtxConvT E n Γ Γ
  | [] => .nil
  | d :: Γ => .same d (assumpCtxConvT_refl Γ)

def assumpCtxConvT_to_ctxConvT {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → AssumpCtxConvT E n Γ Γ' → CtxConvT E n Γ Γ'
  | _, _, .nil => .nil
  | _, _, .same d h => .same d (assumpCtxConvT_to_ctxConvT h)
  | _, _, .assumption h hA hA' hc =>
      .assumption (assumpCtxConvT_to_ctxConvT h) hA hA' hc

theorem assumpCtxConvT_get_letBinding {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → AssumpCtxConvT E n Γ Γ' → {i : Nat} → {A v : Expr Nat} →
    Γ.get? i = some (.letBinding A v) → Γ'.get? i = some (.letBinding A v)
  | _, _, .nil, _, _, _, h => nomatch h
  | _, _, .same _ _, 0, _, _, h => h
  | _, _, .same _ hcc, _ + 1, _, _, h =>
      assumpCtxConvT_get_letBinding hcc h
  | _, _, .assumption .., 0, _, _, h => nomatch h
  | _, _, .assumption hcc _ _ _, _ + 1, _, _, h =>
      assumpCtxConvT_get_letBinding hcc h

def assumpCtxConvT_drop {E : ResolvedEnv} {n : Nat} :
    (i : Nat) → {Γ Γ' : LCtx} → AssumpCtxConvT E n Γ Γ' →
    AssumpCtxConvT E n (Γ.drop i) (Γ'.drop i)
  | 0, _, _, hcc => hcc
  | _ + 1, _, _, .nil => .nil
  | i + 1, _, _, .same _ hcc => assumpCtxConvT_drop i hcc
  | i + 1, _, _, .assumption hcc _ _ _ => assumpCtxConvT_drop i hcc

/-- Context transport for `ParRedT (PEqLeafT E n)` across `AssumpCtxConvT`
    (covering all 18 `ParRedT` constructors). -/
def parRedT_assumpCtx {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → AssumpCtxConvT E n Γ Γ' → {a b T : Expr Nat} →
    ParRedT (PEqLeafT E n) E n Γ a b T →
    ParRedT (PEqLeafT E n) E n Γ' a b T
  | _, Γ', hcc, a, _, A, .refl _ _ _ h =>
      .refl Γ' a A (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) h)
  | _, Γ', hcc, _, _, T, .sortEq _ l₁ l₂ _ h hl hr =>
      .sortEq Γ' l₁ l₂ T h
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hl)
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hr)
  | _, Γ', hcc, _, _, T, .consts _ r ls ls' _ h hl hr =>
      .consts Γ' r ls ls' T h
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hl)
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hr)
  | _, Γ', hcc, _, _, T, .bvarZeta _ i A v v' _ hget hv hl hr =>
      .bvarZeta Γ' i A v v' T
        (assumpCtxConvT_get_letBinding hcc hget)
        (parRedT_assumpCtx hcl (assumpCtxConvT_drop (i + 1) hcc) hv)
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hl)
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hr)
  | _, Γ', hcc, _, _, T, .delta _ r ls m b _ hres hbody htr hlen hwf hl hr =>
      .delta Γ' r ls m b T hres hbody htr hlen hwf
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hl)
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hr)
  | _, Γ', hcc, _, _, _, .app _ f f' a a' A B T₀ v w hf hc hB hTy ha hr =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .app Γ' f f' a a' A B T₀ v w
        (parRedT_assumpCtx hcl hcc hf)
        (tyConvT_ctx hcl hccT hc)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB)
        (hasTyT_ctx hcl hccT hTy)
        (parRedT_assumpCtx hcl hcc ha)
        (hasTyT_ctx hcl hccT hr)
  | _, Γ', hcc, _, _, _, .beta _ A body body' arg arg' B u v w
      hA hB hTy hb ha hred =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .beta Γ' A body body' arg arg' B u v w
        (hasTyT_ctx hcl hccT hA)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB)
        (hasTyT_ctx hcl hccT hTy)
        (parRedT_assumpCtx hcl (.same (.assumption A) hcc) hb)
        (parRedT_assumpCtx hcl hcc ha)
        (hasTyT_ctx hcl hccT hred)
  | _, Γ', hcc, _, _, _, .lam _ A A' b b' B u v hA hA0 hB hb hr =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .lam Γ' A A' b b' B u v
        (convT_ctx hcl hccT hA)
        (hasTyT_ctx hcl hccT hA0)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB)
        (parRedT_assumpCtx hcl (.same (.assumption A) hcc) hb)
        (hasTyT_ctx hcl hccT hr)
  | _, Γ', hcc, _, _, _, .pi _ A A' B B' u v hA hc hB hcB hrt =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .pi Γ' A A' B B' u v
        (hasTyT_ctx hcl hccT hA)
        (convT_ctx hcl hccT hc)
        (hasTyT_ctx hcl (.same (.assumption A) hccT) hB)
        (convT_ctx hcl (.same (.assumption A) hccT) hcB)
        (hasTyT_ctx hcl hccT hrt)
  | _, Γ', hcc, _, _, _, .letE _ A A' v v' b b' B u w
      hc hA hv hB hTy hb hrt =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .letE Γ' A A' v v' b b' B u w
        (convT_ctx hcl hccT hc)
        (hasTyT_ctx hcl hccT hA)
        (parRedT_assumpCtx hcl hcc hv)
        (hasTyT_ctx hcl (.same (.letBinding A v) hccT) hB)
        (hasTyT_ctx hcl hccT hTy)
        (parRedT_assumpCtx hcl (.same (.letBinding A v) hcc) hb)
        (hasTyT_ctx hcl hccT hrt)
  | _, Γ', hcc, _, _, _, .zeta _ A v v' b b' B u w
      hA hv hB hTy hb hred =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .zeta Γ' A v v' b b' B u w
        (hasTyT_ctx hcl hccT hA)
        (parRedT_assumpCtx hcl hcc hv)
        (hasTyT_ctx hcl (.same (.letBinding A v) hccT) hB)
        (hasTyT_ctx hcl hccT hTy)
        (parRedT_assumpCtx hcl (.same (.letBinding A v) hcc) hb)
        (hasTyT_ctx hcl hccT hred)
  | _, Γ', hcc, _, _, _, .iotaSpine _ lhs lhs' rhs T hstep hι hred hrhs =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .iotaSpine Γ' lhs lhs' rhs T
        (parRedT_assumpCtx hcl hcc hstep)
        hι
        (hasTyT_ctx hcl hccT hred)
        (hasTyT_ctx hcl hccT hrhs)
  | _, Γ', hcc, _, _, _, .iotaStarK _ w major Tm rhs T rl afs
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      .iotaStarK Γ' w major Tm rhs T rl afs hrl hsel hfam
        (hasTyT_ctx hcl hccT hmajor)
        (hasTyT_ctx hcl hccT hmk)
        (hasTyT_ctx hcl hccT hTm0)
        hι
        (hasTyT_ctx hcl hccT hlι)
        (hasTyT_ctx hcl hccT hlhs)
        (hasTyT_ctx hcl hccT hrhs)
  | _, Γ', hcc, _, _, _, .iotaStarKEta _ w f A B Tm rhs u rl afs
      happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs =>
      let hccT := assumpCtxConvT_to_ctxConvT hcc
      let hccA := CtxConvT.same (.assumption A) hccT
      .iotaStarKEta Γ' w f A B Tm rhs u rl afs happ
        (hasTyT_ctx hcl hccT hA)
        (hasTyT_ctx hcl hccT hf)
        hrl hsel hfam
        (hasTyT_ctx hcl hccA hmajor)
        (hasTyT_ctx hcl hccA hmk)
        (hasTyT_ctx hcl hccA hTm0)
        hι
        (hasTyT_ctx hcl hccA hlι)
        (hasTyT_ctx hcl hccA hlhs)
        (hasTyT_ctx hcl hccA hrhs)
  | _, Γ', hcc, _, _, _, .lit _ t T hexp =>
      .lit Γ' t T (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hexp)
  | _, Γ', hcc, _, _, _, .eta _ f f' A B hf hl =>
      .eta Γ' f f' A B
        (parRedT_assumpCtx hcl hcc hf)
        (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hl)
  | _, Γ', hcc, _, _, _, .peq _ p q T h =>
      .peq Γ' p q T (peqLeafT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) h)
  | _, Γ', hcc, _, _, _, .conv _ a b A A' h hc =>
      .conv Γ' a b A A'
        (parRedT_assumpCtx hcl hcc h)
        (tyConvT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) hc)

/-- Head-binder `AssumpCtxConvT` built directly from `hcA : ConvT E n Γ A A' (.sort u)`
    at `EnvWfT E` and `CtxWfT E n Γ` (deriving `hA' : HasTyT E n Γ A' (.sort u)` via
    `endpoints3_of_envWfT`). -/
def assumpCtxConvT_of_convA {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hcA : ConvT E n Γ A A' (.sort u)) :
    HasTyT E n Γ A' (.sort u) ×'
      AssumpCtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ) :=
  let hA' : HasTyT E n Γ A' (.sort u) :=
    (endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW) hΓ hcA).2.1
  ⟨hA', .assumption (assumpCtxConvT_refl Γ) hA hA' hcA⟩

/-- Instantiating `.bvar c` at `c` cancels `lift (c + 1) 1`. -/
theorem instantiate_bvar_lift_succ (c : Nat) (e : Expr Nat) :
    instantiate c (.bvar c) (lift (c + 1) 1 e) = e := by
  induction e generalizing c with
  | bvar i =>
      simp only [lift]
      split
      · simp only [instantiate]
        rw [if_neg (by omega : ¬ i + 1 = c), if_pos (by omega : c < i + 1)]
        exact congrArg Expr.bvar (Nat.add_sub_cancel i 1)
      · simp only [instantiate]
        by_cases h2 : i = c
        · subst h2; rw [if_pos rfl]
        · rw [if_neg (by omega : ¬ i = c), if_neg (by omega : ¬ c < i)]
  | sort _ | const _ _ | lit _ => rfl
  | app f x ihf ihx =>
      simp only [lift, instantiate, ihf, ihx]
  | lam a b iha ihb =>
      simp only [lift, instantiate, iha]
      rw [if_pos (Nat.zero_le c)]
      exact congrArg (Expr.lam a) (ihb (c + 1))
  | pi a b iha ihb =>
      simp only [lift, instantiate, iha]
      rw [if_pos (Nat.zero_le c)]
      exact congrArg (Expr.pi a) (ihb (c + 1))
  | letE a v b iha ihv ihb =>
      simp only [lift, instantiate, iha, ihv]
      rw [if_pos (Nat.zero_le c)]
      exact congrArg (Expr.letE a v) (ihb (c + 1))

/-- Construct the stepped `IotaWitness E` when the recursor's universe levels
    `w.ls` step to `ls'`, its `preMajor` spine steps to `pre'`, and the selected
    minor slot `w.nparams + 1 + w.ctorIdx` steps to `minor'`. -/
def replacePreMajorWitness {E : ResolvedEnv} (w : IotaWitness E)
    (ls' : List Level) (pre' : List (Expr Nat)) (minor' : Expr Nat)
    (hls : eqNList w.ls ls')
    (hlenP : pre'.length = w.preMajor.length)
    (hmin' : pre'[w.nparams + 1 + w.ctorIdx]? = some minor') :
    IotaWitness E :=
  have htkLen : (pre'.take w.nparams).length = w.nparams := by
    simp only [List.length_take, hlenP, w.hpre]; omega
  have htelC : isPiTel (w.nparams + w.fields.length)
      (instantiateLevels ls' w.ctorMember.mtype) = true :=
    peelPis_isPiTel _ _ (peelPis_instantiateLevels ls' _ _ w.hpeel)
  have htelCn : isPiTel w.nparams
      (instantiateLevels ls' w.ctorMember.mtype) = true :=
    isPiTel_le (by omega) htelC
  let ⟨ctorAfter', hca'⟩ :=
    applyTel_isPiTel w.nparams (instantiateLevels ls' w.ctorMember.mtype)
      (pre'.take w.nparams) htkLen htelCn
  have hctorTel' : isPiTel w.kinds.length ctorAfter' = true := by
    rw [w.hlen]
    exact isPiTel_of_applyTel w.nparams w.fields.length
      (instantiateLevels ls' w.ctorMember.mtype) (pre'.take w.nparams) htkLen
      (Nat.add_comm w.nparams w.fields.length ▸ htelC) hca'
  have hpeelK : peelPis (w.nparams + w.kinds.length) w.ctorMember.mtype =
      some (w.ctorDoms, w.ctorResult) := by
    rw [w.hlen]; exact w.hpeel
  have hpad :
      directRecConstHead
        (List.replicate w.nparams RecKind.plain ++ w.kinds)
        (instantiateLevels ls' w.ctorMember.mtype) = true := by
    rw [directRecConstHead_instantiateLevels]
    exact directRecConstHead_plain_prefix_of_analyzeFields
      w.familyRef w.nparams w.kinds w.ctorMember.mtype hpeelK w.hkinds
  have hfamTel' : directRecConstHead w.kinds ctorAfter' = true :=
    directRecConstHead_applyTel w.kinds (pre'.take w.nparams)
      (instantiateLevels ls' w.ctorMember.mtype) ctorAfter' hca'
      (by rw [htkLen, w.hlen]; exact htelC)
      (by rw [htkLen]; exact hpad)
  have hpadRes :
      resultConstHead
        (List.replicate w.nparams RecKind.plain ++ w.kinds)
        (instantiateLevels ls' w.ctorMember.mtype) = true := by
    rw [resultConstHead_instantiateLevels]
    exact resultConstHead_of_peelPis
      (List.replicate w.nparams RecKind.plain ++ w.kinds)
      w.ctorMember.mtype
      (by rw [List.length_append, replicate_length]; exact hpeelK)
      (isFamilyApp_spineHeadConst w.hfamApp)
  have hresTel' : resultConstHead w.kinds ctorAfter' = true :=
    resultConstHead_applyTel w.kinds (pre'.take w.nparams)
      (instantiateLevels ls' w.ctorMember.mtype) ctorAfter' hca'
      (by rw [htkLen, w.hlen]; exact htelC)
      (by rw [htkLen]; exact hpadRes)
  { recRef := w.recRef
    ctorRef := w.ctorRef
    ls := ls'
    lsC := w.lsC
    recMember := w.recMember
    ctorMember := w.ctorMember
    hrec := w.hrec
    hctor := w.hctor
    hrecK := w.hrecK
    hctorK := w.hctorK
    preMajor := pre'
    fields := w.fields
    ctorParams := w.ctorParams
    kinds := w.kinds
    minor := minor'
    hlen := w.hlen
    familyRef := w.familyRef
    famMember := w.famMember
    hfam := w.hfam
    hfamK := w.hfamK
    nparams := w.nparams
    nindices := w.nindices
    nMinors := w.nMinors
    ctorIdx := w.ctorIdx
    hctorParams := w.hctorParams
    hnpar := w.hnpar
    hnidx := w.hnidx
    hnmin := w.hnmin
    hidx := w.hidx
    hctorIdx := w.hctorIdx
    hrecIdx := w.hrecIdx
    hpre := by rw [hlenP]; exact w.hpre
    hminor := hmin'
    ctorDoms := w.ctorDoms
    ctorResult := w.ctorResult
    hpeel := w.hpeel
    hfamApp := w.hfamApp
    hkinds := w.hkinds
    recDoms := w.recDoms
    recBody := w.recBody
    hpeelRec := w.hpeelRec
    hrecBody := w.hrecBody
    hmajorTy := w.hmajorTy
    hrecClosed := w.hrecClosed
    hctorClosed := w.hctorClosed
    hlsLen := (eqNList_length w.ls ls' hls).symm.trans w.hlsLen
    ctorAfterParams := ctorAfter'
    hctorAfter := hca'
    hctorTel := hctorTel'
    hfamTel := hfamTel'
    hresTel := hresTel' }

theorem replacePreMajorWitness_happ {E : ResolvedEnv} (w : IotaWitness E)
    {ls' : List Level} {xs' : List (Expr Nat)} {minor' f' : Expr Nat}
    (hf'_eq : f' = foldApps (.const w.recRef ls') xs')
    (hls : eqNList w.ls ls')
    (hlenP : (xs'.map (lift 0 1)).length = w.preMajor.length)
    (hmin' : (xs'.map (lift 0 1))[w.nparams + 1 + w.ctorIdx]? = some minor') :
    let w' := replacePreMajorWitness w ls' (xs'.map (lift 0 1)) minor' hls hlenP hmin'
    recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
      .app (lift 0 1 f') (.bvar 0) := by
  intro w'
  change foldApps (.const w.recRef ls') (xs'.map (lift 0 1) ++ [.bvar 0]) =
    .app (lift 0 1 f') (.bvar 0)
  rw [foldApps_snoc, hf'_eq, foldApps_lift]
  rfl

/-- Derive the stepped η-expanded body typing
    `hlhs' : HasTyT E n (.assumption A :: Γ) (recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0)) B`
    directly from `hf' : HasTyT E n Γ f' (.pi A B)` and `happ'`. -/
def stepped_hlhs {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {w' : IotaWitness E} {f' A B : Expr Nat}
    (happ' : recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
      .app (lift 0 1 f') (.bvar 0))
    (hf' : HasTyT E n Γ f' (.pi A B)) :
    HasTyT E n (.assumption A :: Γ)
      (recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0)) B := by
  have hf'_lift : HasTyT E n (.assumption A :: Γ) (lift 0 1 f')
      (.pi (lift 0 1 A) (lift 1 1 B)) :=
    hasTyTWeaken (.assumption A) hcl (c := 0) hf'
  have hb0 : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A) :=
    .bvar (.assumption A :: Γ) 0 (lift 0 1 A) rfl
  have happ0 : HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 f') (.bvar 0))
      (instantiate0 (.bvar 0) (lift 1 1 B)) :=
    .app (.assumption A :: Γ) (lift 0 1 f') (.bvar 0) (lift 0 1 A) (lift 1 1 B)
      hf'_lift hb0
  rw [happ', ← instantiate_bvar_lift_succ 0 B]
  exact happ0

/-- Derive the stepped synthesized-redex typing
    `hlι' : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w') B`
    directly from `hf' : HasTyT E n Γ f' (.pi A B)`, `hmajor`, `hmk`, and `hTm0`. -/
def stepped_hlι {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {w w' : IotaWitness E} {f' A B Tm : Expr Nat} {u v : Level}
    (hctor : ctorMajor w' = ctorMajor w)
    (happ' : recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
      .app (lift 0 1 f') (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf' : HasTyT E n Γ f' (.pi A B))
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero)) :
    HasTyT E n (.assumption A :: Γ) (iotaLhsOf w') B := by
  have hlhs_eq : iotaLhsOf w' = .app (lift 0 1 f') (ctorMajor w) := by
    have h1 : foldApps (.const w'.recRef w'.ls) w'.preMajor = lift 0 1 f' := by
      rw [recCall, foldApps_snoc] at happ'
      exact (Expr.app.inj happ').1
    change foldApps (.const w'.recRef w'.ls) (w'.preMajor ++ [ctorMajor w']) =
      .app (lift 0 1 f') (ctorMajor w)
    rw [foldApps_snoc, h1, hctor]
  let ⟨T_lk, hlk, hc_lk⟩ := hasTyTInv_bvar hmajor rfl
  have hTeq : T_lk = lift 0 1 A := Option.some.inj hlk.symm
  have hc_ATm : TyConvT E n (.assumption A :: Γ) (lift 0 1 A) Tm :=
    hTeq ▸ hc_lk
  have hmk_A : HasTyT E n (.assumption A :: Γ) (ctorMajor w) (lift 0 1 A) :=
    hasTyT_of_tyConvT hmk hc_ATm.symmT
  have hf'_lift : HasTyT E n (.assumption A :: Γ) (lift 0 1 f')
      (.pi (lift 0 1 A) (lift 1 1 B)) :=
    hasTyTWeaken (.assumption A) hcl (c := 0) hf'
  have happ_mk : HasTyT E n (.assumption A :: Γ)
      (.app (lift 0 1 f') (ctorMajor w)) (instantiate0 (ctorMajor w) (lift 1 1 B)) :=
    .app (.assumption A :: Γ) (lift 0 1 f') (ctorMajor w) (lift 0 1 A) (lift 1 1 B)
      hf'_lift hmk_A
  have hc_irr : ConvT E n (.assumption A :: Γ) (ctorMajor w) (.bvar 0) (lift 0 1 A) :=
    convT_of_tyConv
      (.irr (.assumption A :: Γ) Tm (ctorMajor w) (.bvar 0) hTm0 hmk hmajor)
      hc_ATm.symmT
  have hA_lift : HasTyT E n (.assumption A :: Γ) (lift 0 1 A) (.sort u) :=
    hasTyTWeaken (.assumption A) hcl (c := 0) hA
  have hB_lift1 : HasTyT E n (.assumption (lift 0 1 A) :: .assumption A :: Γ)
      (lift 1 1 B) (.sort v) :=
    hasTyTWeaken (.assumption A) hcl (c := 1) hB
  have hlamB_lift : HasTyT E n (.assumption A :: Γ)
      (.lam (lift 0 1 A) (lift 1 1 B)) (.pi (lift 0 1 A) (.sort v)) :=
    .lam (.assumption A :: Γ) (lift 0 1 A) u (lift 1 1 B) (.sort v) hA_lift hB_lift1
  have hb0 : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A) :=
    .bvar (.assumption A :: Γ) 0 (lift 0 1 A) rfl
  have hc_beta_mk : ConvT E n (.assumption A :: Γ)
      (.app (.lam (lift 0 1 A) (lift 1 1 B)) (ctorMajor w))
      (instantiate0 (ctorMajor w) (lift 1 1 B)) (.sort v) :=
    .beta (.assumption A :: Γ) (lift 0 1 A) (lift 1 1 B) (ctorMajor w) (.sort v) u
      hA_lift hB_lift1 hmk_A
  have hc_beta_b0 : ConvT E n (.assumption A :: Γ)
      (.app (.lam (lift 0 1 A) (lift 1 1 B)) (.bvar 0))
      (instantiate0 (.bvar 0) (lift 1 1 B)) (.sort v) :=
    .beta (.assumption A :: Γ) (lift 0 1 A) (lift 1 1 B) (.bvar 0) (.sort v) u
      hA_lift hB_lift1 hb0
  have hc_app : ConvT E n (.assumption A :: Γ)
      (.app (.lam (lift 0 1 A) (lift 1 1 B)) (ctorMajor w))
      (.app (.lam (lift 0 1 A) (lift 1 1 B)) (.bvar 0)) (.sort v) :=
    .app (.assumption A :: Γ) (.lam (lift 0 1 A) (lift 1 1 B))
      (.lam (lift 0 1 A) (lift 1 1 B)) (ctorMajor w) (.bvar 0) (lift 0 1 A) (.sort v)
      (.refl _ _ _ hlamB_lift) hc_irr
  have hc_B0 : ConvT E n (.assumption A :: Γ)
      (instantiate0 (ctorMajor w) (lift 1 1 B))
      (instantiate0 (.bvar 0) (lift 1 1 B)) (.sort v) :=
    ConvT.trans _ _ _ _ _ (ConvT.symm _ _ _ _ hc_beta_mk)
      (ConvT.trans _ _ _ _ _ hc_app hc_beta_b0)
  have hc_B : ConvT E n (.assumption A :: Γ)
      (instantiate0 (ctorMajor w) (lift 1 1 B)) B (.sort v) := by
    have h := hc_B0
    rw [show instantiate0 (.bvar 0) (lift 1 1 B) = B from
      instantiate_bvar_lift_succ 0 B] at h
    exact h
  rw [hlhs_eq]
  exact .conv (.assumption A :: Γ) (.app (lift 0 1 f') (ctorMajor w))
    (instantiate0 (ctorMajor w) (lift 1 1 B)) B v happ_mk hc_B

/-- General proof-root witness on a `const recRef` spine of length `≤ k` at level
    class `ls₀`. At `eqEnvT` and `recRef = 65`, this is definitionally
    `HasConst65ProofRoot eqEnvT n Γ ls₀ k`. -/
def HasRecProofRoot (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (recRef : Nat) (ls₀ : List Level) (k : Nat) : Prop :=
  ∃ (ls : List Level) (xs : List (Expr Nat)) (P : Expr Nat),
    xs.length ≤ k ∧ eqNList ls ls₀ ∧
    Nonempty (HasTyT E n Γ P (.sort .zero)) ∧
    Nonempty (HasTyT E n Γ (foldApps (.const recRef ls) xs) P)

theorem hasRecProofRoot_mono {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {recRef : Nat} {ls₀ : List Level} {k₁ k₂ : Nat} (hle : k₁ ≤ k₂)
    (h : HasRecProofRoot E n Γ recRef ls₀ k₁) :
    HasRecProofRoot E n Γ recRef ls₀ k₂ := by
  rcases h with ⟨ls, xs, P, hlen, hls, hP, hp⟩
  exact ⟨ls, xs, P, Nat.le_trans hlen hle, hls, hP, hp⟩

/-- General recursor proof-root exclusion from sort uniqueness: if `w.recMember.mtype`
    instantiated at any `ls` with `eqNList ls ls₀` has a sort that evaluates under `ρ`
    to a positive natural number `m + 1`, then `HasRecProofRoot E n Γ w.recRef ls₀ k`
    is impossible at every spine length `k`. -/
theorem no_rec_proof_root_of_sortUniq {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ →
      HasTyT E n Γ T (.sort u) →
      HasTyT E n Γ T (.sort v) →
      eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : IotaWitness E) {ls₀ : List Level} (ρ : Nat → Option Nat)
    (hPosRecSort : ∀ {ls : List Level},
      eqNList ls ls₀ → ls.length = w.recMember.arity → levelsBounded n ls = true →
      ∃ (s : Level) (m : Nat),
        Nonempty (HasTyT E n Γ (instantiateLevels ls w.recMember.mtype) (.sort s)) ∧
        eval ρ s = some (m + 1))
    (k : Nat) :
    ¬ HasRecProofRoot E n Γ w.recRef ls₀ k := by
  rintro ⟨ls, xs, P, _, hls, ⟨hP⟩, ⟨hp⟩⟩
  obtain ⟨T₀, w₀, hw₀, ⟨hT₀⟩, ⟨hc_const⟩⟩ :=
    hasTyT_foldApps_sort_zero_inv hW hSortUniq hΓ xs hp hP (ρ := ρ) rfl
  obtain ⟨m, hres, hlen, hwf, hcv⟩ := hasTyTInv_const hc_const rfl
  have hm : m = w.recMember := by
    have h1 := w.hrec
    rw [hres] at h1
    exact Option.some.inj h1
  subst hm
  obtain ⟨s, m_pos, ⟨hRecTy⟩, heval_pos⟩ := hPosRecSort hls hlen hwf
  have heq : eqN s w₀ :=
    tyConvT_sort_eqN_of_sortUniq hW hSortUniq hΓ hRecTy hT₀ hcv
  have hpos0 : some (m_pos + 1) = some 0 :=
    heval_pos.symm.trans ((heq ρ).trans hw₀)
  cases hpos0

theorem witness_preMajor_length_eq {E : ResolvedEnv}
    (w₁ w₂ : IotaWitness E) (href : w₁.recRef = w₂.recRef) :
    w₁.preMajor.length = w₂.preMajor.length := by
  have hrec : w₁.recMember = w₂.recMember := by
    have h1 := w₁.hrec
    rw [href, w₂.hrec] at h1
    exact (Option.some.inj h1).symm
  have hn1 := w₁.hnmin
  have hn2 := w₂.hnmin
  have hp1 := w₁.hpre
  have hp2 := w₂.hpre
  rw [hrec] at hn1
  omega

theorem witnessS_preMajor_length_eq {E : ResolvedEnv}
    (w₁ : IotaWitness E) (w₂ : IotaWitnessS E) (href : w₁.recRef = w₂.recRef) :
    w₁.preMajor.length = w₂.preMajor.length := by
  have hrec : w₁.recMember = w₂.recMember := by
    have h1 := w₁.hrec
    rw [href, w₂.hrec] at h1
    exact (Option.some.inj h1).symm
  have hn1 := w₁.hnmin
  have hn2 := w₂.hnmin
  have hp1 := w₁.hpre
  have hp2 := w₂.hpre
  rw [hrec] at hn1
  omega

theorem short_witness_not_K_source {E : ResolvedEnv} (w : IotaWitness E)
    {ls : List Level} {xs : List (Expr Nat)}
    (hshort : xs.length ≤ w.preMajor.length)
    (wK : IotaWitness E) (major : Expr Nat)
    (heq : recCall (.const wK.recRef wK.ls) wK.preMajor major =
      foldApps (.const w.recRef ls) xs) : False := by
  have hs := congrArg appsSpine heq
  rw [appsSpine_recCall, appsSpine_foldApps_const] at hs
  have hh : Expr.const wK.recRef wK.ls = Expr.const w.recRef ls :=
    congrArg Prod.fst hs
  have href : wK.recRef = w.recRef := by injection hh
  have hl := congrArg (fun z : Expr Nat × List (Expr Nat) => z.2.length) hs
  have hlen : wK.preMajor.length + 1 = xs.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using hl
  have hpm := witness_preMajor_length_eq w wK href.symm
  omega

theorem short_witness_not_derivedIotaU {E : ResolvedEnv} (w : IotaWitness E)
    {ls : List Level} {xs : List (Expr Nat)} {lhs rhs : Expr Nat}
    (hshort : xs.length ≤ w.preMajor.length)
    (hI : DerivedIotaU E lhs rhs)
    (heq : lhs = foldApps (.const w.recRef ls) xs) : False := by
  cases hI with
  | ofU wI =>
      exact short_witness_not_K_source w hshort wI (ctorMajor wI) heq
  | ofUS wS =>
      have hs := congrArg appsSpine heq
      change appsSpine (foldApps (.const wS.recRef wS.ls)
        (wS.preMajor ++ [foldApps (.const wS.ctorRef wS.lsC)
          (wS.ctorParams ++ wS.fields)])) =
        appsSpine (foldApps (.const w.recRef ls) xs) at hs
      rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
      have hh : Expr.const wS.recRef wS.ls = Expr.const w.recRef ls :=
        congrArg Prod.fst hs
      have href : wS.recRef = w.recRef := by injection hh
      have hl := congrArg (fun z : Expr Nat × List (Expr Nat) => z.2.length) hs
      have hlen : wS.preMajor.length + 1 = xs.length := by
        simpa only [List.length_append, List.length_cons, List.length_nil] using hl
      have hpm := witnessS_preMajor_length_eq w wS href.symm
      omega

theorem witness_rec_not_delta {E : ResolvedEnv} (w : IotaWitness E)
    {r : Nat} {ls1 ls : List Level} {m : CheckedMember} {xs : List (Expr Nat)}
    (hres : E.members r = some m)
    (htr : transparent m.mclass = true)
    (heq : Expr.const r ls1 = foldApps (.const w.recRef ls) xs) : False := by
  have hh := appsSpine_fst_of_eq_foldApps_const heq
  injection hh with hr _
  subst hr
  have hm : m = w.recMember := by
    have h1 := w.hrec
    rw [hres] at h1
    exact Option.some.inj h1
  subst hm
  rw [w.hrecK] at htr
  exact nomatch htr

/-- Per-argument step extracted from a `ParRedT` step on a recursor spine:
    either `x` stays definitionally unchanged (`refl`), or `x` steps by
    `ParRedT` at some type `A` (`parRed`), or `x` steps by raw `PEqT` inside a
    `PEqT.app` spine (`peq`). -/
inductive RecArgStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Type where
  | refl (x : Expr Nat) : RecArgStep E n Γ x x
  | parRed {x x' : Expr Nat} (A : Expr Nat)
      (h : ParRedT (PEqLeafT E n) E n Γ x x' A) :
      RecArgStep E n Γ x x'
  | peq {x x' : Expr Nat} (h : PEqT E n Γ x x') :
      RecArgStep E n Γ x x'

/-- Pointwise argument-list step extracted from a `ParRedT` step on a recursor
    spine. -/
inductive RecArgsStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    List (Expr Nat) → List (Expr Nat) → Type where
  | nil : RecArgsStep E n Γ [] []
  | cons {x x' : Expr Nat} {xs xs' : List (Expr Nat)}
      (h : RecArgStep E n Γ x x')
      (t : RecArgsStep E n Γ xs xs') :
      RecArgsStep E n Γ (x :: xs) (x' :: xs')

def recArgsStep_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (xs : List (Expr Nat)) → RecArgsStep E n Γ xs xs
  | [] => .nil
  | x :: xs => .cons (.refl x) (recArgsStep_refl xs)

def recArgsStep_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs xs' : List (Expr Nat)} {x x' : Expr Nat}
    (h : RecArgsStep E n Γ xs xs')
    (hx : RecArgStep E n Γ x x') :
    RecArgsStep E n Γ (xs ++ [x]) (xs' ++ [x']) :=
  match h with
  | .nil => .cons hx .nil
  | .cons hhd htt => .cons hhd (recArgsStep_snoc htt hx)

theorem recArgsStep_length {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs xs' : List (Expr Nat)} → RecArgsStep E n Γ xs xs' →
    xs'.length = xs.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => congrArg (· + 1) (recArgsStep_length t)

def recArgsStep_get {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs xs' : List (Expr Nat)} → RecArgsStep E n Γ xs xs' →
    (i : Nat) → {x : Expr Nat} → xs[i]? = some x →
    Σ' x' : Expr Nat, (xs'[i]? = some x') ×' RecArgStep E n Γ x x'
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons (x' := x') h _, 0, _, hget =>
      ⟨x', List.getElem?_cons_zero,
        (Option.some.inj (List.getElem?_cons_zero.symm.trans hget)) ▸ h⟩
  | _, _, .cons _ t, i + 1, _, hget =>
      let r := recArgsStep_get t i (List.getElem?_cons_succ.symm.trans hget)
      ⟨r.1, List.getElem?_cons_succ.trans r.2.1, r.2.2⟩

/-- `Type`-valued decomposition of a raw `PEqT` step on a recursor spine of
    length `≤ k_max` when `HasRecProofRoot` is excluded. -/
def peqT_rec_spine_decomp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {recRef : Nat} {ls₀ : List Level} {k_max : Nat}
    (hNoPrf : ¬ HasRecProofRoot E n Γ recRef ls₀ k_max) :
    {a b : Expr Nat} → PEqT E n Γ a b →
    ∀ {ls : List Level} {xs : List (Expr Nat)},
      a = foldApps (.const recRef ls) xs →
      xs.length ≤ k_max →
      eqNList ls ls₀ →
      Σ' (ls' : List Level) (xs' : List (Expr Nat)),
        (b = foldApps (.const recRef ls') xs') ×'
        PLift (eqNList ls' ls₀) ×'
        RecArgsStep E n Γ xs xs'
  | _, _, .const _ r ls1 ls2 hc, ls, xs, heq, _, hls => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls1
          subst hr
          subst hls1
          exact ⟨ls2, [], rfl, ⟨eqNList_trans (eqNList_symm hc) hls⟩, .nil⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const recRef ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .app _ f₀ f₀' x x' hf₀ hx, ls, xs, heq, hk, hls => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by intro hh; cases hh
          let ⟨ys, y, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const recRef ls) (z :: zs) =
              .app (foldApps (.const recRef ls) ys) y := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 hx0
          have hlen_ys : ys.length ≤ k_max := by
            have hl := congrArg List.length hsplit
            simp only [List.length_cons, List.length_append, List.length_singleton] at hl hk
            omega
          let ⟨ls', ys', hf₀'_eq, ⟨hls'⟩, hargs_ys⟩ :=
            peqT_rec_spine_decomp hNoPrf hf₀ hf0 hlen_ys hls
          have hb_eq : Expr.app f₀' x' = foldApps (.const recRef ls') (ys' ++ [x']) := by
            rw [hf₀'_eq, foldApps_snoc]
          have hargs' : RecArgsStep E n Γ (z :: zs) (ys' ++ [x']) := by
            rw [hsplit]
            exact recArgsStep_snoc hargs_ys (.peq (hx0 ▸ hx))
          exact ⟨ls', ys' ++ [x'], hb_eq, ⟨hls'⟩, hargs'⟩
  | _, _, .proof _ _ _ P _ hP _ hp _, ls, xs, heq, hk, hls =>
      False.elim (hNoPrf ⟨ls, xs, P, hk, hls, ⟨hP⟩, ⟨heq ▸ hp⟩⟩)
  | _, _, .bvar .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .sort .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .lam .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .pi .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .letE .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, .lit .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- A proper prefix `xs.length < w.preMajor.length` of a recursor spine cannot
    be the η-contracted source `f_eta` of `ParRedT.iotaStarKEta`. -/
theorem short_witness_not_etaK_source {E : ResolvedEnv} (w : IotaWitness E)
    {ls : List Level} {xs : List (Expr Nat)}
    (hshort : xs.length < w.preMajor.length)
    (wEta : IotaWitness E) (f_eta : Expr Nat)
    (happ_eta : recCall (.const wEta.recRef wEta.ls) wEta.preMajor (.bvar 0) =
      .app (lift 0 1 f_eta) (.bvar 0))
    (heq : f_eta = foldApps (.const w.recRef ls) xs) : False := by
  obtain ⟨h1, _, h3⟩ := iotaStarKEta_head happ_eta
  rw [heq, appsSpine_foldApps_const] at h1 h3
  dsimp only at h1 h3
  injection h1 with href _
  have hpm := witness_preMajor_length_eq w wEta href
  have hpEta := wEta.hpre
  omega

/-- `Type`-valued decomposition of ANY `ParRedT` step on a proper recursor
    pre-major spine prefix (`xs.length < w.preMajor.length`) under
    `¬ HasRecProofRoot`. Requires NO `NoEtaKStep` premise because
    `ParRedT.iotaStarKEta` cannot fire below arity `w.preMajor.length`
    (`short_witness_not_etaK_source`), while `ParRedT.iotaStarKEta` inside
    spine arguments is captured in `RecArgStep.parRed`. Covers all 18
    `ParRedT` constructors. -/
def parRedT_rec_spine_lt_decomp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length) :
    {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T →
    ∀ {ls : List Level} {xs : List (Expr Nat)},
      a = foldApps (.const w.recRef ls) xs →
      xs.length < w.preMajor.length →
      eqNList ls ls₀ →
      Σ' (ls' : List Level) (xs' : List (Expr Nat)),
        (b = foldApps (.const w.recRef ls') xs') ×'
        PLift (eqNList ls' ls₀) ×'
        RecArgsStep E n Γ xs xs'
  | _, _, _, .refl _ _ _ _, ls, xs, heq, _, hls =>
      ⟨ls, xs, heq, ⟨hls⟩, recArgsStep_refl xs⟩
  | _, _, _, .consts _ r ls1 ls2 _ hc _ _, ls, xs, heq, _, hls => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls1
          subst hr
          subst hls1
          exact ⟨ls2, [], rfl, ⟨eqNList_trans (eqNList_symm hc) hls⟩, .nil⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app _ f₀ f₀' x x' A_x _ _ _ _ hf₀ _ _ _ hx _, ls, xs, heq, hk, hls => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by intro hh; cases hh
          let ⟨ys, y, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const w.recRef ls) (z :: zs) =
              .app (foldApps (.const w.recRef ls) ys) y := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 hx0
          have hlen_ys : ys.length < w.preMajor.length := by
            have hl := congrArg List.length hsplit
            simp only [List.length_cons, List.length_append, List.length_singleton] at hl hk
            omega
          let ⟨ls', ys', hf₀'_eq, ⟨hls'⟩, hargs_ys⟩ :=
            parRedT_rec_spine_lt_decomp w hNoPrf hf₀ hf0 hlen_ys hls
          have hb_eq : Expr.app f₀' x' = foldApps (.const w.recRef ls') (ys' ++ [x']) := by
            rw [hf₀'_eq, foldApps_snoc]
          have hargs' : RecArgsStep E n Γ (z :: zs) (ys' ++ [x']) := by
            rw [hsplit]
            exact recArgsStep_snoc hargs_ys (.parRed A_x (hx0 ▸ hx))
          exact ⟨ls', ys' ++ [x'], hb_eq, ⟨hls'⟩, hargs'⟩
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, xs, heq, hk, hls => by
      let ⟨ls', xs', hstep_eq, _, hargs⟩ :=
        parRedT_rec_spine_lt_decomp w hNoPrf hstep heq hk hls
      have hlen' : xs'.length ≤ w.preMajor.length := by
        rw [recArgsStep_length hargs]
        exact Nat.le_of_lt hk
      exact False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w (Nat.le_of_lt hk) wK major heq)
  | _, _, _, .iotaStarKEta _ wEta f_eta _ _ _ _ _ _ _ happ_eta _ _ _ _ _ _ _ _ _ _ _ _,
      _, _, heq, hk, _ =>
      False.elim (short_witness_not_etaK_source w hk wEta f_eta happ_eta heq)
  | _, _, _, .peq _ _ _ _ leaf, _, _, heq, hk, hls =>
      peqT_rec_spine_decomp hNoPrf leaf.1 heq (Nat.le_of_lt hk) hls
  | _, _, _, .conv _ _ _ _ _ hinner _, _, _, heq, hk, hls =>
      parRedT_rec_spine_lt_decomp w hNoPrf hinner heq hk hls
  | _, _, _, .sortEq .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- True iff `h` is a root `ParRedT.iotaStarKEta` step (possibly wrapped in
    `ParRedT.conv`). -/
def IsRootEtaKStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} : ParRedT (PEqLeafT E n) E n Γ a b T → Prop
  | .iotaStarKEta .. => True
  | .conv _ _ _ _ _ hinner _ => IsRootEtaKStep hinner
  | _ => False

theorem isRootEtaKStep_target_is_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    IsRootEtaKStep h → ∃ A rhs, b = .lam A rhs
  | _, _, _, .iotaStarKEta _ _ _ A _ _ rhs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ =>
      ⟨A, rhs, rfl⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, hroot =>
      isRootEtaKStep_target_is_lam hinner hroot
  | _, _, _, .refl .., hroot => False.elim hroot
  | _, _, _, .sortEq .., hroot => False.elim hroot
  | _, _, _, .consts .., hroot => False.elim hroot
  | _, _, _, .bvarZeta .., hroot => False.elim hroot
  | _, _, _, .delta .., hroot => False.elim hroot
  | _, _, _, .app .., hroot => False.elim hroot
  | _, _, _, .beta .., hroot => False.elim hroot
  | _, _, _, .lam .., hroot => False.elim hroot
  | _, _, _, .pi .., hroot => False.elim hroot
  | _, _, _, .letE .., hroot => False.elim hroot
  | _, _, _, .zeta .., hroot => False.elim hroot
  | _, _, _, .iotaSpine .., hroot => False.elim hroot
  | _, _, _, .iotaStarK .., hroot => False.elim hroot
  | _, _, _, .lit .., hroot => False.elim hroot
  | _, _, _, .eta .., hroot => False.elim hroot
  | _, _, _, .peq .., hroot => False.elim hroot

theorem not_isRootEtaKStep_of_noEtaKStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {a b T : Expr Nat} → {h : ParRedT (PEqLeafT E n) E n Γ a b T} →
    NoEtaKStep h → ¬ IsRootEtaKStep h
  | _, _, _, .iotaStarKEta .., hno, _ => hno
  | _, _, _, .conv _ _ _ _ _ hinner _, hno, hroot =>
      not_isRootEtaKStep_of_noEtaKStep (h := hinner) hno hroot
  | _, _, _, .refl .., _, hroot => hroot
  | _, _, _, .sortEq .., _, hroot => hroot
  | _, _, _, .consts .., _, hroot => hroot
  | _, _, _, .bvarZeta .., _, hroot => hroot
  | _, _, _, .delta .., _, hroot => hroot
  | _, _, _, .app .., _, hroot => hroot
  | _, _, _, .beta .., _, hroot => hroot
  | _, _, _, .lam .., _, hroot => hroot
  | _, _, _, .pi .., _, hroot => hroot
  | _, _, _, .letE .., _, hroot => hroot
  | _, _, _, .zeta .., _, hroot => hroot
  | _, _, _, .iotaSpine .., _, hroot => hroot
  | _, _, _, .iotaStarK .., _, hroot => hroot
  | _, _, _, .lit .., _, hroot => hroot
  | _, _, _, .eta .., _, hroot => hroot
  | _, _, _, .peq .., _, hroot => hroot

/-- `Type`-valued decomposition of a `ParRedT` step on a recursor spine of
    length `≤ w.preMajor.length` under `¬ IsRootEtaKStep h` and
    `¬ HasRecProofRoot`. Allows arbitrary nested `ParRedT.iotaStarKEta` nodes
    inside spine arguments (via `parRedT_rec_spine_lt_decomp`). Covers all 18
    `ParRedT` constructors. -/
def parRedT_rec_spine_decomp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    ¬ IsRootEtaKStep h →
    ∀ {ls : List Level} {xs : List (Expr Nat)},
      a = foldApps (.const w.recRef ls) xs →
      xs.length ≤ w.preMajor.length →
      eqNList ls ls₀ →
      Σ' (ls' : List Level) (xs' : List (Expr Nat)),
        (b = foldApps (.const w.recRef ls') xs') ×'
        PLift (eqNList ls' ls₀) ×'
        RecArgsStep E n Γ xs xs'
  | _, _, _, .refl _ _ _ _, _, ls, xs, heq, _, hls =>
      ⟨ls, xs, heq, ⟨hls⟩, recArgsStep_refl xs⟩
  | _, _, _, .consts _ r ls1 ls2 _ hc _ _, _, ls, xs, heq, _, hls => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls1
          subst hr
          subst hls1
          exact ⟨ls2, [], rfl, ⟨eqNList_trans (eqNList_symm hc) hls⟩, .nil⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app _ f₀ f₀' x x' A_x _ _ _ _ hf₀ _ _ _ hx _, _, ls, xs, heq, hk, hls => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by intro hh; cases hh
          let ⟨ys, y, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const w.recRef ls) (z :: zs) =
              .app (foldApps (.const w.recRef ls) ys) y := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 hx0
          have hlen_ys : ys.length < w.preMajor.length := by
            have hl := congrArg List.length hsplit
            simp only [List.length_cons, List.length_append, List.length_singleton] at hl hk
            omega
          let ⟨ls', ys', hf₀'_eq, ⟨hls'⟩, hargs_ys⟩ :=
            parRedT_rec_spine_lt_decomp w hNoPrf hf₀ hf0 hlen_ys hls
          have hb_eq : Expr.app f₀' x' = foldApps (.const w.recRef ls') (ys' ++ [x']) := by
            rw [hf₀'_eq, foldApps_snoc]
          have hargs' : RecArgsStep E n Γ (z :: zs) (ys' ++ [x']) := by
            rw [hsplit]
            exact recArgsStep_snoc hargs_ys (.parRed A_x (hx0 ▸ hx))
          exact ⟨ls', ys' ++ [x'], hb_eq, ⟨hls'⟩, hargs'⟩
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, xs, heq, hk, hls => by
      have hnoRoot_step : ¬ IsRootEtaKStep hstep := fun hroot =>
        let ⟨_, _, hlam⟩ := isRootEtaKStep_target_is_lam hstep hroot
        derivedIotaU_lam_source_false hI hlam
      let ⟨ls', xs', hstep_eq, _, hargs⟩ :=
        parRedT_rec_spine_decomp w hNoPrf hstep hnoRoot_step heq hk hls
      have hlen' : xs'.length ≤ w.preMajor.length := by
        rw [recArgsStep_length hargs]
        exact hk
      exact False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      _, _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w hk wK major heq)
  | _, _, _, .iotaStarKEta .., hnoRoot, _, _, _, _, _ =>
      False.elim (hnoRoot True.intro)
  | _, _, _, .peq _ _ _ _ leaf, _, _, _, heq, hk, hls =>
      peqT_rec_spine_decomp hNoPrf leaf.1 heq hk hls
  | _, _, _, .conv _ _ _ _ _ hinner _, hnoRoot, _, _, heq, hk, hls =>
      parRedT_rec_spine_decomp w hNoPrf hinner hnoRoot heq hk hls
  | _, _, _, .sortEq .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

def list_getElem?_map_inv {α β : Type} (g : α → β) :
    (xs : List α) → (i : Nat) → {y : β} →
    (xs.map g)[i]? = some y →
    Σ' x : α, (xs[i]? = some x) ×' (y = g x)
  | [], _, _, h => nomatch h
  | x :: _, 0, _, h =>
      ⟨x, List.getElem?_cons_zero,
        (Option.some.inj (List.getElem?_cons_zero.symm.trans h)).symm⟩
  | _ :: xs, i + 1, _, h =>
      let r := list_getElem?_map_inv g xs i (List.getElem?_cons_succ.symm.trans h)
      ⟨r.1, List.getElem?_cons_succ.trans r.2.1, r.2.2⟩

theorem list_getElem?_map_of_some {α β : Type} (g : α → β) :
    (xs : List α) → (i : Nat) → {x : α} →
    xs[i]? = some x → (xs.map g)[i]? = some (g x)
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => by
      simp only [List.getElem?_cons_zero] at h
      injection h with hx
      subst hx
      exact List.getElem?_cons_zero
  | _ :: xs, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.map_cons, List.getElem?_cons_succ]
      exact list_getElem?_map_of_some g xs i h

/-- Extract the unlifted minor argument `m` in `(appsSpine f).2` such that
    `(appsSpine f).2[w.nparams + 1 + w.ctorIdx]? = some m` and
    `w.minor = lift 0 1 m`. -/
def minorPreImage {E : ResolvedEnv} (w : IotaWitness E) {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0)) :
    Σ' m : Expr Nat,
      ((appsSpine f).2[w.nparams + 1 + w.ctorIdx]? = some m) ×'
      (w.minor = lift 0 1 m) :=
  have hmap : ((appsSpine f).2.map (lift 0 1))[w.nparams + 1 + w.ctorIdx]? =
      some w.minor := by
    rw [(iotaStarKEta_head happ).2.1]
    exact w.hminor
  list_getElem?_map_inv (lift 0 1) (appsSpine f).2 (w.nparams + 1 + w.ctorIdx) hmap

theorem introTypeSpine_lift (c a : Nat) :
    (e : Expr Nat) → introTypeSpine (lift c a e) = introTypeSpine e
  | .bvar _ => by simp only [lift]; split <;> rfl
  | .sort _ | .const _ _ | .pi _ _ | .app _ _ | .lit _ => rfl
  | .lam _ body => introTypeSpine_lift (c + 1) a body
  | .letE _ _ body => introTypeSpine_lift (c + 1) a body

/-- Lifting a single-argument step `RecArgStep E n Γ m m'` on the selected
    minor `m` (where `w.minor = lift 0 1 m` has type `B` in `.assumption A :: Γ`)
    to a `ParRedT` step at `B`.
    - Automatically inhabited for `RecArgStep.refl` (any `m`).
    - Automatically inhabited for `RecArgStep.parRed` whenever
      `introTypeSpine m = true` (`bvar`/`sort`/`const`/`lam`/`letE`), via
      `parRedT_lift` + `introTypeSpine_unique`.
    - Automatically inhabited for `m = .bvar i` across all three constructors
      (`refl`, `parRed`, `peq`) whenever `.bvar i` is not let-bound and not a
      `Prop` proof root (`minorStepLift_of_bvar`). -/
def MinorStepLift (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A B m : Expr Nat) : Type :=
  ∀ {m' : Expr Nat}, RecArgStep E n Γ m m' →
    ParRedT (PEqLeafT E n) E n (.assumption A :: Γ) (lift 0 1 m) (lift 0 1 m') B

/-- Automatic discharge of `MinorStepLift` whenever `introTypeSpine m = true`
    (`bvar`, `sort`, `const`, `lam`, `letE` spine) and raw `PEqT` on `m` is
    reflexive. -/
def minorStepLift_of_introSpine {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} {A B m : Expr Nat} {u : Level}
    (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hrhs : HasTyT E n (.assumption A :: Γ) (lift 0 1 m) B)
    (hintro : introTypeSpine m = true)
    (hpeq_id : ∀ {m' : Expr Nat}, PEqT E n Γ m m' → m' = m) :
    MinorStepLift E n Γ A B m
  | _, .refl _ => .refl (.assumption A :: Γ) (lift 0 1 m) B hrhs
  | m', .parRed A_m hm =>
      let hcl := envClosed_of_envWfT hW
      let hinst := envMembersSubstStable_of_envWfT hW
      let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      let hm_lift : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ)
          (lift 0 1 m) (lift 0 1 m') (lift 0 1 A_m) :=
        parRedT_lift (.assumption A) hcl (peqLeafTWeaken hcl) (c := 0) hm
      let hm_ty : HasTyT E n (.assumption A :: Γ) (lift 0 1 m) (lift 0 1 A_m) :=
        parRedT_hasTy_left (fun h => ⟨h.2.1, h.2.2⟩) hΓA hm_lift
      have hintro_lift : introTypeSpine (lift 0 1 m) = true := by
        rw [introTypeSpine_lift]
        exact hintro
      let hc_m : TyConvT E n (.assumption A :: Γ) (lift 0 1 A_m) B :=
        introTypeSpine_unique hcl hinst hintro_lift hm_ty hrhs
      .conv (.assumption A :: Γ) (lift 0 1 m) (lift 0 1 m') (lift 0 1 A_m) B
        hm_lift hc_m
  | m', .peq hm_peq => by
      have heq : m' = m := hpeq_id hm_peq
      rw [heq]
      exact .refl (.assumption A :: Γ) (lift 0 1 m) B hrhs

/-- Automatic discharge of `MinorStepLift` across all three `RecArgStep`
    constructors (`refl`, `parRed`, `peq`) when `m = .bvar i` is a non-let
    variable that cannot be typed at a `Prop`. -/
def minorStepLift_of_bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} {i : Nat}
    (hrhs : HasTyT E n (.assumption A :: Γ) (lift 0 1 (.bvar i)) B)
    (hz : ∀ C v, Γ.get? i ≠ some (.letBinding C v))
    (hNoPrf : ∀ P : Expr Nat,
      HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ (.bvar i) P → False) :
    MinorStepLift E n Γ A B (.bvar i)
  | _, .refl _ => .refl (.assumption A :: Γ) (lift 0 1 (.bvar i)) B hrhs
  | m', .parRed _ hm => by
      have hstep : m' = .bvar i := by
        rcases parRedT_bvar_step hz hm rfl with heq | ⟨P, ⟨hP⟩, ⟨hp⟩⟩
        · exact heq
        · exact False.elim (hNoPrf P hP hp)
      subst hstep
      exact .refl (.assumption A :: Γ) (lift 0 1 (.bvar i)) B hrhs
  | m', .peq hm_peq => by
      have hstep : m' = .bvar i := by
        rcases peqT_bvar_step hm_peq rfl with heq | ⟨P, ⟨hP⟩, ⟨hp⟩⟩
        · exact heq
        · exact False.elim (hNoPrf P hP hp)
      subst hstep
      exact .refl (.assumption A :: Γ) (lift 0 1 (.bvar i)) B hrhs

/-- At the positive A-2 peak (`eqEnvT`, `positiveContext`, minor `m = .bvar 0`),
    `MinorStepLift` holds unconditionally under sort uniqueness. -/
def minorStepLift_positive_a2
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    {A B : Expr Nat}
    (hrhs : HasTyT eqEnvT 2 (.assumption A :: positiveContext) (.bvar 1) B) :
    MinorStepLift eqEnvT 2 positiveContext A B (.bvar 0) :=
  minorStepLift_of_bvar hrhs
    (by intro _ _ h; cases h)
    (fun P hP hp => by
      have hΓ := contextWf one positive_levels
      have hΓA : CtxWfT eqEnvT 2 (.assumption (.sort .zero) :: positiveContext) :=
        .assumption positiveContext (.sort .zero) (.succ .zero) hΓ (.sort _ .zero)
      have hcl := envClosed_of_envWfT envWf
      have hP_lift : HasTyT eqEnvT 2 (.assumption (.sort .zero) :: positiveContext)
          (lift 0 1 P) (.sort .zero) :=
        hasTyTWeaken (.assumption (.sort .zero)) hcl (c := 0) hP
      have hp_lift : HasTyT eqEnvT 2 (.assumption (.sort .zero) :: positiveContext)
          (.bvar 1) (lift 0 1 P) :=
        hasTyTWeaken (.assumption (.sort .zero)) hcl (c := 0) hp
      have heq : eqN one .zero :=
        bvar1_type_sort_eqN_of_sortUniq hSortUniq positive_levels hΓA hp_lift hP_lift
      have h10 := heq (fun _ => some 0)
      cases h10)

/-- Wrapper provenance for a root `ParRedT.iotaStarKEta` step at target type `T`:
    either the step is unwrapped (`T = .pi A_eta B_eta`, so no `.conv` wrapper
    is synthesized), or it was wrapped in one or more real `ParRedT.conv` steps
    carrying `hc : TyConvT E n Γ (.pi A_eta B_eta) T`. -/
inductive EtaKWrapper (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A_eta B_eta T : Expr Nat) : Type where
  | unwrapped (heq : T = .pi A_eta B_eta) : EtaKWrapper E n Γ A_eta B_eta T
  | wrapped (hc : TyConvT E n Γ (.pi A_eta B_eta) T) :
      EtaKWrapper E n Γ A_eta B_eta T

def EtaKWrapper.extend {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A_eta B_eta T₁ T₂ : Expr Nat}
    (w : EtaKWrapper E n Γ A_eta B_eta T₁)
    (hc : TyConvT E n Γ T₁ T₂) :
    EtaKWrapper E n Γ A_eta B_eta T₂ :=
  match w with
  | .unwrapped heq => .wrapped (heq ▸ hc)
  | .wrapped hc₀ => .wrapped (.trans Γ (.pi A_eta B_eta) T₁ T₂ hc₀ hc)

/-- Exhaustive two-branch classification of ANY `ParRedT` step out of a
    recursor pre-major spine `a = foldApps (.const w.recRef ls) xs` of length
    `xs.length = w.preMajor.length` (without `NoEtaKStep`):
    - `spine`: `b = foldApps (.const w.recRef ls') xs'` with `eqNList ls' ls₀`
      and `RecArgsStep E n Γ xs xs'` (handling `.refl`, `.consts`, `.app`
      including nested `ParRedT.iotaStarKEta` steps in arguments, `.peq`, and
      `.conv` around `spine`), or
    - `etaK`: `h` fired `ParRedT.iotaStarKEta` at the root of `a` (possibly
      under `.conv` wrappers tracked by `EtaKWrapper`), yielding
      `b = .lam A_eta rhs_eta`. -/
inductive RecPreMajorStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (w : IotaWitness E) (ls₀ : List Level) (xs : List (Expr Nat))
    (a b T : Expr Nat) : Type where
  | spine (ls' : List Level) (xs' : List (Expr Nat))
      (hb : b = foldApps (.const w.recRef ls') xs')
      (hls' : eqNList ls' ls₀)
      (hargs : RecArgsStep E n Γ xs xs') :
      RecPreMajorStep E n Γ w ls₀ xs a b T
  | etaK (w_eta : IotaWitness E) (A_eta B_eta Tm_eta rhs_eta : Expr Nat)
      (u_eta rl_eta : Level) (afs_eta : Prop)
      (hb : b = .lam A_eta rhs_eta)
      (happ_eta : recCall (.const w_eta.recRef w_eta.ls) w_eta.preMajor (.bvar 0) =
        .app (lift 0 1 a) (.bvar 0))
      (hA_eta : HasTyT E n Γ A_eta (.sort u_eta))
      (hf_eta : HasTyT E n Γ a (.pi A_eta B_eta))
      (hrl_eta : piBody w_eta.famMember.mtype = .sort rl_eta)
      (hsel_eta : EliminationSelection rl_eta w_eta.nMinors afs_eta .anySort)
      (hfam_eta : ∃ lsF, (appsSpine Tm_eta).1 = .const w_eta.familyRef lsF)
      (hmajor_eta : HasTyT E n (.assumption A_eta :: Γ) (.bvar 0) Tm_eta)
      (hmk_eta : HasTyT E n (.assumption A_eta :: Γ) (ctorMajor w_eta) Tm_eta)
      (hTm0_eta : HasTyT E n (.assumption A_eta :: Γ) Tm_eta (.sort .zero))
      (hι_eta : DerivedIotaU E (iotaLhsOf w_eta) rhs_eta)
      (hlι_eta : HasTyT E n (.assumption A_eta :: Γ) (iotaLhsOf w_eta) B_eta)
      (hlhs_eta : HasTyT E n (.assumption A_eta :: Γ)
        (recCall (.const w_eta.recRef w_eta.ls) w_eta.preMajor (.bvar 0)) B_eta)
      (hrhs_eta : HasTyT E n (.assumption A_eta :: Γ) rhs_eta B_eta)
      (hwrap : EtaKWrapper E n Γ A_eta B_eta T) :
      RecPreMajorStep E n Γ w ls₀ xs a b T

/-- Full 18-constructor classifier for ANY `ParRedT` step on a recursor
    pre-major spine `a = foldApps (.const w.recRef ls) xs` of length
    `xs.length = w.preMajor.length` under `¬ HasRecProofRoot` (and WITHOUT
    `NoEtaKStep`). -/
def parRedT_rec_preMajor_classify {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length) :
    {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T →
    ∀ {ls : List Level} {xs : List (Expr Nat)},
      a = foldApps (.const w.recRef ls) xs →
      xs.length = w.preMajor.length →
      eqNList ls ls₀ →
      RecPreMajorStep E n Γ w ls₀ xs a b T
  | _, _, _, .refl _ _ _ _, ls, xs, heq, _, hls =>
      .spine ls xs heq hls (recArgsStep_refl xs)
  | _, _, _, .consts _ _ _ ls2 _ hc _ _, _, [], heq, _, hls =>
      have hr := (Expr.const.inj heq).1
      have hls1 := (Expr.const.inj heq).2
      .spine ls2 [] (congrArg (fun r => Expr.const r ls2) hr)
        (eqNList_trans (eqNList_symm hc) (hls1 ▸ hls)) .nil
  | _, _, _, .consts .., ls, x :: xs, heq, _, _ =>
      let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
      False.elim (by rw [happ] at heq; exact nomatch heq)
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app .., _, [], heq, _, _ =>
      nomatch heq
  | _, _, _, .app _ f₀ f₀' x x' A_x _ _ _ _ hf₀ _ _ _ hx _, ls, z :: zs, heq, hk, hls =>
      have hne : z :: zs ≠ ([] : List (Expr Nat)) := by intro hh; cases hh
      let ⟨ys, y, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
      have happ : foldApps (.const w.recRef ls) (z :: zs) =
          .app (foldApps (.const w.recRef ls) ys) y := by
        rw [hsplit, foldApps_snoc]
      have heq' : Expr.app f₀ x = .app (foldApps (.const w.recRef ls) ys) y := by
        rw [← happ, heq]
      have hf0 : f₀ = foldApps (.const w.recRef ls) ys := (Expr.app.inj heq').1
      have hx0 : x = y := (Expr.app.inj heq').2
      have hlen_ys : ys.length < w.preMajor.length := by
        have hl := congrArg List.length hsplit
        simp only [List.length_cons, List.length_append, List.length_singleton] at hl hk
        omega
      let ⟨ls', ys', hf₀'_eq, ⟨hls'⟩, hargs_ys⟩ :=
        parRedT_rec_spine_lt_decomp w hNoPrf hf₀ hf0 hlen_ys hls
      have hb_eq : Expr.app f₀' x' = foldApps (.const w.recRef ls') (ys' ++ [x']) := by
        rw [hf₀'_eq, foldApps_snoc]
      have hargs' : RecArgsStep E n Γ (z :: zs) (ys' ++ [x']) := by
        rw [hsplit]
        exact recArgsStep_snoc hargs_ys (.parRed A_x (hx0 ▸ hx))
      .spine ls' (ys' ++ [x']) hb_eq hls' hargs'
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, xs, heq, hk, hls =>
      match parRedT_rec_preMajor_classify w hNoPrf hstep heq hk hls with
      | .spine _ xs' hstep_eq _ hargs =>
          have hlen' : xs'.length ≤ w.preMajor.length := by
            rw [recArgsStep_length hargs, hk]
            exact Nat.le_refl _
          False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
      | .etaK _ A_eta _ _ rhs_eta _ _ _ hstep_eq .. =>
          False.elim (derivedIotaU_lam_source_false hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w (Nat.le_of_eq hk) wK major heq)
  | _, _, _, .iotaStarKEta _ w_eta f_eta A_eta B_eta Tm_eta rhs_eta u_eta rl_eta afs_eta
      happ_eta hA_eta hf_eta hrl_eta hsel_eta hfam_eta hmajor_eta hmk_eta hTm0_eta
      hι_eta hlι_eta hlhs_eta hrhs_eta, _, _, _, _, _ =>
      .etaK w_eta A_eta B_eta Tm_eta rhs_eta u_eta rl_eta afs_eta rfl
        happ_eta hA_eta hf_eta hrl_eta hsel_eta hfam_eta hmajor_eta hmk_eta hTm0_eta
        hι_eta hlι_eta hlhs_eta hrhs_eta (.unwrapped rfl)
  | _, _, _, .peq _ _ _ _ leaf, _, _, heq, hk, hls =>
      let ⟨ls', xs', hb, ⟨hls'⟩, hargs⟩ :=
        peqT_rec_spine_decomp hNoPrf leaf.1 heq (Nat.le_of_eq hk) hls
      .spine ls' xs' hb hls' hargs
  | _, _, _, .conv _ _ _ _ _ hinner hc_wrap, _, _, heq, hk, hls =>
      match parRedT_rec_preMajor_classify w hNoPrf hinner heq hk hls with
      | .spine ls' xs' hb hls' hargs =>
          .spine ls' xs' hb hls' hargs
      | .etaK w_eta A_eta B_eta Tm_eta rhs_eta u_eta rl_eta afs_eta hb
          happ_eta hA_eta hf_eta hrl_eta hsel_eta hfam_eta hmajor_eta hmk_eta hTm0_eta
          hι_eta hlι_eta hlhs_eta hrhs_eta hwrap =>
          .etaK w_eta A_eta B_eta Tm_eta rhs_eta u_eta rl_eta afs_eta hb
            happ_eta hA_eta hf_eta hrl_eta hsel_eta hfam_eta hmajor_eta hmk_eta hTm0_eta
            hι_eta hlι_eta hlhs_eta hrhs_eta (hwrap.extend hc_wrap)
  | _, _, _, .sortEq .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- `hf_step` does not wrap a root `ParRedT.iotaStarKEta` step inside
    `ParRedT.conv`. Holds definitionally (`True` or `¬ False`) for:
    - an unwrapped root `ParRedT.iotaStarKEta` step (e.g. `partialRec_to_contracted`),
    - every structural step (`.refl`, `.consts`, `.app`, `.peq`), even wrapped
      in `.conv` and even containing nested `ParRedT.iotaStarKEta` steps inside
      arguments. -/
def NoWrappedRootEtaK {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} : ParRedT (PEqLeafT E n) E n Γ a b T → Prop
  | .conv _ _ _ _ _ hinner _ => ¬ IsRootEtaKStep hinner
  | _ => True

theorem noWrappedRootEtaK_of_not_isRootEtaKStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hnoRoot : ¬ IsRootEtaKStep h) : NoWrappedRootEtaK h := by
  cases h with
  | conv _ _ _ _ _ _ _ => exact hnoRoot
  | _ => exact True.intro

theorem noWrappedRootEtaK_of_noEtaKStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hno : NoEtaKStep h) : NoWrappedRootEtaK h :=
  noWrappedRootEtaK_of_not_isRootEtaKStep (not_isRootEtaKStep_of_noEtaKStep hno)

theorem classify_not_etaK_of_not_isRootEtaKStep
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    ¬ IsRootEtaKStep h →
    ∀ {ls : List Level} {xs : List (Expr Nat)}
      (heq : a = foldApps (.const w.recRef ls) xs)
      (hk : xs.length = w.preMajor.length)
      (hls : eqNList ls ls₀),
      match parRedT_rec_preMajor_classify w hNoPrf h heq hk hls with
      | .spine .. => True
      | .etaK .. => False
  | _, _, _, .refl .., _, _, _, _, _, _ => True.intro
  | _, _, _, .consts .., _, _, [], _, _, _ => True.intro
  | _, _, _, .consts .., _, ls, x :: xs, heq, _, _ =>
      let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
      False.elim (by rw [happ] at heq; exact nomatch heq)
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app .., _, _, [], heq, _, _ => nomatch heq
  | _, _, _, .app .., _, _, _ :: _, _, _, _ => True.intro
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, xs, heq, hk, hls => by
      cases parRedT_rec_preMajor_classify w hNoPrf hstep heq hk hls with
      | spine _ xs' hstep_eq _ hargs =>
          have hlen' : xs'.length ≤ w.preMajor.length := by
            rw [recArgsStep_length hargs, hk]
            exact Nat.le_refl _
          exact False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
      | etaK _ A_eta _ _ rhs_eta _ _ _ hstep_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact False.elim (derivedIotaU_lam_source_false hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w (Nat.le_of_eq hk) wK major heq)
  | _, _, _, .iotaStarKEta .., hnoRoot, _, _, _, _, _ =>
      False.elim (hnoRoot True.intro)
  | _, _, _, .peq .., _, _, _, _, _, _ => True.intro
  | _, _, _, .conv _ _ _ _ _ hinner _, hnoRoot, _, _, heq, hk, hls => by
      have ih := classify_not_etaK_of_not_isRootEtaKStep w hNoPrf hinner hnoRoot heq hk hls
      cases hcl : parRedT_rec_preMajor_classify w hNoPrf hinner heq hk hls with
      | spine _ _ _ _ _ =>
          simp only [parRedT_rec_preMajor_classify, hcl]
      | etaK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          rw [hcl] at ih
          exact False.elim ih
  | _, _, _, .sortEq .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

theorem classify_not_etaK_of_noEtaKStep
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length)
    {a b T : Expr Nat} (h : ParRedT (PEqLeafT E n) E n Γ a b T)
    (hno : NoEtaKStep h)
    {ls : List Level} {xs : List (Expr Nat)}
    (heq : a = foldApps (.const w.recRef ls) xs)
    (hk : xs.length = w.preMajor.length)
    (hls : eqNList ls ls₀) :
    match parRedT_rec_preMajor_classify w hNoPrf h heq hk hls with
    | .spine .. => True
    | .etaK .. => False :=
  classify_not_etaK_of_not_isRootEtaKStep w hNoPrf h
    (not_isRootEtaKStep_of_noEtaKStep hno) heq hk hls

theorem not_wrapped_of_noWrappedRootEtaK
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    NoWrappedRootEtaK h →
    ∀ {ls : List Level} {xs : List (Expr Nat)}
      (heq : a = foldApps (.const w.recRef ls) xs)
      (hk : xs.length = w.preMajor.length)
      (hls : eqNList ls ls₀),
      match parRedT_rec_preMajor_classify w hNoPrf h heq hk hls with
      | .spine .. => True
      | .etaK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwrap =>
          match hwrap with
          | .unwrapped _ => True
          | .wrapped _ => False
  | _, _, _, .refl .., _, _, _, _, _, _ => True.intro
  | _, _, _, .consts .., _, _, [], _, _, _ => True.intro
  | _, _, _, .consts .., _, ls, x :: xs, heq, _, _ =>
      let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
      False.elim (by rw [happ] at heq; exact nomatch heq)
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app .., _, _, [], heq, _, _ => nomatch heq
  | _, _, _, .app .., _, _, _ :: _, _, _, _ => True.intro
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, xs, heq, hk, hls => by
      cases parRedT_rec_preMajor_classify w hNoPrf hstep heq hk hls with
      | spine _ xs' hstep_eq _ hargs =>
          have hlen' : xs'.length ≤ w.preMajor.length := by
            rw [recArgsStep_length hargs, hk]
            exact Nat.le_refl _
          exact False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
      | etaK _ A_eta _ _ rhs_eta _ _ _ hstep_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact False.elim (derivedIotaU_lam_source_false hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w (Nat.le_of_eq hk) wK major heq)
  | _, _, _, .iotaStarKEta .., _, _, _, _, _, _ => True.intro
  | _, _, _, .peq .., _, _, _, _, _, _ => True.intro
  | _, _, _, .conv _ _ _ _ _ hinner _, hnoWrap, _, _, heq, hk, hls => by
      have hnot := classify_not_etaK_of_not_isRootEtaKStep w hNoPrf hinner hnoWrap heq hk hls
      cases hcl : parRedT_rec_preMajor_classify w hNoPrf hinner heq hk hls with
      | spine _ _ _ _ _ =>
          simp only [parRedT_rec_preMajor_classify, hcl]
      | etaK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          rw [hcl] at hnot
          exact False.elim hnot
  | _, _, _, .sortEq .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- Two `iotaStarKEta` witnesses at the same η-contracted source `f` have
    identical `recRef`, `ls`, and `preMajor`. -/
theorem iotaStarKEta_same_rec_preMajor {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0)) :
    w₁.recRef = w₂.recRef ∧ w₁.ls = w₂.ls ∧ w₁.preMajor = w₂.preMajor := by
  have hl : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) :=
    happ₁.trans happ₂.symm
  have hs := congrArg appsSpine hl
  rw [appsSpine_recCall, appsSpine_recCall] at hs
  injection hs with hh hargs
  injection hh with hrec hls
  obtain ⟨hpm, _⟩ := list_snoc_inj hargs
  exact ⟨hrec, hls, hpm⟩

theorem iotaArgs_nil_fields {E : ResolvedEnv} {fuel : Nat}
    {rec : Expr Nat} {preMajor : List (Expr Nat)} {nparams nMinors : Nat}
    {shapes : List FieldShape} {tel : Expr Nat} {args : List (Expr Nat)}
    (h : iotaArgs E fuel rec preMajor nparams nMinors shapes [] tel = some args) :
    args = [] := by
  cases shapes with
  | nil =>
      simp only [iotaArgs] at h
      exact (Option.some.inj h).symm
  | cons s ss =>
      cases s with
      | nonrecursive =>
          cases tel <;> cases h
      | recursive inner =>
          cases inner with
          | zero => cases tel <;> cases h
          | succ k => cases tel <;> cases h

theorem iotaOpenRhs_nil_fields {E : ResolvedEnv} {fuel : Nat}
    {rec minor : Expr Nat} {preMajor : List (Expr Nat)} {nparams nMinors : Nat}
    {shapes : List FieldShape} {tel schema : Expr Nat}
    (h : iotaOpenRhs E fuel rec minor preMajor nparams nMinors shapes [] tel = some schema) :
    schema = minor := by
  unfold iotaOpenRhs at h
  cases hargs : iotaArgs E fuel rec preMajor nparams nMinors shapes [] tel with
  | none =>
      rw [hargs] at h
      cases h
  | some args =>
      rw [hargs] at h
      have ha : args = [] := iotaArgs_nil_fields hargs
      subst ha
      exact (Option.some.inj h).symm

theorem iotaRhsOfS_fields_nil {E : ResolvedEnv} (wS : IotaWitnessS E)
    {m : Expr Nat} (hf_nil : wS.fields = [])
    (hmin : wS.preMajor[wS.nparams + 1 + wS.ctorIdx]? = some m) :
    iotaRhsOfS wS = m := by
  have hfb : fieldBvars wS.fields.length = [] := by
    rw [hf_nil]
    rfl
  have hsch0 := wS.hschema
  rw [hfb] at hsch0
  have hsch : wS.schema =
      .bvar (wS.fields.length + wS.nindices + (wS.nMinors - 1 - wS.ctorIdx)) :=
    iotaOpenRhs_nil_fields hsch0
  unfold iotaRhsOfS
  rw [hf_nil, List.append_nil, hsch, instantiateLevels]
  apply instPrefix_bvar_lt
  · have hp := wS.hpre
    have hi := wS.hidx
    have hfl : wS.fields.length = 0 := congrArg List.length hf_nil
    omega
  · have hp := wS.hpre
    have hi := wS.hidx
    have hfl : wS.fields.length = 0 := congrArg List.length hf_nil
    have hidx_eq :
        wS.preMajor.length - 1 -
          (wS.fields.length + wS.nindices + (wS.nMinors - 1 - wS.ctorIdx)) =
        wS.nparams + 1 + wS.ctorIdx := by omega
    rw [hidx_eq]
    exact hmin

theorem witness_witnessS_align {E : ResolvedEnv}
    (w : IotaWitness E) (wS : IotaWitnessS E)
    (heq : iotaLhsOf w = iotaLhsOfS wS) :
    w.preMajor = wS.preMajor ∧
    w.nparams = wS.nparams ∧
    w.ctorIdx = wS.ctorIdx ∧
    w.fields.length = wS.fields.length := by
  have hs := congrArg appsSpine heq
  change appsSpine (recCall (.const w.recRef w.ls) w.preMajor (ctorMajor w)) =
    appsSpine (recCall (.const wS.recRef wS.ls) wS.preMajor
      (foldApps (.const wS.ctorRef wS.lsC) (wS.ctorParams ++ wS.fields))) at hs
  rw [appsSpine_recCall, appsSpine_recCall] at hs
  injection hs with hhead hargs
  injection hhead with hrec _
  obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
  have hsc := congrArg appsSpine hmaj
  change appsSpine (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) =
    appsSpine (foldApps (.const wS.ctorRef wS.lsC) (wS.ctorParams ++ wS.fields)) at hsc
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hsc
  have hchead : Expr.const w.ctorRef w.lsC = Expr.const wS.ctorRef wS.lsC :=
    congrArg Prod.fst hsc
  have hctor : w.ctorRef = wS.ctorRef := by injection hchead
  have hmemr : w.recMember = wS.recMember := by
    have a := w.hrec
    have b := wS.hrec
    rw [← hrec] at b
    exact Option.some.inj (a.symm.trans b)
  have hmemc : w.ctorMember = wS.ctorMember := by
    have a := w.hctor
    have b := wS.hctor
    rw [← hctor] at b
    exact Option.some.inj (a.symm.trans b)
  have hlen : w.preMajor.length = wS.preMajor.length := congrArg List.length hpm
  have hL : w.nparams + 1 + w.nMinors + w.nindices + 1 =
      wS.nparams + 1 + wS.nMinors + wS.nindices + 1 := by
    have a := w.hpre
    have b := wS.hpre
    omega
  have hd : w.recDoms = wS.recDoms ∧ w.recBody = wS.recBody := by
    have a := w.hpeelRec
    have b := wS.hpeelRec
    rw [hL, hmemr] at a
    exact Prod.mk.inj (Option.some.inj (a.symm.trans b))
  have hi : w.nparams + 1 + w.nMinors + w.nindices =
      wS.nparams + 1 + wS.nMinors + wS.nindices := by
    have a := w.hpre
    have b := wS.hpre
    omega
  have m1 := w.hmajorTy
  have m2 := wS.hmajorTy
  rw [hd.1, hi] at m1
  have happ := Option.some.inj (m1.symm.trans m2)
  have hsf := congrArg appsSpine happ
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hsf
  have hfh : Expr.const w.familyRef ((List.range w.famMember.arity).map Level.param) =
      Expr.const wS.familyRef ((List.range wS.famMember.arity).map Level.param) :=
    congrArg Prod.fst hsf
  have hfam : w.familyRef = wS.familyRef := by injection hfh
  have hnmin : w.nMinors = wS.nMinors := by
    have a := w.hrecIdx
    have b := wS.hrecIdx
    rw [← hrec, ← hfam] at b
    omega
  have hidx : w.ctorIdx = wS.ctorIdx := by
    have a := w.hctorIdx
    have b := wS.hctorIdx
    rw [← hctor, ← hfam] at b
    omega
  have hnidx : w.nindices = wS.nindices := by
    have eq := w.hrecBody.symm.trans (hd.2.trans wS.hrecBody)
    have s1 := appsSpine_foldApps
      (.bvar (w.nMinors + w.nindices + 1) : Expr Nat)
      ((List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
        [Expr.bvar 0])
    have s2 := appsSpine_foldApps
      (.bvar (wS.nMinors + wS.nindices + 1) : Expr Nat)
      ((List.range wS.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
        [Expr.bvar 0])
    simp only [appsSpine, List.nil_append] at s1 s2
    have hs_b := congrArg appsSpine eq
    rw [s1, s2] at hs_b
    have hb : (Expr.bvar (w.nMinors + w.nindices + 1) : Expr Nat) =
        Expr.bvar (wS.nMinors + wS.nindices + 1) := congrArg Prod.fst hs_b
    injection hb with hbi
    omega
  have hnpar : w.nparams = wS.nparams := by
    have a := w.hpre
    have b := wS.hpre
    omega
  have hflen : w.fields.length = wS.fields.length := by
    have a := w.hnpar
    have b := wS.hnpar
    rw [← hmemc] at b
    omega
  exact ⟨hpm, hnpar, hidx, hflen⟩

theorem derivedIotaU_rhs_eq_of_fields_nil_aux {E : ResolvedEnv}
    (w : IotaWitness E) {lhs rhs : Expr Nat}
    (hf_nil : w.fields = [])
    (hι : DerivedIotaU E lhs rhs)
    (heq : iotaLhsOf w = lhs) :
    rhs = w.minor := by
  cases hι with
  | ofU wI =>
      have d : DerivedIota E (iotaLhsOf w) (iotaRhsOf wI) :=
        heq ▸ DerivedIota.of wI
      exact (iotaDet d (.of w)).trans (headStepT_iotaRhs_fields_nil w hf_nil)
  | ofUS wS =>
      obtain ⟨hpm, hnpar, hidx, hflen⟩ := witness_witnessS_align w wS heq
      have hfS_len : wS.fields.length = 0 := by
        rw [← hflen, hf_nil]
        rfl
      have hfS_nil : wS.fields = [] := List.eq_nil_of_length_eq_zero hfS_len
      have hminS : wS.preMajor[wS.nparams + 1 + wS.ctorIdx]? = some w.minor := by
        rw [← hpm, ← hnpar, ← hidx]
        exact w.hminor
      exact iotaRhsOfS_fields_nil wS hfS_nil hminS

/-- Full `DerivedIotaU` coherence (covering BOTH `.ofU` and `.ofUS` arms):
    for any `w : IotaWitness E` with `w.fields = []` and any union derivation
    `hι : DerivedIotaU E (iotaLhsOf w) rhs`, `rhs = w.minor`. -/
theorem derivedIotaU_rhs_eq_of_fields_nil {E : ResolvedEnv}
    (w : IotaWitness E) {rhs : Expr Nat}
    (hf_nil : w.fields = [])
    (hι : DerivedIotaU E (iotaLhsOf w) rhs) :
    rhs = w.minor :=
  derivedIotaU_rhs_eq_of_fields_nil_aux w hf_nil hι rfl

theorem derivedIotaU_rhs_eq_iotaRhsOf_of_fields_nil {E : ResolvedEnv}
    (w : IotaWitness E) {rhs : Expr Nat}
    (hf_nil : w.fields = [])
    (hι : DerivedIotaU E (iotaLhsOf w) rhs) :
    rhs = iotaRhsOf w :=
  (derivedIotaU_rhs_eq_of_fields_nil w hf_nil hι).trans
    (headStepT_iotaRhs_fields_nil w hf_nil).symm

/-- Full `DerivedIotaU`-coherent self-overlap on the actual constructor
    right-hand sides `rhs₁, rhs₂` (`hι₁ : DerivedIotaU E (iotaLhsOf w₁) rhs₁`,
    `hι₂ : DerivedIotaU E (iotaLhsOf w₂) rhs₂`, covering BOTH `.ofU` and `.ofUS`)
    when `w₂.nMinors = 1` and `w₂.fields = []` (`w₁.nMinors = 1` and
    `w₁.fields = []` are derived automatically from `w₂`): `rhs₁ = rhs₂`. -/
theorem iotaStarKEta_self_derivedIotaU_rhs_eq_of_fields_nil {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f rhs₁ rhs₂ : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn2 : w₂.nMinors = 1)
    (hf2 : w₂.fields = [])
    (hι₁ : DerivedIotaU E (iotaLhsOf w₁) rhs₁)
    (hι₂ : DerivedIotaU E (iotaLhsOf w₂) rhs₂) :
    rhs₁ = rhs₂ := by
  obtain ⟨hrec, _, hpm⟩ := iotaStarKEta_same_rec_preMajor happ₁ happ₂
  have hn1 : w₁.nMinors = 1 :=
    (headStepT_iotaWitness_nMinors_eq hrec hpm).trans hn2
  have hf1 : w₁.fields = [] :=
    headStepT_iotaStarK_fields_nil hrec hpm hn2 hf2
  have hm : w₁.minor = w₂.minor :=
    headStepT_iotaStarK_minor_eq hrec hpm hn1 hn2
  rw [derivedIotaU_rhs_eq_of_fields_nil w₁ hf1 hι₁,
    derivedIotaU_rhs_eq_of_fields_nil w₂ hf2 hι₂, hm]

/-- Step-specific binder-domain alignment for a parallel step
    `h : ParRedT (PEqLeafT E n) E n Γ a b T` against outer binder domain `A`:
    - for any structural step (`refl`, `consts`, `app` including nested
      `iotaStarKEta`, `peq`, or `.conv` wrapping a structural step), it is `PUnit`;
    - for any root `ParRedT.iotaStarKEta` step (unwrapped OR wrapped in any
      number of `ParRedT.conv` steps) whose inner binder domain `A_eta` equals
      `A`, it is `PUnit` (so `TyConvT.refl` and all domain-preserving `.conv`
      wrappers require no external conversion callback);
    - for a `.conv`-wrapped root `ParRedT.iotaStarKEta` step whose inner binder
      domain `A_eta` (typed at `u_eta`) differs from `A`, it is
      `CtxWfT E n Γ ×' ConvT E n Γ A_eta A (.sort u_eta)`. -/
def RootEtaKDomainConv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} (A : Expr Nat) {T : Expr Nat} :
    ParRedT (PEqLeafT E n) E n Γ a b T → Type
  | .iotaStarKEta _ _ _ A_eta _ _ _ u_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      if A_eta = A then PUnit
      else CtxWfT E n Γ ×' ConvT E n Γ A_eta A (.sort u_eta)
  | .conv _ _ _ _ _ hinner _ =>
      RootEtaKDomainConv A hinner
  | _ => PUnit

/-- Predicate stating that if `h` is a (possibly `.conv`-wrapped) root
    `ParRedT.iotaStarKEta` step, its inner binder domain `A_eta` equals `A`.
    Holds definitionally (`True` or `rfl`) for all structural steps, all
    unwrapped root `iotaStarKEta` steps, and all domain-preserving `.conv`
    wrappers around root `iotaStarKEta` steps (including `TyConvT.refl`). -/
def SameRootEtaKDomain {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} (A : Expr Nat) {T : Expr Nat} :
    ParRedT (PEqLeafT E n) E n Γ a b T → Prop
  | .iotaStarKEta _ _ _ A_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      A_eta = A
  | .conv _ _ _ _ _ hinner _ =>
      SameRootEtaKDomain A hinner
  | _ => True

/-- Unconditional constructor for `RootEtaKDomainConv A h` whenever
    `SameRootEtaKDomain A h` holds (discharged automatically by `rfl` / `trivial`
    for all structural steps, unwrapped root `iotaStarKEta` steps, and
    reflexive/domain-preserving `.conv` wrappers). -/
def rootEtaKDomainConv_of_same {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} {A T : Expr Nat} :
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (hsame : SameRootEtaKDomain A h := by first | rfl | trivial) →
    RootEtaKDomainConv A h
  | .iotaStarKEta _ _ _ A_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, hsame => by
      change A_eta = A at hsame
      dsimp [RootEtaKDomainConv]
      rw [if_pos hsame]
      exact PUnit.unit
  | .conv _ _ _ _ _ hinner _, hsame =>
      rootEtaKDomainConv_of_same hinner hsame
  | .refl .., _ | .sortEq .., _ | .consts .., _ | .bvarZeta .., _
  | .delta .., _ | .app .., _ | .beta .., _ | .lam .., _ | .pi .., _
  | .letE .., _ | .zeta .., _ | .iotaSpine .., _ | .lit .., _
  | .eta .., _ | .iotaStarK .., _ | .peq .., _ => PUnit.unit

theorem sameRootEtaKDomain_of_not_isRootEtaKStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A : Expr Nat) {a b T : Expr Nat} :
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    ¬ IsRootEtaKStep h →
    SameRootEtaKDomain A h
  | .iotaStarKEta .., hno => False.elim (hno True.intro)
  | .conv _ _ _ _ _ hinner _, hno =>
      sameRootEtaKDomain_of_not_isRootEtaKStep A hinner hno
  | .refl .., _ | .sortEq .., _ | .consts .., _ | .bvarZeta .., _
  | .delta .., _ | .app .., _ | .beta .., _ | .lam .., _ | .pi .., _
  | .letE .., _ | .zeta .., _ | .iotaSpine .., _ | .lit .., _
  | .eta .., _ | .iotaStarK .., _ | .peq .., _ => True.intro

theorem sameRootEtaKDomain_of_noWrappedRootEtaK_aux {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A B : Expr Nat) {a b T : Expr Nat} :
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    T = .pi A B →
    NoWrappedRootEtaK h →
    SameRootEtaKDomain A h
  | .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, hT, _ => by
      injection hT with hA _
  | .conv _ _ _ _ _ hinner _, _, hno =>
      sameRootEtaKDomain_of_not_isRootEtaKStep A hinner hno
  | .refl .., _, _ | .sortEq .., _, _ | .consts .., _, _ | .bvarZeta .., _, _
  | .delta .., _, _ | .app .., _, _ | .beta .., _, _ | .lam .., _, _ | .pi .., _, _
  | .letE .., _, _ | .zeta .., _, _ | .iotaSpine .., _, _ | .lit .., _, _
  | .eta .., _, _ | .iotaStarK .., _, _ | .peq .., _, _ => True.intro

theorem sameRootEtaKDomain_of_noWrappedRootEtaK {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A B : Expr Nat} (h : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hno : NoWrappedRootEtaK h) :
    SameRootEtaKDomain A h :=
  sameRootEtaKDomain_of_noWrappedRootEtaK_aux A B h rfl hno

/-- Extract either `A_eta = A` or `CtxWfT E n Γ ×' ConvT E n Γ A_eta A (.sort u_eta)`
    in the `.etaK` branch of `parRedT_rec_preMajor_classify` by peeling all
    `.conv` wrappers on `h`. -/
def classify_etaK_dom {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length)
    (A : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKDomainConv A h →
    ∀ {ls : List Level} {xs : List (Expr Nat)}
      (heq : a = foldApps (.const w.recRef ls) xs)
      (hk : xs.length = w.preMajor.length)
      (hls : eqNList ls ls₀),
      match parRedT_rec_preMajor_classify w hNoPrf h heq hk hls with
      | .spine .. => PUnit
      | .etaK _ A_eta _ _ _ u_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          PSum (A_eta = A) (CtxWfT E n Γ ×' ConvT E n Γ A_eta A (.sort u_eta))
  | _, _, _, .refl .., _, _, _, _, _, _ => PUnit.unit
  | _, _, _, .consts .., _, _, [], _, _, _ => PUnit.unit
  | _, _, _, .consts .., _, ls, x :: xs, heq, _, _ =>
      let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
      False.elim (by rw [happ] at heq; exact nomatch heq)
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app .., _, _, [], heq, _, _ => nomatch heq
  | _, _, _, .app .., _, _, _ :: _, _, _, _ => PUnit.unit
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, xs, heq, hk, hls => by
      cases parRedT_rec_preMajor_classify w hNoPrf hstep heq hk hls with
      | spine _ xs' hstep_eq _ hargs =>
          have hlen' : xs'.length ≤ w.preMajor.length := by
            rw [recArgsStep_length hargs, hk]
            exact Nat.le_refl _
          exact False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
      | etaK _ _ _ _ _ _ _ _ hstep_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact False.elim (derivedIotaU_lam_source_false hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w (Nat.le_of_eq hk) wK major heq)
  | _, _, _, .iotaStarKEta _ _ _ A_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      hDom, _, _, _, _, _ =>
      if hA_eq : A_eta = A then
        PSum.inl hA_eq
      else
        PSum.inr (by
          dsimp [RootEtaKDomainConv] at hDom
          rw [if_neg hA_eq] at hDom
          exact hDom)
  | _, _, _, .peq .., _, _, _, _, _, _ => PUnit.unit
  | _, _, _, .conv _ _ _ _ _ hinner hc_wrap, hDom, _, _, heq, hk, hls => by
      have ih := classify_etaK_dom w hNoPrf A hinner hDom heq hk hls
      cases hcl : parRedT_rec_preMajor_classify w hNoPrf hinner heq hk hls with
      | spine _ _ _ _ _ =>
          simp only [parRedT_rec_preMajor_classify, hcl]
          exact PUnit.unit
      | etaK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          simp only [parRedT_rec_preMajor_classify, hcl]
          rw [hcl] at ih
          exact ih
  | _, _, _, .sortEq .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- Full `Type`-valued 1-step/1-step `ParRedT` diamond for ANY `eta` sub-step
    `hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B)` out of the recursor
    pre-major spine `w.preMajor` (WITHOUT `NoEtaKStep hf_step` or
    `NoWrappedRootEtaK hf_step`), dispatching via `parRedT_rec_preMajor_classify`
    across all 18 `ParRedT` constructors:
    - Case (b) (`.spine`, including nested `ParRedT.iotaStarKEta` steps inside
      arguments): extracts the stepped minor `m'` at `w.nparams + 1 + w.ctorIdx`,
      builds `w' : IotaWitness E` via `replacePreMajorWitness`, derives `happ'`,
      `hf'`, `hlhs'`, and `hlι'` at `f'`, lifts the minor step via `hMinorLift`
      to `hrhs_step : ParRedT ... (.assumption A :: Γ) rhs (iotaRhsOf w') B`,
      and returns `f' ⇉ .lam A (iotaRhsOf w')` and `.lam A rhs ⇉ .lam A (iotaRhsOf w')`.
    - Case (a) (`.etaK`, where `hf_step` is a root `ParRedT.iotaStarKEta` step
      `f ⇉ .lam A_eta rhs_eta`, unwrapped OR wrapped in any number of
      `ParRedT.conv` steps): peels the conversion wrappers via `classify_etaK_dom`,
      aligns `rhs_eta = rhs` via `iotaStarKEta_self_derivedIotaU_rhs_eq_of_fields_nil` + `iotaDet`,
      and reuses the root-ηK arm (via `ParRedT.refl` when `A_eta = A`, or a single
      `ParRedT.lam` step along `hcA_eta` when `A_eta ≠ A`). -/
def eta_lamK_stepped_diamond_data
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    {f f' A B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hd : DerivedIota E (iotaLhsOf w) rhs)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hnmin : w.nMinors = 1 := by rfl)
    (hDom : RootEtaKDomainConv A hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_same _ (by first | rfl | trivial)) :
    Σ' rhs' : Expr Nat,
      ParRedT (PEqLeafT E n) E n Γ f' (.lam A rhs') T ×'
      ParRedT (PEqLeafT E n) E n Γ (.lam A rhs) (.lam A rhs') T ×'
      ParRedT (PEqLeafT E n) E n (.assumption A :: Γ) rhs rhs' B :=
  let hcl := envClosed_of_envWfT hW
  let hhd := iotaStarKEta_head happ
  have hf_eq : f = foldApps (.const w.recRef w.ls) (appsSpine f).2 := by
    rw [← hhd.1]
    exact (foldApps_appsSpine f).symm
  have hlen_xs : (appsSpine f).2.length = w.preMajor.length :=
    hhd.2.2.trans w.hpre.symm
  have hdom_cl := classify_etaK_dom w hNoPrf A hf_step hDom
    hf_eq hlen_xs (eqNList_refl w.ls)
  match hcl_step : parRedT_rec_preMajor_classify w hNoPrf hf_step hf_eq hlen_xs (eqNList_refl w.ls) with
  | .spine ls' xs' hf'_eq hls'_symm hargs =>
      have hls' : eqNList w.ls ls' := eqNList_symm hls'_symm
      let mp := minorPreImage w happ
      let m := mp.1
      have hm_get : (appsSpine f).2[w.nparams + 1 + w.ctorIdx]? = some m := mp.2.1
      have hm_eq : w.minor = lift 0 1 m := mp.2.2
      let ⟨m', hm'_get, hm_step⟩ :=
        recArgsStep_get hargs (w.nparams + 1 + w.ctorIdx) hm_get
      have hlenP : (xs'.map (lift 0 1)).length = w.preMajor.length := by
        rw [List.length_map, recArgsStep_length hargs, hlen_xs]
      have hmin' : (xs'.map (lift 0 1))[w.nparams + 1 + w.ctorIdx]? =
          some (lift 0 1 m') :=
        list_getElem?_map_of_some (lift 0 1) xs' (w.nparams + 1 + w.ctorIdx) hm'_get
      let w' := replacePreMajorWitness w ls' (xs'.map (lift 0 1)) (lift 0 1 m')
        hls' hlenP hmin'
      have happ' : recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
          .app (lift 0 1 f') (.bvar 0) :=
        replacePreMajorWitness_happ w hf'_eq hls' hlenP hmin'
      let hf' : HasTyT E n Γ f' (.pi A B) := parRedT_sr_peqT_val hf_step
      let hlhs' : HasTyT E n (.assumption A :: Γ)
          (recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0)) B :=
        stepped_hlhs hcl happ' hf'
      let hlι' : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w') B :=
        stepped_hlι hcl rfl happ' hA hB hf' hmajor hmk hTm0
      have hrhs_eq : rhs = lift 0 1 m :=
        (iotaDet hd (.of w)).trans
          ((headStepT_iotaRhs_fields_nil w hf_nil).trans hm_eq)
      have hrhs'_eq : iotaRhsOf w' = lift 0 1 m' :=
        headStepT_iotaRhs_fields_nil w' hf_nil
      let hm_par : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ)
          (lift 0 1 m) (lift 0 1 m') B :=
        hMinorLift hm_step
      let hrhs_step : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ)
          rhs (iotaRhsOf w') B := by
        rw [hrhs_eq, hrhs'_eq]
        exact hm_par
      let hrhs' : HasTyT E n (.assumption A :: Γ) (iotaRhsOf w') B :=
        parRedT_sr_peqT_val hrhs_step
      let stepL : ParRedT (PEqLeafT E n) E n Γ f' (.lam A (iotaRhsOf w')) T :=
        eta_lamK_step w' happ' hA hf' hrl hsel hfam hmajor hmk hTm0
          (.ofU w') hlι' hlhs' hrhs' hc
      let stepR : ParRedT (PEqLeafT E n) E n Γ (.lam A rhs) (.lam A (iotaRhsOf w')) T :=
        .conv Γ (.lam A rhs) (.lam A (iotaRhsOf w')) (.pi A B) T
          (.lam Γ A A rhs (iotaRhsOf w') B u v (.refl Γ A (.sort u) hA) hA hB
            hrhs_step (.lam Γ A u (iotaRhsOf w') B hA hrhs'))
          hc
      ⟨iotaRhsOf w', stepL, stepR, hrhs_step⟩
  | .etaK _ A_eta _ _ rhs_eta u_eta _ _ hf'_eq happ_eta hA_eta _ _ _ _ _ _ _
      hι_eta _ _ _ _ =>
      have hrhs_eq : rhs_eta = rhs :=
        (iotaStarKEta_self_derivedIotaU_rhs_eq_of_fields_nil
          happ_eta happ hnmin hf_nil hι_eta (.ofU w)).trans
          (iotaDet hd (.of w)).symm
      let mp := minorPreImage w happ
      have hrhs_m : rhs = lift 0 1 mp.1 :=
        (iotaDet hd (.of w)).trans
          ((headStepT_iotaRhs_fields_nil w hf_nil).trans mp.2.2)
      let hm_refl : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ)
          (lift 0 1 mp.1) (lift 0 1 mp.1) B :=
        hMinorLift (.refl mp.1)
      let hrhs : HasTyT E n (.assumption A :: Γ) rhs B := by
        rw [hrhs_m]
        exact parRedT_sr_peqT_val hm_refl
      let hlamA : HasTyT E n Γ (.lam A rhs) (.pi A B) :=
        .lam Γ A u rhs B hA hrhs
      let hlamT : HasTyT E n Γ (.lam A rhs) T :=
        hasTyT_of_tyConvT hlamA hc
      let stepR : ParRedT (PEqLeafT E n) E n Γ (.lam A rhs) (.lam A rhs) T :=
        .refl Γ (.lam A rhs) T hlamT
      let hrhs_step : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ) rhs rhs B :=
        .refl (.assumption A :: Γ) rhs B hrhs
      have hsum : PSum (A_eta = A) (CtxWfT E n Γ ×' ConvT E n Γ A_eta A (.sort u_eta)) := by
        rw [hcl_step] at hdom_cl
        exact hdom_cl
      match hsum with
      | .inl hA_eq =>
          let stepL : ParRedT (PEqLeafT E n) E n Γ f' (.lam A rhs) T := by
            rw [hf'_eq, hA_eq, hrhs_eq]
            exact .refl Γ (.lam A rhs) T hlamT
          ⟨rhs, stepL, stepR, hrhs_step⟩
      | .inr ⟨hΓ, hcA_eta⟩ =>
          let ⟨hA_u_eta, _⟩ := assumpCtxConvT_of_convA hW hΓ hA_eta hcA_eta
          let ⟨_, hcc_A_to_eta⟩ :=
            assumpCtxConvT_of_convA hW hΓ hA_u_eta (.symm Γ A_eta A (.sort u_eta) hcA_eta)
          let hccT_A_to_eta := assumpCtxConvT_to_ctxConvT hcc_A_to_eta
          let hB_at_Aeta : HasTyT E n (.assumption A_eta :: Γ) B (.sort v) :=
            hasTyT_ctx hcl hccT_A_to_eta hB
          let hrhs_at_Aeta : HasTyT E n (.assumption A_eta :: Γ) rhs B :=
            hasTyT_ctx hcl hccT_A_to_eta hrhs
          let hc_pi_Aeta_A : ConvT E n Γ (.pi A_eta B) (.pi A B) (.sort (.imax u_eta v)) :=
            .pi Γ A_eta A B B u_eta v hcA_eta
              (.refl (.assumption A_eta :: Γ) B (.sort v) hB_at_Aeta)
          let hlamA_piAeta : HasTyT E n Γ (.lam A rhs) (.pi A_eta B) :=
            .conv Γ (.lam A rhs) (.pi A B) (.pi A_eta B) (.imax u_eta v) hlamA
              (.symm Γ (.pi A_eta B) (.pi A B) (.sort (.imax u_eta v)) hc_pi_Aeta_A)
          let hc_Aeta_T : TyConvT E n Γ (.pi A_eta B) T :=
            .trans Γ (.pi A_eta B) (.pi A B) T
              (.of Γ (.pi A_eta B) (.pi A B) (.imax u_eta v) hc_pi_Aeta_A) hc
          let stepL0 : ParRedT (PEqLeafT E n) E n Γ (.lam A_eta rhs) (.lam A rhs) T :=
            .conv Γ (.lam A_eta rhs) (.lam A rhs) (.pi A_eta B) T
              (.lam Γ A_eta A rhs rhs B u_eta v hcA_eta hA_eta hB_at_Aeta
                (.refl (.assumption A_eta :: Γ) rhs B hrhs_at_Aeta) hlamA_piAeta)
              hc_Aeta_T
          let stepL : ParRedT (PEqLeafT E n) E n Γ f' (.lam A rhs) T := by
            rw [hf'_eq, hrhs_eq]
            exact stepL0
          ⟨rhs, stepL, stepR, hrhs_step⟩

/-- Full `Type`-valued `ParRedTStar` join data for ANY `eta` × `lam (iotaStarK)`
    peak with BOTH a general `eta` sub-step `hf_step : f ⇉ f'` (WITHOUT
    `NoEtaKStep hf_step` or `NoWrappedRootEtaK hf_step`, covering structural
    spine steps with nested `iotaStarKEta` nodes, unwrapped root `iotaStarKEta`
    steps, and `.conv`-wrapped root `iotaStarKEta` steps) and an arbitrary
    domain conversion `hcA : ConvT E n Γ A A' (.sort u)`:
    1. Dispatches `hf_step` via `eta_lamK_stepped_diamond_data` into `rhs'`,
       `f' ⇉ .lam A rhs'`, and `hrhs_step : ParRedT ... (.assumption A :: Γ) rhs rhs' B`.
    2. Derives `hA' : HasTyT E n Γ A' (.sort u)`, `hB' : HasTyT E n (.assumption A' :: Γ) B (.sort v)`,
       and `hrhs_step' : ParRedT ... (.assumption A' :: Γ) rhs rhs' B` via
       `assumpCtxConvT_of_convA` and `parRedT_assumpCtx` (never assumed).
    3. Joins `f'` (in 2 steps: `f' ⇉ .lam A rhs' ⇉ .lam A' rhs'`) and `.lam A' rhs`
       (in 1 step: `.lam A' rhs ⇉ .lam A' rhs'`) at `.lam A' rhs'`. -/
def eta_lamK_general_star_data
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hd : DerivedIota E (iotaLhsOf w) rhs)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hnmin : w.nMinors = 1 := by rfl)
    (hDom : RootEtaKDomainConv A hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_same _ (by first | rfl | trivial)) :
    Σ' rhs' : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n Γ f' (.lam A' rhs') T ×'
      ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs') T :=
  let hcl := envClosed_of_envWfT hW
  let ⟨rhs', stepL1, _, hrhs_step⟩ :=
    eta_lamK_stepped_diamond_data hW w happ hA hB hrl hsel hfam
      hmajor hmk hTm0 hd hf_nil hc hf_step hNoPrf hMinorLift hnmin hDom
  let hrhs' : HasTyT E n (.assumption A :: Γ) rhs' B :=
    parRedT_sr_peqT_val hrhs_step
  let ⟨hA', hcc⟩ := assumpCtxConvT_of_convA hW hΓ hA hcA
  let hccT := assumpCtxConvT_to_ctxConvT hcc
  let hB' : HasTyT E n (.assumption A' :: Γ) B (.sort v) :=
    hasTyT_ctx hcl hccT hB
  let hrhs'_A' : HasTyT E n (.assumption A' :: Γ) rhs' B :=
    hasTyT_ctx hcl hccT hrhs'
  let hrt2' : HasTyT E n Γ (.lam A' rhs') (.pi A' B) :=
    .lam Γ A' u rhs' B hA' hrhs'_A'
  let hc_pi_symm : ConvT E n Γ (.pi A' B) (.pi A B) (.sort (.imax u v)) :=
    .symm Γ (.pi A B) (.pi A' B) (.sort (.imax u v))
      (.pi Γ A A' B B u v hcA (.refl (.assumption A :: Γ) B (.sort v) hB))
  let hrt1' : HasTyT E n Γ (.lam A' rhs') (.pi A B) :=
    .conv Γ (.lam A' rhs') (.pi A' B) (.pi A B) (.imax u v) hrt2' hc_pi_symm
  let hc' : TyConvT E n Γ (.pi A' B) T :=
    .trans Γ (.pi A' B) (.pi A B) T
      (.of Γ (.pi A' B) (.pi A B) (.imax u v) hc_pi_symm) hc
  let hrhs_step' : ParRedT (PEqLeafT E n) E n (.assumption A' :: Γ) rhs rhs' B :=
    parRedT_assumpCtx hcl hcc hrhs_step
  let stepL2 : ParRedT (PEqLeafT E n) E n Γ (.lam A rhs') (.lam A' rhs') T :=
    .conv Γ (.lam A rhs') (.lam A' rhs') (.pi A B) T
      (.lam Γ A A' rhs' rhs' B u v hcA hA hB
        (.refl (.assumption A :: Γ) rhs' B hrhs') hrt1')
      hc
  let stepR : ParRedT (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs') T :=
    .conv Γ (.lam A' rhs) (.lam A' rhs') (.pi A' B) T
      (.lam Γ A' A' rhs rhs' B u v (.refl Γ A' (.sort u) hA') hA' hB'
        hrhs_step' hrt2')
      hc'
  let hrtT : HasTyT E n Γ (.lam A' rhs') T :=
    hasTyT_of_tyConvT hrt1' hc
  ⟨rhs',
    .tail stepL1 (.tail stepL2 (.refl Γ (.lam A' rhs') T hrtT)),
    .tail stepR (.refl Γ (.lam A' rhs') T hrtT)⟩

/-- Existential `ParRedTStar` join theorem for the general `eta` × `lam (iotaStarK)`
    peak with ANY `hf_step : f ⇉ f'` (without `NoEtaKStep hf_step` or
    `NoWrappedRootEtaK hf_step`) and domain conversion `hcA` (all stepped
    witnesses, stepped typings, and context transports derived). -/
theorem eta_lamK_general_joins
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hd : DerivedIota E (iotaLhsOf w) rhs)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hnmin : w.nMinors = 1 := by rfl)
    (hDom : RootEtaKDomainConv A hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_same _ (by first | rfl | trivial)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  let ⟨rhs', d1, d2⟩ :=
    eta_lamK_general_star_data hW hΓ w happ hcA hA hB hrl hsel hfam
      hmajor hmk hTm0 hd hf_nil hc hf_step hNoPrf hMinorLift hnmin hDom
  ⟨.lam A' rhs', ⟨d1⟩, ⟨d2⟩⟩

/-- At the positive A-2 peak (`partialRec one`), for ANY parallel step
    `hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext (partialRec one) f' commonIndex`
    (including `partialRec_to_contracted`, `.conv`-wrapped `partialRec_to_contracted`,
    and `alternate_partial_step`, without `NoEtaKStep hf_step` or
    `NoWrappedRootEtaK hf_step`) and ANY domain conversion
    `hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero)`,
    `f'` and `.lam A' (.bvar 1)` join in `ParRedTStar` under sort uniqueness
    alone (with both `HasRecProofRoot` and `MinorStepLift` discharged). -/
theorem positive_stepped_eta_lamK_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex)
    (hDom : RootEtaKDomainConv domain hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKDomainConv_of_same _ (by first | rfl | trivial)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  have hNoPrf : ¬ HasRecProofRoot eqEnvT 2 positiveContext
      (witness one).recRef (witness one).ls (witness one).preMajor.length :=
    no_const65_proof_root_of_sortUniq hSortUniq
      (contextWf one positive_levels) (witness one).preMajor.length
  have hMinorLift : MinorStepLift eqEnvT 2 positiveContext
      domain codomain (minorPreImage (witness one) (f := partialRec one) rfl).1 :=
    minorStepLift_positive_a2 hSortUniq (atP' one positive_levels eqTym)
  eta_lamK_general_joins (f := partialRec one) (Tm := eqPTyAt0)
    envWf (contextWf one positive_levels)
    (witness one) rfl hcA (domainTy one positive_levels)
    (codomainTy one positive_levels) rfl
    (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    (instTy' one positive_levels pinEqGate_met)
    (instTy' one positive_levels eqReflTy2)
    (instTy' one positive_levels eqFamTy3) (.of (witness one)) rfl hc
    hf_step hNoPrf hMinorLift rfl hDom

/-! ## Step 7: Self-overlap, `.ofU` coherence, & `FIELDFUL_K` delegation for `ParRedT.iotaStarKEta` -/

/-- `.ofU` coherence: any legacy `DerivedIota` landing at `iotaLhsOf w` has
    `rhs = iotaRhsOf w` by `iotaDet`. -/
theorem derivedIota_rhs_eq_iotaRhsOf {E : ResolvedEnv}
    {w : IotaWitness E} {rhs : Expr Nat}
    (d : DerivedIota E (iotaLhsOf w) rhs) :
    rhs = iotaRhsOf w :=
  iotaDet d (.of w)

/-- Field-free singleton self-overlap (`w.fields = []`, covering `Eq` and `HEq`):
    two `iotaStarKEta` witnesses at the same η-contracted source `f` produce the
    exact same body `iotaRhsOf w₁ = iotaRhsOf w₂`. -/
theorem iotaStarKEta_self_rhs_eq_of_fields_nil {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1)
    (hf1 : w₁.fields = []) (hf2 : w₂.fields = []) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  obtain ⟨hrec, _, hpm⟩ := iotaStarKEta_same_rec_preMajor happ₁ happ₂
  have hm : w₁.minor = w₂.minor :=
    headStepT_iotaStarK_minor_eq hrec hpm hn1 hn2
  rw [headStepT_iotaRhs_fields_nil w₁ hf1,
    headStepT_iotaRhs_fields_nil w₂ hf2, hm]

/-- `.ofU`-coherent field-free singleton self-overlap on the actual constructor
    right-hand sides `rhs₁, rhs₂` (`d₁ : DerivedIota E (iotaLhsOf w₁) rhs₁`,
    `d₂ : DerivedIota E (iotaLhsOf w₂) rhs₂`): `rhs₁ = rhs₂`. -/
theorem iotaStarKEta_self_actual_rhs_eq_of_fields_nil {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f rhs₁ rhs₂ : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1)
    (hf1 : w₁.fields = []) (hf2 : w₂.fields = [])
    (d₁ : DerivedIota E (iotaLhsOf w₁) rhs₁)
    (d₂ : DerivedIota E (iotaLhsOf w₂) rhs₂) :
    rhs₁ = rhs₂ := by
  rw [derivedIota_rhs_eq_iotaRhsOf d₁, derivedIota_rhs_eq_iotaRhsOf d₂]
  exact iotaStarKEta_self_rhs_eq_of_fields_nil happ₁ happ₂ hn1 hn2 hf1 hf2

/-- Canonical-field singleton self-overlap (`FIELDFUL_K.md`, #6605:
    `w.fields = [.bvar 0]`, where the bound major is `.bvar 0`):
    two `iotaStarKEta` witnesses at the same η-contracted source `f` produce the
    exact same body `iotaRhsOf w₁ = iotaRhsOf w₂`. -/
theorem iotaStarKEta_self_rhs_eq_of_field_bvar0 {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1)
    (hf1 : w₁.fields = [.bvar 0]) (hf2 : w₂.fields = [.bvar 0]) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  obtain ⟨hrec, hls, hpm⟩ := iotaStarKEta_same_rec_preMajor happ₁ happ₂
  exact headStepT_iotaStarKField_rhs_eq hrec hls hpm rfl hf1 hf2 hn1 hn2

/-- `.ofU`-coherent canonical-field singleton self-overlap on the actual
    constructor right-hand sides `rhs₁, rhs₂` (`w.fields = [.bvar 0]`):
    `rhs₁ = rhs₂`. -/
theorem iotaStarKEta_self_actual_rhs_eq_of_field_bvar0 {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f rhs₁ rhs₂ : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1)
    (hf1 : w₁.fields = [.bvar 0]) (hf2 : w₂.fields = [.bvar 0])
    (d₁ : DerivedIota E (iotaLhsOf w₁) rhs₁)
    (d₂ : DerivedIota E (iotaLhsOf w₂) rhs₂) :
    rhs₁ = rhs₂ := by
  rw [derivedIota_rhs_eq_iotaRhsOf d₁, derivedIota_rhs_eq_iotaRhsOf d₂]
  exact iotaStarKEta_self_rhs_eq_of_field_bvar0 happ₁ happ₂ hn1 hn2 hf1 hf2

/-- The unguarded syntactic RHS-equality proposition for `iotaStarKEta`
    witnesses (kept as a regression pin for `not_fieldful_contract`,
    cf. `#6951` comment `6162995462`). Because `IotaWitness.fields` does not appear
    in `recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)`, two raw
    `IotaWitness` values on a fieldful singleton inductive (`pinLoopEnvT`) can
    share the same pre-major source `f` while choosing different field lists
    `[.bvar 0]` vs `[.bvar 1]`. -/
def UnguardedFieldfulK (E : ResolvedEnv) : Prop :=
  ∀ {w₁ w₂ : IotaWitness E} {f rhs₁ rhs₂ : Expr Nat},
    recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0) →
    recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0) →
    w₁.nMinors = 1 → w₂.nMinors = 1 →
    Nonempty (DerivedIotaU E (iotaLhsOf w₁) rhs₁) →
    Nonempty (DerivedIotaU E (iotaLhsOf w₂) rhs₂) →
    rhs₁ = rhs₂

/-- Second `IotaWitness` on `pinLoopEnvT` (recursive singleton `Loop : Prop`,
    `#6951` comment `6162995462`): identical to `wLoopK` (`RcicParRedTPins.lean`)
    except `fields := [.bvar 1]`. -/
def changedFields : IotaWitness pinLoopEnvT :=
  { wLoopK with
    fields := [.bvar 1]
    hlen := rfl
    hnpar := rfl }

/-- Common η-contracted recursor prefix for `wLoopK` and `changedFields`. -/
def recPrefixTerm : Expr Nat :=
  .app (.app (.const 62 [.param 0]) (.bvar 1)) (.bvar 0)

/-- `wLoopK` and `changedFields` produce distinct syntactic right-hand sides
    (`(.app (.app (.bvar 1) (.bvar 0)) ...)` vs `(.app (.app (.bvar 1) (.bvar 1)) ...)`). -/
theorem rhs_differ : iotaRhsOf wLoopK ≠ iotaRhsOf changedFields := by
  decide

/-- Regression pin (`#6951` comment `6162995462`): `UnguardedFieldfulK` is
    refuted on `pinLoopEnvT` by `wLoopK` and `changedFields`. -/
theorem not_fieldful_contract : ¬ UnguardedFieldfulK pinLoopEnvT := by
  intro h
  exact rhs_differ
    (h (w₁ := wLoopK) (w₂ := changedFields) (f := recPrefixTerm)
      rfl rfl rfl rfl ⟨.ofU wLoopK⟩ ⟨.ofU changedFields⟩)

/-- Canonical witness region for `ParRedT.iotaStarKEta` (`FIELDFUL_K.md`, #6605):
    singleton recursor (`w.nMinors = 1`) whose constructor fields are either
    empty (`w.fields = []`, e.g. `Eq`, `HEq`) or the canonical single bound
    major variable (`w.fields = [.bvar 0]`, e.g. `wLoopK`). -/
def CanonicalEtaKWitness {E : ResolvedEnv} (w : IotaWitness E) : Prop :=
  w.nMinors = 1 ∧ (w.fields = [] ∨ w.fields = [.bvar 0])

theorem witness_canonicalEtaKWitness (u : Level) :
    CanonicalEtaKWitness (witness u) :=
  ⟨rfl, .inl rfl⟩

theorem wLoopK_canonicalEtaKWitness :
    CanonicalEtaKWitness wLoopK :=
  ⟨rfl, .inr rfl⟩

theorem not_changedFields_canonicalEtaKWitness :
    ¬ CanonicalEtaKWitness changedFields := by
  intro ⟨_, h⟩
  rcases h with h0 | h1
  · revert h0; decide
  · revert h1; decide

/-- On the canonical witness region `CanonicalEtaKWitness`, two `iotaStarKEta`
    witnesses at the same η-contracted source `f` have identical `iotaRhsOf`:
    `w₁.fields.length = w₂.fields.length` forces both witnesses into the same
    canonical branch (`[]` or `[.bvar 0]`). -/
theorem iotaStarKEta_self_rhs_eq_of_canonical {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcan₁ : CanonicalEtaKWitness w₁)
    (hcan₂ : CanonicalEtaKWitness w₂) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  obtain ⟨hrec, _, hpm⟩ := iotaStarKEta_same_rec_preMajor happ₁ happ₂
  obtain ⟨hn1, hfl1⟩ := hcan₁
  obtain ⟨hn2, hfl2⟩ := hcan₂
  rcases hfl1 with hf1 | hf1
  · have hf2 : w₂.fields = [] :=
      headStepT_iotaStarK_fields_nil hrec.symm hpm.symm hn1 hf1
    exact iotaStarKEta_self_rhs_eq_of_fields_nil happ₁ happ₂ hn1 hn2 hf1 hf2
  · rcases hfl2 with hf2 | hf2
    · have hf1_nil : w₁.fields = [] :=
        headStepT_iotaStarK_fields_nil hrec hpm hn2 hf2
      rw [hf1] at hf1_nil
      cases hf1_nil
    · exact iotaStarKEta_self_rhs_eq_of_field_bvar0 happ₁ happ₂ hn1 hn2 hf1 hf2

/-- `.ofU`-coherent canonical self-overlap on the actual constructor right-hand
    sides `rhs₁, rhs₂` (`d₁ : DerivedIota E (iotaLhsOf w₁) rhs₁`,
    `d₂ : DerivedIota E (iotaLhsOf w₂) rhs₂`): `rhs₁ = rhs₂`. -/
theorem iotaStarKEta_self_actual_rhs_eq_of_canonical {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {f rhs₁ rhs₂ : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcan₁ : CanonicalEtaKWitness w₁)
    (hcan₂ : CanonicalEtaKWitness w₂)
    (d₁ : DerivedIota E (iotaLhsOf w₁) rhs₁)
    (d₂ : DerivedIota E (iotaLhsOf w₂) rhs₂) :
    rhs₁ = rhs₂ := by
  rw [derivedIota_rhs_eq_iotaRhsOf d₁, derivedIota_rhs_eq_iotaRhsOf d₂]
  exact iotaStarKEta_self_rhs_eq_of_canonical happ₁ happ₂ hcan₁ hcan₂

/-- Even for the non-canonical `changedFields` witness on `pinLoopEnvT`, when
    both `.bvar 0` and `.bvar 1` have type `Loop = .const 60 [] : Sort 0` in
    context `Δ`, `iotaRhsOf wLoopK` steps in a single `PEqT` step to
    `iotaRhsOf changedFields` by proof irrelevance at the `.bvar 0` vs `.bvar 1`
    leaves. -/
def wLoopK_changedFields_peq {n : Nat} {Δ : LCtx}
    (hb0 : HasTyT pinLoopEnvT n Δ (.bvar 0) (.const 60 []))
    (hb1 : HasTyT pinLoopEnvT n Δ (.bvar 1) (.const 60 [])) :
    PEqT pinLoopEnvT n Δ (iotaRhsOf wLoopK) (iotaRhsOf changedFields) := by
  have hLoop0 : HasTyT pinLoopEnvT n Δ (.const 60 []) (.sort .zero) :=
    .const Δ 60 [] (m := wLoopK.famMember) wLoopK.hfam rfl rfl
  have hp01 : PEqT pinLoopEnvT n Δ (.bvar 0) (.bvar 1) :=
    .proof Δ (.bvar 0) (.bvar 1) (.const 60 []) (.const 60 []) hLoop0 hLoop0 hb0 hb1
  change PEqT pinLoopEnvT n Δ
    (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.const 62 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0)))
    (.app (.app (.bvar 1) (.bvar 1))
      (.app (.app (.app (.const 62 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 1)))
  exact .app Δ _ _ _ _
    (.app Δ _ _ _ _ (PEqT.refl (.bvar 1)) hp01)
    (.app Δ _ _ _ _
      (PEqT.refl (.app (.app (.const 62 [.param 0]) (.bvar 2)) (.bvar 1)))
      hp01)

/-- In any typing context `Δ` where `.bvar 0` and `.bvar 1` both inhabit
    `Loop = .const 60 [] : Sort 0` and both `iotaRhsOf wLoopK` and
    `iotaRhsOf changedFields` have type `B`, `iotaRhsOf wLoopK` and
    `iotaRhsOf changedFields` join in one `ParRedT.peq` step at `B`.
    (Because `changedFields` sets `fields := [.bvar 1]` which collides with
    `wLoopK.minor = .bvar 1`, see `wLoopK_bvar3` and `wLoopK_bvar3_concrete_body_join` /
    `wLoopK_bvar3_concrete_lam_join` below for the concrete context
    `pinLoopTwoVarsCtx` jointly inhabiting all typing premises with zero open
    hypotheses.) -/
def wLoopK_changedFields_typed_join {n : Nat} {Δ : LCtx} {B : Expr Nat}
    (hb0 : HasTyT pinLoopEnvT n Δ (.bvar 0) (.const 60 []))
    (hb1 : HasTyT pinLoopEnvT n Δ (.bvar 1) (.const 60 []))
    (hrhs1 : HasTyT pinLoopEnvT n Δ (iotaRhsOf wLoopK) B)
    (hrhs2 : HasTyT pinLoopEnvT n Δ (iotaRhsOf changedFields) B) :
    ParRedTStar (PEqLeafT pinLoopEnvT n) pinLoopEnvT n Δ
      (iotaRhsOf wLoopK) (iotaRhsOf changedFields) B ×'
    ParRedTStar (PEqLeafT pinLoopEnvT n) pinLoopEnvT n Δ
      (iotaRhsOf changedFields) (iotaRhsOf changedFields) B :=
  let hstep : ParRedT (PEqLeafT pinLoopEnvT n) pinLoopEnvT n Δ
      (iotaRhsOf wLoopK) (iotaRhsOf changedFields) B :=
    .peq Δ (iotaRhsOf wLoopK) (iotaRhsOf changedFields) B
      ⟨wLoopK_changedFields_peq hb0 hb1, hrhs1, hrhs2⟩
  ⟨.tail hstep (.refl Δ (iotaRhsOf changedFields) B hrhs2),
    .refl Δ (iotaRhsOf changedFields) B hrhs2⟩

/-- Transport a multi-step `ParRedTStar` chain across `AssumpCtxConvT`. -/
def parRedTStar_assumpCtx {E : ResolvedEnv} (hcl : EnvClosed E) {n : Nat}
    {Γ Δ : LCtx} (hcc : AssumpCtxConvT E n Γ Δ)
    {a b T : Expr Nat} :
    ParRedTStar (PEqLeafT E n) E n Γ a b T →
    ParRedTStar (PEqLeafT E n) E n Δ a b T
  | .refl _ a T ha =>
      .refl Δ a T (hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc) ha)
  | .tail hstep hrest =>
      .tail (parRedT_assumpCtx hcl hcc hstep) (parRedTStar_assumpCtx hcl hcc hrest)

/-- Lift a body `ParRedTStar` chain in `.assumption A :: Γ` to a λ-abstraction
    `ParRedTStar` chain in `Γ` at any target type `T` with `TyConvT E n Γ (.pi A B) T`. -/
def parRedTStar_lam_body {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B T : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hc : TyConvT E n Γ (.pi A B) T)
    {b₁ b₂ : Expr Nat} :
    ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) b₁ b₂ B →
    ParRedTStar (PEqLeafT E n) E n Γ (.lam A b₁) (.lam A b₂) T
  | .refl _ b B hb =>
      let hlam : HasTyT E n Γ (.lam A b) (.pi A B) := .lam Γ A u b B hA hb
      .refl Γ (.lam A b) T (hasTyT_of_tyConvT hlam hc)
  | .tail (b := b_mid) hstep hrest =>
      let hb_mid : HasTyT E n (.assumption A :: Γ) b_mid B :=
        parRedT_sr_peqT_val hstep
      let hlam_mid : HasTyT E n Γ (.lam A b_mid) (.pi A B) :=
        .lam Γ A u b_mid B hA hb_mid
      let hstep_lam : ParRedT (PEqLeafT E n) E n Γ (.lam A b₁) (.lam A b_mid) T :=
        .conv Γ (.lam A b₁) (.lam A b_mid) (.pi A B) T
          (.lam Γ A A b₁ b_mid B u v (.refl Γ A (.sort u) hA) hA hB hstep hlam_mid)
          hc
      .tail hstep_lam (parRedTStar_lam_body hA hB hc hrest)

/-- Transitive composition of `ParRedTStar`. -/
def parRedTStar_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c T : Expr Nat} :
    ParRedTStar (PEqLeafT E n) E n Γ a b T →
    ParRedTStar (PEqLeafT E n) E n Γ b c T →
    ParRedTStar (PEqLeafT E n) E n Γ a c T
  | .refl _ _ _ _, h2 => h2
  | .tail hstep h1, h2 => .tail hstep (parRedTStar_trans h1 h2)

/-- Named residual contract `FIELDFUL_K` (alongside `ParRedT.iotaStarK` in
    `research/rcic/FIELDFUL_K.md`, #6605): given two typed singleton-Prop
    `iotaStarKEta` contractions at the same η-contracted source `f` whose bodies
    `rhs₁, rhs₂` are both typed at `B` in `.assumption A :: Γ`, `rhs₁` and
    `rhs₂` join via `ParRedTStar` at `B` in `.assumption A :: Γ`.
    Unlike `UnguardedFieldfulK`, this contract carries the actual typing
    premises of `iotaStarKEta` and produces a typed `ParRedTStar` join rather
    than raw untyped syntactic equality.
    Inhabitants and proved regions:
    - The full universally quantified type `FIELDFUL_K E` is unconditionally
      inhabited for `E = emptyEnv` (`fieldfulK_emptyEnv`) and `E = eqEnvT`
      (`fieldfulK_eqEnvT`, covering all `w₁, w₂ : IotaWitness eqEnvT` and both
      `.ofU` and `.ofUS` arms of `DerivedIotaU`), and inhabited for
      `E = pinLoopEnvT` under constructor domain inversion `LoopMkDomainInv`
      (`fieldfulK_pinLoopEnvT_of_mkDomInv`).
    - For arbitrary `E : ResolvedEnv`, the canonical-witness restriction
      `CanonicalFIELDFUL_K E` (`CanonicalEtaKWitness`) is unconditionally
      inhabited (`canonicalFieldfulK E`), and field-free singletons
      (`w.nMinors = 1`, `w.fields = []`) are discharged across both `.ofU` and
      `.ofUS` arms by `iotaStarKEta_self_join_of_fields_nil`.
    - On `pinLoopEnvT` in `pinLoopTwoVarsCtx`, the canonical witness `wLoopK`
      (`fields = [.bvar 0]`) and the non-canonical witness `wLoopK_bvar3`
      (`fields = [.bvar 3]`) have all typing premises concretely inhabited and
      join unconditionally via `wLoopK_bvar3_concrete_body_join` and
      `wLoopK_bvar3_concrete_lam_join`. -/
def FIELDFUL_K (E : ResolvedEnv) : Type :=
  ∀ {n : Nat} {Γ : LCtx} {A B Tm₁ Tm₂ f rhs₁ rhs₂ : Expr Nat}
    {w₁ w₂ : IotaWitness E},
    recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0) →
    recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0) →
    w₁.nMinors = 1 → w₂.nMinors = 1 →
    HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm₁ →
    HasTyT E n (.assumption A :: Γ) (ctorMajor w₁) Tm₁ →
    HasTyT E n (.assumption A :: Γ) Tm₁ (.sort .zero) →
    HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm₂ →
    HasTyT E n (.assumption A :: Γ) (ctorMajor w₂) Tm₂ →
    HasTyT E n (.assumption A :: Γ) Tm₂ (.sort .zero) →
    DerivedIotaU E (iotaLhsOf w₁) rhs₁ →
    DerivedIotaU E (iotaLhsOf w₂) rhs₂ →
    HasTyT E n (.assumption A :: Γ) rhs₁ B →
    HasTyT E n (.assumption A :: Γ) rhs₂ B →
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₁ rhs_join B ×'
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₂ rhs_join B

/-- Self-overlap body join under the explicit named `FIELDFUL_K` hypothesis. -/
def iotaStarKEta_self_join_of_fieldfulK {E : ResolvedEnv}
    (hFieldfulK : FIELDFUL_K E)
    {n : Nat} {Γ : LCtx} {A B Tm₁ Tm₂ f rhs₁ rhs₂ : Expr Nat}
    {w₁ w₂ : IotaWitness E}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1)
    (hmaj₁ : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm₁)
    (hmk₁ : HasTyT E n (.assumption A :: Γ) (ctorMajor w₁) Tm₁)
    (hTm0₁ : HasTyT E n (.assumption A :: Γ) Tm₁ (.sort .zero))
    (hmaj₂ : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm₂)
    (hmk₂ : HasTyT E n (.assumption A :: Γ) (ctorMajor w₂) Tm₂)
    (hTm0₂ : HasTyT E n (.assumption A :: Γ) Tm₂ (.sort .zero))
    (hι₁ : DerivedIotaU E (iotaLhsOf w₁) rhs₁)
    (hι₂ : DerivedIotaU E (iotaLhsOf w₂) rhs₂)
    (hrhs₁ : HasTyT E n (.assumption A :: Γ) rhs₁ B)
    (hrhs₂ : HasTyT E n (.assumption A :: Γ) rhs₂ B) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₁ rhs_join B ×'
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₂ rhs_join B :=
  hFieldfulK happ₁ happ₂ hn1 hn2 hmaj₁ hmk₁ hTm0₁ hmaj₂ hmk₂ hTm0₂ hι₁ hι₂ hrhs₁ hrhs₂

/-- Unconditional discharge of the `FIELDFUL_K` body-join obligation for
    field-free singletons (`w₂.nMinors = 1`, `w₂.fields = []`) across BOTH
    `.ofU` and `.ofUS` arms of `DerivedIotaU`. -/
def iotaStarKEta_self_join_of_fields_nil {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A B f rhs₁ rhs₂ : Expr Nat}
    {w₁ w₂ : IotaWitness E}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hn2 : w₂.nMinors = 1)
    (hf2 : w₂.fields = [])
    (hι₁ : DerivedIotaU E (iotaLhsOf w₁) rhs₁)
    (hι₂ : DerivedIotaU E (iotaLhsOf w₂) rhs₂)
    (hrhs₂ : HasTyT E n (.assumption A :: Γ) rhs₂ B) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₁ rhs_join B ×'
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₂ rhs_join B := by
  have heq : rhs₁ = rhs₂ :=
    iotaStarKEta_self_derivedIotaU_rhs_eq_of_fields_nil happ₁ happ₂ hn2 hf2 hι₁ hι₂
  rw [heq]
  exact ⟨rhs₂, .refl (.assumption A :: Γ) rhs₂ B hrhs₂,
    .refl (.assumption A :: Γ) rhs₂ B hrhs₂⟩

/-- Unconditional discharge of the `FIELDFUL_K` body-join obligation on the
    `.ofU` canonical witness region (`CanonicalEtaKWitness w₁`,
    `CanonicalEtaKWitness w₂`). -/
def iotaStarKEta_self_join_of_canonical {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A B f rhs₁ rhs₂ : Expr Nat}
    {w₁ w₂ : IotaWitness E}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcan₁ : CanonicalEtaKWitness w₁)
    (hcan₂ : CanonicalEtaKWitness w₂)
    (d₁ : DerivedIota E (iotaLhsOf w₁) rhs₁)
    (d₂ : DerivedIota E (iotaLhsOf w₂) rhs₂)
    (hrhs₂ : HasTyT E n (.assumption A :: Γ) rhs₂ B) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₁ rhs_join B ×'
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₂ rhs_join B := by
  have heq : rhs₁ = rhs₂ :=
    iotaStarKEta_self_actual_rhs_eq_of_canonical happ₁ happ₂ hcan₁ hcan₂ d₁ d₂
  rw [heq]
  exact ⟨rhs₂, .refl (.assumption A :: Γ) rhs₂ B hrhs₂,
    .refl (.assumption A :: Γ) rhs₂ B hrhs₂⟩

/-- `emptyEnv` has no `IotaWitness` (no members are present). -/
theorem emptyEnv_no_iotaWitness (w : IotaWitness emptyEnv) : False := by
  have h := w.hrec
  change none = some w.recMember at h
  cases h

/-- Unconditional inhabitant of `FIELDFUL_K emptyEnv`. -/
def fieldfulK_emptyEnv : FIELDFUL_K emptyEnv :=
  fun {_ _ _ _ _ _ _ _ _ w₁ _} _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    False.elim (emptyEnv_no_iotaWitness w₁)

/-- Every `w : IotaWitness eqEnvT` is a field-free singleton recursor witness
    (`w.nMinors = 1` and `w.fields = []`): the only `.recursorM` in `eqEnvT` is
    `65` (`eqRecT`), the only `.constructorM` is `64` (`eqReflT`), and the only
    `.inductiveM` is `63` (`eqFamT`), forcing `w.nMinors = 1`, `w.nindices = 1`,
    `w.nparams = 2`, and `w.fields.length = 0`. -/
theorem eqEnvT_iotaWitness_nMinors_and_fields_nil (w : IotaWitness eqEnvT) :
    w.nMinors = 1 ∧ w.fields = [] := by
  have hrec_mem : eqEnvT.members w.recRef = some w.recMember := w.hrec
  rw [eqEnvT_mem] at hrec_mem
  have hrec_eq : w.recRef = 65 ∧ w.recMember = eqRecT := by
    by_cases h65 : w.recRef = 65
    · simp only [h65, ↓reduceIte, Option.some.injEq] at hrec_mem
      exact ⟨h65, hrec_mem.symm⟩
    · simp only [h65, ↓reduceIte] at hrec_mem
      by_cases h64 : w.recRef = 64
      · simp only [h64, ↓reduceIte, Option.some.injEq] at hrec_mem
        have hk := w.hrecK
        rw [← hrec_mem] at hk
        cases hk
      · simp only [h64, ↓reduceIte] at hrec_mem
        by_cases h63 : w.recRef = 63
        · simp only [h63, ↓reduceIte, Option.some.injEq] at hrec_mem
          have hk := w.hrecK
          rw [← hrec_mem] at hk
          cases hk
        · simp only [h63, ↓reduceIte] at hrec_mem
          cases hrec_mem
  have hctor_mem : eqEnvT.members w.ctorRef = some w.ctorMember := w.hctor
  rw [eqEnvT_mem] at hctor_mem
  have hctor_eq : w.ctorRef = 64 ∧ w.ctorMember = eqReflT := by
    by_cases h65 : w.ctorRef = 65
    · simp only [h65, ↓reduceIte, Option.some.injEq] at hctor_mem
      have hk := w.hctorK
      rw [← hctor_mem] at hk
      cases hk
    · simp only [h65, ↓reduceIte] at hctor_mem
      by_cases h64 : w.ctorRef = 64
      · simp only [h64, ↓reduceIte, Option.some.injEq] at hctor_mem
        exact ⟨h64, hctor_mem.symm⟩
      · simp only [h64, ↓reduceIte] at hctor_mem
        by_cases h63 : w.ctorRef = 63
        · simp only [h63, ↓reduceIte, Option.some.injEq] at hctor_mem
          have hk := w.hctorK
          rw [← hctor_mem] at hk
          cases hk
        · simp only [h63, ↓reduceIte] at hctor_mem
          cases hctor_mem
  have hfam_mem : eqEnvT.members w.familyRef = some w.famMember := w.hfam
  rw [eqEnvT_mem] at hfam_mem
  have hfam_eq : w.familyRef = 63 ∧ w.famMember = eqFamT := by
    by_cases h65 : w.familyRef = 65
    · simp only [h65, ↓reduceIte, Option.some.injEq] at hfam_mem
      have hk := w.hfamK
      rw [← hfam_mem] at hk
      cases hk
    · simp only [h65, ↓reduceIte] at hfam_mem
      by_cases h64 : w.familyRef = 64
      · simp only [h64, ↓reduceIte, Option.some.injEq] at hfam_mem
        have hk := w.hfamK
        rw [← hfam_mem] at hk
        cases hk
      · simp only [h64, ↓reduceIte] at hfam_mem
        by_cases h63 : w.familyRef = 63
        · simp only [h63, ↓reduceIte, Option.some.injEq] at hfam_mem
          exact ⟨h63, hfam_mem.symm⟩
        · simp only [h63, ↓reduceIte] at hfam_mem
          cases hfam_mem
  have hnmin1 : w.nMinors = 1 := by
    have hidx := w.hrecIdx
    rw [hrec_eq.1, hfam_eq.1] at hidx
    omega
  have hnpar_sum : w.nparams + w.fields.length = 2 := by
    have hp := w.hnpar
    rw [hctor_eq.2] at hp
    exact hp
  have hnidx_sum : w.nparams + w.nindices = 3 := by
    have hi := w.hnidx
    rw [hfam_eq.2] at hi
    exact hi
  have htot : w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 := by
    omega
  have hpeelR := w.hpeelRec
  rw [htot, hrec_eq.2] at hpeelR
  have hbody_eq : w.recBody = .app (.app (.bvar 3) (.bvar 1)) (.bvar 0) := by
    injection hpeelR with hpair
    exact (Prod.mk.inj hpair).2.symm
  have hnidx_cases : w.nindices = 1 ∨ w.nindices = 2 ∨ w.nindices = 3 := by
    omega
  have hnidx1 : w.nindices = 1 := by
    rcases hnidx_cases with h1 | h2 | h3
    · exact h1
    · have hb := w.hrecBody
      rw [hbody_eq, hnmin1, h2] at hb
      cases hb
    · have hb := w.hrecBody
      rw [hbody_eq, hnmin1, h3] at hb
      cases hb
  have hflen0 : w.fields.length = 0 := by
    omega
  refine ⟨hnmin1, ?_⟩
  cases hfl : w.fields with
  | nil => rfl
  | cons _ _ =>
      rw [hfl] at hflen0
      cases hflen0

/-- Every `w : IotaWitness eqEnvT` is in `CanonicalEtaKWitness`. -/
theorem eqEnvT_iotaWitness_canonical (w : IotaWitness eqEnvT) :
    CanonicalEtaKWitness w := by
  obtain ⟨hn, hf⟩ := eqEnvT_iotaWitness_nMinors_and_fields_nil w
  exact ⟨hn, .inl hf⟩

/-- **Unconditional inhabitant of `FIELDFUL_K eqEnvT`** across both `.ofU` and
    `.ofUS` arms of `DerivedIotaU`: every `IotaWitness eqEnvT` has
    `w.nMinors = 1` and `w.fields = []` (`eqEnvT_iotaWitness_nMinors_and_fields_nil`),
    so `iotaStarKEta_self_join_of_fields_nil` discharges `FIELDFUL_K eqEnvT`
    with zero extra hypotheses. -/
def fieldfulK_eqEnvT : FIELDFUL_K eqEnvT :=
  fun {_ _ _ _ _ _ _ _ _ _ w₂} happ₁ happ₂ _ _ _ _ _ _ _ _ hι₁ hι₂ _ hrhs₂ =>
    let h₂ := eqEnvT_iotaWitness_nMinors_and_fields_nil w₂
    iotaStarKEta_self_join_of_fields_nil happ₁ happ₂ h₂.1 h₂.2 hι₁ hι₂ hrhs₂

/-- Named canonical-witness `FIELDFUL_K` supplier (`FIELDFUL_K.md`, #6605)
    for arbitrary `E : ResolvedEnv`: any two `.ofU` singleton `iotaStarKEta`
    contractions in `CanonicalEtaKWitness` (`w.fields = [] ∨ w.fields = [.bvar 0]`)
    at the same source `f` join at `B` in `.assumption A :: Γ`. -/
def CanonicalFIELDFUL_K (E : ResolvedEnv) : Type :=
  ∀ {n : Nat} {Γ : LCtx} {A B f rhs₁ rhs₂ : Expr Nat}
    {w₁ w₂ : IotaWitness E},
    recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0) →
    recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0) →
    CanonicalEtaKWitness w₁ →
    CanonicalEtaKWitness w₂ →
    DerivedIota E (iotaLhsOf w₁) rhs₁ →
    DerivedIota E (iotaLhsOf w₂) rhs₂ →
    HasTyT E n (.assumption A :: Γ) rhs₂ B →
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₁ rhs_join B ×'
      ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs₂ rhs_join B

/-- Unconditional inhabitant of `CanonicalFIELDFUL_K E` for every `E : ResolvedEnv`. -/
def canonicalFieldfulK (E : ResolvedEnv) : CanonicalFIELDFUL_K E :=
  fun happ₁ happ₂ hcan₁ hcan₂ d₁ d₂ hrhs₂ =>
    iotaStarKEta_self_join_of_canonical happ₁ happ₂ hcan₁ hcan₂ d₁ d₂ hrhs₂

/-- Complete structural characterization of every `w : IotaWitness pinLoopEnvT`:
    the only `.recursorM` in `pinLoopEnvT` is `62` (`pinLoopRecT`), the only
    `.constructorM` is `61` (`pinLoopMkT`), and the only `.inductiveM` is `60`
    (`pinLoopFamT`), forcing `w.nparams = 0`, `w.nindices = 0`, `w.nMinors = 1`,
    `w.ctorIdx = 0`, `w.ctorParams = []`, `w.kinds = [.directRec]`,
    `w.ctorAfterParams = .pi (.const 60 []) (.const 60 [])`, and `w.fields.length = 1`. -/
theorem pinLoopEnvT_iotaWitness_shape (w : IotaWitness pinLoopEnvT) :
    w.recRef = 62 ∧ w.recMember = pinLoopRecT ∧
    w.ctorRef = 61 ∧ w.ctorMember = pinLoopMkT ∧
    w.familyRef = 60 ∧ w.famMember = pinLoopFamT ∧
    w.nparams = 0 ∧ w.nindices = 0 ∧ w.nMinors = 1 ∧ w.ctorIdx = 0 ∧
    w.ctorParams = [] ∧ w.kinds = [.directRec] ∧
    w.ctorAfterParams = .pi (.const 60 []) (.const 60 []) ∧
    w.fields.length = 1 := by
  have hrec_mem : pinLoopEnvT.members w.recRef = some w.recMember := w.hrec
  rw [pinLoopEnvT_mem] at hrec_mem
  have hrec_eq : w.recRef = 62 ∧ w.recMember = pinLoopRecT := by
    by_cases h62 : w.recRef = 62
    · simp only [h62, ↓reduceIte, Option.some.injEq] at hrec_mem
      exact ⟨h62, hrec_mem.symm⟩
    · simp only [h62, ↓reduceIte] at hrec_mem
      by_cases h61 : w.recRef = 61
      · simp only [h61, ↓reduceIte, Option.some.injEq] at hrec_mem
        have hk := w.hrecK
        rw [← hrec_mem] at hk
        cases hk
      · simp only [h61, ↓reduceIte] at hrec_mem
        by_cases h60 : w.recRef = 60
        · simp only [h60, ↓reduceIte, Option.some.injEq] at hrec_mem
          have hk := w.hrecK
          rw [← hrec_mem] at hk
          cases hk
        · simp only [h60, ↓reduceIte] at hrec_mem
          cases hrec_mem
  have hctor_mem : pinLoopEnvT.members w.ctorRef = some w.ctorMember := w.hctor
  rw [pinLoopEnvT_mem] at hctor_mem
  have hctor_eq : w.ctorRef = 61 ∧ w.ctorMember = pinLoopMkT := by
    by_cases h62 : w.ctorRef = 62
    · simp only [h62, ↓reduceIte, Option.some.injEq] at hctor_mem
      have hk := w.hctorK
      rw [← hctor_mem] at hk
      cases hk
    · simp only [h62, ↓reduceIte] at hctor_mem
      by_cases h61 : w.ctorRef = 61
      · simp only [h61, ↓reduceIte, Option.some.injEq] at hctor_mem
        exact ⟨h61, hctor_mem.symm⟩
      · simp only [h61, ↓reduceIte] at hctor_mem
        by_cases h60 : w.ctorRef = 60
        · simp only [h60, ↓reduceIte, Option.some.injEq] at hctor_mem
          have hk := w.hctorK
          rw [← hctor_mem] at hk
          cases hk
        · simp only [h60, ↓reduceIte] at hctor_mem
          cases hctor_mem
  have hfam_mem : pinLoopEnvT.members w.familyRef = some w.famMember := w.hfam
  rw [pinLoopEnvT_mem] at hfam_mem
  have hfam_eq : w.familyRef = 60 ∧ w.famMember = pinLoopFamT := by
    by_cases h62 : w.familyRef = 62
    · simp only [h62, ↓reduceIte, Option.some.injEq] at hfam_mem
      have hk := w.hfamK
      rw [← hfam_mem] at hk
      cases hk
    · simp only [h62, ↓reduceIte] at hfam_mem
      by_cases h61 : w.familyRef = 61
      · simp only [h61, ↓reduceIte, Option.some.injEq] at hfam_mem
        have hk := w.hfamK
        rw [← hfam_mem] at hk
        cases hk
      · simp only [h61, ↓reduceIte] at hfam_mem
        by_cases h60 : w.familyRef = 60
        · simp only [h60, ↓reduceIte, Option.some.injEq] at hfam_mem
          exact ⟨h60, hfam_mem.symm⟩
        · simp only [h60, ↓reduceIte] at hfam_mem
          cases hfam_mem
  have hnmin1 : w.nMinors = 1 := by
    have hidx := w.hrecIdx
    rw [hrec_eq.1, hfam_eq.1] at hidx
    omega
  have hctorIdx0 : w.ctorIdx = 0 := by
    have hidx := w.hctorIdx
    rw [hctor_eq.1, hfam_eq.1] at hidx
    omega
  have hnidx_sum : w.nparams + w.nindices = 0 := by
    have hi := w.hnidx
    rw [hfam_eq.2] at hi
    exact hi
  have hnpar0 : w.nparams = 0 := by omega
  have hnidx0 : w.nindices = 0 := by omega
  have hcpar_nil : w.ctorParams = [] := by
    have hcp := w.hctorParams
    rw [hnpar0] at hcp
    cases h : w.ctorParams with
    | nil => rfl
    | cons _ _ => rw [h] at hcp; cases hcp
  have hflen1 : w.fields.length = 1 := by
    have hp := w.hnpar
    rw [hnpar0, hctor_eq.2, Nat.zero_add] at hp
    exact hp
  have hdoms : w.ctorDoms = [.const 60 []] := by
    have hp := w.hpeel
    rw [hnpar0, hflen1, hctor_eq.2] at hp
    injection hp with hpair
    exact (Prod.mk.inj hpair).1.symm
  have hkinds_eq : w.kinds = [.directRec] := by
    have hk := w.hkinds
    rw [hfam_eq.1, hdoms, hnpar0] at hk
    exact (Option.some.inj hk).symm
  have hca_eq : w.ctorAfterParams = .pi (.const 60 []) (.const 60 []) := by
    have hca := w.hctorAfter
    rw [hnpar0, List.take_zero, hctor_eq.2] at hca
    exact (Option.some.inj hca).symm
  exact ⟨hrec_eq.1, hrec_eq.2, hctor_eq.1, hctor_eq.2, hfam_eq.1, hfam_eq.2,
    hnpar0, hnidx0, hnmin1, hctorIdx0, hcpar_nil, hkinds_eq, hca_eq, hflen1⟩

/-- Every `w : IotaWitness pinLoopEnvT` has a single field `t : Expr Nat`
    (`w.fields = [t]`), `ctorMajor w = .app (.const 61 w.lsC) t`, and
    `iotaRhsOf w = .app (.app w.minor t) (foldApps (.const 62 w.ls) (w.preMajor ++ [t]))`. -/
def pinLoopEnvT_iotaWitness_field_rhs (w : IotaWitness pinLoopEnvT) :
    Σ' t : Expr Nat,
      w.fields = [t] ∧
      ctorMajor w = .app (.const 61 w.lsC) t ∧
      iotaRhsOf w =
        .app (.app w.minor t) (foldApps (.const 62 w.ls) (w.preMajor ++ [t])) := by
  obtain ⟨hrec, _, hctor, _, _, _, hnpar, hnidx, hnmin, _, hcpar, hkinds, hca, hflen⟩ :=
    pinLoopEnvT_iotaWitness_shape w
  cases hfl : w.fields with
  | nil =>
      rw [hfl] at hflen
      cases hflen
  | cons t ts =>
      cases ts with
      | cons _ _ =>
          rw [hfl] at hflen
          cases hflen
      | nil =>
          refine ⟨t, rfl, ?_, ?_⟩
          · unfold ctorMajor ctorSpine
            rw [hctor, hcpar, hfl]
            rfl
          · have hpm_len : w.preMajor.length = 2 := by
              have hp := w.hpre
              omega
            have htake : recPrefix w.preMajor 0 1 = w.preMajor := by
              unfold recPrefix
              change w.preMajor.take 2 = w.preMajor
              rw [← hpm_len, List.take_length]
            have hfamIdx : familyIdx 0 (.const 60 []) = [] := rfl
            unfold iotaRhsOf
            rw [hrec, hnpar, hnmin, hfl, hkinds, hca]
            change foldApps w.minor
              [t, foldApps (.const 62 w.ls)
                (recPrefix w.preMajor 0 1 ++ familyIdx 0 (.const 60 []) ++ [t])] =
              .app (.app w.minor t) (foldApps (.const 62 w.ls) (w.preMajor ++ [t]))
            rw [htake, hfamIdx, List.append_nil]
            rfl

theorem instPrefix_app :
    (as : List (Expr Nat)) → (f a : Expr Nat) →
    instPrefix as (.app f a) = .app (instPrefix as f) (instPrefix as a)
  | [], _, _ => rfl
  | _ :: as, _, _ => instPrefix_app as _ _

theorem instPrefix_const :
    (as : List (Expr Nat)) → (r : Nat) → (ls : List Level) →
    instPrefix as (.const r ls) = .const r ls
  | [], _, _ => rfl
  | _ :: as, r, ls => instPrefix_const as r ls

/-- Complete structural characterization of every `wS : IotaWitnessS pinLoopEnvT`:
    `wS.recRef = 62`, `wS.ctorRef = 61`, `wS.familyRef = 60`, `wS.nparams = 0`,
    `wS.nindices = 0`, `wS.nMinors = 1`, `wS.ctorIdx = 0`, `wS.ctorParams = []`,
    `wS.fields.length = 1`, `wS.shapes = [.recursive 0]`, and
    `wS.schema = .app (.app (.bvar 1) (.bvar 0)) (.app (.app (.app (.const 62 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))`. -/
theorem pinLoopEnvT_iotaWitnessS_shape (wS : IotaWitnessS pinLoopEnvT) :
    wS.recRef = 62 ∧ wS.recMember = pinLoopRecT ∧
    wS.ctorRef = 61 ∧ wS.ctorMember = pinLoopMkT ∧
    wS.familyRef = 60 ∧ wS.famMember = pinLoopFamT ∧
    wS.nparams = 0 ∧ wS.nindices = 0 ∧ wS.nMinors = 1 ∧ wS.ctorIdx = 0 ∧
    wS.ctorParams = [] ∧ wS.fields.length = 1 ∧
    wS.shapes = [.recursive 0] ∧
    wS.schema =
      .app (.app (.bvar 1) (.bvar 0))
        (.app (.app (.app (.const 62 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0)) := by
  have hrec_mem : pinLoopEnvT.members wS.recRef = some wS.recMember := wS.hrec
  rw [pinLoopEnvT_mem] at hrec_mem
  have hrec_eq : wS.recRef = 62 ∧ wS.recMember = pinLoopRecT := by
    by_cases h62 : wS.recRef = 62
    · simp only [h62, ↓reduceIte, Option.some.injEq] at hrec_mem
      exact ⟨h62, hrec_mem.symm⟩
    · simp only [h62, ↓reduceIte] at hrec_mem
      by_cases h61 : wS.recRef = 61
      · simp only [h61, ↓reduceIte, Option.some.injEq] at hrec_mem
        have hk := wS.hrecK
        rw [← hrec_mem] at hk
        cases hk
      · simp only [h61, ↓reduceIte] at hrec_mem
        by_cases h60 : wS.recRef = 60
        · simp only [h60, ↓reduceIte, Option.some.injEq] at hrec_mem
          have hk := wS.hrecK
          rw [← hrec_mem] at hk
          cases hk
        · simp only [h60, ↓reduceIte] at hrec_mem
          cases hrec_mem
  have hctor_mem : pinLoopEnvT.members wS.ctorRef = some wS.ctorMember := wS.hctor
  rw [pinLoopEnvT_mem] at hctor_mem
  have hctor_eq : wS.ctorRef = 61 ∧ wS.ctorMember = pinLoopMkT := by
    by_cases h62 : wS.ctorRef = 62
    · simp only [h62, ↓reduceIte, Option.some.injEq] at hctor_mem
      have hk := wS.hctorK
      rw [← hctor_mem] at hk
      cases hk
    · simp only [h62, ↓reduceIte] at hctor_mem
      by_cases h61 : wS.ctorRef = 61
      · simp only [h61, ↓reduceIte, Option.some.injEq] at hctor_mem
        exact ⟨h61, hctor_mem.symm⟩
      · simp only [h61, ↓reduceIte] at hctor_mem
        by_cases h60 : wS.ctorRef = 60
        · simp only [h60, ↓reduceIte, Option.some.injEq] at hctor_mem
          have hk := wS.hctorK
          rw [← hctor_mem] at hk
          cases hk
        · simp only [h60, ↓reduceIte] at hctor_mem
          cases hctor_mem
  have hfam_mem : pinLoopEnvT.members wS.familyRef = some wS.famMember := wS.hfam
  rw [pinLoopEnvT_mem] at hfam_mem
  have hfam_eq : wS.familyRef = 60 ∧ wS.famMember = pinLoopFamT := by
    by_cases h62 : wS.familyRef = 62
    · simp only [h62, ↓reduceIte, Option.some.injEq] at hfam_mem
      have hk := wS.hfamK
      rw [← hfam_mem] at hk
      cases hk
    · simp only [h62, ↓reduceIte] at hfam_mem
      by_cases h61 : wS.familyRef = 61
      · simp only [h61, ↓reduceIte, Option.some.injEq] at hfam_mem
        have hk := wS.hfamK
        rw [← hfam_mem] at hk
        cases hk
      · simp only [h61, ↓reduceIte] at hfam_mem
        by_cases h60 : wS.familyRef = 60
        · simp only [h60, ↓reduceIte, Option.some.injEq] at hfam_mem
          exact ⟨h60, hfam_mem.symm⟩
        · simp only [h60, ↓reduceIte] at hfam_mem
          cases hfam_mem
  have hnmin1 : wS.nMinors = 1 := by
    have hidx := wS.hrecIdx
    rw [hrec_eq.1, hfam_eq.1] at hidx
    omega
  have hctorIdx0 : wS.ctorIdx = 0 := by
    have hidx := wS.hctorIdx
    rw [hctor_eq.1, hfam_eq.1] at hidx
    omega
  have hnidx_sum : wS.nparams + wS.nindices = 0 := by
    have hi := wS.hnidx
    rw [hfam_eq.2] at hi
    exact hi
  have hnpar0 : wS.nparams = 0 := by omega
  have hnidx0 : wS.nindices = 0 := by omega
  have hcpar_nil : wS.ctorParams = [] := by
    have hcp := wS.hctorParams
    rw [hnpar0] at hcp
    cases h : wS.ctorParams with
    | nil => rfl
    | cons _ _ => rw [h] at hcp; cases hcp
  have hflen1 : wS.fields.length = 1 := by
    have hp := wS.hnpar
    rw [hnpar0, hctor_eq.2, Nat.zero_add] at hp
    exact hp
  have hdoms : wS.ctorDoms = [.const 60 []] ∧ wS.ctorResult = .const 60 [] := by
    have hp := wS.hpeel
    rw [hnpar0, hflen1, hctor_eq.2] at hp
    injection hp with hpair
    exact ⟨(Prod.mk.inj hpair).1.symm, (Prod.mk.inj hpair).2.symm⟩
  have hsh_sch : wS.shapes = [.recursive 0] ∧
      wS.schema =
        .app (.app (.bvar 1) (.bvar 0))
          (.app (.app (.app (.const 62 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0)) := by
    have hsh := wS.hshapes
    have hsc := wS.hschema
    rw [hfam_eq.1, hfam_eq.2, hnpar0, hnidx0, hdoms.1] at hsh
    rw [hrec_eq.1, hrec_eq.2, hflen1, hnidx0, hnmin1, hctorIdx0, hnpar0,
      hdoms.1, hdoms.2] at hsc
    cases hf0 : wS.fuel with
    | zero =>
        rw [hf0] at hsh
        cases hsh
    | succ f1 =>
        cases hf1 : f1 with
        | zero =>
            rw [hf0, hf1] at hsh
            cases hsh
        | succ f2 =>
            cases hf2 : f2 with
            | zero =>
                rw [hf0, hf1, hf2] at hsh
                cases hsh
            | succ f3 =>
                rw [hf0, hf1, hf2] at hsh hsc
                have hsh_eq : wS.shapes = [.recursive 0] :=
                  (Option.some.inj hsh).symm
                rw [hsh_eq] at hsc
                exact ⟨hsh_eq, (Option.some.inj hsc).symm⟩
  exact ⟨hrec_eq.1, hrec_eq.2, hctor_eq.1, hctor_eq.2, hfam_eq.1, hfam_eq.2,
    hnpar0, hnidx0, hnmin1, hctorIdx0, hcpar_nil, hflen1, hsh_sch.1, hsh_sch.2⟩

/-- Full `DerivedIotaU` coherence on `pinLoopEnvT` across BOTH `.ofU` and
    `.ofUS` arms: for ANY `w : IotaWitness pinLoopEnvT` and ANY union derivation
    `hι : DerivedIotaU pinLoopEnvT (iotaLhsOf w) rhs`, `rhs = iotaRhsOf w`. -/
theorem pinLoopEnvT_derivedIotaU_rhs_eq_aux (w : IotaWitness pinLoopEnvT)
    {lhs rhs : Expr Nat}
    (hι : DerivedIotaU pinLoopEnvT lhs rhs)
    (heq : iotaLhsOf w = lhs) :
    rhs = iotaRhsOf w := by
  cases hι with
  | ofU wI =>
      have d : DerivedIota pinLoopEnvT (iotaLhsOf w) (iotaRhsOf wI) :=
        heq ▸ DerivedIota.of wI
      exact iotaDet d (.of w)
  | ofUS wS =>
      obtain ⟨hrec, hrecM, hctor, _, _, _, hnpar, hnidx, hnmin, hidx, hcpar, _, _, _⟩ :=
        pinLoopEnvT_iotaWitness_shape w
      let ⟨t, hfl, hcmaj, hrhs_w⟩ := pinLoopEnvT_iotaWitness_field_rhs w
      obtain ⟨hrecS, _, hctorS, _, _, _, hnparS, _, _, _, hcparS, hflenS, _, hschS⟩ :=
        pinLoopEnvT_iotaWitnessS_shape wS
      cases hflS : wS.fields with
      | nil => rw [hflS] at hflenS; cases hflenS
      | cons tS tsS =>
          cases tsS with
          | cons _ _ => rw [hflS] at hflenS; cases hflenS
          | nil =>
              have hs := congrArg appsSpine heq
              change appsSpine (recCall (.const w.recRef w.ls) w.preMajor (ctorMajor w)) =
                appsSpine (recCall (.const wS.recRef wS.ls) wS.preMajor
                  (foldApps (.const wS.ctorRef wS.lsC) (wS.ctorParams ++ wS.fields))) at hs
              rw [appsSpine_recCall, appsSpine_recCall] at hs
              injection hs with hhead hargs
              injection hhead with _ hls_eq
              obtain ⟨hpm_eq, hmaj_eq⟩ := list_snoc_inj hargs
              rw [hcmaj, hctorS, hcparS, hflS] at hmaj_eq
              change Expr.app (.const 61 w.lsC) t = Expr.app (.const 61 wS.lsC) tS at hmaj_eq
              have ht_eq : t = tS := (Expr.app.inj hmaj_eq).2
              have hls_len : w.ls.length = 1 := by
                have hl := w.hlsLen
                rw [hrecM] at hl
                exact hl
              cases hls_list : w.ls with
              | nil => rw [hls_list] at hls_len; cases hls_len
              | cons l ls_tail =>
                  cases ls_tail with
                  | cons _ _ => rw [hls_list] at hls_len; cases hls_len
                  | nil =>
                      have hpm_len : w.preMajor.length = 2 := by
                        have hp := w.hpre
                        omega
                      cases hpm_list : w.preMajor with
                      | nil => rw [hpm_list] at hpm_len; cases hpm_len
                      | cons M pm1 =>
                          cases pm1 with
                          | nil => rw [hpm_list] at hpm_len; cases hpm_len
                          | cons m pm2 =>
                              cases pm2 with
                              | cons _ _ => rw [hpm_list] at hpm_len; cases hpm_len
                              | nil =>
                                  have hmin_eq : w.minor = m := by
                                    have hm := w.hminor
                                    rw [hnpar, hidx, hpm_list] at hm
                                    exact (Option.some.inj hm).symm
                                  unfold iotaRhsOfS
                                  rw [← hpm_eq, ← hls_eq, hpm_list, hls_list, hflS, ← ht_eq, hschS]
                                  change instPrefix [M, m, t]
                                    (.app (.app (.bvar 1) (.bvar 0))
                                      (.app (.app (.app (.const 62 [l]) (.bvar 2)) (.bvar 1)) (.bvar 0))) =
                                    iotaRhsOf w
                                  simp only [instPrefix_app, instPrefix_const]
                                  have hb2 : instPrefix [M, m, t] (.bvar 2) = M :=
                                    instPrefix_bvar_lt (Nat.lt_succ_self 2) rfl
                                  have hb1 : instPrefix [M, m, t] (.bvar 1) = m :=
                                    instPrefix_bvar_lt (Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)) rfl
                                  have hb0 : instPrefix [M, m, t] (.bvar 0) = t :=
                                    instPrefix_bvar_lt (Nat.zero_lt_succ 2) rfl
                                  rw [hb2, hb1, hb0, hrhs_w, hmin_eq, hls_list, hpm_list]
                                  rfl

theorem pinLoopEnvT_derivedIotaU_rhs_eq (w : IotaWitness pinLoopEnvT)
    {rhs : Expr Nat}
    (hι : DerivedIotaU pinLoopEnvT (iotaLhsOf w) rhs) :
    rhs = iotaRhsOf w :=
  pinLoopEnvT_derivedIotaU_rhs_eq_aux w hι rfl

/-- Unconditional discharge of the `FIELDFUL_K` body-join obligation on the
    canonical witness region (`CanonicalEtaKWitness w₁`, `CanonicalEtaKWitness w₂`)
    over `pinLoopEnvT` across BOTH `.ofU` and `.ofUS` arms of `DerivedIotaU`. -/
def iotaStarKEta_self_join_of_canonical_pinLoopEnvT
    {n : Nat} {Γ : LCtx} {A B f rhs₁ rhs₂ : Expr Nat}
    {w₁ w₂ : IotaWitness pinLoopEnvT}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcan₁ : CanonicalEtaKWitness w₁)
    (hcan₂ : CanonicalEtaKWitness w₂)
    (hι₁ : DerivedIotaU pinLoopEnvT (iotaLhsOf w₁) rhs₁)
    (hι₂ : DerivedIotaU pinLoopEnvT (iotaLhsOf w₂) rhs₂)
    (hrhs₂ : HasTyT pinLoopEnvT n (.assumption A :: Γ) rhs₂ B) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT pinLoopEnvT n) pinLoopEnvT n (.assumption A :: Γ) rhs₁ rhs_join B ×'
      ParRedTStar (PEqLeafT pinLoopEnvT n) pinLoopEnvT n (.assumption A :: Γ) rhs₂ rhs_join B := by
  have heq : rhs₁ = rhs₂ := by
    rw [pinLoopEnvT_derivedIotaU_rhs_eq w₁ hι₁,
      pinLoopEnvT_derivedIotaU_rhs_eq w₂ hι₂]
    exact iotaStarKEta_self_rhs_eq_of_canonical happ₁ happ₂ hcan₁ hcan₂
  rw [heq]
  exact ⟨rhs₂, .refl (.assumption A :: Γ) rhs₂ B hrhs₂,
    .refl (.assumption A :: Γ) rhs₂ B hrhs₂⟩

/-- General `PEqT` step between ANY two `iotaStarKEta` right-hand sides on
    `pinLoopEnvT` (covering both `.ofU` and `.ofUS` via `pinLoopEnvT_derivedIotaU_rhs_eq`)
    at the same η-contracted source `f`, given that their single constructor
    field terms `t₁` (`w₁.fields = [t₁]`) and `t₂` (`w₂.fields = [t₂]`) both
    have type `Loop = .const 60 [] : Sort 0` in `Δ`. -/
def pinLoopEnvT_self_peq {n : Nat} {Δ : LCtx}
    {w₁ w₂ : IotaWitness pinLoopEnvT} {f rhs₁ rhs₂ t₁ t₂ : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hι₁ : DerivedIotaU pinLoopEnvT (iotaLhsOf w₁) rhs₁)
    (hι₂ : DerivedIotaU pinLoopEnvT (iotaLhsOf w₂) rhs₂)
    (hfl₁ : w₁.fields = [t₁])
    (hfl₂ : w₂.fields = [t₂])
    (ht₁ : HasTyT pinLoopEnvT n Δ t₁ (.const 60 []))
    (ht₂ : HasTyT pinLoopEnvT n Δ t₂ (.const 60 [])) :
    PEqT pinLoopEnvT n Δ rhs₁ rhs₂ := by
  obtain ⟨hrec_eq, hls_eq, hpm_eq⟩ := iotaStarKEta_same_rec_preMajor happ₁ happ₂
  obtain ⟨_, _, _, _, _, _, _, _, hn1, _, _, _, _, _⟩ := pinLoopEnvT_iotaWitness_shape w₁
  obtain ⟨_, _, _, _, _, _, _, _, hn2, _, _, _, _, _⟩ := pinLoopEnvT_iotaWitness_shape w₂
  have hm_eq : w₁.minor = w₂.minor :=
    headStepT_iotaStarK_minor_eq hrec_eq hpm_eq hn1 hn2
  let ⟨t₁', hfl₁', _, hrhs₁_form⟩ := pinLoopEnvT_iotaWitness_field_rhs w₁
  let ⟨t₂', hfl₂', _, hrhs₂_form⟩ := pinLoopEnvT_iotaWitness_field_rhs w₂
  have ht₁_eq : t₁' = t₁ := List.head_eq_of_cons_eq (hfl₁'.symm.trans hfl₁)
  have ht₂_eq : t₂' = t₂ := List.head_eq_of_cons_eq (hfl₂'.symm.trans hfl₂)
  have hrhs₁_eq : rhs₁ =
      .app (.app w₂.minor t₁) (foldApps (.const 62 w₂.ls) (w₂.preMajor ++ [t₁])) := by
    rw [pinLoopEnvT_derivedIotaU_rhs_eq w₁ hι₁, hrhs₁_form, ht₁_eq, hm_eq, hls_eq, hpm_eq]
  have hrhs₂_eq : rhs₂ =
      .app (.app w₂.minor t₂) (foldApps (.const 62 w₂.ls) (w₂.preMajor ++ [t₂])) := by
    rw [pinLoopEnvT_derivedIotaU_rhs_eq w₂ hι₂, hrhs₂_form, ht₂_eq]
  rw [hrhs₁_eq, hrhs₂_eq, foldApps_snoc, foldApps_snoc]
  have hLoop0 : HasTyT pinLoopEnvT n Δ (.const 60 []) (.sort .zero) :=
    .const Δ 60 [] (m := wLoopK.famMember) wLoopK.hfam rfl rfl
  have hp12 : PEqT pinLoopEnvT n Δ t₁ t₂ :=
    .proof Δ t₁ t₂ (.const 60 []) (.const 60 []) hLoop0 hLoop0 ht₁ ht₂
  exact .app Δ _ _ _ _
    (.app Δ _ _ _ _ (PEqT.refl w₂.minor) hp12)
    (.app Δ _ _ _ _
      (PEqT.refl (foldApps (.const 62 w₂.ls) w₂.preMajor))
      hp12)

/-- General 1-step `ParRedT.peq` body join for ANY two `iotaStarKEta` witnesses
    `w₁, w₂ : IotaWitness pinLoopEnvT` (covering both `.ofU` and `.ofUS` arms of
    `DerivedIotaU`) at the same source `f` once their constructor field terms
    `t₁, t₂` have type `Loop = .const 60 []`. -/
def pinLoopEnvT_self_typed_join {n : Nat} {Δ : LCtx} {B : Expr Nat}
    {w₁ w₂ : IotaWitness pinLoopEnvT} {f rhs₁ rhs₂ t₁ t₂ : Expr Nat}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hι₁ : DerivedIotaU pinLoopEnvT (iotaLhsOf w₁) rhs₁)
    (hι₂ : DerivedIotaU pinLoopEnvT (iotaLhsOf w₂) rhs₂)
    (hfl₁ : w₁.fields = [t₁])
    (hfl₂ : w₂.fields = [t₂])
    (ht₁ : HasTyT pinLoopEnvT n Δ t₁ (.const 60 []))
    (ht₂ : HasTyT pinLoopEnvT n Δ t₂ (.const 60 []))
    (hrhs₁ : HasTyT pinLoopEnvT n Δ rhs₁ B)
    (hrhs₂ : HasTyT pinLoopEnvT n Δ rhs₂ B) :
    ParRedTStar (PEqLeafT pinLoopEnvT n) pinLoopEnvT n Δ rhs₁ rhs₂ B ×'
    ParRedTStar (PEqLeafT pinLoopEnvT n) pinLoopEnvT n Δ rhs₂ rhs₂ B :=
  let hstep : ParRedT (PEqLeafT pinLoopEnvT n) pinLoopEnvT n Δ rhs₁ rhs₂ B :=
    .peq Δ rhs₁ rhs₂ B
      ⟨pinLoopEnvT_self_peq happ₁ happ₂ hι₁ hι₂ hfl₁ hfl₂ ht₁ ht₂, hrhs₁, hrhs₂⟩
  ⟨.tail hstep (.refl Δ rhs₂ B hrhs₂), .refl Δ rhs₂ B hrhs₂⟩

/-- Domain inversion for `mk = .const 61 lsC : Loop → Loop` in `pinLoopEnvT`:
    any well-typed constructor application `.app (.const 61 lsC) t : Tm` has
    `t : .const 60 []` (`Loop`). -/
def LoopMkDomainInv : Type :=
  ∀ {n : Nat} {Δ : LCtx} {lsC : List Level} {t Tm : Expr Nat},
    HasTyT pinLoopEnvT n Δ (.app (.const 61 lsC) t) Tm →
    HasTyT pinLoopEnvT n Δ t (.const 60 [])

/-- Full `FIELDFUL_K pinLoopEnvT` supplier across all `w₁, w₂ : IotaWitness pinLoopEnvT`
    and both `.ofU` and `.ofUS` arms of `DerivedIotaU` from `LoopMkDomainInv`. -/
def fieldfulK_pinLoopEnvT_of_mkDomInv
    (hMkInv : LoopMkDomainInv) :
    FIELDFUL_K pinLoopEnvT :=
  fun {_ _ _ _ _ _ _ _ rhs₂ w₁ w₂}
      happ₁ happ₂ _ _ _ hmk₁ _ _ hmk₂ _ hι₁ hι₂ hrhs₁ hrhs₂ =>
    let ⟨_, hfl₁, hcm₁, _⟩ := pinLoopEnvT_iotaWitness_field_rhs w₁
    let ⟨_, hfl₂, hcm₂, _⟩ := pinLoopEnvT_iotaWitness_field_rhs w₂
    let ht₁ := hMkInv (hcm₁ ▸ hmk₁)
    let ht₂ := hMkInv (hcm₂ ▸ hmk₂)
    let ⟨d1, d2⟩ :=
      pinLoopEnvT_self_typed_join happ₁ happ₂ hι₁ hι₂ hfl₁ hfl₂ ht₁ ht₂ hrhs₁ hrhs₂
    ⟨rhs₂, d1, d2⟩

/-- Second concrete `IotaWitness pinLoopEnvT` with `fields := [.bvar 3]`:
    in `pinLoopTwoVarsCtx = [.assumption (.const 60 []), .assumption loopMinorT, .assumption loopMotT, .assumption (.const 60 [])]`,
    both `.bvar 0` and `.bvar 3` have type `Loop = .const 60 []` while indices
    `0, 1, 2` match `pinLoopCtx` (`x : Loop`, `m : loopMinorT`, `M : loopMotT`),
    so BOTH `wLoopK` (`fields = [.bvar 0]`, canonical) and `wLoopK_bvar3`
    (`fields = [.bvar 3]`, non-canonical) have ALL `ParRedT.iotaStarKEta`
    typing premises concretely inhabited with zero open hypotheses. -/
def wLoopK_bvar3 : IotaWitness pinLoopEnvT :=
  { wLoopK with
    fields := [.bvar 3]
    hlen := rfl
    hnpar := rfl }

theorem not_wLoopK_bvar3_canonicalEtaKWitness :
    ¬ CanonicalEtaKWitness wLoopK_bvar3 := by
  intro ⟨_, h⟩
  rcases h with h0 | h1
  · revert h0; decide
  · revert h1; decide

theorem wLoopK_bvar3_rhs_differ :
    iotaRhsOf wLoopK ≠ iotaRhsOf wLoopK_bvar3 := by
  decide

/-- Outer context `[m : loopMinorT, M : loopMotT, y : Loop]` on `pinLoopEnvT`. -/
def pinLoopTwoVarsOuterCtx : LCtx :=
  [.assumption loopMinorT, .assumption loopMotT, .assumption (.const 60 [])]

/-- Body context `[x : Loop, m : loopMinorT, M : loopMotT, y : Loop] = .assumption (.const 60 []) :: pinLoopTwoVarsOuterCtx`. -/
def pinLoopTwoVarsCtx : LCtx :=
  .assumption (.const 60 []) :: pinLoopTwoVarsOuterCtx

def pinLoopTwoVars_bvar0TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 0) (.const 60 []) :=
  .bvar _ 0 _ rfl

def pinLoopTwoVars_bvar3TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 3) (.const 60 []) :=
  .bvar _ 3 _ rfl

def pinLoopTwoVars_famTyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.const 60 []) (.sort .zero) :=
  .const _ 60 [] pinLoopFamT rfl rfl rfl

def pinLoopTwoVars_outerFamTyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsOuterCtx (.const 60 []) (.sort .zero) :=
  .const _ 60 [] pinLoopFamT rfl rfl rfl

def pinLoopTwoVars_codSortTyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx loopMx (.sort (.param 0)) :=
  .app pinLoopTwoVarsCtx (.bvar 2) (.bvar 0) (.const 60 []) (.sort (.param 0))
    (.bvar _ 2 loopMotT rfl) pinLoopTwoVars_bvar0TyT

def pinLoopTwoVars_mk0TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (ctorMajor wLoopK) (.const 60 []) :=
  .app pinLoopTwoVarsCtx (.const 61 []) (.bvar 0) (.const 60 []) (.const 60 [])
    (.const _ 61 [] pinLoopMkT rfl rfl rfl) pinLoopTwoVars_bvar0TyT

def pinLoopTwoVars_mk3TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (ctorMajor wLoopK_bvar3) (.const 60 []) :=
  .app pinLoopTwoVarsCtx (.const 61 []) (.bvar 3) (.const 60 []) (.const 60 [])
    (.const _ 61 [] pinLoopMkT rfl rfl rfl) pinLoopTwoVars_bvar3TyT

def pinLoopTwoVars_recPrefixTyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsOuterCtx recPrefixTerm
      (.pi (.const 60 []) loopMx) := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopTwoVarsOuterCtx (.bvar 1) loopMotT :=
    .bvar _ 1 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsOuterCtx (.bvar 0)
      (.pi (.const 60 [])
        (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (.app (.const 61 []) (.bvar 1))))) :=
    .bvar _ 0 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsOuterCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsOuterCtx
      (.app pinLoopRecHead (.bvar 1))
      (.pi (.pi (.const 60 [])
        (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (.app (.const 61 []) (.bvar 1)))))
        (.pi (.const 60 []) (.app (.bvar 3) (.bvar 0)))) :=
    .app _ _ _ _ _ h0 hM
  exact .app _ _ _ _ _ h1 hm

def pinLoopTwoVars_lhsTyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (recCall (.const wLoopK.recRef wLoopK.ls) wLoopK.preMajor (.bvar 0))
      loopMx := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app pinLoopRecHead (.bvar 2)) (.pi loopMinorAt loopCodM) :=
    .app _ _ _ _ _ h0 hM
  have h2 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    .app _ _ _ _ _ h1 hm
  exact .app _ _ _ _ _ h2 pinLoopTwoVars_bvar0TyT

def pinLoopTwoVars_lhs3TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (recCall (.const wLoopK.recRef wLoopK.ls) wLoopK.preMajor (.bvar 3))
      (.app (.bvar 2) (.bvar 3)) := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app pinLoopRecHead (.bvar 2)) (.pi loopMinorAt loopCodM) :=
    .app _ _ _ _ _ h0 hM
  have h2 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    .app _ _ _ _ _ h1 hm
  exact .app _ _ _ _ _ h2 pinLoopTwoVars_bvar3TyT

def pinLoopTwoVars_indexConv0 :
    ConvT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app (.bvar 2) (ctorMajor wLoopK)) loopMx (.sort (.param 0)) :=
  .app pinLoopTwoVarsCtx (.bvar 2) (.bvar 2) (ctorMajor wLoopK) (.bvar 0)
    (.const 60 []) (.sort (.param 0))
    (.refl _ _ _ (.bvar _ 2 _ rfl))
    (.irr _ _ _ _ pinLoopTwoVars_famTyT pinLoopTwoVars_mk0TyT pinLoopTwoVars_bvar0TyT)

def pinLoopTwoVars_indexConv3 :
    ConvT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app (.bvar 2) (ctorMajor wLoopK_bvar3)) loopMx (.sort (.param 0)) :=
  .app pinLoopTwoVarsCtx (.bvar 2) (.bvar 2) (ctorMajor wLoopK_bvar3) (.bvar 0)
    (.const 60 []) (.sort (.param 0))
    (.refl _ _ _ (.bvar _ 2 _ rfl))
    (.irr _ _ _ _ pinLoopTwoVars_famTyT pinLoopTwoVars_mk3TyT pinLoopTwoVars_bvar0TyT)

def pinLoopTwoVars_lhsI0TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaLhsOf wLoopK) loopMx := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app pinLoopRecHead (.bvar 2)) (.pi loopMinorAt loopCodM) :=
    .app _ _ _ _ _ h0 hM
  have h2 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    .app _ _ _ _ _ h1 hm
  have h3 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaLhsOf wLoopK)
      (.app (.bvar 2) (ctorMajor wLoopK)) :=
    .app _ _ _ _ _ h2 pinLoopTwoVars_mk0TyT
  exact .conv _ _ _ _ _ h3 pinLoopTwoVars_indexConv0

def pinLoopTwoVars_lhsI3TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaLhsOf wLoopK_bvar3) loopMx := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app pinLoopRecHead (.bvar 2)) (.pi loopMinorAt loopCodM) :=
    .app _ _ _ _ _ h0 hM
  have h2 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    .app _ _ _ _ _ h1 hm
  have h3 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaLhsOf wLoopK_bvar3)
      (.app (.bvar 2) (ctorMajor wLoopK_bvar3)) :=
    .app _ _ _ _ _ h2 pinLoopTwoVars_mk3TyT
  exact .conv _ _ _ _ _ h3 pinLoopTwoVars_indexConv3

def pinLoopTwoVars_rhs0TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaRhsOf wLoopK) loopMx := by
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h4 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.app (.bvar 1) (.bvar 0))
      loopMxTy :=
    .app _ _ _ _ _ hm pinLoopTwoVars_bvar0TyT
  have h5 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaRhsOf wLoopK)
      (.app (.bvar 2) (ctorMajor wLoopK)) :=
    .app _ _ _ _ _ h4 pinLoopTwoVars_lhsTyT
  exact .conv _ _ _ _ _ h5 pinLoopTwoVars_indexConv0

def pinLoopTwoVars_rhs3TyT :
    HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaRhsOf wLoopK_bvar3) loopMx := by
  have hm : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h4 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (.app (.bvar 1) (.bvar 3))
      (.pi (.app (.bvar 2) (.bvar 3))
        (.app (.bvar 3) (.app (.const 61 []) (.bvar 4)))) :=
    .app _ _ _ _ _ hm pinLoopTwoVars_bvar3TyT
  have h5 : HasTyT pinLoopEnvT 1 pinLoopTwoVarsCtx (iotaRhsOf wLoopK_bvar3)
      (.app (.bvar 2) (ctorMajor wLoopK_bvar3)) :=
    .app _ _ _ _ _ h4 pinLoopTwoVars_lhs3TyT
  exact .conv _ _ _ _ _ h5 pinLoopTwoVars_indexConv3

/-- Concrete `ParRedT.iotaStarKEta` step on `pinLoopEnvT` using the canonical
    witness `wLoopK` (`fields = [.bvar 0]`). -/
def pinParRedT_iotaStarKEta_loop0 :
    ParRedT (PEqLeafT pinLoopEnvT 1) pinLoopEnvT 1 pinLoopTwoVarsOuterCtx
      recPrefixTerm (.lam (.const 60 []) (iotaRhsOf wLoopK))
      (.pi (.const 60 []) loopMx) :=
  .iotaStarKEta pinLoopTwoVarsOuterCtx wLoopK recPrefixTerm
    (.const 60 []) loopMx (.const 60 []) (iotaRhsOf wLoopK) .zero .zero True
    rfl pinLoopTwoVars_outerFamTyT pinLoopTwoVars_recPrefixTyT rfl
    (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    pinLoopTwoVars_bvar0TyT pinLoopTwoVars_mk0TyT pinLoopTwoVars_famTyT
    (.ofU wLoopK) pinLoopTwoVars_lhsI0TyT pinLoopTwoVars_lhsTyT
    pinLoopTwoVars_rhs0TyT

/-- Concrete `ParRedT.iotaStarKEta` step on `pinLoopEnvT` at the EXACT same
    source `recPrefixTerm` using the non-canonical witness `wLoopK_bvar3`
    (`fields = [.bvar 3]`), producing the distinct body `iotaRhsOf wLoopK_bvar3`. -/
def pinParRedT_iotaStarKEta_loop3 :
    ParRedT (PEqLeafT pinLoopEnvT 1) pinLoopEnvT 1 pinLoopTwoVarsOuterCtx
      recPrefixTerm (.lam (.const 60 []) (iotaRhsOf wLoopK_bvar3))
      (.pi (.const 60 []) loopMx) :=
  .iotaStarKEta pinLoopTwoVarsOuterCtx wLoopK_bvar3 recPrefixTerm
    (.const 60 []) loopMx (.const 60 []) (iotaRhsOf wLoopK_bvar3) .zero .zero True
    rfl pinLoopTwoVars_outerFamTyT pinLoopTwoVars_recPrefixTyT rfl
    (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    pinLoopTwoVars_bvar0TyT pinLoopTwoVars_mk3TyT pinLoopTwoVars_famTyT
    (.ofU wLoopK_bvar3) pinLoopTwoVars_lhsI3TyT pinLoopTwoVars_lhsTyT
    pinLoopTwoVars_rhs3TyT

/-- Unconditional 1-step `ParRedTStar` body join in `pinLoopTwoVarsCtx` between
    `iotaRhsOf wLoopK` and `iotaRhsOf wLoopK_bvar3` with all typing premises
    concretely inhabited and zero open hypotheses. -/
def wLoopK_bvar3_concrete_body_join :
    ParRedTStar (PEqLeafT pinLoopEnvT 1) pinLoopEnvT 1 pinLoopTwoVarsCtx
      (iotaRhsOf wLoopK) (iotaRhsOf wLoopK_bvar3) loopMx ×'
    ParRedTStar (PEqLeafT pinLoopEnvT 1) pinLoopEnvT 1 pinLoopTwoVarsCtx
      (iotaRhsOf wLoopK_bvar3) (iotaRhsOf wLoopK_bvar3) loopMx :=
  pinLoopEnvT_self_typed_join (w₁ := wLoopK) (w₂ := wLoopK_bvar3) (f := recPrefixTerm)
    rfl rfl (.ofU wLoopK) (.ofU wLoopK_bvar3) rfl rfl
    pinLoopTwoVars_bvar0TyT pinLoopTwoVars_bvar3TyT
    pinLoopTwoVars_rhs0TyT pinLoopTwoVars_rhs3TyT

/-- Unconditional 1-step `ParRedTStar` λ-join in `pinLoopTwoVarsOuterCtx`
    between the targets `.lam (.const 60 []) (iotaRhsOf wLoopK)` and
    `.lam (.const 60 []) (iotaRhsOf wLoopK_bvar3)` of `pinParRedT_iotaStarKEta_loop0`
    and `pinParRedT_iotaStarKEta_loop3`, with zero open hypotheses. -/
def wLoopK_bvar3_concrete_lam_join :
    ParRedTStar (PEqLeafT pinLoopEnvT 1) pinLoopEnvT 1 pinLoopTwoVarsOuterCtx
      (.lam (.const 60 []) (iotaRhsOf wLoopK))
      (.lam (.const 60 []) (iotaRhsOf wLoopK_bvar3))
      (.pi (.const 60 []) loopMx) ×'
    ParRedTStar (PEqLeafT pinLoopEnvT 1) pinLoopEnvT 1 pinLoopTwoVarsOuterCtx
      (.lam (.const 60 []) (iotaRhsOf wLoopK_bvar3))
      (.lam (.const 60 []) (iotaRhsOf wLoopK_bvar3))
      (.pi (.const 60 []) loopMx) :=
  ⟨parRedTStar_lam_body pinLoopTwoVars_outerFamTyT pinLoopTwoVars_codSortTyT
      (.refl pinLoopTwoVarsOuterCtx (.pi (.const 60 []) loopMx))
      wLoopK_bvar3_concrete_body_join.1,
    parRedTStar_lam_body pinLoopTwoVars_outerFamTyT pinLoopTwoVars_codSortTyT
      (.refl pinLoopTwoVarsOuterCtx (.pi (.const 60 []) loopMx))
      wLoopK_bvar3_concrete_body_join.2⟩



/-- Precise `Type`-valued witness-transport contract for the general
    `eta` × `lam (iotaStarK)` peak over the full `DerivedIotaU` union
    (`hι : DerivedIotaU E (iotaLhsOf w) rhs`):
    - `onSpine`: transports `rhs` across a structural pre-major spine step
      `f ⇉ f' = foldApps (.const w.recRef ls') xs'` to the stepped witness
      `w' = replacePreMajorWitness w ls' (xs'.map (lift 0 1)) minor' hls hlenP hmin'`,
      producing the stepped union reduct `rhs'`, its union derivation
      `DerivedIotaU E (iotaLhsOf w') rhs'`, and the body step
      `ParRedT (PEqLeafT E n) E n (.assumption A :: Γ) rhs rhs' B`;
    - `onEtaK`: joins `rhs_eta` (from a competing root `ParRedT.iotaStarKEta`
      step at the same source `f` with `hι_eta : DerivedIotaU E (iotaLhsOf w_eta) rhs_eta`
      and `hrhs_eta_AB : HasTyT E n (.assumption A :: Γ) rhs_eta B`) with `rhs`
      via `ParRedTStar` at `B` in `.assumption A :: Γ` (matching `FIELDFUL_K E`).
    Constructed for any field-free singleton (`w.nMinors = 1`, `w.fields = []`)
    across BOTH `.ofU` and `.ofUS` arms of `DerivedIotaU` from `MinorStepLift`
    via `fieldfulKPeakContract_of_fields_nil` (`onEtaK` requires zero extra
    premises; `onSpine` uses `MinorStepLift`), and concretely inhabited at the
    positive A-2 peak under sort uniqueness alone by
    `positive_fieldfulKPeakContract_of_sortUniq` (consumed in
    `positive_full_eta_lamK_joins_via_contract_of_sortUniq`). -/
structure FieldfulKPeakContract (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A B : Expr Nat) (w : IotaWitness E) {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (rhs : Expr Nat) (_hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (_hrhs : HasTyT E n (.assumption A :: Γ) rhs B) : Type where
  onSpine :
    ∀ {ls' : List Level} {xs' : List (Expr Nat)} {minor' : Expr Nat}
      (hls : eqNList w.ls ls')
      (_hargs : RecArgsStep E n Γ (appsSpine f).2 xs')
      (hlenP : (xs'.map (lift 0 1)).length = w.preMajor.length)
      (hmin' : (xs'.map (lift 0 1))[w.nparams + 1 + w.ctorIdx]? = some minor'),
      let w' := replacePreMajorWitness w ls' (xs'.map (lift 0 1)) minor' hls hlenP hmin'
      Σ' rhs' : Expr Nat,
        DerivedIotaU E (iotaLhsOf w') rhs' ×'
        ParRedT (PEqLeafT E n) E n (.assumption A :: Γ) rhs rhs' B
  onEtaK :
    ∀ {w_eta : IotaWitness E} {rhs_eta : Expr Nat},
      recCall (.const w_eta.recRef w_eta.ls) w_eta.preMajor (.bvar 0) =
        .app (lift 0 1 f) (.bvar 0) →
      DerivedIotaU E (iotaLhsOf w_eta) rhs_eta →
      HasTyT E n (.assumption A :: Γ) rhs_eta B →
      Σ' rhs_join : Expr Nat,
        ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs_eta rhs_join B ×'
        ParRedTStar (PEqLeafT E n) E n (.assumption A :: Γ) rhs rhs_join B

/-- Unconditional discharge of `FieldfulKPeakContract` for any field-free
    singleton recursor (`w.nMinors = 1`, `w.fields = []`, covering `Eq` and
    `HEq`) across BOTH `.ofU` and `.ofUS` arms of `DerivedIotaU`. -/
def fieldfulKPeakContract_of_fields_nil {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} (w : IotaWitness E) {f rhs : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1) :
    FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs where
  onSpine := fun {ls' xs' minor'} hls hargs hlenP hmin' =>
    let mp := minorPreImage w happ
    let m := mp.1
    have hm_get : (appsSpine f).2[w.nparams + 1 + w.ctorIdx]? = some m := mp.2.1
    have hm_eq : w.minor = lift 0 1 m := mp.2.2
    let ⟨m', hm'_get, hm_step⟩ :=
      recArgsStep_get hargs (w.nparams + 1 + w.ctorIdx) hm_get
    have hmin'_eq : minor' = lift 0 1 m' := by
      have hmap := list_getElem?_map_of_some (lift 0 1) xs' (w.nparams + 1 + w.ctorIdx) hm'_get
      exact Option.some.inj (hmin'.symm.trans hmap)
    let w' := replacePreMajorWitness w ls' (xs'.map (lift 0 1)) minor' hls hlenP hmin'
    have hrhs_eq : rhs = lift 0 1 m :=
      (derivedIotaU_rhs_eq_of_fields_nil w hf_nil hι).trans hm_eq
    have hrhs'_eq : iotaRhsOf w' = lift 0 1 m' :=
      (headStepT_iotaRhs_fields_nil w' hf_nil).trans hmin'_eq
    let hm_par : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ)
        (lift 0 1 m) (lift 0 1 m') B :=
      hMinorLift hm_step
    let hrhs_step : ParRedT (PEqLeafT E n) E n (.assumption A :: Γ)
        rhs (iotaRhsOf w') B := by
      rw [hrhs_eq, hrhs'_eq]
      exact hm_par
    ⟨iotaRhsOf w', .ofU w', hrhs_step⟩
  onEtaK := fun happ_eta hι_eta _ =>
    iotaStarKEta_self_join_of_fields_nil happ_eta happ hnmin hf_nil hι_eta hι hrhs

/-- Domain and codomain conversion extracted from a real `.conv` wrapper
    `TyConvT E n Γ (.pi A_eta B_eta) (.pi A B)` around a root
    `ParRedT.iotaStarKEta` step (kept sealed; see `RootEtaKWrapperAlign` for the
    step-specific alignment that avoids any codomain sort typing `v_eta`). -/
def WrappedPiDomainConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A B : Expr Nat) : Type :=
  ∀ {A_eta B_eta : Expr Nat} {u_eta : Level},
    HasTyT E n Γ A_eta (.sort u_eta) →
    TyConvT E n Γ (.pi A_eta B_eta) (.pi A B) →
    Σ' v_eta : Level,
      ConvT E n Γ A_eta A (.sort u_eta) ×'
      TyConvT E n (.assumption A_eta :: Γ) B_eta B ×'
      HasTyT E n (.assumption A_eta :: Γ) B_eta (.sort v_eta)

/-- Step-specific wrapper alignment for a parallel step
    `h : ParRedT (PEqLeafT E n) E n Γ a b T` against outer Π-type `.pi A B`:
    - for any structural step (`refl`, `consts`, `app` including nested
      `iotaStarKEta`, `peq`, or `.conv` wrapping a structural step), it is `PUnit`;
    - for any root `ParRedT.iotaStarKEta` step (unwrapped OR wrapped in any
      number of `ParRedT.conv` steps) whose inner Π-type `.pi A_eta B_eta`
      has `A_eta = A` and `B_eta = B`, it is `PUnit` (so `TyConvT.refl` and all
      Π-preserving `.conv` wrappers require no external conversion callback);
    - for a `.conv`-wrapped root `ParRedT.iotaStarKEta` step with `A_eta = A`
      and `B_eta ≠ B`, it is `TyConvT E n (.assumption A_eta :: Γ) B_eta B`;
    - for a `.conv`-wrapped root `ParRedT.iotaStarKEta` step with `A_eta ≠ A`,
      it is `ConvT E n Γ A_eta A (.sort u_eta) ×' TyConvT E n (.assumption A_eta :: Γ) B_eta B`
      (requiring NO codomain sort `v_eta` or `HasTyT E n (.assumption A_eta :: Γ) B_eta (.sort v_eta)`,
      because the outer peak's `hB : HasTyT E n (.assumption A :: Γ) B (.sort v)`
      transports to `.assumption A_eta :: Γ`). -/
def RootEtaKWrapperAlign {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} (A B : Expr Nat) {T : Expr Nat} :
    ParRedT (PEqLeafT E n) E n Γ a b T → Type
  | .iotaStarKEta _ _ _ A_eta B_eta _ _ u_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      if A_eta = A then
        if B_eta = B then PUnit
        else TyConvT E n (.assumption A_eta :: Γ) B_eta B
      else
        ConvT E n Γ A_eta A (.sort u_eta) ×'
        TyConvT E n (.assumption A_eta :: Γ) B_eta B
  | .conv _ _ _ _ _ hinner _ =>
      RootEtaKWrapperAlign A B hinner
  | _ => PUnit

/-- Predicate stating that if `h` is a (possibly `.conv`-wrapped) root
    `ParRedT.iotaStarKEta` step, its inner Π-type `.pi A_eta B_eta` has
    `A_eta = A ∧ B_eta = B`. Holds definitionally (`True` or `⟨rfl, rfl⟩`) for
    all structural steps, all unwrapped root `iotaStarKEta` steps at `.pi A B`,
    and all Π-preserving `.conv` wrappers around root `iotaStarKEta` steps
    (including `TyConvT.refl`). -/
def SameRootEtaKPi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} (A B : Expr Nat) {T : Expr Nat} :
    ParRedT (PEqLeafT E n) E n Γ a b T → Prop
  | .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      A_eta = A ∧ B_eta = B
  | .conv _ _ _ _ _ hinner _ =>
      SameRootEtaKPi A B hinner
  | _ => True

/-- Unconditional constructor for `RootEtaKWrapperAlign A B h` whenever
    `SameRootEtaKPi A B h` holds (discharged automatically for all structural
    steps, unwrapped root `iotaStarKEta` steps, and reflexive/Π-preserving
    `.conv` wrappers). -/
def rootEtaKWrapperAlign_of_same {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} {A B T : Expr Nat} :
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (hsame : SameRootEtaKPi A B h := by first | exact ⟨rfl, rfl⟩ | rfl | trivial) →
    RootEtaKWrapperAlign A B h
  | .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, hsame => by
      change A_eta = A ∧ B_eta = B at hsame
      dsimp [RootEtaKWrapperAlign]
      rw [if_pos hsame.1, if_pos hsame.2]
      exact PUnit.unit
  | .conv _ _ _ _ _ hinner _, hsame =>
      rootEtaKWrapperAlign_of_same hinner hsame
  | .refl .., _ | .sortEq .., _ | .consts .., _ | .bvarZeta .., _
  | .delta .., _ | .app .., _ | .beta .., _ | .lam .., _ | .pi .., _
  | .letE .., _ | .zeta .., _ | .iotaSpine .., _ | .lit .., _
  | .eta .., _ | .iotaStarK .., _ | .peq .., _ => PUnit.unit

theorem sameRootEtaKPi_of_not_isRootEtaKStep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    ¬ IsRootEtaKStep h → SameRootEtaKPi A B h
  | _, _, _, .iotaStarKEta .., hno => False.elim (hno True.intro)
  | _, _, _, .conv _ _ _ _ _ hinner _, hno =>
      sameRootEtaKPi_of_not_isRootEtaKStep A B hinner hno
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => True.intro

theorem sameRootEtaKPi_of_noWrappedRootEtaK_aux {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A B : Expr Nat) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    T = .pi A B → NoWrappedRootEtaK h → SameRootEtaKPi A B h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, hT, _ => by
      injection hT with hA hB
      exact ⟨hA, hB⟩
  | _, _, _, .conv _ _ _ _ _ hinner _, _, hnoWrap =>
      sameRootEtaKPi_of_not_isRootEtaKStep A B hinner hnoWrap
  | _, _, _, .refl .., _, _ | _, _, _, .sortEq .., _, _ | _, _, _, .consts .., _, _
  | _, _, _, .bvarZeta .., _, _ | _, _, _, .delta .., _, _ | _, _, _, .app .., _, _
  | _, _, _, .beta .., _, _ | _, _, _, .lam .., _, _ | _, _, _, .pi .., _, _
  | _, _, _, .letE .., _, _ | _, _, _, .zeta .., _, _ | _, _, _, .iotaSpine .., _, _
  | _, _, _, .lit .., _, _ | _, _, _, .eta .., _, _ | _, _, _, .iotaStarK .., _, _
  | _, _, _, .peq .., _, _ => True.intro

theorem sameRootEtaKPi_of_noWrappedRootEtaK {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A B : Expr Nat} (h : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B))
    (hnoWrap : NoWrappedRootEtaK h) : SameRootEtaKPi A B h :=
  sameRootEtaKPi_of_noWrappedRootEtaK_aux A B h rfl hnoWrap

/-- Extract `A_eta = A ∧ HasTyT E n (.assumption A :: Γ) rhs_eta B` or
    `ConvT E n Γ A_eta A (.sort u_eta) ×' TyConvT E n (.assumption A_eta :: Γ) B_eta B`
    when `parRedT_rec_preMajor_classify` enters the `.etaK` branch. -/
def classify_etaK_align
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {ls₀ : List Level}
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef ls₀ w.preMajor.length)
    {A B : Expr Nat} :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    RootEtaKWrapperAlign A B h →
    ∀ {ls : List Level} {xs : List (Expr Nat)}
      (heq : a = foldApps (.const w.recRef ls) xs)
      (hk : xs.length = w.preMajor.length)
      (hls : eqNList ls ls₀),
      match parRedT_rec_preMajor_classify w hNoPrf h heq hk hls with
      | .spine .. => PUnit
      | .etaK _ A_eta B_eta _ rhs_eta u_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          (PLift (A_eta = A) ×' HasTyT E n (.assumption A :: Γ) rhs_eta B) ⊕
          (ConvT E n Γ A_eta A (.sort u_eta) ×'
            TyConvT E n (.assumption A_eta :: Γ) B_eta B)
  | _, _, _, .refl .., _, _, _, _, _, _ => PUnit.unit
  | _, _, _, .consts .., _, _, [], _, _, _ => PUnit.unit
  | _, _, _, .consts .., _, ls, x :: xs, heq, _, _ =>
      let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const w.recRef ls) x xs
      False.elim (by rw [happ] at heq; exact nomatch heq)
  | _, _, _, .delta _ _ _ _ _ _ hres _ htr _ _ _ _, _, _, _, heq, _, _ =>
      False.elim (witness_rec_not_delta w hres htr heq)
  | _, _, _, .app .., _, _, [], heq, _, _ => nomatch heq
  | _, _, _, .app .., _, _, _ :: _, _, _, _ => PUnit.unit
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, xs, heq, hk, hls =>
      match parRedT_rec_preMajor_classify w hNoPrf hstep heq hk hls with
      | .spine _ xs' hstep_eq _ hargs =>
          have hlen' : xs'.length ≤ w.preMajor.length := by
            rw [recArgsStep_length hargs, hk]
            exact Nat.le_refl _
          False.elim (short_witness_not_derivedIotaU w hlen' hI hstep_eq)
      | .etaK _ _ _ _ _ _ _ _ hstep_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          False.elim (derivedIotaU_lam_source_false hI hstep_eq)
  | _, _, _, .iotaStarK _ wK major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, _, heq, hk, _ =>
      False.elim (short_witness_not_K_source w (Nat.le_of_eq hk) wK major heq)
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ rhs_eta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrhs_eta,
      hAlign, _, _, _, _, _ => by
      dsimp [parRedT_rec_preMajor_classify, RootEtaKWrapperAlign] at hAlign ⊢
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq] at hAlign
        by_cases hB_eq : B_eta = B
        · exact .inl ⟨⟨hA_eq⟩, hA_eq ▸ hB_eq ▸ hrhs_eta⟩
        · rw [if_neg hB_eq] at hAlign
          exact .inl ⟨⟨hA_eq⟩, hA_eq ▸ hasTyT_of_tyConvT hrhs_eta hAlign⟩
      · rw [if_neg hA_eq] at hAlign
        exact .inr hAlign
  | _, _, _, .peq .., _, _, _, _, _, _ => PUnit.unit
  | _, _, _, .conv _ _ _ _ _ hinner _, hAlign, _, _, heq, hk, hls => by
      have ih := classify_etaK_align w hNoPrf hinner hAlign heq hk hls
      cases hcl : parRedT_rec_preMajor_classify w hNoPrf hinner heq hk hls with
      | spine _ _ _ _ _ =>
          simp only [parRedT_rec_preMajor_classify, hcl]
          exact PUnit.unit
      | etaK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          simp only [parRedT_rec_preMajor_classify, hcl]
          rw [hcl] at ih
          exact ih
  | _, _, _, .sortEq .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .bvarZeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .beta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lam .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .pi .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .letE .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .zeta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .lit .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq
  | _, _, _, .eta .., _, _, _, heq, _, _ =>
      nomatch appsSpine_fst_of_eq_foldApps_const heq

/-- Adapter from `WrappedPiDomainConv E n Γ A B` to `RootEtaKWrapperAlign A B h`
    for any `h : ParRedT (PEqLeafT E n) E n Γ a b T` with `hc_outer : TyConvT E n Γ T (.pi A B)`. -/
def rootEtaKWrapperAlign_of_wrappedPiDomainConv_aux
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (hAnnot : WrappedPiDomainConv E n Γ A B) :
    {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    TyConvT E n Γ T (.pi A B) →
    RootEtaKWrapperAlign A B h
  | _, _, _, .iotaStarKEta _ _ _ A_eta B_eta _ _ _ _ _ _ hA_eta _ _ _ _ _ _ _ _ _ _ _, hc_outer => by
      dsimp [RootEtaKWrapperAlign]
      let ⟨_, hcA_eta, hcB_eta, _⟩ := hAnnot hA_eta hc_outer
      by_cases hA_eq : A_eta = A
      · rw [if_pos hA_eq]
        by_cases hB_eq : B_eta = B
        · rw [if_pos hB_eq]; exact PUnit.unit
        · rw [if_neg hB_eq]; exact hcB_eta
      · rw [if_neg hA_eq]
        exact ⟨hcA_eta, hcB_eta⟩
  | _, _, _, .conv _ _ _ T₁ T₂ hinner hc_wrap, hc_outer =>
      rootEtaKWrapperAlign_of_wrappedPiDomainConv_aux hAnnot hinner
        (.trans Γ T₁ T₂ (.pi A B) hc_wrap hc_outer)
  | _, _, _, .refl .., _ | _, _, _, .sortEq .., _ | _, _, _, .consts .., _
  | _, _, _, .bvarZeta .., _ | _, _, _, .delta .., _ | _, _, _, .app .., _
  | _, _, _, .beta .., _ | _, _, _, .lam .., _ | _, _, _, .pi .., _
  | _, _, _, .letE .., _ | _, _, _, .zeta .., _ | _, _, _, .iotaSpine .., _
  | _, _, _, .lit .., _ | _, _, _, .eta .., _ | _, _, _, .iotaStarK .., _
  | _, _, _, .peq .., _ => PUnit.unit

def rootEtaKWrapperAlign_of_wrappedPiDomainConv
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A B : Expr Nat}
    (hAnnot : WrappedPiDomainConv E n Γ A B)
    (h : ParRedT (PEqLeafT E n) E n Γ a b (.pi A B)) :
    RootEtaKWrapperAlign A B h :=
  rootEtaKWrapperAlign_of_wrappedPiDomainConv_aux hAnnot h (.refl Γ (.pi A B))

/-- Full unrestricted `ParRedTStar` join handler for the general
    `eta` × `lam (iotaStarK)` peak consuming `FieldfulKPeakContract` and
    dispatching on `parRedT_rec_preMajor_classify` across all 18 `ParRedT`
    constructors WITHOUT `NoEtaKStep hf_step` or `NoWrappedRootEtaK hf_step`:
    - Branch `.spine`: constructs `w'` from the stepped spine, invokes
      `hContract.onSpine` to obtain `rhs'`, `hι'`, and `hrhs_step`, and joins
      `f' ⇉ .lam A rhs' ⇉ .lam A' rhs'` with `.lam A' rhs ⇉ .lam A' rhs'`.
    - Branch `.etaK`: invokes `hContract.onEtaK` to join `rhs_eta` and `rhs`
      at `rhs_join` via `ParRedTStar`, then lifts the body join under
      `ParRedT.lam` to `.lam A' rhs_join` (handling both `A_eta = A` wrappers
      and distinct-domain `A_eta ≠ A` wrappers via `RootEtaKWrapperAlign`,
      without requesting any codomain sort typing `v_eta`). -/
def eta_lamK_full_star_data_of_contract
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hContract : FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs)
    (hAlign : RootEtaKWrapperAlign A B hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_same _ (by first | exact ⟨rfl, rfl⟩ | rfl | trivial)) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n Γ f' (.lam A' rhs_join) T ×'
      ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs_join) T :=
  let hcl := envClosed_of_envWfT hW
  let hhd := iotaStarKEta_head happ
  have hf_eq : f = foldApps (.const w.recRef w.ls) (appsSpine f).2 := by
    rw [← hhd.1]
    exact (foldApps_appsSpine f).symm
  have hlen_xs : (appsSpine f).2.length = w.preMajor.length :=
    hhd.2.2.trans w.hpre.symm
  let ⟨hA', hcc⟩ := assumpCtxConvT_of_convA hW hΓ hA hcA
  let hccT := assumpCtxConvT_to_ctxConvT hcc
  let hB' : HasTyT E n (.assumption A' :: Γ) B (.sort v) :=
    hasTyT_ctx hcl hccT hB
  let hc_pi_symm : ConvT E n Γ (.pi A' B) (.pi A B) (.sort (.imax u v)) :=
    .symm Γ (.pi A B) (.pi A' B) (.sort (.imax u v))
      (.pi Γ A A' B B u v hcA (.refl (.assumption A :: Γ) B (.sort v) hB))
  let hc' : TyConvT E n Γ (.pi A' B) T :=
    .trans Γ (.pi A' B) (.pi A B) T
      (.of Γ (.pi A' B) (.pi A B) (.imax u v) hc_pi_symm) hc
  let hcl_align := classify_etaK_align w hNoPrf hf_step hAlign
    hf_eq hlen_xs (eqNList_refl w.ls)
  match hcl_step : parRedT_rec_preMajor_classify w hNoPrf hf_step hf_eq hlen_xs (eqNList_refl w.ls) with
  | .spine ls' xs' hf'_eq hls'_symm hargs =>
      have hls' : eqNList w.ls ls' := eqNList_symm hls'_symm
      let mp := minorPreImage w happ
      let ⟨m', hm'_get, _⟩ :=
        recArgsStep_get hargs (w.nparams + 1 + w.ctorIdx) mp.2.1
      have hlenP : (xs'.map (lift 0 1)).length = w.preMajor.length := by
        rw [List.length_map, recArgsStep_length hargs, hlen_xs]
      have hmin' : (xs'.map (lift 0 1))[w.nparams + 1 + w.ctorIdx]? =
          some (lift 0 1 m') :=
        list_getElem?_map_of_some (lift 0 1) xs' (w.nparams + 1 + w.ctorIdx) hm'_get
      let w' := replacePreMajorWitness w ls' (xs'.map (lift 0 1)) (lift 0 1 m')
        hls' hlenP hmin'
      have happ' : recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0) =
          .app (lift 0 1 f') (.bvar 0) :=
        replacePreMajorWitness_happ w hf'_eq hls' hlenP hmin'
      let hf' : HasTyT E n Γ f' (.pi A B) := parRedT_sr_peqT_val hf_step
      let hlhs' : HasTyT E n (.assumption A :: Γ)
          (recCall (.const w'.recRef w'.ls) w'.preMajor (.bvar 0)) B :=
        stepped_hlhs hcl happ' hf'
      let hlι' : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w') B :=
        stepped_hlι hcl rfl happ' hA hB hf' hmajor hmk hTm0
      let ⟨rhs', hι', hrhs_step⟩ :=
        hContract.onSpine hls' hargs hlenP hmin'
      let hrhs' : HasTyT E n (.assumption A :: Γ) rhs' B :=
        parRedT_sr_peqT_val hrhs_step
      let stepL1 : ParRedT (PEqLeafT E n) E n Γ f' (.lam A rhs') T :=
        eta_lamK_step w' happ' hA hf' hrl hsel hfam hmajor hmk hTm0
          hι' hlι' hlhs' hrhs' hc
      let hrhs'_A' : HasTyT E n (.assumption A' :: Γ) rhs' B :=
        hasTyT_ctx hcl hccT hrhs'
      let hrt2' : HasTyT E n Γ (.lam A' rhs') (.pi A' B) :=
        .lam Γ A' u rhs' B hA' hrhs'_A'
      let hrt1' : HasTyT E n Γ (.lam A' rhs') (.pi A B) :=
        .conv Γ (.lam A' rhs') (.pi A' B) (.pi A B) (.imax u v) hrt2' hc_pi_symm
      let hrhs_step' : ParRedT (PEqLeafT E n) E n (.assumption A' :: Γ) rhs rhs' B :=
        parRedT_assumpCtx hcl hcc hrhs_step
      let stepL2 : ParRedT (PEqLeafT E n) E n Γ (.lam A rhs') (.lam A' rhs') T :=
        .conv Γ (.lam A rhs') (.lam A' rhs') (.pi A B) T
          (.lam Γ A A' rhs' rhs' B u v hcA hA hB
            (.refl (.assumption A :: Γ) rhs' B hrhs') hrt1')
          hc
      let stepR : ParRedT (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs') T :=
        .conv Γ (.lam A' rhs) (.lam A' rhs') (.pi A' B) T
          (.lam Γ A' A' rhs rhs' B u v (.refl Γ A' (.sort u) hA') hA' hB'
            hrhs_step' hrt2')
          hc'
      let hrtT : HasTyT E n Γ (.lam A' rhs') T :=
        hasTyT_of_tyConvT hrt1' hc
      ⟨rhs',
        .tail stepL1 (.tail stepL2 (.refl Γ (.lam A' rhs') T hrtT)),
        .tail stepR (.refl Γ (.lam A' rhs') T hrtT)⟩
  | .etaK _ A_eta B_eta _ rhs_eta u_eta _ _ hf'_eq happ_eta hA_eta _ _ _ _ _ _ _
      hι_eta _ _ hrhs_eta _ =>
      let hal :
          (PLift (A_eta = A) ×' HasTyT E n (.assumption A :: Γ) rhs_eta B) ⊕
          (ConvT E n Γ A_eta A (.sort u_eta) ×'
            TyConvT E n (.assumption A_eta :: Γ) B_eta B) := by
        simpa only [hcl_step] using hcl_align
      match hal with
      | .inl ⟨⟨hA_eq⟩, hrhs_eta_AB⟩ =>
          let ⟨rhs_join, d_eta, d_rhs⟩ :=
            hContract.onEtaK happ_eta hι_eta hrhs_eta_AB
          let hrhs_eta_A' : HasTyT E n (.assumption A' :: Γ) rhs_eta B :=
            hasTyT_ctx hcl hccT hrhs_eta_AB
          let hrt2_eta : HasTyT E n Γ (.lam A' rhs_eta) (.pi A' B) :=
            .lam Γ A' u rhs_eta B hA' hrhs_eta_A'
          let hrt1_eta : HasTyT E n Γ (.lam A' rhs_eta) (.pi A B) :=
            .conv Γ (.lam A' rhs_eta) (.pi A' B) (.pi A B) (.imax u v) hrt2_eta hc_pi_symm
          let stepDomL : ParRedT (PEqLeafT E n) E n Γ (.lam A rhs_eta) (.lam A' rhs_eta) T :=
            .conv Γ (.lam A rhs_eta) (.lam A' rhs_eta) (.pi A B) T
              (.lam Γ A A' rhs_eta rhs_eta B u v hcA hA hB
                (.refl (.assumption A :: Γ) rhs_eta B hrhs_eta_AB) hrt1_eta)
              hc
          let stepDomL_f' : ParRedT (PEqLeafT E n) E n Γ f' (.lam A' rhs_eta) T := by
            rw [hf'_eq, hA_eq]
            exact stepDomL
          let d_eta_A' : ParRedTStar (PEqLeafT E n) E n (.assumption A' :: Γ) rhs_eta rhs_join B :=
            parRedTStar_assumpCtx hcl hcc d_eta
          let d_rhs_A' : ParRedTStar (PEqLeafT E n) E n (.assumption A' :: Γ) rhs rhs_join B :=
            parRedTStar_assumpCtx hcl hcc d_rhs
          let d_lam_eta : ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs_eta) (.lam A' rhs_join) T :=
            parRedTStar_lam_body hA' hB' hc' d_eta_A'
          let d_lam_rhs : ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs_join) T :=
            parRedTStar_lam_body hA' hB' hc' d_rhs_A'
          ⟨rhs_join, .tail stepDomL_f' d_lam_eta, d_lam_rhs⟩
      | .inr ⟨hcA_eta, hcB_eta⟩ =>
          let ⟨hA_u_eta, hcc_eta⟩ := assumpCtxConvT_of_convA hW hΓ hA_eta hcA_eta
          let hccT_eta := assumpCtxConvT_to_ctxConvT hcc_eta
          let hcc_eta_rev : AssumpCtxConvT E n (.assumption A :: Γ) (.assumption A_eta :: Γ) :=
            .assumption (assumpCtxConvT_refl Γ) hA_u_eta hA_eta
              (.symm Γ A_eta A (.sort u_eta) hcA_eta)
          let hB_at_Aeta : HasTyT E n (.assumption A_eta :: Γ) B (.sort v) :=
            hasTyT_ctx hcl (assumpCtxConvT_to_ctxConvT hcc_eta_rev) hB
          let hrhs_eta_B : HasTyT E n (.assumption A_eta :: Γ) rhs_eta B :=
            hasTyT_of_tyConvT hrhs_eta hcB_eta
          let hrhs_eta_AB : HasTyT E n (.assumption A :: Γ) rhs_eta B :=
            hasTyT_ctx hcl hccT_eta hrhs_eta_B
          let ⟨rhs_join, d_eta, d_rhs⟩ :=
            hContract.onEtaK happ_eta hι_eta hrhs_eta_AB
          let hc_pi_eta : ConvT E n Γ (.pi A_eta B) (.pi A B) (.sort (.imax u_eta v)) :=
            .pi Γ A_eta A B B u_eta v hcA_eta
              (.refl (.assumption A_eta :: Γ) B (.sort v) hB_at_Aeta)
          let hlamA_eta : HasTyT E n Γ (.lam A rhs_eta) (.pi A B) :=
            .lam Γ A u rhs_eta B hA hrhs_eta_AB
          let hlamA_eta_piB : HasTyT E n Γ (.lam A rhs_eta) (.pi A_eta B) :=
            .conv Γ (.lam A rhs_eta) (.pi A B) (.pi A_eta B) (.imax u_eta v) hlamA_eta
              (.symm Γ (.pi A_eta B) (.pi A B) (.sort (.imax u_eta v)) hc_pi_eta)
          let hc_etaB_T : TyConvT E n Γ (.pi A_eta B) T :=
            .trans Γ (.pi A_eta B) (.pi A B) T
              (.of Γ (.pi A_eta B) (.pi A B) (.imax u_eta v) hc_pi_eta) hc
          let stepL0 : ParRedT (PEqLeafT E n) E n Γ (.lam A_eta rhs_eta) (.lam A rhs_eta) T :=
            .conv Γ (.lam A_eta rhs_eta) (.lam A rhs_eta) (.pi A_eta B) T
              (.lam Γ A_eta A rhs_eta rhs_eta B u_eta v hcA_eta hA_eta hB_at_Aeta
                (.refl (.assumption A_eta :: Γ) rhs_eta B hrhs_eta_B) hlamA_eta_piB)
              hc_etaB_T
          let stepL1 : ParRedT (PEqLeafT E n) E n Γ f' (.lam A rhs_eta) T := by
            rw [hf'_eq]
            exact stepL0
          let hrhs_eta_A' : HasTyT E n (.assumption A' :: Γ) rhs_eta B :=
            hasTyT_ctx hcl hccT hrhs_eta_AB
          let hrt2_eta : HasTyT E n Γ (.lam A' rhs_eta) (.pi A' B) :=
            .lam Γ A' u rhs_eta B hA' hrhs_eta_A'
          let hrt1_eta : HasTyT E n Γ (.lam A' rhs_eta) (.pi A B) :=
            .conv Γ (.lam A' rhs_eta) (.pi A' B) (.pi A B) (.imax u v) hrt2_eta hc_pi_symm
          let stepL2 : ParRedT (PEqLeafT E n) E n Γ (.lam A rhs_eta) (.lam A' rhs_eta) T :=
            .conv Γ (.lam A rhs_eta) (.lam A' rhs_eta) (.pi A B) T
              (.lam Γ A A' rhs_eta rhs_eta B u v hcA hA hB
                (.refl (.assumption A :: Γ) rhs_eta B hrhs_eta_AB) hrt1_eta)
              hc
          let d_eta_A' : ParRedTStar (PEqLeafT E n) E n (.assumption A' :: Γ) rhs_eta rhs_join B :=
            parRedTStar_assumpCtx hcl hcc d_eta
          let d_rhs_A' : ParRedTStar (PEqLeafT E n) E n (.assumption A' :: Γ) rhs rhs_join B :=
            parRedTStar_assumpCtx hcl hcc d_rhs
          let d_lam_eta : ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs_eta) (.lam A' rhs_join) T :=
            parRedTStar_lam_body hA' hB' hc' d_eta_A'
          let d_lam_rhs : ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs_join) T :=
            parRedTStar_lam_body hA' hB' hc' d_rhs_A'
          ⟨rhs_join, .tail stepL1 (.tail stepL2 d_lam_eta), d_lam_rhs⟩

/-- Existential `ParRedTStar` join theorem consuming `FieldfulKPeakContract`
    without `NoEtaKStep hf_step` or `NoWrappedRootEtaK hf_step`. -/
theorem eta_lamK_full_joins_of_contract
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hContract : FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs)
    (hAlign : RootEtaKWrapperAlign A B hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_same _ (by first | exact ⟨rfl, rfl⟩ | rfl | trivial)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  let ⟨rhs_join, d1, d2⟩ :=
    eta_lamK_full_star_data_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
      hmajor hmk hTm0 hι hrhs hc hf_step hNoPrf hContract hAlign
  ⟨.lam A' rhs_join, ⟨d1⟩, ⟨d2⟩⟩

/-- Full `ParRedTStar` join handler under `NoWrappedRootEtaK hf_step`
    (forwarded directly to `eta_lamK_full_star_data_of_contract` via
    `sameRootEtaKPi_of_noWrappedRootEtaK`). -/
def eta_lamK_unwrapped_star_data_of_contract
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hnoWrap : NoWrappedRootEtaK hf_step)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hContract : FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n Γ f' (.lam A' rhs_join) T ×'
      ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs_join) T :=
  eta_lamK_full_star_data_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hc hf_step hNoPrf hContract
    (rootEtaKWrapperAlign_of_same hf_step (sameRootEtaKPi_of_noWrappedRootEtaK hf_step hnoWrap))

/-- Field-free (`w.nMinors = 1`, `w.fields = []`) specialization of
    `eta_lamK_full_star_data_of_contract` over the full `DerivedIotaU` union
    (`hι : DerivedIotaU E (iotaLhsOf w) rhs`) without `NoEtaKStep hf_step`
    or `NoWrappedRootEtaK hf_step`. -/
def eta_lamK_full_star_data
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hAlign : RootEtaKWrapperAlign A B hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_same _ (by first | exact ⟨rfl, rfl⟩ | rfl | trivial)) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n Γ f' (.lam A' rhs_join) T ×'
      ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs_join) T :=
  eta_lamK_full_star_data_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hc hf_step hNoPrf
    (fieldfulKPeakContract_of_fields_nil w happ hnmin hf_nil hι hrhs hMinorLift)
    hAlign

theorem eta_lamK_full_joins
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1)
    (hAlign : RootEtaKWrapperAlign A B hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_same _ (by first | exact ⟨rfl, rfl⟩ | rfl | trivial)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  let ⟨rhs_join, d1, d2⟩ :=
    eta_lamK_full_star_data hW hΓ w happ hcA hA hB hrl hsel hfam
      hmajor hmk hTm0 hι hrhs hnmin hf_nil hc hf_step hNoPrf hMinorLift hAlign
  ⟨.lam A' rhs_join, ⟨d1⟩, ⟨d2⟩⟩

/-- Field-free (`w.nMinors = 1`, `w.fields = []`) specialization of
    `eta_lamK_unwrapped_star_data_of_contract` over the full `DerivedIotaU`
    union (`hι : DerivedIotaU E (iotaLhsOf w) rhs`) under
    `NoWrappedRootEtaK hf_step`. -/
def eta_lamK_unwrapped_star_data
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hnoWrap : NoWrappedRootEtaK hf_step)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1) :
    Σ' rhs_join : Expr Nat,
      ParRedTStar (PEqLeafT E n) E n Γ f' (.lam A' rhs_join) T ×'
      ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) (.lam A' rhs_join) T :=
  eta_lamK_unwrapped_star_data_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hc hf_step hnoWrap hNoPrf
    (fieldfulKPeakContract_of_fields_nil w happ hnmin hf_nil hι hrhs hMinorLift)

theorem eta_lamK_unwrapped_joins
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ)
    {f f' A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hnmin : w.nMinors = 1)
    (hf_nil : w.fields = [])
    (hc : TyConvT E n Γ (.pi A B) T)
    (hf_step : ParRedT (PEqLeafT E n) E n Γ f f' (.pi A B))
    (hnoWrap : NoWrappedRootEtaK hf_step)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hMinorLift : MinorStepLift E n Γ A B (minorPreImage w happ).1) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) :=
  let ⟨rhs_join, d1, d2⟩ :=
    eta_lamK_unwrapped_star_data hW hΓ w happ hcA hA hB hrl hsel hfam
      hmajor hmk hTm0 hι hrhs hnmin hf_nil hc hf_step hnoWrap hNoPrf hMinorLift
  ⟨.lam A' rhs_join, ⟨d1⟩, ⟨d2⟩⟩

/-- Concrete `FieldfulKPeakContract` instance for the positive A-2 peak
    (`partialRec one` in `positiveContext` over `eqEnvT`) under sort uniqueness. -/
def positive_fieldfulKPeakContract_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    FieldfulKPeakContract eqEnvT 2 positiveContext domain codomain
      (witness one) (f := partialRec one) rfl (.bvar 1)
      (.ofU (witness one)) (atP' one positive_levels eqTym) :=
  fieldfulKPeakContract_of_fields_nil (witness one) (f := partialRec one) rfl rfl rfl
    (.ofU (witness one)) (atP' one positive_levels eqTym)
    (minorStepLift_positive_a2 hSortUniq (atP' one positive_levels eqTym))

/-- At the positive A-2 peak (`partialRec one`), for ANY parallel step
    `hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext (partialRec one) f' commonIndex`
    (including `partialRec_to_contracted`, `.conv`-wrapped `partialRec_to_contracted`,
    and `alternate_partial_step`, WITHOUT `NoEtaKStep hf_step` or
    `NoWrappedRootEtaK hf_step`) and ANY domain conversion
    `hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero)`,
    `f'` and `.lam A' (.bvar 1)` join in `ParRedTStar` under sort uniqueness
    alone via `eta_lamK_full_joins`. -/
theorem positive_full_eta_lamK_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex)
    (hAlign : RootEtaKWrapperAlign domain codomain hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_same _ (by first | exact ⟨rfl, rfl⟩ | rfl | trivial)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  have hNoPrf : ¬ HasRecProofRoot eqEnvT 2 positiveContext
      (witness one).recRef (witness one).ls (witness one).preMajor.length :=
    no_const65_proof_root_of_sortUniq hSortUniq
      (contextWf one positive_levels) (witness one).preMajor.length
  have hMinorLift : MinorStepLift eqEnvT 2 positiveContext
      domain codomain (minorPreImage (witness one) (f := partialRec one) rfl).1 :=
    minorStepLift_positive_a2 hSortUniq (atP' one positive_levels eqTym)
  eta_lamK_full_joins (f := partialRec one) (Tm := eqPTyAt0)
    envWf (contextWf one positive_levels)
    (witness one) rfl hcA (domainTy one positive_levels)
    (codomainTy one positive_levels) rfl
    (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    (instTy' one positive_levels pinEqGate_met)
    (instTy' one positive_levels eqReflTy2)
    (instTy' one positive_levels eqFamTy3)
    (.ofU (witness one)) (atP' one positive_levels eqTym) rfl rfl hc
    hf_step hNoPrf hMinorLift hAlign

/-- Positive A-2 peak join routing directly through `eta_lamK_full_joins_of_contract`
    and `positive_fieldfulKPeakContract_of_sortUniq`. -/
theorem positive_full_eta_lamK_joins_via_contract_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v)
    {f' A' T : Expr Nat}
    (hcA : ConvT eqEnvT 2 positiveContext domain A' (.sort .zero))
    (hc : TyConvT eqEnvT 2 positiveContext commonIndex T)
    (hf_step : ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) f' commonIndex)
    (hAlign : RootEtaKWrapperAlign domain codomain hf_step := by
      exact Rcic.Declarative.F8EtaK.rootEtaKWrapperAlign_of_same _ (by first | exact ⟨rfl, rfl⟩ | rfl | trivial)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext f' z T) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam A' (.bvar 1)) z T) :=
  have hNoPrf : ¬ HasRecProofRoot eqEnvT 2 positiveContext
      (witness one).recRef (witness one).ls (witness one).preMajor.length :=
    no_const65_proof_root_of_sortUniq hSortUniq
      (contextWf one positive_levels) (witness one).preMajor.length
  eta_lamK_full_joins_of_contract (f := partialRec one) (Tm := eqPTyAt0)
    envWf (contextWf one positive_levels)
    (witness one) rfl hcA (domainTy one positive_levels)
    (codomainTy one positive_levels) rfl
    (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    (instTy' one positive_levels pinEqGate_met)
    (instTy' one positive_levels eqReflTy2)
    (instTy' one positive_levels eqFamTy3)
    (.ofU (witness one)) (atP' one positive_levels eqTym) hc
    hf_step hNoPrf (positive_fieldfulKPeakContract_of_sortUniq hSortUniq) hAlign

/-- The non-reflexive `eta` child from the diamond-side review (`#6951`
    comment `6162843614`): `partialRec one` stepping by the new
    `ParRedT.iotaStarKEta` constructor to `contracted = .lam domain (.bvar 1)`. -/
def nonreflexiveEtaKChild :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) contracted commonIndex :=
  partialRec_to_contracted

/-- The `ParRedT.eta` step on `expanded one` with `nonreflexiveEtaKChild`
    (`partialRec_to_contracted`) as its child step. -/
def etaWithNonreflexiveEtaKChild :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (expanded one) contracted commonIndex :=
  .eta positiveContext (partialRec one) contracted domain codomain
    nonreflexiveEtaKChild (expandedTy one positive_levels)

/-- No post-step recursor witness `w' : IotaWitness eqEnvT` can exist at
    `f' = contracted = .lam domain (.bvar 1)`, because `iotaStarKEta_head`
    forces a `.const` head. -/
theorem no_post_child_K_witness (w : IotaWitness eqEnvT) :
    recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) ≠
      .app (lift 0 1 contracted) (.bvar 0) := by
  intro h
  have hh := (iotaStarKEta_head h).1
  change Expr.lam domain (.bvar 1) = Expr.const w.recRef w.ls at hh
  cases hh

/-- The two-branch peak pairing `etaWithNonreflexiveEtaKChild` against the
    original `kBranch one positive_levels`. -/
def actualEtaKChildPeak :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (expanded one) contracted commonIndex ×'
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (expanded one) contracted commonIndex :=
  ⟨etaWithNonreflexiveEtaKChild, kBranch one positive_levels⟩

/-- Direct reflexive join of `actualEtaKChildPeak` at `contracted`. -/
def actualEtaKChildPeak_join_refl :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      contracted contracted commonIndex ×'
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      contracted contracted commonIndex :=
  ⟨.refl positiveContext contracted commonIndex
      (contractedTy one positive_levels),
    .refl positiveContext contracted commonIndex
      (contractedTy one positive_levels)⟩

/-- `positive_full_eta_lamK_joins_of_sortUniq` handles `nonreflexiveEtaKChild`
    (`partialRec_to_contracted`) directly via the `.etaK` branch of
    `parRedT_rec_preMajor_classify` with zero extra wrapper-exclusion premises. -/
theorem positive_nonreflexiveEtaKChild_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_full_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    nonreflexiveEtaKChild

/-- `positive_stepped_eta_lamK_joins_of_sortUniq` (and `eta_lamK_stepped_diamond_data` /
    `eta_lamK_general_joins`) also applies directly to `nonreflexiveEtaKChild`
    (`partialRec_to_contracted`) WITHOUT `NoEtaKStep` or `NoWrappedRootEtaK`! -/
theorem positive_stepped_nonreflexiveEtaKChild_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_stepped_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    nonreflexiveEtaKChild

/-- Concrete `.conv`-wrapped root `ParRedT.iotaStarKEta` child step at
    `positiveContext` (`#6951` review item 1):
    `ParRedT.conv positiveContext (partialRec one) contracted commonIndex commonIndex nonreflexiveEtaKChild (.refl positiveContext commonIndex)`.
    This step is a legitimate `ParRedT` child for `ParRedT.eta` that violates
    `NoWrappedRootEtaK`, yet is handled directly by both
    `positive_stepped_eta_lamK_joins_of_sortUniq` and
    `positive_full_eta_lamK_joins_of_sortUniq` with zero extra premises. -/
def wrappedNonreflexiveEtaKChild :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) contracted commonIndex :=
  .conv positiveContext (partialRec one) contracted commonIndex commonIndex
    nonreflexiveEtaKChild (.refl positiveContext commonIndex)

theorem not_noWrappedRootEtaK_wrappedNonreflexiveEtaKChild :
    ¬ NoWrappedRootEtaK wrappedNonreflexiveEtaKChild :=
  fun h => h True.intro

theorem positive_stepped_wrappedNonreflexiveEtaKChild_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_stepped_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedNonreflexiveEtaKChild

theorem positive_wrappedNonreflexiveEtaKChild_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_full_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedNonreflexiveEtaKChild

/-- Distinct β-redex domain `(λ (X : Sort 0), X) domain` convertible to `domain`
    at `Sort 0` in `positiveContext`. -/
def domainBeta : Expr Nat :=
  .app (.lam (.sort .zero) (.bvar 0)) domain

theorem domainBeta_ne_domain : domainBeta ≠ domain := by
  decide

def domainBetaTy :
    HasTyT eqEnvT 2 positiveContext domainBeta (.sort .zero) :=
  .app positiveContext (.lam (.sort .zero) (.bvar 0)) domain
    (.sort .zero) (.sort .zero)
    (.lam positiveContext (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (.sort positiveContext .zero)
      (.bvar (.assumption (.sort .zero) :: positiveContext) 0 (.sort .zero) rfl))
    (domainTy one positive_levels)

def domainBeta_conv_domain :
    ConvT eqEnvT 2 positiveContext domainBeta domain (.sort .zero) :=
  .beta positiveContext (.sort .zero) (.bvar 0) domain (.sort .zero) (.succ .zero)
    (.sort positiveContext .zero)
    (.bvar (.assumption (.sort .zero) :: positiveContext) 0 (.sort .zero) rfl)
    (domainTy one positive_levels)

def piDomainBeta_conv_commonIndex :
    ConvT eqEnvT 2 positiveContext (.pi domainBeta codomain) commonIndex
      (.sort (.imax .zero one)) :=
  let ⟨hdom, _⟩ :=
    assumpCtxConvT_of_convA envWf (contextWf one positive_levels)
      domainBetaTy domainBeta_conv_domain
  let hcc_rev : AssumpCtxConvT eqEnvT 2
      (.assumption domain :: positiveContext)
      (.assumption domainBeta :: positiveContext) :=
    .assumption (assumpCtxConvT_refl positiveContext) hdom domainBetaTy
      (.symm positiveContext domainBeta domain (.sort .zero) domainBeta_conv_domain)
  let hcod_beta : HasTyT eqEnvT 2 (.assumption domainBeta :: positiveContext)
      codomain (.sort one) :=
    hasTyT_ctx (envClosed_of_envWfT envWf)
      (assumpCtxConvT_to_ctxConvT hcc_rev) (codomainTy one positive_levels)
  .pi positiveContext domainBeta domain codomain codomain .zero one
    domainBeta_conv_domain
    (.refl (.assumption domainBeta :: positiveContext) codomain (.sort one) hcod_beta)

/-- Root `ParRedT.iotaStarKEta` step at `.pi domainBeta codomain` with distinct
    binder domain `domainBeta ≠ domain`, stepping `partialRec one` to
    `.lam domainBeta (.bvar 1) ≠ contracted`. -/
def partialRec_to_contracted_domainBeta :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) (.lam domainBeta (.bvar 1)) (.pi domainBeta codomain) :=
  let hcl := envClosed_of_envWfT envWf
  let ⟨hdom, _⟩ :=
    assumpCtxConvT_of_convA envWf (contextWf one positive_levels)
      domainBetaTy domainBeta_conv_domain
  let hcc_rev : AssumpCtxConvT eqEnvT 2
      (.assumption domain :: positiveContext)
      (.assumption domainBeta :: positiveContext) :=
    .assumption (assumpCtxConvT_refl positiveContext) hdom domainBetaTy
      (.symm positiveContext domainBeta domain (.sort .zero) domainBeta_conv_domain)
  let hccT_rev := assumpCtxConvT_to_ctxConvT hcc_rev
  let hf_beta : HasTyT eqEnvT 2 positiveContext (partialRec one)
      (.pi domainBeta codomain) :=
    .conv positiveContext (partialRec one) commonIndex (.pi domainBeta codomain)
      (.imax .zero one) (partialRecTy one positive_levels)
      (.symm positiveContext (.pi domainBeta codomain) commonIndex
        (.sort (.imax .zero one)) piDomainBeta_conv_commonIndex)
  .iotaStarKEta positiveContext (witness one) (partialRec one)
    domainBeta codomain eqPTyAt0 (.bvar 1) .zero .zero True
    rfl domainBetaTy hf_beta rfl
    (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    (hasTyT_ctx hcl hccT_rev (instTy' one positive_levels pinEqGate_met))
    (hasTyT_ctx hcl hccT_rev (instTy' one positive_levels eqReflTy2))
    (hasTyT_ctx hcl hccT_rev (instTy' one positive_levels eqFamTy3))
    (.ofU (witness one))
    (hasTyT_ctx hcl hccT_rev (atP' one positive_levels eqRecLhsTy))
    (hasTyT_ctx hcl hccT_rev (bodyTy' one positive_levels))
    (hasTyT_ctx hcl hccT_rev (atP' one positive_levels eqTym))

/-- Concrete `.conv`-wrapped root `ParRedT.iotaStarKEta` child step at
    `commonIndex` whose inner binder domain `domainBeta` is distinct from
    `domain` (`domainBeta ≠ domain`) and whose target is `.lam domainBeta (.bvar 1) ≠ contracted`. -/
def wrappedDistinctDomainEtaKChild :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
      (partialRec one) (.lam domainBeta (.bvar 1)) commonIndex :=
  .conv positiveContext (partialRec one) (.lam domainBeta (.bvar 1))
    (.pi domainBeta codomain) commonIndex
    partialRec_to_contracted_domainBeta
    (.of positiveContext (.pi domainBeta codomain) commonIndex (.imax .zero one)
      piDomainBeta_conv_commonIndex)

theorem not_noWrappedRootEtaK_wrappedDistinctDomainEtaKChild :
    ¬ NoWrappedRootEtaK wrappedDistinctDomainEtaKChild :=
  fun h => h True.intro

theorem not_sameRootEtaKDomain_wrappedDistinctDomainEtaKChild :
    ¬ SameRootEtaKDomain domain wrappedDistinctDomainEtaKChild :=
  domainBeta_ne_domain

theorem positive_stepped_wrappedDistinctDomainEtaKChild_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam domainBeta (.bvar 1)) z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_stepped_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedDistinctDomainEtaKChild
    (by
      dsimp [wrappedDistinctDomainEtaKChild, partialRec_to_contracted_domainBeta,
        RootEtaKDomainConv]
      rw [if_neg domainBeta_ne_domain]
      exact ⟨contextWf one positive_levels, domainBeta_conv_domain⟩)

theorem positive_wrappedDistinctDomainEtaKChild_joins_of_sortUniq
    (hSortUniq : ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT eqEnvT 2 Γ →
      HasTyT eqEnvT 2 Γ T (.sort u) →
      HasTyT eqEnvT 2 Γ T (.sort v) →
      eqN u v) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        (.lam domainBeta (.bvar 1)) z commonIndex) ∧
      Nonempty (ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveContext
        contracted z commonIndex) :=
  positive_full_eta_lamK_joins_of_sortUniq hSortUniq
    (.refl positiveContext domain (.sort .zero) (domainTy one positive_levels))
    (.refl positiveContext commonIndex)
    wrappedDistinctDomainEtaKChild
    (by
      dsimp [wrappedDistinctDomainEtaKChild, partialRec_to_contracted_domainBeta,
        RootEtaKWrapperAlign]
      rw [if_neg domainBeta_ne_domain]
      exact ⟨domainBeta_conv_domain,
        .refl (.assumption domainBeta :: positiveContext) codomain⟩)


/-! ## Step 8: Explicit O-M obligation for A.2 annotation reconciliation -/

section OMEtaKAnnot
open Rcic.Declarative.F8Measure

/-- In an A.2 self-overlap of `ParRedT.iotaStarKEta` at source `f`,
    `iotaStarKEta_appParts happ` gives `f = .app f₀ a₀`.
    Inverting the two carried typings `hf₁ : HasTyT E n Γ f (.pi A₁ B₁)` and
    `hf₂ : HasTyT E n Γ f (.pi A₂ B₂)` via `EvTy.invApp` and composing `U` on
    `inv₁.hf, inv₂.hf`, `X` on the Π-type of `f₀`, and `EvTc.subst0` at `a₀`
    produces a provenance chain `EvTc R Γ (.pi A₁ B₁) (.pi A₂ B₂)` whose leaves
    are strictly `SubOf (.ty hf₁)` or `SubOf (.ty hf₂)` (never an imported
    `piRow`). -/
def om_etaK_annot_piChain {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} (U : ∀ R : List (Jd E n), UProc R)
    (X : ∀ R : List (Jd E n), XProc R)
    {Γ : LCtx} {f f₀ a₀ A₁ B₁ A₂ B₂ : Expr Nat}
    (heq : f = .app f₀ a₀)
    (hf₁ : HasTyT E n Γ f (.pi A₁ B₁))
    (hsub₁ : ∃ r ∈ R, SubEq (.ty hf₁) r)
    (hf₂ : HasTyT E n Γ f (.pi A₂ B₂))
    (hsub₂ : ∃ r ∈ R, SubEq (.ty hf₂) r) :
    EvTc R Γ (.pi A₁ B₁) (.pi A₂ B₂) :=
  let inv₁ := (EvTy.lit hf₁ hsub₁).invApp rfl heq
  let inv₂ := (EvTy.lit hf₂ hsub₂).invApp rfl heq
  let c_fn := U R inv₁.hf inv₂.hf
  let c_cod := (X R c_fn).2
  let ha_cast : EvTy R (substRemove a₀ 0 (.assumption inv₁.A :: Γ))
      (lift 0 0 a₀) (lift 0 0 inv₁.A) :=
    EvTy.cast rfl (by simp [lift_zero]) (by simp [lift_zero]) inv₁.ha
  let c_inst : EvTc R Γ (instantiate0 a₀ inv₁.B) (instantiate0 a₀ inv₂.B) :=
    EvTc.cast rfl (by simp [lift_zero, instantiate0])
      (by simp [lift_zero, instantiate0])
      (.subst0 (t := inv₁.A) (v := a₀) 0 c_cod (by simp) ha_cast)
  .trans (.trans (.symm inv₁.hc) c_inst) inv₂.hc

/-- The `X` request on `(A₁, A₂)` and `(B₁, B₂)` extracted from
    `om_etaK_annot_piChain` without any imported `piRow`. -/
def om_etaK_annot_request {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} (U : ∀ R : List (Jd E n), UProc R)
    (X : ∀ R : List (Jd E n), XProc R)
    {Γ : LCtx} {f f₀ a₀ A₁ B₁ A₂ B₂ : Expr Nat}
    (heq : f = .app f₀ a₀)
    (hf₁ : HasTyT E n Γ f (.pi A₁ B₁))
    (hsub₁ : ∃ r ∈ R, SubEq (.ty hf₁) r)
    (hf₂ : HasTyT E n Γ f (.pi A₂ B₂))
    (hsub₂ : ∃ r ∈ R, SubEq (.ty hf₂) r) :
    EvTc R Γ A₁ A₂ × EvTc R (.assumption A₁ :: Γ) B₁ B₂ :=
  X R (om_etaK_annot_piChain U X heq hf₁ hsub₁ hf₂ hsub₂)

/-- Every leaf of `om_etaK_annot_piChain` is strictly `SubOf (.ty hf₁)` or
    `SubOf (.ty hf₂)` under `UContract U` and `XContract X`. -/
theorem om_etaK_annot_piChain_strict {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} (U : ∀ R : List (Jd E n), UProc R)
    (X : ∀ R : List (Jd E n), XProc R)
    (hU : UContract U) (hX : XContract X)
    {Γ : LCtx} {f f₀ a₀ A₁ B₁ A₂ B₂ : Expr Nat}
    (heq : f = .app f₀ a₀)
    (hf₁ : HasTyT E n Γ f (.pi A₁ B₁))
    (hsub₁ : ∃ r ∈ R, SubEq (.ty hf₁) r)
    (hf₂ : HasTyT E n Γ f (.pi A₂ B₂))
    (hsub₂ : ∃ r ∈ R, SubEq (.ty hf₂) r) :
    ∀ ℓ ∈ (om_etaK_annot_piChain U X heq hf₁ hsub₁ hf₂ hsub₂).leaves,
      SubOf ℓ (.ty hf₁) ∨ SubOf ℓ (.ty hf₂) := by
  intro ℓ hℓ
  let inv₁ := (EvTy.lit hf₁ hsub₁).invApp rfl heq
  let inv₂ := (EvTy.lit hf₂ hsub₂).invApp rfl heq
  have hstr₁ : ∀ q ∈ inv₁.leaves, SubOf q (.ty hf₁) :=
    EvTy.invApp_strict hf₁ hsub₁ heq
  have hstr₂ : ∀ q ∈ inv₂.leaves, SubOf q (.ty hf₂) :=
    EvTy.invApp_strict hf₂ hsub₂ heq
  have hfn_sub : ∀ q ∈ (U R inv₁.hf inv₂.hf).leaves,
      SubOf q (.ty hf₁) ∨ SubOf q (.ty hf₂) := by
    intro q hq
    obtain ⟨q', hq', hseq⟩ := hU R inv₁.hf inv₂.hf q hq
    rcases List.mem_append.mp hq' with hq1 | hq2
    · have hmem : q' ∈ inv₁.leaves := by
        simp only [EvInvApp.leaves, List.mem_append]
        exact .inl (.inl hq1)
      exact .inl (subEq_trans_subOf hseq (hstr₁ q' hmem))
    · have hmem : q' ∈ inv₂.leaves := by
        simp only [EvInvApp.leaves, List.mem_append]
        exact .inl (.inl hq2)
      exact .inr (subEq_trans_subOf hseq (hstr₂ q' hmem))
  have hcod_sub : ∀ q ∈ (X R (U R inv₁.hf inv₂.hf)).2.leaves,
      SubOf q (.ty hf₁) ∨ SubOf q (.ty hf₂) := by
    intro q hq
    have hq_in : q ∈ (X R (U R inv₁.hf inv₂.hf)).1.leaves ++
        (X R (U R inv₁.hf inv₂.hf)).2.leaves :=
      List.mem_append.mpr (.inr hq)
    obtain ⟨q', hq', hseq⟩ := hX R (U R inv₁.hf inv₂.hf) q hq_in
    rcases hfn_sub q' hq' with hs1 | hs2
    · exact .inl (subEq_trans_subOf hseq hs1)
    · exact .inr (subEq_trans_subOf hseq hs2)
  simp only [om_etaK_annot_piChain, EvTc.leaves, EvTc.cast_leaves,
    EvTy.cast_leaves, List.mem_append] at hℓ
  rcases hℓ with ((h_hc1 | (h_cod | h_ha1)) | h_hc2)
  · have hmem : ℓ ∈ inv₁.leaves := by
      simp only [EvInvApp.leaves, List.mem_append]
      exact .inr h_hc1
    exact .inl (hstr₁ ℓ hmem)
  · exact hcod_sub ℓ h_cod
  · have hmem : ℓ ∈ inv₁.leaves := by
      simp only [EvInvApp.leaves, List.mem_append]
      exact .inl (.inr h_ha1)
    exact .inl (hstr₁ ℓ hmem)
  · have hmem : ℓ ∈ inv₂.leaves := by
      simp only [EvInvApp.leaves, List.mem_append]
      exact .inr h_hc2
    exact .inr (hstr₂ ℓ hmem)

/-- Every leaf of the `X` request on `(A₁, A₂)` and `(B₁, B₂)` is strictly
    `SubOf (.ty hf₁)` or `SubOf (.ty hf₂)` under `UContract U` and `XContract X`. -/
theorem om_etaK_annot_request_strict {E : ResolvedEnv} {n : Nat}
    {R : List (Jd E n)} (U : ∀ R : List (Jd E n), UProc R)
    (X : ∀ R : List (Jd E n), XProc R)
    (hU : UContract U) (hX : XContract X)
    {Γ : LCtx} {f f₀ a₀ A₁ B₁ A₂ B₂ : Expr Nat}
    (heq : f = .app f₀ a₀)
    (hf₁ : HasTyT E n Γ f (.pi A₁ B₁))
    (hsub₁ : ∃ r ∈ R, SubEq (.ty hf₁) r)
    (hf₂ : HasTyT E n Γ f (.pi A₂ B₂))
    (hsub₂ : ∃ r ∈ R, SubEq (.ty hf₂) r) :
    ∀ ℓ ∈ (om_etaK_annot_request U X heq hf₁ hsub₁ hf₂ hsub₂).1.leaves ++
        (om_etaK_annot_request U X heq hf₁ hsub₁ hf₂ hsub₂).2.leaves,
      SubOf ℓ (.ty hf₁) ∨ SubOf ℓ (.ty hf₂) := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', hseq⟩ :=
    hX R (om_etaK_annot_piChain U X heq hf₁ hsub₁ hf₂ hsub₂) ℓ hℓ
  rcases om_etaK_annot_piChain_strict U X hU hX heq hf₁ hsub₁ hf₂ hsub₂ ℓ' hℓ' with
    hs1 | hs2
  · exact .inl (subEq_trans_subOf hseq hs1)
  · exact .inr (subEq_trans_subOf hseq hs2)

/-- `OM3_edge` for the A.2 annotation request directly below `[.ty hf₁, .ty hf₂]`. -/
theorem om_etaK_annot_edge_typings {E : ResolvedEnv} {n : Nat}
    (U : ∀ R : List (Jd E n), UProc R)
    (X : ∀ R : List (Jd E n), XProc R)
    (hU : UContract U) (hX : XContract X)
    {Γ : LCtx} {f f₀ a₀ A₁ B₁ A₂ B₂ : Expr Nat}
    (heq : f = .app f₀ a₀)
    (hf₁ : HasTyT E n Γ f (.pi A₁ B₁))
    (hf₂ : HasTyT E n Γ f (.pi A₂ B₂)) :
    let R : List (Jd E n) := [.ty hf₁, .ty hf₂]
    let hsub₁ : ∃ r ∈ R, SubEq (.ty hf₁) r := ⟨.ty hf₁, .head _, .inl rfl⟩
    let hsub₂ : ∃ r ∈ R, SubEq (.ty hf₂) r :=
      ⟨.ty hf₂, .tail _ (.head _), .inl rfl⟩
    let req := om_etaK_annot_request U X heq hf₁ hsub₁ hf₂ hsub₂
    OM3_edge R (req.1.leaves ++ req.2.leaves) := by
  intro R hsub₁ hsub₂ req
  simpa only [List.append_nil] using
    om3_edge_of_strictLeaves (X := R) (Z := [])
      (L := req.1.leaves ++ req.2.leaves) (by simp [R])
      (fun ℓ hℓ => by
        rcases om_etaK_annot_request_strict U X hU hX heq hf₁ hsub₁ hf₂ hsub₂ ℓ hℓ with
          hs1 | hs2
        · exact ⟨.ty hf₁, .head _, hs1⟩
        · exact ⟨.ty hf₂, .tail _ (.head _), hs2⟩)

/-- `hf` is an immediate `Child` of any `ParRedT.iotaStarKEta` step. -/
theorem om_etaK_child_hf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {w : IotaWitness E} {f A B Tm rhs : Expr Nat} {u rl : Level} {afs : Prop}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA : HasTyT E n Γ A (.sort u))
    (hf : HasTyT E n Γ f (.pi A B))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
    (hlhs : HasTyT E n (.assumption A :: Γ)
      (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B) :
    Child (.ty hf)
      (.pr (.iotaStarKEta Γ w f A B Tm rhs u rl afs
        happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs)) :=
  .tail _ (.head _)

/-- Bare-step `U`-first `OM3_edge` (`om_etaK_annot_bareU`) for two unwrapped
    `ParRedT.iotaStarKEta` steps `s₁, s₂` out of the same source `f`: the `X`
    request on `(A₁, A₂)` and `(B₁, B₂)` extracted from `om_etaK_annot_piChain`
    is an `OM3_edge` strictly below `[.pr s₁, .pr s₂]` without any imported
    `piRow`. The diamond's wrapped self-overlap consumes `om_etaK_wrapper_edge`
    (`EtaKAnnot.OM_etaK_annot`, `rcic.RcicF8OMEtaKAnnot`). -/
theorem om_etaK_annot_bareU {E : ResolvedEnv} {n : Nat}
    (U : ∀ R : List (Jd E n), UProc R)
    (X : ∀ R : List (Jd E n), XProc R)
    (hU : UContract U) (hX : XContract X)
    {Γ : LCtx} {f f₀ a₀ : Expr Nat}
    (heq : f = .app f₀ a₀)
    {w₁ : IotaWitness E} {A₁ B₁ Tm₁ rhs₁ : Expr Nat} {u₁ rl₁ : Level} {afs₁ : Prop}
    (happ₁ : recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA₁ : HasTyT E n Γ A₁ (.sort u₁))
    (hf₁ : HasTyT E n Γ f (.pi A₁ B₁))
    (hrl₁ : piBody w₁.famMember.mtype = .sort rl₁)
    (hsel₁ : EliminationSelection rl₁ w₁.nMinors afs₁ .anySort)
    (hfam₁ : ∃ lsF, (appsSpine Tm₁).1 = .const w₁.familyRef lsF)
    (hmajor₁ : HasTyT E n (.assumption A₁ :: Γ) (.bvar 0) Tm₁)
    (hmk₁ : HasTyT E n (.assumption A₁ :: Γ) (ctorMajor w₁) Tm₁)
    (hTm0₁ : HasTyT E n (.assumption A₁ :: Γ) Tm₁ (.sort .zero))
    (hι₁ : DerivedIotaU E (iotaLhsOf w₁) rhs₁)
    (hlι₁ : HasTyT E n (.assumption A₁ :: Γ) (iotaLhsOf w₁) B₁)
    (hlhs₁ : HasTyT E n (.assumption A₁ :: Γ)
      (recCall (.const w₁.recRef w₁.ls) w₁.preMajor (.bvar 0)) B₁)
    (hrhs₁ : HasTyT E n (.assumption A₁ :: Γ) rhs₁ B₁)
    {w₂ : IotaWitness E} {A₂ B₂ Tm₂ rhs₂ : Expr Nat} {u₂ rl₂ : Level} {afs₂ : Prop}
    (happ₂ : recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA₂ : HasTyT E n Γ A₂ (.sort u₂))
    (hf₂ : HasTyT E n Γ f (.pi A₂ B₂))
    (hrl₂ : piBody w₂.famMember.mtype = .sort rl₂)
    (hsel₂ : EliminationSelection rl₂ w₂.nMinors afs₂ .anySort)
    (hfam₂ : ∃ lsF, (appsSpine Tm₂).1 = .const w₂.familyRef lsF)
    (hmajor₂ : HasTyT E n (.assumption A₂ :: Γ) (.bvar 0) Tm₂)
    (hmk₂ : HasTyT E n (.assumption A₂ :: Γ) (ctorMajor w₂) Tm₂)
    (hTm0₂ : HasTyT E n (.assumption A₂ :: Γ) Tm₂ (.sort .zero))
    (hι₂ : DerivedIotaU E (iotaLhsOf w₂) rhs₂)
    (hlι₂ : HasTyT E n (.assumption A₂ :: Γ) (iotaLhsOf w₂) B₂)
    (hlhs₂ : HasTyT E n (.assumption A₂ :: Γ)
      (recCall (.const w₂.recRef w₂.ls) w₂.preMajor (.bvar 0)) B₂)
    (hrhs₂ : HasTyT E n (.assumption A₂ :: Γ) rhs₂ B₂) :
    let s₁ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₁ rhs₁) (.pi A₁ B₁) :=
      .iotaStarKEta Γ w₁ f A₁ B₁ Tm₁ rhs₁ u₁ rl₁ afs₁
        happ₁ hA₁ hf₁ hrl₁ hsel₁ hfam₁ hmajor₁ hmk₁ hTm0₁ hι₁ hlι₁ hlhs₁ hrhs₁
    let s₂ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₂ rhs₂) (.pi A₂ B₂) :=
      .iotaStarKEta Γ w₂ f A₂ B₂ Tm₂ rhs₂ u₂ rl₂ afs₂
        happ₂ hA₂ hf₂ hrl₂ hsel₂ hfam₂ hmajor₂ hmk₂ hTm0₂ hι₂ hlι₂ hlhs₂ hrhs₂
    let R : List (Jd E n) := [.pr s₁, .pr s₂]
    let hsub₁ : ∃ r ∈ R, SubEq (.ty hf₁) r :=
      ⟨.pr s₁, .head _, .inr (.child (om_etaK_child_hf happ₁ hA₁ hf₁ hrl₁ hsel₁
        hfam₁ hmajor₁ hmk₁ hTm0₁ hι₁ hlι₁ hlhs₁ hrhs₁))⟩
    let hsub₂ : ∃ r ∈ R, SubEq (.ty hf₂) r :=
      ⟨.pr s₂, .tail _ (.head _), .inr (.child (om_etaK_child_hf happ₂ hA₂ hf₂ hrl₂ hsel₂
        hfam₂ hmajor₂ hmk₂ hTm0₂ hι₂ hlι₂ hlhs₂ hrhs₂))⟩
    let req := om_etaK_annot_request U X heq hf₁ hsub₁ hf₂ hsub₂
    OM3_edge R (req.1.leaves ++ req.2.leaves) := by
  intro s₁ s₂ R hsub₁ hsub₂ req
  have hch₁ : SubOf (.ty hf₁) (.pr s₁) :=
    .child (om_etaK_child_hf happ₁ hA₁ hf₁ hrl₁ hsel₁ hfam₁ hmajor₁ hmk₁ hTm0₁
      hι₁ hlι₁ hlhs₁ hrhs₁)
  have hch₂ : SubOf (.ty hf₂) (.pr s₂) :=
    .child (om_etaK_child_hf happ₂ hA₂ hf₂ hrl₂ hsel₂ hfam₂ hmajor₂ hmk₂ hTm0₂
      hι₂ hlι₂ hlhs₂ hrhs₂)
  simpa only [List.append_nil] using
    om3_edge_of_strictLeaves (X := R) (Z := [])
      (L := req.1.leaves ++ req.2.leaves) (by simp [R])
      (fun ℓ hℓ => by
        rcases om_etaK_annot_request_strict U X hU hX heq hf₁ hsub₁ hf₂ hsub₂ ℓ hℓ with
          hs1 | hs2
        · exact ⟨.pr s₁, .head _, .trans hs1 hch₁⟩
        · exact ⟨.pr s₂, .tail _ (.head _), .trans hs2 hch₂⟩)

/-- Original-wrapper A.2 self-overlap `X` request (consuming `EtaKAnnot.annotRequest`
    from `rcic.RcicF8OMEtaKAnnot`, `#6975`) on two `.conv`-wrapped
    `ParRedT.iotaStarKEta` steps `s₁, s₂` with their original wrapper fields
    `c₁ : TyConvT E n Γ (.pi A₁ B₁) T` and `c₂ : TyConvT E n Γ (.pi A₂ B₂) T`.
    The composite `EvTc.trans (EvTc.lit c₁ …) (EvTc.symm (EvTc.lit c₂ …))` stays
    lazy with leaves `[.tc c₁, .tc c₂]`. -/
def om_etaK_wrapper_request {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A₁ B₁ A₂ B₂ rhs₁ rhs₂ T : Expr Nat}
    (s₁ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₁ rhs₁) (.pi A₁ B₁))
    (s₂ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₂ rhs₂) (.pi A₂ B₂))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T)
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T) :
    EvTc (EtaKAnnot.removedAtoms s₁ s₂ c₁ c₂) Γ (.pi A₁ B₁) (.pi A₂ B₂) :=
  EtaKAnnot.annotRequest s₁ s₂ c₁ c₂

/-- Original-wrapper `OM3_edge` for the A.2 self-overlap of `ParRedT.iotaStarKEta`
    (instantiating `EtaKAnnot.OM_etaK_annot` from `rcic.RcicF8OMEtaKAnnot`):
    caller is `[.pr (leftInput s₁ c₁), .pr (rightInput s₂ c₂)] ++ Z` and
    replaced atoms are `[.pr (leftInput s₁ c₁), .pr (rightInput s₂ c₂)]`. -/
theorem om_etaK_wrapper_edge {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A₁ B₁ A₂ B₂ rhs₁ rhs₂ T : Expr Nat}
    (s₁ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₁ rhs₁) (.pi A₁ B₁))
    (s₂ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₂ rhs₂) (.pi A₂ B₂))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T)
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T)
    (Z : List (Jd E n)) :
    OM3_edge (EtaKAnnot.callerAtoms s₁ s₂ c₁ c₂ Z)
      ((om_etaK_wrapper_request s₁ s₂ c₁ c₂).leaves ++ Z) :=
  EtaKAnnot.OM_etaK_annot s₁ s₂ c₁ c₂ Z

/-- Under `XContract X`, both components returned by `X` on
    `om_etaK_wrapper_request s₁ s₂ c₁ c₂` remain strictly `OM3_edge`-below the
    original `D` caller `EtaKAnnot.callerAtoms s₁ s₂ c₁ c₂ Z`. -/
theorem om_etaK_wrapper_X_outputs_edge {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A₁ B₁ A₂ B₂ rhs₁ rhs₂ T : Expr Nat}
    (s₁ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₁ rhs₁) (.pi A₁ B₁))
    (s₂ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₂ rhs₂) (.pi A₂ B₂))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T)
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T)
    (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    (Z : List (Jd E n)) :
    let q := om_etaK_wrapper_request s₁ s₂ c₁ c₂
    let ans := X (EtaKAnnot.removedAtoms s₁ s₂ c₁ c₂) q
    OM3_edge (EtaKAnnot.callerAtoms s₁ s₂ c₁ c₂ Z)
      ((ans.1.leaves ++ ans.2.leaves) ++ Z) :=
  EtaKAnnot.X_outputs_edge s₁ s₂ c₁ c₂ X hX Z

/-- `Type`-valued codomain sort seed for any `ParRedT.iotaStarKEta` node:
    from the inner step's carried `hA_eta : HasTyT E n Γ A_eta (.sort u_eta)`
    and `hrhs_eta : HasTyT E n (.assumption A_eta :: Γ) rhs_eta B_eta`,
    typing regularity (`regularT_of_envWfT`) under the well-formed binder
    `.assumption Γ A_eta u_eta hΓ hA_eta` unconditionally produces
    `Σ' v_eta : Level, HasTyT E n (.assumption A_eta :: Γ) B_eta (.sort v_eta)`. -/
def iotaStarKEta_codomain_sort_seed {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A_eta B_eta rhs_eta : Expr Nat} {u_eta : Level}
    (hA_eta : HasTyT E n Γ A_eta (.sort u_eta))
    (hrhs_eta : HasTyT E n (.assumption A_eta :: Γ) rhs_eta B_eta) :
    Σ' v_eta : Level, HasTyT E n (.assumption A_eta :: Γ) B_eta (.sort v_eta) :=
  regularT_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW)
    (.assumption Γ A_eta u_eta hΓ hA_eta) hrhs_eta

/-- Collapse any `TyConvT E n Γ a b` chain at a left sort typing
    `hA : HasTyT E n Γ a (.sort u)` to `Nonempty (ConvT E n Γ a b (.sort u))`
    using only `DT009T_endpoints_envWfT` (unconditional at `EnvWfT E`) and
    sort uniqueness `hSortUniq` (`ConvT.sorts` + `ConvT.tyConv`). -/
theorem convT_of_tyConvT_sort_of_sortUniq {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ a (.sort u)) (hc : TyConvT E n Γ a b) :
    Nonempty (ConvT E n Γ a b (.sort u)) := by
  induction hc with
  | refl => exact ⟨.refl _ _ _ hA⟩
  | of _ _ v h =>
      obtain ⟨hav⟩ := (convT_endpoints hW hΓ h).1
      have heq : eqN v u := hSortUniq hΓ hav hA
      exact ⟨.tyConv _ _ _ (.sort v) (.sort u) (.succ v) h (.sorts _ v u heq)⟩
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨c1⟩ := ih1 hA
      obtain ⟨hm⟩ := (convT_endpoints hW hΓ c1).2
      obtain ⟨c2⟩ := ih2 hm
      exact ⟨.trans _ _ _ _ _ c1 c2⟩

/-- Materialize the domain and codomain `EvTc` chains returned by `X` on the
    original-wrapper request `om_etaK_wrapper_request s₁ s₂ c₁ c₂`
    (`EtaKAnnot.annotRequest s₁ s₂ c₁ c₂`, whose leaves are `[.tc c₁, .tc c₂]`
    and whose outputs satisfy `om_etaK_wrapper_X_outputs_edge`) into concrete
    `TyConvT` derivations `TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂`. -/
def om_etaK_wrapper_X_materialize {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} {f A₁ B₁ A₂ B₂ rhs₁ rhs₂ T : Expr Nat}
    (s₁ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₁ rhs₁) (.pi A₁ B₁))
    (s₂ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₂ rhs₂) (.pi A₂ B₂))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T)
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T)
    (X : ∀ R : List (Jd E n), XProc R) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let q := om_etaK_wrapper_request s₁ s₂ c₁ c₂
  let ans := X (EtaKAnnot.removedAtoms s₁ s₂ c₁ c₂) q
  (ans.1.val hcl hinst, ans.2.val hcl hinst)

/-- Semantic alignment package tied directly to the original-wrapper O-M request
    `om_etaK_wrapper_request s₁ s₂ c₁ c₂`:
    1. derives the codomain sort seed `Σ' v₁ : Level, HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v₁)`
       from the inner step's carried `hA₁` and `hrhs₁` via `iotaStarKEta_codomain_sort_seed`;
    2. materializes `TyConvT E n Γ A₁ A₂` and `TyConvT E n (.assumption A₁ :: Γ) B₁ B₂`
       from `X` on `om_etaK_wrapper_request s₁ s₂ c₁ c₂` via `om_etaK_wrapper_X_materialize`;
    3. collapses `TyConvT E n Γ A₁ A₂` at `hA₁` to `Nonempty (ConvT E n Γ A₁ A₂ (.sort u₁))`
       via `convT_of_tyConvT_sort_of_sortUniq`. -/
def om_etaK_wrapper_X_semantic_align {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f A₁ B₁ A₂ B₂ rhs₁ rhs₂ T : Expr Nat} {u₁ : Level}
    (hA₁ : HasTyT E n Γ A₁ (.sort u₁))
    (hrhs₁ : HasTyT E n (.assumption A₁ :: Γ) rhs₁ B₁)
    (s₁ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₁ rhs₁) (.pi A₁ B₁))
    (s₂ : ParRedT (PEqLeafT E n) E n Γ f (.lam A₂ rhs₂) (.pi A₂ B₂))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T)
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T)
    (X : ∀ R : List (Jd E n), XProc R) :
    Σ' v₁ : Level,
      HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v₁) ×'
      TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ ×'
      PLift (Nonempty (ConvT E n Γ A₁ A₂ (.sort u₁))) :=
  let ⟨v₁, hB₁⟩ := iotaStarKEta_codomain_sort_seed hW hΓ hA₁ hrhs₁
  let (hcDom, hcCod) := om_etaK_wrapper_X_materialize hW s₁ s₂ c₁ c₂ X
  ⟨v₁, hB₁, hcCod, ⟨convT_of_tyConvT_sort_of_sortUniq hW hSortUniq hΓ hA₁ hcDom⟩⟩

/-- For ANY `.conv`-wrapped root `ParRedT.iotaStarKEta` child step
    `EtaKAnnot.leftInput s_eta c₁` (`c₁ : TyConvT E n Γ (.pi A_eta B_eta) (.pi A B)`),
    evaluating `X : ∀ R : List (Jd E n), XProc R` on the original-wrapper
    request `om_etaK_wrapper_request s_eta s_k c₁ (.refl Γ (.pi A B))` and
    collapsing the domain conversion via `convT_of_tyConvT_sort_of_sortUniq`
    supplies `RootEtaKWrapperAlign A B (EtaKAnnot.leftInput s_eta c₁)` and
    joins the peak via `eta_lamK_full_joins_of_contract`. -/
theorem eta_lamK_wrapped_root_joins_of_X
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hSortUniq : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level},
      CtxWfT E n Γ' → HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v)
    (X : ∀ R : List (Jd E n), XProc R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f A A' B Tm rhs T : Expr Nat} {u v rl : Level} {afs : Prop}
    (w : IotaWitness E)
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hcA : ConvT E n Γ A A' (.sort u))
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
    (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
    (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hrhs : HasTyT E n (.assumption A :: Γ) rhs B)
    (hc : TyConvT E n Γ (.pi A B) T)
    (hNoPrf : ¬ HasRecProofRoot E n Γ w.recRef w.ls w.preMajor.length)
    (hContract : FieldfulKPeakContract E n Γ A B w happ rhs hι hrhs)
    {w_eta : IotaWitness E} {A_eta B_eta Tm_eta rhs_eta : Expr Nat}
    {u_eta rl_eta : Level} {afs_eta : Prop}
    (happ_eta : recCall (.const w_eta.recRef w_eta.ls) w_eta.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0))
    (hA_eta : HasTyT E n Γ A_eta (.sort u_eta))
    (hf_eta : HasTyT E n Γ f (.pi A_eta B_eta))
    (hrl_eta : piBody w_eta.famMember.mtype = .sort rl_eta)
    (hsel_eta : EliminationSelection rl_eta w_eta.nMinors afs_eta .anySort)
    (hfam_eta : ∃ lsF, (appsSpine Tm_eta).1 = .const w_eta.familyRef lsF)
    (hmajor_eta : HasTyT E n (.assumption A_eta :: Γ) (.bvar 0) Tm_eta)
    (hmk_eta : HasTyT E n (.assumption A_eta :: Γ) (ctorMajor w_eta) Tm_eta)
    (hTm0_eta : HasTyT E n (.assumption A_eta :: Γ) Tm_eta (.sort .zero))
    (hι_eta : DerivedIotaU E (iotaLhsOf w_eta) rhs_eta)
    (hlι_eta : HasTyT E n (.assumption A_eta :: Γ) (iotaLhsOf w_eta) B_eta)
    (hlhs_eta : HasTyT E n (.assumption A_eta :: Γ)
      (recCall (.const w_eta.recRef w_eta.ls) w_eta.preMajor (.bvar 0)) B_eta)
    (hrhs_eta : HasTyT E n (.assumption A_eta :: Γ) rhs_eta B_eta)
    (c₁ : TyConvT E n Γ (.pi A_eta B_eta) (.pi A B)) :
    ∃ z : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A_eta rhs_eta) z T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ (.lam A' rhs) z T) := by
  let s_eta : ParRedT (PEqLeafT E n) E n Γ f (.lam A_eta rhs_eta) (.pi A_eta B_eta) :=
    .iotaStarKEta Γ w_eta f A_eta B_eta Tm_eta rhs_eta u_eta rl_eta afs_eta
      happ_eta hA_eta hf_eta hrl_eta hsel_eta hfam_eta hmajor_eta hmk_eta hTm0_eta
      hι_eta hlι_eta hlhs_eta hrhs_eta
  let hf_TY : HasTyT E n Γ f (.pi A B) := hasTyT_of_tyConvT hf_eta c₁
  let s_k : ParRedT (PEqLeafT E n) E n Γ f (.lam A rhs) (.pi A B) :=
    .iotaStarKEta Γ w f A B Tm rhs u rl afs
      happ hA hf_TY hrl hsel hfam hmajor hmk hTm0 hι
      (stepped_hlι (envClosed_of_envWfT hW) rfl happ hA hB hf_TY hmajor hmk hTm0)
      (stepped_hlhs (envClosed_of_envWfT hW) happ hf_TY) hrhs
  let c₂ : TyConvT E n Γ (.pi A B) (.pi A B) := .refl Γ (.pi A B)
  let ⟨_, _, hcCod, ⟨hneDom⟩⟩ :=
    om_etaK_wrapper_X_semantic_align hW hSortUniq hΓ hA_eta hrhs_eta s_eta s_k c₁ c₂ X
  obtain ⟨hcDom⟩ := hneDom
  have hAlign : RootEtaKWrapperAlign A B (EtaKAnnot.leftInput s_eta c₁) := by
    dsimp [EtaKAnnot.leftInput, s_eta, RootEtaKWrapperAlign]
    by_cases hA_eq : A_eta = A
    · rw [if_pos hA_eq]
      by_cases hB_eq : B_eta = B
      · rw [if_pos hB_eq]; exact PUnit.unit
      · rw [if_neg hB_eq]; exact hcCod
    · rw [if_neg hA_eq]
      exact ⟨hcDom, hcCod⟩
  exact eta_lamK_full_joins_of_contract hW hΓ w happ hcA hA hB hrl hsel hfam
    hmajor hmk hTm0 hι hrhs hc (EtaKAnnot.leftInput s_eta c₁) hNoPrf hContract hAlign

end OMEtaKAnnot

#print axioms tyConvT_sort_transfer
#print axioms tyConvT_sort_eqN_of_sortUniq
#print axioms separationAt_of_sortUniq
#print axioms no_proof_root_commonIndex_of_sortUniq
#print axioms eval_imax_of_eq_zero
#print axioms hasTyT_app_sort_zero_inv
#print axioms hasTyT_foldApps_sort_zero_inv
#print axioms eqRecMtypeTy
#print axioms eval_instLevel_eqRecSort_of_eqN_one
#print axioms no_const65_proof_root_of_sortUniq
#print axioms minorLookupSortTy
#print axioms bvar1_type_sort_eqN_of_sortUniq
#print axioms no_contracted_proof_root_of_sortUniq
#print axioms conditionalNonJoin
#print axioms conditionalNonModuloJoin
#print axioms positive_body_conversion
#print axioms positive_expanded_conversion
#print axioms positive_conversion
#print axioms partial_rec_not_direct_K
#print axioms contracted_not_direct_eta
#print axioms oneAlt_eq
#print axioms alternate_constant_typing
#print axioms alternate_partial_typing
#print axioms alternate_partial_raw
#print axioms alternate_partial_step
#print axioms alternate_partial_ne
#print axioms alternate_partial_no_proof_roots
#print axioms positive_partial_not_literally_normal
#print axioms appsSpine_fst_instantiateLevels
#print axioms tyConvT_instLevels
#print axioms derivedIotaU_instLevels
#print axioms peqT_instLevels
#print axioms peqLeafT_instLevels
#print axioms parRedT_instLevels
#print axioms partialRec_to_contracted_at
#print axioms partialRec_to_contracted
#print axioms positive_peak_joined
#print axioms positive_join
#print axioms positive_modulo_join
#print axioms eta_lamK_step
#print axioms eta_lamK_peak_refl_data
#print axioms eta_lamK_peak_star_data
#print axioms eta_lamK_peak_joins
#print axioms eta_child_hf_step
#print axioms peqTWeaken
#print axioms peqLeafTWeaken
#print axioms tyConvT_ctx
#print axioms AssumpCtxConvT
#print axioms assumpCtxConvT_refl
#print axioms assumpCtxConvT_to_ctxConvT
#print axioms assumpCtxConvT_get_letBinding
#print axioms assumpCtxConvT_drop
#print axioms parRedT_assumpCtx
#print axioms assumpCtxConvT_of_convA
#print axioms instantiate_bvar_lift_succ
#print axioms replacePreMajorWitness
#print axioms replacePreMajorWitness_happ
#print axioms stepped_hlhs
#print axioms stepped_hlι
#print axioms HasRecProofRoot
#print axioms hasRecProofRoot_mono
#print axioms no_rec_proof_root_of_sortUniq
#print axioms witness_preMajor_length_eq
#print axioms witnessS_preMajor_length_eq
#print axioms short_witness_not_K_source
#print axioms short_witness_not_derivedIotaU
#print axioms witness_rec_not_delta
#print axioms RecArgStep
#print axioms RecArgsStep
#print axioms recArgsStep_refl
#print axioms recArgsStep_snoc
#print axioms recArgsStep_length
#print axioms recArgsStep_get
#print axioms peqT_rec_spine_decomp
#print axioms parRedT_rec_spine_decomp
#print axioms list_getElem?_map_inv
#print axioms list_getElem?_map_of_some
#print axioms minorPreImage
#print axioms introTypeSpine_lift
#print axioms MinorStepLift
#print axioms minorStepLift_of_introSpine
#print axioms minorStepLift_of_bvar
#print axioms minorStepLift_positive_a2
#print axioms eta_lamK_stepped_diamond_data
#print axioms eta_lamK_general_star_data
#print axioms eta_lamK_general_joins
#print axioms positive_stepped_eta_lamK_joins_of_sortUniq
#print axioms derivedIota_rhs_eq_iotaRhsOf
#print axioms iotaStarKEta_same_rec_preMajor
#print axioms iotaStarKEta_self_rhs_eq_of_fields_nil
#print axioms iotaStarKEta_self_actual_rhs_eq_of_fields_nil
#print axioms iotaStarKEta_self_rhs_eq_of_field_bvar0
#print axioms iotaStarKEta_self_actual_rhs_eq_of_field_bvar0
#print axioms UnguardedFieldfulK
#print axioms changedFields
#print axioms recPrefixTerm
#print axioms rhs_differ
#print axioms not_fieldful_contract
#print axioms CanonicalEtaKWitness
#print axioms witness_canonicalEtaKWitness
#print axioms wLoopK_canonicalEtaKWitness
#print axioms not_changedFields_canonicalEtaKWitness
#print axioms iotaStarKEta_self_rhs_eq_of_canonical
#print axioms iotaStarKEta_self_actual_rhs_eq_of_canonical
#print axioms wLoopK_changedFields_peq
#print axioms wLoopK_changedFields_typed_join
#print axioms parRedTStar_assumpCtx
#print axioms parRedTStar_lam_body
#print axioms parRedTStar_trans
#print axioms FIELDFUL_K
#print axioms iotaStarKEta_self_join_of_fieldfulK
#print axioms iotaStarKEta_self_join_of_fields_nil
#print axioms iotaStarKEta_self_join_of_canonical
#print axioms om_etaK_annot_piChain
#print axioms om_etaK_annot_request
#print axioms om_etaK_annot_piChain_strict
#print axioms om_etaK_annot_request_strict
#print axioms om_etaK_annot_edge_typings
#print axioms om_etaK_child_hf
#print axioms om_etaK_annot_bareU
#print axioms om_etaK_wrapper_request
#print axioms om_etaK_wrapper_edge
#print axioms om_etaK_wrapper_X_outputs_edge
#print axioms iotaArgs_nil_fields
#print axioms iotaOpenRhs_nil_fields
#print axioms iotaRhsOfS_fields_nil
#print axioms witness_witnessS_align
#print axioms derivedIotaU_rhs_eq_of_fields_nil_aux
#print axioms derivedIotaU_rhs_eq_of_fields_nil
#print axioms derivedIotaU_rhs_eq_iotaRhsOf_of_fields_nil
#print axioms iotaStarKEta_self_derivedIotaU_rhs_eq_of_fields_nil
#print axioms short_witness_not_etaK_source
#print axioms parRedT_rec_spine_lt_decomp
#print axioms IsRootEtaKStep
#print axioms isRootEtaKStep_target_is_lam
#print axioms not_isRootEtaKStep_of_noEtaKStep
#print axioms EtaKWrapper
#print axioms EtaKWrapper.extend
#print axioms RecPreMajorStep
#print axioms parRedT_rec_preMajor_classify
#print axioms NoWrappedRootEtaK
#print axioms noWrappedRootEtaK_of_not_isRootEtaKStep
#print axioms noWrappedRootEtaK_of_noEtaKStep
#print axioms classify_not_etaK_of_not_isRootEtaKStep
#print axioms classify_not_etaK_of_noEtaKStep
#print axioms not_wrapped_of_noWrappedRootEtaK
#print axioms FieldfulKPeakContract
#print axioms fieldfulKPeakContract_of_fields_nil
#print axioms WrappedPiDomainConv
#print axioms eta_lamK_full_star_data_of_contract
#print axioms eta_lamK_full_joins_of_contract
#print axioms eta_lamK_unwrapped_star_data_of_contract
#print axioms eta_lamK_full_star_data
#print axioms eta_lamK_full_joins
#print axioms eta_lamK_unwrapped_star_data
#print axioms eta_lamK_unwrapped_joins
#print axioms positive_full_eta_lamK_joins_of_sortUniq
#print axioms nonreflexiveEtaKChild
#print axioms etaWithNonreflexiveEtaKChild
#print axioms no_post_child_K_witness
#print axioms actualEtaKChildPeak
#print axioms actualEtaKChildPeak_join_refl
#print axioms positive_nonreflexiveEtaKChild_joins_of_sortUniq
#print axioms positive_stepped_nonreflexiveEtaKChild_joins_of_sortUniq
#print axioms RootEtaKDomainConv
#print axioms SameRootEtaKDomain
#print axioms rootEtaKDomainConv_of_same
#print axioms sameRootEtaKDomain_of_not_isRootEtaKStep
#print axioms sameRootEtaKDomain_of_noWrappedRootEtaK_aux
#print axioms sameRootEtaKDomain_of_noWrappedRootEtaK
#print axioms classify_etaK_dom
#print axioms emptyEnv_no_iotaWitness
#print axioms fieldfulK_emptyEnv
#print axioms eqEnvT_iotaWitness_nMinors_and_fields_nil
#print axioms eqEnvT_iotaWitness_canonical
#print axioms fieldfulK_eqEnvT
#print axioms CanonicalFIELDFUL_K
#print axioms canonicalFieldfulK
#print axioms pinLoopEnvT_iotaWitness_shape
#print axioms pinLoopEnvT_iotaWitness_field_rhs
#print axioms instPrefix_app
#print axioms instPrefix_const
#print axioms pinLoopEnvT_iotaWitnessS_shape
#print axioms pinLoopEnvT_derivedIotaU_rhs_eq_aux
#print axioms pinLoopEnvT_derivedIotaU_rhs_eq
#print axioms iotaStarKEta_self_join_of_canonical_pinLoopEnvT
#print axioms pinLoopEnvT_self_peq
#print axioms pinLoopEnvT_self_typed_join
#print axioms LoopMkDomainInv
#print axioms fieldfulK_pinLoopEnvT_of_mkDomInv
#print axioms wLoopK_bvar3
#print axioms not_wLoopK_bvar3_canonicalEtaKWitness
#print axioms wLoopK_bvar3_rhs_differ
#print axioms pinLoopTwoVarsOuterCtx
#print axioms pinLoopTwoVarsCtx
#print axioms pinLoopTwoVars_bvar0TyT
#print axioms pinLoopTwoVars_bvar3TyT
#print axioms pinLoopTwoVars_famTyT
#print axioms pinLoopTwoVars_outerFamTyT
#print axioms pinLoopTwoVars_codSortTyT
#print axioms pinLoopTwoVars_mk0TyT
#print axioms pinLoopTwoVars_mk3TyT
#print axioms pinLoopTwoVars_recPrefixTyT
#print axioms pinLoopTwoVars_lhsTyT
#print axioms pinLoopTwoVars_lhs3TyT
#print axioms pinLoopTwoVars_indexConv0
#print axioms pinLoopTwoVars_indexConv3
#print axioms pinLoopTwoVars_lhsI0TyT
#print axioms pinLoopTwoVars_lhsI3TyT
#print axioms pinLoopTwoVars_rhs0TyT
#print axioms pinLoopTwoVars_rhs3TyT
#print axioms pinParRedT_iotaStarKEta_loop0
#print axioms pinParRedT_iotaStarKEta_loop3
#print axioms wLoopK_bvar3_concrete_body_join
#print axioms wLoopK_bvar3_concrete_lam_join
#print axioms RootEtaKWrapperAlign
#print axioms SameRootEtaKPi
#print axioms rootEtaKWrapperAlign_of_same
#print axioms sameRootEtaKPi_of_not_isRootEtaKStep
#print axioms sameRootEtaKPi_of_noWrappedRootEtaK_aux
#print axioms sameRootEtaKPi_of_noWrappedRootEtaK
#print axioms classify_etaK_align
#print axioms rootEtaKWrapperAlign_of_wrappedPiDomainConv_aux
#print axioms rootEtaKWrapperAlign_of_wrappedPiDomainConv
#print axioms positive_fieldfulKPeakContract_of_sortUniq
#print axioms positive_full_eta_lamK_joins_via_contract_of_sortUniq
#print axioms wrappedNonreflexiveEtaKChild
#print axioms not_noWrappedRootEtaK_wrappedNonreflexiveEtaKChild
#print axioms positive_stepped_wrappedNonreflexiveEtaKChild_joins_of_sortUniq
#print axioms positive_wrappedNonreflexiveEtaKChild_joins_of_sortUniq
#print axioms domainBeta
#print axioms domainBeta_ne_domain
#print axioms domainBetaTy
#print axioms domainBeta_conv_domain
#print axioms piDomainBeta_conv_commonIndex
#print axioms partialRec_to_contracted_domainBeta
#print axioms wrappedDistinctDomainEtaKChild
#print axioms not_noWrappedRootEtaK_wrappedDistinctDomainEtaKChild
#print axioms not_sameRootEtaKDomain_wrappedDistinctDomainEtaKChild
#print axioms positive_stepped_wrappedDistinctDomainEtaKChild_joins_of_sortUniq
#print axioms positive_wrappedDistinctDomainEtaKChild_joins_of_sortUniq
#print axioms iotaStarKEta_codomain_sort_seed
#print axioms convT_of_tyConvT_sort_of_sortUniq
#print axioms om_etaK_wrapper_X_materialize
#print axioms om_etaK_wrapper_X_semantic_align
#print axioms eta_lamK_wrapped_root_joins_of_X

end Rcic.Declarative.F8EtaK
