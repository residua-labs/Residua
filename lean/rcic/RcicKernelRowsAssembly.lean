import rcic.RcicSynBelowCToRows
import rcic.RcicSynMSAP
import rcic.RcicSynTableNoHead
import rcic.RcicSynClauseAlg
import rcic.RcicArity
import rcic.RcicPiRowProj
import rcic.RcicPiRowSaturation
import rcic.RcicFamAppLeftInst
import rcic.RcicNativeFamilyProjection
import rcic.RcicNativeKProjection
import rcic.RcicNativeSortRetypeAudit
import rcic.RcicDTRowFields
import rcic.RcicIotaSRRowsTel

/-!
# Top-level assembly of the kernel rows (`TypedRowsWf`) from the three remaining named inputs

This module wires the landed pieces on `main` into a single conditional assembly for
every `hW : EnvWfT E`, conditional on **only** the three catalogued/requested inputs:
1. `hBel : AllBelowScoped E Aw (tableOf hW)` (`W-F8-SORTROW` / syntactic BelowC pack),
2. `joinPi : PiConvValleyData E n` (Π-conversion valley data; by `#7608`'s
   `nonempty_piConvValleyData_iff_piInj`, `Nonempty (PiConvValleyData E n)` is
   equivalent to `Nonempty (PiInj E n)` modulo `AllBelowScoped`), and
3. `hSlot : FamRelevantSlotConv E n` (`W-F8-FAMAPP-ARG-COMPARISON`, `#7525`'s
   `RelevantSlotConv` at the stored family domains).

Specifically:

1. **`sortRow` and `F8A2Support.SortUnique` from `AllBelowScoped` / `StepSuppliers`**:
   - `sortRow_of_allBelowScoped` / `sortRow_of_allBelowScoped_self` /
     `sortRow_of_allBelowScoped_build` / `sortRow_of_suppliers_envWfT` /
     `sortRow_of_suppliers_build`: discharges the `hMSAP` premise of
     `RcicSynBelowCToRows.sortRow_of_suppliers` unconditionally via
     `RcicSynMSAP.memberSortP_of_envWfT_ap`, and at `tbl = tableOf hW` discharges
     `TableWF (tableOf hW)` unconditionally via `RcicSynTableBuild.tableWF_build`.
   - `sortUnique_of_allBelowScoped_cts` / `sortUnique_of_allBelowScoped_cts_self`:
     supplies `F8A2Support.SortUnique E n` from the `BelowScoped.cts` field on a
     reflexive conversion (`CvP.refl D₂ D₂ D₂` vs `D₁`) with `AssumpPref` discharged by
     `enrichHasTyT_native_ap` (`#7608`, no `TableWF` required).
   - `sortUnique_of_allBelowScoped_eut_cl` / `sortUnique_of_allBelowScoped_eut_cl_build`:
     supplies `F8A2Support.SortUnique E n` from `BelowScoped.eut` and `BelowScoped.cl`
     via `RcicSynBelowScoped.sortCoh_of_allBelowScoped` at `σ = id`.

2. **`piRow` (`PiRowField E n`) wiring from `AllBelowScoped` + `PiConvValleyData`**:
   - `piRow_of_piValleyData_allBelowScoped_cts` and
     `piInj_of_piValleyData_allBelowScoped_cts_bit` /
     `piRow_of_piValleyData_allBelowScoped_cts_bit`: wires `#7608`'s
     `piInj_of_piValleyData_allBelowScoped_cts` (and the `bitCoh` variant) into
     `PiRowField E n`. Note: by `nonempty_piConvValleyData_iff_piInj`
     (`RcicNativePiValleyContract.lean:117`), `PiConvValleyData E n` is
     `Nonempty`-equivalent to `PiInj E n` under `AllBelowScoped`, so this step is an
     interface wiring / restatement, not a reduction of `piRow`.
   - `piRow_of_nativeValleys_allBelowScoped_cts` /
     `piRow_of_nativeValleys_allBelowScoped_eut_cl`: documents how `#7531`'s
     `weak_piRow_of_nativeValleys` receives its `F8A2Support.SortUnique E n` premise
     from `AllBelowScoped`. Note: `NativeConvValleys E n` is **refuted** at the
     canonical admitted instance `trueEnvU` by `#7608`'s `admitted_no_nativeConvValleys`
     (`RcicNativeKValleyAudit.lean:64`); these two declarations are historical/diagnostic
     bridges for `#7531` and are not used by the headline assembly.

3. **`famAppRow` modulo `FamRelevantSlotConv` (`W-F8-FAMAPP-ARG-COMPARISON`)**:
   - Reuses the landed `piDomsOf` (`RcicIotaShapeAdapter`), `piTailOf`, `piResult`
     (`RcicFamRef`), `isArity_piResult_sort` (`RcicArity`),
     `policyPi_piDomsOf_piTailOf` (`RcicIATypedMinor`), and
     `Rcic.Declarative.instantiateLevels_policyPi` (`RcicIotaSRRowsTel`).
   - `eps_enrichHasTyT_foldApps_const`, `eps_enrichHasTyT_of_envWfT_foldApps_const`,
     and `eps_enrichHasTyT_sort_ne_star`: proves that for any sort-typed family spine
     `HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)`, its enriched erasure at
     `σ = id`, `ρ = S.can id` is non-`.star` (via `pbit_of_allBelowScoped`) and
     therefore has the form `ETm.appN (.const r ls) es` for some list `es` of kept
     erased arguments.
   - `famApp_eqNList_of_allBelowScoped_wf` and
     `famApp_eqNList_of_allBelowScoped_build`: **discharges `eqNList ls ls'` from
     `AllBelowScoped E Aw (tableOf hW)` alone** (without any family-valley hypothesis)
     by erasing `TyConvT` into `ConvMod (EStep (tableOf hW)) LvlEq` via
     `esChain_of_allBelowScoped` + `convMod_of_tyCvP_esChain` and applying the landed
     `RcicSynTableNoHead.convE_appN_const_inv_build`.
   - `famAppSaturation_of_allBelowScoped_piRow_wf` and
     `famAppSaturation_of_allBelowScoped_piRow_build`: constructs `#7525`'s
     `FamAppSaturation E r m ls ls' xs xs'` from `AllBelowScoped` and `PiRowField`
     alone (via `famApp_eqNList_of_allBelowScoped_build` for `eqNList ls ls'` and
     `#7569`'s `famApp_saturated_of_piRow_scoped` for argument-list lengths).
   - `FamRelevantSlotConv E n` + `famAppRow_of_allBelowScoped_piValleyData_slotConv_build`:
     produces `TypedRowsWf.famAppRow` via `#7525`'s
     `famAppRow_of_piRow_saturation_slotConv`, adding Prop-slot irrelevance (`ConvT.irr`),
     arity saturation (`#7569`), and level-list equality (`convE_appN_const_inv_build`)
     on top of the relevant-slot comparison port `FamRelevantSlotConv E n`.

4. **Top-level kernel-row and census assembly (`tableOf hW`)**:
   - `typedRowsWf_of_allBelowScoped_piValleyData_slotConv`: full `TypedRowsWf E n` from
     only `hBel : AllBelowScoped E Aw (tableOf hW)`, `joinPi : PiConvValleyData E n`,
     and `hSlot : FamRelevantSlotConv E n` (`TableWF` and `NoHeadRule` discharged at
     `tableOf hW` via `tableWF_build` and `built_no_family_rule`).
   - `typedRowsWf_of_suppliers_piValleyData_slotConv`: `StepSuppliers`-fronted variant
     feeding `RcicSynBelowCToRows.typedRowsWf_of_suppliers`.
   - Downstream corollaries at `tableOf hW` for DT-021, DT-012, DT-010, DT-011, DT-019,
     and IA-024.

`closure_claim = 0`. No remaining input is asserted inhabited here.
-/

namespace Rcic.Declarative.KernelRowsAssembly

open Rcic.Syn
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.NativeKProjectionAudit
open Rcic.Declarative.NativeValleys.NativeSortRetypeAudit

/-! ## §1 — `sortRow` and `F8A2Support.SortUnique` from `AllBelowScoped` / `StepSuppliers` -/

/-- `TypedRowsWf.sortRow` from `AllBelowScoped` and `TableWF`: enriches the native
    `TyConvT` chain, discharges `hMSAP` unconditionally via
    `RcicSynMSAP.memberSortP_of_envWfT_ap`, assembles the scoped `ESChain` via
    `esChain_of_allBelowScoped`, and closes with `sortRow_of_tyCvP_esChain_id`. -/
theorem sortRow_of_allBelowScoped {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl) (hTbl : TableWF tbl)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (h : TyConvT E n Γ (.sort u) (.sort v)) : eqN u v :=
  let S : ScopedCtx Eₐ E n Γ := ⟨hW, hext, hΓ⟩
  sortRow_of_tyCvP_esChain_id hTbl (enrichTyConvT_of_envWfT hW hΓ h) (S.can id)
    (esChain_of_allBelowScoped hBel S levelHom_id _
      (enrichTyConvT_of_envWfT_allAP hW (memberSortP_of_envWfT_ap hW) hΓ h)
      (TyP.sort E n Γ u (.succ u) (eqN_refl _)) trivial
      (TyP.sort E n Γ v (.succ v) (eqN_refl _)) trivial)

/-- Self-scoped `sortRow_of_allBelowScoped` (`Eₐ = E`, `hext = envExt_refl E`). -/
theorem sortRow_of_allBelowScoped_self {E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl) (hTbl : TableWF tbl)
    (hW : EnvWfT E) {n : Nat} : NativeFamilyProjection.SortRow E n :=
  fun {_} hΓ {_ _} h => sortRow_of_allBelowScoped hBel hTbl hW (envExt_refl E) hΓ h

/-- `TypedRowsWf.sortRow` at the canonical derived table `tableOf hW`, with
    `TableWF (tableOf hW)` discharged by `RcicSynTableBuild.tableWF_build`. -/
theorem sortRow_of_allBelowScoped_build {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW)) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_allBelowScoped_self hBel (tableWF_build hW) hW

/-- `StepSuppliers`-fronted `sortRow` with `hMSAP` discharged by
    `memberSortP_of_envWfT_ap`: delegates directly to
    `RcicSynBelowCToRows.sortRow_of_suppliers`. -/
theorem sortRow_of_suppliers_envWfT {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  fun {_} hΓ {_ _} h => sortRow_of_suppliers hTbl W hW hext (memberSortP_of_envWfT_ap hW) hΓ h

/-- `StepSuppliers`-fronted `sortRow` at the canonical derived table `tableOf hW`, with
    both `TableWF (tableOf hW)` and `hMSAP` discharged unconditionally. -/
theorem sortRow_of_suppliers_build {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (W : StepSuppliers Aw (tableOf hW) E) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_suppliers_envWfT (tableWF_build hW) W hW (envExt_refl E)

/-- **How `F8A2Support.SortUnique` is supplied from `AllBelowScoped` (Route 1: `CTS`)**:
    Given `h₁ : HasTyT E n Γ T (.sort u)` and `h₂ : HasTyT E n Γ T (.sort v)`, enrich
    both derivations via `enrichHasTyT_of_envWfT`, discharge their `AssumpPref` receipts
    via `#7608`'s `enrichHasTyT_native_ap` (`memberSortP_of_envWfT_ap` + `letCtxConvP_ap`),
    and query `BelowScoped.cts` on the reflexive conversion
    `CvP.refl E n Γ T (.sort v) D₂ D₂ D₂` against `D₁` at scope `⟨hW, hext, hΓ⟩`
    (`sortLevels_of_allBelowScoped_cts`). Requires no `TableWF`. -/
theorem sortUnique_of_allBelowScoped_cts {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl) (hext : EnvExt E Eₐ)
    {n : Nat} : F8A2Support.SortUnique E n :=
  fun hW {_ _ _ _} hΓ h₁ h₂ =>
    sortLevels_of_allBelowScoped_cts hBel ⟨hW, hext, hΓ⟩
      (enrichHasTyT_of_envWfT hW hΓ h₁)
      (enrichHasTyT_of_envWfT hW hΓ h₂)
      (enrichHasTyT_native_ap hW hΓ h₁)
      (enrichHasTyT_native_ap hW hΓ h₂)

/-- Self-scoped `F8A2Support.SortUnique` via `#7608`'s `sortUniq_of_allBelowScoped_cts`. -/
theorem sortUnique_of_allBelowScoped_cts_self {E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl) {n : Nat} :
    F8A2Support.SortUnique E n :=
  fun hW {_ _ _ _} hΓ h₁ h₂ =>
    sortUniq_of_allBelowScoped_cts hW hBel hΓ h₁ h₂

/-- **How `F8A2Support.SortUnique` is supplied from `AllBelowScoped` (Route 2: `EUT + 2×CL`)**:
    Enrich both sort typings with `enrichHasTyT_native_ap` and apply
    `RcicSynBelowScoped.sortCoh_of_allBelowScoped` at `σ = id` (which combines
    `eut_of_allBelowScoped` with two `cl_of_allBelowScoped` regularity queries under
    `TableWF tbl`). -/
theorem sortUnique_of_allBelowScoped_eut_cl {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl) (hTbl : TableWF tbl)
    (hext : EnvExt E Eₐ) {n : Nat} : F8A2Support.SortUnique E n :=
  fun hW {_ _ _ _} hΓ h₁ h₂ =>
    sortCoh_of_allBelowScoped hBel hTbl ⟨hW, hext, hΓ⟩ levelHom_id
      (enrichHasTyT_of_envWfT hW hΓ h₁)
      (enrichHasTyT_of_envWfT hW hΓ h₂)
      (enrichHasTyT_native_ap hW hΓ h₁)
      (enrichHasTyT_native_ap hW hΓ h₂)

/-- Route 2 (`EUT + 2×CL`) specialized to the canonical derived table `tableOf hW`. -/
theorem sortUnique_of_allBelowScoped_eut_cl_build {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW)) {n : Nat} :
    F8A2Support.SortUnique E n :=
  sortUnique_of_allBelowScoped_eut_cl hBel (tableWF_build hW) (envExt_refl E)

/-! ## §2 — `piRow` (`PiRowField E n`) wiring from `AllBelowScoped` + `PiConvValleyData` -/

/-- `PiInj E n` from `PiConvValleyData E n` and `AllBelowScoped E Aw tbl`, combining
    `#7608`'s `sortRetype_of_allBelowScoped_cts` (from the `CTS` field) and
    `zeroSortCoherence_of_allBelowScoped_bit` (from the `bitCoh` field).
    Note: by `nonempty_piConvValleyData_iff_piInj` (`RcicNativePiValleyContract.lean:117`),
    `Nonempty (PiConvValleyData E n) ↔ Nonempty (PiInj E n)` under `AllBelowScoped`. -/
def piInj_of_piValleyData_allBelowScoped_cts_bit {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} (joinPi : PiConvValleyData E n)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl) :
    PiInj E n :=
  piInj_of_piValleyData_sortRetype hW joinPi
    (sortRetype_of_allBelowScoped_cts hW hBel)
    (zeroSortCoherence_of_allBelowScoped_bit hBel (envExt_refl E))

/-- `PiRowField E n` (`TypedRowsWf.piRow`) wired from `PiConvValleyData E n` and
    `AllBelowScoped E Aw tbl` via `#7608`'s `piInj_of_piValleyData_allBelowScoped_cts`.
    Note: by `nonempty_piConvValleyData_iff_piInj`, `PiConvValleyData E n` is
    `Nonempty`-equivalent to `PiInj E n` modulo `AllBelowScoped E Aw tbl` (no reduction
    of `piRow`). -/
theorem piRow_of_piValleyData_allBelowScoped_cts {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} (joinPi : PiConvValleyData E n)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl) :
    PiRowField E n :=
  piRow_of_piInj (piInj_of_piValleyData_allBelowScoped_cts hW joinPi hBel)

/-- `PiRowField E n` (`TypedRowsWf.piRow`) wired from `PiConvValleyData E n` and
    `AllBelowScoped E Aw tbl` via `piInj_of_piValleyData_allBelowScoped_cts_bit`. -/
theorem piRow_of_piValleyData_allBelowScoped_cts_bit {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} (joinPi : PiConvValleyData E n)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl) :
    PiRowField E n :=
  piRow_of_piInj (piInj_of_piValleyData_allBelowScoped_cts_bit hW joinPi hBel)

/-- Historical/diagnostic bridge for `#7531` (`weak_piRow_of_nativeValleys`): supplies
    its `F8A2Support.SortUnique` premise via `sortUnique_of_allBelowScoped_cts`
    (Route 1, no `TableWF`).
    **Disclosure**: the unrestricted `NativeConvValleys E n` premise is **refuted** at
    the canonical admitted instance `(trueEnvU, 0)` by `#7608`'s
    `admitted_no_nativeConvValleys` (`RcicNativeKValleyAudit.lean:64`); the headline
    assembly below uses `PiConvValleyData E n` instead. -/
theorem piRow_of_nativeValleys_allBelowScoped_cts {Eₐ E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl)
    (hext : EnvExt E Eₐ) {n : Nat} (join : NativeConvValleys E n) :
    PiRowField E n :=
  weak_piRow_of_nativeValleys hW (sortUnique_of_allBelowScoped_cts hBel hext) join

/-- Historical/diagnostic bridge for `#7531` (`weak_piRow_of_nativeValleys`): supplies
    its `F8A2Support.SortUnique` premise via `sortUnique_of_allBelowScoped_eut_cl`
    (Route 2, `EUT + 2×CL` under `TableWF`).
    **Disclosure**: `NativeConvValleys E n` is **refuted** at `(trueEnvU, 0)` by
    `#7608`'s `admitted_no_nativeConvValleys` (`RcicNativeKValleyAudit.lean:64`). -/
theorem piRow_of_nativeValleys_allBelowScoped_eut_cl {Eₐ E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl)
    (hTbl : TableWF tbl) (hext : EnvExt E Eₐ) {n : Nat}
    (join : NativeConvValleys E n) :
    PiRowField E n :=
  weak_piRow_of_nativeValleys hW (sortUnique_of_allBelowScoped_eut_cl hBel hTbl hext) join

/-! ## §3 — Stored arity telescopes, erased family rigidity (`eqNList`), saturation (`#7569`),
    and `famAppRow` modulo `FamRelevantSlotConv` (`#7525`) -/

private theorem piTailOf_eq_piResult : (t : Expr Nat) → piTailOf t = piResult t
  | .pi _ B => piTailOf_eq_piResult B
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .letE _ _ _ | .lit _ => rfl

/-- For any plain typing derivation `h : HasTyT E₁ n Γ e T` of a constant-headed
    application spine `e = foldApps (.const r ls) args`, if its enriched erasure
    `(enrichHasTyT hcl hext hm hlet C h).eps σ ρ` is not `.star`, then it is an
    erased spine `ETm.appN (.const r (ls.map σ)) es` for some list `es : List ETm`
    of kept erased arguments.
    Non-`.star` status propagates from the root of the spine to the head `.const`
    across `.conv` (identity on `.eps`) and `.app` (`eps_app_star_iff`). -/
theorem eps_enrichHasTyT_foldApps_const {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n) :
    {Γ : LCtx} → (C : CtxP E n Γ) → {e T : Expr Nat} → (h : HasTyT E₁ n Γ e T) →
    (r : Nat) → (ls : List Level) → (args : List (Expr Nat)) →
    e = foldApps (.const r ls) args →
    ∀ {σ : Level → Level} {ρ : List Disp},
      (enrichHasTyT hcl hext hm hlet C h).eps σ ρ ≠ .star →
      ∃ es : List ETm,
        (enrichHasTyT hcl hext hm hlet C h).eps σ ρ = ETm.appN (.const r (ls.map σ)) es
  | Γ, C, _, _, .const _ r' ls' m hres hlen hwf, r, ls, args, he, σ, ρ, hne => by
      have hc := (foldApps_const_residual he rfl).1
      injection hc with hr hls
      subst hr; subst hls
      dsimp only [enrichHasTyT] at hne ⊢
      cases hu : levelIsZero (σ (instMemberSortP hcl hm Γ (hext r' m hres) hlen hwf).1) with
      | true => exact False.elim (hne (eps_const_proof hu))
      | false => exact ⟨[], eps_const_rel hu⟩
  | Γ, C, _, _, .app _ f a A B hf ha, r, ls, args, he, σ, ρ, hne => by
      have hnef : (enrichHasTyT hcl hext hm hlet C hf).eps σ ρ ≠ .star :=
        fun hst => hne (by dsimp only [enrichHasTyT]; simp only [TyP.eps, hst])
      obtain ⟨es, hes⟩ :=
        eps_enrichHasTyT_foldApps_const hcl hext hm hlet C hf r ls (appsSpine f).2
          (foldApps_const_of_app he) hnef
      have hns : ETm.appN (.const r (ls.map σ)) es ≠ .star :=
        appN_ne_star es (.const r (ls.map σ)) (by intro h; cases h)
      dsimp only [enrichHasTyT]
      rw [eps_app_appClause, hes]
      by_cases ha_star : (enrichHasTyT hcl hext hm hlet C ha).eps σ ρ = .star
      · rw [ha_star, appClause_right_star]
        exact ⟨es, rfl⟩
      · rw [appClause_app hns ha_star, ← ETm.appN_snoc]
        exact ⟨es ++ [(enrichHasTyT hcl hext hm hlet C ha).eps σ ρ], rfl⟩
  | Γ, C, _, _, .conv _ _ _ _ _ h₀ _, r, ls, args, he, _, _, hne =>
      eps_enrichHasTyT_foldApps_const hcl hext hm hlet C h₀ r ls args he hne
  | _, _, _, _, .sort _ _, _, _, _, he, _, _, _ =>
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, _, .bvar _ _ _ _, _, _, _, he, _, _, _ =>
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, _, .pi _ _ _ _ _ _ _, _, _, _, he, _, _, _ =>
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, _, .lam _ _ _ _ _ _ _, _, _, _, he, _, _, _ =>
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _, _, _, _, he, _, _, _ =>
      nomatch (foldApps_const_residual he rfl).1
  | _, _, _, _, .lit _ _ _ _, _, _, _, he, _, _, _ =>
      nomatch (foldApps_const_residual he rfl).1

/-- `EnvWfT`-fronted `eps_enrichHasTyT_foldApps_const` at `σ = id`. -/
theorem eps_enrichHasTyT_of_envWfT_foldApps_const {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {ls : List Level} {xs : List (Expr Nat)} {T : Expr Nat}
    (h : HasTyT E n Γ (foldApps (.const r ls) xs) T)
    {ρ : List Disp}
    (hne : (enrichHasTyT_of_envWfT hW hΓ h).eps id ρ ≠ .star) :
    ∃ es : List ETm,
      (enrichHasTyT_of_envWfT hW hΓ h).eps id ρ = ETm.appN (.const r ls) es := by
  obtain ⟨es, hes⟩ :=
    eps_enrichHasTyT_foldApps_const (envClosed_of_envWfT hW) (envExt_refl E)
      (memberSortP_of_envWfT hW) (letCtxConvP_of_envWfT hW)
      (enrichCtxWfT_of_envWfT hW hΓ) h r ls xs rfl hne
  rw [List.map_id] at hes
  exact ⟨es, hes⟩

/-- Under `AllBelowScoped`, any sort-typed derivation `h : HasTyT E n Γ A (.sort w)`
    erases to a non-`.star` term at `σ = id`, `ρ = S.can id`: `pbit_of_allBelowScoped`
    against `TyP.sort E n Γ w (.succ w)` equates `.star`-erasure with
    `levelIsZero (.succ w) = true`, which is `false`. -/
theorem eps_enrichHasTyT_sort_ne_star {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level}
    (h : HasTyT E n Γ A (.sort w)) :
    let S : ScopedCtx Eₐ E n Γ := ⟨hW, hext, hΓ⟩
    (enrichHasTyT_of_envWfT hW hΓ h).eps id (S.can id) ≠ .star := by
  intro S hst
  have hpb := pbit_of_allBelowScoped hBel S levelHom_id
    (enrichHasTyT_of_envWfT hW hΓ h)
    (TyP.sort E n Γ w (.succ w) (eqN_refl _))
    (enrichHasTyT_native_ap hW hΓ h) trivial
  have hz : levelIsZero (.succ w) = true := hpb.mp hst
  exact Bool.noConfusion hz

/-- **Level-list rigidity (`eqNList ls ls'`) from `AllBelowScoped` alone (general `tbl`)**:
    Under `AllBelowScoped Eₐ Aw tbl`, `TableWF tbl`, and `NoHeadRule tbl r`, any native
    `TyConvT` between sort-typed applications of `r` erases via `esChain_of_allBelowScoped`
    and `convMod_of_tyCvP_esChain` into a `ConvMod (EStep tbl) LvlEq` between two
    `ETm.appN (.const r ls) es` spines (`eps_enrichHasTyT_of_envWfT_foldApps_const` +
    `eps_enrichHasTyT_sort_ne_star`), from which `convE_appN_const_inv_wf` extracts
    `eqNList ls ls'`. Requires no family-valley or `piRow` hypothesis. -/
theorem famApp_eqNList_of_allBelowScoped_wf {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScoped Eₐ Aw tbl) (hTbl : TableWF tbl)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hNoHead : NoHeadRule tbl r)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' := by
  let S : ScopedCtx Eₐ E n Γ := ⟨hW, hext, hΓ⟩
  let ⟨_, htyR⟩ := tyConvT_rhsSort hW hΓ h ⟨w, hty⟩
  have hesc := esChain_of_allBelowScoped hBel S levelHom_id
    (enrichTyConvT_of_envWfT hW hΓ h)
    (enrichTyConvT_of_envWfT_allAP hW (memberSortP_of_envWfT_ap hW) hΓ h)
    (enrichHasTyT_of_envWfT hW hΓ hty) (enrichHasTyT_native_ap hW hΓ hty)
    (enrichHasTyT_of_envWfT hW hΓ htyR) (enrichHasTyT_native_ap hW hΓ htyR)
  have hmod := convMod_of_tyCvP_esChain hesc
  obtain ⟨es, hes⟩ := eps_enrichHasTyT_of_envWfT_foldApps_const hW hΓ hty
    (eps_enrichHasTyT_sort_ne_star hBel hW hext hΓ hty)
  obtain ⟨es', hes'⟩ := eps_enrichHasTyT_of_envWfT_foldApps_const hW hΓ htyR
    (eps_enrichHasTyT_sort_ne_star hBel hW hext hΓ htyR)
  rw [hes, hes'] at hmod
  exact (convE_appN_const_inv_wf hTbl hNoHead hmod).1

/-- **Level-list rigidity (`eqNList ls ls'`) at the canonical table `tableOf hW`**:
    instantiates `famApp_eqNList_of_allBelowScoped_wf` at `tbl := tableOf hW`, with
    `TableWF (tableOf hW)` discharged by `tableWF_build hW` and
    `NoHeadRule (tableOf hW) r` discharged by `built_no_family_rule hW hm hind`. -/
theorem famApp_eqNList_of_allBelowScoped_build {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW)) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' :=
  famApp_eqNList_of_allBelowScoped_wf hBel (tableWF_build hW) hW (envExt_refl E) hΓ
    (built_no_family_rule hW hm hind) hty h

/-- Construct `#7525`'s `FamAppSaturation E r m ls ls' xs xs'` package from
    `AllBelowScoped E Aw tbl`, `TableWF tbl`, `NoHeadRule tbl r`, and `PiRowField E n`
    via `famApp_eqNList_of_allBelowScoped_wf` and `#7569`'s
    `famApp_saturated_of_piRow_scoped` on both application spines (no family-valley
    premise). -/
noncomputable def famAppSaturation_of_allBelowScoped_piRow_wf {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) (hTbl : TableWF tbl)
    {n : Nat} (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hNoHead : NoHeadRule tbl r)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    FamAppSaturation E r m ls ls' xs xs' :=
  let har := NativeFamilyProjection.familyArity_of_envWfT hW r m hm hind
  let u₀ := (isArity_piResult_sort m.mtype har).1
  let doms := (piDomsOf m.mtype).map (instantiateLevels ls)
  let doms' := (piDomsOf m.mtype).map (instantiateLevels ls')
  let u := instLevel ls u₀
  let u' := instLevel ls' u₀
  have hpol0 : m.mtype = policyPi (piDomsOf m.mtype) (.sort u₀) := by
    have h1 := (policyPi_piDomsOf_piTailOf m.mtype).symm
    rw [piTailOf_eq_piResult, (isArity_piResult_sort m.mtype har).2] at h1
    exact h1
  let telL : instantiateLevels ls m.mtype = policyPi doms (.sort u) :=
    (congrArg (instantiateLevels ls) hpol0).trans
      (Rcic.Declarative.instantiateLevels_policyPi ls (piDomsOf m.mtype) (.sort u₀))
  let telR : instantiateLevels ls' m.mtype = policyPi doms' (.sort u') :=
    (congrArg (instantiateLevels ls') hpol0).trans
      (Rcic.Declarative.instantiateLevels_policyPi ls' (piDomsOf m.mtype) (.sort u₀))
  let S : ScopedCtx E E n Γ := ⟨hW, envExt_refl E, hΓ⟩
  let ⟨_, htyR⟩ := tyConvT_rhsSort hW hΓ h ⟨w, hty⟩
  { doms := doms
    doms' := doms'
    U := .sort u
    U' := .sort u'
    telL := telL
    telR := telR
    eqN := famApp_eqNList_of_allBelowScoped_wf hBel hTbl hW (envExt_refl E) hΓ hNoHead hty h
    lenDD := by simp only [doms, doms', List.length_map]
    lenXD := (famApp_saturated_of_piRow_scoped hBel hTbl S hpi hm hind telL hty).symm
    lenXD' := (famApp_saturated_of_piRow_scoped hBel hTbl S hpi hm hind telR htyR).symm }

/-- Construct `#7525`'s `FamAppSaturation E r m ls ls' xs xs'` at the canonical table
    `tableOf hW` from `AllBelowScoped E Aw (tableOf hW)` and `PiRowField E n` alone
    (`TableWF` and `NoHeadRule` discharged by `tableWF_build` and `built_no_family_rule`). -/
noncomputable def famAppSaturation_of_allBelowScoped_piRow_build {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    FamAppSaturation E r m ls ls' xs xs' :=
  famAppSaturation_of_allBelowScoped_piRow_wf hW hBel (tableWF_build hW) hpi hΓ hm hind
    (built_no_family_rule hW hm hind) hty h

/-- The catalogued relevant-slot comparison input (`W-F8-FAMAPP-ARG-COMPARISON`,
    `#7525`'s `RelevantSlotConv` at the canonical stored-type domains
    `(piDomsOf m.mtype).map (instantiateLevels ls)`). -/
def FamRelevantSlotConv (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level},
    E.members r = some m → m.mclass = .inductiveM →
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') →
    RelevantSlotConv E n Γ [] ((piDomsOf m.mtype).map (instantiateLevels ls)) xs xs'

/-- `TypedRowsWf.famAppRow` (`FamAppRowLink E n`) assembled at a general table `tbl`
    from `AllBelowScoped E Aw tbl`, `TableWF tbl`, family `NoHeadRule`, `PiRowField E n`,
    and `FamRelevantSlotConv E n` via `famApp_eqNList_of_allBelowScoped_wf`, `#7569`
    (`famApp_saturated_of_piRow_scoped`), and `#7525`
    (`famAppRow_of_piRow_saturation_slotConv`). -/
theorem famAppRow_of_piRow_allBelowScoped_slotConv_wf {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) (hTbl : TableWF tbl)
    (hNoHead : ∀ {r : Nat} {m : CheckedMember},
      E.members r = some m → m.mclass = .inductiveM → NoHeadRule tbl r)
    {n : Nat} (hpi : PiRowField E n)
    (hSlot : FamRelevantSlotConv E n) : FamAppRowLink E n :=
  fun {_} hΓ {_ _ _ _ _ _ _} hm hind hty h =>
    famAppRow_of_piRow_saturation_slotConv hpi hW hΓ
      (famAppSaturation_of_allBelowScoped_piRow_wf hW hBel hTbl hpi hΓ hm hind
        (hNoHead hm hind) hty h)
      (hSlot hΓ hm hind hty h) hm hind hty h

/-- `TypedRowsWf.famAppRow` (`FamAppRowLink E n`) at the canonical derived table
    `tableOf hW`, assembled from `AllBelowScoped E Aw (tableOf hW)`, `PiRowField E n`,
    and `FamRelevantSlotConv E n` alone (`TableWF` and `NoHeadRule` discharged by
    `tableWF_build` and `built_no_family_rule`). -/
theorem famAppRow_of_piRow_allBelowScoped_slotConv_build {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (hpi : PiRowField E n)
    (hSlot : FamRelevantSlotConv E n) : FamAppRowLink E n :=
  famAppRow_of_piRow_allBelowScoped_slotConv_wf hW hBel (tableWF_build hW)
    (fun hm hind => built_no_family_rule hW hm hind) hpi hSlot

/-- `TypedRowsWf.famAppRow` at the canonical derived table `tableOf hW`, assembled
    directly from the three remaining inputs `AllBelowScoped E Aw (tableOf hW)`,
    `PiConvValleyData E n`, and `FamRelevantSlotConv E n`. -/
theorem famAppRow_of_allBelowScoped_piValleyData_slotConv_build {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : FamAppRowLink E n :=
  famAppRow_of_piRow_allBelowScoped_slotConv_build hW hBel
    (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel) hSlot

/-! ## §4 — Top-level assembly of `TypedRowsWf` and downstream census rows -/

/-- **Two-row kernel assembly (`sortRow` ∧ `piRow`, general `tbl`)**: for every
    `hW : EnvWfT E`, `AllBelowScoped E Aw tbl`, `TableWF tbl`, and
    `PiConvValleyData E n` produce both `TypedRowsWf.sortRow` and `TypedRowsWf.piRow`. -/
theorem sortRow_and_piRow_of_allBelowScoped_piValleyData {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) (hTbl : TableWF tbl)
    {n : Nat} (joinPi : PiConvValleyData E n) :
    NativeFamilyProjection.SortRow E n ∧ PiRowField E n :=
  ⟨sortRow_of_allBelowScoped_self hBel hTbl hW,
   piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel⟩

/-- **Two-row kernel assembly (`sortRow` ∧ `piRow`) at `tableOf hW`**: requires only
    `AllBelowScoped E Aw (tableOf hW)` and `PiConvValleyData E n` (`TableWF` discharged
    by `tableWF_build hW`). -/
theorem sortRow_and_piRow_of_allBelowScoped_piValleyData_build {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n) :
    NativeFamilyProjection.SortRow E n ∧ PiRowField E n :=
  sortRow_and_piRow_of_allBelowScoped_piValleyData hW hBel (tableWF_build hW) joinPi

/-- **Headline `TypedRowsWf E n` assembly from the three remaining named inputs**:
    for every `hW : EnvWfT E`, `AllBelowScoped E Aw (tableOf hW)`,
    `PiConvValleyData E n`, and `FamRelevantSlotConv E n` (`W-F8-FAMAPP-ARG-COMPARISON`)
    assemble all three fields of `TypedRowsWf E n` (`TableWF` and `NoHeadRule` at
    `tableOf hW` discharged internally by `tableWF_build` and `built_no_family_rule`). -/
theorem typedRowsWf_of_allBelowScoped_piValleyData_slotConv {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel
  famAppRow := famAppRow_of_allBelowScoped_piValleyData_slotConv_build hW hBel joinPi hSlot

/-- General-table variant of `typedRowsWf_of_allBelowScoped_piValleyData_slotConv`. -/
theorem typedRowsWf_of_allBelowScoped_piValleyData_slotConv_wf {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped E Aw tbl) (hTbl : TableWF tbl)
    (hNoHead : ∀ {r : Nat} {m : CheckedMember},
      E.members r = some m → m.mclass = .inductiveM → NoHeadRule tbl r)
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_self hBel hTbl hW
  piRow := piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel
  famAppRow := famAppRow_of_piRow_allBelowScoped_slotConv_wf hW hBel hTbl hNoHead
    (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel) hSlot

/-- **`StepSuppliers`-fronted full `TypedRowsWf E n` assembly at `tableOf hW`**: feeds
    `allBelowScoped_of_suppliers Aw (tableOf hW) (tableWF_build hW) W` and
    `memberSortP_of_envWfT_ap hW` into `RcicSynBelowCToRows.typedRowsWf_of_suppliers`. -/
theorem typedRowsWf_of_suppliers_piValleyData_slotConv {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (W : StepSuppliers Aw (tableOf hW) E)
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n :=
  let hTbl := tableWF_build hW
  let hBel := allBelowScoped_of_suppliers Aw (tableOf hW) hTbl W
  typedRowsWf_of_suppliers hTbl W hW (envExt_refl E) (memberSortP_of_envWfT_ap hW)
    (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel)
    (famAppRow_of_allBelowScoped_piValleyData_slotConv_build hW hBel joinPi hSlot)

/-- **DT-021** (no cumulativity) from `AllBelowScoped E Aw tbl` + `TableWF tbl` alone. -/
theorem dt021_of_allBelowScoped {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl)
    (hTbl : TableWF tbl) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} {T : Expr Nat} (hc : ConvT E n Γ (.sort u) (.sort v) T) :
    eqN u v :=
  DT021T_no_cumulativity_of_sortRow hW (sortRow_of_allBelowScoped_self hBel hTbl hW) hΓ hc

/-- **DT-021** (no cumulativity) at `tableOf hW` from `AllBelowScoped E Aw (tableOf hW)`
    alone (`TableWF` discharged by `tableWF_build hW`). -/
theorem dt021_of_allBelowScoped_build {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} {T : Expr Nat} (hc : ConvT E n Γ (.sort u) (.sort v) T) :
    eqN u v :=
  dt021_of_allBelowScoped hW hBel (tableWF_build hW) hΓ hc

/-- **DT-012** (type uniqueness) from `AllBelowScoped E Aw tbl` + `TableWF tbl` +
    `PiConvValleyData E n` (where `PiConvValleyData E n` is `Nonempty`-equivalent to
    `PiInj E n` modulo `AllBelowScoped` by `nonempty_piConvValleyData_iff_piInj`). -/
theorem dt012_of_allBelowScoped_piValleyData {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScoped E Aw tbl)
    (hTbl : TableWF tbl) {n : Nat} (joinPi : PiConvValleyData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_self hBel hTbl hW)
    (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel) hΓ hA hB

/-- **DT-012** (type uniqueness) at `tableOf hW` from `AllBelowScoped E Aw (tableOf hW)`
    and `PiConvValleyData E n` alone (`TableWF` discharged by `tableWF_build hW`). -/
theorem dt012_of_allBelowScoped_piValleyData_build {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  dt012_of_allBelowScoped_piValleyData hW hBel (tableWF_build hW) joinPi hΓ hA hB

/-- **DT-010** (one-step subject reduction) at `tableOf hW` from the three remaining
    inputs `AllBelowScoped E Aw (tableOf hW)`, `PiConvValleyData E n`, and
    `FamRelevantSlotConv E n`. -/
theorem dt010_of_allBelowScoped_piValleyData_slotConv {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv hW hBel joinPi hSlot)
    hΓ h hs

/-- **DT-011** (multi-step subject reduction) at `tableOf hW` from the three remaining
    inputs `AllBelowScoped E Aw (tableOf hW)`, `PiConvValleyData E n`, and
    `FamRelevantSlotConv E n`. -/
theorem dt011_of_allBelowScoped_piValleyData_slotConv {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv hW hBel joinPi hSlot)
    hΓ h hs

/-- **DT-019** (typed ι subject reduction) at `tableOf hW` from the three remaining
    inputs `AllBelowScoped E Aw (tableOf hW)`, `PiConvValleyData E n`, and
    `FamRelevantSlotConv E n`. -/
theorem dt019_of_allBelowScoped_piValleyData_slotConv {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv hW hBel joinPi hSlot)
    hΓ hd hlhs

/-- **IA-024** (`IotaSRTN`) at `tableOf hW` from the three remaining inputs
    `AllBelowScoped E Aw (tableOf hW)`, `PiConvValleyData E n`, and
    `FamRelevantSlotConv E n`. -/
theorem ia024_of_allBelowScoped_piValleyData_slotConv {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv hW hBel joinPi hSlot)

end Rcic.Declarative.KernelRowsAssembly

#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_of_allBelowScoped
#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_of_allBelowScoped_self
#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_of_allBelowScoped_build
#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_of_suppliers_envWfT
#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_of_suppliers_build
#print axioms Rcic.Declarative.KernelRowsAssembly.sortUnique_of_allBelowScoped_cts
#print axioms Rcic.Declarative.KernelRowsAssembly.sortUnique_of_allBelowScoped_cts_self
#print axioms Rcic.Declarative.KernelRowsAssembly.sortUnique_of_allBelowScoped_eut_cl
#print axioms Rcic.Declarative.KernelRowsAssembly.sortUnique_of_allBelowScoped_eut_cl_build
#print axioms Rcic.Declarative.KernelRowsAssembly.piInj_of_piValleyData_allBelowScoped_cts_bit
#print axioms Rcic.Declarative.KernelRowsAssembly.piRow_of_piValleyData_allBelowScoped_cts
#print axioms Rcic.Declarative.KernelRowsAssembly.piRow_of_piValleyData_allBelowScoped_cts_bit
#print axioms Rcic.Declarative.KernelRowsAssembly.piRow_of_nativeValleys_allBelowScoped_cts
#print axioms Rcic.Declarative.KernelRowsAssembly.piRow_of_nativeValleys_allBelowScoped_eut_cl
#print axioms Rcic.Declarative.KernelRowsAssembly.eps_enrichHasTyT_foldApps_const
#print axioms Rcic.Declarative.KernelRowsAssembly.eps_enrichHasTyT_of_envWfT_foldApps_const
#print axioms Rcic.Declarative.KernelRowsAssembly.eps_enrichHasTyT_sort_ne_star
#print axioms Rcic.Declarative.KernelRowsAssembly.famApp_eqNList_of_allBelowScoped_wf
#print axioms Rcic.Declarative.KernelRowsAssembly.famApp_eqNList_of_allBelowScoped_build
#print axioms Rcic.Declarative.KernelRowsAssembly.famAppSaturation_of_allBelowScoped_piRow_wf
#print axioms Rcic.Declarative.KernelRowsAssembly.famAppSaturation_of_allBelowScoped_piRow_build
#print axioms Rcic.Declarative.KernelRowsAssembly.FamRelevantSlotConv
#print axioms Rcic.Declarative.KernelRowsAssembly.famAppRow_of_piRow_allBelowScoped_slotConv_wf
#print axioms Rcic.Declarative.KernelRowsAssembly.famAppRow_of_piRow_allBelowScoped_slotConv_build
#print axioms Rcic.Declarative.KernelRowsAssembly.famAppRow_of_allBelowScoped_piValleyData_slotConv_build
#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_and_piRow_of_allBelowScoped_piValleyData
#print axioms Rcic.Declarative.KernelRowsAssembly.sortRow_and_piRow_of_allBelowScoped_piValleyData_build
#print axioms Rcic.Declarative.KernelRowsAssembly.typedRowsWf_of_allBelowScoped_piValleyData_slotConv
#print axioms Rcic.Declarative.KernelRowsAssembly.typedRowsWf_of_allBelowScoped_piValleyData_slotConv_wf
#print axioms Rcic.Declarative.KernelRowsAssembly.typedRowsWf_of_suppliers_piValleyData_slotConv
#print axioms Rcic.Declarative.KernelRowsAssembly.dt021_of_allBelowScoped
#print axioms Rcic.Declarative.KernelRowsAssembly.dt021_of_allBelowScoped_build
#print axioms Rcic.Declarative.KernelRowsAssembly.dt012_of_allBelowScoped_piValleyData
#print axioms Rcic.Declarative.KernelRowsAssembly.dt012_of_allBelowScoped_piValleyData_build
#print axioms Rcic.Declarative.KernelRowsAssembly.dt010_of_allBelowScoped_piValleyData_slotConv
#print axioms Rcic.Declarative.KernelRowsAssembly.dt011_of_allBelowScoped_piValleyData_slotConv
#print axioms Rcic.Declarative.KernelRowsAssembly.dt019_of_allBelowScoped_piValleyData_slotConv
#print axioms Rcic.Declarative.KernelRowsAssembly.ia024_of_allBelowScoped_piValleyData_slotConv
