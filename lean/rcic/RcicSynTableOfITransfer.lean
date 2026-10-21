import rcic.RcicKernelRowsAssembly
import rcic.RcicNativeFamModelK
import rcic.RcicSynStepFieldsDeltaIota

/-!
# RcicSynTableOfITransfer — PART 4 of the `tableOfI` team: transfer

The wall (`#7709`): `tableOf` (`RcicSynTableBuild.lean:126`) emits no ι rules for `.group`
nodes, so `AllBelowScoped`/`StepSuppliers` are false on `tableOf natEnvUWfT`
(`natSucc_not_allBelowScoped_closed`). PART 1 builds `tableOfI` = `tableOf`'s entries ++
the erased ι rules of every admitted group; PARTs 2–3 prove `TableWF (tableOfI hW)`.
**This module is the transfer lane**: every landed theorem that mentions `tableOf hW`
itself gets a `*_tableI` version at a table satisfying the interface below — and every
theorem already parametric in `tbl` transfers for free.

## The interface (`TableOfICompat`)

The tableOf-pinned theorems internally discharge exactly three table facts:
1. `TableWF (tableOf hW)` — via `tableWF_build` (`RcicSynTableBuild.lean:222`);
   for `tableOfI` this is PARTs 2–3's `tableWFI_build` (`TableOfICompat.wf`).
2. `NoHeadRule (tableOf hW) r` at admitted family heads — via `built_no_family_rule`
   (`RcicSynTableNoHead.lean:77`), which works because every `tableOf` head is a
   `.definitionM` member. ι rules are headed at `.recursorM` refs — never `.inductiveM` —
   so the same `NoHeadRule` survives on the extended table (`TableOfICompat.headM`).
3. `ρ ∈ tableOf hW` membership facts (`deltaRule_mem_tableOf`) — via
   `TableOfICompat.sup` (`tableOf hW ⊆ tblI`).

When PART 1 lands `tableOfI`/`iotaRulesOf` and PARTs 2–3 land `tableWFI_build`, ONE
inhabitant `TableOfICompat hW (tableOfI hW)` instantiates every `*_tableI` theorem at
the real table; `tableOfICompat_of_recHeaded` covers the expected
`tableOf hW ++ ιrs` shape (each `ρ ∈ ιrs` headed at a `.recursorM` member — the
`natSuccRule` shape, `RcicSynNatSuccIota.lean:154`).

## The `tableOf hW` census (what transfers, what does not)

Parametric-in-`tbl` (transfer for free — listed, not restated):
`sortRow_of_allBelowScoped`, `sortRow_of_suppliers` (`RcicSynBelowCToRows`),
`typedRowsWf_of_suppliers`, `famApp_eqNList_of_allBelowScoped_wf`,
`famAppSaturation_of_allBelowScoped_piRow_wf`,
`famAppRow_of_piRow_allBelowScoped_slotConv_wf`,
`typedRowsWf_of_allBelowScoped_piValleyData_slotConv_wf`,
`dt021_of_allBelowScoped`, `dt012_of_allBelowScoped_piValleyData`,
`sortRow_of_suppliers_envWfT`, `sortUnique_of_allBelowScoped_cts`,
`sortUnique_of_allBelowScoped_cts_self`, `sortUnique_of_allBelowScoped_eut_cl`,
`sortRow_and_piRow_of_allBelowScoped_piValleyData`,
`delta_kept_caseStep_of_obs_ih` (`RcicSynStepFieldsDeltaIota`), and every
`RcicSynTableWF`/field lemma over `tbl`.

`tableOf hW`-pinned (ported here as `*_tableI`): `sortRow_of_allBelowScoped_build`,
`sortRow_of_suppliers_build`, `sortUnique_of_allBelowScoped_eut_cl_build`,
`famApp_eqNList_of_allBelowScoped_build`,
`famAppSaturation_of_allBelowScoped_piRow_build`,
`famAppRow_of_piRow_allBelowScoped_slotConv_build`,
`famAppRow_of_allBelowScoped_piValleyData_slotConv_build`,
`sortRow_and_piRow_of_allBelowScoped_piValleyData_build`,
`typedRowsWf_of_allBelowScoped_piValleyData_slotConv`,
`typedRowsWf_of_suppliers_piValleyData_slotConv`,
`dt021_of_allBelowScoped_build`, `dt012_of_allBelowScoped_piValleyData_build`,
`dt010/dt011/dt019/ia024_of_allBelowScoped_piValleyData_slotConv`
(`RcicKernelRowsAssembly`); `built_no_family_rule`, `convE_appN_const_inv_build`
(`RcicSynTableNoHead`); `deltaRule_mem_tableOf`, `delta_kept_caseStep_tableOf`
(`RcicSynStepFieldsDeltaIota`); and the `RcicNativeFamModel`/`RcicNativeFamModelK`
assemblies `typedRowsWf_of_allBelowScoped_<variant>` +
`dt012/dt010/dt011/dt019/ia024_of_allBelowScoped_<variant>` for
`variant ∈ {LRFamINT, TermFamIN, TermFamIN_core, TermFamIND, TermFamINDBot,
TermFamINDBotDI, TermFamINDBotR, LRFamINBotRK, LRFamINProbeRK, LRFamKT}` plus the
`*_slotPEq_reflect`/`*_slotFin_reflect` suppliers.

Builder-side (PART 1–3's `tableOfI`, not restated): `tableOf` itself,
`buildTableSyntax`, `tableOf_<ctor>` equations, `head_mem_build`,
`major_none_tableOf`, `tableWF_build`, and its six `tableOf_<field>` projections
(`RcicSynTableWF`); the `tableOfI` fields are `tableWFI_build`'s projections.

Deliberately not transferred (δ-only diagnostics that are FALSE by design at `tableOfI`,
kept on `tableOf` as evidence): `iotaRecursor_noHeadRule_tableOf`,
`iotaRetained_no_croot_tableOf` (`RcicSynClosedIotaret`),
`natSucc_not_es_tableOf_closed`, `natSucc_simulation_tableOf_refuted`,
`envWfT_allBelowScoped_tableOf_producer_refuted` (`RcicSynBelowPortsTableObstruction`),
`eutLamPorts_tableOf_empty_refuted` (`RcicSynCensusCorePortRefutations`).
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.KernelRowsAssembly
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelIrrAudit
open Rcic.Declarative.NativeValleys.NativeKProjectionAudit

/-! ## §1 — the PART-4 interface and its two constructors -/

/-- The facts a `tableOfI`-style table must carry for the transfer: it extends
    `tableOf hW` (`sup`), it is well-formed (`wf` — PARTs 2–3's deliverable), and no
    rule head resolves to an `.inductiveM` member (`headM` — δ heads are
    `.definitionM` by `head_defM_build`; ι heads are `.recursorM` by PART 1's spec). -/
structure TableOfICompat {E : ResolvedEnv} (hW : EnvWfT E) (tblI : List CRule) :
    Prop where
  sup : ∀ ρ ∈ tableOf hW, ρ ∈ tblI
  wf : TableWF tblI
  headM : ∀ ρ ∈ tblI, ∃ m, E.members ρ.head = some m ∧ m.mclass ≠ .inductiveM

/-- Every `tableOf hW` head is a `.definitionM` member — `head_defM_build` restated
    in the `headM` shape. -/
theorem headM_tableOf {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ ρ ∈ tableOf hW, ∃ m, E.members ρ.head = some m ∧ m.mclass ≠ .inductiveM :=
  fun ρ hρ =>
    let ⟨m, hm, hmc⟩ := head_defM_build hW ρ hρ
    ⟨m, hm, fun h => MemberClass.noConfusion (h.symm.trans hmc)⟩

/-- `headM` for `tableOf hW ++ ιrs`: the δ half by `head_defM_build`, the ι half
    when every ι rule is headed at a `.recursorM` member (the `natSuccRule` shape). -/
theorem headM_append_recHeaded {E : ResolvedEnv} (hW : EnvWfT E) {ιrs : List CRule}
    (hι : ∀ ρ ∈ ιrs, ∃ m, E.members ρ.head = some m ∧ m.mclass = .recursorM) :
    ∀ ρ ∈ tableOf hW ++ ιrs,
      ∃ m, E.members ρ.head = some m ∧ m.mclass ≠ .inductiveM :=
  fun ρ hρ =>
    (List.mem_append.mp hρ).elim (headM_tableOf hW ρ) fun h =>
      let ⟨m, hm, hmc⟩ := hι ρ h
      ⟨m, hm, fun h => MemberClass.noConfusion (h.symm.trans hmc)⟩

/-- Concrete `TableOfICompat` for the `tableOf hW ++ ιrs` shape: the `TableWF` is the
    team's `tableWFI_build`-side input; the recursor-head fact is PART 1's
    `iotaRulesOf` provenance. -/
theorem tableOfICompat_of_recHeaded {E : ResolvedEnv} (hW : EnvWfT E)
    {ιrs : List CRule} (hwf : TableWF (tableOf hW ++ ιrs))
    (hι : ∀ ρ ∈ ιrs, ∃ m, E.members ρ.head = some m ∧ m.mclass = .recursorM) :
    TableOfICompat hW (tableOf hW ++ ιrs) where
  sup := fun _ρ hρ => List.mem_append_left _ hρ
  wf := hwf
  headM := headM_append_recHeaded hW hι

/-- `built_no_family_rule` at a `tableOfI`-style table: an `.inductiveM` member ref is
    never a rule head, because every rule head resolves to a member of a different
    class and member refs are unique. -/
theorem built_no_family_rule_tableI {E : ResolvedEnv} (hW : EnvWfT E)
    {tblI : List CRule} (I : TableOfICompat hW tblI) {f : Nat}
    {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) : NoHeadRule tblI f := by
  intro ρ hρ hhead
  rcases I.headM ρ hρ with ⟨m, hm, hmc⟩
  rw [hhead] at hm
  rcases Option.some.inj (hm.symm.trans hf)
  exact hmc hclass

/-- `convE_appN_const_inv_wf` at a `tableOfI`-style table: erased family rigidity
    (`eqNList` + arities + pointwise `ConvMod`) for a real admitted family, with
    `TableWF`/`NoHeadRule` discharged by the interface. -/
theorem convE_appN_const_inv_tableI {E : ResolvedEnv} (hW : EnvWfT E)
    {tblI : List CRule} (I : TableOfICompat hW tblI) {f : Nat}
    {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep tblI) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep tblI) LvlEq) xs ys :=
  convE_appN_const_inv_wf I.wf (built_no_family_rule_tableI hW I hf hclass) h

/-- `deltaRule_mem_tableOf` at a `tableOfI`-style table: the δ rule is still a member
    because `tblI` extends `tableOf hW`. -/
theorem deltaRule_mem_tableI {E : ResolvedEnv} (hEnv : EnvWfT E)
    {tblI : List CRule} (I : TableOfICompat hEnv tblI)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    deltaRule r (deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr) ∈ tblI :=
  I.sup _ (deltaRule_mem_tableOf hEnv hres hbody htr)

/-! ## §2 — `RcicKernelRowsAssembly` transfers -/

/-- `sortRow_of_allBelowScoped_build` at a `tableOfI`-style table. -/
theorem sortRow_of_allBelowScoped_tableI {E : ResolvedEnv} (hW : EnvWfT E)
    {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_allBelowScoped_self hBel I.wf hW

/-- `sortRow_of_suppliers_build` at a `tableOfI`-style table. -/
theorem sortRow_of_suppliers_tableI {E : ResolvedEnv} (hW : EnvWfT E)
    {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (W : StepSuppliers Aw tblI E) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_suppliers_envWfT I.wf W hW (envExt_refl E)

/-- `sortUnique_of_allBelowScoped_eut_cl_build` at a `tableOfI`-style table. -/
theorem sortUnique_of_allBelowScoped_eut_cl_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI) {n : Nat} :
    F8A2Support.SortUnique E n :=
  sortUnique_of_allBelowScoped_eut_cl hBel I.wf (envExt_refl E)

/-- `famApp_eqNList_of_allBelowScoped_build` at a `tableOfI`-style table:
    `NoHeadRule tblI r` discharged by `built_no_family_rule_tableI`. -/
theorem famApp_eqNList_of_allBelowScoped_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' :=
  famApp_eqNList_of_allBelowScoped_wf hBel I.wf hW (envExt_refl E) hΓ
    (built_no_family_rule_tableI hW I hm hind) hty h

/-- `famAppSaturation_of_allBelowScoped_piRow_build` at a `tableOfI`-style table. -/
noncomputable def famAppSaturation_of_allBelowScoped_piRow_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    FamAppSaturation E r m ls ls' xs xs' :=
  famAppSaturation_of_allBelowScoped_piRow_wf hW hBel I.wf hpi hΓ hm hind
    (built_no_family_rule_tableI hW I hm hind) hty h

/-- `famAppRow_of_piRow_allBelowScoped_slotConv_build` at a `tableOfI`-style table. -/
theorem famAppRow_of_piRow_allBelowScoped_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (hpi : PiRowField E n)
    (hSlot : FamRelevantSlotConv E n) : FamAppRowLink E n :=
  famAppRow_of_piRow_allBelowScoped_slotConv_wf hW hBel I.wf
    (fun hm hind => built_no_family_rule_tableI hW I hm hind) hpi hSlot

/-- `famAppRow_of_allBelowScoped_piValleyData_slotConv_build` at a `tableOfI`-style
    table. -/
theorem famAppRow_of_allBelowScoped_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : FamAppRowLink E n :=
  famAppRow_of_piRow_allBelowScoped_slotConv_tableI hW I hBel
    (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel) hSlot

/-- `sortRow_and_piRow_of_allBelowScoped_piValleyData_build` at a `tableOfI`-style
    table. -/
theorem sortRow_and_piRow_of_allBelowScoped_piValleyData_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n) :
    NativeFamilyProjection.SortRow E n ∧ PiRowField E n :=
  sortRow_and_piRow_of_allBelowScoped_piValleyData hW hBel I.wf joinPi

/-- `typedRowsWf_of_allBelowScoped_piValleyData_slotConv` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_piValleyData_slotConv_wf hW hBel I.wf
    (fun hm hind => built_no_family_rule_tableI hW I hm hind) joinPi hSlot

/-- `typedRowsWf_of_suppliers_piValleyData_slotConv` at a `tableOfI`-style table. -/
theorem typedRowsWf_of_suppliers_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (W : StepSuppliers Aw tblI E)
    {n : Nat} (joinPi : PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n :=
  let hTbl := I.wf
  let hBel := allBelowScoped_of_suppliers Aw tblI hTbl W
  typedRowsWf_of_suppliers hTbl W hW (envExt_refl E) (memberSortP_of_envWfT_ap hW)
    (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel)
    (famAppRow_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi hSlot)

/-- `dt021_of_allBelowScoped_build` at a `tableOfI`-style table. -/
theorem dt021_of_allBelowScoped_tableI {E : ResolvedEnv} (hW : EnvWfT E)
    {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} {T : Expr Nat} (hc : ConvT E n Γ (.sort u) (.sort v) T) :
    eqN u v :=
  dt021_of_allBelowScoped hW hBel I.wf hΓ hc

/-- `dt012_of_allBelowScoped_piValleyData_build` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_piValleyData_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  dt012_of_allBelowScoped_piValleyData hW hBel I.wf joinPi hΓ hA hB

/-- `dt010_of_allBelowScoped_piValleyData_slotConv` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi hSlot)
    hΓ h hs

/-- `dt011_of_allBelowScoped_piValleyData_slotConv` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi hSlot)
    hΓ h hs

/-- `dt019_of_allBelowScoped_piValleyData_slotConv` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi hSlot)
    hΓ hd hlhs

/-- `ia024_of_allBelowScoped_piValleyData_slotConv` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_piValleyData_slotConv_tableI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : PiConvValleyData E n) (hSlot : FamRelevantSlotConv E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi hSlot)

/-! ## §3 — `RcicSynStepFieldsDeltaIota` transfer -/

/-- `delta_kept_caseStep_tableOf` at a `tableOfI`-style table: the canonical
    `deltaRule` membership transfers through `I.sup`. -/
theorem delta_kept_caseStep_tableI
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    {tblI : List CRule} (I : TableOfICompat S.env tblI)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref)
    (hL : Goal tblI (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)))
    (hB : Goal tblI
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ))) :
    CaseStep Aw tblI
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ (S.can σ)) := by
  intro hq ih
  exact delta_kept_caseStep_of_obs_ih Aw tblI hres hbody htr hlen hwf hb dl dr
    S σ (S.can σ) hu hag hap (S.canDispForHom hq.hom).1
    (deltaRule_mem_tableI S.env I hres hbody htr) hL hB hq ih

/-! ## §4 — `RcicNativeFamModel` transfers -/

/-- `famRelevantSlotConv_of_allBelowScoped_piRow_slotPEq_reflect` at a `tableOfI`-style
    table. -/
theorem famRelevantSlotConv_of_allBelowScoped_piRow_slotPEq_reflect_tableI
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI) {n : Nat} (hprow : PiRowField E n)
    (hslotPEq : FamSlotPEqSoundnessCtxI E n)
    (hrefl : PEqIRelevantSlotReflect E n) :
    FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty h
  intro i x x' d u hx hx' hd hdT hu
  simp only [List.nil_append] at hdT ⊢
  let sat := famAppSaturation_of_allBelowScoped_piRow_tableI hW I hBel hprow hΓ hm hind hty h
  have hlenAA : xs.length = xs'.length :=
    sat.lenXD.symm.trans (sat.lenDD.trans sat.lenXD')
  have hbotL : ApproxI (ctxEnvI Γ) (foldApps (.const r ls) xs) (.spine r (botVecI xs)) :=
    approxI_famApp_botVecI (ctxEnvI Γ) r ls xs
  have hbotR : ApproxI (ctxEnvI Γ) (foldApps (.const r ls') xs') (.spine r (botVecI xs)) :=
    approxI_famApp_botVecI_of_length_eq (ctxEnvI Γ) r ls' hlenAA
  obtain ⟨⟨_, _, hargsL, _⟩⟩ :=
    hasTyT_spineInv_rows hW hprow hΓ hm sat.telL xs sat.lenXD hty
  have hxT : HasTyT E n Γ x (instPrefix (xs.take i) d) := hargsL i x d hx hd
  have hpEq : PEqI E (ctxEnvI Γ) (instPrefix (xs.take i) d) x x' :=
    hslotPEq hΓ hm hind hty h i x x' d hx hx' hd
  exact hrefl hΓ hm hind hty h hbotL hbotR i x x' d u hx hx' hd hdT hu hxT hpEq

/-- `famRelevantSlotConv_of_allBelowScoped_piRow_slotFin_reflect` at a `tableOfI`-style
    table. -/
theorem famRelevantSlotConv_of_allBelowScoped_piRow_slotFin_reflect_tableI
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI) {n : Nat} (hprow : PiRowField E n)
    (hslotFin : FamSlotSemEqFinSoundness E n)
    (hrefl : SemEqFinRelevantSlotReflect E n) :
    FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty h
  intro i x x' d u hx hx' hd hdT hu
  simp only [List.nil_append] at hdT ⊢
  let sat := famAppSaturation_of_allBelowScoped_piRow_tableI hW I hBel hprow hΓ hm hind hty h
  have hlenAA : xs.length = xs'.length :=
    sat.lenXD.symm.trans (sat.lenDD.trans sat.lenXD')
  have hbotL : ApproxFin (ctxEnvFin Γ) (foldApps (.const r ls) xs) (.spine r (botVecFin xs)) :=
    approxFin_famApp_botVecFin (ctxEnvFin Γ) r ls xs
  have hbotR : ApproxFin (ctxEnvFin Γ) (foldApps (.const r ls') xs') (.spine r (botVecFin xs)) :=
    approxFin_famApp_botVecFin_of_length_eq (ctxEnvFin Γ) r ls' hlenAA
  obtain ⟨⟨_, _, hargsL, _⟩⟩ :=
    hasTyT_spineInv_rows hW hprow hΓ hm sat.telL xs sat.lenXD hty
  have hxT : HasTyT E n Γ x (instPrefix (xs.take i) d) := hargsL i x d hx hd
  have hsem : SemEqFin (ctxEnvFin Γ) x x' :=
    hslotFin hΓ hm hind hty h i x x' d u hx hx' hd hdT hu
  exact hrefl hΓ hm hind hty h hbotL hbotR i x x' d u hx hx' hd hdT hu hxT hsem

/-- `typedRowsWf_of_allBelowScoped_piValleyData_slotPEq_reflect` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_piValleyData_slotPEq_reflect_tableI
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : Rcic.Declarative.NativeValleys.NativeKProjectionAudit.PiConvValleyData E n)
    (hslotPEq : FamSlotPEqSoundnessCtxI E n)
    (hrefl : PEqIRelevantSlotReflect E n) :
    TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi
    (famRelevantSlotConv_of_allBelowScoped_piRow_slotPEq_reflect_tableI hW I hBel
      (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel) hslotPEq hrefl)

/-- `typedRowsWf_of_allBelowScoped_piValleyData_slotFin_reflect` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_piValleyData_slotFin_reflect_tableI
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (joinPi : Rcic.Declarative.NativeValleys.NativeKProjectionAudit.PiConvValleyData E n)
    (hslotFin : FamSlotSemEqFinSoundness E n)
    (hrefl : SemEqFinRelevantSlotReflect E n) :
    TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW I hBel joinPi
    (famRelevantSlotConv_of_allBelowScoped_piRow_slotFin_reflect_tableI hW I hBel
      (piRow_of_piValleyData_allBelowScoped_cts hW joinPi hBel) hslotFin hrefl)

/-- `typedRowsWf_of_allBelowScoped_fundamentalLRFamINT` at a `tableOfI`-style table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINT E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalLRFamINT hW F
  famAppRow := famAppRow_of_fundamentalLRFamINT hW F

/-- `dt012_of_allBelowScoped_fundamentalLRFamINT` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalLRFamINT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalLRFamINT hW F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalLRFamINT` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalLRFamINT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINT hW I hBel F) hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalLRFamINT` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalLRFamINT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINT hW I hBel F) hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalLRFamINT` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalLRFamINT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINT hW I hBel F) hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalLRFamINT` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalLRFamINT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINT E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINT hW I hBel F)

/-- `typedRowsWf_of_allBelowScoped_fundamentalTermFamIN` at a `tableOfI`-style table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIN {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) {n : Nat}
    (hS : ShallowTypeSoundnessCtxI E n) (F : FundamentalTermFamIN E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalTermFamIN hW hdet hS F
  famAppRow := famAppRow_of_fundamentalTermFamIN hW hdet hS F

/-- `typedRowsWf_of_allBelowScoped_fundamentalTermFamIN_core` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIN_core
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIN E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalTermFamIN_core hW hdet hcore F
  famAppRow := famAppRow_of_fundamentalTermFamIN_core hW hdet hcore F

/-- `dt012_of_allBelowScoped_fundamentalTermFamIN_core` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalTermFamIN_core {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIN E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalTermFamIN_core hW hdet hcore F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalTermFamIN_core` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalTermFamIN_core {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIN E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIN_core hW I hBel
      hdet hcore F) hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalTermFamIN_core` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalTermFamIN_core {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIN E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIN_core hW I hBel
      hdet hcore F) hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalTermFamIN_core` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalTermFamIN_core {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIN E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIN_core hW I hBel
      hdet hcore F) hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalTermFamIN_core` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalTermFamIN_core {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIN E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIN_core hW I hBel
      hdet hcore F)

/-- `typedRowsWf_of_allBelowScoped_fundamentalTermFamIND` at a `tableOfI`-style table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIND {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIND E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalTermFamIND hW hdet hcore F
  famAppRow := famAppRow_of_fundamentalTermFamIND hW hdet hcore F

/-- `dt012_of_allBelowScoped_fundamentalTermFamIND` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalTermFamIND {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIND E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalTermFamIND hW hdet hcore F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalTermFamIND` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalTermFamIND {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIND E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIND hW I hBel
      hdet hcore F) hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalTermFamIND` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalTermFamIND {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIND E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIND hW I hBel
      hdet hcore F) hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalTermFamIND` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalTermFamIND {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIND E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIND hW I hBel
      hdet hcore F) hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalTermFamIND` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalTermFamIND {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hdet : WhDet E) (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamIND E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamIND hW I hBel
      hdet hcore F)

/-- `typedRowsWf_of_allBelowScoped_fundamentalTermFamINDBot` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBot {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    (hcore : WhApproxInvCore E) {n : Nat}
    (F : FundamentalTermFamINDBot E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalTermFamINDBot hW hcore F
  famAppRow := famAppRow_of_fundamentalTermFamINDBot hW hcore F

/-- `typedRowsWf_of_allBelowScoped_fundamentalTermFamINDBotDI` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI) {n : Nat}
    (F : FundamentalTermFamINDBotDI E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalTermFamINDBotDI hW F
  famAppRow := famAppRow_of_fundamentalTermFamINDBotDI hW F

/-- `dt012_of_allBelowScoped_fundamentalTermFamINDBotDI` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalTermFamINDBotDI hW F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalTermFamINDBotDI` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI hW I hBel F)
    hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalTermFamINDBotDI` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI hW I hBel F)
    hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalTermFamINDBotDI` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI hW I hBel F)
    hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalTermFamINDBotDI` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotDI E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotDI hW I hBel F)

/-- `typedRowsWf_of_allBelowScoped_fundamentalTermFamINDBotR` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotR
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI) {n : Nat}
    (F : FundamentalTermFamINDBotR E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalTermFamINDBotR hW F
  famAppRow := famAppRow_of_fundamentalTermFamINDBotR hW F

/-- `dt012_of_allBelowScoped_fundamentalTermFamINDBotR` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalTermFamINDBotR {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotR E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalTermFamINDBotR hW F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalTermFamINDBotR` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalTermFamINDBotR {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotR E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotR hW I hBel F)
    hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalTermFamINDBotR` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalTermFamINDBotR {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotR E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotR hW I hBel F)
    hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalTermFamINDBotR` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalTermFamINDBotR {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotR E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotR hW I hBel F)
    hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalTermFamINDBotR` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalTermFamINDBotR {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalTermFamINDBotR E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalTermFamINDBotR hW I hBel F)

/-- `typedRowsWf_of_allBelowScoped_fundamentalLRFamINBotRK` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINBotRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINBotRK E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalLRFamINBotRK hW F
  famAppRow := famAppRow_of_fundamentalLRFamINBotRK hW F

/-- `dt012_of_allBelowScoped_fundamentalLRFamINBotRK` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalLRFamINBotRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINBotRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalLRFamINBotRK hW F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalLRFamINBotRK` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalLRFamINBotRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINBotRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINBotRK hW I hBel F)
    hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalLRFamINBotRK` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalLRFamINBotRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINBotRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINBotRK hW I hBel F)
    hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalLRFamINBotRK` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalLRFamINBotRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINBotRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINBotRK hW I hBel F)
    hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalLRFamINBotRK` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalLRFamINBotRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINBotRK E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINBotRK hW I hBel F)

/-- `typedRowsWf_of_allBelowScoped_fundamentalLRFamINProbeRK` at a `tableOfI`-style
    table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK
    {E : ResolvedEnv} (hW : EnvWfT E) {tblI : List CRule}
    (I : TableOfICompat hW tblI) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw tblI) {n : Nat}
    (F : FundamentalLRFamINProbeRK E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalLRFamINProbeRK hW F
  famAppRow := famAppRow_of_fundamentalLRFamINProbeRK hW F

/-- `dt012_of_allBelowScoped_fundamentalLRFamINProbeRK` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINProbeRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalLRFamINProbeRK hW F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalLRFamINProbeRK` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINProbeRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK hW I hBel F)
    hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalLRFamINProbeRK` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINProbeRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK hW I hBel F)
    hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalLRFamINProbeRK` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINProbeRK E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK hW I hBel F)
    hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalLRFamINProbeRK` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamINProbeRK E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINProbeRK hW I hBel F)

/-! ## §5 — `RcicNativeFamModelK` transfers -/

/-- `typedRowsWf_of_allBelowScoped_fundamentalLRFamKT` at a `tableOfI`-style table. -/
theorem typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamKT E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_tableI hW I hBel
  piRow := piRowField_of_fundamentalLRFamKT hW F
  famAppRow := famAppRow_of_fundamentalLRFamKT hW F

/-- `dt012_of_allBelowScoped_fundamentalLRFamKT` at a `tableOfI`-style table. -/
theorem dt012_of_allBelowScoped_tableI_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_tableI hW I hBel)
    (piRowField_of_fundamentalLRFamKT hW F) hΓ hA hB

/-- `dt010_of_allBelowScoped_fundamentalLRFamKT` at a `tableOfI`-style table. -/
theorem dt010_of_allBelowScoped_tableI_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamKT hW I hBel F) hΓ h hs

/-- `dt011_of_allBelowScoped_fundamentalLRFamKT` at a `tableOfI`-style table. -/
theorem dt011_of_allBelowScoped_tableI_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamKT hW I hBel F) hΓ h hs

/-- `dt019_of_allBelowScoped_fundamentalLRFamKT` at a `tableOfI`-style table. -/
theorem dt019_of_allBelowScoped_tableI_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamKT hW I hBel F) hΓ hd hlhs

/-- `ia024_of_allBelowScoped_fundamentalLRFamKT` at a `tableOfI`-style table. -/
theorem ia024_of_allBelowScoped_tableI_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {tblI : List CRule} (I : TableOfICompat hW tblI)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw tblI)
    {n : Nat} (F : FundamentalLRFamKT E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamKT hW I hBel F)

#print axioms Rcic.Syn.TableOfICompat
#print axioms Rcic.Syn.built_no_family_rule_tableI
#print axioms Rcic.Syn.convE_appN_const_inv_tableI
#print axioms Rcic.Syn.deltaRule_mem_tableI
#print axioms Rcic.Syn.sortRow_of_allBelowScoped_tableI
#print axioms Rcic.Syn.sortRow_of_suppliers_tableI
#print axioms Rcic.Syn.famApp_eqNList_of_allBelowScoped_tableI
#print axioms Rcic.Syn.famAppSaturation_of_allBelowScoped_piRow_tableI
#print axioms Rcic.Syn.typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI
#print axioms Rcic.Syn.typedRowsWf_of_suppliers_piValleyData_slotConv_tableI
#print axioms Rcic.Syn.delta_kept_caseStep_tableI
#print axioms Rcic.Syn.typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamINT
#print axioms Rcic.Syn.typedRowsWf_of_allBelowScoped_tableI_fundamentalLRFamKT

end Rcic.Syn
