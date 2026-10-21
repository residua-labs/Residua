import rcic.RcicSynTableOfITransfer
import rcic.RcicSynTableIotaWF
import rcic.RcicSynTableCongrI
import rcic.RcicSynTableOfICensus
import rcic.RcicSynClosedLete
import rcic.RcicSynClosedEta
import rcic.RcicSynClosedFsub

/-!
# RcicSynTableOfIFull — unconditional `TableOfICompat` at the real `tableOfI`

With PARTs 1–4 landed (`RcicSynTableBuildI`, `RcicSynTableIotaWF`,
`RcicSynTableCongrI`, `RcicSynTableOfITransfer`), the two conditional halves
of `tableWF_tableOfI` are discharged by `tableCongr_tableOfI` /
`tableClosed_tableOfI` (`RcicSynTableCongrI`, `ruleData_tableOfI` over every
`tableOfI` rule), and `TableOfICompat`'s three fields are discharged by:

* `sup`    — `mem_tableOfI_of_mem_tableOf` (`RcicSynTableBuildI.lean:248`);
* `wf`     — `tableWF_tableOfI_full` below;
* `headM`  — `tableOfI_head_major` (`RcicSynTableIotaWF.lean:236`): every
  `tableOfI` head resolves to a `.definitionM` or `.recursorM` member —
  never `.inductiveM`.

This closes the PART-4 residual (`PR #7720`): every `*_tableI` theorem in
`RcicSynTableOfITransfer` now instantiates at `tblI := tableOfI hW` with
`I := tableOfICompat_tableOfI hW` — six canonical corollaries are pinned
below.

## `TABLEOFI_SUPPLIER_CENSUS` recount (machine pins below)

Row classification from `RcicSynTableOfICensus` /
`research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md`, recount after this
module: the table-level walls `tableWFI_build` (= `TableWF (tableOfI hW)`),
`TableOfICompat hW (tableOfI hW)`, `tableOfI_headM`, and
`mem_tableOfI_of_mem_tableOf` are **discharged** for every admitted env.
Named-wall deltas per row:

| #  | field              | table-level walls removed                     | retained (d) walls (unchanged)                                    |
|----|--------------------|-----------------------------------------------|-------------------------------------------------------------------|
| 5  | `es_delta`         | `tableOfICompat_tableOfI`                     | `hu`, `hag`, `hap`, `hL`/`hB` (`delta_canon_cl_L/B`)              |
| 10 | `es_pi`            | `tableWFI_build`                              | `leftCl`/`rightCl`, `occHA`/`occHR` (`pi_*Surface_cl`)            |
| 11 | `es_letE`          | `tableWFI_build`                              | `displayFits`, `leftSurfaceCl`/`rightSurfaceCl`, `occ*`, `body`   |
| 12 | `es_eta`           | `tableWFI_build` (`EtaResiduum.tableWF`)      | `AppGot`, binder CLs, `argTag`                                    |
| 13 | `es_fsub`          | `tableWFI_build` (via `.closed`)              | `hL`/`hR` (`fsub_instEnd_cl*`)                                    |
| 14–18 | `cl`/`eut`/`mixed`/`pb`/`delta_obs` | none (no table walls)        | per-cell port packages / `pbHead_*` / `deltaObsRoute_*`           |
| 1–4, 6–9 | remaining        | none (no table walls)                         | their named (d) residuals                                         |

**Machine recount: 0 → 0 discharged, 18 → 18 open.** No row's closer is fully
premise-free at `tableOfI hW` — every row retains at least one named
field-level (d) wall; what changed is that the *table-level* walls are gone
and the residual set is now field-local only. `closure_claim = 0`.

The five pins `es_pi_tableI_wf`, `es_letE_tableI_wf`, `es_eta_tableI_wf`,
`es_fsub_tableI_wf`, `es_delta_tableI_compat` are composition-only
instantiations: each def's remaining telescope **is** the row's retained
wall set after this module.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.KernelRowsAssembly

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv} {Aw : Nat → Nat}

/-! ## §1 — the two headline theorems -/

/-- `TableWF (tableOfI hEnv)` with no extra premises: `congr`/`closed` from
    `ruleData_tableOfI` (PART 3), the four structural fields from
    `RcicSynTableIotaWF` §4 (PART 2). -/
theorem tableWF_tableOfI_full {E : ResolvedEnv} (hW : EnvWfT E) :
    TableWF (tableOfI hW) :=
  tableWF_tableOfI hW (tableCongr_tableOfI hW) (tableClosed_tableOfI hW)

/-- `TableOfICompat.headM` at the real `tableOfI`: `tableOfI_head_major`
    resolves every head to `.definitionM` or `.recursorM` — never
    `.inductiveM`. -/
theorem tableOfI_headM {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ ρ ∈ tableOfI hW, ∃ m, E.members ρ.head = some m ∧ m.mclass ≠ .inductiveM :=
  fun ρ hρ =>
    (tableOfI_head_major hW ρ hρ).elim
      (fun ⟨m, hm, hmc, _⟩ =>
        ⟨m, hm, fun h => MemberClass.noConfusion (h.symm.trans hmc)⟩)
      (fun ⟨m, hm, hmc, _⟩ =>
        ⟨m, hm, fun h => MemberClass.noConfusion (h.symm.trans hmc)⟩)

/-- The PART-4 residual, discharged: `tableOfI hW` extends `tableOf hW`
    (`mem_tableOfI_of_mem_tableOf`), is well-formed (`tableWF_tableOfI_full`),
    and has no `.inductiveM` rule head (`tableOfI_headM`). -/
theorem tableOfICompat_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) :
    TableOfICompat hW (tableOfI hW) where
  sup := fun _ρ hρ => mem_tableOfI_of_mem_tableOf hW hρ
  wf := tableWF_tableOfI_full hW
  headM := tableOfI_headM hW

/-! ## §2 — canonical corollaries at `tableOfI` (`I` discharged) -/

/-- `sortRow_of_allBelowScoped_tableI` at `tableOfI hW`. -/
theorem sortRow_of_allBelowScoped_tableOfI {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOfI hW)) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_allBelowScoped_tableI hW (tableOfICompat_tableOfI hW) hBel

/-- `sortRow_of_suppliers_tableI` at `tableOfI hW`. -/
theorem sortRow_of_suppliers_tableOfI {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (W : StepSuppliers Aw (tableOfI hW) E) {n : Nat} :
    NativeFamilyProjection.SortRow E n :=
  sortRow_of_suppliers_tableI hW (tableOfICompat_tableOfI hW) W

/-- `built_no_family_rule_tableI` at `tableOfI hW`: an `.inductiveM` member
    ref is never a `tableOfI` rule head. -/
theorem built_no_family_rule_tableOfI {E : ResolvedEnv} (hW : EnvWfT E)
    {f : Nat} {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) : NoHeadRule (tableOfI hW) f :=
  built_no_family_rule_tableI hW (tableOfICompat_tableOfI hW) hf hclass

/-- `convE_appN_const_inv_tableI` at `tableOfI hW`: erased family rigidity. -/
theorem convE_appN_const_inv_tableOfI {E : ResolvedEnv} (hW : EnvWfT E)
    {f : Nat} {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) {ls ls' : List Level}
    {xs ys : List ETm}
    (h : ConvMod (EStep (tableOfI hW)) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep (tableOfI hW)) LvlEq) xs ys :=
  convE_appN_const_inv_tableI hW (tableOfICompat_tableOfI hW) hf hclass h

/-- `deltaRule_mem_tableI` at `tableOfI hW`: δ-rule membership of the ι table. -/
theorem deltaRule_mem_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    deltaRule r (deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr) ∈ tableOfI hEnv :=
  deltaRule_mem_tableI hEnv (tableOfICompat_tableOfI hEnv) hres hbody htr

/-- `typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI` at `tableOfI`. -/
theorem typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableOfI
    {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat}
    (hBel : AllBelowScoped E Aw (tableOfI hW))
    {n : Nat}
    (joinPi : Rcic.Declarative.NativeValleys.NativeKProjectionAudit.PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableI hW
    (tableOfICompat_tableOfI hW) hBel joinPi hSlot

/-- `typedRowsWf_of_suppliers_piValleyData_slotConv_tableI` at `tableOfI`. -/
theorem typedRowsWf_of_suppliers_piValleyData_slotConv_tableOfI
    {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat}
    (W : StepSuppliers Aw (tableOfI hW) E) {n : Nat}
    (joinPi : Rcic.Declarative.NativeValleys.NativeKProjectionAudit.PiConvValleyData E n)
    (hSlot : FamRelevantSlotConv E n) : TypedRowsWf E n :=
  typedRowsWf_of_suppliers_piValleyData_slotConv_tableI hW
    (tableOfICompat_tableOfI hW) W joinPi hSlot

/-! ## §3 — `RcicSynTableOfICensus` recount pins -/

/-- `es_pi` at `tableOfI` with `TableWF` discharged by `tableWF_tableOfI_full`:
    the remaining telescope is exactly `hA hB dl dr S σ ρ` (node data) +
    `leftCl occHA occHR rightCl` — the row's retained (d) walls. -/
noncomputable def es_pi_tableI_wf (hW : EnvWfT E) :=
  fun {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat}
      {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level} =>
    es_pi_field_of_tableWF (Eₐ := Eₐ) Aw (tableOfI hW)
      (tableWF_tableOfI_full hW) (E₀ := E₀) (n₀ := n₀) (Γ₀ := Γ₀) (E := E')
      (n := n) (Γ := Γ) (A := A) (A' := A') (B := B) (B' := B') (u := u) (v := v)

/-- `es_letE` at `tableOfI` with `TableWF` discharged: retained walls =
    `displayFits leftSurfaceCl pA pvL pvR occA occvL occvR body rightSurfaceCl`. -/
noncomputable def es_letE_tableI_wf (hE : EnvWfT E) :=
  fun {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx}
      {A A' v v' b b' B : Expr Nat} {u : Level} =>
    es_letE_closed (Eₐ := Eₐ) (E₀ := E₀) (n₀ := n₀) (Γ₀ := Γ₀) (E := E)
      (n := n) (Γ := Γ) (A := A) (A' := A') (v := v) (v' := v') (b := b)
      (b' := b') (B := B) (u := u) (hE := hE)
      (hTbl := tableWF_tableOfI_full hE)

/-- `es_eta` at `tableOfI` with the residuum's `tableWF` field discharged:
    `r`'s remaining fields are the row's retained (d) walls. -/
noncomputable def es_eta_tableI_wf (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E' n Γ f (.pi A B))
    (dl : TyP E' n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E' n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (r : EtaResiduum Aw (tableOfI hW) hf dl σ ρ) :
    CaseStep Aw (tableOfI hW) (.es (CvP.eta E' n Γ f A B hf dl dr) S σ ρ) :=
  es_eta_closed Aw (tableOfI hW) hf dl dr S σ ρ
    { r with tableWF := tableWF_tableOfI_full hW }

/-- `es_fsub` at `tableOfI` with `TableWF` discharged: retained walls =
    `hL`/`hR` (the `instEnd` composite CLs). -/
noncomputable def es_fsub_tableI_wf (hW : EnvWfT E) :=
  fun {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat}
      {Γ : LCtx} {A B Sx a b : Expr Nat} {u : Level} =>
    es_fsub_field_closed (Eₐ := Eₐ) (Aw := Aw) (tbl := tableOfI hW) (E₀ := E₀) (n₀ := n₀)
      (Γ₀ := Γ₀) (E := E') (n := n) (Γ := Γ) (A := A) (B := B) (Sx := Sx)
      (a := a) (b := b) (u := u) (hTbl := tableWF_tableOfI_full hW)

/-- `es_delta` at `tableOfI` with `TableOfICompat` discharged:
    `delta_kept_caseStep_tableI` instantiated at `tblI := tableOfI S.env`,
    `I := tableOfICompat_tableOfI S.env` — retained walls = `hu hag hap hL hB`. -/
noncomputable def es_delta_tableI_compat {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :=
  delta_kept_caseStep_tableI (Aw := Aw) (r := r) (ls := ls) (m := m) (b := b)
    (S := S) (σ := σ) (tblI := tableOfI S.env)
    (I := tableOfICompat_tableOfI S.env)

#print axioms Rcic.Syn.tableWF_tableOfI_full
#print axioms Rcic.Syn.tableOfI_headM
#print axioms Rcic.Syn.tableOfICompat_tableOfI
#print axioms Rcic.Syn.sortRow_of_allBelowScoped_tableOfI
#print axioms Rcic.Syn.sortRow_of_suppliers_tableOfI
#print axioms Rcic.Syn.built_no_family_rule_tableOfI
#print axioms Rcic.Syn.convE_appN_const_inv_tableOfI
#print axioms Rcic.Syn.deltaRule_mem_tableOfI
#print axioms Rcic.Syn.typedRowsWf_of_allBelowScoped_piValleyData_slotConv_tableOfI
#print axioms Rcic.Syn.typedRowsWf_of_suppliers_piValleyData_slotConv_tableOfI
#print axioms Rcic.Syn.es_pi_tableI_wf
#print axioms Rcic.Syn.es_letE_tableI_wf
#print axioms Rcic.Syn.es_eta_tableI_wf
#print axioms Rcic.Syn.es_fsub_tableI_wf
#print axioms Rcic.Syn.es_delta_tableI_compat

end Rcic.Syn
