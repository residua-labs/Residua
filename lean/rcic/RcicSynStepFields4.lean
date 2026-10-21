import rcic.RcicSynStepSkeleton
import rcic.RcicSynLetRight
import rcic.RcicSynTagCoh
import rcic.RcicSynMixedUSurface
import rcic.RcicSynMixedLetConst
import rcic.RcicSynConstEutAdm
import rcic.RcicSynLetEtaFinish

/-!
# Syntactic sortRow — `StepSuppliers` fields `es_zetaLocal`, `es_letE`, `es_eta`, `es_consts`

`research/rcic/sortrow/STEP_SUPPLIERS.md`, `BELOWC_DEMAND_GRAMMAR_CONTINUATION.md`
§3.4 / §4, `BELOWC_SEMANTIC_WALLS.md` Parts I–II,
`BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2 / §8, and
`BELOWC_MIXED_INTERPRETER.md` §§7–8. `closure_claim = 0`.

What this module proves on top of `RcicSynStepSkeleton`, `RcicSynLetRight`,
`RcicSynTagCoh`, `RcicSynMixedUSurface`, `RcicSynMixedLetConst`,
`RcicSynConstEutAdm`, and `RcicSynLetEtaFinish`:

* **§1 `es_zetaLocal` (`CvP.zetaLocal`):**
  * `zetaLocal_issued_value_cl` extracts `CL tbl σ ρ hv dr` from `StepIH`
    through `Issues.zetaLocal_cl` and `dmStep_pair_below`.
  * `zetaLocal_direct_bvar_issued_pb` extracts `PBit σ ρ hv hA` when
    `dl = TyP.bvar E n Γ i A u hty hA` from `StepIH` through `Issues.occ_pb`
    at payload positions `(0, [0])` and `(0, [1, 0])`.
  * `zetaLocal_issued_reg_pb` extracts `PBit σ ρ hv dl.reg.2` from `StepIH`
    through `Issues.occ_pb` whenever `dl.reg.2` sits at a `P2Query.subAt`
    occurrence path `pReg` (with weight and `AssumpPref` discharged from
    `TyP.wt_reg_le` and `hq.ap`).
  * `es_zetaLocal_direct_bvar_proof` closes the proof-sort direct-bvar subcase
    (`dl = TyP.bvar E n Γ i A u hty hA`, `levelIsZero (σ u) = true`) with
    **zero extra hypotheses** from `StepIH` alone.
  * `es_zetaLocal_direct_bvar_rel` closes the relevant-sort direct-bvar subcase
    given the display-slot/value equation `ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)`.
  * `zetaLocalBvarSurface` constructs the canonical bvar surface
    `TyP.bvar E n Γ i A dl.reg.1 hty dl.reg.2` strictly below `node.wt`
    (`zetaLocalBvarSurface_wt_lt`) and preserving `AssumpPref`
    (`zetaLocalBvarSurface_ap`).
  * `es_zetaLocal_proof_of_reg_occ` closes the proof-sort subcase
    (`levelIsZero (σ dl.reg.1) = true`) from `StepIH` (`Issues.occ_pb` +
    `Issues.zetaLocal_cl`), `CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)`, and
    the occurrence path `pReg` for `dl.reg.2` (**never mentioning `dr` or
    assuming `PBit σ ρ hv dl.reg.2`**).
  * `ZetaLocalPorts` packages the left-surface `CL` (`dl` to
    `zetaLocalBvarSurface hty dl`) and the slot/value coherence against `hv`
    (**never mentioning `dr`**), and `zetaLocal_caseStep_of_ports` proves the
    exact `StepSuppliers.es_zetaLocal` `CaseStep` goal by combining
    `ZetaLocalPorts` with `StepIH` (`Issues.zetaLocal_cl`).
  * `zetaLocal_issued_cl_variants` proves the kernel-checked occurrence control
    that every `.cl` child `Issues` emits from `CvP.zetaLocal` is either an
    `occ_cl` occurrence pair or the `zetaLocal_cl` edge (`hv` vs `dr`).

* **§2 `es_letE` (`CvP.letE`):**
  * `letE_issued_dom_es`, `letE_issued_val_es`, `letE_issued_body_es_drop`,
    `letE_issued_body_es_inline`, and `letE_issued_body_es` extract `ES tbl σ ρ hA`,
    `ES tbl σ ρ hv`, and the unconditional body `ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb`
    from `StepIH` through `Issues.letE_esA`, `Issues.letE_esV`,
    `Issues.letE_esB_drop`, and `Issues.letE_esB_inline`.
  * `letE_issued_val_pb_left`, `letE_issued_val_pb_right`, and
    `letE_issued_val_rel` extract `PBit σ ρ hv.dl hA.dl`,
    `PBit σ ρ hv.dr hA.dl`, and `Rel tbl (hv.dl.eps σ ρ) (hv.dr.eps σ ρ)` from
    `StepIH` through `Issues.occ_pb` and `Issues.letE_esV` when `hA.dl`,
    `hv.dl`, and `hv.dr` sit at `P2Query.subAt` occurrence paths `pA`, `pvL`,
    `pvR`.
  * `letE_issued_dl_reg_pb` and `letE_issued_dr_reg_pb` extract
    `PBit σ ρ dl dl.reg.2` and `PBit σ ρ dr dl.reg.2` from `StepIH` through
    `Issues.occ_pb` (at `(0, [3])` and `(0, [4])` against `(0, pReg)`), and
    `es_letE_proof_of_reg_occ`, `es_letE_of_dl_star_reg_occ`, and
    `es_letE_direct_left_proof` close the §8.1 proof-result / whole-read-star
    subcases from `StepIH` alone with **zero `CL`, `PBit`, or `LetEPorts`
    hypotheses**.
  * `letLeftSurface` constructs the canonical left let surface strictly below
    `node.wt` (`letLeftSurface_wt_lt`) and preserving `AssumpPref`
    (`letLeftSurface_ap`).
  * `es_letE_proof_right_leg` and `es_letE_same_decl` wire the landed §8.1 / §8.2
    let finishes (`RcicSynLetEtaFinish.letE_proof_right_leg_display`,
    `letBodyLeftSub`, `letProofResult`, `letSameDeclRight`,
    `letSameDeclRight_continuation` #7444) with `StepIH`
    (`letE_issued_body_es`) and `leftSurfaceCl` to close `CaseStep` on the
    three-leg proof-result continuation and the unchanged-declaration (`A' = A`,
    `v' = v`) branch.
  * `LetEPorts` records the residual left/right surface `CL`s, value `PBit`s,
    and `BodyAnswers` for landed Wall 2 (`RcicSynLetRight`), omitting `valueES`,
    body `ES`, and `hb.dr.AssumpPref` because `StepIH` and `hq.ap` supply them;
    `letE_caseStep_of_ports` proves the exact `StepSuppliers.es_letE` `CaseStep` goal.
  * `LetEUSurfacePorts` and `letE_caseStep_of_uSurfacePorts` specialize
    `es_letE` to the landed §8 `U` right-surface worker (`RcicSynMixedUSurface`
    #7479) and `occ_pb` occurrence paths `pA`, `pvL`, `pvR`, discharging
    `valueES`, `hb_es`, `valuePBLeft`, `valuePBRight`, `hb.dr.AssumpPref`, and
    `rightSurfaceCl` inside the proof from `StepIH` and `hq.ap`.
  * `letE_issued_cl_is_occurrence` proves that every `.cl` child `Issues` emits
    from `CvP.letE` is an `occ_cl` occurrence pair.

* **§3 `es_eta` (`CvP.eta`):**
  * `eta_issued_fun_cl` extracts `CL tbl σ ρ hf dr` from `StepIH` through
    `Issues.eta_cl` and `dmStep_pair_below`.
  * `eta_issued_dl_reg_pb` and `eta_issued_dr_reg_pb` extract
    `PBit σ ρ dl dl.reg.2` and `PBit σ ρ dr dl.reg.2` from `StepIH` through
    `Issues.occ_pb` (at `(0, [1])` and `(0, [2])` against `(0, pReg)`), and
    `es_eta_proof_of_reg_occ`, `es_eta_of_dl_star_reg_occ`, and
    `es_eta_proof_of_hf_reg_occ` close the §3.2 proof-result / whole-read-star
    finish from `StepIH` alone with **zero `CL`, `PBit`, or `EtaPorts`
    hypotheses**.
  * `eta_wkAtZero_cl_drop` and `eta_wkAtZero_cl_keep` transport a body-function
    `CL` against `wkAtZero (A := A) hf` across the `StepIH`-supplied `CL tbl σ ρ hf dr`
    to `dr.eps σ ρ` on `.drop` and `(dr.eps σ ρ).lift 0 1` on `.keep`.
  * `EtaPorts` packages the §3.2 body-application reading `got` of `dl`, the
    function `CL` against `wkAtZero (A := A) hf`, and the variable `CL` /
    `TagCoh` against `etaArg hA` (**never mentioning `dr` at all**), and
    `eta_caseStep_of_ports` proves the exact `StepSuppliers.es_eta` `CaseStep`
    goal by combining `EtaPorts` with `StepIH` (`Issues.eta_cl`) and the landed
    η consumers `RcicSynLetEtaFinish.es_eta_zvar_drop` and
    `RcicSynLetEtaFinish.es_eta_zvar_keep` (#7444).
  * `eta_issued_cl_variants` proves the kernel-checked occurrence control on
    `.cl` children emitted from `CvP.eta`.

* **§4 `es_consts` (`CvP.consts`):**
  * `consts_direct_issued_bitCoh` extracts `BitCoh σ hTL hTR`
    (`levelIsZero (σ uL) = levelIsZero (σ uR)`) from `StepIH` through
    `Issues.occ_bitCoh` at payload paths `(0, [0, 0])` and `(0, [1, 0])` when
    `dl` and `dr` are direct `TyP.const` nodes.
  * `es_consts_direct` closes `CaseStep` for direct `TyP.const` endpoints with
    **zero extra hypotheses** from `StepIH` (`Issues.occ_bitCoh`), `hq.hom`
    (`LevelHom σ`), and landed `RcicSynMixedLetConst.mixedCL_const_nodes` (#7479).
  * `constsCanonLeft` and `constsCanonRight` construct the §3.4 canonical
    `TyP.const` surfaces strictly below `node.wt` (`constsCanonLeft_wt_lt`,
    `constsCanonRight_wt_lt` via `TyP.admW_lt_of_const`) and preserving
    `AssumpPref` (`constsCanonLeft_ap`, `constsCanonRight_ap`).
  * `consts_canonLeft_eut_adm` and `consts_canonRight_eut_adm` wire landed
    Wall 1 (`RcicSynConstEutAdm.eut_const_of_admission_views` #7443, batch 149)
    to prove `EUT` between arbitrary-alias `TyP.const` nodes at `(r, ls)` /
    `(r, ls')` and `constsCanonLeft` / `constsCanonRight` through one admission
    `A : TypeAdm E Aw r m` under `hq.hom` (`LevelHom σ`), with `DMStep`
    payments supplied by `dmStep_constEutAdm_pair`.
  * `ConstsPorts` and `ConstsPorts.ofRegSurfaces` package left/right surface
    `CL`s to `TyP.const` nodes whose type-at-sort witnesses `hTL`, `hTR` sit at
    `subAt` occurrence paths `pL`, `pR` (without assuming `BitCoh σ hTL hTR` or
    `CL tbl σ ρ dl dr`), and `consts_caseStep_of_ports` proves the exact
    `StepSuppliers.es_consts` `CaseStep` goal via `StepIH` (`Issues.occ_bitCoh`),
    `hq.hom`, and `RcicSynMixedLetConst.mixedCL_const_nodes`.
  * `consts_issued_cl_is_occurrence` proves that every `.cl` child `Issues`
    emits from `CvP.consts` is an `occ_cl` occurrence pair.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- Constructor tag of a `CvP`, nonzero on `zetaLocal`, `letE`, `eta`, and `consts`.
    Used by `congrArg esParentTag4` to refute foreign `.es` rows when inverting
    an `Issues` edge whose parent is a concrete `.es` node. -/
def cvpCtorTag4 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    CvP E n Γ a b T → Nat
  | .zetaLocal .. => 1
  | .letE .. => 2
  | .eta .. => 3
  | .consts .. => 4
  | _ => 0

/-- `cvpCtorTag4` lifted to the `.es` parent of an `Issues` edge. -/
def esParentTag4 : P2Query Eₐ → Nat
  | .es c _ _ _ => cvpCtorTag4 c
  | _ => 0

/-! ## §1 `es_zetaLocal` (`CvP.zetaLocal`) -/

/-- `StepIH` on a `CvP.zetaLocal` query yields `CL tbl σ ρ hv dr` via the
    dedicated `Issues.zetaLocal_cl` row and `dmStep_pair_below`. -/
theorem zetaLocal_issued_value_cl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)) :
    CL tbl σ ρ hv dr :=
  ih_local Aw tbl hq ih (.cl hv dr S σ ρ) Issues.zetaLocal_cl rfl
    (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) rfl hv dr
        (by simp only [CvP.wt]; omega) (by simp only [CvP.wt]; omega))))

/-- When the left typing of `CvP.zetaLocal` is a direct `TyP.bvar E n Γ i A u hty hA`,
    both `hv` (payload path `(0, [0])`) and `hA` (payload path `(0, [1, 0])`) are
    genuine `P2Query.subAt` occurrences of the `zetaLocal` node, so `Issues.occ_pb`
    and `StepIH` supply `PBit σ ρ hv hA`. -/
theorem zetaLocal_direct_bvar_issued_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} {u : Level}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (hA : TyP E n Γ A (.sort u)) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.zetaLocal E n Γ i A v hval hty hv
      (TyP.bvar E n Γ i A u hty hA) dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv
      (TyP.bvar E n Γ i A u hty hA) dr) S σ ρ)) :
    PBit σ ρ hv hA := by
  obtain ⟨hapv, hapA, -⟩ := hq.ap
  exact ih_issue Aw tbl hq ih (.pb hv hA S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [0]) (k₂ := 0) (p₂ := [1, 0]) rfl rfl hapv hapA)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.zetaLocal E n Γ i A v hval hty hv (TyP.bvar E n Γ i A u hty hA) dr)
        rfl hv hA
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt, TyP.wt]; omega)))))

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ` (`hv` sits at
    `(0, [0])`), `StepIH` and `Issues.occ_pb` supply `PBit σ ρ hv dl.reg.2`,
    with the weight bounds and `AssumpPref` discharged automatically from
    `TyP.wt_reg_le` and `hq.ap`. -/
theorem zetaLocal_issued_reg_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)) :
    PBit σ ρ hv dl.reg.2 := by
  obtain ⟨hapv, hapdl, -⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb hv dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [0]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapv (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.zetaLocal E n Γ i A v hval hty hv dl dr)
        rfl hv dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- Proof-sort closure of `es_zetaLocal` when `dl` is a direct `TyP.bvar` node:
    closes `CaseStep` with **zero additional hypotheses** from `StepIH` alone
    (`Issues.occ_pb` + `Issues.zetaLocal_cl`). -/
theorem es_zetaLocal_direct_bvar_proof
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} {u : Level}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (hA : TyP E n Γ A (.sort u)) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv
      (TyP.bvar E n Γ i A u hty hA) dr) S σ ρ) := by
  intro hq ih
  have hpb : PBit σ ρ hv hA :=
    zetaLocal_direct_bvar_issued_pb Aw tbl hval hty hv hA dr S σ ρ hq ih
  have hcl : CL tbl σ ρ hv dr :=
    zetaLocal_issued_value_cl Aw tbl hval hty hv (TyP.bvar E n Γ i A u hty hA) dr S σ ρ hq ih
  have hv_star : hv.eps σ ρ = .star := hpb.mpr hu
  have hdl_star : (TyP.bvar E n Γ i A u hty hA).eps σ ρ = .star := by
    simp [TyP.eps, hu]
  show ES tbl σ ρ _
  unfold CL at hcl
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_star]
  rwa [hv_star] at hcl

/-- Relevant-sort closure of `es_zetaLocal` when `dl` is a direct `TyP.bvar` node,
    consuming `CL tbl σ ρ hv dr` from `StepIH` and the display-slot/value equation
    `ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)`. -/
theorem es_zetaLocal_direct_bvar_rel
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} {u : Level}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (hA : TyP E n Γ A (.sort u)) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false)
    (hres : ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv
      (TyP.bvar E n Γ i A u hty hA) dr) S σ ρ) := by
  intro hq ih
  have hcl : CL tbl σ ρ hv dr :=
    zetaLocal_issued_value_cl Aw tbl hval hty hv (TyP.bvar E n Γ i A u hty hA) dr S σ ρ hq ih
  have hdl_rel : (TyP.bvar E n Γ i A u hty hA).eps σ ρ = resolve ρ i := by
    simp [TyP.eps, hu]
  show ES tbl σ ρ _
  unfold CL at hcl
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_rel]
  exact hres.trans hcl

/-- The canonical direct-bvar surface typing for `CvP.zetaLocal`, formed from
    `hty : lookupType Γ i = some A` and `dl.reg`. -/
noncomputable def zetaLocalBvarSurface
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (hty : lookupType Γ i = some A) (dl : TyP E n Γ (.bvar i) A) :
    TyP E n Γ (.bvar i) A :=
  TyP.bvar E n Γ i A dl.reg.1 hty dl.reg.2

/-- `zetaLocalBvarSurface hty dl` has strictly smaller weight than the enclosing
    `CvP.zetaLocal` node (`dl.reg.2.wt ≤ dl.wt` by `TyP.wt_reg_le`, and `hv.wt ≥ 1`
    by `TyP.wt_pos`). -/
theorem zetaLocalBvarSurface_wt_lt
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A) :
    (zetaLocalBvarSurface hty dl).wt Aw <
      (CvP.zetaLocal E n Γ i A v hval hty hv dl dr).wt Aw := by
  have hreg : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  have hpos : 1 ≤ hv.wt Aw := TyP.wt_pos Aw hv
  simp only [zetaLocalBvarSurface, TyP.wt, CvP.wt]
  omega

/-- `zetaLocalBvarSurface hty dl` preserves `AssumpPref` from `dl` via `assumpPref_reg`. -/
theorem zetaLocalBvarSurface_ap
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (hty : lookupType Γ i = some A) (dl : TyP E n Γ (.bvar i) A)
    (hdl : dl.AssumpPref) :
    (zetaLocalBvarSurface hty dl).AssumpPref := by
  simpa [zetaLocalBvarSurface, TyP.AssumpPref] using assumpPref_reg hdl

/-- Proof-sort closure of `es_zetaLocal` for an arbitrary `dl` whose regularity
    typing `dl.reg.2` sits at occurrence path `pReg`: closes `CaseStep` from
    `StepIH` (`zetaLocal_issued_reg_pb` + `zetaLocal_issued_value_cl`) and
    `surfaceCl : CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)` alone (**never
    mentioning `dr` or assuming `PBit σ ρ hv dl.reg.2`**). -/
theorem es_zetaLocal_proof_of_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ dl.reg.1) = true)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hsurf : CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro hq ih
  have hpb : PBit σ ρ hv dl.reg.2 :=
    zetaLocal_issued_reg_pb Aw tbl hval hty hv dl dr S σ ρ pReg hocc hq ih
  have hcl : CL tbl σ ρ hv dr :=
    zetaLocal_issued_value_cl Aw tbl hval hty hv dl dr S σ ρ hq ih
  have hv_star : hv.eps σ ρ = .star := hpb.mpr hu
  have hbvar_star : (zetaLocalBvarSurface hty dl).eps σ ρ = .star := by
    simp [zetaLocalBvarSurface, TyP.eps, hu]
  have hsurf' : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((zetaLocalBvarSurface hty dl).eps σ ρ) :=
    hsurf
  rw [hbvar_star, ← hv_star] at hsurf'
  show ES tbl σ ρ _
  exact hsurf'.trans hcl

/-- Residual ports for `StepSuppliers.es_zetaLocal` (`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md`
    §4). Crucially, `ZetaLocalPorts` **never mentions `dr`**: `dr` is reached
    exclusively through `StepIH` on the issued `Issues.zetaLocal_cl` row
    (`CL tbl σ ρ hv dr`). -/
structure ZetaLocalPorts
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (σ : Level → Level) (ρ : List Disp)
    (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) : Prop where
  /-- Left surface `CL`: `dl` is erased-convertible to the canonical bvar surface
      `zetaLocalBvarSurface hty dl`. (Reflexive when `dl` is already `TyP.bvar`.) -/
  surfaceCl : CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)
  /-- Slot/value coherence against `hv`: either the regularity sort is proof and
      `hv` erases to `★` via `PBit σ ρ hv dl.reg.2`, or the regularity sort is
      relevant and `resolve ρ i` converts to `hv.eps σ ρ`. -/
  slotCoh :
    (levelIsZero (σ dl.reg.1) = true ∧ PBit σ ρ hv dl.reg.2) ∨
      (levelIsZero (σ dl.reg.1) = false ∧
        ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ))

/-- Exact `StepSuppliers.es_zetaLocal` statement closed from `StepIH`
    (`Issues.zetaLocal_cl` supplying `CL tbl σ ρ hv dr`) and `ZetaLocalPorts`. -/
theorem zetaLocal_caseStep_of_ports :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {i : Nat} {A v : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (_ports : ZetaLocalPorts tbl σ ρ hty hv dl),
      CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ i A v hval hty hv dl dr S σ ρ ports hq ih
  have hcl_hv_dr : CL tbl σ ρ hv dr :=
    zetaLocal_issued_value_cl Aw tbl hval hty hv dl dr S σ ρ hq ih
  have hsurf : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((zetaLocalBvarSurface hty dl).eps σ ρ) :=
    ports.surfaceCl
  show ES tbl σ ρ _
  unfold CL at hcl_hv_dr
  unfold ES
  simp only [CvP.dl, CvP.dr]
  rcases ports.slotCoh with ⟨hu, hpb⟩ | ⟨hu, hres⟩
  · have hbvar_star : (zetaLocalBvarSurface hty dl).eps σ ρ = .star := by
      simp [zetaLocalBvarSurface, TyP.eps, hu]
    have hv_star : hv.eps σ ρ = .star := hpb.mpr hu
    rw [hbvar_star, ← hv_star] at hsurf
    exact hsurf.trans hcl_hv_dr
  · have hbvar_rel : (zetaLocalBvarSurface hty dl).eps σ ρ = resolve ρ i := by
      simp [zetaLocalBvarSurface, TyP.eps, hu]
    rw [hbvar_rel] at hsurf
    exact (hsurf.trans hres).trans hcl_hv_dr

/-- Kernel-checked occurrence control on `CvP.zetaLocal`: every `.cl` child
    `Issues` emits from `.es (CvP.zetaLocal ...)` is either an `occ_cl`
    occurrence pair or the `zetaLocal_cl` port (`hv` vs `dr`). -/
theorem zetaLocal_issued_cl_variants
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} {e T₁ T₂ : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
        (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
        (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) k p = some (.ty D₂)) ∨
    ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (i' : Nat) (A' v' : Expr Nat)
      (hval' : lookupValue Γ' i' = some v') (hty' : lookupType Γ' i' = some A')
      (hv' : TyP E' n' Γ' v' A') (dl' : TyP E' n' Γ' (.bvar i') A') (dr' : TyP E' n' Γ' v' A')
      (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx) (S' : ScopedCtx Eₐ E₀' n₀' Γ₀')
      (σ' : Level → Level) (ρ' : List Disp),
      (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ : P2Query Eₐ) =
        .es (CvP.zetaLocal E' n' Γ' i' A' v' hval' hty' hv' dl' dr') S' σ' ρ' ∧
      HEq D₁ hv' ∧ HEq D₂ dr' := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧ (∃ k p, q.subAt k p = some (.ty D₂)) ∨
      ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (i' : Nat) (A' v' : Expr Nat)
        (hval' : lookupValue Γ' i' = some v') (hty' : lookupType Γ' i' = some A')
        (hv' : TyP E' n' Γ' v' A') (dl' : TyP E' n' Γ' (.bvar i') A') (dr' : TyP E' n' Γ' v' A')
        (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx) (S' : ScopedCtx Eₐ E₀' n₀' Γ₀')
        (σ' : Level → Level) (ρ' : List Disp),
        q = .es (CvP.zetaLocal E' n' Γ' i' A' v' hval' hty' hv' dl' dr') S' σ' ρ' ∧
        HEq D₁ hv' ∧ HEq D₂ dr' := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact Or.inl ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | zetaLocal_cl =>
        exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          rfl, HEq.rfl, HEq.rfl⟩
    | _ => exact absurd (congrArg esParentTag4 hq) (by simp [esParentTag4, cvpCtorTag4])
  exact aux _ iss rfl

/-! ## §2 `es_letE` (`CvP.letE`) -/

/-- `StepIH` on a `CvP.letE` query yields `ES tbl σ ρ hA` via `Issues.letE_esA`
    and `rule_sub_before`. -/
theorem letE_issued_dom_es
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    ES tbl σ ρ hA :=
  ih_issue Aw tbl hq ih (.es hA S σ ρ) Issues.letE_esA
    (rule_sub_before Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl hA
      (by simp only [CvP.wt]; omega) S σ ρ _)

/-- `StepIH` on a `CvP.letE` query yields `ES tbl σ ρ hv` via `Issues.letE_esV`
    and `rule_sub_before`. -/
theorem letE_issued_val_es
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    ES tbl σ ρ hv :=
  ih_issue Aw tbl hq ih (.es hv S σ ρ) Issues.letE_esV
    (rule_sub_before Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl hv
      (by simp only [CvP.wt]; omega) S σ ρ _)

/-- `StepIH` on a `CvP.letE` query yields `ES tbl σ (.drop :: ρ) hb` when
    `hv.dl.eps σ ρ = .star` via `Issues.letE_esB_drop` and `rule_sub_before`. -/
theorem letE_issued_body_es_drop
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hvs : hv.dl.eps σ ρ = .star)
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    ES tbl σ (.drop :: ρ) hb :=
  ih_issue Aw tbl hq ih (.es hb S σ (.drop :: ρ)) (Issues.letE_esB_drop hvs)
    (rule_sub_before Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl hb
      (by simp only [CvP.wt]; omega) S σ ρ _)

/-- `StepIH` on a `CvP.letE` query yields `ES tbl σ (.inline (hv.dl.eps σ ρ) :: ρ) hb`
    via `Issues.letE_esB_inline` and `rule_sub_before`. -/
theorem letE_issued_body_es_inline
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    ES tbl σ (.inline (hv.dl.eps σ ρ) :: ρ) hb :=
  ih_issue Aw tbl hq ih (.es hb S σ (.inline (hv.dl.eps σ ρ) :: ρ)) Issues.letE_esB_inline
    (rule_sub_before Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl hb
      (by simp only [CvP.wt]; omega) S σ ρ _)

/-- Combining `letE_issued_body_es_drop` and `letE_issued_body_es_inline` yields
    `ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb` unconditionally from `StepIH`. -/
theorem letE_issued_body_es
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb := by
  by_cases hvs : hv.dl.eps σ ρ = .star
  · rw [hvs, letDisp_star]
    exact letE_issued_body_es_drop Aw tbl hA hv hb dl dr S σ ρ hvs hq ih
  · rw [letDisp_of_ne_star hvs]
    exact letE_issued_body_es_inline Aw tbl hA hv hb dl dr S σ ρ hq ih

/-- When `hv.dl` (at path `pvL`) and `hA.dl` (at path `pA`) are `P2Query.subAt`
    occurrences of `.es (CvP.letE ...) S σ ρ`, `Issues.occ_pb` and `StepIH`
    supply `PBit σ ρ hv.dl hA.dl`, with the weight bounds (`CvP.wt_dl_lt`) and
    `AssumpPref` (`assumpPref_dl`) discharged automatically. -/
theorem letE_issued_val_pb_left
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pvL pA : List Nat)
    (hocc_vL :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvL = some (.ty hv.dl))
    (hocc_A :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pA = some (.ty hA.dl))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ hv.dl hA.dl := by
  obtain ⟨hapA, hapv, -⟩ := hq.ap
  have hvl_wt : hv.dl.wt Aw < hv.wt Aw := CvP.wt_dl_lt Aw hv
  have hAl_wt : hA.dl.wt Aw < hA.wt Aw := CvP.wt_dl_lt Aw hA
  exact ih_issue Aw tbl hq ih (.pb hv.dl hA.dl S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := pvL) (k₂ := 0) (p₂ := pA)
      hocc_vL hocc_A (assumpPref_dl hapv) (assumpPref_dl hapA))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)
        rfl hv.dl hA.dl
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- When `hv.dr` (at path `pvR`) and `hA.dl` (at path `pA`) are `P2Query.subAt`
    occurrences of `.es (CvP.letE ...) S σ ρ`, `Issues.occ_pb` and `StepIH`
    supply `PBit σ ρ hv.dr hA.dl`, with the weight bounds (`CvP.wt_dr_lt`,
    `CvP.wt_dl_lt`) and `AssumpPref` (`assumpPref_dr`, `assumpPref_dl`)
    discharged automatically. -/
theorem letE_issued_val_pb_right
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pvR pA : List Nat)
    (hocc_vR :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvR = some (.ty hv.dr))
    (hocc_A :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pA = some (.ty hA.dl))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ hv.dr hA.dl := by
  obtain ⟨hapA, hapv, -⟩ := hq.ap
  have hvr_wt : hv.dr.wt Aw < hv.wt Aw := CvP.wt_dr_lt Aw hv
  have hAl_wt : hA.dl.wt Aw < hA.wt Aw := CvP.wt_dl_lt Aw hA
  exact ih_issue Aw tbl hq ih (.pb hv.dr hA.dl S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := pvR) (k₂ := 0) (p₂ := pA)
      hocc_vR hocc_A (assumpPref_dr hapv) (assumpPref_dl hapA))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)
        rfl hv.dr hA.dl
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- Combining `letE_issued_val_es`, `letE_issued_val_pb_left`, and
    `letE_issued_val_pb_right` with landed `RcicSynMixedUSurface.rel_value_of_es_pb`
    yields `Rel tbl (hv.dl.eps σ ρ) (hv.dr.eps σ ρ)` directly from `StepIH`. -/
theorem letE_issued_val_rel
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pA pvL pvR : List Nat)
    (hocc_A :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pA = some (.ty hA.dl))
    (hocc_vL :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvL = some (.ty hv.dl))
    (hocc_vR :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvR = some (.ty hv.dr))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    Rel tbl (hv.dl.eps σ ρ) (hv.dr.eps σ ρ) :=
  rel_value_of_es_pb
    (letE_issued_val_es Aw tbl hA hv hb dl dr S σ ρ hq ih)
    (letE_issued_val_pb_left Aw tbl hA hv hb dl dr S σ ρ pvL pA hocc_vL hocc_A hq ih)
    (letE_issued_val_pb_right Aw tbl hA hv hb dl dr S σ ρ pvR pA hocc_vR hocc_A hq ih)

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.letE ...) S σ ρ` (`dl` sits at `(0, [3])`), `StepIH` and
    `Issues.occ_pb` supply `PBit σ ρ dl dl.reg.2`, with weight bounds and
    `AssumpPref` discharged automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem letE_issued_dl_reg_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ dl dl.reg.2 := by
  obtain ⟨_, _, _, hapdl, _⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dl dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [3]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdl (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)
        rfl dl dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.letE ...) S σ ρ` (`dr` sits at `(0, [4])`, and both `dl` and `dr`
    have ascribed type `instantiate0 v B`), `StepIH` and `Issues.occ_pb` supply
    `PBit σ ρ dr dl.reg.2`, with weight bounds and `AssumpPref` discharged
    automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem letE_issued_dr_reg_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ dr dl.reg.2 := by
  obtain ⟨_, _, _, hapdl, hapdr⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dr dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [4]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdr (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)
        rfl dr dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- §8.1 proof-result closure of `es_letE` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
    §8.1): whenever `levelIsZero (σ dl.reg.1) = true` and `dl.reg.2` sits at
    occurrence path `pReg`, `StepIH` (`letE_issued_dl_reg_pb` and
    `letE_issued_dr_reg_pb`) forces both `dl.eps σ ρ = .star` and
    `dr.eps σ ρ = .star`, closing `CaseStep` with **zero `CL`, `PBit`, or
    `LetEPorts` hypotheses**. -/
theorem es_letE_proof_of_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ dl.reg.1) = true)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    letE_issued_dl_reg_pb Aw tbl hA hv hb dl dr S σ ρ pReg hocc hq ih
  have hpbR : PBit σ ρ dr dl.reg.2 :=
    letE_issued_dr_reg_pb Aw tbl hA hv hb dl dr S σ ρ pReg hocc hq ih
  have hdl_star : dl.eps σ ρ = .star := hpbL.mpr hu
  have hdr_star : dr.eps σ ρ = .star := hpbR.mpr hu
  show ES tbl σ ρ _
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_star, hdr_star]
  exact ConvMod.refl _

/-- §8.1 whole-read-star closure of `es_letE`: whenever `dl.eps σ ρ = .star` and
    `dl.reg.2` sits at occurrence path `pReg`, `StepIH` (`letE_issued_dl_reg_pb`
    and `letE_issued_dr_reg_pb`) forces `dr.eps σ ρ = .star` as well, closing
    `CaseStep` with **zero `CL`, `PBit`, or `LetEPorts` hypotheses**. -/
theorem es_letE_of_dl_star_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdl_star : dl.eps σ ρ = .star)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    letE_issued_dl_reg_pb Aw tbl hA hv hb dl dr S σ ρ pReg hocc hq ih
  exact es_letE_proof_of_reg_occ Aw tbl hA hv hb dl dr S σ ρ
    (hpbL.mp hdl_star) pReg hocc hq ih

/-- Direct-left-`TyP.letE` proof-result closure of `es_letE`: when
    `dl = TyP.letE E n Γ A uL v B b wL hAL hvL hbL hTL` and
    `levelIsZero (σ wL) = true`, `hTL` sits at occurrence path `(0, [3, 3])`
    by `rfl`, so `es_letE_proof_of_reg_occ` closes `CaseStep` from `StepIH`
    alone with **zero extra hypotheses**. -/
theorem es_letE_direct_left_proof
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u uL wL : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (hAL : TyP E n Γ A (.sort uL)) (hvL : TyP E n Γ v A)
    (hbL : TyP E n (.letBinding A v :: Γ) b B)
    (hTL : TyP E n Γ (instantiate0 v B) (.sort wL))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hw : levelIsZero (σ wL) = true) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb
      (TyP.letE E n Γ A uL v B b wL hAL hvL hbL hTL) dr) S σ ρ) :=
  es_letE_proof_of_reg_occ Aw tbl hA hv hb
    (TyP.letE E n Γ A uL v B b wL hAL hvL hbL hTL) dr S σ ρ hw [3, 3] rfl

/-- The canonical left surface typing of `.letE A v b`, assembled from `hA.dl`,
    `hv.dl`, `hb.dl`, and `dl.reg`. -/
noncomputable def letLeftSurface
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B)) :
    TyP E n Γ (.letE A v b) (instantiate0 v B) :=
  TyP.letE E n Γ A u v B b dl.reg.1 hA.dl hv.dl hb.dl dl.reg.2

/-- `letLeftSurface hA hv hb dl` has strictly smaller weight than the enclosing
    `CvP.letE` node (`dr.wt ≥ 1` by `TyP.wt_pos` and `dl.reg.2.wt ≤ dl.wt` by
    `TyP.wt_reg_le`). -/
theorem letLeftSurface_wt_lt
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) :
    (letLeftSurface hA hv hb dl).wt Aw <
      (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr).wt Aw := by
  have hAl : hA.dl.wt Aw < hA.wt Aw := CvP.wt_dl_lt Aw hA
  have hvl : hv.dl.wt Aw < hv.wt Aw := CvP.wt_dl_lt Aw hv
  have hbl : hb.dl.wt Aw < hb.wt Aw := CvP.wt_dl_lt Aw hb
  have hreg : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  have hdr : 1 ≤ dr.wt Aw := TyP.wt_pos Aw dr
  simp only [letLeftSurface, TyP.wt, CvP.wt]
  omega

/-- `letLeftSurface hA hv hb dl` preserves `AssumpPref` when the `CvP.letE`
    components satisfy `AssumpPref`. -/
theorem letLeftSurface_ap
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (hhA : hA.AssumpPref) (hhv : hv.AssumpPref) (hhb : hb.AssumpPref)
    (hdl : dl.AssumpPref) :
    (letLeftSurface hA hv hb dl).AssumpPref :=
  ⟨assumpPref_dl hhA, assumpPref_dl hhv, assumpPref_dl hhb, assumpPref_reg hdl⟩

/-- §8.1 three-leg proof-result continuation closure of `es_letE`, wiring
    `StepIH` (`letE_issued_body_es`), `leftSurfaceCl`, and landed
    `RcicSynLetEtaFinish.letE_proof_right_leg_display` (`letBodyLeftSub`,
    `letProofResult` #7444). -/
theorem es_letE_proof_right_leg
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ hb.dr.reg.1) = true)
    (hl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl))
    (pL : PBit σ ρ (letBodyLeftSub hA hv hb) (letProofResult hA hv hb))
    (pR : PBit σ ρ dr (letProofResult hA hv hb)) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro hq ih
  have hb_es : ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb :=
    letE_issued_body_es Aw tbl hA hv hb dl dr S σ ρ hq ih
  have hl' : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((letLeftSurface hA hv hb dl).eps σ ρ) := hl
  have hsurfL :
      (letLeftSurface hA hv hb dl).eps σ ρ =
        hb.dl.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ) := by
    unfold letLeftSurface
    rw [let_eps_eq]
  have hr' :
      ConvMod (EStep tbl) LvlEq
        (hb.dr.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ))
        (dr.eps σ ρ) := by
    have hcont := letE_proof_right_leg_display tbl σ ρ hA hv hb dr hu pL pR
    cases hve : hv.dl.eps σ ρ <;>
      (simp only [letDisp, hve] at hcont ⊢; exact hcont)
  rw [hsurfL] at hl'
  exact es_letE hA hv hb dl dr hb_es hl' hr'

/-- §8.2 unchanged-declaration closure of `es_letE`
    (`BELOWC_FAILED_READERS_AND_LET_BODY.md` §8.2): when `A' = A` and `v' = v`,
    `StepIH` (`letE_issued_body_es`), `leftSurfaceCl`, and landed
    `RcicSynLetEtaFinish.letSameDeclRight_continuation` (`letSameDeclRight`
    #7444) close `CaseStep` directly without `CvWalkHyp`, `TableClosed`,
    `DisplayFits`, `PBit`, or `BodyAnswers`. -/
theorem es_letE_same_decl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hAeq : A' = A) (hveq : v' = v)
    (hl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl))
    (hr : CL tbl σ ρ (letSameDeclRight hA hv hb dr hAeq hveq) dr) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro hq ih
  have hb_es : ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb :=
    letE_issued_body_es Aw tbl hA hv hb dl dr S σ ρ hq ih
  have hl' : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((letLeftSurface hA hv hb dl).eps σ ρ) := hl
  have hsurfL :
      (letLeftSurface hA hv hb dl).eps σ ρ =
        hb.dl.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ) := by
    unfold letLeftSurface
    rw [let_eps_eq]
  have hr' :
      ConvMod (EStep tbl) LvlEq
        (hb.dr.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ))
        (dr.eps σ ρ) := by
    have hcont := letSameDeclRight_continuation tbl σ ρ hA hv hb dr hAeq hveq hr
    cases hve : hv.dl.eps σ ρ <;>
      (simp only [letDisp, hve] at hcont ⊢; exact hcont)
  rw [hsurfL] at hl'
  exact es_letE hA hv hb dl dr hb_es hl' hr'

/-- Residual ports for `StepSuppliers.es_letE` (`BELOWC_SEMANTIC_WALLS.md` Part II
    and `RcicSynLetRight`). Note that `ES tbl σ ρ hv`,
    `ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb`, and `hb.dr.AssumpPref` are
    **omitted** from `LetEPorts` because `StepIH` (`letE_issued_val_es`,
    `letE_issued_body_es`) and `hq.ap` supply them directly. -/
structure LetEPorts {E : ResolvedEnv} {n : Nat} (w : CvWalkHyp E)
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (σ : Level → Level) (ρ : List Disp) : Prop where
  tableClosed : TableClosed tbl
  displayFits : DisplayFits Γ ρ
  leftSurfaceCl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl)
  valuePBLeft : PBit σ ρ hv.dl hA.dl
  valuePBRight : PBit σ ρ hv.dr hA.dl
  body :
    BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl σ
      (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps σ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps σ ρ) :: ρ)
  rightSurfaceCl :
    CL tbl σ ρ (letRightSurface w hA hv hb.dr hb.dr.reg.1 hb.dr.reg.2) dr

/-- Exact `StepSuppliers.es_letE` statement closed from `StepIH`
    (`letE_issued_val_es`, `letE_issued_body_es`), `hq.ap` (`hb.dr.AssumpPref`),
    and landed Wall 2 (`RcicSynLetRight.letE_dr_of_letBridge`). -/
theorem letE_caseStep_of_ports :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
      (hb : CvP E n (.letBinding A v :: Γ) b b' B)
      (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
      (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (w : CvWalkHyp E)
      (_ports : LetEPorts tbl w hA hv hb dl dr σ ρ),
      CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ A A' v v' b b' B u hA hv hb dl dr S σ ρ w ports hq ih
  have hv_es : ES tbl σ ρ hv :=
    letE_issued_val_es Aw tbl hA hv hb dl dr S σ ρ hq ih
  have hb_es : ES tbl σ (letDisp (hv.dl.eps σ ρ) :: ρ) hb :=
    letE_issued_body_es Aw tbl hA hv hb dl dr S σ ρ hq ih
  have hap : hb.dr.AssumpPref := assumpPref_dr hq.ap.2.2.1
  have hl : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((letLeftSurface hA hv hb dl).eps σ ρ) :=
    ports.leftSurfaceCl
  have hsurf_eq :
      (letLeftSurface hA hv hb dl).eps σ ρ =
        hb.dl.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ) := by
    unfold letLeftSurface
    rw [let_eps_eq]
  have hmid :
      ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
        (hb.dr.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ)) := by
    rw [hsurf_eq] at hl
    exact hl.trans hb_es
  have lans : LetBridgeAnswers tbl w hA hv hb dr σ ρ :=
    { valueES := hv_es
      valuePBLeft := ports.valuePBLeft
      valuePBRight := ports.valuePBRight
      body := ports.body
      rightSurface := ports.rightSurfaceCl }
  have hr :
      ConvMod (EStep tbl) LvlEq
        (hb.dr.eps σ (letDisp (hv.dl.eps σ ρ) :: ρ))
        (dr.eps σ ρ) :=
    letE_dr_of_letBridge ports.tableClosed w hA hv hb dr σ ρ hap ports.displayFits lans
  show ES tbl σ ρ _
  exact hmid.trans hr

/-- §8 `U` right-surface specialization of `LetEPorts` (`RcicSynMixedUSurface` #7479).
    Omits `valueES`, `hb_es`, `valuePBLeft`, `valuePBRight`, `hb.dr.AssumpPref`,
    and `rightSurfaceCl`: `StepIH` supplies `valueES`, `hb_es`, `valuePBLeft`,
    and `valuePBRight` via `Issues.letE_esV`, `Issues.letE_esB_drop` /
    `Issues.letE_esB_inline`, and `Issues.occ_pb` at `pA`, `pvL`, `pvR`, while
    `RcicSynMixedUSurface.letBridgeAnswers_of_requests` discharges
    `rightSurfaceCl` from the decoded native let peer `gA, gv, gb, gT` and
    `USurfaceRequests`. -/
structure LetEUSurfacePorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    (w : CvWalkHyp E) {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type where
  tableClosed : TableClosed tbl
  displayFits : DisplayFits Γ ρ
  leftSurfaceCl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl)
  pA : List Nat
  pvL : List Nat
  pvR : List Nat
  occA :
    P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
      0 pA = some (.ty hA.dl)
  occvL :
    P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
      0 pvL = some (.ty hv.dl)
  occvR :
    P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
      0 pvR = some (.ty hv.dr)
  body :
    BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl σ
      (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps σ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps σ ρ) :: ρ)
  u' : Level
  w' : Level
  B' : Expr Nat
  gA : TyP E n Γ A' (.sort u')
  gv : TyP E n Γ v' A'
  gb : TyP E n (.letBinding A' v' :: Γ) b' B'
  gT : TyP E n Γ (instantiate0 v' B') (.sort w')
  hdr : dr.eps σ ρ = (TyP.letE E n Γ A' u' v' B' b' w' gA gv gb gT).eps σ ρ
  requests : USurfaceRequests tbl hv hb gv gb σ ρ

/-- Exact `StepSuppliers.es_letE` statement closed from `StepIH`
    (`letE_issued_val_es`, `letE_issued_body_es`, `letE_issued_val_pb_left`,
    `letE_issued_val_pb_right`), `hq.ap`, and `LetEUSurfacePorts` via landed
    `RcicSynMixedUSurface.letBridgeAnswers_of_requests` (#7479) and
    `RcicSynLetRight.letE_dr_of_letBridge` (#7452). -/
theorem letE_caseStep_of_uSurfacePorts :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
      (hb : CvP E n (.letBinding A v :: Γ) b b' B)
      (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
      (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (w : CvWalkHyp E)
      (_ports : LetEUSurfacePorts tbl w hA hv hb dl dr S σ ρ),
      CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ A A' v v' b b' B u hA hv hb dl dr S σ ρ w ports hq ih
  have hv_es : ES tbl σ ρ hv :=
    letE_issued_val_es Aw tbl hA hv hb dl dr S σ ρ hq ih
  have hpbL : PBit σ ρ hv.dl hA.dl :=
    letE_issued_val_pb_left Aw tbl hA hv hb dl dr S σ ρ ports.pvL ports.pA
      ports.occvL ports.occA hq ih
  have hpbR : PBit σ ρ hv.dr hA.dl :=
    letE_issued_val_pb_right Aw tbl hA hv hb dl dr S σ ρ ports.pvR ports.pA
      ports.occvR ports.occA hq ih
  have hap : hb.dr.AssumpPref := assumpPref_dr hq.ap.2.2.1
  have lans : LetBridgeAnswers tbl w hA hv hb dr σ ρ :=
    letBridgeAnswers_of_requests ports.tableClosed w hA hv hb dr σ ρ hap
      ports.displayFits hv_es hpbL hpbR ports.body
      ports.gA ports.gv ports.gb ports.gT ports.hdr ports.requests
  exact letE_caseStep_of_ports Aw tbl hA hv hb dl dr S σ ρ w
    { tableClosed := ports.tableClosed
      displayFits := ports.displayFits
      leftSurfaceCl := ports.leftSurfaceCl
      valuePBLeft := hpbL
      valuePBRight := hpbR
      body := ports.body
      rightSurfaceCl := lans.rightSurface }
    hq ih

/-- Kernel-checked occurrence control on `CvP.letE`: every `.cl` child `Issues`
    emits from `.es (CvP.letE ...)` is an `occ_cl` occurrence pair. -/
theorem letE_issued_cl_is_occurrence
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level} {e T₁ T₂ : Expr Nat}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
      (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
      (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) k p = some (.ty D₂)) := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧
        (∃ k p, q.subAt k p = some (.ty D₂)) := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | _ => exact absurd (congrArg esParentTag4 hq) (by simp [esParentTag4, cvpCtorTag4])
  exact aux _ iss rfl

/-! ## §3 `es_eta` (`CvP.eta`) -/

/-- `StepIH` on a `CvP.eta` query yields `CL tbl σ ρ hf dr` via the dedicated
    `Issues.eta_cl` row and `dmStep_pair_below`. -/
theorem eta_issued_fun_cl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)) :
    CL tbl σ ρ hf dr :=
  ih_local Aw tbl hq ih (.cl hf dr S σ ρ) Issues.eta_cl rfl
    (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.eta E n Γ f A B hf dl dr) rfl hf dr
        (by simp only [CvP.wt]; omega) (by simp only [CvP.wt]; omega))))

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ` (`dl` sits at `(0, [1])`),
    `StepIH` and `Issues.occ_pb` supply `PBit σ ρ dl dl.reg.2`, with weight
    bounds and `AssumpPref` discharged automatically from `TyP.wt_reg_le` and
    `hq.ap`. -/
theorem eta_issued_dl_reg_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)) :
    PBit σ ρ dl dl.reg.2 := by
  obtain ⟨_, hapdl, _⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dl dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [1]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdl (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.eta E n Γ f A B hf dl dr)
        rfl dl dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ` (`dr` sits at `(0, [2])`, and
    both `dl` and `dr` have ascribed type `.pi A B`), `StepIH` and
    `Issues.occ_pb` supply `PBit σ ρ dr dl.reg.2`, with weight bounds and
    `AssumpPref` discharged automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem eta_issued_dr_reg_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)) :
    PBit σ ρ dr dl.reg.2 := by
  obtain ⟨_, hapdl, hapdr⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dr dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [2]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdr (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.eta E n Γ f A B hf dl dr)
        rfl dr dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- §3.2 proof-result closure of `es_eta` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
    §3.2): whenever `levelIsZero (σ dl.reg.1) = true` and `dl.reg.2` sits at
    occurrence path `pReg`, `StepIH` (`eta_issued_dl_reg_pb` and
    `eta_issued_dr_reg_pb`) forces both `dl.eps σ ρ = .star` and
    `dr.eps σ ρ = .star`, closing `CaseStep` with **zero `CL`, `PBit`, or
    `EtaPorts` hypotheses**. -/
theorem es_eta_proof_of_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ dl.reg.1) = true)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    eta_issued_dl_reg_pb Aw tbl hf dl dr S σ ρ pReg hocc hq ih
  have hpbR : PBit σ ρ dr dl.reg.2 :=
    eta_issued_dr_reg_pb Aw tbl hf dl dr S σ ρ pReg hocc hq ih
  have hdl_star : dl.eps σ ρ = .star := hpbL.mpr hu
  have hdr_star : dr.eps σ ρ = .star := hpbR.mpr hu
  show ES tbl σ ρ _
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_star, hdr_star]
  exact ConvMod.refl _

/-- §3.2 whole-read-star closure of `es_eta` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
    §3.2): whenever `dl.eps σ ρ = .star` and `dl.reg.2` sits at occurrence path
    `pReg`, `StepIH` (`eta_issued_dl_reg_pb` and `eta_issued_dr_reg_pb`) forces
    `dr.eps σ ρ = .star` as well, closing `CaseStep` with **zero `CL`, `PBit`,
    or `EtaPorts` hypotheses**. -/
theorem es_eta_of_dl_star_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdl_star : dl.eps σ ρ = .star)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    eta_issued_dl_reg_pb Aw tbl hf dl dr S σ ρ pReg hocc hq ih
  exact es_eta_proof_of_reg_occ Aw tbl hf dl dr S σ ρ
    (hpbL.mp hdl_star) pReg hocc hq ih

/-- §3.2 proof-result closure of `es_eta` via `hf.reg.2`: since `hf`, `dl`, and
    `dr` all have ascribed type `.pi A B`, whenever `hf.reg.2` sits at occurrence
    path `pReg` and `levelIsZero (σ hf.reg.1) = true`, `StepIH` and
    `Issues.occ_pb` (at `(0, [1])` and `(0, [2])` against `(0, pReg)`) force both
    `dl.eps σ ρ = .star` and `dr.eps σ ρ = .star`, closing `CaseStep` with
    **zero `CL`, `PBit`, or `EtaPorts` hypotheses**. -/
theorem es_eta_proof_of_hf_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ hf.reg.1) = true)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
        0 pReg = some (.ty hf.reg.2)) :
    CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨haphf, hapdl, hapdr⟩ := hq.ap
  have hreg_wt : hf.reg.2.wt Aw ≤ hf.wt Aw := TyP.wt_reg_le Aw hf
  have hpbL : PBit σ ρ dl hf.reg.2 :=
    ih_issue Aw tbl hq ih (.pb dl hf.reg.2 S σ ρ)
      (Issues.occ_pb (k₁ := 0) (p₁ := [1]) (k₂ := 0) (p₂ := pReg)
        rfl hocc hapdl (assumpPref_reg haphf))
      (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
        (lex_of_dm (dmStep_pair_below Aw
          (CvP.eta E n Γ f A B hf dl dr)
          rfl dl hf.reg.2
          (by simp only [CvP.wt]; omega)
          (by simp only [CvP.wt]; omega)))))
  have hpbR : PBit σ ρ dr hf.reg.2 :=
    ih_issue Aw tbl hq ih (.pb dr hf.reg.2 S σ ρ)
      (Issues.occ_pb (k₁ := 0) (p₁ := [2]) (k₂ := 0) (p₂ := pReg)
        rfl hocc hapdr (assumpPref_reg haphf))
      (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
        (lex_of_dm (dmStep_pair_below Aw
          (CvP.eta E n Γ f A B hf dl dr)
          rfl dr hf.reg.2
          (by simp only [CvP.wt]; omega)
          (by simp only [CvP.wt]; omega)))))
  have hdl_star : dl.eps σ ρ = .star := hpbL.mpr hu
  have hdr_star : dr.eps σ ρ = .star := hpbR.mpr hu
  show ES tbl σ ρ _
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_star, hdr_star]
  exact ConvMod.refl _

/-- On the `.drop` binder branch (`bit = true`), a `CL` from the read body
    function `a_hf` to `wkAtZero (A := A) hf` composes with `CL tbl σ ρ hf dr`
    (supplied by `StepIH` via `Issues.eta_cl`) to yield erased conversion from
    `a_hf.eps σ (.drop :: ρ)` to `dr.eps σ ρ`. -/
theorem eta_wkAtZero_cl_drop
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B A' B' : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (hf : TyP E n Γ f (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (a_hf : TyP E n (.assumption A :: Γ) (lift 0 1 f) (.pi A' B'))
    (hfun : CL tbl σ (.drop :: ρ) a_hf (wkAtZero (A := A) hf))
    (hih : CL tbl σ ρ hf dr) :
    ConvMod (EStep tbl) LvlEq (a_hf.eps σ (.drop :: ρ)) (dr.eps σ ρ) := by
  have hfun' : ConvMod (EStep tbl) LvlEq (a_hf.eps σ (.drop :: ρ)) (hf.eps σ ρ) := by
    simpa [CL, eta_fun_drop] using hfun
  exact hfun'.trans hih

/-- On the `.keep` binder branch (`bit = false`), a `CL` from the read body
    function `a_hf` to `wkAtZero (A := A) hf` composes with the lifted
    `CL tbl σ ρ hf dr` (supplied by `StepIH` via `Issues.eta_cl` and
    `convMod_lift`) to yield erased conversion from `a_hf.eps σ (.keep :: ρ)`
    to `(dr.eps σ ρ).lift 0 1`. -/
theorem eta_wkAtZero_cl_keep
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B A' B' : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (hcl_tbl : TableClosed tbl)
    (hf : TyP E n Γ f (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (a_hf : TyP E n (.assumption A :: Γ) (lift 0 1 f) (.pi A' B'))
    (hfun : CL tbl σ (.keep :: ρ) a_hf (wkAtZero (A := A) hf))
    (hih : CL tbl σ ρ hf dr) :
    ConvMod (EStep tbl) LvlEq (a_hf.eps σ (.keep :: ρ)) ((dr.eps σ ρ).lift 0 1) := by
  have hfun' :
      ConvMod (EStep tbl) LvlEq (a_hf.eps σ (.keep :: ρ)) ((hf.eps σ ρ).lift 0 1) := by
    simpa [CL, eta_fun_keep] using hfun
  exact hfun'.trans (convMod_lift hcl_tbl hih 0 1)

/-- Residual ports for `StepSuppliers.es_eta` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
    §3.2). Crucially, `EtaPorts` **never mentions `dr` at all** (`dr` is not even a
    parameter of `EtaPorts`): `funCl` compares `got.hf` against `wkAtZero (A := A) hf`,
    `argCl` and `argTag` compare `got.ha` against `etaArg hA`, and
    `eta_caseStep_of_ports` bridges `hf` to `dr` exclusively through `StepIH` on
    `Issues.eta_cl` (`eta_issued_fun_cl`). -/
structure EtaPorts
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (σ : Level → Level) (ρ : List Disp) : Type where
  tableWF : TableWF tbl
  u : Level
  hA : TyP E n Γ A (.sort u)
  got : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
  eps :
    dl.eps σ ρ =
      lamErasure (levelIsZero (σ u))
        (appClauseOf got σ (binderDisp (levelIsZero (σ u)) :: ρ))
  funCl :
    CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.hf (wkAtZero (A := A) hf)
  argCl :
    CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.ha (etaArg hA)
  argTag :
    TagCoh σ (binderDisp (levelIsZero (σ u)) :: ρ)
      σ (binderDisp (levelIsZero (σ u)) :: ρ) got.ha (etaArg hA)

/-- Exact `StepSuppliers.es_eta` statement closed from `StepIH`
    (`eta_issued_fun_cl` via `Issues.eta_cl`), `EtaPorts`, and the landed η
    consumers `RcicSynLetEtaFinish.es_eta_zvar_drop` and
    `RcicSynLetEtaFinish.es_eta_zvar_keep` (#7444,
    `BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2). -/
theorem eta_caseStep_of_ports :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {f A B : Expr Nat}
      (hf : TyP E n Γ f (.pi A B))
      (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
      (dr : TyP E n Γ f (.pi A B))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (_ports : EtaPorts Aw tbl hf dl σ ρ),
      CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ f A B hf dl dr S σ ρ ports hq ih
  have hih_cl : CL tbl σ ρ hf dr :=
    eta_issued_fun_cl Aw tbl hf dl dr S σ ρ hq ih
  have hW := ports.eps
  have hfun_hf := ports.funCl
  have harg_cl := ports.argCl
  have harg_tag := ports.argTag
  show ES tbl σ ρ _
  cases hu : levelIsZero (σ ports.u) with
  | true =>
      rw [hu, binderDisp_drop] at hW hfun_hf harg_cl harg_tag
      have hCLf : CL tbl σ (.drop :: ρ) ports.got.hf (wkAtZero (A := A) dr) := by
        show ConvMod (EStep tbl) LvlEq (ports.got.hf.eps σ (.drop :: ρ))
          ((wkAtZero (A := A) dr).eps σ (.drop :: ρ))
        rw [eta_fun_drop]
        exact eta_wkAtZero_cl_drop tbl hf dr ports.got.hf hfun_hf hih_cl
      exact es_eta_zvar_drop hf dl dr ports.hA ports.got.hf ports.got.ha hu
        hW hCLf harg_cl harg_tag
  | false =>
      rw [hu, binderDisp_keep] at hW hfun_hf harg_cl harg_tag
      have hCLf : CL tbl σ (.keep :: ρ) ports.got.hf (wkAtZero (A := A) dr) := by
        show ConvMod (EStep tbl) LvlEq (ports.got.hf.eps σ (.keep :: ρ))
          ((wkAtZero (A := A) dr).eps σ (.keep :: ρ))
        rw [eta_fun_keep]
        exact eta_wkAtZero_cl_keep tbl ports.tableWF.closed hf dr ports.got.hf hfun_hf hih_cl
      exact es_eta_zvar_keep hf dl dr ports.hA ports.got.hf ports.got.ha
        ports.tableWF hu hW hCLf harg_cl harg_tag

/-- Kernel-checked occurrence control on `CvP.eta`: every `.cl` child `Issues`
    emits from `.es (CvP.eta ...)` is either an `occ_cl` occurrence pair or the
    `eta_cl` port (`hf` vs `dr`). -/
theorem eta_issued_cl_variants
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {e T₁ T₂ : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
        (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
        (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) k p = some (.ty D₂)) ∨
    ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (f' A' B' : Expr Nat)
      (hf' : TyP E' n' Γ' f' (.pi A' B'))
      (dl' : TyP E' n' Γ' (.lam A' (.app (lift 0 1 f') (.bvar 0))) (.pi A' B'))
      (dr' : TyP E' n' Γ' f' (.pi A' B'))
      (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx) (S' : ScopedCtx Eₐ E₀' n₀' Γ₀')
      (σ' : Level → Level) (ρ' : List Disp),
      (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ : P2Query Eₐ) =
        .es (CvP.eta E' n' Γ' f' A' B' hf' dl' dr') S' σ' ρ' ∧
      HEq D₁ hf' ∧ HEq D₂ dr' := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.eta E n Γ f A B hf dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧ (∃ k p, q.subAt k p = some (.ty D₂)) ∨
      ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (f' A' B' : Expr Nat)
        (hf' : TyP E' n' Γ' f' (.pi A' B'))
        (dl' : TyP E' n' Γ' (.lam A' (.app (lift 0 1 f') (.bvar 0))) (.pi A' B'))
        (dr' : TyP E' n' Γ' f' (.pi A' B'))
        (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx) (S' : ScopedCtx Eₐ E₀' n₀' Γ₀')
        (σ' : Level → Level) (ρ' : List Disp),
        q = .es (CvP.eta E' n' Γ' f' A' B' hf' dl' dr') S' σ' ρ' ∧
        HEq D₁ hf' ∧ HEq D₂ dr' := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact Or.inl ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | eta_cl =>
        exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          rfl, HEq.rfl, HEq.rfl⟩
    | _ => exact absurd (congrArg esParentTag4 hq) (by simp [esParentTag4, cvpCtorTag4])
  exact aux _ iss rfl

/-! ## §4 `es_consts` (`CvP.consts`) -/

/-- When both endpoints of `CvP.consts` are direct `TyP.const` nodes, their
    type-at-sort witnesses `hTL` and `hTR` sit at `P2Query.subAt` positions
    `(0, [0, 0])` and `(0, [1, 0])` with the common subject
    `instantiateLevels ls m.mtype`, so `Issues.occ_bitCoh` and `StepIH` supply
    `BitCoh σ hTL hTR` (`levelIsZero (σ uL) = levelIsZero (σ uR)`). -/
theorem consts_direct_issued_bitCoh
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {uL uR : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (hresL : E.members r = some m) (hlenL : ls.length = m.arity)
    (hwfL : levelsBounded n ls = true) (heqL : eqNList ls ls)
    (hTL : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uL))
    (hresR : E.members r = some m) (hlenR : ls'.length = m.arity)
    (hwfR : levelsBounded n ls' = true) (heqR : eqNList ls' ls)
    (hTR : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uR))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL)
      (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR)) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL)
      (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR)) S σ ρ)) :
    BitCoh σ hTL hTR := by
  obtain ⟨hapL, hapR⟩ := hq.ap
  exact ih_issue Aw tbl hq ih (.bitCoh hTL hTR S σ ρ)
    (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0, 0]) (k₂ := 0) (p₂ := [1, 0]) rfl rfl hapL hapR)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
          (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL)
          (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR))
        rfl hTL hTR
        (by simp only [CvP.wt, TyP.wt]; omega)
        (by simp only [CvP.wt, TyP.wt]; omega)))))

/-- Direct-`TyP.const` closure of `es_consts`: closes `CaseStep` with **zero
    additional hypotheses** from `StepIH` (`Issues.occ_bitCoh` via
    `consts_direct_issued_bitCoh`), `hq.hom` (`LevelHom σ`), and landed
    `RcicSynMixedLetConst.mixedCL_const_nodes` (#7479). -/
theorem es_consts_direct
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {uL uR : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (hresL : E.members r = some m) (hlenL : ls.length = m.arity)
    (hwfL : levelsBounded n ls = true) (heqL : eqNList ls ls)
    (hTL : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uL))
    (hresR : E.members r = some m) (hlenR : ls'.length = m.arity)
    (hwfR : levelsBounded n ls' = true) (heqR : eqNList ls' ls)
    (hTR : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uR))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL)
      (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR)) S σ ρ) := by
  intro hq ih
  have hbit : levelIsZero (σ uL) = levelIsZero (σ uR) :=
    consts_direct_issued_bitCoh Aw tbl hres hlen hwf hwf' hls
      hresL hlenL hwfL heqL hTL hresR hlenR hwfR heqR hTR S σ ρ hq ih
  have hσ : LevelHom σ := hq.hom
  show ES tbl σ ρ _
  exact mixedCL_const_nodes hresL hlenL hwfL heqL hTL hresR hlenR hwfR heqR hTR
    hbit (fun _ => eqNList_map_congr hσ.eqN_map hls)

/-- The §3.4 left canonical `TyP.const` surface for `CvP.consts`, built from
    `dl.reg` (`RcicSynCanon.es_of_below_consts`). -/
noncomputable def constsCanonLeft
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)) :
    TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype) :=
  TyP.const E n Γ r ls ls m dl.reg.1 hres hlen hwf (eqNList_refl ls) dl.reg.2

/-- The §3.4 right canonical `TyP.const` surface for `CvP.consts`, built from
    `dr.reg` (`RcicSynCanon.es_of_below_consts`). -/
noncomputable def constsCanonRight
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf' : levelsBounded n ls' = true) (hls : eqNList ls ls')
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)) :
    TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype) :=
  TyP.const E n Γ r ls' ls m dr.reg.1 hres
    (by rw [← eqNList_length ls ls' hls]; exact hlen)
    hwf' (eqNList_symm hls) dr.reg.2

/-- `constsCanonLeft` has strictly smaller weight than the enclosing `CvP.consts`
    node (`Aw r < dr.wt Aw` by `TyP.admW_lt_of_const`). -/
theorem constsCanonLeft_wt_lt
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)) :
    (constsCanonLeft hres hlen hwf dl).wt Aw <
      (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr).wt Aw := by
  have hreg := TyP.wt_reg_le Aw dl
  have hAw : Aw r < dr.wt Aw := TyP.admW_lt_of_const Aw dr ⟨ls', rfl⟩
  simp only [constsCanonLeft, TyP.wt, CvP.wt]
  omega

/-- `constsCanonRight` has strictly smaller weight than the enclosing `CvP.consts`
    node (`Aw r < dl.wt Aw` by `TyP.admW_lt_of_const`). -/
theorem constsCanonRight_wt_lt
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)) :
    (constsCanonRight hres hlen hwf' hls dr).wt Aw <
      (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr).wt Aw := by
  have hreg := TyP.wt_reg_le Aw dr
  have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
  simp only [constsCanonRight, TyP.wt, CvP.wt]
  omega

/-- `constsCanonLeft` preserves `AssumpPref` from `dl` via `assumpPref_reg`. -/
theorem constsCanonLeft_ap
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (hdl : dl.AssumpPref) :
    (constsCanonLeft hres hlen hwf dl).AssumpPref := by
  simpa [constsCanonLeft, TyP.AssumpPref] using assumpPref_reg hdl

/-- `constsCanonRight` preserves `AssumpPref` from `dr` via `assumpPref_reg`. -/
theorem constsCanonRight_ap
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf' : levelsBounded n ls' = true) (hls : eqNList ls ls')
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (hdr : dr.AssumpPref) :
    (constsCanonRight hres hlen hwf' hls dr).AssumpPref := by
  simpa [constsCanonRight, TyP.AssumpPref] using assumpPref_reg hdr

/-- Left canonical-surface `EUT` through one admission `A : TypeAdm E Aw r m`,
    wired from landed Wall 1 (`RcicSynConstEutAdm.eut_const_of_admission_views`
    #7443, batch 149) and `hq.hom` (`LevelHom σ`). Relates any `TyP.const` node
    at `(r, ls)` with recorded alias `alias₁` to `constsCanonLeft hres hlen hwf dl`
    via the two admission-view answers `q₁` and `q₂`. -/
theorem consts_canonLeft_eut_adm
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' alias₁ : List Level} {m : CheckedMember} {u₁ : Level}
    (A : TypeAdm E Aw r m)
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ))
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hEq₁ : eqNList ls alias₁)
    (H₁ : TyP E n Γ (instantiateLevels alias₁ m.mtype) (.sort u₁))
    (q₁ : ConvMod (EStep tbl) LvlEq (H₁.eps σ ρ)
      (contextLift (ρ.take Γ.length)
        (A.hT.eps (fun l => σ (instLevel alias₁ l)) (ρ.drop Γ.length))))
    (q₂ : ConvMod (EStep tbl) LvlEq (dl.reg.2.eps σ ρ)
      (contextLift (ρ.take Γ.length)
        (A.hT.eps (fun l => σ (instLevel ls l)) (ρ.drop Γ.length)))) :
    EUT tbl σ ρ
      (TyP.const E n Γ r ls alias₁ m u₁ hres₁ hlen₁ hwf₁ hEq₁ H₁)
      (constsCanonLeft hres hlen hwf dl) :=
  eut_const_of_admission_views tbl A hres₁ hlen₁ hwf₁ hEq₁ H₁
    hres hlen hwf (eqNList_refl ls) dl.reg.2 hq.hom ρ q₁ q₂

/-- Right canonical-surface `EUT` through one admission `A : TypeAdm E Aw r m`,
    wired from landed Wall 1 (`RcicSynConstEutAdm.eut_const_of_admission_views`
    #7443, batch 149) and `hq.hom` (`LevelHom σ`). Relates any `TyP.const` node
    at `(r, ls')` with recorded alias `alias₁` to
    `constsCanonRight hres hlen hwf' hls dr` via the two admission-view answers
    `q₁` and `q₂`. -/
theorem consts_canonRight_eut_adm
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' alias₁ : List Level} {m : CheckedMember} {u₁ : Level}
    (A : TypeAdm E Aw r m)
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ))
    (hres₁ : E.members r = some m) (hlen₁ : ls'.length = m.arity)
    (hwf₁ : levelsBounded n ls' = true) (hEq₁ : eqNList ls' alias₁)
    (H₁ : TyP E n Γ (instantiateLevels alias₁ m.mtype) (.sort u₁))
    (q₁ : ConvMod (EStep tbl) LvlEq (H₁.eps σ ρ)
      (contextLift (ρ.take Γ.length)
        (A.hT.eps (fun l => σ (instLevel alias₁ l)) (ρ.drop Γ.length))))
    (q₂ : ConvMod (EStep tbl) LvlEq (dr.reg.2.eps σ ρ)
      (contextLift (ρ.take Γ.length)
        (A.hT.eps (fun l => σ (instLevel ls l)) (ρ.drop Γ.length)))) :
    EUT tbl σ ρ
      (TyP.const E n Γ r ls' alias₁ m u₁ hres₁ hlen₁ hwf₁ hEq₁ H₁)
      (constsCanonRight hres hlen hwf' hls dr) :=
  eut_const_of_admission_views tbl A hres₁ hlen₁ hwf₁ hEq₁ H₁
    hres (by rw [← eqNList_length ls ls' hls]; exact hlen) hwf'
    (eqNList_symm hls) dr.reg.2 hq.hom ρ q₁ q₂

/-- Residual ports for `StepSuppliers.es_consts` (`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md`
    §3.4). Crucially, `ConstsPorts` **does not assume `BitCoh σ hTL hTR`**
    (`levelIsZero (σ uL) = levelIsZero (σ uR)`) or `CL tbl σ ρ dl dr`: `leftCl`
    relates `dl` only to a left `TyP.const` at sort `uL`, `rightCl` relates `dr`
    only to a right `TyP.const` at sort `uR`, and `consts_caseStep_of_ports`
    bridges `uL` and `uR` exclusively through `StepIH` via `Issues.occ_bitCoh`
    at the occurrence paths `pL` and `pR`. -/
structure ConstsPorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type where
  uL : Level
  uR : Level
  hTL : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uL)
  hTR : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uR)
  pL : List Nat
  pR : List Nat
  occL :
    P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
      0 pL = some (.ty hTL)
  occR :
    P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
      0 pR = some (.ty hTR)
  wtL : hTL.wt Aw < (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr).wt Aw
  wtR : hTR.wt Aw < (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr).wt Aw
  apL : hTL.AssumpPref
  apR : hTR.AssumpPref
  leftCl :
    CL tbl σ ρ dl (TyP.const E n Γ r ls ls m uL hres hlen hwf (eqNList_refl ls) hTL)
  rightCl :
    CL tbl σ ρ dr
      (TyP.const E n Γ r ls' ls m uR hres
        (by rw [← eqNList_length ls ls' hls]; exact hlen)
        hwf' (eqNList_symm hls) hTR)

/-- Specializes `ConstsPorts` to the §3.4 canonical surfaces `constsCanonLeft`
    (`dl.reg.2`) and `constsCanonRight` (`dr.reg.2`), discharging `wtL`, `wtR`,
    `apL`, and `apR` automatically from `TyP.wt_reg_le` and `assumpPref_reg`. -/
noncomputable def ConstsPorts.ofRegSurfaces
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pL pR : List Nat)
    (occL :
      P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
        0 pL = some (.ty dl.reg.2))
    (occR :
      P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
        0 pR = some (.ty dr.reg.2))
    (hdl : dl.AssumpPref) (hdr : dr.AssumpPref)
    (leftCl : CL tbl σ ρ dl (constsCanonLeft hres hlen hwf dl))
    (rightCl : CL tbl σ ρ dr (constsCanonRight hres hlen hwf' hls dr)) :
    ConstsPorts Aw tbl hres hlen hwf hwf' hls dl dr S σ ρ where
  uL := dl.reg.1
  uR := dr.reg.1
  hTL := dl.reg.2
  hTR := dr.reg.2
  pL := pL
  pR := pR
  occL := occL
  occR := occR
  wtL := by
    have hreg := TyP.wt_reg_le Aw dl
    simp only [CvP.wt]
    omega
  wtR := by
    have hreg := TyP.wt_reg_le Aw dr
    simp only [CvP.wt]
    omega
  apL := assumpPref_reg hdl
  apR := assumpPref_reg hdr
  leftCl := leftCl
  rightCl := rightCl

/-- Exact `StepSuppliers.es_consts` statement closed from `StepIH`
    (`Issues.occ_bitCoh` supplying `BitCoh σ ports.hTL ports.hTR`), `hq.hom`
    (`LevelHom σ`), `ConstsPorts`, and landed
    `RcicSynMixedLetConst.mixedCL_const_nodes` (#7479). -/
theorem consts_caseStep_of_ports :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {r : Nat} {ls ls' : List Level} {m : CheckedMember}
      (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
      (hls : eqNList ls ls')
      (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
      (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (_ports : ConstsPorts Aw tbl hres hlen hwf hwf' hls dl dr S σ ρ),
      CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr S σ ρ ports hq ih
  have hbit : levelIsZero (σ ports.uL) = levelIsZero (σ ports.uR) :=
    ih_issue Aw tbl hq ih (.bitCoh ports.hTL ports.hTR S σ ρ)
      (Issues.occ_bitCoh (k₁ := 0) (p₁ := ports.pL) (k₂ := 0) (p₂ := ports.pR)
        ports.occL ports.occR ports.apL ports.apR)
      (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
        (lex_of_dm (dmStep_pair_below Aw
          (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr)
          rfl ports.hTL ports.hTR ports.wtL ports.wtR))))
  have hσ : LevelHom σ := hq.hom
  have hmid :=
    mixedCL_const_nodes (tbl := tbl) hres hlen hwf (eqNList_refl ls) ports.hTL
      hres (by rw [← eqNList_length ls ls' hls]; exact hlen) hwf' (eqNList_symm hls) ports.hTR
      (ρL := ρ) (ρR := ρ) hbit (fun _ => eqNList_map_congr hσ.eqN_map hls)
  show ES tbl σ ρ _
  exact ports.leftCl.trans (hmid.trans (ConvMod.symm' LvlEq.symm' ports.rightCl))

/-- Kernel-checked occurrence control on `CvP.consts`: every `.cl` child `Issues`
    emits from `.es (CvP.consts ...)` is an `occ_cl` occurrence pair. -/
theorem consts_issued_cl_is_occurrence
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {e T₁ T₂ : Expr Nat}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
      (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
      (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ) k p = some (.ty D₂)) := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧
        (∃ k p, q.subAt k p = some (.ty D₂)) := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | _ => exact absurd (congrArg esParentTag4 hq) (by simp [esParentTag4, cvpCtorTag4])
  exact aux _ iss rfl

end Rcic.Syn

#print axioms Rcic.Syn.cvpCtorTag4
#print axioms Rcic.Syn.esParentTag4
#print axioms Rcic.Syn.zetaLocal_issued_value_cl
#print axioms Rcic.Syn.zetaLocal_direct_bvar_issued_pb
#print axioms Rcic.Syn.zetaLocal_issued_reg_pb
#print axioms Rcic.Syn.es_zetaLocal_direct_bvar_proof
#print axioms Rcic.Syn.es_zetaLocal_direct_bvar_rel
#print axioms Rcic.Syn.zetaLocalBvarSurface
#print axioms Rcic.Syn.zetaLocalBvarSurface_wt_lt
#print axioms Rcic.Syn.zetaLocalBvarSurface_ap
#print axioms Rcic.Syn.es_zetaLocal_proof_of_reg_occ
#print axioms Rcic.Syn.ZetaLocalPorts
#print axioms Rcic.Syn.zetaLocal_caseStep_of_ports
#print axioms Rcic.Syn.zetaLocal_issued_cl_variants
#print axioms Rcic.Syn.letE_issued_dom_es
#print axioms Rcic.Syn.letE_issued_val_es
#print axioms Rcic.Syn.letE_issued_body_es_drop
#print axioms Rcic.Syn.letE_issued_body_es_inline
#print axioms Rcic.Syn.letE_issued_body_es
#print axioms Rcic.Syn.letE_issued_val_pb_left
#print axioms Rcic.Syn.letE_issued_val_pb_right
#print axioms Rcic.Syn.letE_issued_val_rel
#print axioms Rcic.Syn.letE_issued_dl_reg_pb
#print axioms Rcic.Syn.letE_issued_dr_reg_pb
#print axioms Rcic.Syn.es_letE_proof_of_reg_occ
#print axioms Rcic.Syn.es_letE_of_dl_star_reg_occ
#print axioms Rcic.Syn.es_letE_direct_left_proof
#print axioms Rcic.Syn.letLeftSurface
#print axioms Rcic.Syn.letLeftSurface_wt_lt
#print axioms Rcic.Syn.letLeftSurface_ap
#print axioms Rcic.Syn.es_letE_proof_right_leg
#print axioms Rcic.Syn.es_letE_same_decl
#print axioms Rcic.Syn.LetEPorts
#print axioms Rcic.Syn.letE_caseStep_of_ports
#print axioms Rcic.Syn.LetEUSurfacePorts
#print axioms Rcic.Syn.letE_caseStep_of_uSurfacePorts
#print axioms Rcic.Syn.letE_issued_cl_is_occurrence
#print axioms Rcic.Syn.eta_issued_fun_cl
#print axioms Rcic.Syn.eta_issued_dl_reg_pb
#print axioms Rcic.Syn.eta_issued_dr_reg_pb
#print axioms Rcic.Syn.es_eta_proof_of_reg_occ
#print axioms Rcic.Syn.es_eta_of_dl_star_reg_occ
#print axioms Rcic.Syn.es_eta_proof_of_hf_reg_occ
#print axioms Rcic.Syn.eta_wkAtZero_cl_drop
#print axioms Rcic.Syn.eta_wkAtZero_cl_keep
#print axioms Rcic.Syn.EtaPorts
#print axioms Rcic.Syn.eta_caseStep_of_ports
#print axioms Rcic.Syn.eta_issued_cl_variants
#print axioms Rcic.Syn.consts_direct_issued_bitCoh
#print axioms Rcic.Syn.es_consts_direct
#print axioms Rcic.Syn.constsCanonLeft
#print axioms Rcic.Syn.constsCanonRight
#print axioms Rcic.Syn.constsCanonLeft_wt_lt
#print axioms Rcic.Syn.constsCanonRight_wt_lt
#print axioms Rcic.Syn.constsCanonLeft_ap
#print axioms Rcic.Syn.constsCanonRight_ap
#print axioms Rcic.Syn.consts_canonLeft_eut_adm
#print axioms Rcic.Syn.consts_canonRight_eut_adm
#print axioms Rcic.Syn.ConstsPorts
#print axioms Rcic.Syn.ConstsPorts.ofRegSurfaces
#print axioms Rcic.Syn.consts_caseStep_of_ports
#print axioms Rcic.Syn.consts_issued_cl_is_occurrence
