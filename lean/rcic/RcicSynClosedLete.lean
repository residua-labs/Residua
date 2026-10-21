import rcic.RcicSynStepLetEtaPorts

/-!
# `RcicSynClosedLete` — `es_letE` closed under its genuine walls

swe-letE lane (sortRow `StepSuppliers` supplier group `es_letE`; source field
`RcicSynLetEtaFinish.es_letE_proof_of_pbits` `RcicSynLetEtaFinish.lean:142`,
field filler `RcicSynStepLetEtaPorts.es_letE_field`
`RcicSynStepLetEtaPorts.lean:86`, closer `letE_caseStep_of_ports`
`RcicSynStepFields4.lean:923` over `LetEPorts` `:899`). `closure_claim = 0`.

## Discharge, measured on main 2026-10-19

`es_letE` (`RcicSynStepSkeleton.lean:472`) via `es_letE_field`:

| port | class | evidence |
|---|---|---|
| `ES hv`, `ES hb` (routed), `hb.dr.AssumpPref` | (a) | `letE_issued_val_es` (`RcicSynStepFields4.lean:468`), `letE_issued_body_es` (`:520`), `hq.ap` |
| `valuePBLeft`, `valuePBRight` | (a) | already discharged on main inside `es_letE_field` (`RcicSynStepLetEtaPorts.lean:118-121`) via `letE_issued_val_pb_left`/`_right` (`RcicSynStepFields4.lean:541`/`:577`): `Issues.occ_pb` at `hv.dl`/`hv.dr` × `hA.dl` receipts, `dmStep_pair_below` (`RcicSynBelow.lean:77`) |
| `w : CvWalkHyp E` | **(c) discharged** | `cvWalkHyp_of_envWfT` (`RcicSynMember.lean:60`) from the `EnvWfT E` assembly datum |
| `tableClosed : TableClosed tbl` | **(c) discharged** | `TableWF.closed` (`RcicSynE.lean:527`) — `TableClosed` (`RcicSynCommute.lean:158`) is definitionally the `closed` field — from the `TableWF tbl` assembly datum |
| `displayFits : DisplayFits Γ ρ` | (d) ambient | structural fit of the incoming `ρ` (`RcicSynBelowBoundary.lean:62`); `ρ` is a field input, never demanded |
| `leftSurfaceCl` | (d) | `letLeftSurface` (`RcicSynStepFields4.lean:779`) is freshly assembled from `hA.dl`, `hv.dl`, `hb.dl`, `dl.reg`; `letE_issued_cl_is_occurrence` (`:1055`) kernel-checks every issued `.cl` is an `occ_cl` pair — the surface sits at no `P2Query.subAt` path |
| `pA pvL pvR`, `occA occvL occvR` | (d) | occurrence receipts of `hA.dl`/`hv.dl`/`hv.dr`; the path is **ctor-shape-indexed** — `lefix_occA` (`[0,1]` under `CvP.refl`) vs `lefix_occA_trans` (`[0,2]` under `CvP.trans`), and `lefix_occA_refuted_trans` kernel-refutes the direct path at the wrapped fixture |
| `body : BodyAnswers …` | (d) | per-node structural demand over `hb.dr`'s tree (`RcicSynLetBridge.lean:192`); `Issues` has no row for it |
| `rightSurfaceCl` | (d) | `letRightSurface` (`RcicSynLetRight.lean:36`) freshly assembled; same occurrence-kernel argument |

§8.1 named source `es_letE_proof_of_pbits` (`RcicSynLetEtaFinish.lean:142`):

| port | class | evidence |
|---|---|---|
| `hu : levelIsZero (σ hb.dr.reg.1) = true` | (d) branch data | the proof-result gate: a hypothesis, not a conclusion (inhabited at `σ := fun _ => .zero`, `es_letE_pbits_direct`) |
| `pL : PBit σ ρ dl T0`, `pR : PBit σ ρ dr T0` | **(b) discharged** | NEW `letE_issued_proof_pb_left`/`_right` below: `Issues.occ_pb` (`RcicSynP2Shared.lean:888`) at `dl`/`dr` (literal `(0,[3])`/`(0,[4])`) × the `T0` receipt; `letProofResult_wt_lt` (`RcicSynLetEtaFinish.lean:68`) + `letProofResult_assumpPref` (`:87`) discharge the `Before` bound and `AssumpPref` |
| `pT0` + `occT0` | (d) | `T0 = letSub hb.dr.reg.2 hv.dl hA.dl` (`letProofResult` `:50`) is a `tyCast`-wrapped `lsub` — freshly assembled, at no fixed `subAt` path; reachable at `(0,[3,3])` exactly when `dl`'s `hT` field IS `T0` (`lefix_occT0`), provably not at `(0,[3])` (`lefix_T0_refuted_dlchild`) |

§8.1 three-leg sibling `es_letE_proof_right_leg` (`RcicSynStepFields4.lean:825`)
is strictly dominated by `es_letE_proof_of_pbits` (its `hu`, `pT0`/`occT0`
premises already prove `CaseStep` without `hl` or an `L0` receipt — `dl` sits
at the literal path `[3]`); it is therefore not re-closed here.

§8.2 unchanged-declaration sibling `es_letE_same_decl` (`:863`) is already
wall-minimal: `hAeq`/`hveq` are decidable branch data and `hl`/`hr` are
fresh-surface `CL`s — no `StepIH`-derivable port remains. Already-closed
variants likewise cited, not re-wrapped: `es_letE_proof_of_reg_occ` (`:706`),
`es_letE_of_dl_star_reg_occ` (`:736`), `es_letE_direct_left_proof` (`:761`).

Non-vacuity: `es_letE_closed_direct` inhabits every `es_letE` wall at the
canonical fixture; `es_letE_pbits_direct` inhabits the §8.1 wall at the
`lefixDlT` fixture (`T0` literally stored as `dl`'s `hT`).
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ## §1 `StepIH` discharges the §8.1 `T0`-`PBit`s under a `T0` receipt -/

/-- Whenever `T0 := letProofResult hA hv hb` sits at a `P2Query.subAt`
    occurrence path `pT0` of `.es (CvP.letE ...) S σ ρ` (`dl` sits at the
    literal `(0, [3])`), `Issues.occ_pb` and `StepIH` supply
    `PBit σ ρ dl T0`. The `Before` bound is `letProofResult_wt_lt`, the
    `T0.AssumpPref` is `letProofResult_assumpPref` off `hq.ap`. -/
theorem letE_issued_proof_pb_left
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pT0 : List Nat)
    (occT0 :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pT0 = some (.ty (letProofResult hA hv hb)))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ dl (letProofResult hA hv hb) := by
  obtain ⟨hapA, hapv, hapb, hapdl, _⟩ := hq.ap
  exact ih_issue Aw tbl hq ih (.pb dl (letProofResult hA hv hb) S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [3]) (k₂ := 0) (p₂ := pT0)
      rfl occT0 hapdl
      (letProofResult_assumpPref hA hv hb (assumpPref_dr hapb)
        (assumpPref_dl hapv) (assumpPref_dl hapA)))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)
        rfl dl (letProofResult hA hv hb)
        (by simp only [CvP.wt]; omega)
        (letProofResult_wt_lt Aw hA hv hb dl dr)))))

/-- Whenever `T0` sits at occurrence path `pT0` (`dr` sits at the literal
    `(0, [4])`), `Issues.occ_pb` and `StepIH` supply `PBit σ ρ dr T0`. -/
theorem letE_issued_proof_pb_right
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pT0 : List Nat)
    (occT0 :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pT0 = some (.ty (letProofResult hA hv hb)))
    (hq : Demand (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ dr (letProofResult hA hv hb) := by
  obtain ⟨hapA, hapv, hapb, _, hapdr⟩ := hq.ap
  exact ih_issue Aw tbl hq ih (.pb dr (letProofResult hA hv hb) S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [4]) (k₂ := 0) (p₂ := pT0)
      rfl occT0 hapdr
      (letProofResult_assumpPref hA hv hb (assumpPref_dr hapb)
        (assumpPref_dl hapv) (assumpPref_dl hapA)))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)
        rfl dr (letProofResult hA hv hb)
        (by simp only [CvP.wt]; omega)
        (letProofResult_wt_lt Aw hA hv hb dl dr)))))

/-! ## §2 the §8.1 finish, closed -/

/-- The named source field, closed: `es_letE_proof_of_pbits`'s two `PBit`
    premises are (b)-discharged from `StepIH`; what remains is the proof-result
    gate `hu` and the `T0` occurrence receipt `(pT0, occT0)` — the (d) wall. -/
theorem es_letE_proof_of_pbits_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ hb.dr.reg.1) = true)
    (pT0 : List Nat)
    (occT0 :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pT0 = some (.ty (letProofResult hA hv hb))) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl (letProofResult hA hv hb) :=
    letE_issued_proof_pb_left Aw tbl hA hv hb dl dr S σ ρ pT0 occT0 hq ih
  have hpbR : PBit σ ρ dr (letProofResult hA hv hb) :=
    letE_issued_proof_pb_right Aw tbl hA hv hb dl dr S σ ρ pT0 occT0 hq ih
  exact es_letE_proof_of_pbits tbl σ ρ hA hv hb dl dr hu hpbL hpbR

/-! ## §3 the field, closed under its measured walls -/

/-- `es_letE` (the exact `StepSuppliers` field statement) with every (a)/(b)
    port discharged inside `es_letE_field` and the two (c) ambient ports
    discharged here from assembly data: `w` by `cvWalkHyp_of_envWfT hE` and
    `tableClosed` by `hTbl.closed`. The remaining premises are exactly the
    measured (d) walls: ambient `displayFits`; the fresh
    `leftSurfaceCl`/`rightSurfaceCl` `CL`s; the occurrence pack
    `pA pvL pvR` + `occA occvL occvR`; and the structural `body` demand. -/
theorem es_letE_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hE : EnvWfT E) (hTbl : TableWF tbl)
    (displayFits : DisplayFits Γ ρ)
    (leftSurfaceCl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl))
    (pA pvL pvR : List Nat)
    (occA :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pA = some (.ty hA.dl))
    (occvL :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvL = some (.ty hv.dl))
    (occvR :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvR = some (.ty hv.dr))
    (body :
      BodyAnswers (cvWalkHyp_of_envWfT hE) (iotaPack_of_cvWalkHyp (cvWalkHyp_of_envWfT hE))
        (fun hext' h => derivedIotaExt hext' h) tbl σ (envExt_refl E) hb.dr
        (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
        (letDisp (hv.dl.eps σ ρ) :: ρ) [] .nil
        (letDisp (hv.dr.eps σ ρ) :: ρ))
    (rightSurfaceCl :
      CL tbl σ ρ (letRightSurface (cvWalkHyp_of_envWfT hE) hA hv hb.dr hb.dr.reg.1
        hb.dr.reg.2) dr) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) :=
  es_letE_field Aw tbl hA hv hb dl dr S σ ρ (cvWalkHyp_of_envWfT hE) hTbl.closed
    displayFits leftSurfaceCl pA pvL pvR occA occvL occvR body rightSurfaceCl

/-! ## §4 fixture: `let x : sort 1 := sort 0; sort 0` at `emptyEnv` -/

/-- `sort 0`. -/
def lefixS0 : Expr Nat := .sort .zero

/-- `sort 1`. -/
def lefixS1 : Expr Nat := .sort (.succ .zero)

/-- `sort 2`. -/
def lefixS2 : Expr Nat := .sort (.succ (.succ .zero))

/-- `sort 0 : sort 1` in the empty context. -/
def lefixH0 : TyP emptyEnv 0 [] lefixS0 lefixS1 :=
  TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)

/-- `sort 1 : sort 2` in the empty context. -/
def lefixH1 : TyP emptyEnv 0 [] lefixS1 lefixS2 :=
  TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `sort 0 : sort 1` under the fixture let-binding. -/
def lefixH0Γ : TyP emptyEnv 0 [.letBinding lefixS1 lefixS0] lefixS0 lefixS1 :=
  TyP.sort emptyEnv 0 [.letBinding lefixS1 lefixS0] .zero (.succ .zero) (eqN_refl _)

/-- The domain conversion `sort 1 ≡ sort 1` at `sort 2`, by reflexivity. -/
def lefixHa : CvP emptyEnv 0 [] lefixS1 lefixS1 lefixS2 :=
  CvP.refl emptyEnv 0 [] lefixS1 lefixS2 lefixH1 lefixH1 lefixH1

/-- The value conversion `sort 0 ≡ sort 0` at `sort 1`, by reflexivity. -/
def lefixHv : CvP emptyEnv 0 [] lefixS0 lefixS0 lefixS1 :=
  CvP.refl emptyEnv 0 [] lefixS0 lefixS1 lefixH0 lefixH0 lefixH0

/-- The body conversion `sort 0 ≡ sort 0` at `sort 1` under the binding. -/
def lefixHb : CvP emptyEnv 0 [.letBinding lefixS1 lefixS0] lefixS0 lefixS0 lefixS1 :=
  CvP.refl emptyEnv 0 [.letBinding lefixS1 lefixS0] lefixS0 lefixS1
    lefixH0Γ lefixH0Γ lefixH0Γ

/-- The walk hypothesis at `emptyEnv`, from `EnvWfT.empty`. -/
noncomputable def lefixWalk : CvWalkHyp emptyEnv :=
  cvWalkHyp_of_envWfT EnvWfT.empty

/-- The left endpoint, canonical: `.letE (sort 1) (sort 0) (sort 0)` typed by
    its own component derivations — `letLeftSurface`-shaped by construction. -/
noncomputable def lefixDl :
    TyP emptyEnv 0 [] (.letE lefixS1 lefixS0 lefixS0) (instantiate0 lefixS0 lefixS1) :=
  TyP.letE emptyEnv 0 [] lefixS1 (.succ (.succ .zero)) lefixS0 lefixS1 lefixS0
    (.succ (.succ .zero)) lefixH1 lefixH0 lefixH0Γ lefixH1

/-- The right endpoint, canonical: `letRightSurface` of the fixture's body
    regularity — `rightSurfaceCl`-shaped by construction. -/
noncomputable def lefixDr :
    TyP emptyEnv 0 [] (.letE lefixS1 lefixS0 lefixS0) (instantiate0 lefixS0 lefixS1) :=
  letRightSurface lefixWalk lefixHa lefixHv lefixHb.dr lefixHb.dr.reg.1 lefixHb.dr.reg.2

/-- The canonical `CvP.letE` node at the fixture. -/
noncomputable def lefixNode :
    CvP emptyEnv 0 [] (.letE lefixS1 lefixS0 lefixS0) (.letE lefixS1 lefixS0 lefixS0)
      (instantiate0 lefixS0 lefixS1) :=
  CvP.letE emptyEnv 0 [] lefixS1 lefixS1 lefixS0 lefixS0 lefixS0 lefixS0 lefixS1
    (.succ (.succ .zero)) lefixHa lefixHv lefixHb lefixDl lefixDr

/-- The §8.1 proof-result `T0` at the fixture — `letSub` of `hb.dr.reg.2`. -/
noncomputable def lefixT0 :
    TyP emptyEnv 0 [] (instantiate0 lefixS0 lefixS1) (.sort lefixHb.dr.reg.1) :=
  letProofResult lefixHa lefixHv lefixHb

/-- A `dl` whose `hT` field literally IS `T0` — the shape under which the `T0`
    occurrence receipt is satisfiable at the literal path `(0, [3, 3])`. -/
noncomputable def lefixDlT :
    TyP emptyEnv 0 [] (.letE lefixS1 lefixS0 lefixS0) (instantiate0 lefixS0 lefixS1) :=
  TyP.letE emptyEnv 0 [] lefixS1 (.succ (.succ .zero)) lefixS0 lefixS1 lefixS0
    lefixHb.dr.reg.1 lefixH1 lefixH0 lefixH0Γ lefixT0

/-- The `CvP.letE` node with `lefixDlT` as left endpoint. -/
noncomputable def lefixNodeT :
    CvP emptyEnv 0 [] (.letE lefixS1 lefixS0 lefixS0) (.letE lefixS1 lefixS0 lefixS0)
      (instantiate0 lefixS0 lefixS1) :=
  CvP.letE emptyEnv 0 [] lefixS1 lefixS1 lefixS0 lefixS0 lefixS0 lefixS0 lefixS1
    (.succ (.succ .zero)) lefixHa lefixHv lefixHb lefixDlT lefixDr

/-- `hA` wrapped in a `trans` — the receipt shape the direct path does not
    serve. -/
def lefixHaT : CvP emptyEnv 0 [] lefixS1 lefixS1 lefixS2 :=
  CvP.trans emptyEnv 0 [] lefixS1 lefixS1 lefixS1 lefixS2 lefixHa lefixHa
    lefixH1 lefixH1

/-- The `CvP.letE` node with the `trans`-wrapped domain conversion. -/
noncomputable def lefixNodeTr :
    CvP emptyEnv 0 [] (.letE lefixS1 lefixS0 lefixS0) (.letE lefixS1 lefixS0 lefixS0)
      (instantiate0 lefixS0 lefixS1) :=
  CvP.letE emptyEnv 0 [] lefixS1 lefixS1 lefixS0 lefixS0 lefixS0 lefixS0 lefixS1
    (.succ (.succ .zero)) lefixHaT lefixHv lefixHb lefixDl lefixDr

/-! ## §5 occurrence receipts at the fixture (positive witnesses) -/

/-- `hA.dl` occurs at `(0, [0,1])` when `hA` is `refl`-headed. -/
theorem lefix_occA {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt (.es lefixNode S σ ρ) 0 [0, 1] = some (.ty lefixHa.dl) := rfl

/-- `hv.dl` occurs at `(0, [1,1])` when `hv` is `refl`-headed. -/
theorem lefix_occvL {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt (.es lefixNode S σ ρ) 0 [1, 1] = some (.ty lefixHv.dl) := rfl

/-- `hv.dr` occurs at `(0, [1,2])` when `hv` is `refl`-headed. -/
theorem lefix_occvR {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt (.es lefixNode S σ ρ) 0 [1, 2] = some (.ty lefixHv.dr) := rfl

/-- `hA.dl` of a `trans`-wrapped domain conversion occurs at `(0, [0,2])` —
    through `.cv h2`, not the `refl` path. The receipt is satisfiable, but the
    path is ctor-shape-indexed. -/
theorem lefix_occA_trans {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt (.es lefixNodeTr S σ ρ) 0 [0, 2] = some (.ty lefixHaT.dl) := rfl

/-- `T0` occurs at `(0, [3,3])` exactly when `dl`'s `hT` field literally is
    `letProofResult hA hv hb` — the §8.1 wall is satisfiable. -/
theorem lefix_occT0 {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt (.es lefixNodeT S σ ρ) 0 [3, 3] =
      some (.ty (letProofResult lefixHa lefixHv lefixHb)) := rfl

/-! ## §6 teeth: the direct paths provably fail off-shape -/

/-- **Tooth — the `hA.dl` receipt is ctor-shape-indexed.** At the `trans`-wrapped
    `hA`, the direct `refl` path `(0, [0,1])` resolves to `.cv lefixHa` — a
    conversion node, not `.ty lefixHaT.dl`. -/
theorem lefix_occA_refuted_trans {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ (P2Query.subAt (.es lefixNodeTr S σ ρ) 0 [0, 1] =
        some (.ty lefixHaT.dl)) := by
  intro h
  have hres : P2Query.subAt (.es lefixNodeTr S σ ρ) 0 [0, 1] =
      some (.cv lefixHa) := rfl
  rw [hres] at h
  cases Option.some.inj h

/-- **Tooth — `T0` is not a forest child position.** At the canonical fixture
    `(0, [3])` resolves to `.ty lefixDl` — a letE-headed typing of
    `.letE s1 s0 s0` — while `letProofResult hA hv hb` types `s1` at a sort:
    the `some` equation would force `.letE s1 s0 s0 = instantiate0 s0 s1`. The
    genuine receipt is the shape-indexed `(0, [3,3])` of `lefix_occT0`. -/
theorem lefix_T0_refuted_dlchild {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ (P2Query.subAt (.es lefixNode S σ ρ) 0 [3] =
        some (.ty (letProofResult lefixHa lefixHv lefixHb))) := by
  intro h
  have hres : P2Query.subAt (.es lefixNode S σ ρ) 0 [3] = some (.ty lefixDl) := rfl
  rw [hres] at h
  cases Option.some.inj h

/-! ## §7 non-vacuity: the fields are inhabited -/

/-- **Non-vacuity of `es_letE`'s retained walls**: at the canonical fixture all
    of them are inhabited — `EnvWfT.empty` and `tableWF_nil` for the (c)
    ports' data, `DisplayFits.nil`, `leftSurfaceCl`/`rightSurfaceCl` by
    `ConvMod.refl` (each surface IS the canonical endpoint), the receipts at
    the literal `refl`-shape paths, and `body` by `True` (`hb.dr` is a `sort`
    leaf). -/
theorem es_letE_closed_direct {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw [] (.es lefixNode S σ ρ) :=
  es_letE_closed Aw [] lefixHa lefixHv lefixHb lefixDl lefixDr S σ ρ
    EnvWfT.empty tableWF_nil
    (DisplayFits.nil ρ) (.refl _) [0, 1] [1, 1] [1, 2] rfl rfl rfl trivial (.refl _)

/-- **Non-vacuity of the §8.1 wall**: at the `lefixDlT` fixture the `T0`
    receipt is `(0, [3,3])` by `rfl`, and at `σ := fun _ => .zero` the gate
    `levelIsZero (σ hb.dr.reg.1)` holds by `rfl` — the `CaseStep` is
    unconditional. -/
theorem es_letE_pbits_direct {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp) :
    CaseStep Aw [] (.es lefixNodeT S (fun _ => .zero) ρ) :=
  es_letE_proof_of_pbits_closed Aw [] lefixHa lefixHv lefixHb lefixDlT lefixDr
    S (fun _ => .zero) ρ rfl [3, 3] rfl

#print axioms Rcic.Syn.letE_issued_proof_pb_left
#print axioms Rcic.Syn.letE_issued_proof_pb_right
#print axioms Rcic.Syn.es_letE_proof_of_pbits_closed
#print axioms Rcic.Syn.es_letE_closed
#print axioms Rcic.Syn.lefixS0
#print axioms Rcic.Syn.lefixS1
#print axioms Rcic.Syn.lefixS2
#print axioms Rcic.Syn.lefixH0
#print axioms Rcic.Syn.lefixH1
#print axioms Rcic.Syn.lefixH0Γ
#print axioms Rcic.Syn.lefixHa
#print axioms Rcic.Syn.lefixHv
#print axioms Rcic.Syn.lefixHb
#print axioms Rcic.Syn.lefixWalk
#print axioms Rcic.Syn.lefixDl
#print axioms Rcic.Syn.lefixDr
#print axioms Rcic.Syn.lefixNode
#print axioms Rcic.Syn.lefixT0
#print axioms Rcic.Syn.lefixDlT
#print axioms Rcic.Syn.lefixNodeT
#print axioms Rcic.Syn.lefixHaT
#print axioms Rcic.Syn.lefixNodeTr
#print axioms Rcic.Syn.lefix_occA
#print axioms Rcic.Syn.lefix_occvL
#print axioms Rcic.Syn.lefix_occvR
#print axioms Rcic.Syn.lefix_occA_trans
#print axioms Rcic.Syn.lefix_occT0
#print axioms Rcic.Syn.lefix_occA_refuted_trans
#print axioms Rcic.Syn.lefix_T0_refuted_dlchild
#print axioms Rcic.Syn.es_letE_closed_direct
#print axioms Rcic.Syn.es_letE_pbits_direct
