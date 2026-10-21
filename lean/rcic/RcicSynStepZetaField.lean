import rcic.RcicSynStepFields1
import rcic.RcicSynStepFields4

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-!
# `StepSuppliers` fields `es_zeta` / `es_zetaLocal` — exact statements under named ports

`research/rcic/sortrow/STEP_SUPPLIERS.md`,
`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §3.2 / §4, S15 §8, S16 §2.3,
**W-ER2-SHIFTED-VALUE-SCOPE**. `closure_claim = 0`.

Each theorem below carries the exact `StepSuppliers` field telescope copied
verbatim from `RcicSynStepSkeleton.StepSuppliers`, followed by the ports the
issued-row grammar cannot supply as **named hypotheses** (never weakened,
never vacuous). Composition only: the closers `zeta_caseStep_of_port_cls`
(`RcicSynStepFields1`) and `zetaLocal_caseStep_of_ports` +
`zetaLocal_issued_reg_pb` (`RcicSynStepFields4`) do the assembly; no landed
implementation is re-proved.

## Port triage (per `~/.residua-lean/briefs/sortrow-ports.md` categories)

### `es_zeta` (`CvP.zeta`) — two `CL` ports, both retained verbatim

* `hsurf : CL tbl σ ρ dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2)`
  — **(d) genuinely unanswerable under `StepIH`.** A `.cl` child of the
  `.es` node is demanded only via `rootCl` (which pins `ρ = S.can σ`; the
  field's `ρ` is arbitrary) or an `Issues` edge, and
  `zeta_issued_cl_is_occurrence` (`RcicSynStepFields1`) proves every `.cl`
  row a zeta node issues is an `occ_cl` occurrence pair — the canonical
  `letE` surface is freshly built and never sits at a `P2Query.subAt`
  payload position. A new `Issues` constructor would falsify that landed
  control theorem. No landed decoder/eps lemma identifies `dl.eps σ ρ` with
  the surface's erasure for arbitrary `dl`.
* `hreduct : CL tbl σ ρ (letSub hb hv hA) dr` — **(d), same obstruction**:
  `letSub hb hv hA` is freshly built and `dr` is arbitrary. The issued
  `zeta_pb` row supplies only `PBit[hv, hA]`, which the closer consumes
  internally; it answers neither `CL`.

### `es_zetaLocal` (`CvP.zetaLocal`) — `CL[hv, dr]` always from `StepIH`; `PBit` leg discharged under an occurrence condition

* `CL tbl σ ρ hv dr` — **(a)** supplied by `StepIH` through the issued
  `Issues.zetaLocal_cl` row (`zetaLocal_issued_value_cl`); it never appears
  as a port.
* `ZetaLocalPorts.slotCoh`, proof-sort leg `PBit σ ρ hv dl.reg.2` —
  **(a), conditional**: whenever `dl.reg.2` sits at a `subAt` occurrence
  path (`hregOcc` below), `zetaLocal_issued_reg_pb` discharges it from
  `StepIH` through `Issues.occ_pb`. What remains is the occurrence
  condition itself, `hregOcc` — for `wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`-
  headed `dl`, `dl.reg.2` is a freshly wrapped derivation rather than a
  payload child, so the condition is **(d)** for those inputs (for a
  direct `TyP.bvar` `dl` it holds at `(0, [1, 0])`, and
  `es_zetaLocal_direct_bvar_proof` already closes that subcase with zero
  hypotheses).
* `hsurf : CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)` — **(d)**:
  `zetaLocalBvarSurface hty dl` is freshly built;
  `zetaLocal_issued_cl_variants` confines the issued `.cl` rows to `occ_cl`
  pairs and `zetaLocal_cl` (`hv` vs `dr`), neither of which names it.
* `hres : levelIsZero (σ dl.reg.1) = false →
    ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)` — **(d)**: the
  relevant-sort display/slot correspondence is a `ConvMod` between a
  routed display and an erasure — not a `P2Query` object — so no `Issues`
  row can request it, and `ρ` is arbitrary.

Net effect for `es_zetaLocal`: of `ZetaLocalPorts`' two fields, `surfaceCl`
is retained verbatim and `slotCoh` is split — its proof-sort `PBit` leg is
discharged from `StepIH` under the named occurrence hypothesis `hregOcc`,
and its relevant-sort display leg is retained verbatim as `hres`.
-/

/-- The `StepSuppliers.es_zeta` field with the two §3.2 `CL` ports as named
    hypotheses. Both are (d): the issued `.cl` grammar under a zeta parent is
    occurrence-only (`zeta_issued_cl_is_occurrence`), and the canonical
    `TyP.letE` surface / `letSub` reduct are freshly built. -/
theorem es_zeta_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hsurf : CL tbl σ ρ dl
      (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2))
    (hreduct : CL tbl σ ρ (letSub hb hv hA) dr) :
    CaseStep Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) :=
  zeta_caseStep_of_port_cls Aw tbl hA hv hb dl dr S σ ρ hsurf hreduct

/-- The `StepSuppliers.es_zetaLocal` field. `CL tbl σ ρ hv dr` comes from
    `StepIH` inside `zetaLocal_caseStep_of_ports`; the `PBit` leg of
    `ZetaLocalPorts.slotCoh` is discharged from `StepIH` under the named
    occurrence hypothesis `hregOcc`; `hsurf` and `hres` are the retained (d)
    ports with their exact statements. -/
theorem es_zetaLocal_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hsurf : CL tbl σ ρ dl (zetaLocalBvarSurface hty dl))
    (hregOcc : levelIsZero (σ dl.reg.1) = true →
      ∃ pReg : List Nat,
        P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
          0 pReg = some (.ty dl.reg.2))
    (hres : levelIsZero (σ dl.reg.1) = false →
      ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro hq ih
  refine zetaLocal_caseStep_of_ports Aw tbl hval hty hv dl dr S σ ρ
    ⟨hsurf, ?_⟩ hq ih
  match hzi : levelIsZero (σ dl.reg.1) with
  | true =>
      obtain ⟨pReg, hocc⟩ := hregOcc hzi
      exact Or.inl ⟨rfl,
        zetaLocal_issued_reg_pb Aw tbl hval hty hv dl dr S σ ρ pReg hocc hq ih⟩
  | false =>
      exact Or.inr ⟨rfl, hres hzi⟩
