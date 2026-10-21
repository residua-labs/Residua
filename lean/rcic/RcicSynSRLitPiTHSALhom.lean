import rcic.RcicSynSRLitPiTHSA

/-!
# `RcicSynSRLitPiTHSALhom` — the TRANSPORT-HEAD family under the `LevelHom` gate

cc 17:30Z (after swe-cleut's REFUSE of #7799 at c3414f3838): the §4
refutation `transportHeadSortAt_refuted` instantiated σ := `sr2_σ`, which is
NOT a `LevelHom` (it zeroes `.succ .zero` while fixing
`.max (.succ .zero) .zero`, breaking `map_succ`/`map_max`) — off-cone. What
the step actually consumes is `Demand.hom : LevelHom σ`; this module restates
the whole family under that exact gate (new names, as #7800 did for rows
14/15/16; the landed-candidate statements are untouched).

## Verdicts at `tableOfI` under the gate

* **The lit tooth evaporates** (kernel-checked, `thsa_lit_gap_closes…`):
  every `LevelHom σ` fixes BOTH lit cutoffs — `σ (.succ .zero) = .succ .zero`
  (`map_zero`+`map_succ`) and `σ (.max (.succ .zero) .zero) =
  .max (.succ .zero) .zero` (`map_max`) — so tooth and surface co-erase to
  `.const 1 []` and the separating `CL` of the off-cone refutation now
  HOLDS at every hom, including the commuting `.ewk` endpoint `sr2LitEwk`.
  The σ-distinguisher is GONE; a gated refutation would have to come from a
  different tooth in the re-typing universe, not from the lit cutoffs.
* **The gated wall** `thsaLhom_lit_wall`: the gated predicate at the
  transport-headed endpoint — same-subject erasure uniqueness for EVERY
  re-typing `D'` at every hom σ. This is canonicity-scale (a full TyP+CvP
  enumeration; the traced transport re-typings all collapse: `esub`-wrapped
  bvar cores inst-collapse to the replacement's erasure, `lsub` localizes a
  closed `const` through, `wk` cannot land at `Γ = []`), so it is named as
  ONE Prop, not claimed.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the gated predicate and the bridges -/

/-- `TransportHeadSortAt` under the `LevelHom σ` gate (`Demand.hom`'s exact
    shape): the same receipt-free same-subject erasure-uniqueness demand,
    instantiable only at homomorphic σ. The body is the ungated body; the
    gate restricts supply, not meaning. -/
def TransportHeadSortAtLhom (tbl : List CRule) (σ : Level → Level)
    (hσ : LevelHom σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : Prop :=
  ∀ {T' : Expr Nat} (D' : TyP E n Γ e T'), CL tbl σ ρ D D'

/-- Bridge: the gated predicate implies the ungated one (same body). -/
theorem thsa_of_thsaLhom (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D : TyP E n Γ e T} (h : TransportHeadSortAtLhom tbl σ hσ ρ D) :
    TransportHeadSortAt tbl σ ρ D := h

/-- Bridge: the ungated predicate implies the gated one at a hom. -/
theorem thsaLhom_of_thsa (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D : TyP E n Γ e T} (h : TransportHeadSortAt tbl σ ρ D) :
    TransportHeadSortAtLhom tbl σ hσ ρ D := h

#print axioms Rcic.Syn.TransportHeadSortAtLhom
#print axioms Rcic.Syn.thsa_of_thsaLhom
#print axioms Rcic.Syn.thsaLhom_of_thsa

/-! ## §2 commutation (gated replay of `thsa_ewk_of`) -/

/-- The `ewk` head commutes under the gate: `eps_ewk` forwards the erasure
    literally, so re-typings of the wrapped subject cohere exactly when they
    cohere for `D`. -/
theorem thsaLhom_ewk_of (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (hext : EnvExt E E) (D : TyP E n Γ e T)
    (h : TransportHeadSortAtLhom tbl σ hσ ρ D) :
    TransportHeadSortAtLhom tbl σ hσ ρ (TyP.ewk E E n Γ e T hext D) :=
  fun D' => h D'

#print axioms Rcic.Syn.thsaLhom_ewk_of

/-! ## §3 kernel implications, gated replays (rows 8 / 5 / 1) -/

/-- `occH1`'s role under the gate: the function-leg decoder `CL` `hclF`,
    from THSA-Lhom at `h1.dr`. -/
theorem thsaLhom_app_hclF (tbl : List CRule) (σ : Level → Level)
    (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (ρ : List Disp)
    (h : TransportHeadSortAtLhom tbl σ hσ ρ h1.dr) :
    CL tbl σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) :=
  h _

/-- `occH2`'s role under the gate: the argument-leg decoder `CL` `hclA`,
    from THSA-Lhom at `h2.dr`. -/
theorem thsaLhom_app_hclA (tbl : List CRule) (σ : Level → Level)
    (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (ρ : List Disp)
    (h : TransportHeadSortAtLhom tbl σ hσ ρ h2.dr) :
    CL tbl σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) :=
  h _

#print axioms Rcic.Syn.thsaLhom_app_hclF
#print axioms Rcic.Syn.thsaLhom_app_hclA

/-- Row 5 `hL` under the gate: `dl` against the canonical left surface,
    from THSA-Lhom at `dl`. -/
theorem thsaLhom_delta_hL {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
    (h : TransportHeadSortAtLhom (tableOfI S.env) σ hσ (S.can σ) dl) :
    Goal (tableOfI S.env)
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)) :=
  h _

/-- Row 5 `hB` under the gate: the instantiated body surface against `hb`,
    from THSA-Lhom at the `deltaDbΓ … hb`-shaped node. -/
theorem thsaLhom_delta_hB {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
    (h : TransportHeadSortAtLhom (tableOfI S.env) σ hσ (S.can σ)
      (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr))) :
    Goal (tableOfI S.env)
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
          (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ)) :=
  h _

#print axioms Rcic.Syn.thsaLhom_delta_hL
#print axioms Rcic.Syn.thsaLhom_delta_hB

/-- Row 5 full field under the gated THSA: `hag` plus THSA-Lhom at `dl`
    and at the body surface node supply the whole `esDeltaKeptWall`,
    consumed by the landed `es_delta_kept_tableOfI`. -/
theorem es_delta_of_thsaLhom (Aw : Nat → Nat) {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hdl : TransportHeadSortAtLhom (tableOfI S.env) σ hσ (S.can σ) dl)
    (hdb : TransportHeadSortAtLhom (tableOfI S.env) σ hσ (S.can σ)
      (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr))) :
    CaseStep Aw (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) :=
  es_delta_kept_tableOfI Aw hres hbody htr hlen hwf hb dl dr S σ hu
    ⟨hag, hdl _, hdb _⟩

#print axioms Rcic.Syn.es_delta_of_thsaLhom

/-- Row 1 occ-role gate bit under the gate: `levelIsZero` agreement from
    THSA-Lhom at the two reg-of-reg sort typings plus the cross-subject
    `EUT` premise (`bitCoh_of_eut_cl`). -/
theorem thsaLhom_consts_hgate (tbl : List CRule) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp)
    (heut : EUT tbl σ ρ dl.reg.2 dr.reg.2)
    (hrrL : TransportHeadSortAtLhom tbl σ hσ ρ dl.reg.2.reg.2)
    (hrrR : TransportHeadSortAtLhom tbl σ hσ ρ dr.reg.2.reg.2) :
    levelIsZero (σ dl.reg.1) = levelIsZero (σ dr.reg.1) :=
  bitCoh_of_eut_cl hW dl.reg.2 dr.reg.2 σ ρ heut (hrrL _) (hrrR _)

/-- Row 1 full field under the gated THSA: the two canonical `CL`s are
    THSA-Lhom instances at the endpoints, the gate bit comes from
    `thsaLhom_consts_hgate`, and the landed `mixedCL_const_nodes` finishes
    the `ES` goal. -/
theorem es_consts_of_thsaLhom {Eₐ : ResolvedEnv} (Aw : Nat → Nat)
    (tbl : List CRule) (hW : TableWF tbl)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp)
    (heut : EUT tbl σ ρ dl.reg.2 dr.reg.2)
    (hdl : TransportHeadSortAtLhom tbl σ hσ ρ dl)
    (hdr : TransportHeadSortAtLhom tbl σ hσ ρ dr)
    (hrrL : TransportHeadSortAtLhom tbl σ hσ ρ dl.reg.2.reg.2)
    (hrrR : TransportHeadSortAtLhom tbl σ hσ ρ dr.reg.2.reg.2) :
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      dl dr) S σ ρ) := by
  intro hq ih
  have hbit : levelIsZero (σ dl.reg.1) = levelIsZero (σ dr.reg.1) :=
    thsaLhom_consts_hgate tbl hW dl dr σ hσ ρ heut hrrL hrrR
  have hmid := mixedCL_const_nodes (tbl := tbl) hres hlen hwf (eqNList_refl ls)
      dl.reg.2 hres (by rw [← eqNList_length ls ls' hls]; exact hlen) hwf'
      (eqNList_symm hls) dr.reg.2 (ρL := ρ) (ρR := ρ) hbit
      (fun _ => eqNList_map_congr hσ.eqN_map hls)
  show ES tbl σ ρ _
  exact (hdl (constsCanonLeft hres hlen hwf dl)).trans
    (hmid.trans (ConvMod.symm' LvlEq.symm' (hdr (constsCanonRight hres hlen hwf'
      hls dr))))

#print axioms Rcic.Syn.thsaLhom_consts_hgate
#print axioms Rcic.Syn.es_consts_of_thsaLhom

/-! ## §4 the gate verdict at `tableOfI`: the lit tooth evaporates -/

/-- The crux arithmetic of the REFUSE: every `LevelHom` fixes BOTH lit
    cutoffs — `map_zero`+`map_succ` pin `.succ .zero`, `map_max` then pins
    `.max (.succ .zero) .zero`. The off-cone distinguisher `sr2_σ` (zeroes
    the first, fixes the second) is exactly what `LevelHom` forbids. -/
theorem levelHom_fixes_lit_cutoffs (σ : Level → Level) (hσ : LevelHom σ) :
    σ (.succ .zero) = .succ (.zero : Level) ∧
      σ (.max (.succ .zero) .zero) = .max (.succ .zero) .zero := by
  refine ⟨?_, ?_⟩
  · rw [hσ.map_succ, hσ.map_zero]
  · rw [hσ.map_max, hσ.map_succ, hσ.map_zero]

#print axioms Rcic.Syn.levelHom_fixes_lit_cutoffs

/-- At every hom the row-7 tooth erases to `.const 1 []` — the surviving
    cutoff `.max (.succ .zero) .zero` is fixed pointwise, so its
    `levelIsZero` stays `false`. -/
theorem sr2_litTooth_eps_lhom (σ : Level → Level) (hσ : LevelHom σ) :
    sr2_litTooth.eps σ [] = ETm.const 1 [] := by
  have ⟨h1, hmax⟩ := levelHom_fixes_lit_cutoffs σ hσ
  have hf : levelIsZero (σ (.max (.succ .zero) .zero)) = false := by
    rw [hmax]; rfl
  have e : sr2_litTooth.eps σ [] =
      (match levelIsZero (σ (.max (.succ .zero) .zero)) with
       | true => ETm.star
       | false => ETm.const 1 (List.map σ [])) := rfl
  rw [e, hf]
  rfl

/-- At every hom the canonical surface erases to `.const 1 []` — the
    surface cutoff `.succ .zero` is fixed pointwise, so its `levelIsZero`
    stays `false`. -/
theorem sr2_litSurface_eps_lhom (σ : Level → Level) (hσ : LevelHom σ) :
    (litSurface (LiteralExpansion.of 0) sr2_zeroTy).eps σ [] = ETm.const 1 [] := by
  have ⟨h1, _⟩ := levelHom_fixes_lit_cutoffs σ hσ
  have hf : levelIsZero (σ (.succ .zero)) = false := by rw [h1]; rfl
  have e : sr2_zeroTy.eps σ [] =
      (match levelIsZero (σ (.succ .zero)) with
       | true => ETm.star
       | false => ETm.const 1 (List.map σ [])) := rfl
  rw [litSurface_eps, e, hf]
  rfl

#print axioms Rcic.Syn.sr2_litTooth_eps_lhom
#print axioms Rcic.Syn.sr2_litSurface_eps_lhom

/-- **The lit gap closes at every hom**: the `CL` whose failure at `sr2_σ`
    carried the off-cone refutation HOLDS at every `LevelHom σ` — tooth and
    surface co-erase to `.const 1 []`. A gated refutation cannot re-use the
    lit cutoffs. -/
theorem thsa_lit_gap_closes_under_levelHom (σ : Level → Level)
    (hσ : LevelHom σ) :
    CL (tableOfI natEnvUWfT) σ [] sr2_litTooth
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy) := by
  show ConvMod (EStep (tableOfI natEnvUWfT)) LvlEq
    (sr2_litTooth.eps σ [])
    ((litSurface (LiteralExpansion.of 0) sr2_zeroTy).eps σ [])
  rw [sr2_litTooth_eps_lhom σ hσ, sr2_litSurface_eps_lhom σ hσ]
  exact ConvMod.refl _

/-- Same closure at the transport-headed endpoint: `eps_ewk` forwards the
    tooth's erasure, so the `.ewk`-wrapped endpoint is CL to the surface at
    every hom — the exact instance the off-cone refutation had killed. -/
theorem thsa_lit_ewk_gap_closes_under_levelHom (σ : Level → Level)
    (hσ : LevelHom σ) :
    CL (tableOfI natEnvUWfT) σ [] sr2LitEwk
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy) := by
  have ew : sr2LitEwk.eps σ [] = sr2_litTooth.eps σ [] := rfl
  show ConvMod (EStep (tableOfI natEnvUWfT)) LvlEq
    (sr2LitEwk.eps σ [])
    ((litSurface (LiteralExpansion.of 0) sr2_zeroTy).eps σ [])
  rw [ew, sr2_litTooth_eps_lhom σ hσ, sr2_litSurface_eps_lhom σ hσ]
  exact ConvMod.refl _

#print axioms Rcic.Syn.thsa_lit_gap_closes_under_levelHom
#print axioms Rcic.Syn.thsa_lit_ewk_gap_closes_under_levelHom

/-! ## §5 the gated wall at the endpoint -/

/-- **The gated predicate at `tableOfI`, named**: same-subject erasure
    uniqueness for EVERY re-typing of the `.ewk`-wrapped lit endpoint, at
    every hom σ. The distinguishing lit instance is DISCHARGED
    (`thsa_lit_ewk_gap_closes_under_levelHom`); what remains is the full
    re-typing enumeration — canonicity-scale (every traced transport
    collapses: an `esub`-wrapped bvar core inst-collapses to the
    replacement's erasure, an `lsub` localizes the closed `const 1 []`
    through, `wk` cannot land at `Γ = []`, and all natEnvU sort cutoffs are
    ≢ `0` so no `★`-divergence exists). Not claimed. -/
def thsaLhom_lit_wall : Prop :=
  ∀ (σ : Level → Level), ∀ (hσ : LevelHom σ),
    TransportHeadSortAtLhom (tableOfI natEnvUWfT) σ hσ [] sr2LitEwk

/-- The wall's distinguishing instance is inhabited and passes: the fixture
    (`tableOfI natEnvUWfT`, `sr2LitEwk`, the lit surface) is real data, and
    the one `CL` that failed off-cone holds at `σ := id` — a `LevelHom`. -/
theorem thsaLhom_lit_wall_instance_id :
    CL (tableOfI natEnvUWfT) id [] sr2LitEwk
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy) :=
  thsa_lit_ewk_gap_closes_under_levelHom id levelHom_id

#print axioms Rcic.Syn.thsaLhom_lit_wall
#print axioms Rcic.Syn.thsaLhom_lit_wall_instance_id
