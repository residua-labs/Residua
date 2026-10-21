import rcic.RcicSynSRLitPiLit
import rcic.RcicSynSRConsts
import rcic.RcicSynSRDelta
import rcic.RcicSynClosedEsapp
import rcic.RcicSynPBitAll

/-!
# `RcicSynSRLitPiTHSA` — the TRANSPORT-HEAD wall family: one weaker predicate

cc 2026-10-20 16:00Z task. Rows 1 (`EsConstsWall` occ leg, `RcicSynSRConsts`),
8 (`EsAppOccTransportWall`, `RcicSynSRAppOcc`) and 5 (`esDeltaKeptWall`,
`RcicSynSRDelta`) all stop at the transport heads `ewk`/`esub`/`linst`/`cctx`:
the `subAt`/`RegSubAt` receipts are kernel-refuted there because a transport
head's `reg`/`dr` is a freshly re-wrapped node, never a forest member.

## `TransportHeadSortAt` — the receipt-free demand

ONE predicate, what the step needs at a transport-headed endpoint:
**same-subject erasure uniqueness** — every re-typing `D'` of the endpoint's
subject (same env, same ctx, any type) erases `ConvMod`-equal at `(σ, ρ)`.

Weaker than a `RegSubAt` receipt as a demand on the endpoint: no forest
membership, only the semantic conclusions the receipt route was manufacturing
through `ih_issue` (the `hgate` bit, the decoder `CL`s, the canon `CL`s) —
asked for directly, so it stays suppliable exactly where those conclusions
hold, transport head or not.

## Results

* Commutation (positive): the display- and context-neutral head `ewk`
  commutes — `TransportHeadSortAt D → TransportHeadSortAt (.ewk … D)`
  (`eps_ewk` forwards the erasure literally). No other head commutes at
  fixed `(E, n, Γ, σ, ρ)`: `cctx` re-indexes the context, `linst` re-scopes
  `σ`, `esub`/`lsub`/`wk` shift `ρ` — the induction on the transport stack
  stops there (documented, not papered over).
* Kernel implications to each wall: row 8's occ-role decoder `CL`s
  (`thsa_app_hclF`/`thsa_app_hclA`), row 5's `hL`/`hB` legs
  (`thsa_delta_hL`/`thsa_delta_hB`, plus the full field
  `es_delta_of_thsa`), row 1's `leftCl`/`rightCl` and occ-role `hgate`
  (`thsa_consts_leftCl`/`_rightCl`/`thsa_consts_hgate`, plus the full field
  `es_consts_of_thsa`).
* Refutation at `tableOfI`: `transportHeadSortAt_refuted` — the predicate
  FAILS at a transport-headed endpoint: the row-7 tooth `sr2_litTooth`
  wrapped in `.ewk` (`envExt_refl`) still erases to `const 1 []` while the
  canonical surface erases to `★` (`sr2_not_cl_litTooth`), so the ∀-re-typing
  clause dies at `D' := litSurface`. All fixture data inhabited; the refuted
  proposition is exactly the predicate at one transport-headed endpoint.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the predicate -/

/-- What the step needs at a transport-headed endpoint: same-subject erasure
    uniqueness — every re-typing `D'` of `D`'s subject (same `E`/`Γ`, any
    type index) is `CL` at `(σ, ρ)`. Receipt-free: no `subAt` path, no
    `RegSubAt`, no forest membership. -/
def TransportHeadSortAt (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : Prop :=
  ∀ {T' : Expr Nat} (D' : TyP E n Γ e T'), CL tbl σ ρ D D'

/-! ## §2 commutation — the display-neutral transport heads -/

/-! Only `ewk` commutes at fixed `(E, n, Γ, σ, ρ)`. Every other head moves
the re-typing universe: `cctx` re-indexes `.assumption A :: Γ` to
`.assumption A' :: Γ`; `linst` re-scopes `σ` to `σ ∘ instLevel ls`; `esub`/
`lsub`/`wk` shift `ρ`. The induction on the transport stack stops there. -/

/-- The `ewk` head commutes: `eps_ewk` forwards the erasure literally, so
    re-typings of the wrapped subject cohere exactly when they cohere for
    `D`. -/
theorem thsa_ewk_of (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (hext : EnvExt E E) (D : TyP E n Γ e T)
    (h : TransportHeadSortAt tbl σ ρ D) :
    TransportHeadSortAt tbl σ ρ (TyP.ewk E E n Γ e T hext D) :=
  fun D' => h D'

#print axioms Rcic.Syn.TransportHeadSortAt
#print axioms Rcic.Syn.thsa_ewk_of

/-! ## §3 kernel implications to the transport-head walls -/

/-! ### row 8 (`es_app`, `EsAppOccTransportWall`'s stuck legs)

`EsAppClosedPorts.occH1`/`occH2` have no semantic disjunct: at a
transport-headed `h1` the `subAt` receipt is refuted
(`es_app_occWall_refuted`) and the `isTransport = false` escape is false, so
the ports structure is uninhabitable there. What the receipts manufacture
downstream (`es_app_field`, `RcicSynStepFields5.lean:456/:470`) is exactly
the two decoder `CL`s below — direct `TransportHeadSortAt` instances at the
re-wrapped right endpoints. -/

/-- `occH1`'s role: the function-leg decoder `CL` `hclF`, from THSA at
    `h1.dr` (the `.ewk`-re-wrapped endpoint). -/
theorem thsa_app_hclF (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp)
    (h : TransportHeadSortAt tbl σ ρ h1.dr) :
    CL tbl σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) :=
  h _

/-- `occH2`'s role: the argument-leg decoder `CL` `hclA`, from THSA at
    `h2.dr`. -/
theorem thsa_app_hclA (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp)
    (h : TransportHeadSortAt tbl σ ρ h2.dr) :
    CL tbl σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) :=
  h _

#print axioms Rcic.Syn.thsa_app_hclF
#print axioms Rcic.Syn.thsa_app_hclA

/-! ### row 5 (`es_delta`, `esDeltaKeptWall`'s `hL`/`hB` legs)

The kept-branch wall's two `CL` legs are same-subject re-typing coherences:
`deltaCanonL` re-types the `.const r ls` subject at the body's own
regularity, `deltaDbΓ` re-types the instantiated body. Both are direct
`TransportHeadSortAt` instances, so THSA supplies the whole wall minus
`hag` — and the landed conditional field consumes it. -/

/-- `hL`: `dl` against the canonical left surface, from THSA at `dl`. -/
theorem thsa_delta_hL {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (h : TransportHeadSortAt (tableOfI S.env) σ (S.can σ) dl) :
    Goal (tableOfI S.env)
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)) :=
  h _

/-- `hB`: the instantiated body surface against `hb`, from THSA at
    `deltaDbΓ … hb`-shaped node (the wall's left operand). -/
theorem thsa_delta_hB {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (h : TransportHeadSortAt (tableOfI S.env) σ (S.can σ)
      (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr))) :
    Goal (tableOfI S.env)
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
          (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ)) :=
  h _

#print axioms Rcic.Syn.thsa_delta_hL
#print axioms Rcic.Syn.thsa_delta_hB

/-- Row 5 full field under THSA: `hag` plus THSA at `dl` and at the body
    surface node supply the whole `esDeltaKeptWall`, consumed by the landed
    `es_delta_kept_tableOfI`. -/
theorem es_delta_of_thsa (Aw : Nat → Nat) {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hdl : TransportHeadSortAt (tableOfI S.env) σ (S.can σ) dl)
    (hdb : TransportHeadSortAt (tableOfI S.env) σ (S.can σ)
      (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr))) :
    CaseStep Aw (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) :=
  es_delta_kept_tableOfI Aw hres hbody htr hlen hwf hb dl dr S σ hu
    ⟨hag, hdl _, hdb _⟩

#print axioms Rcic.Syn.es_delta_of_thsa

/-! ### row 1 (`es_consts`, `EsConstsWall`'s occ legs)

`EsConstsWall`'s `occL`/`occR` legs are kernel-refuted at transport heads;
what they manufacture inside `consts_caseStep_of_ports` is (i) the two
canonical `CL`s — THSA instances at `dl`/`dr` — and (ii) the gate bit
`hgate` — composed from THSA at the reg-of-reg sort typings plus the
cross-subject `EUT` premise (`bitCoh_of_eut_cl`). The full field follows
by the landed `mixedCL_const_nodes` composition. -/

/-- The occ-role gate bit: `levelIsZero (σ dl.reg.1) = levelIsZero (σ dr.reg.1)`
    from THSA at the two reg-of-reg sort typings (both CL legs are
    same-`.sort u`-subject instances) plus the cross-subject `EUT`. -/
theorem thsa_consts_hgate (tbl : List CRule) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp)
    (heut : EUT tbl σ ρ dl.reg.2 dr.reg.2)
    (hrrL : TransportHeadSortAt tbl σ ρ dl.reg.2.reg.2)
    (hrrR : TransportHeadSortAt tbl σ ρ dr.reg.2.reg.2) :
    levelIsZero (σ dl.reg.1) = levelIsZero (σ dr.reg.1) :=
  bitCoh_of_eut_cl hW dl.reg.2 dr.reg.2 σ ρ heut (hrrL _) (hrrR _)

/-- Row 1 full field under THSA: the two canonical `CL`s are THSA instances
    at the endpoints, the gate bit comes from `thsa_consts_hgate`, and the
    landed `mixedCL_const_nodes` finishes the `ES` goal. -/
theorem es_consts_of_thsa {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hW : TableWF tbl)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (heut : EUT tbl σ ρ dl.reg.2 dr.reg.2)
    (hdl : TransportHeadSortAt tbl σ ρ dl)
    (hdr : TransportHeadSortAt tbl σ ρ dr)
    (hrrL : TransportHeadSortAt tbl σ ρ dl.reg.2.reg.2)
    (hrrR : TransportHeadSortAt tbl σ ρ dr.reg.2.reg.2) :
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      dl dr) S σ ρ) := by
  intro hq ih
  have hbit : levelIsZero (σ dl.reg.1) = levelIsZero (σ dr.reg.1) :=
    thsa_consts_hgate tbl hW dl dr σ ρ heut hrrL hrrR
  have hσ : LevelHom σ := hq.hom
  have hmid := mixedCL_const_nodes (tbl := tbl) hres hlen hwf (eqNList_refl ls)
      dl.reg.2 hres (by rw [← eqNList_length ls ls' hls]; exact hlen) hwf'
      (eqNList_symm hls) dr.reg.2 (ρL := ρ) (ρR := ρ) hbit
      (fun _ => eqNList_map_congr hσ.eqN_map hls)
  show ES tbl σ ρ _
  exact (hdl (constsCanonLeft hres hlen hwf dl)).trans
    (hmid.trans (ConvMod.symm' LvlEq.symm' (hdr (constsCanonRight hres hlen hwf'
      hls dr))))

#print axioms Rcic.Syn.thsa_consts_hgate
#print axioms Rcic.Syn.es_consts_of_thsa

/-! ## §4 the refutation at `tableOfI`

THSA FAILS at a transport-headed endpoint: wrap the row-7 tooth
`sr2_litTooth` in `.ewk` (`envExt_refl` — the one head that commutes, so the
failure is the tooth's, not the head's). The wrapped endpoint still erases
to `const 1 []` while the canonical surface `litSurface` erases to `★`
(`sr2_not_cl_litTooth` / `not_convMod_star_const`), so the ∀-re-typing
clause dies at `D' := litSurface`. The refuted proposition is exactly
`TransportHeadSortAt` at one transport-headed endpoint; the fixture data is
inhabited by construction. -/

/-- The transport-headed refutation witness: the row-7 tooth behind the
    commuting `ewk` head. -/
def sr2LitEwk : TyP natEnvU 0 [] (.lit 0) (.const 0 []) :=
  TyP.ewk natEnvU natEnvU 0 [] (.lit 0) (.const 0 []) (envExt_refl natEnvU)
    sr2_litTooth

/-- **THSA refuted at `tableOfI`**: the `.ewk`-wrapped tooth is a
    transport-headed endpoint whose same-subject re-typing universe includes
    the canonical surface, and that one `CL` already fails. -/
theorem transportHeadSortAt_refuted :
    ¬ TransportHeadSortAt (tableOfI natEnvUWfT) sr2_σ [] sr2LitEwk := by
  intro h
  exact sr2_not_cl_litTooth
    (h (litSurface (LiteralExpansion.of 0) sr2_zeroTy))

/-- The witness really is transport-headed: its erasure is the tooth's
    (`eps_ewk`), and it fails against the surface exactly as the tooth does
    — the head commuted, the obligation did not get easier. -/
theorem sr2LitEwk_eps : sr2LitEwk.eps sr2_σ [] = .const 1 [] :=
  eps_ewk sr2_σ []

#print axioms Rcic.Syn.sr2LitEwk
#print axioms Rcic.Syn.transportHeadSortAt_refuted
#print axioms Rcic.Syn.sr2LitEwk_eps
