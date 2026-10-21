import rcic.RcicSynStepZetaField
import rcic.RcicSynLetInline
import rcic.RcicSynClosedIotaret

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-!
# `StepSuppliers` `es_zeta`/`es_zetaLocal` — the closed fragments

`swe-zeta` lane of the RCIC `sortRow` supplier effort.
`research/rcic/sortrow/STEP_SUPPLIERS.md`,
`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §3.2 / §4, S15 §8, S16 §2.3,
**W-ER2-SHIFTED-VALUE-SCOPE**. `closure_claim = 0`.

Composition only: the landed closers `es_zeta_field` /
`es_zetaLocal_field` (`RcicSynStepZetaField`) do the assembly; the landed
direct-bvar closures `es_zetaLocal_direct_bvar_proof` /
`es_zetaLocal_direct_bvar_rel` (`RcicSynStepFields4`) cover the bvar
fragment; `zetaLocal_issued_reg_pb` supplies `PBit σ ρ hv dl.reg.2` once an
occurrence path to `dl.reg.2` exists in the payload. No landed statement
is edited and no landed proof is copied.

## §0 Measurement — every port of the two fields, classified

Categories: (a) already discharged on main; (b) answerable from `StepIH`
through an existing `Issues` row; (c) provable outright from landed lemmas;
(d) genuinely open — kept as a named premise with a satisfiability witness.

### `es_zeta` (`CvP.zeta`, `es_zeta_field` `RcicSynStepZetaField.lean:79`)

| port | exact type | class | evidence |
|---|---|---|---|
| `hsurf` | `CL tbl σ ρ dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2)` | (d) general / **(c) at `dl` literal-`letE`** | `zeta_issued_cl_is_occurrence` (`RcicSynStepFields1.lean:206`): every `.cl` a zeta node issues is an `occ_cl` pair — the `letE` surface is freshly built, never at a `subAt` position. Name search (`letE`/`surface`/`eps_let_clause` producers) and type search (`CL _ _ dl (TyP.letE …)`) find only the `Below`-route `zeta_dl` (`RcicSynClause.lean:159`). For `dl := TyP.letE … hA hv hb hT` the surface is `dl` itself (`reg` is `⟨w, hT⟩`), so `hsurf` is reflexivity — `es_zeta_letE_closed` below. |
| `hreduct` | `CL tbl σ ρ (letSub hb hv hA) dr` | **(d)** | `letSub` is freshly built (`RcicSynLetSub.lean:37`) and `dr` is arbitrary; the issued `zeta_pb` row supplies `PBit` only. Name/type searches find only the `Below`-route `zeta_dr` (`RcicSynLetSub.lean:68`). Satisfiable: `dr := letSub hb hv hA` makes it `ConvMod.refl` — `zeta_hreduct_satisfiable`. |

### `es_zetaLocal` (`CvP.zetaLocal`, `es_zetaLocal_field` `RcicSynStepZetaField.lean:98`)

| port | exact type | class | evidence |
|---|---|---|---|
| `CL tbl σ ρ hv dr` | — | **(a)** | `zetaLocal_issued_value_cl` (`RcicSynStepFields4.lean`) via the issued `Issues.zetaLocal_cl` row; never a port. |
| `hsurf` | `CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)` | (d) general / **(c) at `dl` literal-`bvar`** | surface is freshly built; `zetaLocal_issued_cl_variants` confines issued `.cl` rows to `occ_cl` pairs and `zetaLocal_cl`. For `dl := TyP.bvar …` the surface is `dl` itself (up to the `lookupType` proof) — `zetaLocal_hsurf_satisfiable`. |
| `hregOcc` | `levelIsZero (σ dl.reg.1) = true → ∃ pReg, subAt … = some (.ty dl.reg.2)` | **(a)/(c) fragments, (d) general** | `dl := TyP.bvar`: `(0, [1, 0])` — discharged zero-hypothesis by `es_zetaLocal_direct_bvar_proof`. `dl := TyP.conv … hc` with `hc` non-transport: `dl.reg.2 = hc.dr` is `hc`'s last `dchildren` entry — `(0, [1, 1, k])` — `zetaLocal_conv_reg_occ`/`es_zetaLocal_conv_closed` below. `dl` transport-headed or `conv` over a transport: `reg.2` is freshly wrapped — (d). |
| `hres` | `levelIsZero (σ dl.reg.1) = false → ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)` | (d) general / **(c) at the spine-aligned `i = 0` fragment** | the display/slot correspondence is the R2/`localize` scope fact — not a `P2Query` object; name search (`resolve`, `DispEntry`, `localize`) and type search (`ConvMod … (resolve ρ i) (… .eps …)`) find no unconditional producer. At `i = 0`, `hv := wkLetAtZero hv₀`, `ρ := .inline (hv₀.eps σ ρ₀) :: ρ₀` both sides are `hv₀.eps σ ρ₀` definitionally-modulo `eps_wk_not_keep` — `es_zetaLocal_zero_inline_closed`. The `.drop` analogue reduces `hres` to the `letDrop` condition — `es_zetaLocal_zero_drop_closed`. |

Net effect: the `(b)/(c)` fragments close as `*_closed` theorems below; the
retained `(d)` ports are named verbatim with satisfiability witnesses —
no port is weakened, dropped silently, or replaced by an equivalent
restatement.
-/

/-! ## §1 `dr` is the last derivation child of every non-transport `CvP`

Landed on main as `CvP.dr_dchildren_last` (`RcicSynClosedIotaret`,
batch 195, in the concrete index form `hc.dchildren[hc.dchildren.length - 1]?
= some (.ty hc.dr)`) — imported, not re-proved. -/

/-! ## §2 `hregOcc` discharged for `conv`-headed `dl` over a rule node -/

/-- `dl := TyP.conv … hinner hc` has `dl.reg = ⟨u, hc.dr⟩`; when `hc` is a
    non-transport `CvP`, `hc.dr` sits at the last `dchildren` position of
    `hc`, i.e. payload path `(0, [1, 1, k])` inside the `zetaLocal` node.
    This discharges `es_zetaLocal_field`'s `hregOcc` port outright — the
    `PBit σ ρ hv dl.reg.2` leg then comes from `zetaLocal_issued_reg_pb`. -/
theorem zetaLocal_conv_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v A' : Expr Nat} {u : Level}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (hinner : TyP E n Γ (.bvar i) A')
    (hc : CvP E n Γ A' A (.sort u)) (htr : hc.isTransport = false)
    (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ∃ pReg : List Nat,
      P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv
          (TyP.conv E n Γ (.bvar i) A' A u hinner hc) dr) S σ ρ) 0 pReg =
        some (.ty (TyP.conv E n Γ (.bvar i) A' A u hinner hc).reg.2) := by
  refine ⟨[1, 1, hc.dchildren.length - 1], ?_⟩
  show (DNode.subAt (.cv (CvP.zetaLocal E n Γ i A v hval hty hv
      (TyP.conv E n Γ (.bvar i) A' A u hinner hc) dr))
      [1, 1, hc.dchildren.length - 1] = _)
  show (DNode.subAt (.cv hc) [hc.dchildren.length - 1] = _)
  show ((hc.dchildren[hc.dchildren.length - 1]?).bind (·.subAt []) = _)
  rw [CvP.dr_dchildren_last hc htr]
  rfl

/-- `es_zetaLocal` for `dl := TyP.conv … hinner hc` over a non-transport
    `hc`: `hregOcc` is discharged outright by `zetaLocal_conv_reg_occ`, so
    only `hsurf` and `hres` remain as ports — two fewer than the general
    field statement. -/
theorem es_zetaLocal_conv_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v A' : Expr Nat} {u : Level}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (hinner : TyP E n Γ (.bvar i) A')
    (hc : CvP E n Γ A' A (.sort u)) (htr : hc.isTransport = false)
    (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hsurf : CL tbl σ ρ (TyP.conv E n Γ (.bvar i) A' A u hinner hc)
      (zetaLocalBvarSurface hty (TyP.conv E n Γ (.bvar i) A' A u hinner hc)))
    (hres : levelIsZero (σ u) = false →
      ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv
      (TyP.conv E n Γ (.bvar i) A' A u hinner hc) dr) S σ ρ) :=
  es_zetaLocal_field Aw tbl hval hty hv
    (TyP.conv E n Γ (.bvar i) A' A u hinner hc) dr S σ ρ hsurf
    (fun _ => zetaLocal_conv_reg_occ hval hty hv hinner hc htr dr S σ ρ)
    (fun hzu => hres (by simpa [TyP.reg] using hzu))

/-! ## §3 `hsurf` discharged for the literal-`letE` `dl` of `es_zeta` -/

/-- `es_zeta` for `dl := TyP.letE …` built from the node's own `hA hv hb`:
    the canonical `letE` surface is `dl` itself (`dl.reg = ⟨w, hT⟩`), so
    `hsurf` is reflexivity and only `hreduct` remains as a port. -/
theorem es_zeta_letE_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hreduct : CL tbl σ ρ (letSub hb hv hA) dr) :
    CaseStep Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb
      (TyP.letE E n Γ A u value B body w hA hv hb hT) dr) S σ ρ) :=
  es_zeta_field Aw tbl hA hv hb
    (TyP.letE E n Γ A u value B body w hA hv hb hT) dr S σ ρ
    (by
      show CL tbl σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT)
        (TyP.letE E n Γ A u value B body w hA hv hb hT)
      exact ConvMod.refl _)
    hreduct

/-! ## §4 `hres` discharged on the spine-aligned `i = 0` fragment -/

/-- `wkLetAtZero`'s erasure under a head `.inline` display carrying its own
    erasure: the `wk` is not `keep`-blocked, so the display resolves to the
    body's own erasure — the `hres` correspondence at `i = 0`. -/
theorem wkLetAtZero_eps_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A v : Expr Nat} (D : TyP E n Γ e T)
    (σ : Level → Level) (ρ₀ : List Disp) :
    (wkLetAtZero (A := A) (v := v) D).eps σ (.inline (D.eps σ ρ₀) :: ρ₀) =
      D.eps σ ρ₀ := by
  rw [wkLetAtZero, eps_tyCastCtx,
    eps_wk_not_keep (hk := Or.inr (Or.inr ⟨D.eps σ ρ₀, by
      simp [List.get?_cons_zero]⟩)),
    removeAt_zero]

/-- `wkLetAtZero`'s erasure under a head `.drop` display: same
    not-`keep`-blocked computation. -/
theorem wkLetAtZero_eps_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A v : Expr Nat} (D : TyP E n Γ e T)
    (σ : Level → Level) (ρ₀ : List Disp) :
    (wkLetAtZero (A := A) (v := v) D).eps σ (.drop :: ρ₀) = D.eps σ ρ₀ := by
  rw [wkLetAtZero, eps_tyCastCtx,
    eps_wk_not_keep (hk := Or.inr (Or.inl (by simp [List.get?_cons_zero]))),
    removeAt_zero]

/-- `es_zetaLocal` at `i = 0` on the context-spine-aligned stored value
    `hv := wkLetAtZero hv₀`, a direct `TyP.bvar` `dl`, a relevant regularity
    sort, and the head-`.inline` display that `RoutedDisp.letInline` /
    `DispEntry.zero_letInline` produce. `resolve ρ 0` and `hv.eps σ ρ` are
    both `hv₀.eps σ ρ₀`, so `hres` is reflexivity — zero residual ports. -/
theorem es_zetaLocal_zero_inline_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ v₀ : Expr Nat} {u : Level}
    (hv₀ : TyP E n Γ v₀ A₀)
    (hval : lookupValue (.letBinding A₀ v₀ :: Γ) 0 = some (lift 0 1 v₀))
    (hty : lookupType (.letBinding A₀ v₀ :: Γ) 0 = some (lift 0 1 A₀))
    (hA : TyP E n (.letBinding A₀ v₀ :: Γ) (lift 0 1 A₀) (.sort u))
    (dr : TyP E n (.letBinding A₀ v₀ :: Γ) (lift 0 1 v₀) (lift 0 1 A₀))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ₀ : List Disp)
    (hu : levelIsZero (σ u) = false) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n (.letBinding A₀ v₀ :: Γ) 0
      (lift 0 1 A₀) (lift 0 1 v₀) hval hty (wkLetAtZero (A := A₀) (v := v₀) hv₀)
      (TyP.bvar E n (.letBinding A₀ v₀ :: Γ) 0 (lift 0 1 A₀) u hty hA) dr)
      S σ (.inline (hv₀.eps σ ρ₀) :: ρ₀)) := by
  refine es_zetaLocal_direct_bvar_rel Aw tbl hval hty
    (wkLetAtZero (A := A₀) (v := v₀) hv₀) hA dr S σ
    (.inline (hv₀.eps σ ρ₀) :: ρ₀) hu ?_
  show ConvMod (EStep tbl) LvlEq (hv₀.eps σ ρ₀)
    ((wkLetAtZero (A := A₀) (v := v₀) hv₀).eps σ (.inline (hv₀.eps σ ρ₀) :: ρ₀))
  rw [wkLetAtZero_eps_inline]
  exact ConvMod.refl _

/-- `es_zetaLocal` at `i = 0`, spine-aligned `hv`, direct `TyP.bvar` `dl`,
    relevant sort, and the head-`.drop` display that `RoutedDisp.letDrop` /
    `DispEntry.zero_letDrop` produce. `resolve ρ 0` is `.star`; `hres`
    reduces to the `letDrop` condition `hv₀.eps σ ρ₀ = .star` itself, which
    stays as the single honest premise. -/
theorem es_zetaLocal_zero_drop_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ v₀ : Expr Nat} {u : Level}
    (hv₀ : TyP E n Γ v₀ A₀)
    (hval : lookupValue (.letBinding A₀ v₀ :: Γ) 0 = some (lift 0 1 v₀))
    (hty : lookupType (.letBinding A₀ v₀ :: Γ) 0 = some (lift 0 1 A₀))
    (hA : TyP E n (.letBinding A₀ v₀ :: Γ) (lift 0 1 A₀) (.sort u))
    (dr : TyP E n (.letBinding A₀ v₀ :: Γ) (lift 0 1 v₀) (lift 0 1 A₀))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ₀ : List Disp)
    (hu : levelIsZero (σ u) = false)
    (hstar : hv₀.eps σ ρ₀ = .star) :
    CaseStep Aw tbl (.es (CvP.zetaLocal E n (.letBinding A₀ v₀ :: Γ) 0
      (lift 0 1 A₀) (lift 0 1 v₀) hval hty (wkLetAtZero (A := A₀) (v := v₀) hv₀)
      (TyP.bvar E n (.letBinding A₀ v₀ :: Γ) 0 (lift 0 1 A₀) u hty hA) dr)
      S σ (.drop :: ρ₀)) := by
  refine es_zetaLocal_direct_bvar_rel Aw tbl hval hty
    (wkLetAtZero (A := A₀) (v := v₀) hv₀) hA dr S σ (.drop :: ρ₀) hu ?_
  show ConvMod (EStep tbl) LvlEq .star
    ((wkLetAtZero (A := A₀) (v := v₀) hv₀).eps σ (.drop :: ρ₀))
  rw [wkLetAtZero_eps_drop, hstar]
  exact ConvMod.refl _

/-! ## §5 Satisfiability witnesses for the retained `(d)` ports -/

/-- `hreduct` is satisfiable: taking `dr := letSub hb hv hA` makes the port
    `CL tbl σ ρ (letSub hb hv hA) dr` reflexivity. Non-vacuous: `letSub`
    exists as a real derivation (`RcicSynLetSub.lean:37`). -/
theorem zeta_hreduct_satisfiable
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (σ : Level → Level) (ρ : List Disp) :
    ∃ dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B),
      CL tbl σ ρ (letSub hb hv hA) dr :=
  ⟨letSub hb hv hA, ConvMod.refl _⟩

/-- `hsurf` (`es_zetaLocal`) is satisfiable at `dl := TyP.bvar …`: the
    canonical surface is `dl` itself (same `lookupType` proof slot, same
    `reg` = `⟨u, hA⟩`), so the port is reflexivity. -/
theorem zetaLocal_hsurf_satisfiable
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u : Level}
    (hty : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ (TyP.bvar E n Γ i A u hty hA)
      (zetaLocalBvarSurface hty (TyP.bvar E n Γ i A u hty hA)) :=
  ConvMod.refl _

/-- `hsurf` (`es_zeta`) is satisfiable at the literal-`letE` `dl`: the
    surface is `dl` itself. -/
theorem zeta_hsurf_satisfiable
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body B : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT)
      (TyP.letE E n Γ A u value B body
        (TyP.letE E n Γ A u value B body w hA hv hb hT).reg.1 hA hv hb
        (TyP.letE E n Γ A u value B body w hA hv hb hT).reg.2) :=
  ConvMod.refl _

/-- `hres` is satisfiable: at `i = 0`, `hv := wkLetAtZero hv₀`, and the
    head-`.inline` display of `hv₀`'s own erasure, both sides of the port
    are `hv₀.eps σ ρ₀`. -/
theorem zetaLocal_hres_satisfiable
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A₀ v₀ : Expr Nat}
    (hv₀ : TyP E n Γ v₀ A₀) (σ : Level → Level) (ρ₀ : List Disp) :
    ∃ ρ : List Disp, ConvMod (EStep tbl) LvlEq (resolve ρ 0)
      ((wkLetAtZero (A := A₀) (v := v₀) hv₀).eps σ ρ) :=
  ⟨.inline (hv₀.eps σ ρ₀) :: ρ₀, by
    show ConvMod (EStep tbl) LvlEq (hv₀.eps σ ρ₀)
      ((wkLetAtZero (A := A₀) (v := v₀) hv₀).eps σ
        (.inline (hv₀.eps σ ρ₀) :: ρ₀))
    rw [wkLetAtZero_eps_inline]
    exact ConvMod.refl _⟩

/-- `hregOcc` is satisfiable at `dl := TyP.bvar …`: `dl.reg.2 = hA` sits at
    payload path `(0, [1, 0])`. -/
theorem zetaLocal_hregOcc_satisfiable
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} {u : Level}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (hA : TyP E n Γ A (.sort u)) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ∃ pReg : List Nat,
      P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv
        (TyP.bvar E n Γ i A u hty hA) dr) S σ ρ) 0 pReg =
        some (.ty (TyP.bvar E n Γ i A u hty hA).reg.2) :=
  ⟨[1, 0], rfl⟩

end Rcic.Syn

#print axioms Rcic.Syn.zetaLocal_conv_reg_occ
#print axioms Rcic.Syn.es_zetaLocal_conv_closed
#print axioms Rcic.Syn.es_zeta_letE_closed
#print axioms Rcic.Syn.wkLetAtZero_eps_inline
#print axioms Rcic.Syn.wkLetAtZero_eps_drop
#print axioms Rcic.Syn.es_zetaLocal_zero_inline_closed
#print axioms Rcic.Syn.es_zetaLocal_zero_drop_closed
#print axioms Rcic.Syn.zeta_hreduct_satisfiable
#print axioms Rcic.Syn.zetaLocal_hsurf_satisfiable
#print axioms Rcic.Syn.zeta_hsurf_satisfiable
#print axioms Rcic.Syn.zetaLocal_hres_satisfiable
#print axioms Rcic.Syn.zetaLocal_hregOcc_satisfiable
