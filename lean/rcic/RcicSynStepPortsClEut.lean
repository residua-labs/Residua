import rcic.RcicSynStepCore4

/-!
# `cl_case` / `eut_case` field assembly — discharging the `RcicSynStepCore4` ports

The `StepSuppliers.cl_case` / `.eut_case` fields are `CaseStep`s over an arbitrary
`TyP` pair `(D₁, D₂)` of the same subject `e`, same context `Γ`, same site
`S : ScopedCtx Eₐ E₀ n₀ Γ₀` and display `(σ, ρ)`.  `RcicSynStepCore4` closed the
individual head-cells through `*_caseStep_of_ports` theorems whose `*Ports`
records held the obligations that are **not** reachable through `Issues` rows:
binder-display bodies, `letSub`-substituted pairs, regularity-derived typings,
and `eqN` sort coherences.

This module is the per-cell dispatch.  Eliminating `TyP` needs a *free* subject
index (transport constructors carry `lift`/`instantiate`-computed subjects, so
`cases` on a concretely-indexed derivation fails its index equations), hence the
convoy: the right operand is re-abstracted to `D₂' : TyP E n Γ e₂ T₂` with a
receipt `he : e₂ = e`, both sides are `cases`-eliminated while `e` is still
free, and each cell then discharges `he` — `subst` where a side is a variable
(`conv`, `ewk`, `cctx`), `cases he` for same-head rule pairs (which substitutes
the component equalities and reduces the `he ▸ D₂'` cast) and for impossible
off-diagonal rule pairs (noConfusion), and the residual hypotheses
`clOther`/`eutOther` (transport-headed cells, where `he` is genuinely stuck and
the `▸` cast is handed over as data).

Ports discharged outright (brief class (c)):

* `EutBvarPorts.sortConv` — it is *definitionally* `CL tbl σ ρ hA₁ hA₂`
  (`CL` unfolds to `ConvMod (EStep tbl) LvlEq` of the `eps`), and `hA₁`/`hA₂`
  are payload positions `(0,[0])`/`(1,[0])` of the bvar operands, so `occ_cl`
  issues it at a strictly smaller `tyPairMeas` — new zero-port
  `eut_bvar_bvar_caseStep`.
* `eut_sort_sort`'s `LevelSub σ` — every demanded query is `Hom`
  (`Demand.hom`), and `LevelHom.levelSub` projects it.
* `EutBvarPorts`'s `hAeq : A₁ = A₂` — both `lookupType Γ i` receipts agree.

Ports remaining as named hypotheses (brief class (d), exact statements kept):

* `ClPiPorts`/`ClLamPorts`/`EutLamPorts` — `bodyCl`/`convB` live at the
  `binderDisp`-shifted display and in the extended context; no `Issues` row
  produces a `.cl` at a shifted `ρ`, and `TableClosed tbl` has no unconditional
  inhabitant.
* `ClAppPorts.shape`/`ClLamPorts.shape` — the `eps = .star` dichotomies are not
  decidable in general (the mixed case is genuinely open).
* `ClLetEPorts.letSubCl`, `EutConv*Ports.regCl`, `EutAppPorts`/`EutLetEPorts`/
  `EutConstPorts.typeSortConv` — the `letSub`/`reg.2`/`instantiate*` typings are
  not `subAt` payload positions, so no `occ_*` row can name the pair.
* `EutPiPorts.imaxCoh` — an `eqN` of sort images; no query kind returns `eqN`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Head-constructor tag of a `TyP` node: which of the 15 `TyP` constructors
heads the derivation.  Used to state the residual cells' reach decidably. -/
inductive StepHeadTag : Type where
  | sort | bvar | const | pi | lam | app | letE | lit | conv
  | wk | esub | lsub | linst | ewk | cctx
  deriving DecidableEq

/-- The six transport constructors of `TyP`. -/
def StepHeadTag.isTransport : StepHeadTag → Bool
  | .wk | .esub | .lsub | .linst | .ewk | .cctx => true
  | _ => false

/-- The head-constructor tag of a `TyP` derivation. -/
def TyP.headTag {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} :
    TyP E n Γ e T → StepHeadTag
  | .sort .. => .sort | .bvar .. => .bvar | .const .. => .const
  | .pi .. => .pi | .lam .. => .lam | .app .. => .app | .letE .. => .letE
  | .lit .. => .lit | .conv .. => .conv | .wk .. => .wk | .esub .. => .esub
  | .lsub .. => .lsub | .linst .. => .linst | .ewk .. => .ewk
  | .cctx .. => .cctx

/-- Cells of the `cl` dispatch not closed by the landed/issued case-steps:
a transport-headed operand with no `.conv` on either side.  `.conv` peels cover
every `(.conv, t₂)`/`(t₁, .conv)` cell outright, and off-diagonal rule pairs are
refuted by `Expr.noConfusion` on the subject receipts — neither is residual. -/
def clResidualTag (t₁ t₂ : StepHeadTag) : Bool :=
  !decide (t₁ = .conv) && !decide (t₂ = .conv) &&
    (t₁.isTransport || t₂.isTransport)

/-- Cells of the `eut` dispatch not closed: same shape — non-`.conv` cells with
a transport-headed operand (all rule-head diagonals, `const`-`const` included,
are closed by dedicated case-steps). -/
def eutResidualTag (t₁ t₂ : StepHeadTag) : Bool :=
  !decide (t₁ = .conv) && !decide (t₂ = .conv) &&
    (t₁.isTransport || t₂.isTransport)

/-- **`cl_case`**, the exact `StepSuppliers` field statement, with the
`RcicSynStepCore4` port obligations lifted to named hypotheses:

* `piCl`/`lamCl`/`appCl`/`letCl` — the per-cell `*Ports` records (class (d):
  binder-display bodies, `★`-shape dichotomies, `letSub` pairs; none issuable).
* `constCl` — `ClConstPorts`, binding the actual sort-typings `hT₁ hT₂` at the
  shared member `m`; its `hbit` is only owed for `ls₁ ≠ ls₂` (the `ls₁ = ls₂`
  gate bit is class (a), issued via `occ_bitCoh` inside the closer).
* `clOther` — cells the landed closers don't cover: transport-headed operands
  on either side of a non-`.conv` pair, tagged decidably by `clResidualTag`.
  `.conv` peels cover every `.conv` cell (the right-side peel runs before the
  residual so `(transport, .conv)` never reaches `clOther`), and off-diagonal
  rule pairs are refuted by `Expr.noConfusion` on the subject receipts.

Every other cell is closed outright: `conv` peels on either side, `sort`/`lit`
are zero-request, `bvar`/`bitCoh` and the `pi`/`lam`/`app`/`letE` operand
requests are issued by `occ_*` rows inside the ported case-steps. -/
theorem es_cl_field (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (piCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
        {u₁ v₁ v₂ : Level}
        (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
        (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
        {σ : Level → Level} {ρ : List Disp},
        ClPiPorts tbl σ ρ u₁ hB₁ hB₂)
    (lamCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat}
        {u₁ : Level}
        (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
        (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
        {σ : Level → Level} {ρ : List Disp},
        ClLamPorts tbl σ ρ u₁ hb₁ hb₂)
    (appCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {f a A₁ B₁ A₂ B₂ : Expr Nat}
        (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
        (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
        {σ : Level → Level} {ρ : List Disp},
        ClAppPorts tbl σ ρ hf₁ ha₁ hf₂ ha₂)
    (letCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
        (hv₁ : TyP E n Γ v A)
        (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
        (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂) (hv₂ : TyP E n Γ v A)
        {σ : Level → Level} {ρ : List Disp},
        ClLetEPorts tbl σ ρ hv₁ hb₁ hb₂ hv₂)
    (constCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
        (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
        (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
        {σ : Level → Level} {ρ : List Disp},
        ClConstPorts tbl σ ρ hT₁ hT₂)
    (clOther : ∀ {E : ResolvedEnv} {n : Nat}
        {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
        {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
        (D₁ : TyP E n Γ₁ e₁ T₁) (D₂ : TyP E n Γ₂ e₂ T₂)
        (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
        (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp),
        clResidualTag D₁.headTag D₂.headTag = true →
        CaseStep Aw tbl (.cl (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)) :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
      {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁)
      (D₂ : TyP E n Γ e T₂) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
      (ρ : List Disp), CaseStep Aw tbl (.cl D₁ D₂ S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ
  -- The two sides of a `const`/`const` cell can carry different
  -- `CheckedMember`s `m₁ m₂`; their `hres` receipts force `m₁ = m₂`, which the
  -- single-`m` port (`ClConstPorts` binds `hT₁ hT₂` at the shared member)
  -- needs discharged first — same bridge as `constCell` in `es_eut_field`.
  have constCell : ∀ {r ls ls₁ ls₂ : _} {m₁ m₂ : CheckedMember}
      {u₁ u₂ : Level}
      (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
      (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
      (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
      (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
      (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
      (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
      (S' : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
      (∀ {u₁' u₂' : Level}
        (hT₁' : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁'))
        (hT₂' : TyP E n Γ (instantiateLevels ls₂ m₁.mtype) (.sort u₂')),
        ClConstPorts tbl σ ρ hT₁' hT₂') →
      CaseStep Aw tbl (.cl (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁
          hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S' σ ρ) := by
    intro r ls ls₁ ls₂ m₁ m₂ u₁ u₂ hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' ρ' portsFn
    have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
    subst hm
    exact cl_const_const_caseStep_of_port Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' ρ' (portsFn hT₁ hT₂)
  -- double convoy: `cases` needs *free* subject/context indices (transport
  -- constructors carry `lift`/`instantiate`/`insertAt`-computed indices), so
  -- both operands are re-abstracted with index receipts; each cell discharges
  -- them by `subst`/`cases` (noConfusion) and the residual `clOther` carries
  -- the genuinely stuck transport cells' receipts as data.
  have aux : ∀ {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
      (D₁' : TyP E n Γ₁ e₁ T₁) (D₂' : TyP E n Γ₂ e₂ T₂)
      (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
      {D₁'' : TyP E n Γ e T₁} {D₂'' : TyP E n Γ e T₂}
      (_ : D₁'' = hΓ₁ ▸ he₁ ▸ D₁') (_ : D₂'' = hΓ₂ ▸ he₂ ▸ D₂'),
      CaseStep Aw tbl (.cl D₁'' D₂'' S σ ρ) := by
    intro Γ₁ Γ₂ e₁ e₂ T₁ T₂ D₁' D₂' hΓ₁ he₁ hΓ₂ he₂
    revert hΓ₁ he₁ hΓ₂ he₂
    cases D₁' <;> cases D₂' <;> intro hΓ₁ he₁ hΓ₂ he₂ D₁'' D₂'' hcast₁ hcast₂ <;>
      subst he₂ <;> subst hΓ₂ <;> subst hcast₂ <;> subst hcast₁ <;> first
        | subst hΓ₁; cases he₁
          first
            | exact cl_conv_left_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_sort_sort_caseStep Aw tbl _ _ S σ ρ
            | exact cl_bvar_bvar_caseStep Aw tbl _ _ _ _ S σ ρ
            | exact cl_lit_lit_caseStep Aw tbl _ _ S σ ρ
            | refine cl_pi_pi_caseStep_of_ports Aw tbl _ _ _ _ S σ ρ ?_
              exact piCl _ _
            | refine cl_lam_lam_caseStep_of_ports Aw tbl _ _ _ _ _ _ S σ ρ ?_
              exact lamCl _ _
            | refine cl_app_app_caseStep_of_ports Aw tbl _ _ _ _ _ _ S σ ρ ?_
              exact appCl _ _ _ _
            | refine cl_letE_letE_caseStep_of_ports Aw tbl _ _ _ _ _ _ _ _ S σ ρ ?_
              exact letCl _ _ _ _
            | refine constCell _ _ _ _ _ _ _ _ _ _ S σ ρ ?_
              exact fun hT₁' hT₂' => constCl hT₁' hT₂'
            | refine clOther _ _ rfl rfl rfl rfl S σ ρ ?_; rfl
        | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
        | subst hΓ₁
          refine clOther _ _ rfl he₁ rfl rfl S σ ρ ?_; rfl
        | cases hΓ₁; cases he₁
          first
            | exact cl_conv_left_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
            | refine clOther _ _ rfl rfl rfl rfl S σ ρ ?_; rfl
        | cases hΓ₁
          refine clOther _ _ rfl he₁ rfl rfl S σ ρ ?_; rfl
        | subst he₁
          first
            | exact cl_conv_left_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
            | refine clOther _ _ hΓ₁ rfl rfl rfl S σ ρ ?_; rfl
        | exact Expr.noConfusion he₁
        | refine clOther _ _ hΓ₁ he₁ rfl rfl S σ ρ ?_; rfl
  exact aux D₁ D₂ rfl rfl rfl rfl rfl rfl

/-- **`eut_case`**, the exact `StepSuppliers` field statement, with the
`RcicSynStepCore4` port obligations lifted to named hypotheses:

* `convL`/`convR` — the `SortCoh`-shaped left/right conv-peel links;
* `piP`/`lamP` — `EutPiPorts`/`EutLamPorts`;
* `appP` — `EutAppPorts`, existential over the Π-surface typings `hA₁ hB₁ hA₂
  hB₂` (port data, since a `casted` operand can't expose them);
* `letP` — `EutLetEPorts`;
* `constP` — `EutConstPorts Aw` for the `const`/`const` cell;
* `eutOther` — residual cells: transport-headed operands in non-`.conv` pairs
  (`.conv` peels run before the residual — including the right peel on
  `(transport, .conv)` cells — and off-diagonal rule pairs are refuted by
  `Expr.noConfusion` on the subject receipts). -/
theorem es_eut_field (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (convL : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat}
        {u : Level} (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
        {σ : Level → Level} {ρ : List Disp}, EutConvLPorts tbl σ ρ h hc)
    (convR : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat}
        {u : Level} (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
        {σ : Level → Level} {ρ : List Disp}, EutConvRPorts tbl σ ρ h hc)
    (piP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
        {u₁ u₂ v₁ v₂ : Level}
        (hA₁ : TyP E n Γ A (.sort u₁))
        (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
        (hA₂ : TyP E n Γ A (.sort u₂))
        (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
        {σ : Level → Level} {ρ : List Disp},
        EutPiPorts tbl σ ρ hA₁ hB₁ hA₂ hB₂)
    (lamP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
        {u₁ : Level} {v₁ v₂ : Level}
        (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
        (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
        {σ : Level → Level} {ρ : List Disp},
        EutLamPorts tbl σ ρ u₁ hB₁ hB₂)
    (appP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
        (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
        (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
        (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
        (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
        {σ : Level → Level} {ρ : List Disp},
        ∃ (u₁' v₁' u₂' v₂' : Level) (hA₁ : TyP E n Γ A₁ (.sort u₁'))
          (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁'))
          (hA₂ : TyP E n Γ A₂ (.sort u₂'))
          (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂')),
          EutAppPorts tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ hA₁ hB₁ hA₂ hB₂)
    (letP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
        {u₁ w₁ u₂ w₂ : Level}
        (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
        (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
        (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
        (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
        (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
        (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
        {σ : Level → Level} {ρ : List Disp},
        EutLetEPorts tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂)
    (constP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
        {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
        (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
        (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
        {σ : Level → Level} {ρ : List Disp},
        EutConstPorts Aw tbl σ ρ r hT₁ hT₂)
    (eutOther : ∀ {E : ResolvedEnv} {n : Nat}
        {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
        {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
        (D₁ : TyP E n Γ₁ e₁ T₁) (D₂ : TyP E n Γ₂ e₂ T₂)
        (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
        (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp),
        eutResidualTag D₁.headTag D₂.headTag = true →
        CaseStep Aw tbl (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)) :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
      {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁)
      (D₂ : TyP E n Γ e T₂) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
      (ρ : List Disp), CaseStep Aw tbl (.eut D₁ D₂ S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ
  -- The two sides of a `const`/`const` cell can carry different
  -- `CheckedMember`s `m₁ m₂`; their `hres` receipts force `m₁ = m₂`, which the
  -- single-`m` closer needs discharged first.
  have constCell : ∀ {r ls ls₁ ls₂ : _} {m₁ m₂ : CheckedMember}
      {u₁ u₂ : Level}
      (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
      (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
      (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
      (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
      (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
      (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
      (S' : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
      (∀ {u₁' u₂' : Level}
        (hT₁' : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁'))
        (hT₂' : TyP E n Γ (instantiateLevels ls₂ m₁.mtype) (.sort u₂')),
        EutConstPorts Aw tbl σ ρ r hT₁' hT₂') →
      CaseStep Aw tbl (.eut (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁
          hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S' σ ρ) := by
    intro r ls ls₁ ls₂ m₁ m₂ u₁ u₂ hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' ρ' portsFn
    have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
    subst hm
    exact eut_const_const_caseStep_of_port Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' ρ' (portsFn hT₁ hT₂)
  have aux : ∀ {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
      (D₁' : TyP E n Γ₁ e₁ T₁) (D₂' : TyP E n Γ₂ e₂ T₂)
      (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
      {D₁'' : TyP E n Γ e T₁} {D₂'' : TyP E n Γ e T₂}
      (_ : D₁'' = hΓ₁ ▸ he₁ ▸ D₁') (_ : D₂'' = hΓ₂ ▸ he₂ ▸ D₂'),
      CaseStep Aw tbl (.eut D₁'' D₂'' S σ ρ) := by
    intro Γ₁ Γ₂ e₁ e₂ T₁ T₂ D₁' D₂' hΓ₁ he₁ hΓ₂ he₂
    revert hΓ₁ he₁ hΓ₂ he₂
    cases D₁' <;> cases D₂' <;> intro hΓ₁ he₁ hΓ₂ he₂ D₁'' D₂'' hcast₁ hcast₂ <;>
      subst he₂ <;> subst hΓ₂ <;> subst hcast₂ <;> subst hcast₁ <;> first
        | subst hΓ₁; cases he₁
          first
            | exact eut_conv_left_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convL _ _)
            | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convR _ _)
            | exact eut_sort_sort_caseStep Aw tbl _ _ S σ ρ
            | exact eut_bvar_bvar_caseStep Aw tbl _ _ _ _ S σ ρ
            | exact eut_lit_lit_caseStep Aw tbl _ _ S σ ρ
            | exact eut_pi_pi_caseStep_of_ports Aw tbl _ _ _ _ S σ ρ
                (piP _ _ _ _)
            | exact eut_lam_lam_caseStep_of_ports Aw tbl _ _ _ _ _ _ S σ ρ
                (lamP _ _)
            | obtain ⟨u₁', v₁', u₂', v₂', hA₁, hB₁, hA₂, hB₂, ports⟩ :=
                appP _ _ _ _ _ _
              exact eut_app_app_caseStep_of_ports Aw tbl _ _ _ _ _ _
                hA₁ hB₁ hA₂ hB₂ S σ ρ ports
            | exact eut_letE_letE_caseStep_of_ports Aw tbl _ _ _ _ _ _ _ _
                S σ ρ (letP _ _ _ _ _ _ _ _)
            | refine constCell _ _ _ _ _ _ _ _ _ _ S σ ρ ?_
              exact fun hT₁' hT₂' => constP hT₁' hT₂'
            | refine eutOther _ _ rfl rfl rfl rfl S σ ρ ?_; rfl
        | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
            (convR _ _)
        | subst hΓ₁
          refine eutOther _ _ rfl he₁ rfl rfl S σ ρ ?_; rfl
        | cases hΓ₁; cases he₁
          first
            | exact eut_conv_left_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convL _ _)
            | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convR _ _)
            | refine eutOther _ _ rfl rfl rfl rfl S σ ρ ?_; rfl
        | cases hΓ₁
          refine eutOther _ _ rfl he₁ rfl rfl S σ ρ ?_; rfl
        | subst he₁
          first
            | exact eut_conv_left_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convL _ _)
            | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convR _ _)
            | refine eutOther _ _ hΓ₁ rfl rfl rfl S σ ρ ?_; rfl
        | exact Expr.noConfusion he₁
        | refine eutOther _ _ hΓ₁ he₁ rfl rfl S σ ρ ?_; rfl
  exact aux D₁ D₂ rfl rfl rfl rfl rfl rfl
