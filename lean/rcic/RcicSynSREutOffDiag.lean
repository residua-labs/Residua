import rcic.RcicSynSRClEutOther
import rcic.RcicSynDispForPathPins
import rcic.RcicSynSpineComb
import rcic.RcicTypedGroupPins
import rcic.RcicFixtures

/-!
# RcicSynSREutOffDiag — row 15 `eutOther` off-diagonal scaffolding (cc 12:50Z task)

The named wall `eutOtherP_tableOfI` (`RcicSynSRClEutOther`) quantifies over
every non-`.conv` cell of the `eut` dispatch with a transport-headed operand
(`eutResidualTag`).  Its diagonal is closed outright
(`eut_diag_caseStep`/`eut_residual_cell_sat`); the residual cells are the
**off-diagonal** ordered pairs `(t₁, t₂)` with `eutResidualTag t₁ t₂ = true`
and `t₁ ≠ t₂` (`8·6 + 6·8 + 6·5 = 126` cells over `eutRuleTags` and
`eutTransportTags`).

This module lands the reusable scaffolding for those cells:

* `eutOffDiagSat` — the proposition that a given ordered head pair admits an
  inhabited on-cone instance: a `Demand.rootEut` query (so `LevelHom`,
  `RoutedDisp` and `AssumpPref` hold on the nose) whose `Goal` is inhabited
  and whose operands carry the two tags.
* `eutOffDiagSat_of` — the packer: any two same-typing derivations with
  inhabited `AssumpPref`s and a reflexive `Goal` yield an `eutOffDiagSat` at
  their head tags.
* A private fixture bank (`§2`–`§4`): context-free and `natEnvU` derivations
  headed at each rule tag, transport twins of each landing at a common
  `Γ* = [.assumption s1]`, and the `AssumpPref`/`ScopedCtx` terms pairing
  them — the raw material for concrete `eutOffDiagSat_of` calls.

No off-diagonal cell is proved or refuted here, and no enumeration table is
kept: the pair-indexed scene table moved out of the compiled artifact.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 the off-diagonal head pairs, enumerated -/

/-- The six transport heads of `TyP`. -/
def eutTransportTags : List StepHeadTag := [.wk, .esub, .lsub, .linst, .ewk, .cctx]

/-- The eight non-`.conv` rule heads of `TyP`. -/
def eutRuleTags : List StepHeadTag := [.sort, .bvar, .const, .pi, .lam, .app, .letE, .lit]

/-! ## §1 the on-cone instance package -/

/-- An inhabited on-cone instance of `eutOtherP_tableOfI`'s cell at the ordered
    head pair `(t₁, t₂)`: a `Demand`-rooted `.eut` query — `LevelHom σ`,
    `RoutedDisp`, `AssumpPref` and reachability all inhabited on the nose —
    whose `Goal` is inhabited and whose operands carry the two tags. -/
def eutOffDiagSat (t₁ t₂ : StepHeadTag) : Prop :=
  ∃ (Eₐ E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat)
    (D₁ : TyP E n Γ e T) (D₂ : TyP E n Γ e T)
    (_h₁ : D₁.AssumpPref) (_h₂ : D₂.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ),
    D₁.headTag = t₁ ∧ D₂.headTag = t₂ ∧
    (∀ tbl, Goal tbl (.eut D₁ D₂ S id (S.can id))) ∧
    Demand (.eut D₁ D₂ S id (S.can id))

/-- The instance constructor: two same-typing operands of the required heads.
    The `Goal` argument is usually `ConvMod.refl` (identical regularity
    erasures); the `Demand` is the `rootEut` root at the canonical display. -/
theorem eutOffDiagSat_of {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D₁ D₂ : TyP E n Γ e T)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ)
    (hg : ∀ tbl, Goal tbl (.eut D₁ D₂ S id (S.can id))) :
    eutOffDiagSat D₁.headTag D₂.headTag :=
  ⟨_, _, _, _, _, _, D₁, D₂, h₁, h₂, S, rfl, rfl, hg,
    .rootEut D₁ D₂ h₁ h₂ S id levelHom_id⟩

/-! ## §2 fixtures at `emptyEnv`

The shared subjects/types: `s0 : s1` where `s0 = .sort 0`, `s1 = .sort 1`,
`s2 = .sort 2`.  All transports are built to land at
`Γ* = [.assumption s1]` so any two can be paired. -/

/-- `s0 : s1`, context-free (a `.sort` node needs nothing from `Γ`). -/
private def tyS0 (Γ : LCtx) : TyP emptyEnv 0 Γ DispForPathPins.s0 DispForPathPins.s1 :=
  .sort emptyEnv 0 Γ .zero DispForPathPins.one (eqN_refl _)

/-- `s1 : s2`, context-free. -/
private def tyS1 (Γ : LCtx) : TyP emptyEnv 0 Γ DispForPathPins.s1 (.sort DispForPathPins.two) :=
  .sort emptyEnv 0 Γ DispForPathPins.one DispForPathPins.two (eqN_refl _)

/-- `s2 : s3`, context-free. -/
private def tyS2 (Γ : LCtx) :
    TyP emptyEnv 0 Γ (.sort DispForPathPins.two) (.sort (.succ DispForPathPins.two)) :=
  .sort emptyEnv 0 Γ DispForPathPins.two (.succ DispForPathPins.two) (eqN_refl _)

/-- `.bvar 0 : s1` at any context headed by `.assumption s1`. -/
private def tyB0 (Γ : LCtx) :
    TyP emptyEnv 0 (.assumption DispForPathPins.s1 :: Γ) (.bvar 0) DispForPathPins.s1 :=
  .bvar emptyEnv 0 _ 0 DispForPathPins.s1 DispForPathPins.two rfl (tyS1 _)

/-- `.bvar 1 : s1` at any context `[d, .assumption s1, …]`. -/
private def tyB1 (Γ : LCtx) (d : LocalDecl) :
    TyP emptyEnv 0 (d :: .assumption DispForPathPins.s1 :: Γ) (.bvar 1) DispForPathPins.s1 :=
  .bvar emptyEnv 0 _ 1 DispForPathPins.s1 DispForPathPins.two rfl (tyS1 _)

/-- `.pi s0 s0 : .sort (imax 1 1)`, context-free. -/
private def fixPi (Γ : LCtx) :
    TyP emptyEnv 0 Γ (.pi DispForPathPins.s0 DispForPathPins.s0)
      (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .pi emptyEnv 0 Γ DispForPathPins.s0 DispForPathPins.one DispForPathPins.s0
    DispForPathPins.one (tyS0 Γ) (tyS0 (.assumption DispForPathPins.s0 :: Γ))

/-- `.lam s1 (.bvar 0) : .pi s1 s1`, context-free. -/
private def fixLam (Γ : LCtx) :
    TyP emptyEnv 0 Γ (.lam DispForPathPins.s1 (.bvar 0))
      (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .lam emptyEnv 0 Γ DispForPathPins.s1 DispForPathPins.two (.bvar 0)
    DispForPathPins.s1 DispForPathPins.two (tyS1 Γ) (tyB0 Γ) (tyS1 _)

/-- `.app (.lam s1 (.bvar 0)) s0 : s1`, context-free. -/
private def fixApp (Γ : LCtx) :
    TyP emptyEnv 0 Γ (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0)
      DispForPathPins.s1 :=
  .app emptyEnv 0 Γ (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0
    DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.two (fixLam Γ)
    (tyS0 Γ) (tyS1 Γ)

/-- `.letE s1 s0 (.bvar 0) : s1`, context-free. -/
private def fixLet (Γ : LCtx) :
    TyP emptyEnv 0 Γ (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0))
      DispForPathPins.s1 :=
  .letE emptyEnv 0 Γ DispForPathPins.s1 DispForPathPins.two DispForPathPins.s0
    DispForPathPins.s1 (.bvar 0) DispForPathPins.two (tyS1 Γ) (tyS0 Γ)
    (.bvar emptyEnv 0 _ 0 DispForPathPins.s1 DispForPathPins.two rfl (tyS1 _))
    (tyS1 Γ)

/-- `wk` of `s0 : s1` at `[]`, landing at `[.assumption s1]` —
    `DispForPathPins.wkTy` is exactly this shape. -/
private def tWk : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 := DispForPathPins.wkTy

/-- `esub` of `s0 : s1` at `[.assumption s2, .assumption s1]` (`j = 0`,
    `v = s1`), landing at `[.assumption s1]`. -/
private def tEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .esub emptyEnv 0 [.assumption (.sort DispForPathPins.two), .assumption DispForPathPins.s1]
    DispForPathPins.s0 DispForPathPins.s1 (.sort DispForPathPins.two)
    DispForPathPins.s1 0 (.succ DispForPathPins.two) (tyS0 _) rfl
    (tyS1 _) (tyS2 _)

/-- `lsub` of `s0 : s1` at `[.letBinding s2 s1, .assumption s1]` (`j = 0`,
    `v = s1`), landing at `[.assumption s1]`. -/
private def tLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .lsub emptyEnv 0 [.letBinding (.sort DispForPathPins.two) DispForPathPins.s1,
      .assumption DispForPathPins.s1]
    DispForPathPins.s0 DispForPathPins.s1 (.sort DispForPathPins.two)
    DispForPathPins.s1 0 (.succ DispForPathPins.two) (tyS0 _) rfl
    (tyS1 _) (tyS2 _)

/-- `linst` of `s0 : s1` at the empty level list, landing at `[.assumption s1]`. -/
private def tLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 [] rfl rfl DispForPathPins.hs0s

/-- `ewk` of `s0 : s1` at the reflexive extension, landing at `[.assumption s1]`. -/
private def tEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 (envExt_refl _) DispForPathPins.hs0s

/-- `cctx` of `s0 : s1` along the reflexive binder conversion `s1 ≡ s1`,
    landing at `[.assumption s1]`. -/
private def tCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .cctx emptyEnv 0 [] DispForPathPins.s0 DispForPathPins.s1 DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.two DispForPathPins.hs0s
    (.refl emptyEnv 0 [] DispForPathPins.s1 (.sort DispForPathPins.two)
      (tyS1 []) (tyS1 []) (tyS1 []))

/-- the `CtxWfT` of `Γ* = [.assumption s1]` at `emptyEnv`. -/
private def ctxS1 : CtxWfT emptyEnv 0 [.assumption DispForPathPins.s1] :=
  .assumption [] DispForPathPins.s1 DispForPathPins.two .nil (.sort [] DispForPathPins.one)

/-- the `ScopedCtx` frame at `emptyEnv`, `Γ*`. -/
private def S1 : ScopedCtx emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1] :=
  ⟨EnvWfT.empty, envExt_refl _, ctxS1⟩

/-- `AssumptionPrefix` at cutoff `0` is trivially inhabited. -/
private def ap0 (Γ : LCtx) : AssumptionPrefix Γ 0 := assumptionPrefix_zero _

/-- `AssumpPref` of the six `s0 : s1` transports. -/
private def apWk : tWk.AssumpPref := ⟨ap0 _, ⟨⟩⟩
private def apEsub : tEsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLsub : tLsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLinst : tLinst.AssumpPref := ⟨⟩
private def apEwk : tEwk.AssumpPref := ⟨⟩
private def apCctx : tCctx.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-! ## §3 the rule-headed fixtures and their transport twins

Every scene lands at `Γ* = [.assumption s1]`.  For each rule head `r` the
fixture family is a `TyP E 0 Γ* e_r T_r` headed `r` plus the six transport
wrappers of (a context-free copy of) the same typing, landing back at
`Γ*`, `e_r`, `T_r`.  `const`/`lit` live at `natEnvU` (the Nat member group);
`bvar` needs the head binder, and its `wk` twin lands `.bvar 1` at
`[s1, s1]` since a head insertion re-indexes the bound variable. -/

/-- the `s0 : s1` sort fixture at `Γ*`. -/
private def srtD : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 := tyS0 _

/-- transport twins of `srtD`, landing at `Γ*`, `s0 : s1`. -/
private def srtWk : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .wk emptyEnv 0 [] DispForPathPins.s0 DispForPathPins.s1
    (.assumption DispForPathPins.s1) 0 (tyS0 [])
private def srtEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .esub emptyEnv 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    DispForPathPins.s0 DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (tyS0 _) rfl (tyS0 _) (tyS1 _)
private def srtLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .lsub emptyEnv 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    DispForPathPins.s0 DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (tyS0 _) rfl (tyS0 _) (tyS1 _)
private def srtLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 [] rfl rfl (tyS0 _)
private def srtEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 (envExt_refl _) (tyS0 _)
private def srtCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1] DispForPathPins.s0
    DispForPathPins.s1 :=
  .cctx emptyEnv 0 [] DispForPathPins.s0 DispForPathPins.s1 DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.two (tyS0 [.assumption DispForPathPins.s1])
    (.refl emptyEnv 0 [] DispForPathPins.s1 (.sort DispForPathPins.two)
      (tyS1 []) (tyS1 []) (tyS1 []))

/-- the reflexive binder conversion `s1 ≡ s1 : Sort 2` used by every `cctx` twin. -/
private def cvS1 (E : ResolvedEnv) (Γ : LCtx) (h : TyP E 0 Γ DispForPathPins.s1
    (.sort DispForPathPins.two)) :
    CvP E 0 Γ DispForPathPins.s1 DispForPathPins.s1 (.sort DispForPathPins.two) :=
  .refl E 0 Γ DispForPathPins.s1 (.sort DispForPathPins.two) h h h

/-- `.pi s0 s0 : .sort (imax 1 1)` at `Γ*` — the `pi` rule head. -/
private def piD : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  fixPi _

/-- transport twins of `piD`. -/
private def odPiWk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .wk emptyEnv 0 [] (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one))
    (.assumption DispForPathPins.s1) 0 (fixPi [])
private def odPiEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .esub emptyEnv 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one))
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixPi _)
    rfl (tyS0 _) (tyS1 _)
private def odPiLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .lsub emptyEnv 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one))
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixPi _)
    rfl (tyS0 _) (tyS1 _)
private def odPiLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) [] rfl rfl (fixPi _)
private def odPiEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) (envExt_refl _) (fixPi _)
private def odPiCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one)) :=
  .cctx emptyEnv 0 [] (.pi DispForPathPins.s0 DispForPathPins.s0)
    (.sort (.imax DispForPathPins.one DispForPathPins.one))
    DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.two
    (fixPi [.assumption DispForPathPins.s1]) (cvS1 _ _ (tyS1 _))

/-- `.lam s1 (.bvar 0) : .pi s1 s1` at `Γ*` — the `lam` rule head. -/
private def lamD : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  fixLam _

/-- transport twins of `lamD`. -/
private def lamWk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .wk emptyEnv 0 [] (.lam DispForPathPins.s1 (.bvar 0))
    (.pi DispForPathPins.s1 DispForPathPins.s1)
    (.assumption DispForPathPins.s1) 0 (fixLam [])
private def lamEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .esub emptyEnv 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1)
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixLam _)
    rfl (tyS0 _) (tyS1 _)
private def lamLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .lsub emptyEnv 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1)
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixLam _)
    rfl (tyS0 _) (tyS1 _)
private def lamLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1)
    [] rfl rfl (fixLam _)
private def lamEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1)
    (envExt_refl _) (fixLam _)
private def lamCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.lam DispForPathPins.s1 (.bvar 0)) (.pi DispForPathPins.s1 DispForPathPins.s1) :=
  .cctx emptyEnv 0 [] (.lam DispForPathPins.s1 (.bvar 0))
    (.pi DispForPathPins.s1 DispForPathPins.s1)
    DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.two
    (fixLam [.assumption DispForPathPins.s1]) (cvS1 _ _ (tyS1 _))

/-- `.app (.lam s1 (.bvar 0)) s0 : s1` at `Γ*` — the `app` rule head. -/
private def appD : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  fixApp _

/-- transport twins of `appD`. -/
private def appWk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  .wk emptyEnv 0 [] (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0)
    DispForPathPins.s1 (.assumption DispForPathPins.s1) 0 (fixApp [])
private def appEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  .esub emptyEnv 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixApp _)
    rfl (tyS0 _) (tyS1 _)
private def appLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  .lsub emptyEnv 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixApp _)
    rfl (tyS0 _) (tyS1 _)
private def appLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1
    [] rfl rfl (fixApp _)
private def appEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1
    (envExt_refl _) (fixApp _)
private def appCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0) DispForPathPins.s1 :=
  .cctx emptyEnv 0 [] (.app (.lam DispForPathPins.s1 (.bvar 0)) DispForPathPins.s0)
    DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.two
    (fixApp [.assumption DispForPathPins.s1]) (cvS1 _ _ (tyS1 _))

/-- `.letE s1 s0 (.bvar 0) : s1` at `Γ*` — the `letE` rule head. -/
private def letD : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  fixLet _

/-- transport twins of `letD`. -/
private def letWk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  .wk emptyEnv 0 [] (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0))
    DispForPathPins.s1 (.assumption DispForPathPins.s1) 0 (fixLet [])
private def letEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  .esub emptyEnv 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixLet _)
    rfl (tyS0 _) (tyS1 _)
private def letLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  .lsub emptyEnv 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.s0 0 DispForPathPins.two (fixLet _)
    rfl (tyS0 _) (tyS1 _)
private def letLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1
    [] rfl rfl (fixLet _)
private def letEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1
    (envExt_refl _) (fixLet _)
private def letCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1]
    (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0)) DispForPathPins.s1 :=
  .cctx emptyEnv 0 [] (.letE DispForPathPins.s1 DispForPathPins.s0 (.bvar 0))
    DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.two
    (fixLet [.assumption DispForPathPins.s1]) (cvS1 _ _ (tyS1 _))

/-- `.bvar 0 : s1` at `Γ*` — the `bvar` rule head. -/
private def bvD : TyP emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0)
    DispForPathPins.s1 := tyB0 []

/-- `.bvar 1 : s1` at `[s1, s1]` — partner of the `bvar` `wk` twin (a head
    insertion re-indexes the bound variable). -/
private def bvD1 : TyP emptyEnv 0
    [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1] (.bvar 1)
    DispForPathPins.s1 := tyB1 [] (.assumption DispForPathPins.s1)

/-- transport twins of `bvD` (`esub`/`lsub` substitute the head entry's
    `.bvar 1` back down to `.bvar 0`; `wk` lands `.bvar 1` at `[s1, s1]`). -/
private def bvWk : TyP emptyEnv 0
    [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1] (.bvar 1)
    DispForPathPins.s1 :=
  .wk emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0) DispForPathPins.s1
    (.assumption DispForPathPins.s1) 0 (tyB0 [])
private def bvEsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0)
    DispForPathPins.s1 :=
  .esub emptyEnv 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.bvar 1) DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (tyB1 [] (.assumption DispForPathPins.s1))
    rfl (tyS0 _) (tyS1 _)
private def bvLsub : TyP emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0)
    DispForPathPins.s1 :=
  .lsub emptyEnv 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.bvar 1) DispForPathPins.s1 DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (tyB1 [] (.letBinding DispForPathPins.s1 DispForPathPins.s0))
    rfl (tyS0 _) (tyS1 _)
private def bvLinst : TyP emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0)
    DispForPathPins.s1 :=
  .linst emptyEnv 0 0 [.assumption DispForPathPins.s1] (.bvar 0) DispForPathPins.s1
    [] rfl rfl (tyB0 [])
private def bvEwk : TyP emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0)
    DispForPathPins.s1 :=
  .ewk emptyEnv emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0) DispForPathPins.s1
    (envExt_refl _) (tyB0 [])
private def bvCctx : TyP emptyEnv 0 [.assumption DispForPathPins.s1] (.bvar 0)
    DispForPathPins.s1 :=
  .cctx emptyEnv 0 [] (.bvar 0) DispForPathPins.s1 DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.two (tyB0 []) (cvS1 _ _ (tyS1 _))

/-- the `CtxWfT` of `[s1, s1]` at `emptyEnv` (the `bvar` `wk` twin's scene). -/
private def ctxS2 : CtxWfT emptyEnv 0
    [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1] :=
  .assumption [.assumption DispForPathPins.s1] DispForPathPins.s1 DispForPathPins.two
    ctxS1 (.sort [.assumption DispForPathPins.s1] DispForPathPins.one)

/-- the `ScopedCtx` frame at `emptyEnv`, `[s1, s1]`. -/
private def S2 : ScopedCtx emptyEnv emptyEnv 0
    [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1] :=
  ⟨EnvWfT.empty, envExt_refl _, ctxS2⟩

/-- `natEnvU` sort helpers (`s0 : s1`, `s1 : s2`, `s2 : s3` work at any env). -/
private def uS0 (Γ : LCtx) : TyP natEnvU 0 Γ DispForPathPins.s0 DispForPathPins.s1 :=
  .sort natEnvU 0 Γ .zero DispForPathPins.one (eqN_refl _)
private def uS1 (Γ : LCtx) : TyP natEnvU 0 Γ DispForPathPins.s1
    (.sort DispForPathPins.two) :=
  .sort natEnvU 0 Γ DispForPathPins.one DispForPathPins.two (eqN_refl _)
private def uS2 (Γ : LCtx) : TyP natEnvU 0 Γ (.sort DispForPathPins.two)
    (.sort (.succ DispForPathPins.two)) :=
  .sort natEnvU 0 Γ DispForPathPins.two (.succ DispForPathPins.two) (eqN_refl _)

/-- `N = .const 0 [] : s1` at `natEnvU` — member 0 (`natFamMember`, `N : Sort 1`). -/
private def cNat (Γ : LCtx) : TyP natEnvU 0 Γ (.const 0 []) DispForPathPins.s1 :=
  .const natEnvU 0 Γ 0 [] [] natFamMember DispForPathPins.two rfl rfl rfl
    (eqNList_refl _) (.sort natEnvU 0 Γ DispForPathPins.one DispForPathPins.two
      (eqN_refl _))

/-- `zero = .const 1 [] : N` at `natEnvU` — member 1 (`natZeroMember`, `zero : N`). -/
private def cZero (Γ : LCtx) : TyP natEnvU 0 Γ (.const 1 []) (.const 0 []) :=
  .const natEnvU 0 Γ 1 [] [] natZeroMember DispForPathPins.one rfl rfl rfl
    (eqNList_refl _) (cNat Γ)

/-- `.const 1 [] : N` at `Γ*` — the `const` rule head. -/
private def cstD : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) := cZero _

/-- transport twins of `cstD`. -/
private def cstWk : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) :=
  .wk natEnvU 0 [] (.const 1 []) (.const 0 []) (.assumption DispForPathPins.s1)
    0 (cZero [])
private def cstEsub : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) :=
  .esub natEnvU 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.const 1 []) (.const 0 []) DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (cZero _) rfl (uS0 _) (uS1 _)
private def cstLsub : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) :=
  .lsub natEnvU 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.const 1 []) (.const 0 []) DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (cZero _) rfl (uS0 _) (uS1 _)
private def cstLinst : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) :=
  .linst natEnvU 0 0 [.assumption DispForPathPins.s1] (.const 1 []) (.const 0 [])
    [] rfl rfl (cZero _)
private def cstEwk : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) :=
  .ewk natEnvU natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 []) (.const 0 [])
    (envExt_refl _) (cZero _)
private def cstCctx : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.const 1 [])
    (.const 0 []) :=
  .cctx natEnvU 0 [] (.const 1 []) (.const 0 []) DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.two (cZero [.assumption DispForPathPins.s1])
    (cvS1 _ _ (uS1 _))

/-- `.lit 0 : N` at `natEnvU` — the `lit` rule head (`natExpand 0 = .const 1 []`). -/
private def litD : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .lit natEnvU 0 _ 0 (.const 0 []) (cZero _)

/-- transport twins of `litD`. -/
private def litWk : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .wk natEnvU 0 [] (.lit 0) (.const 0 []) (.assumption DispForPathPins.s1)
    0 (.lit natEnvU 0 [] 0 (.const 0 []) (cZero []))
private def litEsub : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .esub natEnvU 0 [.assumption DispForPathPins.s1, .assumption DispForPathPins.s1]
    (.lit 0) (.const 0 []) DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (.lit natEnvU 0 _ 0 (.const 0 []) (cZero _))
    rfl (uS0 _) (uS1 _)
private def litLsub : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .lsub natEnvU 0 [.letBinding DispForPathPins.s1 DispForPathPins.s0,
      .assumption DispForPathPins.s1]
    (.lit 0) (.const 0 []) DispForPathPins.s1 DispForPathPins.s0
    0 DispForPathPins.two (.lit natEnvU 0 _ 0 (.const 0 []) (cZero _))
    rfl (uS0 _) (uS1 _)
private def litLinst : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .linst natEnvU 0 0 [.assumption DispForPathPins.s1] (.lit 0) (.const 0 [])
    [] rfl rfl (.lit natEnvU 0 _ 0 (.const 0 []) (cZero _))
private def litEwk : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .ewk natEnvU natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0) (.const 0 [])
    (envExt_refl _) (.lit natEnvU 0 _ 0 (.const 0 []) (cZero _))
private def litCctx : TyP natEnvU 0 [.assumption DispForPathPins.s1] (.lit 0)
    (.const 0 []) :=
  .cctx natEnvU 0 [] (.lit 0) (.const 0 []) DispForPathPins.s1
    DispForPathPins.s1 DispForPathPins.two
    (.lit natEnvU 0 [.assumption DispForPathPins.s1] 0 (.const 0 [])
      (cZero [.assumption DispForPathPins.s1])) (cvS1 _ _ (uS1 _))

/-- the `CtxWfT` of `Γ*` at `natEnvU`. -/
private def ctxS1U : CtxWfT natEnvU 0 [.assumption DispForPathPins.s1] :=
  .assumption [] DispForPathPins.s1 DispForPathPins.two .nil
    (.sort [] DispForPathPins.one)

/-- the `ScopedCtx` frame at `natEnvU`, `Γ*`. -/
private def S3 : ScopedCtx natEnvU natEnvU 0 [.assumption DispForPathPins.s1] :=
  ⟨natEnvUWfT, envExt_refl _, ctxS1U⟩

/-- `AssumpPref` terms for the rule fixtures and twins (all `True`-valued
    conjunctions over sort/bvar leaves plus the cutoff-0 `AssumptionPrefix`). -/
private def apSrt : srtD.AssumpPref := ⟨⟩
private def apSrtWk : srtWk.AssumpPref := ⟨ap0 _, ⟨⟩⟩
private def apSrtEsub : srtEsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apSrtLsub : srtLsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apSrtLinst : srtLinst.AssumpPref := ⟨⟩
private def apSrtEwk : srtEwk.AssumpPref := ⟨⟩
private def apSrtCctx : srtCctx.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apBv : bvD.AssumpPref := ⟨⟩
private def apBv1 : bvD1.AssumpPref := ⟨⟩
private def apBvWk : bvWk.AssumpPref := ⟨ap0 _, ⟨⟩⟩
private def apBvEsub : bvEsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apBvLsub : bvLsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apBvLinst : bvLinst.AssumpPref := ⟨⟩
private def apBvEwk : bvEwk.AssumpPref := ⟨⟩
private def apBvCctx : bvCctx.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apPi : piD.AssumpPref := ⟨⟨⟩, ⟨⟩⟩
private def apOdPiWk : odPiWk.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩⟩⟩
private def apOdPiEsub : odPiEsub.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apOdPiLsub : odPiLsub.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apOdPiLinst : odPiLinst.AssumpPref := ⟨⟨⟩, ⟨⟩⟩
private def apOdPiEwk : odPiEwk.AssumpPref := ⟨⟨⟩, ⟨⟩⟩
private def apOdPiCctx : odPiCctx.AssumpPref := ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLam : lamD.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLamWk : lamWk.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩, ⟨⟩⟩⟩
private def apLamEsub : lamEsub.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apLamLsub : lamLsub.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apLamLinst : lamLinst.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLamEwk : lamEwk.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLamCctx : lamCctx.AssumpPref := ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apApp : appD.AssumpPref := ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apAppWk : appWk.AssumpPref := ⟨ap0 _, ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩⟩
private def apAppEsub : appEsub.AssumpPref := ⟨ap0 _, ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apAppLsub : appLsub.AssumpPref := ⟨ap0 _, ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apAppLinst : appLinst.AssumpPref := ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apAppEwk : appEwk.AssumpPref := ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apAppCctx : appCctx.AssumpPref := ⟨⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLet : letD.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLetWk : letWk.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩⟩
private def apLetEsub : letEsub.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apLetLsub : letLsub.AssumpPref := ⟨ap0 _, ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
private def apLetLinst : letLinst.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLetEwk : letEwk.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLetCctx : letCctx.AssumpPref := ⟨⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apCst : cstD.AssumpPref := ⟨⟩
private def apCstWk : cstWk.AssumpPref := ⟨ap0 _, ⟨⟩⟩
private def apCstEsub : cstEsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apCstLsub : cstLsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apCstLinst : cstLinst.AssumpPref := ⟨⟩
private def apCstEwk : cstEwk.AssumpPref := ⟨⟩
private def apCstCctx : cstCctx.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLit : litD.AssumpPref := ⟨⟩
private def apLitWk : litWk.AssumpPref := ⟨ap0 _, ⟨⟩⟩
private def apLitEsub : litEsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLitLsub : litLsub.AssumpPref := ⟨ap0 _, ⟨⟩, ⟨⟩, ⟨⟩⟩
private def apLitLinst : litLinst.AssumpPref := ⟨⟩
private def apLitEwk : litEwk.AssumpPref := ⟨⟩
private def apLitCctx : litCctx.AssumpPref := ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-! ## §5 sanity witnesses

Two `eutOffDiagSat_of` calls at concrete fixture pairs — one in each
direction — keeping the pack checked end-to-end without the per-cell table. -/

/-- The `(wk, sort)` cell is inhabited on-cone: `srtWk` and `srtD` type
    `s0 : s1` at `Γ*`, so `Demand.rootEut` applies with a reflexive goal. -/
theorem eutOffDiagSat_wk_sort : eutOffDiagSat .wk .sort :=
  eutOffDiagSat_of srtWk srtD apSrtWk apSrt S1 (fun _ => ConvMod.refl _)

/-- The `(sort, wk)` cell is inhabited on-cone, symmetrically. -/
theorem eutOffDiagSat_sort_wk : eutOffDiagSat .sort .wk :=
  eutOffDiagSat_of srtD srtWk apSrt apSrtWk S1 (fun _ => ConvMod.refl _)

/-! ## §6 erased-head-shape lemmas (cc 16:55Z method)

The off-diagonal cells group by the ERASED head shapes of the two goal
sides `Dᵢ.reg.2.eps σ ρ` instead of 126 literal pairs:

* `{sort,pi}`-leaf derivations erase their ascribed type to a `.sort` —
  `reg_eps_of_isSortOrPiHead` (landed).
* `.lam`-leaf derivations erase theirs to a `.pi` — `eps_pi_of_piLeaf`
  below, applied to `reg.2` (`reg_piLeaf_of_isLamHead`).

A `Goal` whose sides are `.sort` vs `.pi` is uninhabited at a `TableWF`
table — the landed `not_convE_sort_pi_wf`/`not_convE_pi_sort_wf` via
`confluent_eStep_wf` + `rstar_eStep_pi_inv` + `eStep_sort_normal`.  The two
`eutOffDiagGoal_not_*` lemmas are the one head-clash call per shape group;
same-shape cells need real work. -/

/-- Leaf-`.lam` head predicate: transports recurse, all other heads false. -/
def TyP.isLamHead : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → Bool
  | _, _, _, _, _, .sort .. => false
  | _, _, _, _, _, .bvar .. => false
  | _, _, _, _, _, .const .. => false
  | _, _, _, _, _, .pi .. => false
  | _, _, _, _, _, .lam .. => true
  | _, _, _, _, _, .app .. => false
  | _, _, _, _, _, .letE .. => false
  | _, _, _, _, _, .lit .. => false
  | _, _, _, _, _, .conv .. => false
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.isLamHead
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _ => D.isLamHead
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _ => D.isLamHead
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.isLamHead
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.isLamHead
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.isLamHead

/-- A `.pi`-leaf derivation (`isSortOrPiHead` without `isSortHead`) erases
    to a `.pi`-headed term at every level map and display. -/
theorem eps_pi_of_piLeaf :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortOrPiHead = true → D.isSortHead = false →
    (σ : Level → Level) → (ρ : List Disp) → ∃ A B, D.eps σ ρ = .pi A B
  | _, _, _, _, _, .pi _ _ _ _ u _ _ _ _, _, _, σ, ρ => by
      simp only [TyP.eps]
      cases levelIsZero (σ u) <;> exact ⟨_, _, rfl⟩
  | _, _, _, _, _, .sort .., _, hsh, _, _ => Bool.noConfusion hsh
  | _, _, _, _, _, .bvar .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .const .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .lam .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .app .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .letE .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .lit .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .conv .., hsp, _, _, _ => Bool.noConfusion hsp
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, hsp, hsh, σ, ρ => by
      by_cases hk : ρ[c]? = some .keep
      · rw [eps_wk_keep hk]
        obtain ⟨a, b, hab⟩ := eps_pi_of_piLeaf D hsp hsh σ (removeAt ρ c)
        rw [hab]; exact ⟨_, _, rfl⟩
      · rw [eps_wk_not_keep_of_ne hk]
        exact eps_pi_of_piLeaf D hsp hsh σ (removeAt ρ c)
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _, hsp, hsh, σ, ρ => by
      simp only [TyP.eps]
      cases levelIsZero (σ u) with
      | true => exact eps_pi_of_piLeaf D hsp hsh σ (insertDisp .drop j ρ)
      | false =>
          obtain ⟨a, b, hab⟩ := eps_pi_of_piLeaf D hsp hsh σ (insertDisp .keep j ρ)
          rw [hab]; exact ⟨_, _, rfl⟩
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, hsp, hsh, σ, ρ => by
      rw [lsub_eps_eq D hget hv hvT]
      exact eps_pi_of_piLeaf D hsp hsh σ _
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, hsp, hsh, σ, ρ =>
      eps_pi_of_piLeaf D hsp hsh (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, hsp, hsh, σ, ρ =>
      eps_pi_of_piLeaf D hsp hsh σ ρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, hsp, hsh, σ, ρ =>
      eps_pi_of_piLeaf D hsp hsh σ ρ

/-- A `.lam`-leaf derivation's regularity is a `.pi`-leaf derivation: `D.reg.2`
    is a `.pi` node under the same transport wrappers. -/
theorem reg_piLeaf_of_isLamHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isLamHead = true →
    D.reg.2.isSortOrPiHead = true ∧ D.reg.2.isSortHead = false
  | _, _, _, _, _, .lam .., _ => ⟨rfl, rfl⟩
  | _, _, _, _, _, .sort .., h => Bool.noConfusion h
  | _, _, _, _, _, .bvar .., h => Bool.noConfusion h
  | _, _, _, _, _, .const .., h => Bool.noConfusion h
  | _, _, _, _, _, .pi .., h => Bool.noConfusion h
  | _, _, _, _, _, .app .., h => Bool.noConfusion h
  | _, _, _, _, _, .letE .., h => Bool.noConfusion h
  | _, _, _, _, _, .lit .., h => Bool.noConfusion h
  | _, _, _, _, _, .conv .., h => Bool.noConfusion h
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D, h => reg_piLeaf_of_isLamHead D h
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _, h =>
      reg_piLeaf_of_isLamHead D h
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _, h =>
      reg_piLeaf_of_isLamHead D h
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D, h => reg_piLeaf_of_isLamHead D h
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, h => reg_piLeaf_of_isLamHead D h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, h => reg_piLeaf_of_isLamHead D h

/-- The erased ascribed type of a `.lam`-leaf derivation is `.pi`-headed. -/
theorem reg_eps_pi_of_isLamHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {D : TyP E n Γ e T} (h : D.isLamHead = true)
    (σ : Level → Level) (ρ : List Disp) :
    ∃ A B, D.reg.2.eps σ ρ = .pi A B :=
  eps_pi_of_piLeaf D.reg.2 (reg_piLeaf_of_isLamHead D h).1
    (reg_piLeaf_of_isLamHead D h).2 σ ρ

/-- Head clash, `.sort`-erased vs `.pi`-erased type: the `.eut` goal of a
    `{sort,pi}`-leaf derivation against a `.lam`-leaf one is uninhabited at
    `tableOfI hW`. -/
theorem eutOffDiagGoal_not_sortPi_lam {Eₐ E₀' E' E : ResolvedEnv}
    (hW : EnvWfT E) {n₀' n : Nat} {Γ₀' Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {D₁ : TyP E' n Γ e T₁} {D₂ : TyP E' n Γ e T₂}
    (h₁ : D₁.isSortOrPiHead = true) (h₂ : D₂.isLamHead = true)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    ¬ Goal (tableOfI hW) (.eut D₁ D₂ S σ ρ) := by
  rw [goal_eut_residual_unfold]
  obtain ⟨w, -, hw⟩ := reg_eps_of_isSortOrPiHead D₁ h₁
  obtain ⟨A, B, hpi⟩ := reg_eps_pi_of_isLamHead h₂ σ ρ
  rw [hw σ ρ, hpi]
  exact not_convE_sort_pi_wf (tableWF_tableOfI_full hW) _ _ _

/-- Head clash, `.pi`-erased vs `.sort`-erased type: the symmetric arm. -/
theorem eutOffDiagGoal_not_lam_sortPi {Eₐ E₀' E' E : ResolvedEnv}
    (hW : EnvWfT E) {n₀' n : Nat} {Γ₀' Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {D₁ : TyP E' n Γ e T₁} {D₂ : TyP E' n Γ e T₂}
    (h₁ : D₁.isLamHead = true) (h₂ : D₂.isSortOrPiHead = true)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    ¬ Goal (tableOfI hW) (.eut D₁ D₂ S σ ρ) := by
  rw [goal_eut_residual_unfold]
  obtain ⟨w, -, hw⟩ := reg_eps_of_isSortOrPiHead D₂ h₂
  obtain ⟨A, B, hpi⟩ := reg_eps_pi_of_isLamHead h₁ σ ρ
  rw [hpi, hw σ ρ]
  exact not_convE_pi_sort_wf (tableWF_tableOfI_full hW) _ _ _

/-! ## §7 subject head shapes — the vacuous-clash provider

The `.eut` query types ONE subject `e` twice; a derivation's leaf fixes the
subject's head ctor through every transport (`lift`/`instantiate`/
`instantiateLevels`/env/context moves preserve each `Expr` head), and
`esub`/`lsub` on a `.bvar` leaf decide by index: `instantiate j` either
hits `.bvar j` and yields the replacement's head, or misses and stays
`.bvar`.  `TyP.subjInfo` tracks head ctor AND bvar index through the
chain, so `TyP.subjHead` is TOTAL — every derivation's subject head is
determined (`subjHead_isSome`).  A cell whose two sides force different
subject heads is inhabited vacuously — `Expr.noConfusion` on the shared
`e` — via `eutOffDiag_caseStep_of_subjHeadClash`. -/

/-- The `Expr` head constructor as a `StepHeadTag` (rule heads only —
    `Expr` has no transport constructors). -/
def exprHeadCtor : Expr Nat → StepHeadTag
  | .bvar _ => .bvar
  | .sort _ => .sort
  | .const _ _ => .const
  | .app _ _ => .app
  | .lam _ _ => .lam
  | .pi _ _ => .pi
  | .letE _ _ _ => .letE
  | .lit _ => .lit

/-- `lift` preserves the head ctor. -/
theorem exprHeadCtor_lift (c k : Nat) (e : Expr Nat) :
    exprHeadCtor (lift c k e) = exprHeadCtor e := by
  cases e <;> try rfl
  unfold lift; split <;> rfl

/-- `instantiateLevels` preserves the head ctor. -/
theorem exprHeadCtor_instantiateLevels (ls : List Level) (e : Expr Nat) :
    exprHeadCtor (instantiateLevels ls e) = exprHeadCtor e := by
  cases e <;> rfl

/-- `instantiate` preserves every non-`.bvar` head ctor (at a `.bvar` the
    replacement can be anything). -/
theorem exprHeadCtor_instantiate_of_ne_bvar (j : Nat) (r e : Expr Nat)
    (h : exprHeadCtor e ≠ .bvar) :
    exprHeadCtor (instantiate j r e) = exprHeadCtor e := by
  cases e <;> first | rfl | exact absurd rfl h

/-- The bound-variable index of a literal `.bvar` subject, `none` otherwise. -/
def exprBvarIdx : Expr Nat → Option Nat
  | .bvar i => some i
  | _ => none

/-- `exprHeadCtor` on a literal `.bvar`: the head is `.bvar` exactly when the
    index is known. -/
theorem exprHeadCtor_eq_bvar_iff {e : Expr Nat} :
    exprHeadCtor e = .bvar ↔ ∃ i, e = .bvar i := by
  cases e <;> simp [exprHeadCtor]

/-- `exprBvarIdx = some i` iff the expression is literally `.bvar i`. -/
theorem eq_bvar_of_exprBvarIdx {e : Expr Nat} {i : Nat}
    (h : exprBvarIdx e = some i) : e = .bvar i := by
  cases e <;> simp_all [exprBvarIdx]

/-- `lift` on the `.bvar` index: at/above the cutoff the index shifts. -/
theorem exprBvarIdx_lift (c k : Nat) (e : Expr Nat) :
    exprBvarIdx (lift c k e) =
      (exprBvarIdx e).map fun i => if c ≤ i then i + k else i := by
  cases e with
  | bvar i =>
      show exprBvarIdx (if c ≤ i then .bvar (i + k) else .bvar i) =
        some (if c ≤ i then i + k else i)
      by_cases h : c ≤ i
      · rw [if_pos h, if_pos h]
        rfl
      · rw [if_neg h, if_neg h]
        rfl
  | _ => rfl

/-- `instantiateLevels` keeps `.bvar` indices — levels don't touch term vars. -/
theorem exprBvarIdx_instantiateLevels (ls : List Level) (e : Expr Nat) :
    exprBvarIdx (instantiateLevels ls e) = exprBvarIdx e := by
  cases e <;> rfl

/-- `instantiate` on a non-`.bvar` keeps the head ctor, so `exprBvarIdx`
    stays `none`. -/
theorem exprBvarIdx_instantiate_of_ne_bvar (j : Nat) (r e : Expr Nat)
    (h : exprHeadCtor e ≠ .bvar) :
    exprBvarIdx (instantiate j r e) = none := by
  cases e <;> first | rfl | exact absurd rfl h

/-- The subject's head ctor AND, for literal `.bvar` subjects, the index —
    computed through the whole transport chain.  Every operation is
    head-tracking: `lift`/`instantiate`/`instantiateLevels` preserve each
    `Expr` head, `conv`/`ewk`/`cctx` leave the subject alone, `wk`
    re-indexes the `.bvar`, and `esub`/`lsub` decide by whether the inner
    subject is exactly `.bvar j` — a hit gives the replacement's head
    (`lift` preserves it), a miss gives `.bvar` back. -/
def TyP.subjInfo : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → StepHeadTag × Option Nat
  | _, _, _, _, _, .sort .. => (.sort, none)
  | _, _, _, _, _, .bvar _ _ _ i .. => (.bvar, some i)
  | _, _, _, _, _, .const .. => (.const, none)
  | _, _, _, _, _, .pi .. => (.pi, none)
  | _, _, _, _, _, .lam .. => (.lam, none)
  | _, _, _, _, _, .app .. => (.app, none)
  | _, _, _, _, _, .letE .. => (.letE, none)
  | _, _, _, _, _, .lit .. => (.lit, none)
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ D _ => D.subjInfo
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D =>
      match D.subjInfo with
      | (.bvar, some i) => (.bvar, some (if c ≤ i then i + 1 else i))
      | s => s
  | _, _, _, _, _, .esub _ _ _ _ _ _ v j _ D _ _ _ =>
      match D.subjInfo with
      | (.bvar, some i) =>
          if i = j then (exprHeadCtor v, exprBvarIdx v |>.map (· + j))
          else (.bvar, some (if j < i then i - 1 else i))
      | s => s
  | _, _, _, _, _, .lsub _ _ _ _ _ _ v j _ D _ _ _ =>
      match D.subjInfo with
      | (.bvar, some i) =>
          if i = j then (exprHeadCtor v, exprBvarIdx v |>.map (· + j))
          else (.bvar, some (if j < i then i - 1 else i))
      | s => s
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.subjInfo
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.subjInfo
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.subjInfo

/-- The subject's head ctor, where the transport chain forces it —
    projection of `subjInfo` (always determined). -/
def TyP.subjHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) : Option StepHeadTag :=
  some (D.subjInfo).1

/-- The literal `.bvar` index of the subject, where it is one —
    projection of `subjInfo`. -/
def TyP.subjBvarIdx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) : Option Nat :=
  (D.subjInfo).2

/-- `subjInfo` is right: it computes the actual subject head ctor and
    bvar index. -/
theorem subjInfo_eq :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) →
    D.subjInfo = (exprHeadCtor e, exprBvarIdx e)
  | _, _, _, _, _, .sort .. => rfl
  | _, _, _, _, _, .bvar .. => rfl
  | _, _, _, _, _, .const .. => rfl
  | _, _, _, _, _, .pi .. => rfl
  | _, _, _, _, _, .lam .. => rfl
  | _, _, _, _, _, .app .. => rfl
  | _, _, _, _, _, .letE .. => rfl
  | _, _, _, _, _, .lit .. => rfl
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ D _ => subjInfo_eq D
  | _, _, _, _, _, .wk _ _ _ e _ _ c D => by
      have ih := subjInfo_eq D
      simp only [TyP.subjInfo]
      cases hsi : D.subjInfo with
      | mk t bi =>
          rw [hsi] at ih
          have h1 := congrArg Prod.fst ih
          have h2 := congrArg Prod.snd ih
          cases t with
          | bvar =>
              cases bi with
              | some i =>
                  have he := eq_bvar_of_exprBvarIdx h2.symm
                  subst he
                  dsimp only
                  unfold lift
                  by_cases hle : c ≤ i
                  · simp only [if_pos hle]; rfl
                  · simp only [if_neg hle]; rfl
              | none =>
                  obtain ⟨i, hi⟩ := exprHeadCtor_eq_bvar_iff.mp h1.symm
                  rw [hi] at h2
                  exact Option.noConfusion h2
          | _ =>
              cases bi with
              | some i =>
                  obtain rfl := eq_bvar_of_exprBvarIdx h2.symm
                  exact StepHeadTag.noConfusion h1
              | none =>
                  have hbv : exprBvarIdx e = none := h2.symm
                  have hnb : exprHeadCtor e ≠ .bvar := fun hb => by
                    obtain ⟨i, hi⟩ := exprHeadCtor_eq_bvar_iff.mp hb
                    rw [hi] at hbv
                    exact Option.noConfusion hbv
                  dsimp only
                  rw [ih]
                  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
                  · exact (exprHeadCtor_lift _ _ _).symm
                  · rw [exprBvarIdx_lift, hbv]
                    rfl
  | _, _, _, _, _, .esub _ _ _ e _ _ _ j _ D _ _ _ => by
      have ih := subjInfo_eq D
      simp only [TyP.subjInfo]
      cases hsi : D.subjInfo with
      | mk t bi =>
          rw [hsi] at ih
          have h1 := congrArg Prod.fst ih
          have h2 := congrArg Prod.snd ih
          cases t with
          | bvar =>
              cases bi with
              | some i =>
                  have he := eq_bvar_of_exprBvarIdx h2.symm
                  subst he
                  dsimp only
                  unfold instantiate
                  by_cases h : i = j
                  · simp only [if_pos h]
                    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
                    · exact (exprHeadCtor_lift _ _ _).symm
                    · rw [exprBvarIdx_lift]; simp
                  · simp only [if_neg h]
                    by_cases h2i : j < i
                    · simp only [if_pos h2i]
                      refine Prod.ext_iff.mpr ⟨rfl, rfl⟩
                    · simp only [if_neg h2i]
                      refine Prod.ext_iff.mpr ⟨rfl, rfl⟩
              | none =>
                  obtain ⟨i, hi⟩ := exprHeadCtor_eq_bvar_iff.mp h1.symm
                  rw [hi] at h2
                  exact Option.noConfusion h2
          | _ =>
              cases bi with
              | some i =>
                  obtain rfl := eq_bvar_of_exprBvarIdx h2.symm
                  exact StepHeadTag.noConfusion h1
              | none =>
                  have hbv : exprBvarIdx e = none := h2.symm
                  have hnb : exprHeadCtor e ≠ .bvar := fun hb => by
                    obtain ⟨i, hi⟩ := exprHeadCtor_eq_bvar_iff.mp hb
                    rw [hi] at hbv
                    exact Option.noConfusion hbv
                  dsimp only
                  rw [ih]
                  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
                  · exact (exprHeadCtor_instantiate_of_ne_bvar _ _ _ hnb).symm
                  · rw [hbv]
                    exact (exprBvarIdx_instantiate_of_ne_bvar _ _ _ hnb).symm
  | _, _, _, _, _, .lsub _ _ _ e _ _ _ j _ D _ _ _ => by
      have ih := subjInfo_eq D
      simp only [TyP.subjInfo]
      cases hsi : D.subjInfo with
      | mk t bi =>
          rw [hsi] at ih
          have h1 := congrArg Prod.fst ih
          have h2 := congrArg Prod.snd ih
          cases t with
          | bvar =>
              cases bi with
              | some i =>
                  have he := eq_bvar_of_exprBvarIdx h2.symm
                  subst he
                  dsimp only
                  unfold instantiate
                  by_cases h : i = j
                  · simp only [if_pos h]
                    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
                    · exact (exprHeadCtor_lift _ _ _).symm
                    · rw [exprBvarIdx_lift]; simp
                  · simp only [if_neg h]
                    by_cases h2i : j < i
                    · simp only [if_pos h2i]
                      refine Prod.ext_iff.mpr ⟨rfl, rfl⟩
                    · simp only [if_neg h2i]
                      refine Prod.ext_iff.mpr ⟨rfl, rfl⟩
              | none =>
                  obtain ⟨i, hi⟩ := exprHeadCtor_eq_bvar_iff.mp h1.symm
                  rw [hi] at h2
                  exact Option.noConfusion h2
          | _ =>
              cases bi with
              | some i =>
                  obtain rfl := eq_bvar_of_exprBvarIdx h2.symm
                  exact StepHeadTag.noConfusion h1
              | none =>
                  have hbv : exprBvarIdx e = none := h2.symm
                  have hnb : exprHeadCtor e ≠ .bvar := fun hb => by
                    obtain ⟨i, hi⟩ := exprHeadCtor_eq_bvar_iff.mp hb
                    rw [hi] at hbv
                    exact Option.noConfusion hbv
                  dsimp only
                  rw [ih]
                  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
                  · exact (exprHeadCtor_instantiate_of_ne_bvar _ _ _ hnb).symm
                  · rw [hbv]
                    exact (exprBvarIdx_instantiate_of_ne_bvar _ _ _ hnb).symm
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => by
      have ih := subjInfo_eq D
      simp only [TyP.subjInfo]
      rw [ih]
      exact Prod.ext_iff.mpr ⟨(exprHeadCtor_instantiateLevels _ _).symm,
        (exprBvarIdx_instantiateLevels _ _).symm⟩
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => subjInfo_eq D
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => subjInfo_eq D

/-- `subjHead` is right: wherever it reports a shape, the subject's head
    ctor is that shape. -/
theorem exprHeadCtor_of_subjHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) {t : StepHeadTag}
    (h : D.subjHead = some t) : exprHeadCtor e = t := by
  have hi := subjInfo_eq D
  unfold TyP.subjHead at h
  rw [hi] at h
  exact Option.some.inj h

/-- `subjHead` is total: every derivation's subject head is determined. -/
theorem subjHead_isSome {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) : ∃ t, D.subjHead = some t :=
  ⟨_, rfl⟩

/-- The vacuous side of the head-shape grouping: two derivations of the same
    subject whose `subjHead`s differ cannot both exist — the `.eut` cell is
    inhabited trivially, by `absurd`. -/
theorem eutOffDiag_caseStep_of_subjHeadClash {Eₐ E₀' E' : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e T₁ T₂ : Expr Nat}
    {D₁ : TyP E' n Γ e T₁} {D₂ : TyP E' n Γ e T₂}
    {t₁ t₂ : StepHeadTag} (h₁ : D₁.subjHead = some t₁)
    (h₂ : D₂.subjHead = some t₂) (hne : t₁ ≠ t₂)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.eut D₁ D₂ S σ ρ) :=
  fun _ _ =>
    absurd ((exprHeadCtor_of_subjHead D₁ h₁).symm.trans
      (exprHeadCtor_of_subjHead D₂ h₂)) hne

/-- The bridge to the `eutOtherP_tableOfI` premise shape: the residual
    quantifies over derivations of possibly different subjects/contexts,
    then `▸`-casts them onto a shared `(Γ, e)` before forming `.eut`.
    After `cases` on the four equalities the casts collapse and the
    shared-subject clash applies.  This discharges — vacuously — every
    residual cell whose two sides force distinct subject head ctors, at
    any transport depth, in one lemma. -/
theorem eutOtherP_caseStep_of_subjHeadClash {Eₐ E : ResolvedEnv}
    (hW : EnvWfT E) (Aw : Nat → Nat)
    {E' : ResolvedEnv} {n : Nat} {Γ Γ₁ Γ₂ : LCtx}
    {e e₁ e₂ T₁ T₂ : Expr Nat} {E₀' : ResolvedEnv} {n₀' : Nat}
    {Γ₀' : LCtx}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp)
    {t₁ t₂ : StepHeadTag} (h₁ : D₁.subjHead = some t₁)
    (h₂ : D₂.subjHead = some t₂) (hne : t₁ ≠ t₂) :
    CaseStep Aw (tableOfI hW)
      (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ) := by
  cases hΓ₁; cases he₁; cases hΓ₂; cases he₂
  exact eutOffDiag_caseStep_of_subjHeadClash h₁ h₂ hne S σ ρ

/-- Decidable form of the cross-shape condition for dispatch: both
    `subjHead`s determined and distinct. -/
def subjHeadClash {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) :
    Bool :=
  match D₁.subjHead, D₂.subjHead with
  | some t₁, some t₂ => decide (t₁ ≠ t₂)
  | _, _ => false

theorem eutOffDiag_caseStep_of_subjHeadClash_true {Eₐ E₀' E' : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e T₁ T₂ : Expr Nat}
    {D₁ : TyP E' n Γ e T₁} {D₂ : TyP E' n Γ e T₂}
    (hc : subjHeadClash D₁ D₂ = true)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.eut D₁ D₂ S σ ρ) := by
  unfold subjHeadClash at hc
  cases hs₁ : D₁.subjHead with
  | none => rw [hs₁] at hc; exact Bool.noConfusion hc
  | some t₁ =>
      cases hs₂ : D₂.subjHead with
      | none => rw [hs₁, hs₂] at hc; exact Bool.noConfusion hc
      | some t₂ =>
          rw [hs₁, hs₂] at hc
          exact eutOffDiag_caseStep_of_subjHeadClash hs₁ hs₂
            (of_decide_eq_true hc) S σ ρ

/-! ## §9 the two-way dispatch — clash ∨ same-head

With `subjHead` total, every `.eut` cell decides one of two ways: the
`subjHeadClash` Bool is `true` (distinct forced subject heads — the cell is
vacuous) or `false` (same head — the substantive residue).  This section is
the packaging: `subjHeadClash` reduces to a `decide` on the `subjInfo`
projections, and the casted form of the residual premise collapses through
`cases` to the un-casted one. -/

/-- `subjHead` is always `some`, so the Bool is exactly the tag disequality. -/
theorem subjHeadClash_eq_decide {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) :
    subjHeadClash D₁ D₂ = decide ((D₁.subjInfo).1 ≠ (D₂.subjInfo).1) := by
  unfold subjHeadClash TyP.subjHead
  rfl

theorem subjHeadClash_true_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) :
    subjHeadClash D₁ D₂ = true ↔ (D₁.subjInfo).1 ≠ (D₂.subjInfo).1 := by
  rw [subjHeadClash_eq_decide]
  exact decide_eq_true_iff

/-- The `false` side: same forced subject head. -/
theorem subjHeadClash_false_same {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h : subjHeadClash D₁ D₂ = false) : (D₁.subjInfo).1 = (D₂.subjInfo).1 := by
  rw [subjHeadClash_eq_decide] at h
  by_cases heq : (D₁.subjInfo).1 = (D₂.subjInfo).1
  · exact heq
  · rw [decide_eq_true_iff.mpr heq] at h
    exact Bool.noConfusion h

/-- Same-head fact plus the head itself: both sides force the shared
    subject's head ctor. -/
theorem subjHeadClash_false_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h : subjHeadClash D₁ D₂ = false) :
    (D₁.subjInfo).1 = (D₂.subjInfo).1 ∧ exprHeadCtor e = (D₁.subjInfo).1 :=
  ⟨subjHeadClash_false_same D₁ D₂ h, exprHeadCtor_of_subjHead D₁ rfl⟩

/-- The `eutOtherP`-shaped dispatch: `subjHeadClash` on the casted
    derivations decides the cell — `cases` collapses the casts. -/
theorem eutOtherP_caseStep_of_subjHeadClash_true {Eₐ E : ResolvedEnv}
    (hW : EnvWfT E) (Aw : Nat → Nat)
    {E' : ResolvedEnv} {n : Nat} {Γ Γ₁ Γ₂ : LCtx}
    {e e₁ e₂ T₁ T₂ : Expr Nat} {E₀' : ResolvedEnv} {n₀' : Nat}
    {Γ₀' : LCtx}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp)
    (hc : subjHeadClash (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) = true) :
    CaseStep Aw (tableOfI hW)
      (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ) := by
  cases hΓ₁; cases he₁; cases hΓ₂; cases he₂
  exact eutOffDiag_caseStep_of_subjHeadClash_true hc S σ ρ

/-- The casted same-head fact for the `false` branch. -/
theorem eutOtherP_sameSubjHead_of_clash_false
    {n : Nat} {Γ Γ₁ Γ₂ : LCtx}
    {e e₁ e₂ T₁ T₂ : Expr Nat} {E' : ResolvedEnv}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (hc : subjHeadClash (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) = false) :
    (D₁.subjInfo).1 = (D₂.subjInfo).1 := by
  cases hΓ₁; cases he₁; cases hΓ₂; cases he₂
  exact subjHeadClash_false_same D₁ D₂ hc

end Rcic.Syn
