import rcic.RcicSynSREqnAppCell
import rcic.RcicSynSRClEutTransport
import rcic.RcicSynClosedCleut
import rcic.RcicSynPBitAll

/-!
# RcicSynSREqnCellIH — row 14 non-const cells: the uniq-as-IH measurement

cc 2026-10-21 12:55Z item, lane glm/sr4-eqn, over
`research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md` row 14 and the common
note `sortrow-uniq-as-ih.md` (cc 12:50Z): for each wall, name the exact
uniqueness instance; if both derivations are strict subderivations, issue
it through an additive `IssuesCT`-style row; otherwise give the inhabited
boundary.

## (1) `appCl` — NOT issuable: inhabited boundary

`ClAppPorts.shape` is propositionally `TagCoh σ ρ σ ρ hf₁ hf₂ ×
TagCoh σ ρ σ ρ ha₁ ha₂` (`clAppPorts_of_tagCoh`, AppCell §1). By `PBit`
each star-status is the bit of the derivation's own regularity universe
(`hfᵢ.eps σ ρ = .star ↔ levelIsZero (σ hfᵢ.reg.1) = true`), so the needed
uniqueness is the bit-equality at the TWO NAMED DERIVATIONS

    hf₁.reg.2 : TyP E n Γ (.pi A₁ B₁) (.sort hf₁.reg.1)
    hf₂.reg.2 : TyP E n Γ (.pi A₂ B₂) (.sort hf₂.reg.1)

(the natural sort-typings of `f`'s two ascribed π-types), and for the
argument side `haᵢ.reg.2 : TyP E n Γ Aᵢ (.sort haᵢ.reg.1)` at `A₁`/`A₂`.
`appCl_bitWall_fun`/`appCl_bitWall_arg` are exactly `BitCoh σ` at those
pairs, and `clAppPorts_of_bitWalls` shows the ports follow from them
modulo the per-side `PBit`s.

**The obstruction is kind-formability, not rank** (`appCl_hf_reg_lex_lt`
proves the rank would drop — `reg` is never heavier than the node,
`TyP.wt_reg_le`):

* every two-typing kind binds ONE subject (`.cl`/`.eut`/`.bitCoh`/`.pb`/
  `.mixed`); the two reg derivations type the DISTINCT subjects
  `.pi A₁ B₁` / `.pi A₂ B₂` — `Site.bitCoh hf₁.reg.2 hf₂.reg.2` does not
  typecheck in the heterogeneous cell;
* `.head` is the only kind answering `levelIsZero (σ uL) =
  levelIsZero (σ uR)` at distinct subjects, but its premise is
  `c : CvP E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort u)` — no conversion
  between `f`'s two ascribed types sits on the `app`/`app` pair;
* `hfᵢ.reg.2` is `TyP.reg`-computed — `occ_*` rows name only `subAt`
  occurrences (for `const`/`bvar`/`app`/`letE`/`conv`-headed `hfᵢ` it
  coincides with a real child, but the subject mismatch still blocks);
* `.eut hf₁ hf₂` answers `ConvMod` of the reg.2 ERASURES — the erasure
  layer, not the gate bits;
* `.obsPair` zips `gateLevels` bits — the right shape — but is the frozen
  Q269 control (`obsPair_not_demanded`: no live `Issues` row targets it).

Boundary, inhabited (landed in AppCell §3): `sr5_appCl_sat`.
Homogeneous fragment: at a shared ascribed type the bitCoh kind IS
formable (`appCl_hom_bitCoh`, `appCl_hom_bitCoh_goal`) — heterogeneity of
the ascribed π-types is precisely the residue.

## (2) `piCl` — `bodyCl` issuable; `letCl` — `shape` wall; `clOther` — mixed cells

* **piCl**: `ClPiPorts.bodyCl` is `CL` at `hBᵢ : TyP _ _ (.assumption A :: Γ)
  B (.sort vᵢ)` — ONE subject `B`, strict children at `[1]`, extended
  display `binderDisp (levelIsZero (σ u₁)) :: ρ`. Rank decrease
  (`cl_pi_body_lex_lt`) and routedness (`cl_pi_body_routed`) are proved
  here; the candidate additive row is
  `cl_pi_clB : .cl (pi₁) (pi₂) S σ ρ ↦ .cl hB₁ hB₂ S σ ρ⁺` — the
  `eut_lam_eut` shape at the `cl` dispatch (same `S`, so
  `originalPrefixLength` agrees definitionally). No landed `Issues`/
  `IssuesC`/`IssuesCT` row targets it, so inside the landed closer it
  stays the port. `hTC` is `tableClosed_tableOfI hW` at `tableOfI hW`.
* **letCl**: `ClLetEPorts.shape` is LITERAL eps-equality of the value
  pair — `(hv₁.eps = .star ∧ hv₂.eps = .star) ∨ ∃ ev ≠ .star, both = ev`.
  No kind answers `Eq` on eps (`.cl` answers `ConvMod`): NOT issuable —
  the named wall, inhabited on the diagonal (`clLetEPorts_shape_diag`,
  and `clLetEPorts_sat` landed). `bodyDrop`/`bodyInline` are `CL`-shaped
  at the routed let displays — `hbᵢ` types ONE subject `b` at child `[2]`;
  rank (`cl_letE_body_lex_lt`) and routed (`cl_letE_body_drop_routed`,
  `cl_letE_body_inline_routed`; `RoutedDisp.letDrop`'s `hv.eps = .star`
  premise is exactly `shape`'s first disjunct) proved here — issuable via
  additive `cl_letE_clB_drop`/`cl_letE_clB_inline` rows.
* **clOther** (`clResidualTag`-true): diagonal transport pairs are
  issuable through the LANDED `IssuesCT` payload rows (`cl_wk_cl`,
  `cl_ewk_cl`, `cl_esub_cl` + `cl_esub_clv`, `cl_lsub_cl`, `cl_linst_cl`,
  `cl_cctx_cl`); identical pairs are closed outright
  (`cl_diag_caseStep`). The residual is the MIXED cells — a
  transport-headed operand against a different transport or a non-conv
  rule head — inhabited on the diagonal by `cl_residual_cell_sat`.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `appCl`: the named sort derivations and the rank pin -/

/-- The `hf`-side uniqueness instance, named: the bit-equality of the
    regularity universes of `f`'s two ascribed π-types — what
    `BitCoh σ hf₁.reg.2 hf₂.reg.2` would state at ONE subject; the
    subjects `.pi A₁ B₁` / `.pi A₂ B₂` differ, so the kind is unformable
    and this raw equality is the residual. -/
def appCl_bitWall_fun {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A₁ B₁ A₂ B₂ : Expr Nat} (hf₁ : TyP E n Γ f (.pi A₁ B₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (σ : Level → Level) : Prop :=
  levelIsZero (σ hf₁.reg.1) = levelIsZero (σ hf₂.reg.1)

/-- The `ha`-side uniqueness instance: the sorts of `a`'s two ascribed
    types `A₁`/`A₂`. -/
def appCl_bitWall_arg {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A₁ A₂ : Expr Nat} (ha₁ : TyP E n Γ a A₁) (ha₂ : TyP E n Γ a A₂)
    (σ : Level → Level) : Prop :=
  levelIsZero (σ ha₁.reg.1) = levelIsZero (σ ha₂.reg.1)

/-- The port follows from the two named bitWalls once each side's
    `PBit`-at-`reg` is granted — i.e. the `TagCoh` wall IS the eqN/bit of
    the two `reg` sort typings, and the four `PBit`s are row-16 content
    (`PBitRegResid`). -/
theorem clAppPorts_of_bitWalls {tbl : List CRule} {σ : Level → Level} {ρ : List Disp}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {hf₁ : TyP E n Γ f (.pi A₁ B₁)} {ha₁ : TyP E n Γ a A₁}
    {hf₂ : TyP E n Γ f (.pi A₂ B₂)} {ha₂ : TyP E n Γ a A₂}
    (hpf₁ : PBit σ ρ hf₁ hf₁.reg.2) (hpf₂ : PBit σ ρ hf₂ hf₂.reg.2)
    (hpa₁ : PBit σ ρ ha₁ ha₁.reg.2) (hpa₂ : PBit σ ρ ha₂ ha₂.reg.2)
    (hbf : appCl_bitWall_fun hf₁ hf₂ σ) (hba : appCl_bitWall_arg ha₁ ha₂ σ) :
    ClAppPorts tbl σ ρ hf₁ ha₁ hf₂ ha₂ := by
  have hbf' : levelIsZero (σ hf₁.reg.1) = true ↔
      levelIsZero (σ hf₂.reg.1) = true := by rw [hbf]
  have hba' : levelIsZero (σ ha₁.reg.1) = true ↔
      levelIsZero (σ ha₂.reg.1) = true := by rw [hba]
  exact clAppPorts_of_iffs ((hpf₁.trans hbf').trans hpf₂.symm)
    ((hpa₁.trans hba').trans hpa₂.symm)

/-- Rank pin (moot): had a kind carried the reg pair, the measure would
    drop — `hfᵢ.reg.2` is never heavier than `hfᵢ` (`wt_reg_le`) and a
    child is strictly lighter than its `app` node. -/
theorem appCl_hf_reg_lex_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂)) :
    LexDM (tyPairMeas Aw hf₁.reg.2 hf₂.reg.2)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
  lexDM_wt_lt_pair Aw hf₁.reg.2 hf₂.reg.2 _ _ rfl rfl
    (Nat.lt_of_le_of_lt (hf₁.wt_reg_le Aw) (by simp only [TyP.wt]; omega))
    (Nat.lt_of_le_of_lt (hf₂.wt_reg_le Aw) (by simp only [TyP.wt]; omega))

/-- The argument side's rank pin. -/
theorem appCl_ha_reg_lex_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂)) :
    LexDM (tyPairMeas Aw ha₁.reg.2 ha₂.reg.2)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
  lexDM_wt_lt_pair Aw ha₁.reg.2 ha₂.reg.2 _ _ rfl rfl
    (Nat.lt_of_le_of_lt (ha₁.wt_reg_le Aw) (by simp only [TyP.wt]; omega))
    (Nat.lt_of_le_of_lt (ha₂.wt_reg_le Aw) (by simp only [TyP.wt]; omega))

/-- The homogeneous fragment: at a SHARED ascribed type the two reg
    typings have ONE subject — the `.bitCoh` request is well-formed. The
    heterogeneity `.pi A₁ B₁ ≠ .pi A₂ B₂` is exactly what the boundary
    retains. -/
def appCl_hom_bitCoh {Eₐ : ResolvedEnv} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f A B : Expr Nat} (hf₁ hf₂ : TyP E n Γ f (.pi A B))
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp) : P2Query Eₐ :=
  .bitCoh hf₁.reg.2 hf₂.reg.2 S σ ρ

/-- …and its goal is the named bitWall: in the fragment the uniqueness
    IS an issuable kind (subject to `subAt`/`PBit` availability), i.e.
    `eqN` of two `TyP` sorts at ONE subject. -/
theorem appCl_hom_bitCoh_goal {tbl : List CRule} {Eₐ : ResolvedEnv}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf₁ hf₂ : TyP E n Γ f (.pi A B)) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
    (ρ : List Disp) :
    Goal tbl (appCl_hom_bitCoh hf₁ hf₂ S σ ρ) =
      (levelIsZero (σ hf₁.reg.1) = levelIsZero (σ hf₂.reg.1)) := rfl

/-! ## §2 `piCl`: `bodyCl` is issuable — rank and routedness of the row -/

/-- `cl_pi_clB`'s rank decrease: `hBᵢ` at child `[1]` of the `pi` node —
    strictly lighter, so the issued `.cl hB₁ hB₂` at `ρ⁺` is `Before`. -/
theorem cl_pi_body_lex_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B : Expr Nat} {u₁ u₂ v₁ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁))
    (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂))
    (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂)) :
    LexDM (tyPairMeas Aw hB₁ hB₂)
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁)
        (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)) :=
  lexDM_wt_lt_pair Aw hB₁ hB₂ _ _ rfl rfl
    (by simp only [TyP.wt]; omega) (by simp only [TyP.wt]; omega)

/-- Its display is routed: `RoutedDisp.assumption` at the domain typing —
    the `eut_lam_eut` routedness step verbatim. -/
theorem cl_pi_body_routed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u₁ : Level} {σ : Level → Level} {ρ : List Disp}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hr : RoutedDisp σ E n Γ ρ) :
    RoutedDisp σ E n (.assumption A :: Γ)
      (binderDisp (levelIsZero (σ u₁)) :: ρ) :=
  RoutedDisp.assumption hr hA₁

/-! ## §3 `letCl`: `shape` wall; bodies issuable -/

/-- `ClLetEPorts.shape` is eps-EQUALITY of the value pair — no query kind
    answers `Eq` on eps (`.cl`/``.eut` answer `ConvMod`). Inhabited on
    the diagonal: identical value typings share their eps literally. -/
theorem clLetEPorts_shape_diag {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v A : Expr Nat} (hv : TyP E n Γ v A) (σ : Level → Level)
    (ρ : List Disp) :
    (hv.eps σ ρ = .star ∧ hv.eps σ ρ = .star) ∨
      (∃ ev : ETm, ev ≠ .star ∧ hv.eps σ ρ = ev ∧ hv.eps σ ρ = ev) := by
  by_cases h : hv.eps σ ρ = .star
  · exact .inl ⟨h, h⟩
  · exact .inr ⟨_, h, rfl, rfl⟩

/-- `cl_letE_clB_*`'s rank decrease: `hbᵢ` at child `[2]` of the `letE`
    node. -/
theorem cl_letE_body_lex_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂)) :
    LexDM (tyPairMeas Aw hb₁ hb₂)
      (tyPairMeas Aw (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂)) :=
  lexDM_wt_lt_pair Aw hb₁ hb₂ _ _ rfl rfl
    (by simp only [TyP.wt]; omega) (by simp only [TyP.wt]; omega)

/-- The `drop` display is routed under `shape`'s star premise —
    `RoutedDisp.letDrop` consumes exactly `hv.eps σ ρ = .star`. -/
theorem cl_letE_body_drop_routed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (hr : RoutedDisp σ E n Γ ρ) (hstar : hv.eps σ ρ = .star) :
    RoutedDisp σ E n (.letBinding A v :: Γ) (.drop :: ρ) :=
  RoutedDisp.letDrop hr hA hv hstar

/-- The `inline` display is routed unconditionally —
    `RoutedDisp.letInline` at the actual value erasure. -/
theorem cl_letE_body_inline_routed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (hr : RoutedDisp σ E n Γ ρ) :
    RoutedDisp σ E n (.letBinding A v :: Γ) (.inline (hv.eps σ ρ) :: ρ) :=
  RoutedDisp.letInline hr hA hv

#print axioms appCl_bitWall_fun
#print axioms appCl_bitWall_arg
#print axioms clAppPorts_of_bitWalls
#print axioms appCl_hf_reg_lex_lt
#print axioms appCl_ha_reg_lex_lt
#print axioms appCl_hom_bitCoh
#print axioms appCl_hom_bitCoh_goal
#print axioms cl_pi_body_lex_lt
#print axioms cl_pi_body_routed
#print axioms clLetEPorts_shape_diag
#print axioms cl_letE_body_lex_lt
#print axioms cl_letE_body_drop_routed
#print axioms cl_letE_body_inline_routed

end Rcic.Syn
