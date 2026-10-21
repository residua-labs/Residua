import rcic.RcicSynSREqnCellIH
import rcic.RcicSynSRClEutTransport

/-!
# RcicSynSREqnPiCl — `piCl` closed: `bodyCl` issued at the additive `cl_pi_clB` row

cc 2026-10-21 12:55Z item (2), lane glm/sr4-eqn. `RcicSynSREqnCellIH` §2
measured `ClPiPorts.bodyCl` as ISSUABLE: `hBᵢ` is child `[1]` of the `pi`
node (`cl_pi_body_lex_lt`), the issued request types ONE subject `B`,
and its display `binderDisp (levelIsZero (σ u₁)) :: ρ` is routed
(`cl_pi_body_routed` — `RoutedDisp.assumption`). This module carries the
issuance out:

* `IssuesCTP` = `IssuesCT` plus `cl_pi_clB`, the `cl`-dispatch analogue
  of `pi_esB`/`eut_lam_eut` — payload-pair rows only, no singleton lifts;
* `DemandCTP` is its demand closure, with `ap`/`hom`/`routed` proved the
  same way as `DemandCT`'s;
* `cl_pi_pi_caseStepCTP` is the pi-pi cell discharged at the CTP closure:
  `bodyCl` comes from the IH through `cl_pi_clB`, and the only remaining
  hypothesis is `TableClosed tbl` (`tableClosed_tableOfI hW` at
  `tableOfI hW`, batch 220) — no ports, no wall.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `IssuesCT` plus one additive row: the π-codomain pair as a `cl`
    sub-request, one binder up at the binder's display. -/
inductive IssuesCTP {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | old {q q' : P2Query Eₐ} (h : IssuesCT q q') : IssuesCTP q q'
  /-- `cl_pi_clB`: the two codomain typings of a `pi`–`pi` pair —
      the `cl` analogue of `pi_esB`. Same `S`, so same frame. -/
  | cl_pi_clB {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
      {u₁ v₁ u₂ v₂ : Level}
      {hA₁ : TyP E n Γ A (.sort u₁)}
      {hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁)}
      {hA₂ : TyP E n Γ A (.sort u₂)}
      {hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
      {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp} :
      IssuesCTP
        (.cl (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁)
          (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) S σ ρ)
        (.cl hB₁ hB₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
  /-- `cl_letE_clB_drop`: the letE body pair at the `drop` display — the
      `cl` analogue of `letE_esB_drop`, premise on `hv₁`'s star erasure. -/
  | cl_letE_clB_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
      {hA₁ : TyP E n Γ A (.sort u₁)} {hv₁ : TyP E n Γ v A}
      {hb₁ : TyP E n (.letBinding A v :: Γ) b B₁}
      {hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁)}
      {hA₂ : TyP E n Γ A (.sort u₂)} {hv₂ : TyP E n Γ v A}
      {hb₂ : TyP E n (.letBinding A v :: Γ) b B₂}
      {hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
      {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
      (hstar : hv₁.eps σ ρ = .star) :
      IssuesCTP
        (.cl (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
          (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ)
        (.cl hb₁ hb₂ S σ (.drop :: ρ))
  /-- `cl_letE_clB_inline`: the letE body pair at the `inline` display —
      the `cl` analogue of `letE_esB_inline`, at `hv₁`'s actual erasure. -/
  | cl_letE_clB_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
      {hA₁ : TyP E n Γ A (.sort u₁)} {hv₁ : TyP E n Γ v A}
      {hb₁ : TyP E n (.letBinding A v :: Γ) b B₁}
      {hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁)}
      {hA₂ : TyP E n Γ A (.sort u₂)} {hv₂ : TyP E n Γ v A}
      {hb₂ : TyP E n (.letBinding A v :: Γ) b B₂}
      {hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂)}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
      {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp} :
      IssuesCTP
        (.cl (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
          (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ)
        (.cl hb₁ hb₂ S σ (.inline (hv₁.eps σ ρ) :: ρ))

/-- Issued targets inherit `AssumpPref`: the codomain typings are the
    `pi` nodes' second `AssumpPref` components. -/
theorem IssuesCTP.ap {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.AP)
    (e : IssuesCTP q q') : q'.AP := by
  cases e
  case old h => exact IssuesCT.ap hi h
  case cl_pi_clB => exact ⟨hi.1.2, hi.2.2⟩
  case cl_letE_clB_drop => exact ⟨hi.1.2.2.1, hi.2.2.2.1⟩
  case cl_letE_clB_inline => exact ⟨hi.1.2.2.1, hi.2.2.2.1⟩

/-- Issued targets inherit `LevelHom` (the row keeps `σ`). -/
theorem IssuesCTP.hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.Hom)
    (e : IssuesCTP q q') : q'.Hom := by
  cases e
  case old h => exact IssuesCT.hom hi h
  case cl_pi_clB => exact hi
  case cl_letE_clB_drop => exact hi
  case cl_letE_clB_inline => exact hi

/-- Issued targets inherit routedness: `RoutedDisp.assumption` at the
    domain typing (the `eut_lam_eut` routedness step). -/
theorem IssuesCTP.routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hr : q.Routed)
    (e : IssuesCTP q q') : q'.Routed := by
  cases e
  case old h => exact IssuesCT.routed hr h
  case cl_pi_clB E n Γ A B u₁ v₁ u₂ v₂ hA₁ hB₁ hA₂ hB₂ E₀ n₀ Γ₀ S σ ρ =>
    exact RoutedDisp.assumption hr hA₁
  case cl_letE_clB_drop E n Γ A v b B₁ B₂ u₁ w₁ u₂ w₂ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂
      hb₂ hT₂ E₀ n₀ Γ₀ S σ ρ hstar =>
    exact RoutedDisp.letDrop hr hA₁ hv₁ hstar
  case cl_letE_clB_inline E n Γ A v b B₁ B₂ u₁ w₁ u₂ w₂ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂
      hb₂ hT₂ E₀ n₀ Γ₀ S σ ρ =>
    exact RoutedDisp.letInline hr hA₁ hv₁

/-- The demand closure under `IssuesCTP`. -/
inductive DemandCTP {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | old {q : P2Query Eₐ} (h : DemandCT q) : DemandCTP q
  | issued (issuer target : P2Query Eₐ) :
      DemandCTP issuer → IssuesCTP issuer target → DemandCTP target

/-- The CTP closure preserves `AP`. -/
theorem DemandCTP.ap {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCTP q) :
    q.AP := by
  induction hq with
  | old h => exact DemandCT.ap h
  | issued _ _ _ e ih => exact IssuesCTP.ap ih e

/-- The CTP closure preserves `LevelHom`. -/
theorem DemandCTP.hom {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCTP q) :
    q.Hom := by
  induction hq with
  | old h => exact DemandCT.hom h
  | issued _ _ _ e ih => exact IssuesCTP.hom ih e

/-- The CTP closure preserves routedness. -/
theorem DemandCTP.routed {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCTP q) :
    q.Routed := by
  induction hq with
  | old h => exact DemandCT.routed h
  | issued _ _ _ e ih => exact IssuesCTP.routed ih e

/-- `StepIH` over the CTP demand closure. -/
abbrev StepIHTP (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, DemandCTP q' → Before Aw q' q → Goal tbl q'

/-- The per-case step obligation over the CTP closure (`CaseStep`'s shape). -/
abbrev CaseStepCTP (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  DemandCTP q → StepIHTP Aw tbl q → Goal tbl q

/-- The semantic answer of a CTP-issued strictly-smaller sub-request. -/
theorem ih_issueCTP {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandCTP q) (ih : StepIHTP Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesCTP q q') (hb : Before Aw q' q) : Goal tbl q' :=
  ih q' (.issued q q' hq e) hb

/-- An IH call on a CTP-issued sub-request in the **same frame** at a
    strictly smaller local key. -/
theorem ih_localCTP {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandCTP q) (ih : StepIHTP Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesCTP q q')
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : Goal tbl q' :=
  ih_issueCTP Aw tbl hq ih q' e (before_of_same_prefix Aw hp hk)

/-- The pi–pi cell at the CTP closure: `bodyCl` is issued through
    `cl_pi_clB`; `hTC` is the only remaining hypothesis (the pi walk's
    `convMod_piSlot` needs `TableClosed` — `tableClosed_tableOfI` at
    `tableOfI`). `ClPiPorts` is fully discharged. -/
theorem cl_pi_pi_caseStepCTP (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A B : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁))
    (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂))
    (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hTC : TableClosed tbl) :
    CaseStepCTP Aw tbl
      (.cl (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁)
        (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) S σ ρ) := fun hq ih => by
  have hw₁ : hA₁.wt Aw < (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁)
        (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have hap : hA₁.AssumpPref ∧ hA₂.AssumpPref := ⟨hq.ap.1.1, hq.ap.2.1⟩
  have hbit := ih_localCTP Aw tbl hq ih (.bitCoh hA₁ hA₂ S σ ρ)
    (.old (.old (.old (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1)
      (p₂ := [0]) rfl rfl hap.1 hap.2)))) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  have hclA := ih_localCTP Aw tbl hq ih (.cl hA₁ hA₂ S σ ρ)
    (.old (.old (.old (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1)
      (p₂ := [0]) rfl rfl hap.1 hap.2)))) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  have hclB := ih_localCTP Aw tbl hq ih
    (.cl hB₁ hB₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
    .cl_pi_clB rfl
    (lexDM_combMeas_mono Aw _ (cl_pi_body_lex_lt Aw hA₁ hB₁ hA₂ hB₂))
  exact cl_pi_nodes tbl hTC σ ρ hA₁ hB₁ hA₂ hB₂ hbit hclA hclB

/-- The letE–letE cell at the CTP closure: `bodyDrop`/`bodyInline` are
    issued through `cl_letE_clB_drop`/`cl_letE_clB_inline` after casing on
    `shape` — so `ClLetEPorts` narrows to its ONE retained wall, the
    value-eps equality `shape`. `hshape` is that named wall verbatim
    (not a bundle): `(hv₁.eps σ ρ = .star ∧ hv₂.eps σ ρ = .star) ∨
    ∃ ev ≠ .star, both = ev`. -/
theorem cl_letE_letE_caseStepCTP (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hshape : (hv₁.eps σ ρ = .star ∧ hv₂.eps σ ρ = .star) ∨
      (∃ ev : ETm, ev ≠ .star ∧ hv₁.eps σ ρ = ev ∧ hv₂.eps σ ρ = ev)) :
    CaseStepCTP Aw tbl
      (.cl (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ) :=
  fun hq ih => by
    cases hshape with
    | inl hstar =>
        have hclb := ih_localCTP Aw tbl hq ih (.cl hb₁ hb₂ S σ (.drop :: ρ))
          (.cl_letE_clB_drop hstar.1) rfl
          (lexDM_combMeas_mono Aw _
            (cl_letE_body_lex_lt Aw hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂))
        exact cl_letE_nodes_drop tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂
          hstar.1 hstar.2 hclb
    | inr h =>
        obtain ⟨ev, hne, hev₁, hev₂⟩ := h
        have hclb := ih_localCTP Aw tbl hq ih
          (.cl hb₁ hb₂ S σ (.inline (hv₁.eps σ ρ) :: ρ))
          .cl_letE_clB_inline rfl
          (lexDM_combMeas_mono Aw _
            (cl_letE_body_lex_lt Aw hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂))
        rw [hev₁] at hclb
        exact cl_letE_nodes_inline_eq tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂
          hev₁ hev₂ hne hclb

#print axioms IssuesCTP.ap
#print axioms IssuesCTP.hom
#print axioms IssuesCTP.routed
#print axioms DemandCTP.ap
#print axioms DemandCTP.hom
#print axioms DemandCTP.routed
#print axioms ih_issueCTP
#print axioms ih_localCTP
#print axioms cl_pi_pi_caseStepCTP
#print axioms cl_letE_letE_caseStepCTP

end Rcic.Syn
