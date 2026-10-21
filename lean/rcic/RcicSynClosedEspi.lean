import rcic.RcicSynStepFields5

/-!
# `es_pi` closed-port discharge (`RcicSynClosedEspi`)

Port audit of the `StepSuppliers.es_pi` assembly
`RcicSynStepFields5.es_pi_field` over `PiPorts`. `closure_claim = 0`.

## Measurement

| port | class | disposition |
|---|---|---|
| `tableClosed` | (c) | `TableWF.closed` — discharged in `es_pi_field_of_tableWF` |
| `leftCl` | (d) | retained verbatim — `piLeftSurface` is freshly built; no `subAt` path reaches it |
| `occHA` | (d) | retained verbatim — holds when `hA.dr` is a payload subderivation (rule-headed `hA`); transport heads re-wrap `dr`, see `es_pi_occHA_wk_absent` |
| `occHR` | (d) | retained verbatim — holds when `piDomSrc` returns a `dr`-subderivation (`pi`/`conv`/`cctx`/`esub`-here `dr`); `wk`/`linst`/`ewk`/`esub`-under re-wrap |
| `rightCl` | (d) | retained verbatim — the §3.5 deeper-codomain route `piDomain` does not supply |

Already unconditional on main: `es_pi_ih_dom`/`es_pi_ih_body` (the `pi_esA`/
`pi_esB`-issued `ES` halves) and the `occ_cl`/`occ_bitCoh` issuance given the
two receipts (`es_issued_occ_cl`, `es_issued_occ_bitCoh`).

## Deliverables

* `es_pi_field_of_tableWF` — the `es_pi` `CaseStep` from `TableWF` plus the
  four named residual ports.
* `es_pi_ports_inhabited` — non-vacuity witness: every residual port holds at
  the canonical sort-domain fixture (`tbl := []`, `nilScope`, `id`, `[]`).
* `es_pi_occHA_wk_absent` — the `occHA` tooth: a `wk`-headed `hA` re-wraps
  `dr`, so `hA.dr` is absent from `hA`'s own payload subtree.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- **`es_pi` under `TableWF`.** `tableClosed` is discharged by
    `TableWF.closed`; the four residual ports are named verbatim. -/
theorem es_pi_field_of_tableWF (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (leftCl : CL tbl σ ρ dl (piLeftSurface hA hB))
    (occHA : ∃ p, P2Query.subAt
        (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) 0 p =
      some (.ty hA.dr))
    (occHR : ∃ p, P2Query.subAt
        (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) 0 p =
      some (.ty ((dr.piDomain rfl).H)))
    (rightCl : CL tbl σ ρ (piRightSurface hA hB dr) dr) :
    CaseStep Aw tbl (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) :=
  es_pi_field Aw tbl hA hB dl dr S σ ρ
    ⟨hTbl.closed, leftCl, occHA, occHR, rightCl⟩

/-! ## The canonical sort-domain fixture -/

/-- Fixture domain sort typing `sort 0 : sort 1` at `Γ := []`. -/
def espiSortD : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)

/-- Fixture domain sort typing `sort 0 : sort 1` under the `sort 0` binder. -/
def espiSortDB : TyP emptyEnv 0 [.assumption (.sort .zero)]
    (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _)

/-- Fixture domain conversion `sort 0 ≡ sort 0 : sort 1` at `Γ := []`. -/
def espiHA : CvP emptyEnv 0 [] (.sort .zero) (.sort .zero)
    (.sort (.succ .zero)) :=
  CvP.sorts emptyEnv 0 [] .zero .zero (eqN_refl _) espiSortD espiSortD

/-- Fixture codomain conversion `sort 0 ≡ sort 0 : sort 1` under the
    `sort 0` binder. -/
def espiHB : CvP emptyEnv 0 [.assumption (.sort .zero)] (.sort .zero)
    (.sort .zero) (.sort (.succ .zero)) :=
  CvP.sorts emptyEnv 0 _ .zero .zero (eqN_refl _) espiSortDB espiSortDB

/-- Fixture left Π typing — the canonical left surface itself, so
    `leftCl` is `ConvMod.refl`. -/
noncomputable def espiDL : TyP emptyEnv 0 [] (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  piLeftSurface espiHA espiHB

/-- Fixture right Π typing — `dr` recorded exactly as
    `piRightSurface espiHA espiHB dr`: the recorded domain `espiSortD`
    (`tyCast` at `Eq.refl`) over the `cctx`-viewed codomain, so
    `rightCl` is `ConvMod.refl`. -/
def espiDR : TyP emptyEnv 0 [] (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  TyP.pi emptyEnv 0 [] (.sort .zero) (.succ .zero) (.sort .zero)
    (.succ .zero) espiSortD
    (TyP.cctx emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) (.sort .zero)
      (.sort .zero) (.succ .zero) espiHB.dr espiHA)

/-- **Non-vacuity of the residual port tuple.** At the canonical fixture
    every `PiPorts` field holds: `tableClosed` vacuously at `tbl := []`;
    `occHA`/`occHR` by the payload paths `[0,1]` (`.cv espiHA`'s `dr`
    child) and `[3,0]` (`.ty espiDR`'s domain child, which `piDomSrc`
    selects); `leftCl`/`rightCl` by `ConvMod.refl`, since the surfaces
    are `espiDL`/`espiDR` themselves. -/
theorem es_pi_ports_inhabited (Aw : Nat → Nat) :
    PiPorts Aw [] espiHA espiHB espiDL espiDR nilScope id [] where
  tableClosed := fun ρ hρ _ _ => (List.not_mem_nil _ hρ).elim
  leftCl := .refl _
  occHA := ⟨[0, 1], rfl⟩
  occHR := ⟨[3, 0], rfl⟩
  rightCl := by
    show ConvMod (EStep []) LvlEq
      ((piRightSurface espiHA espiHB espiDR).eps id []) (espiDR.eps id [])
    rw [piRightSurface_eps]
    exact .refl _

/-- The `wk`-headed domain conversion over the fixture: context-lifted by
    one `sort 0` assumption, `dr` re-wrapped as a `TyP.wk` node. -/
def espiHAwk : CvP emptyEnv 0 [.assumption (.sort .zero)] (.sort .zero)
    (.sort .zero) (.sort (.succ .zero)) :=
  CvP.wk emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero))
    (.assumption (.sort .zero)) 0 espiHA

/-- **`occHA` tooth.** For `hA` transport-headed, `hA.dr` is the re-wrapped
    `TyP.wk` node at `insertAt d 0 [] = [d]`, while every `.ty` node inside
    `.cv espiHAwk`'s own subtree lives at `Γ = []` — so no `subAt` path in
    the `hA` branch yields `.ty hA.dr`. (The full payload could still
    coincidentally host an identical node through `dl`/`dr` when those
    happen to contain it — the port is a per-instance shape condition.) -/
theorem es_pi_occHA_wk_absent :
    ¬ ∃ p : List Nat,
      DNode.subAt (.cv espiHAwk) p = some (.ty espiHAwk.dr) := by
  rintro ⟨p, hp⟩
  have hne : DNode.ty espiSortD ≠ DNode.ty espiHAwk.dr := by
    intro h; cases h
  revert hp
  match p with
  | [] => simp [DNode.subAt]
  | [0] =>
    intro hp
    simp [DNode.subAt, DNode.children, CvP.dchildren, espiHAwk] at hp
  | [0, 0] =>
    intro hp
    have h0 : DNode.subAt (.cv espiHAwk) [0, 0] =
        some (.ty espiSortD) := rfl
    rw [h0] at hp
    exact hne (Option.some.inj hp)
  | [0, 1] =>
    intro hp
    have h1 : DNode.subAt (.cv espiHAwk) [0, 1] =
        some (.ty espiSortD) := rfl
    rw [h1] at hp
    exact hne (Option.some.inj hp)
  | 0 :: 0 :: _ :: _ =>
    intro hp
    simp [DNode.subAt, DNode.children, CvP.dchildren, TyP.dchildren,
      espiHAwk, espiHA, espiSortD] at hp
  | 0 :: 1 :: _ :: _ =>
    intro hp
    simp [DNode.subAt, DNode.children, CvP.dchildren, TyP.dchildren,
      espiHAwk, espiHA, espiSortD] at hp
  | 0 :: (_ + 2) :: _ =>
    intro hp
    simp [DNode.subAt, DNode.children, CvP.dchildren, TyP.dchildren,
      espiHAwk, espiHA] at hp
  | (_ + 1) :: _ =>
    intro hp
    simp [DNode.subAt, DNode.children, CvP.dchildren, espiHAwk] at hp

end Rcic.Syn

#print axioms Rcic.Syn.es_pi_field_of_tableWF
#print axioms Rcic.Syn.es_pi_ports_inhabited
#print axioms Rcic.Syn.es_pi_occHA_wk_absent
