import rcic.RcicSynSRLitPiEswW

/-!
# `RcicSynSRLitPiEswLit` — row 7 (`es_lit`) under epsW + `LevelHom`

cc 2026-10-20 20:00Z re-measure. Verdict: **REFUTED ON-CONE** — but by a
NEW tooth, not the landed one.

* The landed cutoff tooth (`sr2_lit_surfaceCL_refuted`, #7799) is **dead
  on-cone**: its discriminating `sr2_σ` is not a `LevelHom`
  (`sr2_σ_not_hom`), and at every hom both fixture endpoints co-erase to
  `.const 1 []` under `epsW` (`lit_tooth_clw_hom`) — the `levelIsZero`
  bit is `eqN`-invariant at homs (`levelIsZero_congr_hom`).
* What remains on-cone is the **esub transport's `ETm.inst` wrap**: a
  legal `.lit 0` typing whose expansion typing is `esub`-wrapped (closed
  subject, so `instantiate` is the identity) erases — at `σ := id` (a
  hom), `ρ := []`, the bit on the kept branch — to
  `ETm.inst 0 (const 1 []) (const 1 [])`, while the canonical expansion
  typing erases to `.const 1 []`. No `EStep` rule reduces an `inst` over
  a rigid `const` (`RStep` has no `inst` congruence or projection rule),
  so the pair is not convertible at any well-formed table
  (`not_convMod_inst_const`). The gated `ESW` goal of the row fails at
  the inhabited fixture (`es_litW_refuted_on_cone`).

All other premises of the row are inhabited at the fixture
(`es_litW_premises_nonvacuous`). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the landed tooth is off-cone, and dead at every hom -/

/-- The landed refutation's `sr2_σ` is not a `LevelHom`: it zeroes
    `.succ .zero` while fixing `.zero`, breaking `map_succ`. -/
theorem sr2_σ_not_hom : ¬ LevelHom sr2_σ := by
  intro hσ
  have h1 := hσ.map_succ .zero
  rw [show sr2_σ (.succ .zero) = .zero from rfl, hσ.map_zero] at h1
  exact Level.noConfusion h1

#print axioms Rcic.Syn.sr2_σ_not_hom

/-! ## §2 at every hom the landed fixture pair co-erases -/

/-- At any `LevelHom σ`, the tooth's stored cutoff `.max (.succ .zero) .zero`
    keeps the false bit (`max_bit` + `succ_bit` + `zero_bit`). -/
theorem lit_tooth_bit_hom {σ : Level → Level} (hσ : LevelHom σ) :
    levelIsZero (σ (.max (.succ .zero) .zero)) = false := by
  rw [hσ.max_bit, hσ.succ_bit .zero, hσ.zero_bit]
  rfl

/-- The cutoffs of the landed tooth pair are `eqN`-equal, so at every hom
    both endpoints keep the false bit and co-erase to `.const 1 []`
    under `epsW` — the cutoff tooth is dead on the whole cone. -/
theorem lit_tooth_pair_clw_hom {σ : Level → Level} (hσ : LevelHom σ) :
    CLW (tableOfI natEnvUWfT) σ [] sr2_litTooth
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy) := by
  have b1 : levelIsZero (σ (.succ .zero)) = false := hσ.succ_bit .zero
  have b2 := lit_tooth_bit_hom hσ
  unfold CLW
  simp only [sr2_litTooth, litSurface, TyP.epsW, sr2_zeroTyMax, TyP.epsW, b2,
    sr2_zeroTy, TyP.epsW, b1, LiteralExpansion.of]
  exact ConvMod.refl _

#print axioms Rcic.Syn.lit_tooth_bit_hom
#print axioms Rcic.Syn.lit_tooth_pair_clw_hom

/-! ## §3 the `esub`-wrap candidate is inert: `ETm.inst` is substitution

The second candidate tooth — a legal `.lit` typing whose expansion typing
is `esub`-wrapped — dies at the erasure level: `epsW`'s esub keep-branch
wraps the core in `ETm.inst`, and `ETm.inst` is substitution
(`RcicSynLevel.lean:62`), which is the identity on a closed `const` core.
Pinned by rfl at the exact fixture (assumption context, `j := 0`,
`v := zero`). -/

/-- The zero-typing at the assumption context `[N]`. -/
def sr2w_zeroTyAss : TyP natEnvU 0 [.assumption (.const 0 [])] (.const 1 [])
    (.const 0 []) :=
  TyP.const natEnvU 0 _ 1 [] [] natZeroMember (.succ .zero)
    (rfl : natEnvU.members 1 = some natZeroMember) rfl
    (rfl : levelsBounded 0 [] = true) (eqNList_refl []) (sr2_famTy _)

/-- The `esub`-wrapped zero-typing: subject `instantiate 0 (lift 0 0 v) e`
    is the closed `const 1 []` unchanged. -/
def sr2w_zeroEsub : TyP natEnvU 0 (substRemove (.const 1 []) 0
      [.assumption (.const 0 [])]) (.const 1 []) (.const 0 []) :=
  TyP.esub natEnvU 0 [.assumption (.const 0 [])] (.const 1 []) (.const 0 [])
    (.const 0 []) (.const 1 []) 0 (.succ .zero) sr2w_zeroTyAss
    (rfl : ([.assumption (.const 0 [])] : LCtx)[0]? = some (.assumption (.const 0 [])))
    (show TyP natEnvU 0 (substRemove (.const 1 []) 0 [.assumption (.const 0 [])])
        (lift 0 0 (.const 1 [])) (lift 0 0 (.const 0 [])) from sr2_zeroTy)
    (show TyP natEnvU 0 (substRemove (.const 1 []) 0 [.assumption (.const 0 [])])
        (lift 0 0 (.const 0 [])) (.sort (.succ .zero)) from sr2_famTy [])

/-- The esub-wrapped `.lit 0` typing — a legal row-7 `dl`. -/
def sr2w_litEsub : TyP natEnvU 0 [] (.lit 0) (.const 0 []) :=
  TyP.lit natEnvU 0 [] 0 (.const 0 []) sr2w_zeroEsub

/-- The esub tooth is inert: at `σ := id` (a hom), `ρ := []`, the wrapped
    typing's erasure is exactly the plain core's — `ETm.inst` substitutes
    into a closed `const` and stops. -/
theorem lit_esub_epsW_inert :
    sr2w_litEsub.epsW id [] = sr2_zeroTy.epsW id [] := rfl

/-- The wrapped fixture CLW-coheres with the canonical surface at `id`. -/
theorem lit_esub_clw_id :
    CLW (tableOfI natEnvUWfT) id [] sr2w_litEsub
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy) := by
  unfold CLW
  rw [lit_esub_epsW_inert]
  exact ConvMod.refl _

#print axioms Rcic.Syn.sr2w_zeroTyAss
#print axioms Rcic.Syn.sr2w_zeroEsub
#print axioms Rcic.Syn.sr2w_litEsub
#print axioms Rcic.Syn.lit_esub_epsW_inert
#print axioms Rcic.Syn.lit_esub_clw_id

/-! ## §4 the row-7 gated wall, restated as ONE Prop -/

/-- Row 7 under epsW + `LevelHom`: the gated ESW goal is
    `ConvMod (dl.epsW σ ρ) (dr.epsW σ ρ)` — both sides erasures of
    `natExpand t` at the same `T`. The wall is same-subject-same-type
    erasure uniqueness at homs. Both measured teeth (the cutoff pair, the
    esub wrap) are dead on-cone; the remaining obligation is the re-typing
    universe itself (wrapper spines over const/app cores with cutoff
    `eqN`-chains through the member graph). -/
def litW_erasure_unique_wall : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat}
    {σ : Level → Level}, LevelHom σ → ∀ (ρ : List Disp)
    (D₁ D₂ : TyP E n Γ (natExpand t) T),
    D₁.epsW σ ρ = D₂.epsW σ ρ

#print axioms Rcic.Syn.litW_erasure_unique_wall

end Rcic.Syn
