import rcic.RcicSynSRLitPiCLW
import rcic.RcicSynSRLitPiLit
import rcic.RcicNativeValleyDecoTransfer

/-!
# `RcicSynLinkA` — syntactic-inversion route, link A (cc 06:40Z)

Target chain for `piRow`: `model ⇒ SortUniq ⇒ erasure coherence ⇒
erased confluence ⇒ Π components`. This module measures link A:
`SortUniq E n` (landed `Rcic.Declarative.NativeValleys.SortUniq`;
`zsc_of_sortUniq` feeds it to `HostPropAudit.ZeroSortCoherence`) plus the
landed typing-erasure coherence machinery (#7811, `RcicSynSRLitPiCLW`) ⇒
`TyP.eps` derivation-independence (two typings of one term give the same
erasure).

**Conditional consumers are measurements, not supplies** — every
docstring says so. The measured verdict:

1. **The Eq-form is not free, but its failure modes are exactly
   sort-level slack.** `eps` reads no conclusion type index; derivation
   erasures differ only through (i) `levelIsZero (σ u)` bits on stored
   universes (const/bvar/pi/lam/esub nodes) and (ii) sub-derivation
   erasures (recursion). Transport wrappers (`conv`/`ewk`/`cctx`/`linst`,
   `esub`/`lsub`/`wk`) leave no syntactic residue — `ETm.inst` COMPUTES
   (`sr2_toothEsub_eps_id`: the esub-headed re-typing collapses to
   `.const 1 []` by `rfl`). On-cone instances: `sr2_zero_pair_eps_eq` and
   `sr2_lit_pair_eps_eq` hold at every `LevelHom`.
2. **Where `SortUniq` reaches:** the const-bit channel is exactly
   `eqN u₁ u₂` on the member type's sort-typings — the landed
   `ConstSortLadderEqNW` fragment (#7811). `SortUniq` (HasTyT-side)
   supplies its same-subject fragment only through the named bridge
   `TyPForgetW` (a TyP→HasTyT degradation, ABSENT on main — enrichment
   `enrichHasTyT_of_envWfT` is one-directional). The ladder's
   `eqNList`-slack arm (subjects `instantiateLevels ls₀ᵢ m.mtype` differ)
   is beyond same-subject `SortUniq` — it needs eqN-indexed sort
   coherence (`SortCoh`-shaped).
3. **The consumed form downstream is ConvMod, not Eq.** `EpsIndepConvW`
   is `CL` between same-subject derivations — exactly
   `TypingEpsCoherenceW`'s conclusion transported `epsW → eps` at
   no-inline displays (`epsIndepConvW_of_sortUniq_coh`; `SortUniq`
   inert).

So: `SortUniq ⇒ erasure coherence` is not a tautology — the named middle
is `TyPSortUniqW` via `TyPForgetW` (same-subject fragment supplied by
`constLadder_sameSubj_of_sortUniq`/`tyPSortUniqW_of_sortUniq`), and the
residual beyond it is the arm ledger, not sort facts.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.NativeValleys

/-! ## §1 the two forms of "derivation-independent" -/

/-- Link A, Eq-form: two typings of one term erase EQUAL on-cone
    (`LevelHom σ`, `RoutedDisp`). -/
def EpsDerivIndepEqW : Prop :=
  ∀ {E : ResolvedEnv} (_hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E' n Γ e T₁)
    (D₂ : TyP E' n Γ e T₂) {σ : Level → Level} (hσ : LevelHom σ)
    {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ),
    D₁.eps σ ρ = D₂.eps σ ρ

/-- Link A, ConvMod-form — the shape erased confluence actually consumes:
    same-subject derivations erase `CL`-convertibly at `tableOfI hW`.
    `TypingEpsCoherenceW`'s conclusion, at `eps`. -/
def EpsIndepConvW : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E' n Γ e T₁)
    (D₂ : TyP E' n Γ e T₂) {σ : Level → Level} (hσ : LevelHom σ)
    {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ),
    CL (tableOfI hW) σ ρ D₁ D₂

/-! ## §2 natEnvU fixture measurements (all premises inhabited) -/

/-- The expansion typing of `zero` in the once-extended context. -/
def sr2_zeroTy_at1 : TyP natEnvU 0 [.assumption (.const 0 [])]
    (.const 1 []) (.const 0 []) :=
  TyP.const natEnvU 0 [.assumption (.const 0 [])] 1 [] [] natZeroMember
    (.succ .zero) rfl rfl rfl (eqNList_refl [])
    (sr2_famTy [.assumption (.const 0 [])])

/-- The `.lit 0` typing in the once-extended context. -/
def sr2_litTooth_at1 : TyP natEnvU 0 [.assumption (.const 0 [])]
    (.lit 0) (.const 0 []) :=
  TyP.lit natEnvU 0 [.assumption (.const 0 [])] 0 (.const 0 []) sr2_zeroTy_at1

/-- An `esub`-headed second typing of `.lit 0 : const 0 []` at `[]` —
    substitution is inert on the bvar-free subject, so this is a
    same-subject, same-type, different-HEAD derivation. -/
def sr2_litToothEsub : TyP natEnvU 0 [] (.lit 0) (.const 0 []) :=
  TyP.esub natEnvU 0 [.assumption (.const 0 [])] (.lit 0) (.const 0 [])
    (.const 0 []) (.const 1 []) 0 (.succ .zero) sr2_litTooth_at1 rfl
    sr2_zeroTy (sr2_famTy [])

/-- The canonical tooth erases plainly. -/
theorem sr2_tooth_eps_id : sr2_litTooth.eps id [] = .const 1 [] := rfl

/-- The transport wrapper leaves no residue: `ETm.inst` computes on the
    closed core, so the esub-headed typing's erasure collapses to the
    same `.const 1 []` — `rfl`. -/
theorem sr2_toothEsub_eps_id :
    sr2_litToothEsub.eps id [] = .const 1 [] := rfl

/-- Same-subject const pair under hom: cutoffs `1` vs `max 1 0` erase
    EQUAL at every `LevelHom` — the `levelIsZero` bits agree because the
    stored universes are `eqN`. -/
theorem sr2_zero_pair_eps_eq {σ : Level → Level} (hσ : LevelHom σ)
    (ρ : List Disp) :
    sr2_zeroTy.eps σ ρ = sr2_zeroTyMax.eps σ ρ := by
  have b₁ : levelIsZero (σ (.succ .zero)) = false := by
    rw [hσ.map_succ]; rfl
  have b₂ : levelIsZero (σ (.max (.succ .zero) .zero)) = false := by
    rw [hσ.map_max, hσ.map_succ, hσ.map_zero]; rfl
  simp only [sr2_zeroTy, sr2_zeroTyMax, TyP.eps, b₁, b₂, List.map_nil]

/-- Same-subject pair across DIFFERENT heads (`lit` vs `esub`): erasures
    equal at every `LevelHom` — the `inst` collapse is definitional and
    the esub's own bit (`levelIsZero (σ 1)`) is hom-invariant. The Eq-form
    survives both same-head slack and cross-head transports at this
    fixture. -/
theorem sr2_lit_pair_eps_eq {σ : Level → Level} (hσ : LevelHom σ)
    (ρ : List Disp) :
    sr2_litTooth.eps σ ρ = sr2_litToothEsub.eps σ ρ := by
  have b₁ : levelIsZero (σ (.succ .zero)) = false := by
    rw [hσ.map_succ]; rfl
  have bm : levelIsZero (σ (.max (.succ .zero) .zero)) = false := by
    rw [hσ.map_max, hσ.map_succ, hσ.map_zero]; rfl
  have hl : sr2_litTooth.eps σ ρ = .const 1 [] := by
    simp only [sr2_litTooth, sr2_zeroTyMax, TyP.eps, bm, List.map_nil]
  have hr : sr2_litToothEsub.eps σ ρ = .const 1 [] := by
    simp only [sr2_litToothEsub, sr2_litTooth_at1, sr2_zeroTy_at1,
      sr2_zeroTy, TyP.eps, b₁, ETm.inst, List.map_nil]
  rw [hl, hr]

/-! ## §3 the named extra premises — where `SortUniq` enters -/

/-- **Extra premise (a), named:** the forgetful projection TyP→HasTyT.
    `SortUniq` is `HasTyT`-quantified; `TyP` derivations reach it only
    through this map. Absent on main — enrichment
    (`enrichHasTyT_of_envWfT`) is one-directional. Stated, not supplied.
    (`Type`, not `Prop`: the missing object is a projection FUNCTION.) -/
def TyPForgetW : Type :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat},
    TyP E n Γ e T → HasTyT E n Γ e T

/-- The premise is inhabited at the fixture: `sr2_famTy`'s plain image is
    a direct `HasTyT.const` derivation (TyP's extra `u`/`hT` fields are
    exactly what forgetting drops). -/
def sr2_famTy_plain :
    HasTyT natEnvU 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  HasTyT.const [] 0 [] natFamMember rfl rfl rfl

/-- TyP-side eqN sort uniqueness — what `SortUniq + TyPForgetW` supplies;
    the TyP analogue of the landed `SortUniq`. -/
def TyPSortUniqW (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {A : Expr Nat} {u v : Level},
    TyP E n Γ A (.sort u) → TyP E n Γ A (.sort v) → eqN u v

/-- Conditional consumer: `SortUniq` + the forget bridge give TyP-side
    same-subject sort uniqueness (`CtxWfT` premise explicit).
    Measurement, not supply. -/
theorem tyPSortUniqW_of_sortUniq {E : ResolvedEnv} {n : Nat}
    (su : SortUniq E n) (fg : TyPForgetW) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    ∀ {A : Expr Nat} {u v : Level},
      TyP E n Γ A (.sort u) → TyP E n Γ A (.sort v) → eqN u v :=
  fun h₁ h₂ => su hΓ (fg h₁) (fg h₂)

/-- The same-subject fragment of the landed `ConstSortLadderEqNW`:
    `SortUniq` + `TyPForgetW` supply it when the instantiating level
    lists coincide. The `eqNList`-slack arm (subjects differ:
    `instantiateLevels ls₀₁ m.mtype` vs `ls₀₂`) is NOT same-subject —
    beyond `SortUniq`'s reach; it needs eqN-indexed sort coherence
    (`SortCoh`-shaped). Measurement, not supply. -/
theorem constLadder_sameSubj_of_sortUniq {E : ResolvedEnv} {n : Nat}
    (su : SortUniq E n) (fg : TyPForgetW) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {m : CheckedMember} {u₁ u₂ : Level} {ls₀ : List Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u₂)) :
    eqN u₁ u₂ :=
  su hΓ (fg hT₁) (fg hT₂)

/-- The premise's conclusion is inhabited at the fixture: the two
    sort-typings `sr2_famTy`/`sr2_famTyMax` of `.const 0 []` agree to
    `eqN` (`sr2_eqN_max_zero`, landed) — satisfiable, not vacuous. -/
theorem sr2_ladder_instance :
    eqN (.succ .zero) (.max (.succ .zero) .zero) :=
  fun ρ => (sr2_eqN_max_zero (.succ .zero) ρ).symm

/-! ## §4 per-head measurements: where the bits live -/

/-- Two `sort`-headed derivations of one subject erase rfl-equal — the
    subject fixes `l`; the `eqN`-slack `k` never reaches the erasure. -/
theorem eps_sort_node_indep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l k₁ k₂ : Level} (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.sort E n Γ l k₁ h₁).eps σ ρ
      = (TyP.sort E n Γ l k₂ h₂).eps σ ρ := rfl

/-- `conv`-headed derivations erase to their inner derivation verbatim —
    the conversion wrapper is eps-transparent. -/
theorem eps_conv_inner {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level} (h : TyP E n Γ e A)
    (hc : CvP E n Γ A B (.sort u)) (σ : Level → Level) (ρ : List Disp) :
    (TyP.conv E n Γ e A B u h hc).eps σ ρ = h.eps σ ρ := rfl

/-- For `const`-headed derivations of the same subject, eps-equality IS
    bit-equality: the stored universes `u₁ u₂` enter only through
    `levelIsZero (σ u)`. This is the exact point where `SortUniq`-class
    premises touch the erasure. -/
theorem eps_const_eq_of_bit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls₀₁ ls₀₂ : List Level} {m : CheckedMember}
    {u₁ u₂ : Level} {hres₁ hres₂ : E.members r = some m}
    {hlen₁ hlen₂ : ls.length = m.arity}
    {hwf₁ hwf₂ : levelsBounded n ls = true}
    {hls₁ : eqNList ls ls₀₁} {hls₂ : eqNList ls ls₀₂}
    (hT₁ : TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂))
    {σ : Level → Level} {ρ : List Disp}
    (hb : levelIsZero (σ u₁) = levelIsZero (σ u₂)) :
    (TyP.const E n Γ r ls ls₀₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁).eps σ ρ
      = (TyP.const E n Γ r ls ls₀₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂).eps
        σ ρ := by
  simp only [TyP.eps, hb]

/-! ## §5 the consumer the chain actually gets -/

/-- Conditional consumer: the ConvMod-form follows from the landed
    coherence wall at no-inline derivations/displays — `SortUniq` is
    carried but inert (the supplier is `TypingEpsCoherenceW`). The two
    side-premisses `HasNoInlinePush`/`NoInlineEntry` are exactly the
    `epsW ↔ eps` bridge conditions. Measurement, not supply. -/
theorem epsIndepConvW_of_sortUniq_coh {E : ResolvedEnv} {n : Nat}
    (_su : SortUniq E n) (coh : TypingEpsCoherenceW) (hW : EnvWfT E)
    {E' : ResolvedEnv} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E' n Γ e T₁) (D₂ : TyP E' n Γ e T₂)
    (hD₁ : HasNoInlinePush D₁) (hD₂ : HasNoInlinePush D₂)
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : RoutedDisp σ E' n Γ ρ) (hni : NoInlineEntry ρ) :
    CL (tableOfI hW) σ ρ D₁ D₂ := by
  unfold CL
  rw [← epsW_eq_eps_noInline hD₁ σ ρ hni,
      ← epsW_eq_eps_noInline hD₂ σ ρ hni]
  exact coh hW D₁ D₂ hσ hρ

#print axioms Rcic.Syn.EpsDerivIndepEqW
#print axioms Rcic.Syn.EpsIndepConvW
#print axioms Rcic.Syn.sr2_zeroTy_at1
#print axioms Rcic.Syn.sr2_litTooth_at1
#print axioms Rcic.Syn.sr2_litToothEsub
#print axioms Rcic.Syn.sr2_tooth_eps_id
#print axioms Rcic.Syn.sr2_toothEsub_eps_id
#print axioms Rcic.Syn.sr2_zero_pair_eps_eq
#print axioms Rcic.Syn.sr2_lit_pair_eps_eq
#print axioms Rcic.Syn.TyPForgetW
#print axioms Rcic.Syn.sr2_famTy_plain
#print axioms Rcic.Syn.TyPSortUniqW
#print axioms Rcic.Syn.tyPSortUniqW_of_sortUniq
#print axioms Rcic.Syn.constLadder_sameSubj_of_sortUniq
#print axioms Rcic.Syn.sr2_ladder_instance
#print axioms Rcic.Syn.eps_sort_node_indep
#print axioms Rcic.Syn.eps_conv_inner
#print axioms Rcic.Syn.eps_const_eq_of_bit
#print axioms Rcic.Syn.epsIndepConvW_of_sortUniq_coh

end Rcic.Syn
