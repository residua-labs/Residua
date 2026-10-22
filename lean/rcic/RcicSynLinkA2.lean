import rcic.RcicSynLinkA
import rcic.RcicSynSRLitPiErase
import rcic.RcicLevelCalc

/-!
# `RcicSynLinkA2` — link A, gap closure (cc 10:50Z)

#7894 named two gaps on the `SortUniq ⇒ erasure coherence` leg:

1. **`TyPForgetW`** — the TyP→HasTyT projection. CLOSED: `tyPErase`
   (landed, `RcicSynSRLitPiErase` §2) IS the projection, covering 14/14
   `TyP` and 24/24 `CvP` constructors under three already-named Props:
   `TyPEraseGatesW` (the four env fronts), `InstEqNCongrW` (the const
   arm's eqNList instantiation congruence — which IS gap 2), and
   `DerivedIotaEwkW` (the iota-witness env-extension boundary). The
   delivered form is `Nonempty`-valued — the honest Prop-truncation:
   extracting `HasTyT` from `Nonempty` needs choice, which is off-cone.
   `tyPForgetNW_of_gates` is the consumer name.

2. **`InstEqNCongrW`** — the eqNList instantiation slack. The exact
   `SortCoh`-shaped premise is a `TyConvT` between two instantiations of
   one type, `TyConvT E n Γ (instantiateLevels ls₀₁ A)
   (instantiateLevels ls₀₂ A)` — which is `InstEqNCongrW` itself.
   **It does NOT follow from `SortUniq`:** `SortUniq` yields `eqN u v`
   between conclusion sort indices; `InstEqNCongrW` demands a `TyConvT`
   DERIVATION — a different kind of object (`sortRetype_of_sortUniq`
   supplies `TyConvT` only at literal `.sort` endpoints, not at
   instantiated member types; `convT_instantiateLevels` differs on all
   three fronts: context `instLvlsCtx ls Γ`, arity premise
   `ls.length = a`, conclusion sort `instantiateLevels ls A`).
   Inhabited boundary, proved here: `.sort`-headed `A`
   (`instEqNCongr_sort` — covers `natFamMember.mtype`), and
   `instantiateLevels`-invariant `A` (`instEqNCongr_refl`).

**Deliverables** (only `SortUniq` + the named premises):
- `tyPSortUniqW_of_sortUniq_gates` — TyP-side sort uniqueness at a
  `CtxWfT` context (TyP does not carry ctx wellformedness).
- `constSortLadderEqNWAt_of_sortUniq` — the FULL eqNList ladder at one
  env: erase both typings, `hB3`-retype the second subject across
  `hB2`'s congruence (`tyConvT_symm`), then `su`.
- `constPair_eps_eq_of_sortUniq` — eps equality for `const`-headed
  derivation pairs at every `LevelHom` (ladder → `levelIsZero_congr_hom`
  → `eps_const_eq_of_bit`).

`closure_claim = 0`. All consumers are measurements, not supplies.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.NativeValleys

/-! ## §1 gap 1 closed — the projection is `tyPErase` -/

/-- The honest form of #7894's `TyPForgetW`: Prop-truncated. `tyPErase`
    lands here; a `Type`-valued projection would need choice to leave
    `Nonempty`, which is off-cone. -/
def TyPForgetNW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat},
    TyP E n Γ e T → Nonempty (HasTyT E n Γ e T)

/-- Gap 1 closed: the forgetful projection under the three named Props.
    Measurement, not supply — the gates/`hB2`/`hι` are the wall's own
    premises. -/
theorem tyPForgetNW_of_gates (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW)
    (hι : DerivedIotaEwkW) : TyPForgetNW :=
  fun D => tyPErase hG hB2 hι D

/-- Per-env gates out of `EnvWfT` — the four fronts
    `hasTyTWeaken`/`hasTyT_substS`/`hasTyT_instLevels`/`convT_substCongr`
    read, composed from the landed `EnvWfT` projections. -/
def tyPEraseGates_at_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    EnvClosed E ∧ EnvMembersSubstStable E ∧ EnvLevelsT E ∧
      IotaLevelsT E :=
  ⟨envClosed_of_envWfT hW, envMembersSubstStable_of_envWfT hW,
    envWfT_levels hW, iotaLevelsT_of_envWfT hW⟩

/-! ## §2 `TyConvT` symmetry (small, not on main) -/

/-- `TyConvT` is symmetric: `.refl` maps to itself, `.of` through
    `ConvT.symm`, `.trans` in reverse. -/
def tyConvT_symm {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B →
      TyConvT E n Γ B A
  | _, _, _, .refl Γ' x => .refl Γ' x
  | _, _, _, .of Γ' x y u h => .of Γ' y x u (.symm Γ' x y (.sort u) h)
  | _, _, _, .trans Γ' x y z h₁ h₂ =>
      .trans Γ' z y x (tyConvT_symm h₂) (tyConvT_symm h₁)

/-! ## §3 gap 2 — the exact premise and its inhabited boundary -/

/-- `InstEqNCongrW` at a `.sort`-headed `A` — FREE: `ConvT.sorts` under
    `.of` with `instLevel_eqNList`. Covers every sort-typed member
    `mtype`. Measurement: this is the whole of the boundary the link-A
    fixture needs. -/
def instEqNCongr_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l : Level} {ls₀₁ ls₀₂ : List Level} (hls : eqNList ls₀₁ ls₀₂) :
    Nonempty (TyConvT E n Γ (instantiateLevels ls₀₁ (.sort l))
      (instantiateLevels ls₀₂ (.sort l))) :=
  ⟨.of _ _ _ _ (.sorts _ _ _ (instLevel_eqNList hls l))⟩

/-- `InstEqNCongrW` at an `instantiateLevels`-invariant `A` — `.refl`.
    Covers `ls₀₁ = ls₀₂` and `A` without `.param` occurrences. -/
def instEqNCongr_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {ls₀₁ ls₀₂ : List Level}
    (h : instantiateLevels ls₀₁ A = instantiateLevels ls₀₂ A) :
    Nonempty (TyConvT E n Γ (instantiateLevels ls₀₁ A)
      (instantiateLevels ls₀₂ A)) :=
  h ▸ ⟨.refl _ _⟩

/-- The boundary at the link-A fixture: `natFamMember.mtype` is
    `.sort (.succ .zero)`, so the eqNList instantiation congruence is
    inhabited for the member the row-7/10 chain actually touches. -/
def sr2_instEqNCongr_mtype {ls₀₁ ls₀₂ : List Level}
    (hls : eqNList ls₀₁ ls₀₂) :
    Nonempty (TyConvT natEnvU 0 []
      (instantiateLevels ls₀₁ natFamMember.mtype)
      (instantiateLevels ls₀₂ natFamMember.mtype)) :=
  instEqNCongr_sort (l := .succ .zero) hls

/-! ## §4 the deliverables — `SortUniq` + named premises only -/

/-- TyP-side sort uniqueness at a well-formed context — the shape
    `SortUniq` can reach (a `TyP` derivation does not itself carry
    `CtxWfT`). Only `SortUniq` + the erasure triple. -/
theorem tyPSortUniqW_of_sortUniq_gates {E : ResolvedEnv} {n : Nat}
    (su : SortUniq E n) (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW)
    (hι : DerivedIotaEwkW) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u v : Level},
      TyP E n Γ A (.sort u) → TyP E n Γ A (.sort v) → eqN u v :=
  fun {_} hΓ {_ _ _} h₁ h₂ =>
    (tyPErase hG hB2 hι h₁).elim fun k₁ =>
    (tyPErase hG hB2 hι h₂).elim fun k₂ => su hΓ k₁ k₂

/-- The `CtxWfT`-gated const-sort ladder at one env — `SortUniq`'s exact
    reach through the erasure. -/
def ConstSortLadderEqNWAt (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {ls₀₁ ls₀₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level},
    eqNList ls₀₁ ls₀₂ →
    TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁) →
    TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂) → eqN u₁ u₂

/-- **Link A delivered:** the full eqNList-slack ladder at one env from
    `SortUniq` + the named premises. Erase both `TyP` typings (`tyPErase`),
    `hB3`-retype the second's subject across `hB2`'s instantiation
    congruence (symmetrised), then `su` at the shared subject. This is
    `constSortLadderEqNWWf_of_coneRows`'s shape with `SortUniq` in place
    of the row-1 supplier — measurement, not supply. -/
theorem constSortLadderEqNWAt_of_sortUniq {E : ResolvedEnv} {n : Nat}
    (su : SortUniq E n) (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW)
    (hι : DerivedIotaEwkW) (hB3 : ConvSubjectRetypeW) :
    ConstSortLadderEqNWAt E n :=
  fun {_} hΓ {_ _ _ _ _} hls hT₁ hT₂ =>
    (tyPErase hG hB2 hι hT₁).elim fun k₁ =>
    (tyPErase hG hB2 hι hT₂).elim fun k₂ =>
    (hB2 hls).elim fun kc =>
    (hB3 k₂ (tyConvT_symm kc)).elim fun k₂' =>
    su hΓ k₁ k₂'

/-- eps-independence at `const`-headed pairs: `SortUniq` + the named
    premises give `eqN u₁ u₂` through the ladder; `levelIsZero_congr_hom`
    turns it into bit equality at every `LevelHom`;
    `eps_const_eq_of_bit` (#7894) lands the erasure equality. This is
    the `Eq`-form endpoint of link A, conditional on the named boundary.
    Measurement, not supply. -/
theorem constPair_eps_eq_of_sortUniq {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls ls₀₁ ls₀₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level}
    {hres₁ hres₂ : E.members r = some m}
    {hlen₁ hlen₂ : ls.length = m.arity}
    {hwf₁ hwf₂ : levelsBounded n ls = true}
    {hls₁ : eqNList ls ls₀₁} {hls₂ : eqNList ls ls₀₂}
    (su : SortUniq E n) (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW)
    (hι : DerivedIotaEwkW) (hB3 : ConvSubjectRetypeW)
    (hΓ : CtxWfT E n Γ)
    (hT₁ : TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp} :
    (TyP.const E n Γ r ls ls₀₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁).eps σ ρ
      = (TyP.const E n Γ r ls ls₀₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂).eps
        σ ρ :=
  eps_const_eq_of_bit hT₁ hT₂
    (levelIsZero_congr_hom hσ
      (constSortLadderEqNWAt_of_sortUniq su hG hB2 hι hB3 hΓ
        (eqNList_trans (eqNList_symm hls₁) hls₂) hT₁ hT₂))

#print axioms Rcic.Syn.TyPForgetNW
#print axioms Rcic.Syn.tyPForgetNW_of_gates
#print axioms Rcic.Syn.tyPEraseGates_at_of_envWfT
#print axioms Rcic.Syn.tyConvT_symm
#print axioms Rcic.Syn.instEqNCongr_sort
#print axioms Rcic.Syn.instEqNCongr_refl
#print axioms Rcic.Syn.sr2_instEqNCongr_mtype
#print axioms Rcic.Syn.tyPSortUniqW_of_sortUniq_gates
#print axioms Rcic.Syn.ConstSortLadderEqNWAt
#print axioms Rcic.Syn.constSortLadderEqNWAt_of_sortUniq
#print axioms Rcic.Syn.constPair_eps_eq_of_sortUniq

end Rcic.Syn
