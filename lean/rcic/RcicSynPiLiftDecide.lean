import rcic.RcicSynBelowCToRows
import rcic.RcicSynSortRow
import rcic.RcicSynTable
import rcic.RcicConvPlus
import rcic.RcicSynLetInline
import rcic.RcicSynEnvRebase
import rcic.RcicSynPiLift

/-!
# `EpsConvReflects` — decisive measurement (Route C, cc 10:50Z)

The syntactic route's core open proposition: erased conversion of
`TyP.eps`-images reflects back to typed `TyConvT`, at least at the Π
components piRow consumes. This module decides it.

## (a) the proved fragment — sort-headed endpoints, faithful σ

`epsReflD_sortNode`: for `TyP.sort`-headed derivations at *any* `TableWF`
table, erased conversion `ConvMod (EStep tbl) LvlEq (sort (σ l)) (sort (σ l'))`
reflects to `Nonempty (TyConvT Γ (sort l) (sort l'))` — **unconditionally**
once `σ` is `EpsLevelFaithful` (eqN-injective). The leg is `eqN_of_convE_sort_wf`
(erased sort-sort inversion at `TableWF`) + the gate `EpsLevelFaithful`. No
`AllBelow`/`AllBelowScoped` premise: the erased-side inversion is raw.

`levelIsZero_sigma_eq` is the companion bit-faithfulness lemma: under
`LevelHom σ + EpsLevelFaithful σ`, `levelIsZero (σ l) = levelIsZero l` pointwise — so
the `piSlot` drop/keep bit is *faithful*, and the cross-bit display escape
route of the ungated statement cannot exist.

## the gated restatement (cc 12:35Z) — §4

`EpsReflSameTyInj`: `EpsReflSameTy` with `EpsLevelFaithful σ` restored as a premise.
On-cone at `σ = id` (`epsLevelFaithful_id`). The gate is *tight around the measured
obstruction*: `pilift_eps_conv_inj_absent` shows the counterexample pair's
erased-conv premise is unsatisfiable under injective σ — `eqN (σ (param 1))
(σ (param 5))` reflects through `EpsLevelFaithful` to `eqN (param 1) (param 5)`,
refuted by `eval`.

Proof-attempt results on the gated form:

- **irr-free fragment**: `epsReflD_sortNode` (sort atoms) +
  `epsReflD_piComponents` (the Π-Π step) — a lifted Π conv decomposes at a
  shared drop-bit into `ConvMod` of domain epses (`convE_pi_inv_wf`) and of
  codomain epses (`convMod_unpiSlot` under `.drop`, direct under `.keep`).
  The residual is the recursion ports — component `ConvMod → TyConvT` at
  sub-derivations — i.e. `EpsReflSameTyInj` applied structurally; full
  induction additionally needs binder-ctx transport
  (`TyConvT (A::Γ) B B'` under `A ≈ A'`) and the wrapper nodes
  (`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`).
- **with irr**: `epsReflD_conv_head` — `TyP.conv` nodes are eps-invisible
  (`eps_conv` is `rfl`), so `irr`/`beta`/`eta` inside a `CvP` cannot be seen
  at the erased surface. At endpoints the with-irr fragment coincides with
  the irr-free one; `irr` only matters inside component consumers.

## (b) the inhabited same-type counterexample

`piliftDL`/`piliftDR`: `Π (x : sort (param i)), ∀ P : Prop, P` for `i = 1,5`,
both typed at `sort 0` in `emptyEnv` at level arity 6
(`imax (succ (param i)) 0 ≈ 0` gives the common target — *the same type*,
unlike the differing-target sort pair of `RcicSynPiLift`'s on-cone
refutation). Under the `LevelHom` `collapseParam` (param i ↦ param 0,
preserving `zero/succ/max/imax` — on-cone, since `LevelHom` has no
`map_param` field) the two eps-images coincide and the erased conversion is
`ConvMod.refl` — inhabited at every table.

`not_tyConvT_piLift_of_allBelowScoped`: the typed conversion is refuted —
through the standard Route-C premise `AllBelowScoped` (the channel every
landed `not_tyConvT_*` refutation carries; a hypothesis, not a supply):
`TyConvT` enriches to a `TyCvP` chain, `esChain_of_allBelowScoped` +
`convMod_of_tyCvP_esChain` collapse it at `σ = id` to `ConvMod` of the eps,
`convE_pi_inv_wf` extracts `ConvMod (sort (param 1)) (sort (param 5))`,
`eqN_of_convE_sort_wf` yields `eqN (param 1) (param 5)`, refuted at the
discriminating valuation `ρ 1 = 0, ρ 5 = 9`.

`EpsReflSameTy` — reflection between sort-typed endpoints *at the same
type* — is therefore **false** on-cone: `not_epsReflSameTy_of_allBelowScoped`
exhibits the refutation at the inhabited fixture.

## which typed rule breaks reflection — none; the collapse is below typing

The decisive content of the measurement: at sort-typed endpoints **no**
`TyP`/`ConvT` rule is the breaker.

- `★`-collapse is scope-excluded: an endpoint `TyP Γ A (sort u)` never
  erases to `★` — every eps-gate `levelIsZero (σ u')` on such an endpoint
  sees the sort *of a sort*, `succ`-headed, and `LevelHom` preserves `succ`.
- `irr`, `lit`-expansion, `letE`/`.inline`, `wk`/`esub`/`lsub` transports are
  all `ConvT`-mirrored or display-coherent.
- `ConvT.pi`/`ConvT.sorts`/`ConvT.consts` are faithful *except* through the
  level map: `eps` applies `σ` inside `.sort` (`.sort (σ l)`) and inside
  `.const` (`ls.map σ`). `LevelHom`'s missing `map_param` field lets `σ`
  identify `param 1` with `param 5` — *below* every typed rule. The single
  breaker: **universe-parameter identification under a non-injective
  `LevelHom`** — false at the atoms, hence at the Π components piRow needs.

The residual (developed in §4): the gated form is provable at sort atoms
and decomposes at Π-Π pairs (`epsReflD_piComponents`); what remains open
is the structural induction itself — component-level `ConvMod → TyConvT`
recursion ports, binder-ctx transport for the codomain chain
(`TyConvT (A::Γ) B B'` under `A ≈ A'`), and the non-syntax-directed
wrappers (`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`) — measured, not
supplied.

## §5 the K-index guard (cc 16:35Z, post-merge batch 284)

The faithful-σ gate does NOT cover the erased K channel: `iotaKRuleOf`'s
K rule carries `major = none` — it fires a stuck recursor to its minor
*regardless of the major's shape*. grok-epsc's `eqKMin`/`eqKTy` candidate
(`RcicPinEqStuckTy`: `eqKFire_ty` inhabited, `eqKFire_headed` — every
`ParRedStar` reduct stays `const 65`-headed, so no ordinary step can fire
through the bvar-major spine) is a same-type pair whose erased images can
be joined ONLY by the erased K-collapse while `TyConvT` is refuted — at
`σ = id`, orthogonal to `EpsLevelFaithful`.

- `EpsReflSameTyInjK tbl₀` — the guarded restatement: the erased premise
  measured at a K-free subtable `tbl₀`.
- `epsReflD_sortNode_kfree` / `epsReflD_piComponents_kfree` — the proved
  fragments instantiated at the empty table (`tableWF_nil`), where no
  K-step exists to collapse an index.
- `EpsKIdxMismatchW` — the wall shape the candidate must supply.
- `not_epsReflSameTyInj_of_kMismatch` — PROVED: any `EpsKIdxMismatchW`
  inhabitant refutes the *unguarded* `EpsReflSameTyInj` at that table —
  at `σ = id` itself, so no level gate can save it.

The concrete `ConvMod (EStep (tableOfK hEqWf))` inhabitance for the eqK
pair is grok-epsc's independent leg; if it lands, the guarded
`EpsReflSameTyInjK` is the surviving statement.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  {σ : Level → Level} {ρ : List Disp}

/-! ## §1 the faithfulness gate and level-map transport -/

/- The gate is the landed `EpsLevelFaithful`: an `eqN`-injective level
   map, inhabited at `id` (`epsLevelFaithful_id`). The counterexample
   map is the landed `collapseParam` (param i ↦ param 0), a `LevelHom`
   (`levelHom_collapseParam`) — on-cone, since `LevelHom` has no
   `map_param` field — refuted faithful by
   `epsLevelFaithful_collapseParam_false`. -/

/-- `LevelHom` evaluation: `eval ρ (σ l)` is `l` evaluated at `σ`'s
    parameter values. Induction on `l` using the four `map_*` fields. -/
theorem levelHom_eval (hσ : LevelHom σ) (l : Level) (ρ : Nat → Option Nat) :
    eval ρ (σ l) = eval (fun i => eval ρ (σ (.param i))) l := by
  induction l with
  | zero => rw [hσ.map_zero]; simp only [eval]
  | succ l ih => rw [hσ.map_succ]; simp only [eval]; rw [ih]
  | max a b iha ihb => rw [hσ.map_max]; simp only [eval]; rw [iha, ihb]
  | imax a b iha ihb => rw [hσ.map_imax]; simp only [eval]; rw [iha, ihb]
  | param i => rfl

/-- `eqN` is preserved by any `LevelHom` (in the `σ`-applied sense). -/
theorem eqN_map_levelHom (hσ : LevelHom σ) {a b : Level} (h : eqN a b) :
    eqN (σ a) (σ b) := fun ρ => by
  rw [levelHom_eval hσ, levelHom_eval hσ]
  exact h _

/-- Bit-faithfulness: `levelIsZero (σ l) = levelIsZero l` under
    `LevelHom + EpsLevelFaithful` — the `piSlot` drop/keep bit cannot mismatch. -/
theorem levelIsZero_sigma_eq (hσ : LevelHom σ) (hF : EpsLevelFaithful σ) (l : Level) :
    levelIsZero (σ l) = levelIsZero l := by
  by_cases hz : levelIsZero l = true
  · rw [hz]
    have hl0 : eqN l .zero := (levelIsZero_iff l).mp hz
    have hσl0 : eqN (σ l) .zero := by
      rw [← hσ.map_zero]
      exact eqN_map_levelHom hσ hl0
    have := (levelIsZero_iff (σ l)).mpr hσl0
    rw [this]
  · have hz' : levelIsZero l = false := by
      cases hl : levelIsZero l <;> simp_all
    rw [hz']
    by_cases hz2 : levelIsZero (σ l) = true
    · have hσl0 : eqN (σ l) .zero := (levelIsZero_iff (σ l)).mp hz2
      have hσl0' : eqN (σ l) (σ .zero) := by rwa [hσ.map_zero]
      have hl0 : eqN l .zero := hF hσl0'
      rw [(levelIsZero_iff l).mpr hl0] at hz'
      exact Bool.noConfusion hz'
    · have hz2' : levelIsZero (σ l) = false := by
        cases hl2 : levelIsZero (σ l) <;> simp_all
      rw [hz2']

/-! ## §2 (a) the proved fragment: reflection at `TyP.sort` nodes -/

/-- **Proved fragment.** At `TyP.sort`-headed endpoints, under a
    `LevelHom + EpsLevelFaithful` level map, erased conversion of the eps-images
    reflects to typed conversion — at every `TableWF` table, with no
    `AllBelow` premise. `eqN_of_convE_sort_wf` is the landed erased-side
    inversion. -/
theorem epsReflD_sortNode {tbl : List CRule} (hW : TableWF tbl)
    (_hσ : LevelHom σ) (hF : EpsLevelFaithful σ)
    {l k l' k' : Level} (hl : eqN k (.succ l)) (hl' : eqN k' (.succ l')) :
    ConvMod (EStep tbl) LvlEq
      ((TyP.sort E n Γ l k hl).eps σ ρ) ((TyP.sort E n Γ l' k' hl').eps σ ρ) →
    Nonempty (TyConvT E n Γ (.sort l) (.sort l')) := fun h => by
  have hσl : eqN (σ l) (σ l') :=
    eqN_of_convE_sort_wf hW (by simpa only [eps_sort] using h)
  exact ⟨.of _ _ _ (.succ l) (.sorts _ _ _ (hF hσl))⟩

/-! ## §3 (b) the inhabited same-type counterexample -/

/-- `∀ P : Prop, P` — the shared codomain (its `wk`-lift is the same term,
    `bvar 0` being bound by its own Π). -/
def piLiftSnd : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- `Π (x : sort (param 1)), ∀ P : Prop, P`. -/
def piLiftL : Expr Nat := .pi (.sort (.param 1)) piLiftSnd

/-- `Π (x : sort (param 5)), ∀ P : Prop, P`. -/
def piLiftR : Expr Nat := .pi (.sort (.param 5)) piLiftSnd

/-- `wk` of `pinForallP` into `[x : sort (param i)]`. -/
noncomputable def piliftBodyW {i : Nat} :
    TyP emptyEnv 0 [.assumption (.sort (.param i))] piLiftSnd (.sort .zero) :=
  .wk _ _ _ _ _ (.assumption _) 0 pinForallP

/-- `piliftDL : Π (x : sort (param 1)), ∀P:Prop.P : sort 0`. -/
noncomputable def piliftDL : TyP emptyEnv 0 [] piLiftL (.sort .zero) :=
  .conv _ _ _ _ (.sort (.imax (.succ (.param 1)) .zero)) (.sort .zero)
    (.succ (.imax (.succ (.param 1)) .zero))
    (.pi _ _ _ _ (.succ (.param 1)) _ .zero
      (.sort _ _ _ _ _ (eqN_refl _)) piliftBodyW)
    (.sorts _ _ _ _ _ (fun _ => rfl)
      (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (eqN_refl _)))

/-- `piliftDR : Π (x : sort (param 5)), ∀P:Prop.P : sort 0`. -/
noncomputable def piliftDR : TyP emptyEnv 0 [] piLiftR (.sort .zero) :=
  .conv _ _ _ _ (.sort (.imax (.succ (.param 5)) .zero)) (.sort .zero)
    (.succ (.imax (.succ (.param 5)) .zero))
    (.pi _ _ _ _ (.succ (.param 5)) _ .zero
      (.sort _ _ _ _ _ (eqN_refl _)) piliftBodyW)
    (.sorts _ _ _ _ _ (fun _ => rfl)
      (.sort _ _ _ _ _ (eqN_refl _)) (.sort _ _ _ _ _ (eqN_refl _)))

/-- PIN: `piliftDL.eps collapseParam []` — outer `pi` keeps (domain sort
    `succ (param 0)` is nonzero); the inner body's eps is the wk-shifted
    `pi (sort 0) (bvar 0)` (the `bvar 0` is bound by the inner Π, so the
    `lift 0 1` is the identity on it). -/
theorem piliftDL_eps : piliftDL.eps collapseParam [] =
    .pi (.sort (.param 0)) (.pi (.sort .zero) (.bvar 0)) := by
  have hz : levelIsZero (collapseParam (.succ (.param 1))) = false := rfl
  have hz0 : levelIsZero (collapseParam (.succ .zero)) = false := rfl
  have hk : ([.keep] : List Disp)[0]? = some .keep := rfl
  simp only [piliftDL, eps_conv, eps_pi_keep hz, eps_sort, piliftBodyW,
    eps_wk_keep hk, pinForallP, eps_pi_keep hz0, eps_bvar_rel hz0, collapseParam]
  rfl

theorem piliftDR_eps : piliftDR.eps collapseParam [] =
    .pi (.sort (.param 0)) (.pi (.sort .zero) (.bvar 0)) := by
  have hz : levelIsZero (collapseParam (.succ (.param 5))) = false := rfl
  have hz0 : levelIsZero (collapseParam (.succ .zero)) = false := rfl
  have hk : ([.keep] : List Disp)[0]? = some .keep := rfl
  simp only [piliftDR, eps_conv, eps_pi_keep hz, eps_sort, piliftBodyW,
    eps_wk_keep hk, pinForallP, eps_pi_keep hz0, eps_bvar_rel hz0, collapseParam]
  rfl

/-- The erased images coincide — `ConvMod.refl` at every table. -/
theorem pilift_eps_conv {tbl : List CRule} :
    ConvMod (EStep tbl) LvlEq (piliftDL.eps collapseParam []) (piliftDR.eps collapseParam []) := by
  rw [piliftDL_eps, piliftDR_eps]
  exact .refl _

/-- `piliftDL` satisfies `AssumpPref` (all nodes are `sort`/`bvar`/`pi`/
    `conv`/`wk at 0` — `AssumptionPrefix [] 0` vacuous). -/
theorem piliftDL_ap : piliftDL.AssumpPref := by
  simp only [piliftDL, TyP.AssumpPref, piliftBodyW, pinForallP, CvP.AssumpPref]
  exact ⟨⟨trivial, assumptionPrefix_zero _, ⟨trivial, trivial⟩, trivial, trivial⟩,
    trivial, trivial⟩

theorem piliftDR_ap : piliftDR.AssumpPref := by
  simp only [piliftDR, TyP.AssumpPref, piliftBodyW, pinForallP, CvP.AssumpPref]
  exact ⟨⟨trivial, assumptionPrefix_zero _, ⟨trivial, trivial⟩, trivial, trivial⟩,
    trivial, trivial⟩

/-- `MemberSortP.AssumpPref` at `emptyEnv`: `members = fun _ => none`, so
    the premise is vacuous. -/
theorem emptyEnv_msap :
    MemberSortP.AssumpPref (memberSortP_of_envWfT EnvWfT.empty) := by
  intro r m hres
  have hnone : emptyEnv.members r = none := rfl
  rw [hnone] at hres
  exact Option.noConfusion hres

/-- **(b) refutation leg**: under the standard `AllBelowScoped` Route-C
    premise (a hypothesis, as in every landed `not_tyConvT_*`), the two
    same-type terms are not `TyConvT`-related — chain collapse at `σ = id`,
    Π-domain inversion, sort inversion, `eval`-discrimination. -/
theorem not_tyConvT_piLift_of_allBelowScoped {Eₐ : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hTbl : TableWF tbl)
    (h : TyConvT emptyEnv 0 [] piLiftL piLiftR) : False := by
  let S : ScopedCtx Eₐ emptyEnv 0 [] := ⟨EnvWfT.empty, envExt_emptyEnv _, .nil⟩
  have hcan : S.can id = [] := by with_unfolding_all rfl
  have hchain := esChain_of_allBelowScoped hBel S levelHom_id
    (enrichTyConvT_of_envWfT EnvWfT.empty .nil h)
    (enrichTyConvT_of_envWfT_allAP EnvWfT.empty emptyEnv_msap .nil h)
    piliftDL piliftDL_ap piliftDR piliftDR_ap
  have hmod := convMod_of_tyCvP_esChain hchain
  rw [hcan] at hmod
  have h1 : piliftDL.eps id [] =
      .pi (.sort (.param 1)) (.pi (.sort .zero) (.bvar 0)) := by
    have hz : levelIsZero (id (.succ (.param 1))) = false := rfl
    have hz0 : levelIsZero (id (.succ .zero)) = false := rfl
    have hk : ([.keep] : List Disp)[0]? = some .keep := rfl
    simp only [piliftDL, eps_conv, eps_pi_keep hz, eps_sort, piliftBodyW,
      eps_wk_keep hk, pinForallP, eps_pi_keep hz0, eps_bvar_rel hz0]
    rfl
  have h2 : piliftDR.eps id [] =
      .pi (.sort (.param 5)) (.pi (.sort .zero) (.bvar 0)) := by
    have hz : levelIsZero (id (.succ (.param 5))) = false := rfl
    have hz0 : levelIsZero (id (.succ .zero)) = false := rfl
    have hk : ([.keep] : List Disp)[0]? = some .keep := rfl
    simp only [piliftDR, eps_conv, eps_pi_keep hz, eps_sort, piliftBodyW,
      eps_wk_keep hk, pinForallP, eps_pi_keep hz0, eps_bvar_rel hz0]
    rfl
  rw [h1, h2] at hmod
  have hdom := (convE_pi_inv_wf hTbl hmod).1
  have heq : eqN (.param 1) (.param 5) := eqN_of_convE_sort_wf hTbl hdom
  have := heq (fun i => if i = 1 then some 0 else some 9)
  simp [eval] at this

/-- **the statement (b) decides**: reflection between sort-typed endpoints
    at the *same* type — the strong form of cc's counterexample search. -/
def EpsReflSameTy (tbl : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {A A' : Expr Nat} {T : Expr Nat} {u u' : Level}
    (dl : TyP E n Γ A T) (_dT : TyP E n Γ T (.sort u))
    (dr : TyP E n Γ A' T) (_dT' : TyP E n Γ T (.sort u')),
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) →
    Nonempty (TyConvT E n Γ A A')

/-- `EpsReflSameTy` is false on-cone: `collapseParam` is a `LevelHom`, the eps
    conv is `refl`-inhabited, and the `TyConvT` is refuted under
    `AllBelowScoped`. Conditional on the Route-C premise — a measurement,
    not a supply. -/
theorem not_epsReflSameTy_of_allBelowScoped {Eₐ : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hTbl : TableWF tbl) :
    ¬ EpsReflSameTy tbl emptyEnv 0 := fun hR =>
  (hR piliftDL (.sort _ _ _ _ _ (eqN_refl _)) piliftDR
    (.sort _ _ _ _ _ (eqN_refl _)) pilift_eps_conv).elim
    (not_tyConvT_piLift_of_allBelowScoped hBel hTbl)

/-! ## §4 the gated restatement and the Π-Π fragment (cc 12:35Z)

The measured obstruction is non-injective σ; the restatement puts
`EpsLevelFaithful σ` back as a premise. `σ = id` is inhabited (`epsLevelFaithful_id`), so
`piRow`'s consumer stays on-cone at the identity map. -/

/-- **Gated restatement** (`EpsReflSameTyInj`): same-type reflection
    under an injective-on-sort-atoms level map. The counterexample
    above breaks exactly the `EpsLevelFaithful` premise, nothing else. -/
def EpsReflSameTyInj (tbl : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {A A' : Expr Nat} {T : Expr Nat} {u u' : Level}
    (_hσ : LevelHom σ) (_hF : EpsLevelFaithful σ)
    (dl : TyP E n Γ A T) (_dT : TyP E n Γ T (.sort u))
    (dr : TyP E n Γ A' T) (_dT' : TyP E n Γ T (.sort u')),
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) →
    Nonempty (TyConvT E n Γ A A')

/-- σ-generic eps pin for the left fixture: under **any** `LevelHom`,
    `piliftDL` erases to `Π (sort (σ (param 1))). (∀P:Prop.P)`. -/
theorem piliftDL_eps_σ (hσ : LevelHom σ) {ρ : List Disp} :
    piliftDL.eps σ ρ =
      .pi (.sort (σ (.param 1))) (.pi (.sort .zero) (.bvar 0)) := by
  have hz : levelIsZero (σ (.succ (.param 1))) = false := by
    rw [hσ.map_succ]; rfl
  have hz0 : levelIsZero (σ (.succ .zero)) = false := by
    rw [hσ.map_succ]; rfl
  have hk : (.keep :: ρ : List Disp)[0]? = some .keep :=
    List.getElem?_cons_zero
  simp only [piliftDL, eps_conv, eps_pi_keep hz, eps_sort, piliftBodyW,
    eps_wk_keep hk, removeAt_zero, pinForallP, eps_pi_keep hz0, eps_sort,
    eps_bvar_rel hz0, resolve_keep_zero, hσ.map_zero, pinSortP, eps_sort,
    hσ.map_zero, List.take_zero, countKeep]
  rfl

theorem piliftDR_eps_σ (hσ : LevelHom σ) {ρ : List Disp} :
    piliftDR.eps σ ρ =
      .pi (.sort (σ (.param 5))) (.pi (.sort .zero) (.bvar 0)) := by
  have hz : levelIsZero (σ (.succ (.param 5))) = false := by
    rw [hσ.map_succ]; rfl
  have hz0 : levelIsZero (σ (.succ .zero)) = false := by
    rw [hσ.map_succ]; rfl
  have hk : (.keep :: ρ : List Disp)[0]? = some .keep :=
    List.getElem?_cons_zero
  simp only [piliftDR, eps_conv, eps_pi_keep hz, eps_sort, piliftBodyW,
    eps_wk_keep hk, removeAt_zero, pinForallP, eps_pi_keep hz0, eps_sort,
    eps_bvar_rel hz0, resolve_keep_zero, hσ.map_zero, pinSortP, eps_sort,
    hσ.map_zero, List.take_zero, countKeep]
  rfl

/-- **the obstruction vanishes exactly at faithful σ**: under
    `EpsLevelFaithful`, the counterexample pair's erased-conversion premise is
    unsatisfiable at every `TableWF` table — the lifted Π conv would
    give `eqN (σ (param 1)) (σ (param 5))`, which injectivity refutes
    at `param 1`/`param 5` (discriminated by `eval`). -/
theorem pilift_eps_conv_inj_absent {tbl : List CRule} (hW : TableWF tbl)
    (hσ : LevelHom σ) (hF : EpsLevelFaithful σ) :
    ¬ ConvMod (EStep tbl) LvlEq (piliftDL.eps σ []) (piliftDR.eps σ []) := by
  intro h
  rw [piliftDL_eps_σ hσ, piliftDR_eps_σ hσ] at h
  have hdom := (convE_pi_inv_wf hW h).1
  have heq : eqN (σ (.param 1)) (σ (.param 5)) :=
    eqN_of_convE_sort_wf hW hdom
  have h15 : eqN (.param 1) (.param 5) := hF heq
  have := h15 (fun i => if i = 1 then some 0 else some 9)
  simp [eval] at this

/-- **Π-Π component decomposition (irr-free fragment, step case).**
    For `TyP.pi`-headed endpoints at a *shared* drop-bit
    (`levelIsZero (σ u) = levelIsZero (σ u')` — the sortRow/ZSC leg),
    a lifted Π-conv reduces to the two component erased convs:
    `convE_pi_inv_wf` on the domains, and on the codomains
    `convMod_unpiSlot` (needs `TableClosed`, held by `TableWF`) under
    `.drop`, direct under `.keep`. The residual component
    `ConvMod → TyConvT` legs are the recursion ports a full structural
    induction must supply — for sort-headed domains this is
    `epsReflD_sortNode`; in general this is `EpsReflSameTyInj` itself
    at the sub-derivations. -/
theorem epsReflD_piComponents {tbl : List CRule} (hW : TableWF tbl)
    {Γ : LCtx} {A B A' B' : Expr Nat} {u v u' v' : Level}
    {hA : TyP E n Γ A (.sort u)} {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
    {hA' : TyP E n Γ A' (.sort u')} {hB' : TyP E n (.assumption A' :: Γ) B' (.sort v')}
    {σ : Level → Level} {ρ : List Disp}
    (hbit : levelIsZero (σ u) = levelIsZero (σ u')) :
    ConvMod (EStep tbl) LvlEq
      ((TyP.pi E n Γ A u B v hA hB).eps σ ρ)
      ((TyP.pi E n Γ A' u' B' v' hA' hB').eps σ ρ) →
    ConvMod (EStep tbl) LvlEq (hA.eps σ ρ) (hA'.eps σ ρ) ∧
    ∃ d : Disp, ConvMod (EStep tbl) LvlEq
      (hB.eps σ (d :: ρ)) (hB'.eps σ (d :: ρ)) := by
  intro hconv
  cases hb : levelIsZero (σ u) with
  | true =>
    have hu' : levelIsZero (σ u') = true := hbit ▸ hb
    rw [eps_pi_drop hb, eps_pi_drop hu'] at hconv
    obtain ⟨hd, hc⟩ := convE_pi_inv_wf hW hconv
    exact ⟨hd, .drop, convMod_unpiSlot hW.closed hc⟩
  | false =>
    have hu' : levelIsZero (σ u') = false := hbit ▸ hb
    rw [eps_pi_keep hb, eps_pi_keep hu'] at hconv
    obtain ⟨hd, hc⟩ := convE_pi_inv_wf hW hconv
    exact ⟨hd, .keep, hc⟩

/-- **`conv`-wrappers are eps-invisible — the "with-irr" answer.** A
    `TyP.conv` node carries a `CvP` (which may internally use `irr`,
    `beta`, `zeta`, `eta`, `tyConv`, …) and `TyP.eps` drops it
    entirely (`eps_conv` is `rfl`). Reflection at a `conv`-headed
    endpoint therefore reduces to its base derivation: the with-irr
    fragment coincides with the irr-free one at the endpoint. `irr`
    can only matter inside a *component* reflection consumer, never at
    the erased surface. -/
theorem epsReflD_conv_head {tbl : List CRule} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    {h : TyP E n Γ e A} {hc : CvP E n Γ A B (.sort u)}
    {σ : Level → Level} {ρ : List Disp} {x : ETm} :
    ConvMod (EStep tbl) LvlEq ((TyP.conv E n Γ e A B u h hc).eps σ ρ) x ↔
    ConvMod (EStep tbl) LvlEq (h.eps σ ρ) x := by
  rw [eps_conv]

/-! ## §5 the K-index guard (cc 16:35Z, grok-epsc's candidate)

grok-epsc's in-flight candidate: an `eqKMin`/`eqKTy`-shaped pair —
erased-convertible at `tableOfK` (the bare-head K-rule collapses the
stuck rec to its minor spine) while a first-order evaluator separates
them (the typed K/iota never fires: the major `b` is a bvar). If it
holds it refutes `EpsReflSameTyInj` **at `tableOfK`** even at
`σ = id` — the collapse is not a level collapse but an *index*
collapse: K discards the Eq-index the evaluator can still read.

The guard that restores the cone: the erased premise must be
realizable at a **K-free subtable**. `ConvMod (EStep tbl₀) LvlEq`
with `tbl₀` carrying no K-rule cannot collapse an index — every step
it takes is index-shape-preserving. `[]` is the strongest K-free host
(`tableWF_nil`); `tableOfI` is the inhabited iota-only variant. -/

/-- **K-guarded restatement** (`EpsReflSameTyInjK`): the gated
    reflection with the erased premise taken at the K-free subtable
    `tbl₀`. Structurally identical to `EpsReflSameTyInj` at `tbl₀`;
    the guard lives in which table the premise is measured at. -/
def EpsReflSameTyInjK (tbl₀ : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {A A' : Expr Nat} {T : Expr Nat} {u u' : Level}
    (_hσ : LevelHom σ) (_hF : EpsLevelFaithful σ)
    (dl : TyP E n Γ A T) (_dT : TyP E n Γ T (.sort u))
    (dr : TyP E n Γ A' T) (_dT' : TyP E n Γ T (.sort u')),
    ConvMod (EStep tbl₀) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) →
    Nonempty (TyConvT E n Γ A A')

/-- Guarded form, sort-atom instance: `epsReflD_sortNode` at the empty
    table — no K-step exists to collapse an index, so the strongest
    guard is already inhabited for the proved fragment. -/
theorem epsReflD_sortNode_kfree {σ : Level → Level}
    (_hσ : LevelHom σ) (hF : EpsLevelFaithful σ)
    {l k l' k' : Level} (hl : eqN k (.succ l)) (hl' : eqN k' (.succ l')) :
    ConvMod (EStep []) LvlEq
      ((TyP.sort E n Γ l k hl).eps σ ρ) ((TyP.sort E n Γ l' k' hl').eps σ ρ) →
      Nonempty (TyConvT E n Γ (.sort l) (.sort l')) :=
  epsReflD_sortNode tableWF_nil _hσ hF hl hl'

/-- Guarded form, Π-Π instance: the component decomposition at the
    empty table — `convE_pi_inv_wf`/`convMod_unpiSlot` need only
    `TableWF`, and `[]` is `TableWF`. -/
theorem epsReflD_piComponents_kfree
    {Γ : LCtx} {A B A' B' : Expr Nat} {u v u' v' : Level}
    {hA : TyP E n Γ A (.sort u)} {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
    {hA' : TyP E n Γ A' (.sort u')} {hB' : TyP E n (.assumption A' :: Γ) B' (.sort v')}
    {σ : Level → Level} {ρ : List Disp}
    (hbit : levelIsZero (σ u) = levelIsZero (σ u')) :
    ConvMod (EStep []) LvlEq
      ((TyP.pi E n Γ A u B v hA hB).eps σ ρ)
      ((TyP.pi E n Γ A' u' B' v' hA' hB').eps σ ρ) →
    ConvMod (EStep []) LvlEq (hA.eps σ ρ) (hA'.eps σ ρ) ∧
    ∃ d : Disp, ConvMod (EStep []) LvlEq
      (hB.eps σ (d :: ρ)) (hB'.eps σ (d :: ρ)) :=
  epsReflD_piComponents tableWF_nil hbit

/-- The conditional K-mismatch wall, named for the audit trail: if
    grok-epsc's `eqKMin`/`eqKTy` evaluator lands, it supplies
    `EpsKIdxMismatchW` at `tableOfK` — an erased conv that no faithful
    σ can reflect — refuting `EpsReflSameTyInj` there. The guarded
    `EpsReflSameTyInjK` is the form that survives. -/
def EpsKIdxMismatchW (tbl : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∃ (Γ : LCtx) (ρ : List Disp) (A A' T : Expr Nat) (u u' : Level)
    (dl : TyP E n Γ A T) (_dT : TyP E n Γ T (.sort u))
    (dr : TyP E n Γ A' T) (_dT' : TyP E n Γ T (.sort u')),
    ConvMod (EStep tbl) LvlEq (dl.eps id ρ) (dr.eps id ρ) ∧
    ¬ Nonempty (TyConvT E n Γ A A')

/-- The conditional consequence, proved: any inhabitant of the
    K-mismatch wall refutes the *unguarded* `EpsReflSameTyInj` at that
    table — at `σ = id` itself, so no level gate can save it. -/
theorem not_epsReflSameTyInj_of_kMismatch {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} (hW : EpsKIdxMismatchW tbl E n) :
    ¬ EpsReflSameTyInj tbl E n := by
  intro hR
  obtain ⟨_, _, _, _, _, _, _, dl, dT, dr, dT', hconv, hnot⟩ := hW
  exact hnot (hR levelHom_id epsLevelFaithful_id dl dT dr dT' hconv)

end Rcic.Syn

#print axioms Rcic.Syn.epsLevelFaithful_id
#print axioms Rcic.Syn.levelHom_collapseParam
#print axioms Rcic.Syn.levelHom_eval
#print axioms Rcic.Syn.eqN_map_levelHom
#print axioms Rcic.Syn.levelIsZero_sigma_eq
#print axioms Rcic.Syn.epsReflD_sortNode
#print axioms Rcic.Syn.piLiftSnd
#print axioms Rcic.Syn.piLiftL
#print axioms Rcic.Syn.piLiftR
#print axioms Rcic.Syn.piliftBodyW
#print axioms Rcic.Syn.piliftDL
#print axioms Rcic.Syn.piliftDR
#print axioms Rcic.Syn.piliftDL_eps
#print axioms Rcic.Syn.piliftDR_eps
#print axioms Rcic.Syn.pilift_eps_conv
#print axioms Rcic.Syn.piliftDL_ap
#print axioms Rcic.Syn.piliftDR_ap
#print axioms Rcic.Syn.emptyEnv_msap
#print axioms Rcic.Syn.not_tyConvT_piLift_of_allBelowScoped
#print axioms Rcic.Syn.EpsReflSameTy
#print axioms Rcic.Syn.not_epsReflSameTy_of_allBelowScoped
#print axioms Rcic.Syn.EpsReflSameTyInj
#print axioms Rcic.Syn.piliftDL_eps_σ
#print axioms Rcic.Syn.piliftDR_eps_σ
#print axioms Rcic.Syn.pilift_eps_conv_inj_absent
#print axioms Rcic.Syn.epsReflD_piComponents
#print axioms Rcic.Syn.epsReflD_conv_head
#print axioms Rcic.Syn.EpsReflSameTyInjK
#print axioms Rcic.Syn.epsReflD_sortNode_kfree
#print axioms Rcic.Syn.epsReflD_piComponents_kfree
#print axioms Rcic.Syn.EpsKIdxMismatchW
#print axioms Rcic.Syn.not_epsReflSameTyInj_of_kMismatch
