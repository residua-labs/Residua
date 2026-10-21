import rcic.RcicSynSlotOriginPins
import rcic.RcicSynSpineComb
import rcic.RcicSynRegStep

/-!
4c pre-assembly slice — ChatGPT's approved S0
`research/rcic/sortrow/S0_BELOWC_ALLBELOW_ASSEMBLY.md` (#7303) §4 and §5.

§4 lands `combLexDM_fixed_spine`, lifting a raw `LexDM` step through `combMeas`
at ONE fixed spine `C`: `dmStep_append_left` on the DM branch,
`Nat.add_lt_add_left` on the numeric branch. It never applies when a transport
changes `C` — `wk/esub/lsub/cctx/linst/ewk` spine changes keep their own
per-transport edges (`combLexDM_linst_strip`, `combLexDM_ewk_strip`, …).

§5 lands the four linst consumers over the composite source map
`σsrc l = σ (instLevel ls l)` — `linst` is never inverted. They reuse the
pinned native witness `linstAmbient`, `pin_linst_sort_reflection` and
`pin_linst_map_bit`. §5.2's tooth is live: the mapped-list equation used
without the `levelBounded` bound is refused on the empty-`ls` / `param 0` /
nonidentity-`σ` counterexample (`param 0` vs `zero`).

No `AllBelow` producer, coverage, or public endpoint is claimed.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Syn.SlotOriginPins

/-! ## §4 — the fixed-spine combined edge -/

/-- A `LexDM` step on the node measure lifts through `combMeas` at the SAME
    spine `C`. DM branch: `dmStep_append_left`; numeric branch:
    `Nat.add_lt_add_left`. It does not apply to a different `C`. -/
theorem combLexDM_fixed_spine (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) {a b : List Nat × Nat} (h : LexDM a b) :
    LexDM (combMeas Aw C a) (combMeas Aw C b) := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  cases h with
  | left _ _ hdm => exact Prod.Lex.left _ _ (dmStep_append_left hdm (C.atoms Aw))
  | right _ hlt => exact Prod.Lex.right _ (Nat.add_lt_add_left hlt (C.wt Aw))

/-! ## §5 — the linst consumers over `σsrc = σ ∘ instLevel ls` -/

/-- §5.1: along a `linst ls` step, the internal source map is the composite
    `σsrc l = σ (instLevel ls l)`. It stays a `LevelHom`, and on the step's
    actual source sort `u` it agrees with `σ` applied to the step's real output
    sort `instLevel ls u` — definitionally. No inversion of `linst`. -/
theorem path_linst_source_map_exact {E : ResolvedEnv} {a m : Nat} {Δ₀ Δ : LCtx}
    {A₀ A : Expr Nat} {u₀ u : Level}
    (_path : SortTyTransport E a Δ₀ A₀ u₀ m Δ A u) (n : Nat) (ls : List Level)
    (_hls : levelsBounded n ls = true) (_hlen : ls.length = m)
    (_hEL : EnvLevelsT E) (_hIL : IotaLevelsT E)
    {σ : Level → Level} (hσ : LevelHom σ) :
    LevelHom (fun l => σ (instLevel ls l)) ∧
    (fun l => σ (instLevel ls l)) u = σ (instLevel ls u) :=
  ⟨sortTransport_levelHom_linst hσ ls, rfl⟩

/-- The actual linst path's output sort is exactly `instLevel ls u` — the
    fixture's source sort `.param 0` materializes as `.zero`, not `.param 0`. -/
theorem path_linst_sort_exact :
    linstAmbient.original.sort = .param 0 ∧
    instLevel [.zero] (.param 0) = .zero ∧
    instLevel [.zero] linstAmbient.original.sort = .zero := by
  exact ⟨rfl, pin_linst_sort_reflection.1, pin_linst_sort_reflection.1⟩

/-- The proof/relevance bit changes along the actual linst path: the source
    sort's bit is `false`, the output sort's bit is `true`, and the bounded
    mapped-list adapter agrees with the composite map bit-for-bit. -/
theorem path_linst_bit_exact :
    levelIsZero (.param 0) = false ∧
    levelIsZero (instLevel [.zero] (.param 0)) = true ∧
    levelIsZero (instLevel ([.param 0].map adapterMap) (.param 0)) =
      levelIsZero (adapterMap (instLevel [.param 0] (.param 0))) :=
  ⟨pin_linst_sort_reflection.2.1, pin_linst_sort_reflection.2.2, pin_linst_map_bit⟩

/-- The linst path keeps the ORIGINAL ambient receipt and prefix: the arity
    change `1 → 0` creates no new root, and the original prefix is strictly
    shorter than the original root. -/
theorem path_linst_original_receipt :
    linstAmbient.original = levelReceipt ∧
    linstAmbient.original.index = 0 ∧
    (levelRoot.drop (linstAmbient.original.index + 1)).length = 1 ∧
    (levelRoot.drop (linstAmbient.original.index + 1)).length < levelRoot.length :=
  ⟨pin_linst_original, rfl, rfl, linstAmbient.prefix_lt⟩

/-! ## §5.2 — the unbounded mapped-list counterexample (the tooth) -/

/-- A claimed use of the mapped-list equation
    `instLevel (ls.map σ) u = σ (instLevel ls u)`. -/
structure LinstMapClaim where
  ls : List Level
  u : Level
  mapSide : Level
  compSide : Level
  deriving DecidableEq

/-- Exact: the equation is licensed only with the genuinely-held bound AND
    literal equality of the two routes' outputs. -/
def exactLinstMapEq (σ : Level → Level) (c : LinstMapClaim) : Bool :=
  levelBounded c.ls.length c.u &&
    decide (instLevel (c.ls.map σ) c.u = σ (instLevel c.ls c.u))

/-- Weak (mutant): accepts once both sides are honestly computed along their
    routes — the equation is used without ever checking the bound or the
    equality it was meant to deliver. -/
def weakLinstMapEq (σ : Level → Level) (c : LinstMapClaim) : Bool :=
  decide (c.mapSide = instLevel (c.ls.map σ) c.u ∧
    c.compSide = σ (instLevel c.ls c.u))

/-- §5.2's counterexample claim, honestly computed: `ls = []`, `u = .param 0`,
    `σ = instLevel [.zero]`. The mapped route returns `.param 0`; the composite
    route returns `.zero` — the equation is false at this input. -/
def linstUnboundedClaim : LinstMapClaim where
  ls := []
  u := .param 0
  mapSide := instLevel (([] : List Level).map adapterMap) (.param 0)
  compSide := adapterMap (instLevel [] (.param 0))

/-- The same claim with the bound really held: `ls = [.param 0]`, `u = .param 0`,
    and both routes agree. -/
def linstBoundedClaim : LinstMapClaim where
  ls := [.param 0]
  u := .param 0
  mapSide := instLevel ([.param 0].map adapterMap) (.param 0)
  compSide := adapterMap (instLevel [.param 0] (.param 0))

/-- The live §9 tooth: the unbounded use is wrongly ACCEPTED by the weak
    checker and refused by the exact one; the same exact checker accepts the
    bounded instance where the equation genuinely holds. -/
theorem pin_linst_unbounded_map_mutant :
    weakLinstMapEq adapterMap linstUnboundedClaim = true ∧
    exactLinstMapEq adapterMap linstUnboundedClaim = false ∧
    linstUnboundedClaim.mapSide = .param 0 ∧
    linstUnboundedClaim.compSide = .zero ∧
    exactLinstMapEq adapterMap linstBoundedClaim = true ∧
    weakLinstMapEq adapterMap linstBoundedClaim = true := by
  decide

end Rcic.Syn
