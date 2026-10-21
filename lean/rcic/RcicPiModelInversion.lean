import rcic.RcicModelShape
import rcic.RcicTypedRowsWf
import rcic.RcicAndHeadStepNoGo

/-!
# `RcicPiModelInversion` — Semantic Π-Inversion via `RcicModelShape` (arXiv 2607.13662)

This module attacks `PiInj E n` (`PiInjType E n` / `PiRowField E n`, the Π-injectivity
row of `TyConvT`) by the semantic method of *Definitional Inversion, Without
Normalisation* (arXiv 2607.13662), building directly on the landed domain and
interpretation layers `RcicDomainShape` and `RcicModelShape` (`Rcic.Domain.Model.Interp`,
`LeT`, `SEq`) and connecting to the landed large-elimination fixture
`RcicAndHeadStepNoGo` (`andEnvU`, `mixAnd_conv`, `mixAnd_headStepT_none`).

## Deliverables in this module

1. **Injective Π-interpretation and canonical bottom graphs on `RcicModelShape`**:
   - Order inversion for `piT` (`piT_leT_iff`) and `lamT` (`lamT_leT_iff`), plus
     sort/Π and bottom disjointness (`not_leT_piT_sortT`, `not_leT_sortT_piT`,
     `not_leT_lamT_botT`, `not_leT_piT_botT`).
   - The canonical bottom step-function graph `botWFun n : WFun n` (`[(⊥, ⊥)]`),
     its well-formedness (`wf_botWFun`), domain coverage (`hasDomP_botWFun`), and
     canonical `Interp` introduction/inversion for `.pi A B` (`interp_pi_botWFun`,
     `interp_pi_dom_of_botWFun`).
   - **Unconditional semantic Π-domain injectivity** (`seq_pi_dom_inv :
     SEq EI ρ (.pi A B) (.pi A' B') → SEq EI ρ A A'`), **semantic sort injectivity**
     (`seq_sort_inv : SEq EI ρ (.sort u) (.sort v) → eqN u v`), and **semantic
     Π/sort disjointness** (`not_seq_pi_sort : ¬ SEq EI ρ (.pi A B) (.sort u)`).

2. **Valuation lift/substitution algebra and constructor-by-constructor `Interp`/`SEq`
   soundness across all 18 `ConvT` constructors**:
   - Valuation shift/insert operations (`liftVal`, `insertVal`) and the lifting and
     instantiation lemmas (`interp_lift_iff`, `interp_instantiate_of_bound`).
   - Unconditional left-to-right β and ζ soundness (`interp_beta_lhs`, `interp_zeta_lhs`)
     and unconditional `SEq` soundness for `refl`, `symm`, `trans`, `tyConv`, `sorts`,
     `lit`, `app`, `lam`, `pi`, `letE`, plus `consts` (`EIConsts`) and `delta` (`EIDelta`).
   - Exact named gap statements (`BetaRhsGap`, `ZetaRhsGap`, `ZetaLocalSemGap`,
     `IotaSemGap`, `EtaSemGap`, `IrrSemGap`) and the **18-constructor Fundamental
     Lemma** (`fundamental_convT_seq`, `fundamental_tyConvT_seq`) on `RcicModelShape.SEq`,
     together with its consequences (`sortRow_of_seqModel`, `piDomSEq_of_seqModel`,
     `not_tyConvT_pi_sort_of_seqModel`).

3. **Three machine-checked admitted obstructions**:
   - **Obstruction 1 (`eta_unsound_interp_at_bot`)**: In `emptyEnv` at the `CtxWfT`
     context `Γ = [f : Sort 0 → Sort 0]`, `ConvT.eta` derives
     `(.lam (.sort 0) (.app (.bvar 1) (.bvar 0))) ≡ .bvar 0`, but at any valuation
     mapping `f` to `botT k` (as in the paper's ⊥-variable valuation), `lamT (botWFun 0)`
     approximates the η-expanded λ-term while `¬ Interp EI ρ (lamT (botWFun 0)) (.bvar 0)`
     because `RcicModelShape` does not quotient `lam [(⊥, ⊥)]` to `⊥`.
   - **Obstruction 2 (`irr_unsound_interp`)**: In `emptyEnv` at the `CtxWfT` context
     `Γ = [x : P, P : Sort 0]`, `ConvT.irr` derives `(λ y : P. x) ≡ (λ y : P. y)` at
     the proposition `P → P : Sort 0`, yet `lamT constSort0WFun` (`[(⊥, sort 0)]`)
     approximates `λ y. x` and not `λ y. y` under `ρ 0 = sortT 0`.
   - **Obstruction 3 (`whredPiClause_refuted_at_andEnvU`)**: Even after collapsing proofs
     to `⊥`, arXiv 2607.13662's weak-head-reduction logical-relation Π-clause
     (`WhredPiClause`, requiring `HeadStepTStar` reduction of both sides to `.pi`) is
     **refuted** at the admitted `EnvWfT` environment `andEnvU` and `CtxWfT` context
     `mixAndCtx`: `mixPi = Π (_ : Sort 0), Sort 0` and
     `mixAndRedex = And.rec a b (λ_. Sort 1) (λ x y. Sort 0 → Sort 0) h` are `ConvT`-convertible
     at `Sort 1` (`mixAnd_conv`), `piT ⊥ [(⊥, ⊥)]` is a lower bound of `⟦mixPi⟧_⊥`,
     yet `mixAndRedex` has no `HeadStepTStar` reduction to any `.pi A B`
     (`mixAndRedex_not_headStepTStar_pi`).

4. **Named open hypothesis bundle (`SemanticPiModel E n`) at least as strong as `PiInjType E n`**:
   - Packages a relation `RelConv : LCtx → Expr Nat → Expr Nat → Type` assuming conversion
     soundness arm by arm across all 18 `ConvT` constructors (`refl_arm` .. `irr_arm`)
     together with Π-injectivity readback (`piReadback`) on `RelConv`.
   - `fundamental_convT` and `fundamental_tyConvT` are the structural constructor-wise fold
     over those assumed arms (not a semantic fundamental lemma), and
     `piInjType_of_semanticPiModel` / `piRowField_of_semanticPiModel` are `piReadback ∘ fold`.

5. **Two-way semantic weakening, concrete `ZetaLocal` discharge, conditional `η`/`irr`/`ζ`/`β`
   lemmas, and the `SEqModelSupply` → `SemanticPiModel` bridge (vacuous on raw `Interp`)**:
   - Full two-way weakening (`interp_lift_insertVal_inv`, `interp_lift_insertVal_iff`,
     `interp_lift0_one_iff`, `seq_lift0_one_iff`) and valuation monotonicity on `insertVal`
     (`insertVal_leP`, `interp_insertVal_mono`).
   - Concrete `ZetaValOK` admissibility predicate discharging `ZetaLocalSemGap`
     (`zetaValOK_nil`, `zetaValOK_push_assumption`, `zetaValOK_push_letBinding`,
     `zetaLocalSemGap_of_zetaValOK`), plus unconditional `SEq` soundness of identity and
     vacuous ζ/β redexes (`seq_zeta_bvar0`, `seq_zeta_vacuous`,
     `interp_beta_rhs_constSortWFun`, `seq_beta_vacuous_sort`).
   - Conditional η-calculus on `Interp` (`interp_eta_rhs_lam`, `interp_app_lift0_bvar0_inv`,
     `EtaFloor`, `LamDirected`, `LamDomCovered`, `interp_eta_lhs_of_floor_directed`,
     `interp_eta_rhs_of_domCovered`, `seq_eta_of_etaReady`) and proof-irrelevance collapse
     (`BotOnly`, `seq_of_botOnly`, `seq_irrObs_at_bot`).
   - Bridge `semanticPiModel_of_seqModel` / `piInjType_of_seqModel` / `piRowField_of_seqModel`:
     by Section 7 (`valOK_empty_of_seqModel`, `tyConvT_total_of_seqModel`), the premises
     `SEqModelSupply` and `SEqPiReadbackGap` on raw `RcicModelShape.Interp` force
     `ValOK ≡ ⊥` and hence total `TyConvT`.

6. **Admitted Obstruction 4 (refutation of `BetaRhsGap` and `ZetaRhsGap` on
   `RcicModelShape.Interp`), vacuity teeth for `SEqModelSupply`, reverse-substitution
   factorization (`SubstFactorizes`), and `eqNList`-saturated `EI`**:
   - **Obstruction 4a (`beta_linear_unsound_interp`, `not_betaRhsGap_of_valOK`)**: In
     `RcicModelShape.Interp`, `.lam (.pi D C) body` restricts step-function inputs to
     lower bounds of the type annotation `.pi D C` (`piT`), while `.lam D' b` only has
     `lamT` lower bounds (`interp_pi_and_lam_eq_botT`), forcing every β-redex
     `.app (.lam (.pi D C) body) (.lam D' b)` to erase its argument to `botT n`
     (`interp_app_lam_pi_lam_inv`, `botOnly_app_lam_pi_bvar0_lam`) and refuting
     `BetaRhsGap` even for the linear identity body `.bvar 0`.
   - **Obstruction 4b (`zeta_unsound_interp`, `not_zetaRhsGap_of_valOK`)**: In
     `RcicModelShape.Interp`, `Valuation = Nat → LTShape` binds `.bvar 0` to a single
     stratified level `s.1 : Nat`, whereas `zetaBetaObsVal = Prop → Prop` has `piT`
     lower bounds at both level 1 and level 2, refuting `ZetaRhsGap` on the well-typed
     body `zetaBetaObsBody = Π (_ : X), Π (_ : X), Prop`.
   - **Vacuity teeth (`valOK_empty_of_seqModel`, `valOK_empty_of_seqModel_zeta`,
     `seqVal_total_of_seqModel`, `tyConvT_total_of_seqModel`)**: Any `SEqModelSupply` on
     raw `RcicModelShape.Interp` forces `∀ Γ ρ, ¬ ValOK Γ ρ`, making `SEqVal` total and
     forcing `SEqPiReadbackGap` to return `TyConvT` between every pair of types.
   - **Proposed repair (`SubstFactorizes`, `DirectedDen`) and `EI` closure (`eqNListClose`,
     `emptyEnvInterp`)**: Reverse-substitution factorization discharging `ZetaRhsGap`
     (`seq_zeta_of_substFactorizes`) and `EIConsts` saturation (`eiConsts_eqNListClose`).

7. **Filter-Valuation & Untyped-Lambda Domain Model (`fden` / `FSEq`): Exact Two-Way
   Substitution, Unconditional `ConvT.zeta` / `ConvT.zetaLocal` Soundness, Concrete Repairs
   of Obstructions 4a and 4b, and Admitted Obstruction 5 (`polyPiBeta_unsound_fden`)**:
   - Replaces point valuations `Valuation = Nat → LTShape` by filter valuations
     `FValuation = Nat → LTShape → Prop` and drops the parameter-domain restriction on
     `.lam` in `fden` while keeping `.pi` domain-typed and injective (`fseq_pi_dom_inv`,
     `fseq_pi_cod_sort_iff`, `fseq_sort_inv`, `not_fseq_pi_sort`).
   - Proves **exact propositional equalities (`=`)** for weakening (`fden_lift`) and
     substitution (`fden_instantiate`), yielding **unconditional two-way soundness** of
     `ConvT.zeta` (`fden_zeta`, `fseq_zeta`) and `ConvT.zetaLocal`
     (`fseq_zetaLocal_of_fzetaValOK` on `FZetaValOK`, inhabited in every `Γ` by
     `fzetaValOK_default`), and concretely repairs Obstruction 4b (`fden_letE_zetaBetaObs`)
     and Obstruction 4a (`fden_app_lam_pi_bvar0_lam`).
   - **Admitted Obstruction 5 (`isBotT_of_interp_sort_succ`, `isBotT_of_fden_sort_succ`,
     `interp_app_lam_pi_bvar0_dom_bot`, `fden_app_lam_pi_bvar0_dom_bot`,
     `polyPiBeta_unsound_fden`, `not_fbetaRhsGap_of_fvalOK`, `not_fseqModelSupply`)**:
     Even in `fden`, `RcicDomainShape` / `RcicModelShape`'s disjoint-level order `LeT`
     (`s.1 = t.1`) combined with `piT`'s level increment (`k ↦ k + 1`) forces the domain
     of any `piT a₀ g₀` approximating `.app (.lam A (.pi (.bvar 0) B)) arg` to be bottom
     (`k = k + 1` impossibility). This refutes `FSEq` on the polymorphic type-returning
     β-redex `polyPiBetaRedex = (fun (X : Sort 1) => Π (_ : X), Sort 0) (Sort 0)`,
     refutes `FBetaRhsGap` on every inhabited `FValOK`, and refutes `FSEqModelSupply`.
-/

namespace Rcic.Domain.Model.PiInversion

open Rcic.Declarative
open Rcic.Domain
open Rcic.Domain.Model

/-! ## 1. Order inversions and canonical bottom graphs on `RcicModelShape` -/

/-- `LeT` between two `piT` codes at level `n + 1` unpacks to domain and graph `LEP`. -/
theorem piT_leT_iff {n : Nat} {a a' : LSh n} {f f' : WFun n} :
    LeT (piT a f) (piT a' f') ↔
      DShape.LEP eqN a.1 a'.1 ∧ DShapeFun.LEP (DShape.LEP eqN) f.1 f'.1 :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

/-- `LeT` between two `lamT` codes at level `n + 1` unpacks to graph `LEP`. -/
theorem lamT_leT_iff {n : Nat} {f f' : WFun n} :
    LeT (lamT f) (lamT f') ↔
      DShapeFun.LEP (DShape.LEP eqN) f.1 f'.1 :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

/-- A `piT` code at level `n + 1` is never `LeT`-below a `sortT` code at level `0`. -/
theorem not_leT_piT_sortT {n : Nat} {a : LSh n} {f : WFun n} {u : Level} :
    ¬ LeT (piT a f) (sortT u) := by
  rintro ⟨h, _⟩
  exact Nat.succ_ne_zero n h

/-- A `sortT` code at level `0` is never `LeT`-below a `piT` code at level `n + 1`. -/
theorem not_leT_sortT_piT {n : Nat} {a : LSh n} {f : WFun n} {u : Level} :
    ¬ LeT (sortT u) (piT a f) := by
  rintro ⟨h, _⟩
  exact Nat.succ_ne_zero n h.symm

/-- A `lamT` code is never `LeT`-below any `botT k`. -/
theorem not_leT_lamT_botT {n k : Nat} {f : WFun n} :
    ¬ LeT (lamT f) (botT k) := by
  rintro ⟨hn, hle⟩
  have hnk : n + 1 = k := hn
  subst hnk
  exact nomatch DShape.LEP.le_bot hle rfl

/-- A `piT` code is never `LeT`-below any `botT k`. -/
theorem not_leT_piT_botT {n k : Nat} {a : LSh n} {f : WFun n} :
    ¬ LeT (piT a f) (botT k) := by
  rintro ⟨hn, hle⟩
  have hnk : n + 1 = k := hn
  subst hnk
  exact nomatch DShape.LEP.le_bot hle rfl

/-- A `sortT` code is never `LeT`-below any `botT k`. -/
theorem not_leT_sortT_botT {k : Nat} {u : Level} :
    ¬ LeT (sortT u) (botT k) := by
  rintro ⟨hn, hle⟩
  have hnk : 0 = k := hn
  subst hnk
  exact nomatch DShape0.LEP.le_bot hle

theorem not_lamT_eq_botT {n k : Nat} {f : WFun n} :
    lamT f ≠ ⟨k, WShape.bot⟩ := by
  intro h
  have hle : LeT (lamT f) (botT k) := by
    change LeT (lamT f) ⟨k, WShape.bot⟩
    rw [← h]
    exact LeT.refl _
  exact not_leT_lamT_botT hle

theorem not_piT_eq_botT {n k : Nat} {a : LSh n} {f : WFun n} :
    piT a f ≠ ⟨k, WShape.bot⟩ := by
  intro h
  have hle : LeT (piT a f) (botT k) := by
    change LeT (piT a f) ⟨k, WShape.bot⟩
    rw [← h]
    exact LeT.refl _
  exact not_leT_piT_botT hle

theorem not_sortT_eq_botT {k : Nat} {u : Level} :
    sortT u ≠ ⟨k, WShape.bot⟩ := by
  intro h
  have hle : LeT (sortT u) (botT k) := by
    change LeT (sortT u) ⟨k, WShape.bot⟩
    rw [← h]
    exact LeT.refl _
  exact not_leT_sortT_botT hle

/-- Projection extracting the step-function graph of a level-`(n + 1)` `.lam` shape. -/
def getLamGraph (n : Nat) (s : LTShape) : List (DShape Level n × DShape Level n) :=
  if h : s.1 = n + 1 then
    match h ▸ s.2.1 with
    | .lam g => g
    | _ => []
  else []

theorem getLamGraph_lamT {n : Nat} (f : WFun n) :
    getLamGraph n (lamT f) = f.1 := by
  simp [getLamGraph, lamT]

/-- The singleton `[(⊥, ⊥)]` step-function graph is well-formed at every level `n + 1`. -/
theorem wf_botWFun (n : Nat) :
    DShape.WF (α := Level) (n := n + 1) (.lam [(DShape.bot, DShape.bot)]) := by
  refine ⟨⟨?_, ?_⟩, ⟨(DShape.bot, DShape.bot), List.mem_singleton_self _,
    DShape.ble_bot _, DShape.ble_bot _⟩⟩
  · intro x hx
    rcases List.mem_singleton.1 hx with rfl
    exact ⟨DShape.wf_bot, DShape.wf_bot⟩
  · intro x hx y hy _
    rcases List.mem_singleton.1 hx with rfl
    rcases List.mem_singleton.1 hy with rfl
    refine ⟨(DShape.bot, DShape.bot), List.mem_singleton_self _, ?_, ?_, ?_⟩ <;>
      simpa [DShape.join_bot_l] using DShape.ble_bot DShape.bot

/-- The canonical bottom step-function graph `[(⊥, ⊥)]` at level `n`. -/
def botWFun (n : Nat) : WFun n :=
  ⟨[(DShape.bot, DShape.bot)], wf_botWFun n⟩

/-- `lamT (botWFun n)` has domain coverage `HasDomP` at every domain `⟨n, a⟩`. -/
theorem hasDomP_botWFun (n : Nat) (a : LSh n) :
    HasDomP (lamT (botWFun n)) ⟨n, a⟩ := by
  intro k fg x y hlam hxy
  have hnk : n + 1 = k + 1 := congrArg Sigma.fst hlam
  have hn : n = k := Nat.succ.inj hnk
  subst hn
  have hlist : (botWFun n).1 = fg.1 := by
    simpa [getLamGraph_lamT] using congrArg (getLamGraph n) hlam
  rw [← hlist] at hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  refine ⟨WShape.bot, WShape.bot, ?_, DShape.LEP.bot _, ?_, LeT.bot_le ⟨n, a⟩⟩
  · rw [← hlist]
    exact List.mem_singleton_self _
  · rw [hxy'.2]
    exact DShape.LEP.bot _

/-- Whenever `⟨n, a⟩` approximates `A`, `piT a (botWFun n)` approximates `.pi A B`
for any codomain `B`. -/
theorem interp_pi_botWFun {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {n : Nat} {a : LSh n} {A B : Expr Nat}
    (hA : Interp EI ρ ⟨n, a⟩ A) :
    Interp EI ρ (piT a (botWFun n)) (.pi A B) := by
  refine .pi hA hA (hasDomP_botWFun n a) ?_ (LeT.refl _)
  intro x y hxy _
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hy' : y = WShape.bot := Subtype.ext hxy'.2
  subst hy'
  exact .bot

/-- Whenever `⟨n, a⟩` approximates `A`, `lamT (botWFun n)` approximates `.lam A B`
for any body `B`. -/
theorem interp_lam_botWFun {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {n : Nat} {a : LSh n} {A B : Expr Nat}
    (hA : Interp EI ρ ⟨n, a⟩ A) :
    Interp EI ρ (lamT (botWFun n)) (.lam A B) := by
  refine .lam hA (hasDomP_botWFun n a) ?_ (LeT.refl _)
  intro x y hxy _
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hy' : y = WShape.bot := Subtype.ext hxy'.2
  subst hy'
  exact .bot

/-- Inverting `Interp EI ρ (piT a₀ f₀) (.pi A B)` yields `Interp EI ρ ⟨n, a₀⟩ A`. -/
theorem interp_pi_dom_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {n : Nat} {a₀ : LSh n} {f₀ : WFun n} {A B : Expr Nat}
    (H : Interp EI ρ (piT a₀ f₀) (.pi A B)) :
    Interp EI ρ ⟨n, a₀⟩ A := by
  generalize hm : piT a₀ f₀ = m at H
  cases H with
  | bot =>
    exact False.elim (not_piT_eq_botT hm)
  | pi ha _ _ _ hle =>
    rw [← hm] at hle
    rcases hle with ⟨hn, hle'⟩
    have hn' : n = _ := Nat.succ.inj hn
    subst hn'
    exact Interp.mono ha ⟨rfl, hle'.1⟩

/-- **Unconditional semantic Π-domain injectivity on `RcicModelShape.SEq`:**
if `.pi A B` and `.pi A' B'` have the same lower bounds in `Interp`, then `A` and
`A'` have the same lower bounds in `Interp`. -/
theorem seq_pi_dom_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A B A' B' : Expr Nat}
    (h : SEq EI ρ (.pi A B) (.pi A' B')) :
    SEq EI ρ A A' := by
  rintro ⟨n, a⟩
  constructor
  · intro hA
    exact interp_pi_dom_inv ((h (piT a (botWFun n))).1 (interp_pi_botWFun hA))
  · intro hA'
    exact interp_pi_dom_inv ((h (piT a (botWFun n))).2 (interp_pi_botWFun hA'))

/-- **Unconditional semantic sort injectivity on `RcicModelShape.SEq`:**
`SEq EI ρ (.sort u) (.sort v)` implies `eqN u v`. -/
theorem seq_sort_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {u v : Level}
    (h : SEq EI ρ (.sort u) (.sort v)) :
    eqN u v := by
  have hu : Interp EI ρ (sortT u) (.sort v) := (h (sortT u)).1 Interp.sort'
  rcases Interp.le_sort hu with ⟨k, hbot⟩ | hle
  · exact False.elim (not_sortT_eq_botT hbot)
  · exact sortT_leT_iff.1 hle

/-- **Unconditional semantic Π/sort disjointness on `RcicModelShape.SEq`:**
`.pi A B` and `.sort u` are never semantically equal. -/
theorem not_seq_pi_sort {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A B : Expr Nat} {u : Level} :
    ¬ SEq EI ρ (.pi A B) (.sort u) := by
  intro h
  have hpi : Interp EI ρ (piT (WShape.bot : LSh 0) (botWFun 0)) (.pi A B) :=
    interp_pi_botWFun .bot
  have hsort : Interp EI ρ (piT (WShape.bot : LSh 0) (botWFun 0)) (.sort u) :=
    (h _).1 hpi
  rcases Interp.le_sort hsort with ⟨k, hbot⟩ | hle
  · exact not_piT_eq_botT hbot
  · exact not_leT_piT_sortT hle

/-- Well-formedness of the constant sort step-function graph `[(⊥, sort u)]` at level 1. -/
theorem wf_constSortWFun (u : Level) :
    DShape.WF (α := Level) (n := 1) (.lam [(DShape0.bot, DShape0.sort u)]) := by
  have hbeq : (u == u) = true := beq_self_eq_true u
  refine ⟨⟨?_, ?_⟩,
    ⟨(DShape0.bot, DShape0.sort u), List.mem_singleton_self _, rfl, rfl⟩⟩
  · intro x hx
    rcases List.mem_singleton.1 hx with rfl
    exact ⟨trivial, trivial⟩
  · intro x hx y hy _
    rcases List.mem_singleton.1 hx with rfl
    rcases List.mem_singleton.1 hy with rfl
    refine ⟨(DShape0.bot, DShape0.sort u),
      List.mem_singleton_self _, rfl, ?_, ?_⟩ <;>
      simp [DShape.join, DShape.ble, DShape0.join, DShape0.ble, hbeq]

/-- The constant sort step-function graph `[(⊥, sort u)] : WFun 0`. -/
def constSortWFun (u : Level) : WFun 0 :=
  ⟨[(DShape0.bot, DShape0.sort u)], wf_constSortWFun u⟩

theorem hasDomP_constSortWFun (u : Level) (a : LSh 0) :
    HasDomP (lamT (constSortWFun u)) ⟨0, a⟩ := by
  intro k fg x y hlam hxy
  have hnk : 1 = k + 1 := congrArg Sigma.fst hlam
  have hk : 0 = k := Nat.succ.inj hnk
  subst hk
  have hlist : (constSortWFun u).1 = fg.1 := by
    simpa [getLamGraph_lamT] using congrArg (getLamGraph 0) hlam
  rw [← hlist] at hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  refine ⟨WShape.bot, ⟨DShape0.sort u, trivial⟩, ?_,
    DShape.LEP.bot _, ?_, LeT.bot_le ⟨0, a⟩⟩
  · rw [← hlist]
    exact List.mem_singleton_self _
  · rw [hxy'.2]
    exact DShape0.LEP.rfl (fun _ _ => rfl) _

/-- If `sortT u` approximates codomain `B` under `ρ.push (botT 0)`, then
`piT ⊥ (constSortWFun u)` approximates `.pi A B`. -/
theorem interp_pi_constSortWFun {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {u : Level} {A B : Expr Nat}
    (hB : Interp EI (ρ.push (botT 0)) (sortT u) B) :
    Interp EI ρ (piT (WShape.bot : LSh 0) (constSortWFun u)) (.pi A B) := by
  refine .pi .bot .bot (hasDomP_constSortWFun u WShape.bot) ?_ (LeT.refl _)
  intro x y hxy _
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hx' : (⟨0, x⟩ : LTShape) = botT 0 :=
    congrArg (Sigma.mk 0) (Subtype.ext hxy'.1)
  have hy' : (⟨0, y⟩ : LTShape) = sortT u :=
    congrArg (Sigma.mk 0) (Subtype.ext hxy'.2)
  rw [hx', hy']
  exact hB

/-- Inverting `Interp EI ρ (piT ⊥ (constSortWFun u)) (.pi A B)` recovers
`Interp EI (ρ.push (botT 0)) (sortT u) B`. -/
theorem interp_pi_cod_sort_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {u : Level} {A B : Expr Nat}
    (H : Interp EI ρ (piT (WShape.bot : LSh 0) (constSortWFun u)) (.pi A B)) :
    Interp EI (ρ.push (botT 0)) (sortT u) B := by
  generalize hm : piT (WShape.bot : LSh 0) (constSortWFun u) = m at H
  cases H with
  | bot =>
    exact False.elim (not_piT_eq_botT hm)
  | @pi _ _ n' a _ f _ _ _ _ hdom hb hle =>
    rw [← hm] at hle
    have hn : 1 = n' + 1 := hle.1
    have hn' : 0 = n' := Nat.succ.inj hn
    subst hn'
    have hfg : DShapeFun.LEP (DShape.LEP eqN) (constSortWFun u).1 f.1 := hle.2.2
    obtain ⟨⟨u₀, v₀⟩, huv, hbotu, hsortv⟩ :=
      hfg (DShape0.bot, DShape0.sort u) (List.mem_singleton_self _)
    have hwu : DShape.WF u₀ := (f.2.1.entries (u₀, v₀) huv).1
    have hwv : DShape.WF v₀ := (f.2.1.entries (u₀, v₀) huv).2
    obtain ⟨x', y', hx'y', hx'u, hvy', hx'a⟩ :=
      hdom 0 f ⟨u₀, hwu⟩ ⟨v₀, hwv⟩ rfl huv
    have hu_eq : u₀ = DShape0.bot := DShape0.LEP.le_bot hbotu
    have hx'_eq : x'.1 = DShape0.bot := DShape0.LEP.le_bot (hu_eq ▸ hx'u)
    have hx'_bot : (⟨0, x'⟩ : LTShape) = botT 0 :=
      congrArg (Sigma.mk 0) (Subtype.ext hx'_eq)
    have hbody : Interp EI (ρ.push ⟨0, x'⟩) ⟨0, y'⟩ B := hb x' y' hx'y' hx'a
    rw [hx'_bot] at hbody
    have hsort_y' : LeT (sortT u) ⟨0, y'⟩ :=
      ⟨rfl, DShape0.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hsortv hvy'⟩
    exact Interp.mono hbody hsort_y'

/-- **Unconditional semantic Π-codomain sort-probe injectivity on `RcicModelShape.SEq`:**
if `.pi A B` and `.pi A' B'` have the same lower bounds in `Interp`, then `B` and `B'`
have the same `sortT u` lower bounds under `ρ.push (botT 0)`. -/
theorem seq_pi_cod_sort_iff {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A B A' B' : Expr Nat}
    (h : SEq EI ρ (.pi A B) (.pi A' B')) (u : Level) :
    Interp EI (ρ.push (botT 0)) (sortT u) B ↔
      Interp EI (ρ.push (botT 0)) (sortT u) B' :=
  ⟨fun hB => interp_pi_cod_sort_inv ((h _).1 (interp_pi_constSortWFun hB)),
   fun hB' => interp_pi_cod_sort_inv ((h _).2 (interp_pi_constSortWFun hB'))⟩

/-- Specialisation of `seq_pi_cod_sort_iff`: `SEq EI ρ (.pi A (.sort u)) (.pi A' (.sort v))`
implies `eqN u v`. -/
theorem seq_pi_cod_sort_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A A' : Expr Nat} {u v : Level}
    (h : SEq EI ρ (.pi A (.sort u)) (.pi A' (.sort v))) :
    eqN u v := by
  have hsort : Interp EI (ρ.push (botT 0)) (sortT u) (.sort v) :=
    (seq_pi_cod_sort_iff h u).1 Interp.sort'
  rcases Interp.le_sort hsort with ⟨k, hbot⟩ | hle
  · exact False.elim (not_sortT_eq_botT hbot)
  · exact sortT_leT_iff.1 hle

/-! ## 2. Valuation lift/substitution algebra and constructor-by-constructor `Interp` laws -/

/-- Shift valuation `ρ` above cutoff `c` by `k` de Bruijn indices (inserting `botT 0`
in the shifted gap). -/
def liftVal (c k : Nat) (ρ : Valuation) : Valuation :=
  fun i => if i < c then ρ i else if i < c + k then botT 0 else ρ (i - k)

/-- Insert compact shape `s` at de Bruijn index `k` in `ρ`. -/
def insertVal (k : Nat) (s : LTShape) (ρ : Valuation) : Valuation :=
  fun i => if i < k then ρ i else if i = k then s else ρ (i - 1)

theorem liftVal_push (c k : Nat) (ρ : Valuation) (x : LTShape) :
    (liftVal c k ρ).push x = liftVal (c + 1) k (ρ.push x) := by
  funext i
  cases i with
  | zero =>
    simp [Valuation.push, liftVal]
  | succ j =>
    simp only [Valuation.push, liftVal]
    by_cases h1 : j < c
    · have h1' : j + 1 < c + 1 := Nat.succ_lt_succ h1
      rw [if_pos h1, if_pos h1']
    · have h1' : ¬ (j + 1 < c + 1) := fun h => h1 (Nat.lt_of_succ_lt_succ h)
      rw [if_neg h1, if_neg h1']
      by_cases h2 : j < c + k
      · have h2' : j + 1 < c + 1 + k := by omega
        rw [if_pos h2, if_pos h2']
      · have h2' : ¬ (j + 1 < c + 1 + k) := by omega
        rw [if_neg h2, if_neg h2']
        cases k with
        | zero => rfl
        | succ k' =>
          have hsub : j + 1 - (k' + 1) = (j - (k' + 1)) + 1 := by omega
          rw [hsub]

theorem insertVal_zero (s : LTShape) (ρ : Valuation) :
    insertVal 0 s ρ = ρ.push s := by
  funext i
  cases i <;> rfl

theorem insertVal_push (k : Nat) (s x : LTShape) (ρ : Valuation) :
    (insertVal k s ρ).push x = insertVal (k + 1) s (ρ.push x) := by
  funext i
  cases i with
  | zero =>
    simp [Valuation.push, insertVal]
  | succ j =>
    simp only [Valuation.push, insertVal]
    by_cases h1 : j < k
    · have h1' : j + 1 < k + 1 := Nat.succ_lt_succ h1
      rw [if_pos h1, if_pos h1']
    · have h1' : ¬ (j + 1 < k + 1) := fun h => h1 (Nat.lt_of_succ_lt_succ h)
      rw [if_neg h1, if_neg h1']
      by_cases h2 : j = k
      · have h2' : j + 1 = k + 1 := congrArg Nat.succ h2
        rw [if_pos h2, if_pos h2']
      · have h2' : j + 1 ≠ k + 1 := fun h => h2 (Nat.succ.inj h)
        rw [if_neg h2, if_neg h2']
        cases j with
        | zero => exact False.elim (by omega)
        | succ j' => rfl

theorem liftVal_insertVal_cancel (k : Nat) (s : LTShape) (ρ : Valuation) (i : Nat) :
    insertVal k s ρ (if k ≤ i then i + 1 else i) = ρ i := by
  by_cases h : k ≤ i
  · rw [if_pos h]
    simp only [insertVal]
    have h1 : ¬ (i + 1 < k) := by omega
    have h2 : i + 1 ≠ k := by omega
    rw [if_neg h1, if_neg h2]
    rfl
  · rw [if_neg h]
    simp only [insertVal]
    have h1 : i < k := by omega
    rw [if_pos h1]

theorem lift_natExpand (c k t : Nat) : lift c k (natExpand t) = natExpand t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [natExpand, litSucc, lift, ih]

theorem instantiate_natExpand (k : Nat) (v : Expr Nat) (t : Nat) :
    instantiate k v (natExpand t) = natExpand t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [natExpand, litSucc, instantiate, ih]

/-- Lifting `e` by `k` above `c` is interpreted under `liftVal c k ρ`. -/
theorem interp_lift_of {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} {e : Expr Nat}
    (H : Interp EI ρ m e) :
    ∀ c k, Interp EI (liftVal c k ρ) m (lift c k e) := by
  induction H with
  | bot => intros; exact .bot
  | @bvar ρ m i h =>
    intro c k
    simp only [lift]
    by_cases hc : c ≤ i
    · rw [if_pos hc]
      refine .bvar ?_
      simp only [liftVal]
      have h1 : ¬ (i + k < c) := by omega
      have h2 : ¬ (i + k < c + k) := by omega
      rw [if_neg h1, if_neg h2, Nat.add_sub_cancel]
      exact h
    · rw [if_neg hc]
      refine .bvar ?_
      simp only [liftVal]
      have h1 : i < c := by omega
      rw [if_pos h1]
      exact h
  | sort h => intros; exact .sort h
  | app _ _ h1 ihf iha =>
    intro c k
    exact .app (ihf c k) (iha c k) h1
  | lam _ hdom _ hm iha ihb =>
    intro c k
    refine .lam (iha c k) hdom (fun x y hxy hxa => ?_) hm
    rw [liftVal_push]
    exact ihb x y hxy hxa (c + 1) k
  | pi _ _ hdom _ hm iha iha' ihb =>
    intro c k
    refine .pi (iha c k) (iha' c k) hdom (fun x y hxy hxa => ?_) hm
    rw [liftVal_push]
    exact ihb x y hxy hxa (c + 1) k
  | letE _ _ ihs ihb =>
    intro c k
    refine .letE (ihs c k) ?_
    rw [liftVal_push]
    exact ihb (c + 1) k
  | const hu hm => intros; exact .const hu hm
  | @lit _ _ t _ ih =>
    intro c k
    exact .lit (lift_natExpand c k t ▸ ih c k)

/-- Specialisation of `interp_lift_of`: `insertVal k s ρ` interprets `lift k 1 v`
whenever `ρ` interprets `v`. -/
theorem interp_lift_insertVal {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m s : LTShape} {v : Expr Nat}
    (H : Interp EI ρ m v) :
    ∀ k, Interp EI (insertVal k s ρ) m (lift k 1 v) := by
  induction H with
  | bot => intros; exact .bot
  | @bvar ρ m i h =>
    intro k
    simp only [lift]
    have hlookup := liftVal_insertVal_cancel k s ρ i
    by_cases hk : k ≤ i
    · rw [if_pos hk]
      rw [if_pos hk] at hlookup
      exact .bvar (hlookup.symm ▸ h)
    · rw [if_neg hk]
      rw [if_neg hk] at hlookup
      exact .bvar (hlookup.symm ▸ h)
  | sort h => intros; exact .sort h
  | app _ _ h1 ihf iha =>
    intro k
    exact .app (ihf k) (iha k) h1
  | lam _ hdom _ hm iha ihb =>
    intro k
    refine .lam (iha k) hdom (fun x y hxy hxa => ?_) hm
    rw [insertVal_push]
    exact ihb x y hxy hxa (k + 1)
  | pi _ _ hdom _ hm iha iha' ihb =>
    intro k
    refine .pi (iha k) (iha' k) hdom (fun x y hxy hxa => ?_) hm
    rw [insertVal_push]
    exact ihb x y hxy hxa (k + 1)
  | letE _ _ ihs ihb =>
    intro k
    refine .letE (ihs k) ?_
    rw [insertVal_push]
    exact ihb (k + 1)
  | const hu hm => intros; exact .const hu hm
  | @lit _ _ t _ ih =>
    intro k
    exact .lit (lift_natExpand k 1 t ▸ ih k)

/-- **Semantic substitution (`Interp` → `instantiate`)**: if `s` approximates `v` under
`ρ` and `m` approximates `b` under `insertVal k s ρ`, then `m` approximates
`instantiate k v b` under `ρ`. -/
theorem interp_instantiate_gen {EI : Nat → List Level → LTShape → Prop}
    {ρ' : Valuation} {m : LTShape} {b : Expr Nat}
    (Hb : Interp EI ρ' m b) :
    ∀ {k : Nat} {s : LTShape} {ρ : Valuation} {v : Expr Nat},
      ρ' = insertVal k s ρ → Interp EI ρ s v →
      Interp EI ρ m (instantiate k v b) := by
  induction Hb with
  | bot => intros; exact .bot
  | @bvar ρ₁ m i h =>
    intro k s ρ v hρ' hv
    subst hρ'
    simp only [instantiate]
    by_cases h1 : i = k
    · rw [if_pos h1]
      have hlt : ¬ (i < k) := by omega
      simp only [insertVal, if_neg hlt, if_pos h1] at h
      exact Interp.mono hv h
    · rw [if_neg h1]
      by_cases h2 : k < i
      · rw [if_pos h2]
        have hlt : ¬ (i < k) := by omega
        simp only [insertVal, if_neg hlt, if_neg h1] at h
        exact .bvar h
      · rw [if_neg h2]
        have hlt : i < k := by omega
        simp only [insertVal, if_pos hlt] at h
        exact .bvar h
  | sort h => intros; exact .sort h
  | app _ _ h1 ihf iha =>
    intro k s ρ v hρ' hv
    exact .app (ihf hρ' hv) (iha hρ' hv) h1
  | @lam ρ₁ _ _ _ _ _ _ _ hdom _ hm iha ihb =>
    intro k s ρ v hρ' hv
    refine .lam (iha hρ' hv) hdom (fun x y hxy hxa => ?_) hm
    have hpush : ρ₁.push ⟨_, x⟩ = insertVal (k + 1) s (ρ.push ⟨_, x⟩) := by
      rw [hρ', insertVal_push]
    have hv' : Interp EI (ρ.push ⟨_, x⟩) s (lift 0 1 v) := by
      rw [← insertVal_zero]
      exact interp_lift_insertVal hv 0
    exact ihb x y hxy hxa hpush hv'
  | @pi ρ₁ _ _ _ _ _ _ _ _ _ hdom _ hm iha iha' ihb =>
    intro k s ρ v hρ' hv
    refine .pi (iha hρ' hv) (iha' hρ' hv) hdom (fun x y hxy hxa => ?_) hm
    have hpush : ρ₁.push ⟨_, x⟩ = insertVal (k + 1) s (ρ.push ⟨_, x⟩) := by
      rw [hρ', insertVal_push]
    have hv' : Interp EI (ρ.push ⟨_, x⟩) s (lift 0 1 v) := by
      rw [← insertVal_zero]
      exact interp_lift_insertVal hv 0
    exact ihb x y hxy hxa hpush hv'
  | @letE ρ₁ _ s₀ _ _ _ _ _ ihs ihb =>
    intro k s ρ v hρ' hv
    refine .letE (ihs hρ' hv) ?_
    have hpush : ρ₁.push s₀ = insertVal (k + 1) s (ρ.push s₀) := by
      rw [hρ', insertVal_push]
    have hv' : Interp EI (ρ.push s₀) s (lift 0 1 v) := by
      rw [← insertVal_zero]
      exact interp_lift_insertVal hv 0
    exact ihb hpush hv'
  | const hu hm => intros; exact .const hu hm
  | @lit _ _ t _ ih =>
    intro k s ρ v hρ' hv
    exact .lit (instantiate_natExpand k v t ▸ ih hρ' hv)

/-- Index-0 semantic substitution: `Interp EI ρ s v` and `Interp EI (ρ.push s) m b`
yield `Interp EI ρ m (instantiate0 v b)`. -/
theorem interp_instantiate_of_bound {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m s : LTShape} {v b : Expr Nat}
    (hv : Interp EI ρ s v) (hb : Interp EI (ρ.push s) m b) :
    Interp EI ρ m (instantiate0 v b) :=
  interp_instantiate_gen hb (insertVal_zero s ρ).symm hv

/-- **Unconditional ζ left-to-right soundness on `RcicModelShape.Interp`:**
every compact lower bound of `.letE A v b` is a lower bound of `instantiate0 v b`. -/
theorem interp_zeta_lhs {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} {A v b : Expr Nat}
    (H : Interp EI ρ m (.letE A v b)) :
    Interp EI ρ m (instantiate0 v b) := by
  cases H with
  | bot => exact .bot
  | letE hs hb => exact interp_instantiate_of_bound hs hb

/-- Inversion of `Interp` on `.lam A body` at `lamT fg`: any entry `(x, y) ∈ fg.1`
produces an entry of the underlying `f` covered by the domain `a₀` whose output bounds
`body` under `ρ.push ⟨n, x'⟩`. -/
theorem interp_lam_appLe {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {f a m : LTShape} {A body arg : Expr Nat}
    (Hlam : Interp EI ρ f (.lam A body))
    (Harg : Interp EI ρ a arg)
    (Happ : AppLe f a m) :
    Interp EI ρ m (instantiate0 arg body) := by
  rcases Happ with ⟨n, fg, x, y, rfl, hxy, hxa, hmy⟩
  cases Hlam with
  | @lam _ _ n' a₀ f₀ _ _ ha₀ hdom hb hle =>
    have hn : n + 1 = n' + 1 := hle.1
    have hn' : n = n' := Nat.succ.inj hn
    subst hn'
    have hfg : DShapeFun.LEP (DShape.LEP eqN) fg.1 f₀.1 := hle.2
    obtain ⟨⟨u, v⟩, huv, hux, hyv⟩ := hfg (x.1, y.1) hxy
    have hwf_f0 : DShapeFun.WF DShape.WF DShape.ble DShape.compat DShape.join f₀.1 :=
      f₀.2.1
    have hwu : DShape.WF u := (hwf_f0.entries (u, v) huv).1
    have hwv : DShape.WF v := (hwf_f0.entries (u, v) huv).2
    let uL : LSh n := ⟨u, hwu⟩
    let vL : LSh n := ⟨v, hwv⟩
    obtain ⟨x', y', hx'y', hx'u, hvy', hx'a₀⟩ :=
      hdom n f₀ uL vL rfl huv
    have hx'x : LeT ⟨n, x'⟩ ⟨n, x⟩ :=
      ⟨rfl, DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hx'u hux⟩
    have hx'arg : Interp EI ρ ⟨n, x'⟩ arg :=
      Interp.mono Harg (LeT.trans hx'x hxa)
    have hbody' : Interp EI (ρ.push ⟨n, x'⟩) ⟨n, y'⟩ body :=
      hb x' y' hx'y' hx'a₀
    have hinst : Interp EI ρ ⟨n, y'⟩ (instantiate0 arg body) :=
      interp_instantiate_of_bound hx'arg hbody'
    have hyy' : LeT ⟨n, y⟩ ⟨n, y'⟩ :=
      ⟨rfl, DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hyv hvy'⟩
    exact Interp.mono hinst (LeT.trans hmy hyy')

/-- **Unconditional β left-to-right soundness on `RcicModelShape.Interp`:**
every compact lower bound of `.app (.lam A body) arg` is a lower bound of
`instantiate0 arg body`. -/
theorem interp_beta_lhs {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} {A body arg : Expr Nat}
    (H : Interp EI ρ m (.app (.lam A body) arg)) :
    Interp EI ρ m (instantiate0 arg body) := by
  cases H with
  | bot => exact .bot
  | app hf ha hap => exact interp_lam_appLe hf ha hap

/-! ## 3. Constructor-by-constructor `SEq` soundness on `RcicModelShape` -/

/-- `ConvT.sorts` is unconditionally sound for `SEq`. -/
theorem seq_sorts {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {l₁ l₂ : Level} (h : eqN l₁ l₂) :
    SEq EI ρ (.sort l₁) (.sort l₂) := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | sort h1 => exact .sort (LeT.trans h1 (sortT_leT_iff.2 h))
  · intro hm
    cases hm with
    | bot => exact .bot
    | sort h2 =>
      have hsymm : eqN l₂ l₁ := fun r => (h r).symm
      exact .sort (LeT.trans h2 (sortT_leT_iff.2 hsymm))

/-- `ConvT.lit` is unconditionally sound for `SEq`. -/
theorem seq_lit {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {t : Nat} {exp : Expr Nat}
    (h : LiteralExpansion t exp) :
    SEq EI ρ (.lit t) exp := by
  cases h with
  | of =>
    intro m
    constructor
    · intro hm
      cases hm with
      | bot => exact .bot
      | lit h1 => exact h1
    · intro hm
      exact .lit hm

/-- `ConvT.app` congruence is unconditionally sound for `SEq`. -/
theorem seq_app {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {f g a b : Expr Nat}
    (hfg : SEq EI ρ f g) (hab : SEq EI ρ a b) :
    SEq EI ρ (.app f a) (.app g b) := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | app hf ha hap => exact .app ((hfg _).1 hf) ((hab _).1 ha) hap
  · intro hm
    cases hm with
    | bot => exact .bot
    | app hg hb hap => exact .app ((hfg _).2 hg) ((hab _).2 hb) hap

/-- `ConvT.lam` congruence is unconditionally sound for `SEq`. -/
theorem seq_lam {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A A' b b' : Expr Nat}
    (hA : SEq EI ρ A A') (hb : ∀ x, SEq EI (ρ.push x) b b') :
    SEq EI ρ (.lam A b) (.lam A' b') := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | lam ha hdom hbody hle =>
      exact .lam ((hA _).1 ha) hdom
        (fun x y hxy hxa => (hb ⟨_, x⟩ ⟨_, y⟩).1 (hbody x y hxy hxa)) hle
  · intro hm
    cases hm with
    | bot => exact .bot
    | lam ha' hdom hbody hle =>
      exact .lam ((hA _).2 ha') hdom
        (fun x y hxy hxa => (hb ⟨_, x⟩ ⟨_, y⟩).2 (hbody x y hxy hxa)) hle

/-- `ConvT.pi` congruence is unconditionally sound for `SEq`. -/
theorem seq_pi {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A A' B B' : Expr Nat}
    (hA : SEq EI ρ A A') (hB : ∀ x, SEq EI (ρ.push x) B B') :
    SEq EI ρ (.pi A B) (.pi A' B') := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | pi ha ha' hdom hbody hle =>
      exact .pi ((hA _).1 ha) ((hA _).1 ha') hdom
        (fun x y hxy hxa => (hB ⟨_, x⟩ ⟨_, y⟩).1 (hbody x y hxy hxa)) hle
  · intro hm
    cases hm with
    | bot => exact .bot
    | pi ha ha' hdom hbody hle =>
      exact .pi ((hA _).2 ha) ((hA _).2 ha') hdom
        (fun x y hxy hxa => (hB ⟨_, x⟩ ⟨_, y⟩).2 (hbody x y hxy hxa)) hle

/-- `ConvT.letE` congruence is unconditionally sound for `SEq`. -/
theorem seq_letE {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A A' v v' b b' : Expr Nat}
    (hv : SEq EI ρ v v') (hb : ∀ s, SEq EI (ρ.push s) b b') :
    SEq EI ρ (.letE A v b) (.letE A' v' b') := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | letE hs hbody => exact .letE ((hv _).1 hs) ((hb _ _).1 hbody)
  · intro hm
    cases hm with
    | bot => exact .bot
    | letE hs hbody => exact .letE ((hv _).2 hs) ((hb _ _).2 hbody)

/-- Contract on `EI` for `ConvT.consts`: level-equivalent lists give the same `EI`. -/
def EIConsts (EI : Nat → List Level → LTShape → Prop) : Prop :=
  ∀ r ls ls' u, eqNList ls ls' → (EI r ls u ↔ EI r ls' u)

/-- `ConvT.consts` is sound for `SEq` under `EIConsts`. -/
theorem seq_consts {EI : Nat → List Level → LTShape → Prop}
    (hEI : EIConsts EI) {ρ : Valuation} {r : Nat} {ls ls' : List Level}
    (h : eqNList ls ls') :
    SEq EI ρ (.const r ls) (.const r ls') := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | const hu hle => exact .const ((hEI r ls ls' _ h).1 hu) hle
  · intro hm
    cases hm with
    | bot => exact .bot
    | const hu hle => exact .const ((hEI r ls ls' _ h).2 hu) hle

/-- Contract on `EI` for `ConvT.delta`: transparent definitions have the same lower
bounds as their level-instantiated bodies. -/
def EIDelta (E : ResolvedEnv) (EI : Nat → List Level → LTShape → Prop) : Prop :=
  ∀ r ls m b, E.members r = some m → m.body = some b →
    transparent m.mclass = true →
    ∀ ρ, SEq EI ρ (.const r ls) (instantiateLevels ls b)

/-! ### Exact named gap statements for the remaining `ConvT` redexes on `RcicModelShape.SEq` -/

/-- Reverse-substitution gap for `ConvT.beta` (since left-to-right `interp_beta_lhs`
holds unconditionally). -/
def BetaRhsGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop :=
  ∀ {Γ A body arg B u},
    HasTyT E n Γ A (.sort u) →
    HasTyT E n (.assumption A :: Γ) body B →
    HasTyT E n Γ arg A →
    ∀ {ρ m}, ValOK Γ ρ →
      Interp EI ρ m (instantiate0 arg body) →
      Interp EI ρ m (.app (.lam A body) arg)

/-- Reverse-substitution gap for `ConvT.zeta` (since left-to-right `interp_zeta_lhs`
holds unconditionally). -/
def ZetaRhsGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop :=
  ∀ {Γ A value body B u},
    HasTyT E n Γ A (.sort u) →
    HasTyT E n Γ value A →
    HasTyT E n (.letBinding A value :: Γ) body B →
    ∀ {ρ m}, ValOK Γ ρ →
      Interp EI ρ m (instantiate0 value body) →
      Interp EI ρ m (.letE A value body)

/-- Named gap for `ConvT.zetaLocal`: admissible valuations interpret let-bound
context variables identically to their stored values. -/
def ZetaLocalSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop :=
  ∀ {Γ i A v},
    lookupValue Γ i = some v →
    lookupType Γ i = some A →
    HasTyT E n Γ v A →
    ∀ {ρ}, ValOK Γ ρ → SEq EI ρ (.bvar i) v

/-- Named gap for `ConvT.iota`: `DerivedIota` steps preserve `SEq` under admissible
valuations. -/
def IotaSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop :=
  ∀ {Γ lhs rhs T},
    DerivedIota E lhs rhs →
    HasTyT E n Γ lhs T →
    HasTyT E n Γ rhs T →
    ∀ {ρ}, ValOK Γ ρ → SEq EI ρ lhs rhs

/-- Named gap for `ConvT.eta`: η-expansion preserves `SEq` under admissible valuations
(refuted at `botT` valuations by `eta_unsound_interp_at_bot` below). -/
def EtaSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop :=
  ∀ {Γ f A B},
    HasTyT E n Γ f (.pi A B) →
    ∀ {ρ}, ValOK Γ ρ → SEq EI ρ (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- Named gap for `ConvT.irr`: proof irrelevance preserves `SEq` under admissible
valuations (refuted on the unquotiented `RcicModelShape.Interp` by `irr_unsound_interp`
below). -/
def IrrSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop :=
  ∀ {Γ P p q},
    HasTyT E n Γ P (.sort .zero) →
    HasTyT E n Γ p P →
    HasTyT E n Γ q P →
    ∀ {ρ}, ValOK Γ ρ → SEq EI ρ p q

/-- Bundle of the `RcicModelShape.SEq` hypotheses needed to run the 18-constructor
Fundamental Lemma over `ConvT E n`. -/
structure SEqModelSupply (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Prop where
  pushAssump : ∀ {Γ A ρ} (x : LTShape), ValOK Γ ρ → ValOK (.assumption A :: Γ) (ρ.push x)
  pushLet : ∀ {Γ A v ρ} (s : LTShape), ValOK Γ ρ → ValOK (.letBinding A v :: Γ) (ρ.push s)
  consts : EIConsts EI
  delta : EIDelta E EI
  betaRhs : BetaRhsGap E n EI ValOK
  zetaRhs : ZetaRhsGap E n EI ValOK
  zetaLocal : ZetaLocalSemGap E n EI ValOK
  iota : IotaSemGap E n EI ValOK
  eta : EtaSemGap E n EI ValOK
  irr : IrrSemGap E n EI ValOK

/-- **18-constructor Fundamental Lemma for `ConvT` on `RcicModelShape.SEq`:**
every `ConvT` constructor is verified against `SEq EI ρ`. -/
theorem fundamental_convT_seq {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    ∀ {ρ : Valuation}, ValOK Γ ρ → SEq EI ρ a b :=
  match h with
  | .refl _ a _ _ => fun _ => SEq.refl a
  | .symm _ _ _ _ h1 => fun hρ => SEq.symm (fundamental_convT_seq M h1 hρ)
  | .trans _ _ _ _ _ h1 h2 =>
      fun hρ => SEq.trans (fundamental_convT_seq M h1 hρ) (fundamental_convT_seq M h2 hρ)
  | .beta _ _ _ _ _ _ hA hbody harg =>
      fun hρ _ => ⟨interp_beta_lhs, M.betaRhs hA hbody harg hρ⟩
  | .zeta _ _ _ _ _ _ hA hv hb =>
      fun hρ _ => ⟨interp_zeta_lhs, M.zetaRhs hA hv hb hρ⟩
  | .zetaLocal _ _ _ _ hval hty hv =>
      fun hρ => M.zetaLocal hval hty hv hρ
  | .delta _ r ls m b hres hbody htr _ _ _ =>
      fun _ => M.delta r ls m b hres hbody htr _
  | .iota _ _ _ _ hiota hlhs hrhs =>
      fun hρ => M.iota hiota hlhs hrhs hρ
  | .lit _ _ _ _ hlit _ =>
      fun _ => seq_lit hlit
  | .app _ _ _ _ _ _ _ h1 h2 =>
      fun hρ => seq_app (fundamental_convT_seq M h1 hρ) (fundamental_convT_seq M h2 hρ)
  | .lam _ _ _ _ _ _ _ hA hb =>
      fun hρ => seq_lam (fundamental_convT_seq M hA hρ)
        (fun x => fundamental_convT_seq M hb (M.pushAssump x hρ))
  | .pi _ _ _ _ _ _ _ hA hB =>
      fun hρ => seq_pi (fundamental_convT_seq M hA hρ)
        (fun x => fundamental_convT_seq M hB (M.pushAssump x hρ))
  | .letE _ _ _ _ _ _ _ _ _ _ hv hb =>
      fun hρ => seq_letE (fundamental_convT_seq M hv hρ)
        (fun s => fundamental_convT_seq M hb (M.pushLet s hρ))
  | .sorts _ _ _ heq =>
      fun _ => seq_sorts heq
  | .consts _ _ _ _ _ _ _ _ _ heq =>
      fun _ => seq_consts M.consts heq
  | .eta _ _ _ _ hf =>
      fun hρ => M.eta hf hρ
  | .irr _ _ _ _ hP hp hq =>
      fun hρ => M.irr hP hp hq hρ
  | .tyConv _ _ _ _ _ _ h1 _ =>
      fun hρ => fundamental_convT_seq M h1 hρ

/-- **Fundamental Lemma for `TyConvT` on `RcicModelShape.SEq`**. -/
theorem fundamental_tyConvT_seq {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    {Γ : LCtx} {A B : Expr Nat}
    (h : TyConvT E n Γ A B) :
    ∀ {ρ : Valuation}, ValOK Γ ρ → SEq EI ρ A B :=
  match h with
  | .refl _ A => fun _ => SEq.refl A
  | .of _ _ _ _ hc => fun hρ => fundamental_convT_seq M hc hρ
  | .trans _ _ _ _ h1 h2 =>
      fun hρ => SEq.trans (fundamental_tyConvT_seq M h1 hρ) (fundamental_tyConvT_seq M h2 hρ)

/-- From `SEqModelSupply` and an inhabited `ValOK Γ ρ`, `TyConvT (.sort u) (.sort v)`
yields `eqN u v` (`TypedRowsWf.sortRow`). -/
theorem sortRow_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    {Γ : LCtx} {ρ : Valuation} (hρ : ValOK Γ ρ)
    {u v : Level} (h : TyConvT E n Γ (.sort u) (.sort v)) :
    eqN u v :=
  seq_sort_inv (fundamental_tyConvT_seq M h hρ)

/-- From `SEqModelSupply`, `TyConvT (.pi A B) (.pi A' B')` yields `SEq EI ρ A A'`
(semantic Π-domain injectivity). -/
theorem piDomSEq_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    {Γ : LCtx} {ρ : Valuation} (hρ : ValOK Γ ρ)
    {A B A' B' : Expr Nat} (h : TyConvT E n Γ (.pi A B) (.pi A' B')) :
    SEq EI ρ A A' :=
  seq_pi_dom_inv (fundamental_tyConvT_seq M h hρ)

/-- From `SEqModelSupply`, `.pi A B` and `.sort u` are never `TyConvT`-convertible. -/
theorem not_tyConvT_pi_sort_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    {Γ : LCtx} {ρ : Valuation} (hρ : ValOK Γ ρ)
    {A B : Expr Nat} {u : Level}
    (h : TyConvT E n Γ (.pi A B) (.sort u)) : False :=
  not_seq_pi_sort (fundamental_tyConvT_seq M h hρ)

/-! ## 4. Admitted Obstructions on `RcicModelShape` and arXiv 2607.13662's WHRed LR -/

/-! ### Obstruction 1: `ConvT.eta` is unsound on `RcicModelShape.Interp` at `botT` valuations -/

/-- Context `[f : Π (_ : Sort 0), Sort 0]` for the η-obstruction fixture. -/
def etaObsCtx : LCtx :=
  [.assumption (.pi (.sort .zero) (.sort .zero))]

/-- `etaObsCtx` is `CtxWfT` in `emptyEnv`. -/
def etaObsCtx_wf (n : Nat) : CtxWfT emptyEnv n etaObsCtx :=
  .assumption [] _ _ .nil
    (.pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
      (.sort [] .zero) (.sort _ .zero))

/-- `.bvar 0 : Π (_ : Sort 0), Sort 0` in `etaObsCtx`. -/
def etaObsF_ty (n : Nat) :
    HasTyT emptyEnv n etaObsCtx (.bvar 0) (.pi (.sort .zero) (.sort .zero)) :=
  .bvar _ 0 _ rfl

/-- The `ConvT.eta` instance in `emptyEnv` at `etaObsCtx`:
`(λ x : Sort 0. f x) ≡ f` at `Π (_ : Sort 0), Sort 0`. -/
def etaObs_convT (n : Nat) :
    ConvT emptyEnv n etaObsCtx
      (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))
      (.bvar 0)
      (.pi (.sort .zero) (.sort .zero)) :=
  .eta etaObsCtx (.bvar 0) (.sort .zero) (.sort .zero) (etaObsF_ty n)

/-- **Admitted Obstruction 1 (`eta_unsound_interp_at_bot`):**
In `Rcic.Domain.Model.Interp`, for any `EI` and any valuation `ρ` that interprets free
variable `0` as `botT k` (including `k = 0` and `k = 1`, the paper's ⊥-variable
valuation), the `ConvT.eta` conversion `etaObs_convT` is **unsound** for `SEq EI ρ`:
`lamT (botWFun 0)` approximates `.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))`
while `¬ Interp EI ρ (lamT (botWFun 0)) (.bvar 0)`. -/
theorem eta_unsound_interp_at_bot
    (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (k : Nat) (hρ : ρ 0 = botT k) :
    Interp EI ρ (lamT (botWFun 0)) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) ∧
      ¬ Interp EI ρ (lamT (botWFun 0)) (.bvar 0) ∧
      ¬ SEq EI ρ (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) (.bvar 0) := by
  have hlhs : Interp EI ρ (lamT (botWFun 0))
      (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) :=
    interp_lam_botWFun .bot
  have hrhs : ¬ Interp EI ρ (lamT (botWFun 0)) (.bvar 0) := by
    intro h
    rcases Interp.le_bvar h with ⟨m, hbot⟩ | hle
    · exact not_lamT_eq_botT hbot
    · rw [hρ] at hle
      exact not_leT_lamT_botT hle
  exact ⟨hlhs, hrhs, fun hseq => hrhs ((hseq (lamT (botWFun 0))).1 hlhs)⟩

/-! ### Obstruction 2: `ConvT.irr` is unsound on `RcicModelShape.Interp` -/

/-- Context `[x : P, P : Sort 0]` for the proof-irrelevance obstruction fixture. -/
def irrObsCtx : LCtx :=
  [.assumption (.bvar 0), .assumption (.sort .zero)]

/-- `irrObsCtx` is `CtxWfT` in `emptyEnv`. -/
def irrObsCtx_wf (n : Nat) : CtxWfT emptyEnv n irrObsCtx :=
  .assumption [.assumption (.sort .zero)] (.bvar 0) .zero
    (.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero))
    (.bvar _ 0 _ rfl)

/-- Constant proof function `λ (y : P). x` in `irrObsCtx`. -/
def irrConstX : Expr Nat := .lam (.bvar 1) (.bvar 1)

/-- Identity proof function `λ (y : P). y` in `irrObsCtx`. -/
def irrIdP : Expr Nat := .lam (.bvar 1) (.bvar 0)

/-- The proposition `P → P` (`Π (_ : P), P`) in `irrObsCtx`. -/
def irrPropPP : Expr Nat := .pi (.bvar 1) (.bvar 2)

private theorem eqN_imax00_0 : eqN (.imax .zero .zero) .zero := fun _ => rfl
private theorem eqN_succ_imax00_1 :
    eqN (.succ (.imax .zero .zero)) (.succ .zero) := fun _ => rfl

/-- `irrPropPP : Sort 0` in `irrObsCtx`. -/
def irrPropPP_ty (n : Nat) :
    HasTyT emptyEnv n irrObsCtx irrPropPP (.sort .zero) :=
  .conv _ _ _ _ (.succ .zero)
    (.pi _ (.bvar 1) .zero (.bvar 2) .zero
      (.bvar _ 1 _ rfl)
      (.bvar _ 2 _ rfl))
    (.tyConv _ _ _ _ _ _
      (.sorts _ _ _ eqN_imax00_0)
      (.sorts _ _ _ eqN_succ_imax00_1))

/-- `irrConstX : P → P` in `irrObsCtx`. -/
def irrConstX_ty (n : Nat) :
    HasTyT emptyEnv n irrObsCtx irrConstX irrPropPP :=
  .lam _ (.bvar 1) .zero (.bvar 1) (.bvar 2)
    (.bvar _ 1 _ rfl)
    (.bvar _ 1 _ rfl)

/-- `irrIdP : P → P` in `irrObsCtx`. -/
def irrIdP_ty (n : Nat) :
    HasTyT emptyEnv n irrObsCtx irrIdP irrPropPP :=
  .lam _ (.bvar 1) .zero (.bvar 0) (.bvar 2)
    (.bvar _ 1 _ rfl)
    (.bvar _ 0 _ rfl)

/-- `ConvT.irr` directly equates `irrConstX` (`λ y. x`) and `irrIdP` (`λ y. y`) at
`irrPropPP : Sort 0` in `emptyEnv`. -/
def irrObs_convT (n : Nat) :
    ConvT emptyEnv n irrObsCtx irrConstX irrIdP irrPropPP :=
  .irr irrObsCtx irrPropPP irrConstX irrIdP
    (irrPropPP_ty n) (irrConstX_ty n) (irrIdP_ty n)

/-- Well-formedness of the constant step-function graph `[(⊥, sort 0)]` at level 1. -/
theorem wf_constSort0WFun :
    DShape.WF (α := Level) (n := 1) (.lam [(DShape0.bot, DShape0.sort .zero)]) :=
  wf_constSortWFun .zero

/-- The constant step-function graph `[(⊥, sort 0)] : WFun 0`. -/
abbrev constSort0WFun : WFun 0 := constSortWFun .zero

theorem hasDomP_constSort0WFun (a : LSh 0) :
    HasDomP (lamT constSort0WFun) ⟨0, a⟩ :=
  hasDomP_constSortWFun .zero a

/-- **Admitted Obstruction 2 (`irr_unsound_interp`):**
In `Rcic.Domain.Model.Interp`, for any `EI` and any valuation `ρ` with
`ρ 0 = sortT .zero`, the `ConvT.irr` conversion `irrObs_convT` between
`irrConstX` (`λ y : P. x`) and `irrIdP` (`λ y : P. y`) is **unsound** for `SEq EI ρ`:
`lamT constSort0WFun` approximates `irrConstX` while `¬ Interp EI ρ (lamT constSort0WFun) irrIdP`. -/
theorem irr_unsound_interp
    (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (hρ : ρ 0 = sortT .zero) :
    Interp EI ρ (lamT constSort0WFun) irrConstX ∧
      ¬ Interp EI ρ (lamT constSort0WFun) irrIdP ∧
      ¬ SEq EI ρ irrConstX irrIdP := by
  have hlhs : Interp EI ρ (lamT constSort0WFun) irrConstX := by
    refine .lam .bot (hasDomP_constSort0WFun WShape.bot) ?_ (LeT.refl _)
    intro x y hxy _
    have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
    have hy' : (⟨0, y⟩ : LTShape) = sortT .zero :=
      congrArg (Sigma.mk 0) (Subtype.ext hxy'.2)
    rw [hy']
    refine .bvar ?_
    simp [Valuation.push, hρ, LeT.refl]
  have hrhs : ¬ Interp EI ρ (lamT constSort0WFun) irrIdP := by
    intro h
    generalize hm : lamT constSort0WFun = m at h
    cases h with
    | bot =>
      exact not_lamT_eq_botT hm
    | @lam _ _ n' a f _ _ _ hdom hb hle =>
      rw [← hm] at hle
      have hn : 1 = n' + 1 := hle.1
      have hn' : 0 = n' := Nat.succ.inj hn
      subst hn'
      have hfg : DShapeFun.LEP (DShape.LEP eqN) constSort0WFun.1 f.1 := hle.2
      obtain ⟨⟨u, v⟩, huv, hbotu, hsortv⟩ :=
        hfg (DShape0.bot, DShape0.sort .zero) (List.mem_singleton_self _)
      have hwu : DShape.WF u := (f.2.1.entries (u, v) huv).1
      have hwv : DShape.WF v := (f.2.1.entries (u, v) huv).2
      obtain ⟨x', y', hx'y', hx'u, hvy', hx'a⟩ :=
        hdom 0 f ⟨u, hwu⟩ ⟨v, hwv⟩ rfl huv
      have hu_eq : u = DShape0.bot := DShape0.LEP.le_bot hbotu
      have hx'_eq : x'.1 = DShape0.bot := DShape0.LEP.le_bot (hu_eq ▸ hx'u)
      have hbody : Interp EI (ρ.push ⟨0, x'⟩) ⟨0, y'⟩ (.bvar 0) :=
        hb x' y' hx'y' hx'a
      have hsort_y' : LeT (sortT .zero) ⟨0, y'⟩ :=
        ⟨rfl, DShape0.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hsortv hvy'⟩
      have hsort_bvar : Interp EI (ρ.push ⟨0, x'⟩) (sortT .zero) (.bvar 0) :=
        Interp.mono hbody hsort_y'
      rcases Interp.le_bvar hsort_bvar with ⟨k, hbot⟩ | hle_x'
      · exact not_sortT_eq_botT hbot
      · have hle0 : DShape0.LEP eqN (DShape0.sort .zero) x'.1 := hle_x'.2
        rw [hx'_eq] at hle0
        exact hle0
  exact ⟨hlhs, hrhs, fun hseq => hrhs ((hseq (lamT constSort0WFun)).1 hlhs)⟩

/-! ### Obstruction 3: arXiv 2607.13662's WHRed-based LR Π-clause is refuted at `andEnvU` -/

/-- Reflexive-transitive closure of deterministic weak-head reduction `HeadStepT`. -/
inductive HeadStepTStar (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop where
  | refl (a : Expr Nat) : HeadStepTStar E n Γ a a
  | step {a b c T : Expr Nat} :
      HeadStepT E n Γ a b T → HeadStepTStar E n Γ b c →
      HeadStepTStar E n Γ a c

/-- `mixAndCtx` is a well-formed local context (`CtxWfT`) in `andEnvU`. -/
def mixAndCtx_wf : CtxWfT andEnvU 0 mixAndCtx := by
  let Γ4 : LCtx :=
    [.assumption (.bvar 1), .assumption (.bvar 1),
     .assumption (.sort .zero), .assumption (.sort .zero)]
  have h1 : CtxWfT andEnvU 0 [.assumption (.sort .zero)] :=
    .assumption [] (.sort .zero) (.succ .zero) .nil (.sort _ .zero)
  have h2 : CtxWfT andEnvU 0 [.assumption (.sort .zero), .assumption (.sort .zero)] :=
    .assumption _ (.sort .zero) (.succ .zero) h1 (.sort _ .zero)
  have h3 : CtxWfT andEnvU 0
      [.assumption (.bvar 1), .assumption (.sort .zero), .assumption (.sort .zero)] :=
    .assumption _ (.bvar 1) .zero h2 (.bvar _ 1 _ rfl)
  have h4 : CtxWfT andEnvU 0 Γ4 :=
    .assumption _ (.bvar 1) .zero h3 (.bvar _ 1 _ rfl)
  have hand : HasTyT andEnvU 0 Γ4 (.const 0 [])
      (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero))) :=
    .const _ 0 [] andFamMember rfl rfl rfl
  have ha : HasTyT andEnvU 0 Γ4 (.bvar 3) (.sort .zero) := .bvar _ 3 _ rfl
  have hb : HasTyT andEnvU 0 Γ4 (.bvar 2) (.sort .zero) := .bvar _ 2 _ rfl
  have handA : HasTyT andEnvU 0 Γ4 (.app (.const 0 []) (.bvar 3))
      (.pi (.sort .zero) (.sort .zero)) :=
    .app _ _ _ _ _ hand ha
  have handAB : HasTyT andEnvU 0 Γ4 (andApp (.bvar 3) (.bvar 2)) (.sort .zero) :=
    .app _ _ _ _ _ handA hb
  exact .assumption _ (andApp (.bvar 3) (.bvar 2)) .zero h4 handAB

/-- Every `HeadStepTStar` reduct of `mixAndRedex` in `andEnvU` is `mixAndRedex` itself. -/
theorem mixAndRedex_headStepTStar_eq {n : Nat} {c : Expr Nat}
    (h : HeadStepTStar andEnvU n mixAndCtx mixAndRedex c) :
    c = mixAndRedex := by
  cases h with
  | refl => rfl
  | step hstep _ => exact False.elim (mixAnd_headStepT_none hstep)

/-- `mixAndRedex` never weak-head reduces via `HeadStepTStar` to any `.pi A B`. -/
theorem mixAndRedex_not_headStepTStar_pi {n : Nat} {A B : Expr Nat} :
    ¬ HeadStepTStar andEnvU n mixAndCtx mixAndRedex (.pi A B) := by
  intro h
  have heq := mixAndRedex_headStepTStar_eq h
  exact nomatch heq

/-- The paper's (arXiv 2607.13662 §2.6, Fig. 4) weak-head-reduction Π-clause at the
base Π-compact `piT ⊥ [(⊥, ⊥)]`: two convertible types at a Π-compact must weak-head
reduce via `HeadStepTStar` to syntactic `.pi` types with convertible domains and
codomains. -/
def WhredPiClause (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T₁ T₂ : Expr Nat) : Prop :=
  ∃ A₁ B₁ A₂ B₂,
    HeadStepTStar E n Γ T₁ (.pi A₁ B₁) ∧
    HeadStepTStar E n Γ T₂ (.pi A₂ B₂) ∧
    Nonempty (TyConvT E n Γ A₁ A₂) ∧
    Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)

/-- **Admitted Obstruction 3 (`whredPiClause_refuted_at_andEnvU`):**
At the admitted `EnvWfT` environment `andEnvU` and `CtxWfT` context `mixAndCtx`,
`mixPi = Π (_ : Sort 0), Sort 0` and
`mixAndRedex = And.rec a b (λ_. Sort 1) (λ x y. Sort 0 → Sort 0) h` are `ConvT`-convertible
at `Sort (imax 1 1)` and `piT ⊥ (botWFun 0)` is a lower bound of `mixPi` in `Interp`
under every `EI` and `ρ`, yet `WhredPiClause andEnvU 0 mixAndCtx mixPi mixAndRedex`
is **FALSE** because `mixAndRedex` is stuck for `HeadStepT`. -/
theorem whredPiClause_refuted_at_andEnvU :
    Nonempty (EnvWfT andEnvU) ∧
      Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
      Nonempty (ConvT andEnvU 0 mixAndCtx mixPi mixAndRedex
        (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
      (∀ EI ρ, Interp EI ρ (piT (WShape.bot : LSh 0) (botWFun 0)) mixPi) ∧
      ¬ WhredPiClause andEnvU 0 mixAndCtx mixPi mixAndRedex := by
  refine ⟨⟨andEnvUWfT⟩, ⟨mixAndCtx_wf⟩, ?_, ?_, ?_⟩
  · obtain ⟨h⟩ := mixAnd_conv
    exact ⟨.symm _ _ _ _ h⟩
  · intro EI ρ
    exact interp_pi_botWFun .bot
  · rintro ⟨A₁, B₁, A₂, B₂, _, hred2, _, _⟩
    exact mixAndRedex_not_headStepTStar_pi hred2

/-! ## 5. Named Hypothesis Bundle (`SemanticPiModel`) at Least as Strong as `PiInjType` -/

/-- `Type`-valued Π-injectivity of `TyConvT` (`PiInj E n`). -/
def PiInjType (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat},
    TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) →
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂

/-- `PiInjType E n` directly supplies `PiRowField E n` (`TypedRowsWf.piRow`). -/
theorem piRowField_of_piInjType {E : ResolvedEnv} {n : Nat}
    (h : PiInjType E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hty
  obtain ⟨hA, hB⟩ := h hΓ hty
  exact ⟨⟨hA⟩, ⟨hB⟩⟩

/-- **Named open hypothesis bundle (`SemanticPiModel E n`) at least as strong as `PiInjType E n`:**
packages an abstract relation `RelConv : LCtx → Expr Nat → Expr Nat → Type` with one
assumed soundness field per `ConvT` constructor (`refl_arm` .. `irr_arm`, so `RelConv ⊇ ConvT`)
together with `piReadback` assuming Π-injectivity on `RelConv`. Because `piReadback`
assumes injectivity on a relation at least as large as `TyConvT`, this structure is a
named hypothesis at least as strong as `PiInjType E n`, not a standalone reduction of `PiInjType`. -/
structure SemanticPiModel (E : ResolvedEnv) (n : Nat) : Type 1 where
  RelConv : LCtx → Expr Nat → Expr Nat → Type
  refl_arm : ∀ {Γ a A}, HasTyT E n Γ a A → RelConv Γ a a
  symm_arm : ∀ {Γ a b}, RelConv Γ a b → RelConv Γ b a
  trans_arm : ∀ {Γ a b c}, RelConv Γ a b → RelConv Γ b c → RelConv Γ a c
  beta_arm : ∀ {Γ A body arg B u},
    HasTyT E n Γ A (.sort u) →
    HasTyT E n (.assumption A :: Γ) body B →
    HasTyT E n Γ arg A →
    RelConv Γ (.app (.lam A body) arg) (instantiate0 arg body)
  zeta_arm : ∀ {Γ A value body B u},
    HasTyT E n Γ A (.sort u) →
    HasTyT E n Γ value A →
    HasTyT E n (.letBinding A value :: Γ) body B →
    RelConv Γ (.letE A value body) (instantiate0 value body)
  zetaLocal_arm : ∀ {Γ i A v},
    lookupValue Γ i = some v →
    lookupType Γ i = some A →
    HasTyT E n Γ v A →
    RelConv Γ (.bvar i) v
  delta_arm : ∀ {Γ r ls m b},
    E.members r = some m →
    m.body = some b →
    transparent m.mclass = true →
    ls.length = m.arity →
    levelsBounded n ls = true →
    HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) →
    RelConv Γ (.const r ls) (instantiateLevels ls b)
  iota_arm : ∀ {Γ lhs rhs T},
    DerivedIota E lhs rhs →
    HasTyT E n Γ lhs T →
    HasTyT E n Γ rhs T →
    RelConv Γ lhs rhs
  lit_arm : ∀ {Γ t exp T},
    LiteralExpansion t exp →
    HasTyT E n Γ exp T →
    RelConv Γ (.lit t) exp
  app_arm : ∀ {Γ f g a b},
    RelConv Γ f g → RelConv Γ a b → RelConv Γ (.app f a) (.app g b)
  lam_arm : ∀ {Γ A A' b b'},
    RelConv Γ A A' →
    RelConv (.assumption A :: Γ) b b' →
    RelConv Γ (.lam A b) (.lam A' b')
  pi_arm : ∀ {Γ A A' B B'},
    RelConv Γ A A' →
    RelConv (.assumption A :: Γ) B B' →
    RelConv Γ (.pi A B) (.pi A' B')
  letE_arm : ∀ {Γ A A' v v' b b'},
    RelConv Γ A A' →
    RelConv Γ v v' →
    RelConv (.letBinding A v :: Γ) b b' →
    RelConv Γ (.letE A v b) (.letE A' v' b')
  sorts_arm : ∀ {Γ l₁ l₂}, eqN l₁ l₂ → RelConv Γ (.sort l₁) (.sort l₂)
  consts_arm : ∀ {Γ r ls ls' m},
    E.members r = some m →
    ls.length = m.arity →
    levelsBounded n ls = true →
    levelsBounded n ls' = true →
    eqNList ls ls' →
    RelConv Γ (.const r ls) (.const r ls')
  eta_arm : ∀ {Γ f A B},
    HasTyT E n Γ f (.pi A B) →
    RelConv Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f
  irr_arm : ∀ {Γ P p q},
    HasTyT E n Γ P (.sort .zero) →
    HasTyT E n Γ p P →
    HasTyT E n Γ q P →
    RelConv Γ p q
  piReadback : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat},
    RelConv Γ (.pi A₁ B₁) (.pi A₂ B₂) →
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂

/-- **Constructor-wise fold for `ConvT` over the assumed arms of `SemanticPiModel E n`**
(not a semantic fundamental lemma: each `ConvT` constructor is answered directly by the
assumed record field of the same name). -/
def fundamental_convT {E : ResolvedEnv} {n : Nat}
    (M : SemanticPiModel E n) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) : M.RelConv Γ a b :=
  match h with
  | .refl _ _ _ ha => M.refl_arm ha
  | .symm _ _ _ _ h1 => M.symm_arm (fundamental_convT M h1)
  | .trans _ _ _ _ _ h1 h2 =>
      M.trans_arm (fundamental_convT M h1) (fundamental_convT M h2)
  | .beta _ _ _ _ _ _ hA hbody harg => M.beta_arm hA hbody harg
  | .zeta _ _ _ _ _ _ hA hv hb => M.zeta_arm hA hv hb
  | .zetaLocal _ _ _ _ hval hty hv => M.zetaLocal_arm hval hty hv
  | .delta _ _ _ _ _ hres hbody htr hlen hwf hb =>
      M.delta_arm hres hbody htr hlen hwf hb
  | .iota _ _ _ _ hiota hlhs hrhs => M.iota_arm hiota hlhs hrhs
  | .lit _ _ _ _ hlit hexp => M.lit_arm hlit hexp
  | .app _ _ _ _ _ _ _ h1 h2 =>
      M.app_arm (fundamental_convT M h1) (fundamental_convT M h2)
  | .lam _ _ _ _ _ _ _ hA hb =>
      M.lam_arm (fundamental_convT M hA) (fundamental_convT M hb)
  | .pi _ _ _ _ _ _ _ hA hB =>
      M.pi_arm (fundamental_convT M hA) (fundamental_convT M hB)
  | .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      M.letE_arm (fundamental_convT M hA) (fundamental_convT M hv) (fundamental_convT M hb)
  | .sorts _ _ _ heq => M.sorts_arm heq
  | .consts _ _ _ _ _ hres hlen hwf hwf' heq =>
      M.consts_arm hres hlen hwf hwf' heq
  | .eta _ _ _ _ hf => M.eta_arm hf
  | .irr _ _ _ _ hP hp hq => M.irr_arm hP hp hq
  | .tyConv _ _ _ _ _ _ h1 _ => fundamental_convT M h1

/-- Reflexive-transitive closure of `M.RelConv`, interpreting `TyConvT E n` without
requiring a typing derivation at `.refl`. -/
inductive RelTyChain {E : ResolvedEnv} {n : Nat} (M : SemanticPiModel E n)
    (Γ : LCtx) : Expr Nat → Expr Nat → Type where
  | refl (A : Expr Nat) : RelTyChain M Γ A A
  | step {A B C : Expr Nat} : M.RelConv Γ A B → RelTyChain M Γ B C → RelTyChain M Γ A C

/-- Appending two `RelTyChain` derivations. -/
def RelTyChain.append {E : ResolvedEnv} {n : Nat} {M : SemanticPiModel E n}
    {Γ : LCtx} {A B C : Expr Nat}
    (h1 : RelTyChain M Γ A B) (h2 : RelTyChain M Γ B C) :
    RelTyChain M Γ A C :=
  match h1 with
  | .refl _ => h2
  | .step hab hbc => .step hab (hbc.append h2)

/-- Collapsing a non-empty `RelTyChain` into a single `M.RelConv`. -/
def RelTyChain.collapse {E : ResolvedEnv} {n : Nat} {M : SemanticPiModel E n}
    {Γ : LCtx} {A B C : Expr Nat}
    (hab : M.RelConv Γ A B) (hbc : RelTyChain M Γ B C) :
    M.RelConv Γ A C :=
  match hbc with
  | .refl _ => hab
  | .step h1 h2 => M.trans_arm hab (RelTyChain.collapse h1 h2)

/-- Π-inversion readback on `RelTyChain`: a `.refl` chain injects `.pi` syntactically,
and a `.step` chain collapses via `RelTyChain.collapse` and reads back via `M.piReadback`. -/
def RelTyChain.piInv {E : ResolvedEnv} {n : Nat} {M : SemanticPiModel E n}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y A₁ B₁ A₂ B₂ : Expr Nat}
    (h : RelTyChain M Γ X Y)
    (hX : X = .pi A₁ B₁) (hY : Y = .pi A₂ B₂) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ := by
  cases h with
  | refl _ =>
    have hpi : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ := hX.symm.trans hY
    injection hpi with hA hB
    subst hA; subst hB
    exact ⟨.refl Γ A₁, .refl (.assumption A₁ :: Γ) B₁⟩
  | step hab hbc =>
    subst hX; subst hY
    exact M.piReadback hΓ (RelTyChain.collapse hab hbc)

/-- **Constructor-wise fold for `TyConvT` into `RelTyChain M`**. -/
def fundamental_tyConvT {E : ResolvedEnv} {n : Nat}
    (M : SemanticPiModel E n) {Γ : LCtx} {A B : Expr Nat}
    (h : TyConvT E n Γ A B) : RelTyChain M Γ A B :=
  match h with
  | .refl _ A => .refl A
  | .of _ _ _ _ hc => .step (fundamental_convT M hc) (.refl _)
  | .trans _ _ _ _ h1 h2 =>
      (fundamental_tyConvT M h1).append (fundamental_tyConvT M h2)

/-- **`PiInjType E n` extracted from `SemanticPiModel E n` (`piReadback ∘ fold`)**:
a pure `.refl` chain returns `(.refl, .refl)` directly, and any chain with at least
one conversion step collapses via `M.trans_arm` and applies the assumed `M.piReadback`. -/
def piInjType_of_semanticPiModel {E : ResolvedEnv} {n : Nat}
    (M : SemanticPiModel E n) : PiInjType E n :=
  fun {_} hΓ {_ _ _ _} hty => (fundamental_tyConvT M hty).piInv hΓ rfl rfl

/-- **`PiRowField E n` extracted from `SemanticPiModel E n` (`piReadback ∘ fold`)**. -/
theorem piRowField_of_semanticPiModel {E : ResolvedEnv} {n : Nat}
    (M : SemanticPiModel E n) : PiRowField E n :=
  piRowField_of_piInjType (piInjType_of_semanticPiModel M)

/-! ## 6. Two-Way Semantic Weakening, Concrete `ZetaLocal` Discharge, Conditional `η`/`irr`
Lemmas, and the `SEqModelSupply` → `SemanticPiModel` Bridge -/

/-! ### 6.1 Two-way semantic weakening (`interp_lift_insertVal_iff`, `interp_lift0_one_iff`) -/

/-- Inverse of `interp_lift_insertVal`: if `m` approximates `lift k 1 v` under
`insertVal k s ρ`, then `m` approximates `v` under `ρ`. -/
theorem interp_lift_insertVal_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ' : Valuation} {m : LTShape} {e : Expr Nat}
    (H : Interp EI ρ' m e) :
    ∀ {k : Nat} {s : LTShape} {ρ : Valuation} {v : Expr Nat},
      ρ' = insertVal k s ρ → e = lift k 1 v →
      Interp EI ρ m v := by
  induction H with
  | bot => intros; exact .bot
  | @bvar ρ₁ m i h =>
    intro k s ρ v hρ' he
    subst hρ'
    cases v with
    | bvar j =>
      simp only [lift] at he
      have hij : i = (if k ≤ j then j + 1 else j) := by
        by_cases hkj : k ≤ j
        · rw [if_pos hkj] at he ⊢; injection he
        · rw [if_neg hkj] at he ⊢; injection he
      rw [hij, liftVal_insertVal_cancel k s ρ j] at h
      exact .bvar h
    | sort _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp [lift] at he
  | @sort _ m u h =>
    intro k s ρ v _ he
    cases v with
    | sort u' =>
      simp only [lift] at he
      injection he with hu
      subst hu
      exact .sort h
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp [lift] at he
  | @app _ m f a F A _ _ h1 ihf iha =>
    intro k s ρ v hρ' he
    cases v with
    | app F₀ A₀ =>
      simp only [lift] at he
      injection he with hF hA
      exact .app (ihf hρ' hF) (iha hρ' hA) h1
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp [lift] at he
  | @lam ρ₁ m n a f A F _ hdom _ hm iha ihb =>
    intro k s ρ v hρ' he
    cases v with
    | lam A₀ F₀ =>
      simp only [lift] at he
      injection he with hA hF
      refine .lam (iha hρ' hA) hdom (fun x y hxy hxa => ?_) hm
      have hpush : ρ₁.push ⟨n, x⟩ = insertVal (k + 1) s (ρ.push ⟨n, x⟩) := by
        rw [hρ', insertVal_push]
      exact ihb x y hxy hxa hpush hF
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | sort _ | const _ _ | app _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp [lift] at he
  | @pi ρ₁ m n a a' f A B _ _ hdom _ hm iha iha' ihb =>
    intro k s ρ v hρ' he
    cases v with
    | pi A₀ B₀ =>
      simp only [lift] at he
      injection he with hA hB
      refine .pi (iha hρ' hA) (iha' hρ' hA) hdom (fun x y hxy hxa => ?_) hm
      have hpush : ρ₁.push ⟨n, x⟩ = insertVal (k + 1) s (ρ.push ⟨n, x⟩) := by
        rw [hρ', insertVal_push]
      exact ihb x y hxy hxa hpush hB
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
      simp [lift] at he
  | @letE ρ₁ m s₀ A val b _ _ ihs ihb =>
    intro k s ρ v hρ' he
    cases v with
    | letE A₀ val₀ b₀ =>
      simp only [lift] at he
      injection he with _ hval hb
      refine .letE (ihs hρ' hval) ?_
      have hpush : ρ₁.push s₀ = insertVal (k + 1) s (ρ.push s₀) := by
        rw [hρ', insertVal_push]
      exact ihb hpush hb
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | sort _ | const _ _ | app _ _ | lam _ _ | pi _ _ | lit _ =>
      simp [lift] at he
  | @const _ m u r ls hu hm =>
    intro k s ρ v _ he
    cases v with
    | const r' ls' =>
      simp only [lift] at he
      injection he with hr hls
      subst hr; subst hls
      exact .const hu hm
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp [lift] at he
  | @lit _ m t _ ih =>
    intro k s ρ v hρ' he
    cases v with
    | lit t' =>
      simp only [lift] at he
      injection he with ht
      subst ht
      exact .lit (ih hρ' (lift_natExpand k 1 t).symm)
    | bvar _ => simp [lift] at he; split at he <;> simp at he
    | sort _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ =>
      simp [lift] at he

/-- **Two-way semantic weakening (`insertVal` ↔ `lift k 1`):**
`m` approximates `lift k 1 v` under `insertVal k s ρ` iff `m` approximates `v` under `ρ`. -/
theorem interp_lift_insertVal_iff {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m s : LTShape} {v : Expr Nat} (k : Nat) :
    Interp EI (insertVal k s ρ) m (lift k 1 v) ↔ Interp EI ρ m v :=
  ⟨fun h => interp_lift_insertVal_inv h rfl rfl, fun h => interp_lift_insertVal h k⟩

/-- **Under-binder semantic weakening (`ρ.push s` ↔ `lift 0 1`):**
`m` approximates `lift 0 1 v` under `ρ.push s` iff `m` approximates `v` under `ρ`. -/
theorem interp_lift0_one_iff {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m s : LTShape} {v : Expr Nat} :
    Interp EI (ρ.push s) m (lift 0 1 v) ↔ Interp EI ρ m v := by
  rw [← insertVal_zero s ρ]
  exact interp_lift_insertVal_iff 0

/-- **Under-binder `SEq` weakening (`ρ.push s` ↔ `lift 0 1`):**
`lift 0 1 u` and `lift 0 1 v` are `SEq`-equivalent under `ρ.push s` iff `u` and `v`
are `SEq`-equivalent under `ρ`. -/
theorem seq_lift0_one_iff {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {s : LTShape} {u v : Expr Nat} :
    SEq EI (ρ.push s) (lift 0 1 u) (lift 0 1 v) ↔ SEq EI ρ u v := by
  constructor
  · intro h m
    exact (interp_lift0_one_iff (s := s)).symm.trans
      ((h m).trans interp_lift0_one_iff)
  · intro h m
    exact interp_lift0_one_iff.trans ((h m).trans interp_lift0_one_iff.symm)

/-! ### 6.2 Concrete `ZetaLocalSemGap` discharge via `ZetaValOK` -/

/-- `lookupValue` at index `0` on an assumption head is `none`. -/
theorem lookupValue_cons_assumption_zero (A : Expr Nat) (Γ : LCtx) :
    lookupValue (.assumption A :: Γ) 0 = none := rfl

/-- `lookupValue` at index `0` on a let-binding head is `some (lift 0 1 v)`. -/
theorem lookupValue_cons_letBinding_zero (A v : Expr Nat) (Γ : LCtx) :
    lookupValue (.letBinding A v :: Γ) 0 = some (lift 0 1 v) := rfl

/-- `lookupValue` at successor index `j + 1` lifts `lookupValue Γ j` by `lift 0 1`. -/
theorem lookupValue_cons_succ (d : LocalDecl) (Γ : LCtx) (j : Nat) :
    lookupValue (d :: Γ) (j + 1) = (lookupValue Γ j).map (lift 0 1) := by
  unfold lookupValue
  show (match Γ.get? j with
    | some (.letBinding _ v) => some (lift 0 (j + 1 + 1) v)
    | _ => none) =
    (match Γ.get? j with
    | some (.letBinding _ v) => some (lift 0 (j + 1) v)
    | _ => none).map (lift 0 1)
  cases Γ.get? j with
  | none => rfl
  | some decl =>
    cases decl with
    | assumption _ => rfl
    | letBinding _ v =>
      simp only [Option.map, lift_shift_comp_idx 0 (j + 1) v]

/-- Concrete valuation-admissibility predicate for `ConvT.zetaLocal`: every let-bound
variable in `Γ` is `SEq`-equivalent to its lifted value under `ρ`. -/
def ZetaValOK (EI : Nat → List Level → LTShape → Prop)
    (Γ : LCtx) (ρ : Valuation) : Prop :=
  ∀ i v, lookupValue Γ i = some v → SEq EI ρ (.bvar i) v

/-- `ZetaValOK` holds unconditionally on the empty context `[]` for every valuation `ρ`. -/
theorem zetaValOK_nil (EI : Nat → List Level → LTShape → Prop) (ρ : Valuation) :
    ZetaValOK EI [] ρ := by
  intro i _ h
  cases i <;> exact Option.noConfusion h

/-- Pushing an `.assumption A` preserves `ZetaValOK` under `ρ.push x` for **every**
compact shape `x : LTShape` (using `lookupValue_cons_succ` and `seq_lift0_one_iff`). -/
theorem zetaValOK_push_assumption {EI : Nat → List Level → LTShape → Prop}
    {Γ : LCtx} {ρ : Valuation} (A : Expr Nat) (x : LTShape)
    (hρ : ZetaValOK EI Γ ρ) :
    ZetaValOK EI (.assumption A :: Γ) (ρ.push x) := by
  intro i v h
  cases i with
  | zero => exact Option.noConfusion h
  | succ j =>
    rw [lookupValue_cons_succ] at h
    cases hlookup : lookupValue Γ j with
    | none =>
      rw [hlookup] at h
      exact Option.noConfusion h
    | some v₀ =>
      rw [hlookup, Option.map] at h
      injection h with hv
      subst hv
      have hlift : (Expr.bvar (j + 1) : Expr Nat) = lift 0 1 (.bvar j) := by
        simp [lift]
      rw [hlift]
      exact (seq_lift0_one_iff (s := x)).2 (hρ j v₀ hlookup)

/-- Pushing a `.letBinding A v₀` preserves `ZetaValOK` under `ρ.push s` whenever `s`
has the same lower bounds as `v₀` under `ρ`. -/
theorem zetaValOK_push_letBinding {EI : Nat → List Level → LTShape → Prop}
    {Γ : LCtx} {ρ : Valuation} (A v₀ : Expr Nat) (s : LTShape)
    (hρ : ZetaValOK EI Γ ρ)
    (hs : ∀ m, Interp EI (ρ.push s) m (.bvar 0) ↔ Interp EI ρ m v₀) :
    ZetaValOK EI (.letBinding A v₀ :: Γ) (ρ.push s) := by
  intro i v h
  cases i with
  | zero =>
    injection h with hv
    subst hv
    intro m
    exact (hs m).trans interp_lift0_one_iff.symm
  | succ j =>
    rw [lookupValue_cons_succ] at h
    cases hlookup : lookupValue Γ j with
    | none =>
      rw [hlookup] at h
      exact Option.noConfusion h
    | some w =>
      rw [hlookup, Option.map] at h
      injection h with hv
      subst hv
      have hlift : (Expr.bvar (j + 1) : Expr Nat) = lift 0 1 (.bvar j) := by
        simp [lift]
      rw [hlift]
      exact (seq_lift0_one_iff (s := s)).2 (hρ j w hlookup)

/-- `ZetaValOK EI` unconditionally discharges `ZetaLocalSemGap E n EI (ZetaValOK EI)`. -/
theorem zetaLocalSemGap_of_zetaValOK (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop) :
    ZetaLocalSemGap E n EI (ZetaValOK EI) := by
  intro Γ i A v hval _ _ ρ hρ
  exact hρ i v hval

/-! ### 6.3 Positive η-calculus on `RcicModelShape.Interp` (pairing with Obstruction 1) -/

/-- Any graph entry `(x.1, y.1) ∈ g.1` of `g : WFun n` witnesses `AppLe (lamT g) ⟨n, x⟩ ⟨n, y⟩`. -/
theorem appLe_of_mem_graph {n : Nat} (g : WFun n) (x y : LSh n)
    (hxy : (x.1, y.1) ∈ g.1) :
    AppLe (lamT g) ⟨n, x⟩ ⟨n, y⟩ :=
  ⟨n, g, x, y, rfl, hxy, LeT.refl ⟨n, x⟩, LeT.refl ⟨n, y⟩⟩

/-- **Unconditional η RHS-to-LHS step-function lemma:**
if `⟨n, a⟩` approximates `A`, `lamT g` has domain covered by `⟨n, a⟩`, and `lamT g`
approximates `f`, then every `m ≤ lamT g` approximates `.lam A (.app (lift 0 1 f) (.bvar 0))`. -/
theorem interp_eta_rhs_lam {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {n : Nat} {a : LSh n} {g : WFun n} {m : LTShape}
    {A f : Expr Nat}
    (hA : Interp EI ρ ⟨n, a⟩ A)
    (hdom : HasDomP (lamT g) ⟨n, a⟩)
    (hf : Interp EI ρ (lamT g) f)
    (hm : LeT m (lamT g)) :
    Interp EI ρ m (.lam A (.app (lift 0 1 f) (.bvar 0))) :=
  .lam hA hdom
    (fun x y hxy _ =>
      .app (interp_lift0_one_iff.2 hf)
        (.bvar (LeT.refl ⟨n, x⟩))
        (appLe_of_mem_graph g x y hxy))
    hm

/-- **Unconditional inversion of `.app (lift 0 1 f) (.bvar 0)` under `ρ.push ⟨n, x⟩`:**
every compact output `⟨n, y⟩` either is `WShape.bot` or is covered by an entry
`(x₀, y₀) ∈ fg.1` of some `lamT fg` lower bound of `f` under `ρ` with `x₀ ≤ x` and
`y ≤ y₀`. -/
theorem interp_app_lift0_bvar0_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {n : Nat} {x y : LSh n} {f : Expr Nat}
    (h : Interp EI (ρ.push ⟨n, x⟩) ⟨n, y⟩ (.app (lift 0 1 f) (.bvar 0))) :
    y = WShape.bot ∨
      ∃ (fg : WFun n) (x₀ y₀ : LSh n),
        Interp EI ρ (lamT fg) f ∧
        (x₀.1, y₀.1) ∈ fg.1 ∧
        DShape.LEP eqN x₀.1 x.1 ∧
        DShape.LEP eqN y.1 y₀.1 := by
  generalize hm : (⟨n, y⟩ : LTShape) = m at h
  cases h with
  | bot =>
    have hnn : n = _ := congrArg Sigma.fst hm
    subst hnn
    have hy : y = WShape.bot := by
      injection hm with _ h2
    exact .inl hy
  | @app _ _ fn arg _ _ hfn harg happ =>
    rcases happ with ⟨k, fg, x₀, y₀, rfl, hxy₀, hx₀arg, hmy₀⟩
    rw [← hm] at hmy₀
    have hnk : n = k := hmy₀.1
    subst hnk
    have hyy₀ : DShape.LEP eqN y.1 y₀.1 := hmy₀.2
    have hf : Interp EI ρ (lamT fg) f := interp_lift0_one_iff.1 hfn
    have hx₀x : DShape.LEP eqN x₀.1 x.1 := by
      rcases Interp.le_bvar harg with ⟨j, hbot⟩ | hle
      · rw [hbot] at hx₀arg
        have hnj : n = j := hx₀arg.1
        subst hnj
        exact (LeT.trans hx₀arg (LeT.bot_le ⟨n, x⟩)).2
      · exact (LeT.trans hx₀arg hle).2
    exact .inr ⟨fg, x₀, y₀, hf, hxy₀, hx₀x, hyy₀⟩

/-- `f` has the bottom step-function graph `[(⊥, ⊥)]` at every level `n` in its
`Interp EI ρ` denotation (the exact property refuted at `ρ 0 = botT k` in
Obstruction 1 `eta_unsound_interp_at_bot`). -/
def EtaFloor (EI : Nat → List Level → LTShape → Prop) (ρ : Valuation)
    (f : Expr Nat) : Prop :=
  ∀ n : Nat, Interp EI ρ (lamT (botWFun n)) f

/-- `f`'s step-function lower bounds at each level `n` in `Interp EI ρ` are directed
under `LeT`. -/
def LamDirected (EI : Nat → List Level → LTShape → Prop) (ρ : Valuation)
    (f : Expr Nat) : Prop :=
  ∀ {n : Nat} (g₁ g₂ : WFun n),
    Interp EI ρ (lamT g₁) f → Interp EI ρ (lamT g₂) f →
    ∃ g : WFun n, Interp EI ρ (lamT g) f ∧
      LeT (lamT g₁) (lamT g) ∧ LeT (lamT g₂) (lamT g)

private theorem exists_lamT_le_of_entries {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {f : Expr Nat}
    (hfloor : EtaFloor EI ρ f) (hdir : LamDirected EI ρ f)
    {n : Nat} (es : List (DShape Level n × DShape Level n))
    (hes : ∀ p ∈ es, ∃ fg : WFun n, Interp EI ρ (lamT fg) f ∧
      ∃ q ∈ fg.1, DShape.LEP eqN q.1 p.1 ∧ DShape.LEP eqN p.2 q.2) :
    ∃ fg : WFun n, Interp EI ρ (lamT fg) f ∧
      DShapeFun.LEP (DShape.LEP eqN) es fg.1 := by
  induction es with
  | nil =>
    exact ⟨botWFun n, hfloor n, fun _ hp => nomatch hp⟩
  | cons p tail ih =>
    obtain ⟨g₁, hg₁, q₁, hq₁, hq₁p, hpq₁⟩ := hes p (.head _)
    obtain ⟨g₂, hg₂, htail⟩ := ih (fun x hx => hes x (.tail _ hx))
    obtain ⟨g, hg, hle₁, hle₂⟩ := hdir g₁ g₂ hg₁ hg₂
    have hlep₁ : DShapeFun.LEP (DShape.LEP eqN) g₁.1 g.1 := lamT_leT_iff.1 hle₁
    have hlep₂ : DShapeFun.LEP (DShape.LEP eqN) g₂.1 g.1 := lamT_leT_iff.1 hle₂
    refine ⟨g, hg, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hmem
    · obtain ⟨q, hq, hqq₁, hq₁q⟩ := hlep₁ q₁ hq₁
      exact ⟨q, hq,
        DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hqq₁ hq₁p,
        DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hpq₁ hq₁q⟩
    · obtain ⟨q₂, hq₂, hq₂x, hxq₂⟩ := htail x hmem
      obtain ⟨q, hq, hqq₂, hq₂q⟩ := hlep₂ q₂ hq₂
      exact ⟨q, hq,
        DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hqq₂ hq₂x,
        DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hxq₂ hq₂q⟩

/-- **Positive η LHS-to-RHS soundness on `RcicModelShape.Interp`:**
under `EtaFloor EI ρ f` and `LamDirected EI ρ f`, every compact lower bound of
`.lam A (.app (lift 0 1 f) (.bvar 0))` is a lower bound of `f`. -/
theorem interp_eta_lhs_of_floor_directed {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A f : Expr Nat}
    (hfloor : EtaFloor EI ρ f) (hdir : LamDirected EI ρ f)
    {m : LTShape} (h : Interp EI ρ m (.lam A (.app (lift 0 1 f) (.bvar 0)))) :
    Interp EI ρ m f := by
  cases h with
  | bot => exact .bot
  | @lam _ _ n a g _ _ _ hdom hb hm =>
    have hentries : ∀ p ∈ g.1, ∃ fg : WFun n, Interp EI ρ (lamT fg) f ∧
        ∃ q ∈ fg.1, DShape.LEP eqN q.1 p.1 ∧ DShape.LEP eqN p.2 q.2 := by
      intro p hp
      let x : LSh n := ⟨p.1, (g.2.1.entries p hp).1⟩
      let y : LSh n := ⟨p.2, (g.2.1.entries p hp).2⟩
      obtain ⟨x', y', hx'y', hx'x, hyy', hx'a⟩ := hdom n g x y rfl hp
      have hbody : Interp EI (ρ.push ⟨n, x'⟩) ⟨n, y'⟩ (.app (lift 0 1 f) (.bvar 0)) :=
        hb x' y' hx'y' hx'a
      rcases interp_app_lift0_bvar0_inv hbody with hy' | ⟨fg, x₀, y₀, hfg, hxy₀, hx₀x', hy'y₀⟩
      · refine ⟨botWFun n, hfloor n, (DShape.bot, DShape.bot),
          List.mem_singleton_self _, DShape.LEP.bot p.1, ?_⟩
        have hy'_eq : y'.1 = DShape.bot := congrArg Subtype.val hy'
        rw [← hy'_eq]
        exact hyy'
      · refine ⟨fg, hfg, (x₀.1, y₀.1), hxy₀,
          DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hx₀x' hx'x,
          DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hyy' hy'y₀⟩
    obtain ⟨fg, hfg, hlep⟩ := exists_lamT_le_of_entries hfloor hdir g.1 hentries
    exact Interp.mono hfg (LeT.trans hm (lamT_leT_iff.2 hlep))

/-- Every non-bottom compact lower bound `m` of `f` in `Interp EI ρ` is bounded by some
step-function code `lamT g` of `f` whose domain is covered by some `a` in `⟦A⟧_ρ`. -/
def LamDomCovered (EI : Nat → List Level → LTShape → Prop) (ρ : Valuation)
    (A f : Expr Nat) : Prop :=
  ∀ m : LTShape, Interp EI ρ m f →
    (∃ k, m = botT k) ∨
      ∃ (n : Nat) (a : LSh n) (g : WFun n),
        Interp EI ρ ⟨n, a⟩ A ∧
        HasDomP (lamT g) ⟨n, a⟩ ∧
        Interp EI ρ (lamT g) f ∧
        LeT m (lamT g)

/-- **Positive η RHS-to-LHS soundness on `RcicModelShape.Interp`:**
under `LamDomCovered EI ρ A f`, every compact lower bound of `f` is a lower bound of
its η-expansion `.lam A (.app (lift 0 1 f) (.bvar 0))`. -/
theorem interp_eta_rhs_of_domCovered {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A f : Expr Nat}
    (hcov : LamDomCovered EI ρ A f)
    {m : LTShape} (hf : Interp EI ρ m f) :
    Interp EI ρ m (.lam A (.app (lift 0 1 f) (.bvar 0))) := by
  rcases hcov m hf with ⟨k, rfl⟩ | ⟨n, a, g, hA, hdom, hfg, hm⟩
  · exact .bot
  · exact interp_eta_rhs_lam hA hdom hfg hm

/-- **Positive `SEq` soundness of `ConvT.eta` under `EtaFloor`, `LamDirected`, and
`LamDomCovered`** (the exact semantic conditions repairing Obstruction 1). -/
theorem seq_eta_of_etaReady {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {A f : Expr Nat}
    (hfloor : EtaFloor EI ρ f)
    (hdir : LamDirected EI ρ f)
    (hcov : LamDomCovered EI ρ A f) :
    SEq EI ρ (.lam A (.app (lift 0 1 f) (.bvar 0))) f :=
  fun _ => ⟨interp_eta_lhs_of_floor_directed hfloor hdir,
            interp_eta_rhs_of_domCovered hcov⟩

/-! ### 6.4 Positive proof-irrelevance (`ConvT.irr`) collapse (pairing with Obstruction 2) -/

/-- A term `e` is semantically collapsed to bottom under `(EI, ρ)` if its only compact
lower bounds in `Interp EI ρ` are the level-indexed bottom codes `botT k`. -/
def BotOnly (EI : Nat → List Level → LTShape → Prop) (ρ : Valuation)
    (e : Expr Nat) : Prop :=
  ∀ m : LTShape, Interp EI ρ m e → ∃ k, m = botT k

/-- Any two `BotOnly` terms are `SEq`-equivalent (proof irrelevance for bottom-collapsed
terms). -/
theorem seq_of_botOnly {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {p q : Expr Nat}
    (hp : BotOnly EI ρ p) (hq : BotOnly EI ρ q) :
    SEq EI ρ p q := by
  intro m
  constructor
  · intro hm
    obtain ⟨k, rfl⟩ := hp m hm
    exact .bot
  · intro hm
    obtain ⟨k, rfl⟩ := hq m hm
    exact .bot

/-- Under any valuation `ρ` that collapses `x : P` (`ρ 0 = botT k₀`), every lower bound
of `irrConstX` (`λ y : P. x`) from Obstruction 2 is either `botT k` or bounded by
`lamT (botWFun n)`. -/
theorem interp_irrConstX_le_botWFun {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {k₀ : Nat} (hρ0 : ρ 0 = botT k₀)
    {m : LTShape} (H : Interp EI ρ m irrConstX) :
    (∃ k, m = botT k) ∨ ∃ n, LeT m (lamT (botWFun n)) := by
  cases H with
  | bot => exact .inl ⟨_, rfl⟩
  | @lam _ _ n a f _ _ _ hdom hb hm =>
    refine .inr ⟨n, LeT.trans hm (lamT_leT_iff.2 ?_)⟩
    intro p hp
    let x : LSh n := ⟨p.1, (f.2.1.entries p hp).1⟩
    let y : LSh n := ⟨p.2, (f.2.1.entries p hp).2⟩
    obtain ⟨x', y', hx'y', _, hyy', hx'a⟩ := hdom n f x y rfl hp
    have hbody : Interp EI (ρ.push ⟨n, x'⟩) ⟨n, y'⟩ (.bvar 1) := hb x' y' hx'y' hx'a
    have hy'_bot : DShape.LEP eqN y'.1 DShape.bot := by
      rcases Interp.le_bvar hbody with ⟨j, hbot⟩ | hle
      · have hle' : LeT ⟨n, y'⟩ (botT j) := hbot ▸ LeT.refl ⟨n, y'⟩
        have hnj : n = j := hle'.1
        subst hnj
        exact hle'.2
      · simp only [Valuation.push, hρ0] at hle
        have hnk : n = k₀ := hle.1
        subst hnk
        exact hle.2
    refine ⟨(DShape.bot, DShape.bot), List.mem_singleton_self _, DShape.LEP.bot p.1, ?_⟩
    exact DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hyy' hy'_bot

/-- Under any valuation `ρ` that collapses `P` (`ρ 1 = botT k₁`), every lower bound
of `irrIdP` (`λ y : P. y`) from Obstruction 2 is either `botT k` or bounded by
`lamT (botWFun n)`. -/
theorem interp_irrIdP_le_botWFun {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {k₁ : Nat} (hρ1 : ρ 1 = botT k₁)
    {m : LTShape} (H : Interp EI ρ m irrIdP) :
    (∃ k, m = botT k) ∨ ∃ n, LeT m (lamT (botWFun n)) := by
  cases H with
  | bot => exact .inl ⟨_, rfl⟩
  | @lam _ _ n a f _ _ ha hdom hb hm =>
    have ha_bot : DShape.LEP eqN a.1 DShape.bot := by
      rcases Interp.le_bvar ha with ⟨j, hbot⟩ | hle
      · have hle' : LeT ⟨n, a⟩ (botT j) := hbot ▸ LeT.refl ⟨n, a⟩
        have hnj : n = j := hle'.1
        subst hnj
        exact hle'.2
      · rw [hρ1] at hle
        have hnk : n = k₁ := hle.1
        subst hnk
        exact hle.2
    refine .inr ⟨n, LeT.trans hm (lamT_leT_iff.2 ?_)⟩
    intro p hp
    let x : LSh n := ⟨p.1, (f.2.1.entries p hp).1⟩
    let y : LSh n := ⟨p.2, (f.2.1.entries p hp).2⟩
    obtain ⟨x', y', hx'y', _, hyy', hx'a⟩ := hdom n f x y rfl hp
    have hx'_bot : DShape.LEP eqN x'.1 DShape.bot :=
      DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hx'a.2 ha_bot
    have hbody : Interp EI (ρ.push ⟨n, x'⟩) ⟨n, y'⟩ (.bvar 0) := hb x' y' hx'y' hx'a
    have hy'_bot : DShape.LEP eqN y'.1 DShape.bot := by
      rcases Interp.le_bvar hbody with ⟨j, hbot⟩ | hle
      · have hle' : LeT ⟨n, y'⟩ (botT j) := hbot ▸ LeT.refl ⟨n, y'⟩
        have hnj : n = j := hle'.1
        subst hnj
        exact hle'.2
      · exact DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hle.2 hx'_bot
    refine ⟨(DShape.bot, DShape.bot), List.mem_singleton_self _, DShape.LEP.bot p.1, ?_⟩
    exact DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hyy' hy'_bot

/-- **Positive repair of Obstruction 2 (`seq_irrObs_at_bot`):**
whereas `irr_unsound_interp` refutes `SEq EI ρ irrConstX irrIdP` when `ρ 0 = sortT 0`,
under any bottom-collapsed valuation (`ρ 0 = botT k₀`, `ρ 1 = botT k₁`, in particular
`botVal`) the two proof functions `irrConstX` (`λ y : P. x`) and `irrIdP` (`λ y : P. y`)
ARE `SEq`-equivalent. -/
theorem seq_irrObs_at_bot (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) {k₀ k₁ : Nat} (hρ0 : ρ 0 = botT k₀) (hρ1 : ρ 1 = botT k₁) :
    SEq EI ρ irrConstX irrIdP := by
  intro m
  constructor
  · intro hm
    rcases interp_irrConstX_le_botWFun hρ0 hm with ⟨k, rfl⟩ | ⟨n, hle⟩
    · exact .bot
    · exact Interp.mono (interp_lam_botWFun .bot) hle
  · intro hm
    rcases interp_irrIdP_le_botWFun hρ1 hm with ⟨k, rfl⟩ | ⟨n, hle⟩
    · exact .bot
    · exact Interp.mono (interp_lam_botWFun .bot) hle

/-! ### 6.5 Bridge from `SEqModelSupply` (Section 3) to `SemanticPiModel` (Section 5) -/

/-- Context-indexed semantic equivalence over `ValOK`: `a` and `b` have the same
lower bounds in `Interp EI ρ` for every `ValOK Γ ρ`. -/
def SEqVal (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop)
    (Γ : LCtx) (a b : Expr Nat) : Prop :=
  ∀ {ρ : Valuation}, ValOK Γ ρ → SEq EI ρ a b

/-- `SEqVal` inherits unconditional semantic Π-domain injectivity (`seq_pi_dom_inv`). -/
theorem seqVal_pi_dom_inv {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : SEqVal EI ValOK Γ (.pi A₁ B₁) (.pi A₂ B₂)) :
    SEqVal EI ValOK Γ A₁ A₂ :=
  fun hρ => seq_pi_dom_inv (h hρ)

/-- Readback interface from `SEqVal` on `.pi A₁ B₁` and `.pi A₂ B₂` (together with the
already-extracted semantic domain equivalence `SEqVal EI ValOK Γ A₁ A₂`) to syntactic
`TyConvT` component conversions. -/
def SEqPiReadbackGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (ValOK : LCtx → Valuation → Prop) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat},
    SEqVal EI ValOK Γ (.pi A₁ B₁) (.pi A₂ B₂) →
    SEqVal EI ValOK Γ A₁ A₂ →
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂

/-- **Bridge from `SEqModelSupply` + `SEqPiReadbackGap` to `SemanticPiModel E n`
(vacuous on raw `RcicModelShape.Interp`):**
by Section 7 (`valOK_empty_of_seqModel`, `tyConvT_total_of_seqModel`), `M.betaRhs` and
`M.zetaRhs` force `∀ Γ ρ, ¬ ValOK Γ ρ` on raw `Interp`, making `SEqVal EI ValOK` the
total relation (`seqVal_total_of_seqModel`) and forcing `R` to return `TyConvT` between
any two expressions. -/
def semanticPiModel_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    (R : SEqPiReadbackGap E n EI ValOK) :
    SemanticPiModel E n where
  RelConv Γ a b := PLift (SEqVal EI ValOK Γ a b)
  refl_arm _ := .up (fun _ => SEq.refl _)
  symm_arm h := .up (fun hρ => SEq.symm (h.down hρ))
  trans_arm h1 h2 := .up (fun hρ => SEq.trans (h1.down hρ) (h2.down hρ))
  beta_arm hA hbody harg :=
    .up (fun hρ _ => ⟨interp_beta_lhs, M.betaRhs hA hbody harg hρ⟩)
  zeta_arm hA hv hb :=
    .up (fun hρ _ => ⟨interp_zeta_lhs, M.zetaRhs hA hv hb hρ⟩)
  zetaLocal_arm hval hty hv :=
    .up (fun hρ => M.zetaLocal hval hty hv hρ)
  delta_arm hres hbody htr _ _ _ :=
    .up (fun _ => M.delta _ _ _ _ hres hbody htr _)
  iota_arm hiota hlhs hrhs :=
    .up (fun hρ => M.iota hiota hlhs hrhs hρ)
  lit_arm hlit _ :=
    .up (fun _ => seq_lit hlit)
  app_arm h1 h2 :=
    .up (fun hρ => seq_app (h1.down hρ) (h2.down hρ))
  lam_arm hA hb :=
    .up (fun hρ => seq_lam (hA.down hρ) (fun x => hb.down (M.pushAssump x hρ)))
  pi_arm hA hB :=
    .up (fun hρ => seq_pi (hA.down hρ) (fun x => hB.down (M.pushAssump x hρ)))
  letE_arm _ hv hb :=
    .up (fun hρ => seq_letE (hv.down hρ) (fun s => hb.down (M.pushLet s hρ)))
  sorts_arm heq :=
    .up (fun _ => seq_sorts heq)
  consts_arm _ _ _ _ heq :=
    .up (fun _ => seq_consts M.consts heq)
  eta_arm hf :=
    .up (fun hρ => M.eta hf hρ)
  irr_arm hP hp hq :=
    .up (fun hρ => M.irr hP hp hq hρ)
  piReadback := fun {_} hΓ {_ _ _ _} h => R hΓ h.down (seqVal_pi_dom_inv h.down)

/-- **`PiInjType E n` from `SEqModelSupply` and `SEqPiReadbackGap` (vacuous on raw `Interp`;
see `valOK_empty_of_seqModel` and `tyConvT_total_of_seqModel`)**. -/
def piInjType_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    (R : SEqPiReadbackGap E n EI ValOK) :
    PiInjType E n :=
  piInjType_of_semanticPiModel (semanticPiModel_of_seqModel M R)

/-- **`PiRowField E n` from `SEqModelSupply` and `SEqPiReadbackGap` (vacuous on raw `Interp`;
see `valOK_empty_of_seqModel` and `tyConvT_total_of_seqModel`)**. -/
theorem piRowField_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    (R : SEqPiReadbackGap E n EI ValOK) :
    PiRowField E n :=
  piRowField_of_semanticPiModel (semanticPiModel_of_seqModel M R)

/-! ### 6.6 `insertVal` monotonicity and unconditional `SEq` soundness of ζ/β redexes -/

/-- `insertVal` is monotone in the inserted compact shape `s`. -/
theorem insertVal_leP {k : Nat} {s₁ s₂ : LTShape} (h : LeT s₁ s₂) (ρ : Valuation) :
    (insertVal k s₁ ρ).LeP (insertVal k s₂ ρ) := by
  intro i
  simp only [insertVal]
  split
  · exact LeT.refl _
  · split
    · exact h
    · exact LeT.refl _

/-- `Interp` is monotone in the shape inserted by `insertVal`. -/
theorem interp_insertVal_mono {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {k : Nat} {s₁ s₂ m : LTShape} {b : Expr Nat}
    (h : LeT s₁ s₂) (Hb : Interp EI (insertVal k s₁ ρ) m b) :
    Interp EI (insertVal k s₂ ρ) m b :=
  Interp.mono_l Hb (insertVal_leP h ρ)

/-- **Unconditional `SEq` soundness of identity ζ-reduction** (`let x : A := v in x ≡ v`). -/
theorem seq_zeta_bvar0 {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} (A v : Expr Nat) :
    SEq EI ρ (.letE A v (.bvar 0)) v := by
  intro m
  constructor
  · intro hm
    exact interp_zeta_lhs hm
  · intro hm
    exact .letE hm (.bvar (LeT.refl m))

/-- **Unconditional `SEq` soundness of vacuous ζ-reduction**
(`let x : A := v in lift 0 1 e ≡ e`). -/
theorem seq_zeta_vacuous {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} (A v e : Expr Nat) :
    SEq EI ρ (.letE A v (lift 0 1 e)) e := by
  intro m
  constructor
  · intro hm
    cases hm with
    | bot => exact .bot
    | letE _ hb => exact interp_lift0_one_iff.1 hb
  · intro hm
    exact .letE (s := botT 0) .bot (interp_lift0_one_iff.2 hm)

/-- **Unconditional RHS-to-LHS β-introduction at `sortT u` for vacuous λ-abstractions:**
if `sortT u` approximates `e` under `ρ`, then `sortT u` approximates
`.app (.lam A (lift 0 1 e)) arg` for any `A` and `arg`. -/
theorem interp_beta_rhs_constSortWFun {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {u : Level} {A e arg : Expr Nat}
    (he : Interp EI ρ (sortT u) e) :
    Interp EI ρ (sortT u) (.app (.lam A (lift 0 1 e)) arg) := by
  have hlam : Interp EI ρ (lamT (constSortWFun u)) (.lam A (lift 0 1 e)) := by
    refine .lam .bot (hasDomP_constSortWFun u WShape.bot) ?_ (LeT.refl _)
    intro x y hxy _
    have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
    have hy' : (⟨0, y⟩ : LTShape) = sortT u :=
      congrArg (Sigma.mk 0) (Subtype.ext hxy'.2)
    rw [hy']
    exact interp_lift0_one_iff.2 he
  exact .app hlam (a := botT 0) .bot
    (appLe_of_mem_graph (constSortWFun u) WShape.bot ⟨.sort u, trivial⟩
      (List.mem_singleton_self _))

/-- **Unconditional `SEq` soundness of vacuous sort β-reduction**
(`(λ _ : A. Sort u) arg ≡ Sort u`). -/
theorem seq_beta_vacuous_sort {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} (A arg : Expr Nat) (u : Level) :
    SEq EI ρ (.app (.lam A (.sort u)) arg) (.sort u) := by
  intro m
  constructor
  · intro hm
    exact interp_beta_lhs hm
  · intro hm
    cases hm with
    | bot => exact .bot
    | sort hle =>
      have hsort : Interp EI ρ (sortT u) (.app (.lam A (lift 0 1 (.sort u))) arg) :=
        interp_beta_rhs_constSortWFun Interp.sort'
      exact Interp.mono hsort hle

/-! ## 7. Admitted Obstruction 4 (Refutation of `BetaRhsGap` and `ZetaRhsGap`),
    Reverse-Substitution Factorization (`SubstFactorizes`), and `eqNList`-Saturation -/

/-! ### 7.1 Admitted Obstruction 4a: Linear `ConvT.beta` is unsound on `RcicModelShape.Interp` -/

/-- Disjointness of `.pi` and `.lam` lower bounds in `RcicModelShape.Interp`:
any compact shape `s` that simultaneously approximates `.pi A B` and `.lam C D`
must be a bottom shape `botT k`. -/
theorem interp_pi_and_lam_eq_botT {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {s : LTShape} {A B C D : Expr Nat}
    (hpi : Interp EI ρ s (.pi A B))
    (hlam : Interp EI ρ s (.lam C D)) :
    ∃ k : Nat, s = botT k := by
  cases hpi with
  | bot => exact ⟨_, rfl⟩
  | @pi _ s n₁ a₁ _ f₁ _ _ _ _ _ _ hle_pi =>
    cases hlam with
    | bot => exact ⟨_, rfl⟩
    | @lam _ _ n₂ _ f₂ _ _ _ _ _ hle_lam =>
      rcases s with ⟨k, w, hw⟩
      obtain ⟨hk₁, hpi_w⟩ := hle_pi
      cases hk₁
      obtain ⟨hk₂, hlam_w⟩ := hle_lam
      have hn₁₂ : n₁ = n₂ := Nat.succ.inj hk₂
      cases hn₁₂
      change DShapeS.LEP eqN (DShape.LEP eqN) w (.pi a₁.1 f₁.1) at hpi_w
      change DShapeS.LEP eqN (DShape.LEP eqN) w (.lam f₂.1) at hlam_w
      refine ⟨n₁ + 1, congrArg (Sigma.mk (n₁ + 1)) (Subtype.ext ?_)⟩
      cases w <;> first
        | rfl
        | exact False.elim hpi_w
        | exact False.elim hlam_w

/-- **Structural erasure of Π-annotated β-redexes on `RcicModelShape.Interp`:**
because `Interp.lam` restricts step-function inputs to lower bounds of the domain
annotation `.pi D C` (`piT`), while `.lam D' b` only has `lamT` lower bounds,
every compact lower bound `m` of `.app (.lam (.pi D C) body) (.lam D' b)` comes from
evaluating `body` at `ρ.push (botT n)` (with the argument erased to `botT n`). -/
theorem interp_app_lam_pi_lam_inv {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} {D C body D' b : Expr Nat}
    (H : Interp EI ρ m (.app (.lam (.pi D C) body) (.lam D' b))) :
    ∃ n : Nat, Interp EI (ρ.push (botT n)) m body := by
  cases H with
  | bot => exact ⟨0, .bot⟩
  | app hf ha happ =>
    rcases happ with ⟨n, fg, x, y, rfl, hxy, hxa, hmy⟩
    cases hf with
    | @lam _ _ n' a₀ f₀ _ _ ha₀ hdom hb hle =>
      have hn : n = n' := Nat.succ.inj hle.1
      subst hn
      have hfg : DShapeFun.LEP (DShape.LEP eqN) fg.1 f₀.1 := hle.2
      obtain ⟨⟨u, v⟩, huv, hux, hyv⟩ := hfg (x.1, y.1) hxy
      have hwu : DShape.WF u := (f₀.2.1.entries (u, v) huv).1
      have hwv : DShape.WF v := (f₀.2.1.entries (u, v) huv).2
      obtain ⟨x', y', hx'y', hx'u, hvy', hx'a₀⟩ :=
        hdom n f₀ ⟨u, hwu⟩ ⟨v, hwv⟩ rfl huv
      have hx'x : LeT ⟨n, x'⟩ ⟨n, x⟩ :=
        ⟨rfl, DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hx'u hux⟩
      have hx'_pi : Interp EI ρ ⟨n, x'⟩ (.pi D C) :=
        Interp.mono ha₀ hx'a₀
      have hx'_lam : Interp EI ρ ⟨n, x'⟩ (.lam D' b) :=
        Interp.mono ha (LeT.trans hx'x hxa)
      obtain ⟨k, hbot⟩ := interp_pi_and_lam_eq_botT hx'_pi hx'_lam
      have hnk : n = k := congrArg Sigma.fst hbot
      subst hnk
      have hyy' : LeT ⟨n, y⟩ ⟨n, y'⟩ :=
        ⟨rfl, DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hyv hvy'⟩
      have hbody : Interp EI (ρ.push ⟨n, x'⟩) m body :=
        Interp.mono (hb x' y' hx'y' hx'a₀) (LeT.trans hmy hyy')
      rw [hbot] at hbody
      exact ⟨n, hbody⟩

/-- Applying the identity function `.lam (.pi D C) (.bvar 0)` to any λ-abstraction
`.lam D' b` has only bottom lower bounds (`BotOnly`) in `RcicModelShape.Interp`. -/
theorem botOnly_app_lam_pi_bvar0_lam (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (D C D' b : Expr Nat) :
    BotOnly EI ρ (.app (.lam (.pi D C) (.bvar 0)) (.lam D' b)) := by
  intro m hm
  obtain ⟨n, hbody⟩ := interp_app_lam_pi_lam_inv hm
  rcases Interp.le_bvar hbody with ⟨k, hbot⟩ | hle
  · exact ⟨k, hbot⟩
  · exact ⟨n, TShape.LEP.le_bot hle⟩

/-- **Admitted Obstruction 4a (`beta_linear_unsound_interp`):**
Even for the linear identity body `.bvar 0`, `ConvT.beta` is unsound on
`RcicModelShape.Interp` whenever the parameter domain is `.pi D C` and the argument
is `.lam D' b`: `lamT (botWFun 0)` approximates the contractum `instantiate0 (.lam D' b) (.bvar 0)`
while the β-redex `.app (.lam (.pi D C) (.bvar 0)) (.lam D' b)` is `BotOnly`. -/
theorem beta_linear_unsound_interp (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (D C D' b : Expr Nat) :
    Interp EI ρ (lamT (botWFun 0)) (instantiate0 (.lam D' b) (.bvar 0)) ∧
      ¬ Interp EI ρ (lamT (botWFun 0)) (.app (.lam (.pi D C) (.bvar 0)) (.lam D' b)) ∧
      ¬ SEq EI ρ (.app (.lam (.pi D C) (.bvar 0)) (.lam D' b))
        (instantiate0 (.lam D' b) (.bvar 0)) := by
  have hrhs : Interp EI ρ (lamT (botWFun 0)) (instantiate0 (.lam D' b) (.bvar 0)) := by
    simpa [instantiate0, instantiate] using
      (interp_lam_botWFun (a := (WShape.bot : LSh 0)) .bot :
        Interp EI ρ (lamT (botWFun 0)) (.lam D' b))
  have hlhs : ¬ Interp EI ρ (lamT (botWFun 0))
      (.app (.lam (.pi D C) (.bvar 0)) (.lam D' b)) := by
    intro h
    obtain ⟨k, hbot⟩ := botOnly_app_lam_pi_bvar0_lam EI ρ D C D' b (lamT (botWFun 0)) h
    exact not_lamT_eq_botT hbot
  exact ⟨hrhs, hlhs, fun hseq => hlhs ((hseq (lamT (botWFun 0))).2 hrhs)⟩

/-- Domain `Π (_ : Sort 0), Sort 0` for the well-typed linear β-obstruction fixture. -/
def betaLinObsDom : Expr Nat := .pi (.sort .zero) (.sort .zero)

/-- Argument `λ (x : Sort 0). x` for the well-typed linear β-obstruction fixture. -/
def betaLinObsArg : Expr Nat := .lam (.sort .zero) (.bvar 0)

/-- `betaLinObsDom : Sort (imax 1 1)` in any context `Γ`. -/
def hasTyT_betaLinObsDom (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ betaLinObsDom (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort Γ .zero) (.sort (.assumption (.sort .zero) :: Γ) .zero)

/-- `betaLinObsArg : betaLinObsDom` in any context `Γ`. -/
def hasTyT_betaLinObsArg (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ betaLinObsArg betaLinObsDom :=
  .lam Γ (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
    (.sort Γ .zero) (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)

/-- `.bvar 0 : betaLinObsDom` in `.assumption betaLinObsDom :: Γ`. -/
def hasTyT_betaLinObsBody (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n (.assumption betaLinObsDom :: Γ) (.bvar 0) betaLinObsDom :=
  .bvar (.assumption betaLinObsDom :: Γ) 0 betaLinObsDom rfl

/-- **Refutation of `BetaRhsGap` on `RcicModelShape.Interp`:**
`BetaRhsGap E n EI ValOK` is false whenever `ValOK Γ ρ` is inhabited for at least one
context `Γ` and valuation `ρ`. -/
theorem not_betaRhsGap_of_valOK {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    {Γ : LCtx} {ρ : Valuation} (hρ : ValOK Γ ρ) :
    ¬ BetaRhsGap E n EI ValOK := by
  intro hbeta
  obtain ⟨hrhs, hlhs, _⟩ :=
    beta_linear_unsound_interp EI ρ (.sort .zero) (.sort .zero) (.sort .zero) (.bvar 0)
  exact hlhs (hbeta (hasTyT_betaLinObsDom E n Γ)
    (hasTyT_betaLinObsBody E n Γ) (hasTyT_betaLinObsArg E n Γ) hρ hrhs)

/-! ### 7.2 Admitted Obstruction 4b: Multi-level `ConvT.zeta` is unsound on `RcicModelShape.Interp` -/

/-- Sort level `imax 1 1` for the well-typed ζ-obstruction fixture. -/
def zetaBetaObsLevel : Level := .imax (.succ .zero) (.succ .zero)

/-- Type `Sort (imax 1 1)` of the let-bound type variable `X`. -/
def zetaBetaObsDom : Expr Nat := .sort zetaBetaObsLevel

/-- Let-bound value `Π (_ : Sort 0), Sort 0 : Sort (imax 1 1)`. -/
def zetaBetaObsVal : Expr Nat := .pi (.sort .zero) (.sort .zero)

/-- Let-body `Π (_ : X), Π (_ : X), Sort 0`, using `X` at two binder depths. -/
def zetaBetaObsBody : Expr Nat := .pi (.bvar 0) (.pi (.bvar 1) (.sort .zero))

/-- Sort of `zetaBetaObsBody`. -/
def zetaBetaObsCod : Expr Nat :=
  .sort (.imax zetaBetaObsLevel (.imax zetaBetaObsLevel (.succ .zero)))

/-- `zetaBetaObsDom : Sort (succ zetaBetaObsLevel)` in any context `Γ`. -/
def hasTyT_zetaBetaObsDom (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ zetaBetaObsDom (.sort (.succ zetaBetaObsLevel)) :=
  .sort Γ zetaBetaObsLevel

/-- `zetaBetaObsVal : zetaBetaObsDom` in any context `Γ`. -/
def hasTyT_zetaBetaObsVal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ zetaBetaObsVal zetaBetaObsDom :=
  hasTyT_betaLinObsDom E n Γ

/-- `zetaBetaObsBody : zetaBetaObsCod` under `.letBinding zetaBetaObsDom zetaBetaObsVal :: Γ`. -/
def hasTyT_zetaBetaObsBody_letBinding (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n (.letBinding zetaBetaObsDom zetaBetaObsVal :: Γ)
      zetaBetaObsBody zetaBetaObsCod :=
  let Γ₁ : LCtx := .letBinding zetaBetaObsDom zetaBetaObsVal :: Γ
  let Γ₂ : LCtx := .assumption (.bvar 0) :: Γ₁
  let Γ₃ : LCtx := .assumption (.bvar 1) :: Γ₂
  .pi Γ₁ (.bvar 0) zetaBetaObsLevel (.pi (.bvar 1) (.sort .zero))
    (.imax zetaBetaObsLevel (.succ .zero))
    (.bvar Γ₁ 0 zetaBetaObsDom rfl)
    (.pi Γ₂ (.bvar 1) zetaBetaObsLevel (.sort .zero) (.succ .zero)
      (.bvar Γ₂ 1 zetaBetaObsDom rfl)
      (.sort Γ₃ .zero))

/-- Level-1 Π-shape `(piT ⊥ (botWFun 0)).2 : LSh 1`. -/
def zetaBetaObsP1 : LSh 1 := (piT (WShape.bot : LSh 0) (botWFun 0)).2

/-- Level-2 Π-shape `(piT ⊥ (botWFun 1)).2 : LSh 2`. -/
def zetaBetaObsP2 : LSh 2 := (piT (WShape.bot : LSh 1) (botWFun 1)).2

/-- Level-2 Π-shape `(piT zetaBetaObsP1 (botWFun 1)).2 : LSh 2`. -/
def zetaBetaObsInnerPi : LSh 2 := (piT zetaBetaObsP1 (botWFun 1)).2

/-- Well-formedness of the constant step-function graph `[(⊥, zetaBetaObsInnerPi)]` at level 3. -/
theorem wf_constInnerPiWFun :
    DShape.WF (α := Level) (n := 3)
      (.lam [(DShape.bot, zetaBetaObsInnerPi.1)]) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨(DShape.bot, zetaBetaObsInnerPi.1), List.mem_singleton_self _, rfl, rfl⟩⟩
  · intro x hx
    rcases List.mem_singleton.1 hx with rfl
    exact ⟨DShape.wf_bot, zetaBetaObsInnerPi.2⟩
  · intro x hx y hy _
    rcases List.mem_singleton.1 hx with rfl
    rcases List.mem_singleton.1 hy with rfl
    exact ⟨(DShape.bot, zetaBetaObsInnerPi.1),
      List.mem_singleton_self _, rfl, rfl, rfl⟩

/-- The constant step-function graph `[(⊥, zetaBetaObsInnerPi)] : WFun 2`. -/
def constInnerPiWFun : WFun 2 :=
  ⟨[(DShape.bot, zetaBetaObsInnerPi.1)], wf_constInnerPiWFun⟩

theorem hasDomP_constInnerPiWFun (a : LSh 2) :
    HasDomP (lamT constInnerPiWFun) ⟨2, a⟩ := by
  intro k fg x y hlam hxy
  have hnk : 3 = k + 1 := congrArg Sigma.fst hlam
  have hk : 2 = k := Nat.succ.inj hnk
  subst hk
  have hlist : constInnerPiWFun.1 = fg.1 := by
    simpa [getLamGraph_lamT] using congrArg (getLamGraph 2) hlam
  rw [← hlist] at hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  refine ⟨WShape.bot, zetaBetaObsInnerPi, ?_,
    DShape.LEP.bot _, ?_, LeT.bot_le ⟨2, a⟩⟩
  · rw [← hlist]
    exact List.mem_singleton_self _
  · rw [hxy'.2]
    exact DShape.LEP.rfl (fun _ _ => rfl) _

/-- Probe compact shape `piT zetaBetaObsP2 constInnerPiWFun : LTShape` at level 3. -/
def zetaBetaObsM : LTShape := piT zetaBetaObsP2 constInnerPiWFun

theorem interp_zetaBetaObsInnerPi (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (B : Expr Nat) :
    Interp EI ρ (piT zetaBetaObsP1 (botWFun 1)) (.pi zetaBetaObsVal B) :=
  interp_pi_botWFun (a := zetaBetaObsP1)
    (interp_pi_botWFun (a := (WShape.bot : LSh 0)) .bot)

/-- `zetaBetaObsM` approximates the ζ-contractum `instantiate0 zetaBetaObsVal zetaBetaObsBody`
because the two syntactic copies of `zetaBetaObsVal` are approximated independently at
level 2 (`zetaBetaObsP2`) and level 1 (`zetaBetaObsP1`). -/
theorem interp_instantiate_zetaBetaObs (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) :
    Interp EI ρ zetaBetaObsM (instantiate0 zetaBetaObsVal zetaBetaObsBody) := by
  change Interp EI ρ (piT zetaBetaObsP2 constInnerPiWFun)
    (.pi zetaBetaObsVal (.pi zetaBetaObsVal (.sort .zero)))
  have hp2 : Interp EI ρ ⟨2, zetaBetaObsP2⟩ zetaBetaObsVal :=
    interp_pi_botWFun (a := (WShape.bot : LSh 1)) .bot
  refine .pi hp2 .bot (hasDomP_constInnerPiWFun WShape.bot) ?_ (LeT.refl _)
  intro x y hxy _
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hy' : (⟨2, y⟩ : LTShape) = piT zetaBetaObsP1 (botWFun 1) :=
    congrArg (Sigma.mk 2) (Subtype.ext hxy'.2)
  rw [hy']
  exact interp_zetaBetaObsInnerPi EI (ρ.push ⟨2, x⟩) (.sort .zero)

/-- No single compact shape `s : LTShape` can satisfy `Interp EI (ρ.push s) zetaBetaObsM zetaBetaObsBody`,
because the outer domain `.bvar 0` forces `s.1 = 2` while the inner domain `.bvar 1`
forces `s.1 = 1`. -/
theorem not_interp_push_zetaBetaObsBody (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (s : LTShape) :
    ¬ Interp EI (ρ.push s) zetaBetaObsM zetaBetaObsBody := by
  intro H
  have hp2 : Interp EI (ρ.push s) (piT (WShape.bot : LSh 1) (botWFun 1)) (.bvar 0) :=
    interp_pi_dom_inv H
  have hs2 : 2 = s.1 := by
    rcases Interp.le_bvar hp2 with ⟨k, hbot⟩ | hle
    · exact False.elim (not_piT_eq_botT hbot)
    · exact hle.1
  generalize hm : zetaBetaObsM = m at H
  cases H with
  | bot =>
    exact not_piT_eq_botT hm
  | @pi _ _ n' a a' f _ _ _ _ hdom hb hle =>
    rw [← hm] at hle
    have hn : 3 = n' + 1 := hle.1
    have hn' : 2 = n' := Nat.succ.inj hn
    subst hn'
    have hfg : DShapeFun.LEP (DShape.LEP eqN) constInnerPiWFun.1 f.1 := hle.2.2
    obtain ⟨⟨u₀, v₀⟩, huv, _, hinner_v⟩ :=
      hfg (DShape.bot, zetaBetaObsInnerPi.1) (List.mem_singleton_self _)
    have hwu : DShape.WF u₀ := (f.2.1.entries (u₀, v₀) huv).1
    have hwv : DShape.WF v₀ := (f.2.1.entries (u₀, v₀) huv).2
    obtain ⟨x', y', hx'y', _, hvy', hx'a'⟩ :=
      hdom 2 f ⟨u₀, hwu⟩ ⟨v₀, hwv⟩ rfl huv
    have hle_inner : LeT (piT zetaBetaObsP1 (botWFun 1)) ⟨2, y'⟩ :=
      ⟨rfl, DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hinner_v hvy'⟩
    have hinner : Interp EI ((ρ.push s).push ⟨2, x'⟩)
        (piT zetaBetaObsP1 (botWFun 1)) (.pi (.bvar 1) (.sort .zero)) :=
      Interp.mono (hb x' y' hx'y' hx'a') hle_inner
    have hp1 : Interp EI ((ρ.push s).push ⟨2, x'⟩)
        (piT (WShape.bot : LSh 0) (botWFun 0)) (.bvar 1) :=
      interp_pi_dom_inv hinner
    have hs1 : 1 = s.1 := by
      rcases Interp.le_bvar hp1 with ⟨k, hbot⟩ | hle₁
      · exact False.elim (not_piT_eq_botT hbot)
      · exact hle₁.1
    omega

theorem not_interp_letE_zetaBetaObs (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (A : Expr Nat) :
    ¬ Interp EI ρ zetaBetaObsM (.letE A zetaBetaObsVal zetaBetaObsBody) := by
  generalize hm : zetaBetaObsM = m
  intro H
  cases H with
  | bot => exact not_piT_eq_botT hm
  | letE _ hb =>
    rw [← hm] at hb
    exact not_interp_push_zetaBetaObsBody EI ρ _ hb

/-- **Admitted Obstruction 4b (`zeta_unsound_interp`):**
On `RcicModelShape.Interp`, `ConvT.zeta` is unsound for `zetaBetaObsVal` and
`zetaBetaObsBody` under every `EI` and `ρ` because `Valuation` binds `.bvar 0` to a
single stratified level `s.1 : Nat`. -/
theorem zeta_unsound_interp (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (A : Expr Nat) :
    Interp EI ρ zetaBetaObsM (instantiate0 zetaBetaObsVal zetaBetaObsBody) ∧
      ¬ Interp EI ρ zetaBetaObsM (.letE A zetaBetaObsVal zetaBetaObsBody) ∧
      ¬ SEq EI ρ (.letE A zetaBetaObsVal zetaBetaObsBody)
        (instantiate0 zetaBetaObsVal zetaBetaObsBody) := by
  have hrhs := interp_instantiate_zetaBetaObs EI ρ
  have hlhs := not_interp_letE_zetaBetaObs EI ρ A
  exact ⟨hrhs, hlhs, fun hseq => hlhs ((hseq zetaBetaObsM).2 hrhs)⟩

/-- **Refutation of `ZetaRhsGap` on `RcicModelShape.Interp`:**
`ZetaRhsGap E n EI ValOK` is false whenever `ValOK Γ ρ` is inhabited for at least one
context `Γ` and valuation `ρ`. -/
theorem not_zetaRhsGap_of_valOK {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    {Γ : LCtx} {ρ : Valuation} (hρ : ValOK Γ ρ) :
    ¬ ZetaRhsGap E n EI ValOK := by
  intro hzeta
  obtain ⟨hrhs, hlhs, _⟩ := zeta_unsound_interp EI ρ zetaBetaObsDom
  exact hlhs (hzeta (hasTyT_zetaBetaObsDom E n Γ)
    (hasTyT_zetaBetaObsVal E n Γ) (hasTyT_zetaBetaObsBody_letBinding E n Γ) hρ hrhs)

/-- **Vacuity Tooth 1a (`valOK_empty_of_seqModel`):**
Any `M : SEqModelSupply E n EI ValOK` forces `ValOK` to be empty (`∀ Γ ρ, ¬ ValOK Γ ρ`),
because `M.betaRhs` contradicts `not_betaRhsGap_of_valOK`. -/
theorem valOK_empty_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK) :
    ∀ Γ ρ, ¬ ValOK Γ ρ :=
  fun _ _ hρ => not_betaRhsGap_of_valOK hρ M.betaRhs

/-- **Vacuity Tooth 1b (`valOK_empty_of_seqModel_zeta`):**
Independently of `M.betaRhs`, `M.zetaRhs` also forces `∀ Γ ρ, ¬ ValOK Γ ρ` via
`not_zetaRhsGap_of_valOK`. -/
theorem valOK_empty_of_seqModel_zeta {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK) :
    ∀ Γ ρ, ¬ ValOK Γ ρ :=
  fun _ _ hρ => not_zetaRhsGap_of_valOK hρ M.zetaRhs

/-- **Vacuity Tooth 2 (`seqVal_total_of_seqModel`):**
Under `M : SEqModelSupply E n EI ValOK`, `SEqVal EI ValOK` is the total relation on
all contexts and expressions because `ValOK` is empty. -/
theorem seqVal_total_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    (Γ : LCtx) (a b : Expr Nat) :
    SEqVal EI ValOK Γ a b :=
  fun {ρ} hρ => False.elim (valOK_empty_of_seqModel M Γ ρ hρ)

/-- **Vacuity Tooth 3 (`tyConvT_total_of_seqModel`):**
Combining `M : SEqModelSupply E n EI ValOK` with `R : SEqPiReadbackGap E n EI ValOK`
forces `TyConvT E n Γ A₁ A₂` between **every** pair of expressions `A₁, A₂`, showing
that `semanticPiModel_of_seqModel`, `piInjType_of_seqModel`, and `piRowField_of_seqModel`
have vacuous premises on raw `RcicModelShape.Interp`. -/
def tyConvT_total_of_seqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {ValOK : LCtx → Valuation → Prop}
    (M : SEqModelSupply E n EI ValOK)
    (R : SEqPiReadbackGap E n EI ValOK)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A₁ A₂ : Expr Nat) :
    TyConvT E n Γ A₁ A₂ :=
  (R hΓ (seqVal_total_of_seqModel M Γ (.pi A₁ (.sort .zero)) (.pi A₂ (.sort .zero)))
    (seqVal_total_of_seqModel M Γ A₁ A₂)).1

/-! ### 7.3 Proposed Repair of Obstruction 4b on `Interp`: Reverse-Substitution Factorization (`SubstFactorizes`) -/

/-- Reverse-substitution factorization: every compact lower bound `m` of
`instantiate0 v body` under `ρ` is witnessed by a single compact lower bound `s` of `v`
such that `m` approximates `body` under `ρ.push s`. -/
def SubstFactorizes (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v body : Expr Nat) : Prop :=
  ∀ m : LTShape, Interp EI ρ m (instantiate0 v body) →
    ∃ s : LTShape, Interp EI ρ s v ∧ Interp EI (ρ.push s) m body

/-- Under `SubstFactorizes EI ρ v body`, the right-to-left direction of `ConvT.zeta`
holds unconditionally. -/
theorem interp_letE_rhs_of_substFactorizes
    {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} (A : Expr Nat) {v body : Expr Nat}
    (hF : SubstFactorizes EI ρ v body)
    (hm : Interp EI ρ m (instantiate0 v body)) :
    Interp EI ρ m (.letE A v body) := by
  obtain ⟨s, hsv, hmb⟩ := hF m hm
  exact .letE hsv hmb

/-- **Positive ζ-soundness under `SubstFactorizes`:**
combining `interp_zeta_lhs` with `interp_letE_rhs_of_substFactorizes` yields full
two-way `SEq` for `.letE A v body` and `instantiate0 v body`. -/
theorem seq_zeta_of_substFactorizes
    {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} (A : Expr Nat) {v body : Expr Nat}
    (hF : SubstFactorizes EI ρ v body) :
    SEq EI ρ (.letE A v body) (instantiate0 v body) :=
  fun _ => ⟨interp_zeta_lhs, interp_letE_rhs_of_substFactorizes A hF⟩

theorem substFactorizes_bvar0 (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v : Expr Nat) :
    SubstFactorizes EI ρ v (.bvar 0) := by
  intro m hm
  exact ⟨m, hm, .bvar (LeT.refl m)⟩

theorem substFactorizes_bvar_succ (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v : Expr Nat) (i : Nat) :
    SubstFactorizes EI ρ v (.bvar (i + 1)) := by
  intro m hm
  have hi : Interp EI ρ m (.bvar i) := by
    simpa [instantiate0, instantiate] using hm
  have hlift : (Expr.bvar (i + 1) : Expr Nat) = lift 0 1 (.bvar i) := by
    simp [lift]
  rw [hlift]
  exact ⟨botT 0, .bot, (interp_lift0_one_iff (s := botT 0)).2 hi⟩

theorem substFactorizes_sort (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v : Expr Nat) (u : Level) :
    SubstFactorizes EI ρ v (.sort u) := by
  intro m hm
  exact ⟨botT 0, .bot, (interp_lift0_one_iff (s := botT 0)).2 hm⟩

theorem substFactorizes_const (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v : Expr Nat) (r : Nat) (ls : List Level) :
    SubstFactorizes EI ρ v (.const r ls) := by
  intro m hm
  exact ⟨botT 0, .bot, (interp_lift0_one_iff (s := botT 0)).2 hm⟩

theorem substFactorizes_lift0_one (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v e : Expr Nat) :
    SubstFactorizes EI ρ v (lift 0 1 e) := by
  intro m hm
  rw [instantiate0, instantiate_lift_id 0 v e] at hm
  exact ⟨botT 0, .bot, (interp_lift0_one_iff (s := botT 0)).2 hm⟩

/-- Directedness of the denotation of `v` under `ρ`: any two compact lower bounds
`s₁, s₂` of `v` have a common upper bound `s` in `Interp EI ρ · v`. -/
def DirectedDen (EI : Nat → List Level → LTShape → Prop)
    (ρ : Valuation) (v : Expr Nat) : Prop :=
  ∀ s₁ s₂ : LTShape, Interp EI ρ s₁ v → Interp EI ρ s₂ v →
    ∃ s : LTShape, Interp EI ρ s v ∧ LeT s₁ s ∧ LeT s₂ s

/-- Under `DirectedDen EI ρ v`, `SubstFactorizes EI ρ v` is closed under `.app F A`
even when `.bvar 0` occurs in both `F` and `A`. -/
theorem substFactorizes_app_of_directed
    {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {v F A : Expr Nat}
    (hdir : DirectedDen EI ρ v)
    (hF : SubstFactorizes EI ρ v F)
    (hA : SubstFactorizes EI ρ v A) :
    SubstFactorizes EI ρ v (.app F A) := by
  intro m hm
  cases hm with
  | bot => exact ⟨botT 0, .bot, .bot⟩
  | app hf ha happ =>
    obtain ⟨s₁, hs₁v, hf'⟩ := hF _ hf
    obtain ⟨s₂, hs₂v, ha'⟩ := hA _ ha
    obtain ⟨s, hsv, hle₁, hle₂⟩ := hdir s₁ s₂ hs₁v hs₂v
    have hf_s : Interp EI (ρ.push s) _ F :=
      Interp.mono_l hf' (Valuation.LeP.push (Valuation.LeP.rfl ρ) hle₁)
    have ha_s : Interp EI (ρ.push s) _ A :=
      Interp.mono_l ha' (Valuation.LeP.push (Valuation.LeP.rfl ρ) hle₂)
    exact ⟨s, hsv, .app hf_s ha_s happ⟩

/-- When `.bvar 0` does not occur in the function `lift 0 1 F`, `SubstFactorizes`
for `.app (lift 0 1 F) A` requires no directedness assumption on `v`. -/
theorem substFactorizes_app_left_vacuous
    {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {v F A : Expr Nat}
    (hA : SubstFactorizes EI ρ v A) :
    SubstFactorizes EI ρ v (.app (lift 0 1 F) A) := by
  intro m hm
  cases hm with
  | bot => exact ⟨botT 0, .bot, .bot⟩
  | app hf ha happ =>
    rw [instantiate_lift_id 0 v F] at hf
    obtain ⟨s, hsv, ha'⟩ := hA _ ha
    exact ⟨s, hsv, .app ((interp_lift0_one_iff (s := s)).2 hf) ha' happ⟩

/-- When `.bvar 0` does not occur in the argument `lift 0 1 A`, `SubstFactorizes`
for `.app F (lift 0 1 A)` requires no directedness assumption on `v`. -/
theorem substFactorizes_app_right_vacuous
    {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {v F A : Expr Nat}
    (hF : SubstFactorizes EI ρ v F) :
    SubstFactorizes EI ρ v (.app F (lift 0 1 A)) := by
  intro m hm
  cases hm with
  | bot => exact ⟨botT 0, .bot, .bot⟩
  | app hf ha happ =>
    rw [instantiate_lift_id 0 v A] at ha
    obtain ⟨s, hsv, hf'⟩ := hF _ hf
    exact ⟨s, hsv, .app hf' ((interp_lift0_one_iff (s := s)).2 ha) happ⟩

/-! ### 7.4 Concrete Environment Interpretations (`eqNListClose` and `emptyEnvInterp`) -/

theorem eqNList_refl : ∀ ls : List Level, eqNList ls ls
  | [] => trivial
  | _ :: t => ⟨fun _ => rfl, eqNList_refl t⟩

theorem eqNList_symm : ∀ {ls₁ ls₂ : List Level}, eqNList ls₁ ls₂ → eqNList ls₂ ls₁
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, ht⟩ => ⟨fun ρ => (h ρ).symm, eqNList_symm ht⟩

theorem eqNList_trans :
    ∀ {ls₁ ls₂ ls₃ : List Level}, eqNList ls₁ ls₂ → eqNList ls₂ ls₃ → eqNList ls₁ ls₃
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, ht1⟩, ⟨h2, ht2⟩ =>
      ⟨fun ρ => (h1 ρ).trans (h2 ρ), eqNList_trans ht1 ht2⟩

/-- Saturation of any `EI : Nat → List Level → LTShape → Prop` under `eqNList`. -/
def eqNListClose (EI : Nat → List Level → LTShape → Prop) :
    Nat → List Level → LTShape → Prop :=
  fun r ls u => ∃ ls', eqNList ls ls' ∧ EI r ls' u

theorem le_eqNListClose {EI : Nat → List Level → LTShape → Prop}
    {r : Nat} {ls : List Level} {u : LTShape} (h : EI r ls u) :
    eqNListClose EI r ls u :=
  ⟨ls, eqNList_refl ls, h⟩

/-- `eqNListClose EI` unconditionally satisfies `EIConsts` for every `EI`. -/
theorem eiConsts_eqNListClose (EI : Nat → List Level → LTShape → Prop) :
    EIConsts (eqNListClose EI) := by
  intro r ls ls' u h
  constructor
  · rintro ⟨ls₀, h₀, hu⟩
    exact ⟨ls₀, eqNList_trans (eqNList_symm h) h₀, hu⟩
  · rintro ⟨ls₀, h₀, hu⟩
    exact ⟨ls₀, eqNList_trans h h₀, hu⟩

/-- Canonical empty environment interpretation. -/
def emptyEnvInterp : Nat → List Level → LTShape → Prop :=
  fun _ _ _ => False

theorem eiConsts_emptyEnvInterp : EIConsts emptyEnvInterp := by
  intro _ _ _ _ _
  exact Iff.rfl

/-- `EIDelta emptyEnv EI` holds unconditionally for every environment interpretation `EI`. -/
theorem eiDelta_emptyEnv (EI : Nat → List Level → LTShape → Prop) :
    EIDelta emptyEnv EI := by
  intro r _ _ _ hmem
  simp [emptyEnv] at hmem

/-! ## 8. Filter-Valuation & Untyped-Lambda Domain Model (`fden` / `FSEq`):
Simultaneous Repair of Obstructions 4a and 4b, Exact Two-Way Substitution,
Unconditional `ConvT.zeta` / `ConvT.zetaLocal` Soundness, and Injective Π-Model -/

/-! ### 8.1 `IsBotT`, Filter Valuations (`FValuation`), and `fden` Evaluator -/

/-- A compact shape `m : LTShape` is a bottom shape at its level. -/
def IsBotT (m : LTShape) : Prop := ∃ k, m = botT k

theorem isBotT_botT (k : Nat) : IsBotT (botT k) := ⟨k, rfl⟩

theorem isBotT_of_leT {m' m : LTShape} (hle : LeT m' m) (hm : IsBotT m) :
    IsBotT m' := by
  rcases hm with ⟨k, rfl⟩
  exact ⟨k, TShape.LEP.le_bot hle⟩

/-- Filter valuations: each de Bruijn index denotes a predicate (filter) of compact shapes. -/
abbrev FValuation := Nat → LTShape → Prop

/-- Pointwise inclusion of filter valuations. -/
def FValLe (Φ₁ Φ₂ : FValuation) : Prop :=
  ∀ i m, Φ₁ i m → Φ₂ i m

theorem FValLe.refl (Φ : FValuation) : FValLe Φ Φ :=
  fun _ _ h => h

theorem FValLe.trans {Φ₁ Φ₂ Φ₃ : FValuation}
    (h1 : FValLe Φ₁ Φ₂) (h2 : FValLe Φ₂ Φ₃) : FValLe Φ₁ Φ₃ :=
  fun i m h => h2 i m (h1 i m h)

/-- Push a filter `P` at de Bruijn index `0`. -/
def fpush (P : LTShape → Prop) (Φ : FValuation) : FValuation
  | 0 => P
  | i + 1 => Φ i

theorem FValLe.fpush {P₁ P₂ : LTShape → Prop} {Φ₁ Φ₂ : FValuation}
    (hP : ∀ m, P₁ m → P₂ m) (hΦ : FValLe Φ₁ Φ₂) :
    FValLe (PiInversion.fpush P₁ Φ₁) (PiInversion.fpush P₂ Φ₂)
  | 0, m, h => hP m h
  | i + 1, m, h => hΦ i m h

/-- Shift a filter valuation for `lift c k`: indices below `c` stay, indices `≥ c`
read `Φ (i + k)`. -/
def fliftVal (c k : Nat) (Φ : FValuation) : FValuation :=
  fun i => if i < c then Φ i else Φ (i + k)

/-- Insert a filter `P` at de Bruijn index `j` (for `instantiate j`). -/
def finsert (j : Nat) (P : LTShape → Prop) (Φ : FValuation) : FValuation :=
  fun i => if i = j then P else if j < i then Φ (i - 1) else Φ i

theorem fliftVal_fpush (c k : Nat) (P : LTShape → Prop) (Φ : FValuation) :
    fliftVal (c + 1) k (fpush P Φ) = fpush P (fliftVal c k Φ) := by
  funext i
  cases i with
  | zero =>
    simp [fliftVal, fpush]
  | succ i' =>
    simp only [fliftVal, fpush]
    by_cases h : i' < c
    · have h' : i' + 1 < c + 1 := Nat.succ_lt_succ h
      rw [if_pos h', if_pos h]
    · have h' : ¬ (i' + 1 < c + 1) := fun hc => h (Nat.lt_of_succ_lt_succ hc)
      rw [if_neg h', if_neg h]
      have hadd : i' + 1 + k = (i' + k) + 1 := by omega
      rw [hadd]

theorem fliftVal_zero_one_fpush (P : LTShape → Prop) (Φ : FValuation) :
    fliftVal 0 1 (fpush P Φ) = Φ := by
  funext i
  simp [fliftVal, fpush]

theorem finsert_zero (P : LTShape → Prop) (Φ : FValuation) :
    finsert 0 P Φ = fpush P Φ := by
  funext i
  cases i with
  | zero => rfl
  | succ n =>
    simp only [finsert, fpush]
    have h1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
    have h2 : 0 < n + 1 := Nat.zero_lt_succ n
    rw [if_neg h1, if_pos h2]
    rfl

theorem finsert_succ_fpush (j : Nat) (P Q : LTShape → Prop) (Φ : FValuation) :
    finsert (j + 1) P (fpush Q Φ) = fpush Q (finsert j P Φ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i' =>
    simp only [finsert, fpush]
    by_cases h1 : i' = j
    · have h1' : i' + 1 = j + 1 := congrArg Nat.succ h1
      rw [if_pos h1', if_pos h1]
    · have h1' : i' + 1 ≠ j + 1 := fun h => h1 (Nat.succ.inj h)
      rw [if_neg h1', if_neg h1]
      by_cases h2 : j < i'
      · have h2' : j + 1 < i' + 1 := Nat.succ_lt_succ h2
        rw [if_pos h2', if_pos h2]
        cases i' with
        | zero => exact False.elim (by omega)
        | succ i'' => rfl
      · have h2' : ¬ (j + 1 < i' + 1) := fun h => h2 (Nat.lt_of_succ_lt_succ h)
        rw [if_neg h2', if_neg h2]

/-- Filter denotation of a constant `.const r ls`. -/
def fdenConst (EI : Nat → List Level → LTShape → Prop)
    (r : Nat) (ls : List Level) (m : LTShape) : Prop :=
  IsBotT m ∨ ∃ u, EI r ls u ∧ LeT m u

/-- Relational application on filter denotations. -/
def fdenApp (F A : LTShape → Prop) (m : LTShape) : Prop :=
  IsBotT m ∨ ∃ tf ta, F tf ∧ A ta ∧ AppLe tf ta m

/-- Filter denotation of a natural number literal `.lit t` (matching `natExpand t`). -/
def fdenLit (EI : Nat → List Level → LTShape → Prop) : Nat → LTShape → Prop
  | 0 => fdenConst EI 1 []
  | t + 1 => fdenApp (fdenConst EI 2 []) (fdenLit EI t)

/-- **Filter-Valuation Domain Denotation (`fden`):**
Maps each expression `e : Expr Nat` under filter valuation `Φ : FValuation` to its
filter of compact lower bounds `LTShape → Prop`.
1. `.lam` is untyped in its parameter domain (resolving Admitted Obstruction 4a while
   keeping `.pi` domain-typed and injective).
2. `.letE` pushes the full denotation filter `fden EI v Φ` onto `Φ` (resolving
   Admitted Obstruction 4b). -/
def fden (EI : Nat → List Level → LTShape → Prop) :
    Expr Nat → FValuation → LTShape → Prop
  | .bvar i, Φ => fun m => IsBotT m ∨ ∃ s, Φ i s ∧ LeT m s
  | .sort u, _ => fun m => IsBotT m ∨ LeT m (sortT u)
  | .const r ls, _ => fdenConst EI r ls
  | .app f a, Φ => fdenApp (fden EI f Φ) (fden EI a Φ)
  | .lam _ b, Φ => fun m =>
      IsBotT m ∨ ∃ (n : Nat) (f : WFun n),
        (∀ x y : LSh n, (x.1, y.1) ∈ f.1 →
          fden EI b (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩) ∧
        LeT m (lamT f)
  | .pi A B, Φ => fun m =>
      IsBotT m ∨ ∃ (n : Nat) (a : LSh n) (f : WFun n),
        fden EI A Φ ⟨n, a⟩ ∧
        (∀ x y : LSh n, (x.1, y.1) ∈ f.1 →
          fden EI B (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩) ∧
        LeT m (piT a f)
  | .letE _ v b, Φ => fden EI b (fpush (fden EI v Φ) Φ)
  | .lit t, _ => fdenLit EI t

theorem fdenConst_bot {EI : Nat → List Level → LTShape → Prop}
    (r : Nat) (ls : List Level) (n : Nat) :
    fdenConst EI r ls (botT n) :=
  Or.inl ⟨n, rfl⟩

theorem fdenApp_bot {F A : LTShape → Prop} (n : Nat) :
    fdenApp F A (botT n) :=
  Or.inl ⟨n, rfl⟩

theorem fdenLit_bot {EI : Nat → List Level → LTShape → Prop} :
    ∀ (t n : Nat), fdenLit EI t (botT n)
  | 0, n => fdenConst_bot 1 [] n
  | _ + 1, n => fdenApp_bot n

theorem fden_bot {EI : Nat → List Level → LTShape → Prop} :
    ∀ (e : Expr Nat) (Φ : FValuation) (n : Nat), fden EI e Φ (botT n)
  | .bvar _, _, n => Or.inl ⟨n, rfl⟩
  | .sort _, _, n => Or.inl ⟨n, rfl⟩
  | .const r ls, _, n => fdenConst_bot r ls n
  | .app _ _, _, n => fdenApp_bot n
  | .lam _ _, _, n => Or.inl ⟨n, rfl⟩
  | .pi _ _, _, n => Or.inl ⟨n, rfl⟩
  | .letE _ v b, Φ, n => fden_bot b (fpush (fden EI v Φ) Φ) n
  | .lit t, _, n => fdenLit_bot t n

theorem fden_of_isBotT {EI : Nat → List Level → LTShape → Prop}
    {e : Expr Nat} {Φ : FValuation} {m : LTShape} (hm : IsBotT m) :
    fden EI e Φ m := by
  rcases hm with ⟨n, rfl⟩
  exact fden_bot e Φ n

theorem fdenConst_mono {EI : Nat → List Level → LTShape → Prop}
    {r : Nat} {ls : List Level} {m m' : LTShape}
    (h : fdenConst EI r ls m) (hle : LeT m' m) :
    fdenConst EI r ls m' := by
  rcases h with hm | ⟨u, hu, hmu⟩
  · exact Or.inl (isBotT_of_leT hle hm)
  · exact Or.inr ⟨u, hu, LeT.trans hle hmu⟩

theorem fdenApp_mono {F A : LTShape → Prop} {m m' : LTShape}
    (h : fdenApp F A m) (hle : LeT m' m) :
    fdenApp F A m' := by
  rcases h with hm | ⟨tf, ta, hf, ha, happ⟩
  · exact Or.inl (isBotT_of_leT hle hm)
  · exact Or.inr ⟨tf, ta, hf, ha, AppLe.mono hle happ⟩

theorem fdenLit_mono {EI : Nat → List Level → LTShape → Prop} :
    ∀ {t : Nat} {m m' : LTShape}, fdenLit EI t m → LeT m' m → fdenLit EI t m'
  | 0, _, _, h, hle => fdenConst_mono h hle
  | _ + 1, _, _, h, hle => fdenApp_mono h hle

/-- `fden` is downward-closed in the compact shape `m`. -/
theorem fden_mono {EI : Nat → List Level → LTShape → Prop}
    {e : Expr Nat} :
    ∀ {Φ : FValuation} {m m' : LTShape},
      fden EI e Φ m → LeT m' m → fden EI e Φ m' := by
  induction e with
  | bvar _ =>
    rintro _ _ _ (hm | ⟨s, hs, hms⟩) hle
    · exact Or.inl (isBotT_of_leT hle hm)
    · exact Or.inr ⟨s, hs, LeT.trans hle hms⟩
  | sort _ =>
    rintro _ _ _ (hm | hms) hle
    · exact Or.inl (isBotT_of_leT hle hm)
    · exact Or.inr (LeT.trans hle hms)
  | const _ _ =>
    intro _ _ _ h hle
    exact fdenConst_mono h hle
  | app _ _ _ _ =>
    intro _ _ _ h hle
    exact fdenApp_mono h hle
  | lam _ _ _ _ =>
    rintro _ _ _ (hm | ⟨n, f, hb, hmf⟩) hle
    · exact Or.inl (isBotT_of_leT hle hm)
    · exact Or.inr ⟨n, f, hb, LeT.trans hle hmf⟩
  | pi _ _ _ _ =>
    rintro _ _ _ (hm | ⟨n, a, f, hA, hB, hmp⟩) hle
    · exact Or.inl (isBotT_of_leT hle hm)
    · exact Or.inr ⟨n, a, f, hA, hB, LeT.trans hle hmp⟩
  | letE _ _ _ _ _ ihb =>
    intro _ _ _ h hle
    exact ihb h hle
  | lit _ =>
    intro _ _ _ h hle
    exact fdenLit_mono h hle

/-- Downward-closure idempotence on `fden EI e Φ`. -/
theorem fdown_fden (EI : Nat → List Level → LTShape → Prop)
    (e : Expr Nat) (Φ : FValuation) :
    (fun m => IsBotT m ∨ ∃ s, fden EI e Φ s ∧ LeT m s) = fden EI e Φ := by
  funext m
  exact propext ⟨by
    rintro (hm | ⟨s, hs, hms⟩)
    · exact fden_of_isBotT hm
    · exact fden_mono hs hms,
    fun hm => Or.inr ⟨m, hm, LeT.refl m⟩⟩

/-- `fden` is monotone in the filter valuation `Φ`. -/
theorem fden_mono_val {EI : Nat → List Level → LTShape → Prop} :
    ∀ (e : Expr Nat) {Φ₁ Φ₂ : FValuation},
      FValLe Φ₁ Φ₂ → ∀ {m : LTShape}, fden EI e Φ₁ m → fden EI e Φ₂ m
  | .bvar _, _, _, _, _, Or.inl hm => Or.inl hm
  | .bvar i, _, _, hΦ, _, Or.inr ⟨s, hs, hms⟩ => Or.inr ⟨s, hΦ i s hs, hms⟩
  | .sort _, _, _, _, _, h => h
  | .const _ _, _, _, _, _, h => h
  | .lit _, _, _, _, _, h => h
  | .app _ _, _, _, _, _, Or.inl hm => Or.inl hm
  | .app f a, _, _, hΦ, _, Or.inr ⟨tf, ta, hf, ha, happ⟩ =>
      Or.inr ⟨tf, ta, fden_mono_val f hΦ hf, fden_mono_val a hΦ ha, happ⟩
  | .lam _ _, _, _, _, _, Or.inl hm => Or.inl hm
  | .lam _ b, _, _, hΦ, _, Or.inr ⟨n, f, hb, hmf⟩ =>
      Or.inr ⟨n, f,
        fun x y hxy => fden_mono_val b (FValLe.fpush (fun _ h => h) hΦ) (hb x y hxy),
        hmf⟩
  | .pi _ _, _, _, _, _, Or.inl hm => Or.inl hm
  | .pi A B, _, _, hΦ, _, Or.inr ⟨n, a, f, hA, hB, hmp⟩ =>
      Or.inr ⟨n, a, f, fden_mono_val A hΦ hA,
        fun x y hxy => fden_mono_val B (FValLe.fpush (fun _ h => h) hΦ) (hB x y hxy),
        hmp⟩
  | .letE _ v b, _, _, hΦ, _, hm =>
      fden_mono_val b (FValLe.fpush (fun _ hv => fden_mono_val v hΦ hv) hΦ) hm

/-- `fden` on `natExpand t` equals `fdenLit EI t`. -/
theorem fden_natExpand (EI : Nat → List Level → LTShape → Prop) (Φ : FValuation) :
    ∀ t : Nat, fden EI (natExpand t) Φ = fdenLit EI t
  | 0 => rfl
  | t + 1 => by
      show fdenApp (fdenConst EI 2 []) (fden EI (natExpand t) Φ) =
        fdenApp (fdenConst EI 2 []) (fdenLit EI t)
      rw [fden_natExpand EI Φ t]

/-! ### 8.2 Exact Two-Way Weakening (`fden_lift`), Exact Two-Way Substitution (`fden_instantiate`),
and Unconditional `ConvT.zeta` Soundness (`fden_zeta`) -/

/-- **Exact two-way weakening for `fden`:**
`fden EI (lift c k e) Φ` is propositionally equal to `fden EI e (fliftVal c k Φ)`. -/
theorem fden_lift (EI : Nat → List Level → LTShape → Prop) (e : Expr Nat) :
    ∀ (Φ : FValuation) (c k : Nat),
      fden EI (lift c k e) Φ = fden EI e (fliftVal c k Φ) := by
  induction e with
  | bvar i =>
    intro Φ c k
    simp only [lift]
    by_cases h : c ≤ i
    · have hnot : ¬ (i < c) := Nat.not_lt_of_le h
      rw [if_pos h]
      funext m
      simp [fden, fliftVal, hnot]
    · have hlt : i < c := Nat.lt_of_not_le h
      rw [if_neg h]
      funext m
      simp [fden, fliftVal, hlt]
  | sort _ => intro _ _ _; rfl
  | const _ _ => intro _ _ _; rfl
  | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro Φ c k
    simp only [lift, fden, ihf Φ c k, iha Φ c k]
  | lam A b _ ihb =>
    intro Φ c k
    funext m
    simp only [lift, fden]
    have hbody : ∀ (n : Nat) (x y : LSh n),
        fden EI (lift (c + 1) k b) (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ =
          fden EI b (fpush (fun s => LeT s ⟨n, x⟩) (fliftVal c k Φ)) ⟨n, y⟩ := by
      intro n x y
      rw [ihb (fpush (fun s => LeT s ⟨n, x⟩) Φ) (c + 1) k, fliftVal_fpush]
    simp only [hbody]
  | pi A B ihA ihB =>
    intro Φ c k
    funext m
    simp only [lift, fden, ihA Φ c k]
    have hbody : ∀ (n : Nat) (x y : LSh n),
        fden EI (lift (c + 1) k B) (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ =
          fden EI B (fpush (fun s => LeT s ⟨n, x⟩) (fliftVal c k Φ)) ⟨n, y⟩ := by
      intro n x y
      rw [ihB (fpush (fun s => LeT s ⟨n, x⟩) Φ) (c + 1) k, fliftVal_fpush]
    simp only [hbody]
  | letE A v b _ ihv ihb =>
    intro Φ c k
    simp only [lift, fden, ihv Φ c k]
    rw [ihb (fpush (fden EI v (fliftVal c k Φ)) Φ) (c + 1) k, fliftVal_fpush]

/-- Under-binder weakening equality: `fden EI (lift 0 1 e) (fpush P Φ) = fden EI e Φ`. -/
theorem fden_lift0_one (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (P : LTShape → Prop) (e : Expr Nat) :
    fden EI (lift 0 1 e) (fpush P Φ) = fden EI e Φ := by
  rw [fden_lift, fliftVal_zero_one_fpush]

/-- **Exact two-way substitution for `fden`:**
`fden EI (instantiate j rep e) Φ` equals `fden EI e (finsert j (fden EI rep Φ) Φ)` for
all expressions `e, rep : Expr Nat` and all filter valuations `Φ`. -/
theorem fden_instantiate (EI : Nat → List Level → LTShape → Prop) (e : Expr Nat) :
    ∀ (Φ : FValuation) (j : Nat) (rep : Expr Nat),
      fden EI (instantiate j rep e) Φ =
        fden EI e (finsert j (fden EI rep Φ) Φ) := by
  induction e with
  | bvar i =>
    intro Φ j rep
    simp only [instantiate]
    by_cases h1 : i = j
    · rw [if_pos h1]
      simp only [fden, finsert, if_pos h1]
      exact (fdown_fden EI rep Φ).symm
    · rw [if_neg h1]
      by_cases h2 : j < i
      · rw [if_pos h2]
        simp only [fden, finsert, if_neg h1, if_pos h2]
      · rw [if_neg h2]
        simp only [fden, finsert, if_neg h1, if_neg h2]
  | sort _ => intro _ _ _; rfl
  | const _ _ => intro _ _ _; rfl
  | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro Φ j rep
    simp only [instantiate, fden, ihf Φ j rep, iha Φ j rep]
  | lam A b _ ihb =>
    intro Φ j rep
    funext m
    simp only [instantiate, fden]
    have hbody : ∀ (n : Nat) (x y : LSh n),
        fden EI (instantiate (j + 1) (lift 0 1 rep) b)
          (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ =
          fden EI b (fpush (fun s => LeT s ⟨n, x⟩)
            (finsert j (fden EI rep Φ) Φ)) ⟨n, y⟩ := by
      intro n x y
      rw [ihb (fpush (fun s => LeT s ⟨n, x⟩) Φ) (j + 1) (lift 0 1 rep),
        fden_lift0_one, finsert_succ_fpush]
    simp only [hbody]
  | pi A B ihA ihB =>
    intro Φ j rep
    funext m
    simp only [instantiate, fden, ihA Φ j rep]
    have hbody : ∀ (n : Nat) (x y : LSh n),
        fden EI (instantiate (j + 1) (lift 0 1 rep) B)
          (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ =
          fden EI B (fpush (fun s => LeT s ⟨n, x⟩)
            (finsert j (fden EI rep Φ) Φ)) ⟨n, y⟩ := by
      intro n x y
      rw [ihB (fpush (fun s => LeT s ⟨n, x⟩) Φ) (j + 1) (lift 0 1 rep),
        fden_lift0_one, finsert_succ_fpush]
    simp only [hbody]
  | letE A v b _ ihv ihb =>
    intro Φ j rep
    simp only [instantiate, fden, ihv Φ j rep]
    rw [ihb (fpush (fden EI v (finsert j (fden EI rep Φ) Φ)) Φ) (j + 1) (lift 0 1 rep),
      fden_lift0_one, finsert_succ_fpush]

/-- Index-0 exact substitution: `fden EI (instantiate0 v body) Φ = fden EI body (fpush (fden EI v Φ) Φ)`. -/
theorem fden_instantiate0 (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (v body : Expr Nat) :
    fden EI (instantiate0 v body) Φ = fden EI body (fpush (fden EI v Φ) Φ) := by
  rw [instantiate0, fden_instantiate, finsert_zero]

/-- **Unconditional two-way `ConvT.zeta` soundness in `fden`:**
`fden EI (.letE A v body) Φ` is propositionally equal to `fden EI (instantiate0 v body) Φ`
for all `EI, Φ, A, v, body`. -/
theorem fden_zeta (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (A v body : Expr Nat) :
    fden EI (.letE A v body) Φ = fden EI (instantiate0 v body) Φ :=
  (fden_instantiate0 EI Φ v body).symm

/-- **Unconditional `ConvT.beta` left-to-right soundness in `fden`:**
every compact lower bound of `.app (.lam A body) arg` is a lower bound of
`instantiate0 arg body`. -/
theorem fden_beta_lhs {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A body arg : Expr Nat} {m : LTShape}
    (H : fden EI (.app (.lam A body) arg) Φ m) :
    fden EI (instantiate0 arg body) Φ m := by
  rcases H with hm | ⟨tf, ta, hlam, harg, happ⟩
  · exact fden_of_isBotT hm
  · rcases happ with ⟨n, fg, x, y, rfl, hxy, hxa, hmy⟩
    rcases hlam with ⟨k, hbot⟩ | ⟨n', f₀, hb, hle⟩
    · exact False.elim (not_lamT_eq_botT hbot)
    · have hn : n + 1 = n' + 1 := hle.1
      have hn' : n = n' := Nat.succ.inj hn
      subst hn'
      have hfg : DShapeFun.LEP (DShape.LEP eqN) fg.1 f₀.1 := hle.2
      obtain ⟨⟨u, v⟩, huv, hux, hyv⟩ := hfg (x.1, y.1) hxy
      have hwu : DShape.WF u := (f₀.2.1.entries (u, v) huv).1
      have hwv : DShape.WF v := (f₀.2.1.entries (u, v) huv).2
      let uL : LSh n := ⟨u, hwu⟩
      let vL : LSh n := ⟨v, hwv⟩
      have hbody_u : fden EI body (fpush (fun s => LeT s ⟨n, uL⟩) Φ) ⟨n, vL⟩ :=
        hb uL vL huv
      have hux_le : LeT ⟨n, uL⟩ ⟨n, x⟩ := ⟨rfl, hux⟩
      have hu_arg : fden EI arg Φ ⟨n, uL⟩ :=
        fden_mono harg (LeT.trans hux_le hxa)
      have hval_le : FValLe (fpush (fun s => LeT s ⟨n, uL⟩) Φ)
          (fpush (fden EI arg Φ) Φ) :=
        FValLe.fpush (fun _ hs => fden_mono hu_arg hs) (FValLe.refl Φ)
      have hbody_arg : fden EI body (fpush (fden EI arg Φ) Φ) ⟨n, vL⟩ :=
        fden_mono_val body hval_le hbody_u
      have hyv_le : LeT ⟨n, y⟩ ⟨n, vL⟩ := ⟨rfl, hyv⟩
      have hm_arg : fden EI body (fpush (fden EI arg Φ) Φ) m :=
        fden_mono hbody_arg (LeT.trans hmy hyv_le)
      rw [fden_instantiate0]
      exact hm_arg

/-! ### 8.3 Concrete Repairs of Admitted Obstructions 4a and 4b in `fden` -/

theorem fden_pi_botWFun {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {n : Nat} {a : LSh n} {A B : Expr Nat}
    (hA : fden EI A Φ ⟨n, a⟩) :
    fden EI (.pi A B) Φ (piT a (botWFun n)) := by
  refine Or.inr ⟨n, a, botWFun n, hA, ?_, LeT.refl _⟩
  intro x y hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hy' : (⟨n, y⟩ : LTShape) = botT n :=
    congrArg (Sigma.mk n) (Subtype.ext hxy'.2)
  rw [hy']
  exact fden_bot B _ n

theorem fden_zetaBetaObsInnerPi (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (B : Expr Nat) :
    fden EI (.pi zetaBetaObsVal B) Φ (piT zetaBetaObsP1 (botWFun 1)) :=
  fden_pi_botWFun (a := zetaBetaObsP1) (fden_pi_botWFun (a := (WShape.bot : LSh 0))
    (fden_bot (.sort .zero) Φ 0))

theorem fden_instantiate_zetaBetaObs (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) :
    fden EI (instantiate0 zetaBetaObsVal zetaBetaObsBody) Φ zetaBetaObsM := by
  change fden EI (.pi zetaBetaObsVal (.pi zetaBetaObsVal (.sort .zero))) Φ
    (piT zetaBetaObsP2 constInnerPiWFun)
  have hp2 : fden EI zetaBetaObsVal Φ ⟨2, zetaBetaObsP2⟩ :=
    fden_pi_botWFun (a := (WShape.bot : LSh 1)) (fden_bot (.sort .zero) Φ 1)
  refine Or.inr ⟨2, zetaBetaObsP2, constInnerPiWFun, hp2, ?_, LeT.refl _⟩
  intro x y hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hy' : (⟨2, y⟩ : LTShape) = piT zetaBetaObsP1 (botWFun 1) :=
    congrArg (Sigma.mk 2) (Subtype.ext hxy'.2)
  rw [hy']
  exact fden_zetaBetaObsInnerPi EI (fpush (fun s => LeT s ⟨2, x⟩) Φ) (.sort .zero)

/-- **Repair of Admitted Obstruction 4b (`fden_letE_zetaBetaObs`):**
Whereas `¬ Interp EI ρ zetaBetaObsM (.letE A zetaBetaObsVal zetaBetaObsBody)` holds on
`RcicModelShape.Interp` (`not_interp_letE_zetaBetaObs`, `zeta_unsound_interp`), in `fden`
the multi-level let-redex `.letE A zetaBetaObsVal zetaBetaObsBody` has the exact same
denotation as its contractum and is approximated by `zetaBetaObsM`. -/
theorem fden_letE_zetaBetaObs (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (A : Expr Nat) :
    fden EI (.letE A zetaBetaObsVal zetaBetaObsBody) Φ zetaBetaObsM := by
  rw [fden_zeta]
  exact fden_instantiate_zetaBetaObs EI Φ

/-- Graph `[(⊥, ⊥), (lamT (botWFun 0), lamT (botWFun 0))]` at level 2. -/
def idBotLamList : DShapeFun Level 1 :=
  [(DShape.bot, DShape.bot), ((lamT (botWFun 0)).2.1, (lamT (botWFun 0)).2.1)]

theorem wf_idBotLamWFun :
    DShape.WF (α := Level) (n := 2) (.lam idBotLamList) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨(DShape.bot, DShape.bot), List.mem_cons_self _ _, rfl, rfl⟩⟩
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨DShape.wf_bot, DShape.wf_bot⟩
    · rcases List.mem_singleton.1 hp with rfl
      exact ⟨(lamT (botWFun 0)).2.2, (lamT (botWFun 0)).2.2⟩
  · intro x hx y hy _
    rcases List.mem_cons.1 hx with rfl | hx <;>
      rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨(DShape.bot, DShape.bot), List.mem_cons_self _ _, rfl, rfl, rfl⟩
    · rcases List.mem_singleton.1 hy with rfl
      exact ⟨((lamT (botWFun 0)).2.1, (lamT (botWFun 0)).2.1),
        List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
    · rcases List.mem_singleton.1 hx with rfl
      exact ⟨((lamT (botWFun 0)).2.1, (lamT (botWFun 0)).2.1),
        List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
    · rcases List.mem_singleton.1 hx with rfl
      rcases List.mem_singleton.1 hy with rfl
      exact ⟨((lamT (botWFun 0)).2.1, (lamT (botWFun 0)).2.1),
        List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl, rfl⟩

/-- The step-function graph `idBotLamWFun : WFun 1` mapping `lamT (botWFun 0)` to itself. -/
def idBotLamWFun : WFun 1 := ⟨idBotLamList, wf_idBotLamWFun⟩

theorem fden_lam_botWFun {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} (n : Nat) (A b : Expr Nat) :
    fden EI (.lam A b) Φ (lamT (botWFun n)) := by
  refine Or.inr ⟨n, botWFun n, ?_, LeT.refl _⟩
  intro x y hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hy' : (⟨n, y⟩ : LTShape) = botT n :=
    congrArg (Sigma.mk n) (Subtype.ext hxy'.2)
  rw [hy']
  exact fden_bot b _ n

theorem fden_lam_idBotLamWFun (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (A : Expr Nat) :
    fden EI (.lam A (.bvar 0)) Φ (lamT idBotLamWFun) := by
  refine Or.inr ⟨1, idBotLamWFun, ?_, LeT.refl _⟩
  intro x y hxy
  rcases List.mem_cons.1 hxy with hbot | hlam
  · have hxy' := Prod.mk.inj hbot
    have hy' : (⟨1, y⟩ : LTShape) = botT 1 :=
      congrArg (Sigma.mk 1) (Subtype.ext hxy'.2)
    rw [hy']
    exact fden_bot (.bvar 0) _ 1
  · have hxy' := Prod.mk.inj (List.mem_singleton.1 hlam)
    have hxy_eq : (⟨1, y⟩ : LTShape) = ⟨1, x⟩ :=
      congrArg (Sigma.mk 1) (Subtype.ext (hxy'.2.trans hxy'.1.symm))
    rw [hxy_eq]
    exact Or.inr ⟨⟨1, x⟩, LeT.refl ⟨1, x⟩, LeT.refl ⟨1, x⟩⟩

theorem appLe_idBotLamWFun :
    AppLe (lamT idBotLamWFun) (lamT (botWFun 0)) (lamT (botWFun 0)) :=
  ⟨1, idBotLamWFun, (lamT (botWFun 0)).2, (lamT (botWFun 0)).2, rfl,
    List.mem_cons_of_mem _ (List.mem_singleton_self _),
    LeT.refl (lamT (botWFun 0)), LeT.refl (lamT (botWFun 0))⟩

/-- **Repair of Admitted Obstruction 4a (`fden_app_lam_pi_bvar0_lam`):**
Whereas `(λ (f : Π D, C). f) (λ D'. b)` is `BotOnly` on `RcicModelShape.Interp`
(`botOnly_app_lam_pi_bvar0_lam`, `beta_linear_unsound_interp`), in `fden` it has the
non-bottom lower bound `lamT (botWFun 0)` matching its contractum `λ D'. b`. -/
theorem fden_app_lam_pi_bvar0_lam (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (D C D' b : Expr Nat) :
    fden EI (.app (.lam (.pi D C) (.bvar 0)) (.lam D' b)) Φ (lamT (botWFun 0)) :=
  Or.inr ⟨lamT idBotLamWFun, lamT (botWFun 0),
    fden_lam_idBotLamWFun EI Φ (.pi D C),
    fden_lam_botWFun 0 D' b,
    appLe_idBotLamWFun⟩

/-! ### 8.4 `FSEq`, Injective Π-Interpretation, Concrete `FZetaValOK`, and 18-Constructor Fundamental Lemma -/

/-- Semantic equality of filter denotations: `M` and `N` have the same compact lower bounds
under filter valuation `Φ`. -/
def FSEq (EI : Nat → List Level → LTShape → Prop) (Φ : FValuation)
    (M N : Expr Nat) : Prop :=
  ∀ m : LTShape, fden EI M Φ m ↔ fden EI N Φ m

theorem fseq_iff_eq {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {M N : Expr Nat} :
    FSEq EI Φ M N ↔ fden EI M Φ = fden EI N Φ :=
  ⟨fun h => funext fun m => propext (h m), fun h _ => h ▸ Iff.rfl⟩

theorem FSEq.refl {EI : Nat → List Level → LTShape → Prop} {Φ : FValuation}
    (M : Expr Nat) : FSEq EI Φ M M :=
  fun _ => Iff.rfl

theorem FSEq.symm {EI : Nat → List Level → LTShape → Prop} {Φ : FValuation}
    {M N : Expr Nat} (h : FSEq EI Φ M N) : FSEq EI Φ N M :=
  fun m => (h m).symm

theorem FSEq.trans {EI : Nat → List Level → LTShape → Prop} {Φ : FValuation}
    {M N P : Expr Nat} (h1 : FSEq EI Φ M N) (h2 : FSEq EI Φ N P) : FSEq EI Φ M P :=
  fun m => (h1 m).trans (h2 m)

theorem fden_pi_dom_inv {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {n : Nat} {a : LSh n} {f : WFun n} {A B : Expr Nat}
    (H : fden EI (.pi A B) Φ (piT a f)) :
    fden EI A Φ ⟨n, a⟩ := by
  rcases H with ⟨k, hbot⟩ | ⟨n', a₀, _, hA₀, _, hle⟩
  · exact False.elim (not_piT_eq_botT hbot)
  · have hn : n + 1 = n' + 1 := hle.1
    have hn' : n = n' := Nat.succ.inj hn
    subst hn'
    have ha : LeT ⟨n, a⟩ ⟨n, a₀⟩ := ⟨rfl, hle.2.1⟩
    exact fden_mono hA₀ ha

/-- **Unconditional Π-domain injectivity on `FSEq`:**
`FSEq EI Φ (.pi A B) (.pi A' B')` implies `FSEq EI Φ A A'`. -/
theorem fseq_pi_dom_inv {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A B A' B' : Expr Nat}
    (h : FSEq EI Φ (.pi A B) (.pi A' B')) :
    FSEq EI Φ A A' := by
  rintro ⟨n, a⟩
  constructor
  · intro hA
    exact fden_pi_dom_inv ((h (piT a (botWFun n))).1 (fden_pi_botWFun hA))
  · intro hA'
    exact fden_pi_dom_inv ((h (piT a (botWFun n))).2 (fden_pi_botWFun hA'))

/-- **Unconditional sort injectivity on `FSEq`:**
`FSEq EI Φ (.sort u) (.sort v)` implies `eqN u v`. -/
theorem fseq_sort_inv {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {u v : Level}
    (h : FSEq EI Φ (.sort u) (.sort v)) :
    eqN u v := by
  have hu : fden EI (.sort v) Φ (sortT u) :=
    (h (sortT u)).1 (Or.inr (LeT.refl (sortT u)))
  rcases hu with ⟨k, hbot⟩ | hle
  · exact False.elim (not_sortT_eq_botT hbot)
  · exact sortT_leT_iff.1 hle

/-- **Unconditional Π/sort disjointness on `FSEq`:**
`.pi A B` and `.sort u` are never `FSEq`-equivalent. -/
theorem not_fseq_pi_sort {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A B : Expr Nat} {u : Level} :
    ¬ FSEq EI Φ (.pi A B) (.sort u) := by
  intro h
  have hpi : fden EI (.pi A B) Φ (piT (WShape.bot : LSh 0) (botWFun 0)) :=
    fden_pi_botWFun (fden_bot A Φ 0)
  have hsort : fden EI (.sort u) Φ (piT (WShape.bot : LSh 0) (botWFun 0)) :=
    (h _).1 hpi
  rcases hsort with ⟨k, hbot⟩ | hle
  · exact not_piT_eq_botT hbot
  · exact not_leT_piT_sortT hle

theorem fden_pi_constSortWFun {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {u : Level} {A B : Expr Nat}
    (hB : fden EI B (fpush (fun s => LeT s (botT 0)) Φ) (sortT u)) :
    fden EI (.pi A B) Φ (piT (WShape.bot : LSh 0) (constSortWFun u)) := by
  refine Or.inr ⟨0, WShape.bot, constSortWFun u, fden_bot A Φ 0, ?_, LeT.refl _⟩
  intro x y hxy
  have hxy' := Prod.mk.inj (List.mem_singleton.1 hxy)
  have hx' : (⟨0, x⟩ : LTShape) = botT 0 :=
    congrArg (Sigma.mk 0) (Subtype.ext hxy'.1)
  have hy' : (⟨0, y⟩ : LTShape) = sortT u :=
    congrArg (Sigma.mk 0) (Subtype.ext hxy'.2)
  rw [hx', hy']
  exact hB

theorem fden_pi_cod_sort_inv {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {u : Level} {A B : Expr Nat}
    (H : fden EI (.pi A B) Φ (piT (WShape.bot : LSh 0) (constSortWFun u))) :
    fden EI B (fpush (fun s => LeT s (botT 0)) Φ) (sortT u) := by
  rcases H with ⟨k, hbot⟩ | ⟨n', _, f₀, _, hb, hle⟩
  · exact False.elim (not_piT_eq_botT hbot)
  · have hn : 1 = n' + 1 := hle.1
    have hn' : 0 = n' := Nat.succ.inj hn
    subst hn'
    have hfg : DShapeFun.LEP (DShape.LEP eqN) (constSortWFun u).1 f₀.1 := hle.2.2
    obtain ⟨⟨u₀, v₀⟩, huv, hbotu, hsortv⟩ :=
      hfg (DShape0.bot, DShape0.sort u) (List.mem_singleton_self _)
    have hwu : DShape.WF u₀ := (f₀.2.1.entries (u₀, v₀) huv).1
    have hwv : DShape.WF v₀ := (f₀.2.1.entries (u₀, v₀) huv).2
    have hu_eq : u₀ = DShape0.bot := DShape0.LEP.le_bot hbotu
    have hu_bot : (⟨0, u₀, hwu⟩ : LTShape) = botT 0 :=
      congrArg (Sigma.mk 0) (Subtype.ext hu_eq)
    have hbody : fden EI B (fpush (fun s => LeT s ⟨0, u₀, hwu⟩) Φ) ⟨0, v₀, hwv⟩ :=
      hb ⟨u₀, hwu⟩ ⟨v₀, hwv⟩ huv
    rw [hu_bot] at hbody
    have hsort_v : LeT (sortT u) ⟨0, v₀, hwv⟩ := ⟨rfl, hsortv⟩
    exact fden_mono hbody hsort_v

/-- **Unconditional Π-codomain sort-probe injectivity on `FSEq`:**
if `.pi A B` and `.pi A' B'` are `FSEq`-equivalent under `Φ`, then `B` and `B'` have the
same `sortT u` lower bounds under `fpush (LeT · (botT 0)) Φ`. -/
theorem fseq_pi_cod_sort_iff {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A B A' B' : Expr Nat}
    (h : FSEq EI Φ (.pi A B) (.pi A' B')) (u : Level) :
    fden EI B (fpush (fun s => LeT s (botT 0)) Φ) (sortT u) ↔
      fden EI B' (fpush (fun s => LeT s (botT 0)) Φ) (sortT u) :=
  ⟨fun hB => fden_pi_cod_sort_inv ((h _).1 (fden_pi_constSortWFun hB)),
   fun hB' => fden_pi_cod_sort_inv ((h _).2 (fden_pi_constSortWFun hB'))⟩

theorem fseq_pi_cod_sort_inv {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A A' : Expr Nat} {u v : Level}
    (h : FSEq EI Φ (.pi A (.sort u)) (.pi A' (.sort v))) :
    eqN u v := by
  have hsort : fden EI (.sort v) (fpush (fun s => LeT s (botT 0)) Φ) (sortT u) :=
    (fseq_pi_cod_sort_iff h u).1 (Or.inr (LeT.refl (sortT u)))
  rcases hsort with ⟨k, hbot⟩ | hle
  · exact False.elim (not_sortT_eq_botT hbot)
  · exact sortT_leT_iff.1 hle

/-- `ConvT.sorts` is unconditionally sound for `FSEq`. -/
theorem fseq_sorts {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {l₁ l₂ : Level} (h : eqN l₁ l₂) :
    FSEq EI Φ (.sort l₁) (.sort l₂) := by
  intro m
  constructor
  · rintro (hm | hle)
    · exact Or.inl hm
    · exact Or.inr (LeT.trans hle (sortT_leT_iff.2 h))
  · rintro (hm | hle)
    · exact Or.inl hm
    · have hsymm : eqN l₂ l₁ := fun r => (h r).symm
      exact Or.inr (LeT.trans hle (sortT_leT_iff.2 hsymm))

/-- `ConvT.consts` is unconditionally sound for `FSEq` under `EIConsts EI`. -/
theorem fseq_consts {EI : Nat → List Level → LTShape → Prop}
    (hEI : EIConsts EI) {Φ : FValuation} {r : Nat} {ls₁ ls₂ : List Level}
    (h : eqNList ls₁ ls₂) :
    FSEq EI Φ (.const r ls₁) (.const r ls₂) := by
  intro m
  constructor
  · rintro (hm | ⟨u, hu, hmu⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨u, (hEI r ls₁ ls₂ u h).1 hu, hmu⟩
  · rintro (hm | ⟨u, hu, hmu⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨u, (hEI r ls₁ ls₂ u h).2 hu, hmu⟩

/-- `ConvT.lit` is unconditionally sound for `FSEq`. -/
theorem fseq_lit {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {t : Nat} {exp : Expr Nat}
    (h : LiteralExpansion t exp) :
    FSEq EI Φ (.lit t) exp := by
  cases h with
  | of =>
    rw [fseq_iff_eq]
    exact (fden_natExpand EI Φ t).symm

/-- `ConvT.app` congruence is unconditionally sound for `FSEq`. -/
theorem fseq_app {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {f g a b : Expr Nat}
    (hfg : FSEq EI Φ f g) (hab : FSEq EI Φ a b) :
    FSEq EI Φ (.app f a) (.app g b) := by
  rw [fseq_iff_eq] at hfg hab ⊢
  simp only [fden, hfg, hab]

/-- `ConvT.lam` congruence is unconditionally sound for `FSEq`. -/
theorem fseq_lam {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A A' b b' : Expr Nat}
    (hb : ∀ (n : Nat) (x : LSh n), FSEq EI (fpush (fun s => LeT s ⟨n, x⟩) Φ) b b') :
    FSEq EI Φ (.lam A b) (.lam A' b') := by
  rw [fseq_iff_eq]
  funext m
  simp only [fden]
  have hbody : ∀ (n : Nat) (x y : LSh n),
      fden EI b (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ =
        fden EI b' (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ :=
    fun n x y => propext (hb n x ⟨n, y⟩)
  simp only [hbody]

/-- `ConvT.pi` congruence is unconditionally sound for `FSEq`. -/
theorem fseq_pi {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A A' B B' : Expr Nat}
    (hA : FSEq EI Φ A A')
    (hB : ∀ (n : Nat) (x : LSh n), FSEq EI (fpush (fun s => LeT s ⟨n, x⟩) Φ) B B') :
    FSEq EI Φ (.pi A B) (.pi A' B') := by
  rw [fseq_iff_eq] at hA ⊢
  funext m
  simp only [fden, hA]
  have hbody : ∀ (n : Nat) (x y : LSh n),
      fden EI B (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ =
        fden EI B' (fpush (fun s => LeT s ⟨n, x⟩) Φ) ⟨n, y⟩ :=
    fun n x y => propext (hB n x ⟨n, y⟩)
  simp only [hbody]

/-- `ConvT.letE` congruence is unconditionally sound for `FSEq`. -/
theorem fseq_letE {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {A A' v v' b b' : Expr Nat}
    (hv : FSEq EI Φ v v')
    (hb : FSEq EI (fpush (fden EI v Φ) Φ) b b') :
    FSEq EI Φ (.letE A v b) (.letE A' v' b') := by
  rw [fseq_iff_eq] at hv hb ⊢
  simp only [fden, ← hv, hb]

/-- **Unconditional `ConvT.zeta` soundness for `FSEq`:**
`FSEq EI Φ (.letE A v body) (instantiate0 v body)` holds for all `A, v, body`. -/
theorem fseq_zeta (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (A v body : Expr Nat) :
    FSEq EI Φ (.letE A v body) (instantiate0 v body) :=
  fseq_iff_eq.2 (fden_zeta EI Φ A v body)

/-- Under `fpush (fden EI v Φ) Φ`, `.bvar 0` and `lift 0 1 v` are unconditionally
`FSEq`-equivalent for every `v : Expr Nat`. -/
theorem fseq_bvar0_lift0_one (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) (v : Expr Nat) :
    FSEq EI (fpush (fden EI v Φ) Φ) (.bvar 0) (lift 0 1 v) := by
  rw [fseq_iff_eq, fden_lift0_one]
  exact fdown_fden EI v Φ

/-- Under-binder `FSEq` weakening (`fpush P Φ` ↔ `lift 0 1`). -/
theorem fseq_lift0_one_iff {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {P : LTShape → Prop} {M N : Expr Nat} :
    FSEq EI (fpush P Φ) (lift 0 1 M) (lift 0 1 N) ↔ FSEq EI Φ M N := by
  rw [fseq_iff_eq, fseq_iff_eq, fden_lift0_one, fden_lift0_one]

/-- Concrete inductive context-valuation compatibility for `fden`:
- `nil`: any filter valuation `Φ` is valid in `[]`.
- `assumption`: pushing any filter `P` preserves validity under `.assumption A`.
- `letBinding`: pushing `fden EI v Φ` preserves validity under `.letBinding A v`. -/
inductive FZetaValOK (EI : Nat → List Level → LTShape → Prop) :
    LCtx → FValuation → Prop where
  | nil {Φ : FValuation} :
      FZetaValOK EI [] Φ
  | assumption {Γ : LCtx} {Φ : FValuation} (A : Expr Nat) (P : LTShape → Prop) :
      FZetaValOK EI Γ Φ →
      FZetaValOK EI (.assumption A :: Γ) (fpush P Φ)
  | letBinding {Γ : LCtx} {Φ : FValuation} (A v : Expr Nat) :
      FZetaValOK EI Γ Φ →
      FZetaValOK EI (.letBinding A v :: Γ) (fpush (fden EI v Φ) Φ)

/-- Canonical default filter valuation for any context `Γ : LCtx`. -/
def fdefaultVal (EI : Nat → List Level → LTShape → Prop) : LCtx → FValuation
  | [] => fun _ => IsBotT
  | .assumption _ :: Γ => fpush IsBotT (fdefaultVal EI Γ)
  | .letBinding _ v :: Γ => fpush (fden EI v (fdefaultVal EI Γ)) (fdefaultVal EI Γ)

/-- Every context `Γ : LCtx` inhabits `FZetaValOK EI Γ` via `fdefaultVal EI Γ`. -/
theorem fzetaValOK_default (EI : Nat → List Level → LTShape → Prop) :
    ∀ Γ : LCtx, FZetaValOK EI Γ (fdefaultVal EI Γ)
  | [] => .nil
  | .assumption A :: Γ => .assumption A IsBotT (fzetaValOK_default EI Γ)
  | .letBinding A v :: Γ => .letBinding A v (fzetaValOK_default EI Γ)

/-- **Unconditional `ConvT.zetaLocal` soundness under `FZetaValOK`:**
every let-bound variable `i` in `Γ` with `lookupValue Γ i = some val` is `FSEq`-equivalent
to `val` under any `Φ` satisfying `FZetaValOK EI Γ Φ`. -/
theorem fseq_zetaLocal_of_fzetaValOK {EI : Nat → List Level → LTShape → Prop}
    {Γ : LCtx} {Φ : FValuation} (hok : FZetaValOK EI Γ Φ) :
    ∀ {i : Nat} {val : Expr Nat},
      lookupValue Γ i = some val → FSEq EI Φ (.bvar i) val := by
  induction hok with
  | nil =>
    intro i _ h
    cases i <;> exact Option.noConfusion h
  | assumption A P _ ih =>
    intro i v h
    cases i with
    | zero => exact Option.noConfusion h
    | succ j =>
      rw [lookupValue_cons_succ] at h
      cases hlookup : lookupValue _ j with
      | none =>
        rw [hlookup] at h
        exact Option.noConfusion h
      | some v₀ =>
        rw [hlookup, Option.map] at h
        injection h with hv
        subst hv
        have hlift : (Expr.bvar (j + 1) : Expr Nat) = lift 0 1 (.bvar j) := by
          simp [lift]
        rw [hlift, fseq_lift0_one_iff]
        exact ih hlookup
  | letBinding A v _ ih =>
    intro i val h
    cases i with
    | zero =>
      rw [lookupValue_cons_letBinding_zero] at h
      injection h with hval
      subst hval
      exact fseq_bvar0_lift0_one EI _ v
    | succ j =>
      rw [lookupValue_cons_succ] at h
      cases hlookup : lookupValue _ j with
      | none =>
        rw [hlookup] at h
        exact Option.noConfusion h
      | some v₀ =>
        rw [hlookup, Option.map] at h
        injection h with hv
        subst hv
        have hlift : (Expr.bvar (j + 1) : Expr Nat) = lift 0 1 (.bvar j) := by
          simp [lift]
        rw [hlift, fseq_lift0_one_iff]
        exact ih hlookup

/-- Named right-to-left β-gap for `fden` (repaired for untyped `.lam` on identity/constant
redexes by `fden_app_lam_pi_bvar0_lam`, remaining only for non-linear multi-entry join
graphs). -/
def FBetaRhsGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (FValOK : LCtx → FValuation → Prop) : Prop :=
  ∀ {Γ A B body a u},
    HasTyT E n Γ A (.sort u) →
    HasTyT E n (.assumption A :: Γ) body B →
    HasTyT E n Γ a A →
    ∀ {Φ}, FValOK Γ Φ →
    ∀ {m}, fden EI (instantiate0 a body) Φ m → fden EI (.app (.lam A body) a) Φ m

/-- Named gap for `ConvT.iota` on `FSEq`. -/
def FIotaSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (FValOK : LCtx → FValuation → Prop) : Prop :=
  ∀ {Γ lhs rhs T},
    DerivedIota E lhs rhs →
    HasTyT E n Γ lhs T →
    HasTyT E n Γ rhs T →
    ∀ {Φ}, FValOK Γ Φ → FSEq EI Φ lhs rhs

/-- Named gap for `ConvT.eta` on `FSEq`. -/
def FEtaSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (FValOK : LCtx → FValuation → Prop) : Prop :=
  ∀ {Γ f A B},
    HasTyT E n Γ f (.pi A B) →
    ∀ {Φ}, FValOK Γ Φ → FSEq EI Φ (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- Named gap for `ConvT.irr` on `FSEq`. -/
def FIrrSemGap (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop)
    (FValOK : LCtx → FValuation → Prop) : Prop :=
  ∀ {Γ P p q},
    HasTyT E n Γ P (.sort .zero) →
    HasTyT E n Γ p P →
    HasTyT E n Γ q P →
    ∀ {Φ}, FValOK Γ Φ → FSEq EI Φ p q

/-- Model supply for the 18-constructor Fundamental Lemma on `FSEq` under `FZetaValOK EI`:
both `ZetaRhsGap` and `ZetaLocalSemGap` are **completely eliminated** (discharged
unconditionally by `fseq_zeta` and `fseq_zetaLocal_of_fzetaValOK`). -/
structure FSEqModelSupply (E : ResolvedEnv) (n : Nat)
    (EI : Nat → List Level → LTShape → Prop) : Prop where
  consts : EIConsts EI
  delta : ∀ r ls m b, E.members r = some m → m.body = some b →
    transparent m.mclass = true → ∀ Φ, FSEq EI Φ (.const r ls) (instantiateLevels ls b)
  betaRhs : FBetaRhsGap E n EI (FZetaValOK EI)
  iota : FIotaSemGap E n EI (FZetaValOK EI)
  eta : FEtaSemGap E n EI (FZetaValOK EI)
  irr : FIrrSemGap E n EI (FZetaValOK EI)

/-- **18-constructor Fundamental Lemma for `ConvT` on `FSEq` (with `FZetaValOK`):**
`ConvT.zeta` and `ConvT.zetaLocal` are discharged unconditionally without gap fields. -/
theorem fundamental_convT_fseq {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    (M : FSEqModelSupply E n EI)
    {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    ∀ {Φ : FValuation}, FZetaValOK EI Γ Φ → FSEq EI Φ a b :=
  match h with
  | .refl _ a _ _ => fun _ => FSEq.refl a
  | .symm _ _ _ _ h1 => fun hΦ => FSEq.symm (fundamental_convT_fseq M h1 hΦ)
  | .trans _ _ _ _ _ h1 h2 =>
      fun hΦ => FSEq.trans (fundamental_convT_fseq M h1 hΦ) (fundamental_convT_fseq M h2 hΦ)
  | .beta _ _ _ _ _ _ hA hbody harg =>
      fun hΦ _ => ⟨fden_beta_lhs, M.betaRhs hA hbody harg hΦ⟩
  | .zeta _ A v body _ _ _ _ _ =>
      fun _ => fseq_zeta EI _ A v body
  | .zetaLocal _ _ _ _ hval _ _ =>
      fun hΦ => fseq_zetaLocal_of_fzetaValOK hΦ hval
  | .delta _ r ls m b hres hbody htr _ _ _ =>
      fun _ => M.delta r ls m b hres hbody htr _
  | .iota _ _ _ _ hiota hlhs hrhs =>
      fun hΦ => M.iota hiota hlhs hrhs hΦ
  | .lit _ _ _ _ hlit _ =>
      fun _ => fseq_lit hlit
  | .app _ _ _ _ _ _ _ h1 h2 =>
      fun hΦ => fseq_app (fundamental_convT_fseq M h1 hΦ) (fundamental_convT_fseq M h2 hΦ)
  | .lam _ A _ _ _ _ _ _ hb =>
      fun hΦ => fseq_lam (fun k x =>
        fundamental_convT_fseq M hb (.assumption A (fun s => LeT s ⟨k, x⟩) hΦ))
  | .pi _ A _ _ _ _ _ hA hB =>
      fun hΦ => fseq_pi (fundamental_convT_fseq M hA hΦ) (fun k x =>
        fundamental_convT_fseq M hB (.assumption A (fun s => LeT s ⟨k, x⟩) hΦ))
  | .letE _ A _ v _ _ _ _ _ _ hv hb =>
      fun hΦ => fseq_letE (fundamental_convT_fseq M hv hΦ)
        (fundamental_convT_fseq M hb (.letBinding A v hΦ))
  | .sorts _ _ _ heq =>
      fun _ => fseq_sorts heq
  | .consts _ _ _ _ _ _ _ _ _ heq =>
      fun _ => fseq_consts M.consts heq
  | .eta _ _ _ _ hf =>
      fun hΦ => M.eta hf hΦ
  | .irr _ _ _ _ hP hp hq =>
      fun hΦ => M.irr hP hp hq hΦ
  | .tyConv _ _ _ _ _ _ h1 _ =>
      fun hΦ => fundamental_convT_fseq M h1 hΦ

/-- **Fundamental Lemma for `TyConvT` on `FSEq` (with `FZetaValOK`)**. -/
theorem fundamental_tyConvT_fseq {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    (M : FSEqModelSupply E n EI)
    {Γ : LCtx} {A B : Expr Nat}
    (h : TyConvT E n Γ A B) :
    ∀ {Φ : FValuation}, FZetaValOK EI Γ Φ → FSEq EI Φ A B :=
  match h with
  | .refl _ A => fun _ => FSEq.refl A
  | .of _ _ _ _ hc => fun hΦ => fundamental_convT_fseq M hc hΦ
  | .trans _ _ _ _ h1 h2 =>
      fun hΦ => FSEq.trans (fundamental_tyConvT_fseq M h1 hΦ) (fundamental_tyConvT_fseq M h2 hΦ)

/-- From `FSEqModelSupply`, `TyConvT (.sort u) (.sort v)` yields `eqN u v` in **every**
context `Γ : LCtx` (using `fzetaValOK_default EI Γ` — no external valuation witness needed!). -/
theorem sortRow_of_fseqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    (M : FSEqModelSupply E n EI)
    {Γ : LCtx} {u v : Level}
    (h : TyConvT E n Γ (.sort u) (.sort v)) :
    eqN u v :=
  fseq_sort_inv (fundamental_tyConvT_fseq M h (fzetaValOK_default EI Γ))

/-- From `FSEqModelSupply`, `TyConvT (.pi A B) (.pi A' B')` yields `FSEq EI Φ A A'`
for every `Φ` satisfying `FZetaValOK EI Γ Φ` (and in particular `fdefaultVal EI Γ`). -/
theorem piDomFSEq_of_fseqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    (M : FSEqModelSupply E n EI)
    {Γ : LCtx} {A B A' B' : Expr Nat}
    (h : TyConvT E n Γ (.pi A B) (.pi A' B'))
    {Φ : FValuation} (hΦ : FZetaValOK EI Γ Φ) :
    FSEq EI Φ A A' :=
  fseq_pi_dom_inv (fundamental_tyConvT_fseq M h hΦ)

/-- From `FSEqModelSupply`, `.pi A B` and `.sort u` are never `TyConvT`-convertible in
any context `Γ : LCtx` (using `fzetaValOK_default EI Γ`). -/
theorem not_tyConvT_pi_sort_of_fseqModel {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    (M : FSEqModelSupply E n EI)
    {Γ : LCtx} {A B : Expr Nat} {u : Level}
    (h : TyConvT E n Γ (.pi A B) (.sort u)) : False :=
  not_fseq_pi_sort (fundamental_tyConvT_fseq M h (fzetaValOK_default EI Γ))

/-! ### 8.5 Admitted Obstruction 5: Disjoint-Level Stratification in `RcicDomainShape` /
`RcicModelShape` Refutes Polymorphic Π-Returning β-Redexes Even in `fden` -/

/-- In `RcicModelShape.Interp`, because `sortT u` is hardcoded at level `0`
(`⟨0, ⟨.sort u, trivial⟩⟩`), any compact approximation of `.sort u` at a successor level
`n + 1 ≥ 1` is forced to be `botT (n + 1)` (`IsBotT`). -/
theorem isBotT_of_interp_sort_succ {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {n : Nat} {y : LSh (n + 1)} {u : Level}
    (H : Interp EI ρ ⟨n + 1, y⟩ (.sort u)) :
    IsBotT ⟨n + 1, y⟩ := by
  rcases Interp.le_sort H with ⟨k, hbot⟩ | hle
  · exact ⟨k, hbot⟩
  · exact False.elim (Nat.succ_ne_zero n hle.1)

/-- In `fden`, any compact approximation of `.sort u` at a successor level `n + 1 ≥ 1`
is forced to be `IsBotT`. -/
theorem isBotT_of_fden_sort_succ {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {n : Nat} {y : LSh (n + 1)} {u : Level}
    (H : fden EI (.sort u) Φ ⟨n + 1, y⟩) :
    IsBotT ⟨n + 1, y⟩ := by
  rcases H with hm | hle
  · exact hm
  · exact False.elim (Nat.succ_ne_zero n hle.1)

/-- In `RcicModelShape.Interp`, for any `A, B, arg, ρ` and any `a₀ : LSh k`, `g₀ : WFun k`,
if `piT a₀ g₀` approximates `.app (.lam A (.pi (.bvar 0) B)) arg`, then `IsBotT ⟨k, a₀⟩`
(`k = k + 1` level-stratification obstruction between `AppLe` and `piT`). -/
theorem interp_app_lam_pi_bvar0_dom_bot {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {k : Nat} {a₀ : LSh k} {g₀ : WFun k}
    {A B arg : Expr Nat}
    (H : Interp EI ρ (piT a₀ g₀) (.app (.lam A (.pi (.bvar 0) B)) arg)) :
    IsBotT ⟨k, a₀⟩ := by
  generalize hm : piT a₀ g₀ = m at H
  cases H with
  | bot =>
    exact False.elim (not_piT_eq_botT hm)
  | @app _ _ f a _ _ hlam _ happ =>
    rw [← hm] at happ
    rcases happ with ⟨n, fg, x, y, rfl, hxy, _, hmy⟩
    generalize htf : lamT fg = tf at hlam
    cases hlam with
    | bot =>
      exact False.elim (not_lamT_eq_botT htf)
    | @lam _ _ n' a_dom f₀ _ _ _ hdom hb hle_lam =>
      rw [← htf] at hle_lam
      have hn : n + 1 = n' + 1 := hle_lam.1
      have hn' : n = n' := Nat.succ.inj hn
      subst hn'
      have hfg : DShapeFun.LEP (DShape.LEP eqN) fg.1 f₀.1 := hle_lam.2
      obtain ⟨⟨u, v⟩, huv, _, hyv⟩ := hfg (x.1, y.1) hxy
      have hwu : DShape.WF u := (f₀.2.1.entries (u, v) huv).1
      have hwv : DShape.WF v := (f₀.2.1.entries (u, v) huv).2
      obtain ⟨x', y', hx'y', _, hvy', hx'a⟩ :=
        hdom n f₀ ⟨u, hwu⟩ ⟨v, hwv⟩ rfl huv
      have hyy' : LeT ⟨n, y⟩ ⟨n, y'⟩ :=
        ⟨rfl, DShape.LEP.trans (fun _ _ _ h1 h2 r => (h1 r).trans (h2 r)) hyv hvy'⟩
      have hmy' : LeT (piT a₀ g₀) ⟨n, y'⟩ :=
        LeT.trans hmy hyy'
      have hpi_x' : Interp EI (ρ.push ⟨n, x'⟩) (piT a₀ g₀) (.pi (.bvar 0) B) :=
        Interp.mono (hb x' y' hx'y' hx'a) hmy'
      have hbvar : Interp EI (ρ.push ⟨n, x'⟩) ⟨k, a₀⟩ (.bvar 0) :=
        interp_pi_dom_inv hpi_x'
      rcases Interp.le_bvar hbvar with hbot | hku
      · exact hbot
      · have hkn : k = n := hku.1
        have hkn1 : k + 1 = n := hmy'.1
        exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self k) (hkn.trans hkn1.symm))

/-- **Admitted Obstruction 5a (`fden_app_lam_pi_bvar0_dom_bot`):**
In `fden` (over `RcicModelShape`'s disjoint-level `LeT`), for any `A, B, arg, Φ` and any
`a₀ : LSh k`, `g₀ : WFun k`, if `piT a₀ g₀` approximates the type-returning β-redex
`.app (.lam A (.pi (.bvar 0) B)) arg`, then the domain shape `⟨k, a₀⟩` is forced to be
bottom (`IsBotT ⟨k, a₀⟩`), because `AppLe` binds `.bvar 0` at the output level `k + 1` of
`piT a₀ g₀` while `.pi (.bvar 0) B` evaluates its domain `.bvar 0` at level `k`, and
`LeT` across `k` and `k + 1` is impossible (`k ≠ k + 1`). -/
theorem fden_app_lam_pi_bvar0_dom_bot {EI : Nat → List Level → LTShape → Prop}
    {Φ : FValuation} {k : Nat} {a₀ : LSh k} {g₀ : WFun k}
    {A B arg : Expr Nat}
    (H : fden EI (.app (.lam A (.pi (.bvar 0) B)) arg) Φ (piT a₀ g₀)) :
    IsBotT ⟨k, a₀⟩ := by
  rcases H with ⟨j, hbot⟩ | ⟨tf, ta, hlam, _, happ⟩
  · exact False.elim (not_piT_eq_botT hbot)
  · rcases happ with ⟨n, fg, x, y, rfl, hxy, _, hmy⟩
    rcases hlam with ⟨j, hbot⟩ | ⟨n', f₀, hb, hle_lam⟩
    · exact False.elim (not_lamT_eq_botT hbot)
    · have hn : n + 1 = n' + 1 := hle_lam.1
      have hn' : n = n' := Nat.succ.inj hn
      subst hn'
      have hfg : DShapeFun.LEP (DShape.LEP eqN) fg.1 f₀.1 := hle_lam.2
      obtain ⟨⟨u, v⟩, huv, _, hyv⟩ := hfg (x.1, y.1) hxy
      have hwu : DShape.WF u := (f₀.2.1.entries (u, v) huv).1
      have hwv : DShape.WF v := (f₀.2.1.entries (u, v) huv).2
      let uL : LSh n := ⟨u, hwu⟩
      let vL : LSh n := ⟨v, hwv⟩
      have hmyv : LeT (piT a₀ g₀) ⟨n, vL⟩ :=
        LeT.trans hmy ⟨rfl, hyv⟩
      have hpi_u : fden EI (.pi (.bvar 0) B) (fpush (fun s => LeT s ⟨n, uL⟩) Φ) (piT a₀ g₀) :=
        fden_mono (hb uL vL huv) hmyv
      have hbvar : fden EI (.bvar 0) (fpush (fun s => LeT s ⟨n, uL⟩) Φ) ⟨k, a₀⟩ :=
        fden_pi_dom_inv hpi_u
      rcases hbvar with hbot | ⟨s, hsu, has⟩
      · exact hbot
      · have hku : LeT ⟨k, a₀⟩ ⟨n, uL⟩ := LeT.trans has hsu
        have hkn : k = n := hku.1
        have hkn1 : k + 1 = n := hmyv.1
        exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self k) (hkn.trans hkn1.symm))

/-- Polymorphic type-returning β-redex `(fun (X : Sort 1) => Π (_ : X), Sort 0) (Sort 0)`. -/
def polyPiBetaRedex : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.pi (.bvar 0) (.sort .zero))) (.sort .zero)

/-- Probe compact shape `piT (sortT .zero).2 (botWFun 0) : LTShape` at level 1. -/
def polyPiBetaProbe : LTShape :=
  piT (sortT .zero).2 (botWFun 0)

/-- `.sort (.succ .zero) : .sort (.succ (.succ .zero))` in any context `Γ`. -/
def hasTyT_polyPiBetaDom (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort Γ (.succ .zero)

/-- `.pi (.bvar 0) (.sort .zero) : .sort (.imax (.succ .zero) (.succ .zero))` in
`.assumption (.sort (.succ .zero)) :: Γ`. -/
def hasTyT_polyPiBetaBody (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n (.assumption (.sort (.succ .zero)) :: Γ)
      (.pi (.bvar 0) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  let Γ₁ : LCtx := .assumption (.sort (.succ .zero)) :: Γ
  let Γ₂ : LCtx := .assumption (.bvar 0) :: Γ₁
  .pi Γ₁ (.bvar 0) (.succ .zero) (.sort .zero) (.succ .zero)
    (.bvar Γ₁ 0 (.sort (.succ .zero)) rfl)
    (.sort Γ₂ .zero)

/-- `.sort .zero : .sort (.succ .zero)` in any context `Γ`. -/
def hasTyT_polyPiBetaArg (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sort Γ .zero

/-- `polyPiBetaProbe` approximates the β-contractum
`instantiate0 (.sort .zero) (.pi (.bvar 0) (.sort .zero)) = .pi (.sort .zero) (.sort .zero)`
in `fden`. -/
theorem fden_polyPiBetaContractum (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) :
    fden EI (instantiate0 (.sort .zero) (.pi (.bvar 0) (.sort .zero))) Φ polyPiBetaProbe :=
  fden_pi_botWFun (a := (sortT .zero).2) (Or.inr (LeT.refl (sortT .zero)))

/-- `polyPiBetaProbe` does **not** approximate `polyPiBetaRedex` in `fden` under any `EI`
and `Φ`. -/
theorem not_fden_polyPiBetaRedex (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) :
    ¬ fden EI polyPiBetaRedex Φ polyPiBetaProbe := by
  intro H
  obtain ⟨k, hbot⟩ := fden_app_lam_pi_bvar0_dom_bot H
  exact not_sortT_eq_botT hbot

/-- **Admitted Obstruction 5b (`polyPiBeta_unsound_fden`):**
Even in `fden` (after repairing Obstructions 4a and 4b), `RcicModelShape`'s disjoint-level
order `LeT` (`s.1 = t.1`) combined with `piT`'s level increment (`k ↦ k + 1`) makes
`polyPiBetaRedex` (`(fun (X : Sort 1) => Π (_ : X), Sort 0) (Sort 0)`) and its
β-contractum `Π (_ : Sort 0), Sort 0` non-equivalent in `FSEq` for all `EI` and `Φ`. -/
theorem polyPiBeta_unsound_fden (EI : Nat → List Level → LTShape → Prop)
    (Φ : FValuation) :
    fden EI (instantiate0 (.sort .zero) (.pi (.bvar 0) (.sort .zero))) Φ polyPiBetaProbe ∧
      ¬ fden EI polyPiBetaRedex Φ polyPiBetaProbe ∧
      ¬ FSEq EI Φ polyPiBetaRedex
        (instantiate0 (.sort .zero) (.pi (.bvar 0) (.sort .zero))) := by
  have hrhs := fden_polyPiBetaContractum EI Φ
  have hlhs := not_fden_polyPiBetaRedex EI Φ
  exact ⟨hrhs, hlhs, fun hfseq => hlhs ((hfseq polyPiBetaProbe).2 hrhs)⟩

/-- **Refutation of `FBetaRhsGap` on `fden`:**
`FBetaRhsGap E n EI FValOK` is false whenever `FValOK Γ Φ` is inhabited for at least one
context `Γ` and filter valuation `Φ`. -/
theorem not_fbetaRhsGap_of_fvalOK {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {FValOK : LCtx → FValuation → Prop}
    {Γ : LCtx} {Φ : FValuation} (hΦ : FValOK Γ Φ) :
    ¬ FBetaRhsGap E n EI FValOK := by
  intro hbeta
  obtain ⟨hrhs, hlhs, _⟩ := polyPiBeta_unsound_fden EI Φ
  exact hlhs (hbeta (hasTyT_polyPiBetaDom E n Γ)
    (hasTyT_polyPiBetaBody E n Γ) (hasTyT_polyPiBetaArg E n Γ) hΦ hrhs)

/-- **Vacuity Tooth for `FBetaRhsGap` (`fvalOK_empty_of_fbetaRhsGap`):**
Any `FBetaRhsGap E n EI FValOK` forces `FValOK` to be empty (`∀ Γ Φ, ¬ FValOK Γ Φ`). -/
theorem fvalOK_empty_of_fbetaRhsGap {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop}
    {FValOK : LCtx → FValuation → Prop}
    (hbeta : FBetaRhsGap E n EI FValOK) :
    ∀ Γ Φ, ¬ FValOK Γ Φ :=
  fun _ _ hΦ => not_fbetaRhsGap_of_fvalOK hΦ hbeta

/-- **Vacuity Tooth for `FSEqModelSupply` (`not_fseqModelSupply`):**
Because `FSEqModelSupply` includes `betaRhs : FBetaRhsGap E n EI (FZetaValOK EI)` and
`FZetaValOK EI [] (fdefaultVal EI [])` is inhabited (`fzetaValOK_default`),
`FSEqModelSupply E n EI` is refuted on `fden` over `RcicModelShape`'s disjoint-level `LeT`. -/
theorem not_fseqModelSupply {E : ResolvedEnv} {n : Nat}
    {EI : Nat → List Level → LTShape → Prop} :
    ¬ FSEqModelSupply E n EI :=
  fun M => not_fbetaRhsGap_of_fvalOK (fzetaValOK_default EI []) M.betaRhs

end Rcic.Domain.Model.PiInversion

#print axioms Rcic.Domain.Model.PiInversion.seq_pi_dom_inv
#print axioms Rcic.Domain.Model.PiInversion.seq_sort_inv
#print axioms Rcic.Domain.Model.PiInversion.not_seq_pi_sort
#print axioms Rcic.Domain.Model.PiInversion.seq_pi_cod_sort_inv
#print axioms Rcic.Domain.Model.PiInversion.interp_beta_lhs
#print axioms Rcic.Domain.Model.PiInversion.interp_zeta_lhs
#print axioms Rcic.Domain.Model.PiInversion.fundamental_convT_seq
#print axioms Rcic.Domain.Model.PiInversion.fundamental_tyConvT_seq
#print axioms Rcic.Domain.Model.PiInversion.eta_unsound_interp_at_bot
#print axioms Rcic.Domain.Model.PiInversion.irr_unsound_interp
#print axioms Rcic.Domain.Model.PiInversion.whredPiClause_refuted_at_andEnvU
#print axioms Rcic.Domain.Model.PiInversion.piInjType_of_semanticPiModel
#print axioms Rcic.Domain.Model.PiInversion.piRowField_of_semanticPiModel
#print axioms Rcic.Domain.Model.PiInversion.interp_lift_insertVal_iff
#print axioms Rcic.Domain.Model.PiInversion.interp_lift0_one_iff
#print axioms Rcic.Domain.Model.PiInversion.seq_lift0_one_iff
#print axioms Rcic.Domain.Model.PiInversion.zetaValOK_push_assumption
#print axioms Rcic.Domain.Model.PiInversion.zetaValOK_push_letBinding
#print axioms Rcic.Domain.Model.PiInversion.zetaLocalSemGap_of_zetaValOK
#print axioms Rcic.Domain.Model.PiInversion.interp_eta_rhs_lam
#print axioms Rcic.Domain.Model.PiInversion.interp_app_lift0_bvar0_inv
#print axioms Rcic.Domain.Model.PiInversion.interp_eta_lhs_of_floor_directed
#print axioms Rcic.Domain.Model.PiInversion.interp_eta_rhs_of_domCovered
#print axioms Rcic.Domain.Model.PiInversion.seq_eta_of_etaReady
#print axioms Rcic.Domain.Model.PiInversion.seq_of_botOnly
#print axioms Rcic.Domain.Model.PiInversion.seq_irrObs_at_bot
#print axioms Rcic.Domain.Model.PiInversion.semanticPiModel_of_seqModel
#print axioms Rcic.Domain.Model.PiInversion.piInjType_of_seqModel
#print axioms Rcic.Domain.Model.PiInversion.piRowField_of_seqModel
#print axioms Rcic.Domain.Model.PiInversion.insertVal_leP
#print axioms Rcic.Domain.Model.PiInversion.interp_insertVal_mono
#print axioms Rcic.Domain.Model.PiInversion.seq_zeta_bvar0
#print axioms Rcic.Domain.Model.PiInversion.seq_zeta_vacuous
#print axioms Rcic.Domain.Model.PiInversion.interp_beta_rhs_constSortWFun
#print axioms Rcic.Domain.Model.PiInversion.seq_beta_vacuous_sort
#print axioms Rcic.Domain.Model.PiInversion.interp_pi_and_lam_eq_botT
#print axioms Rcic.Domain.Model.PiInversion.interp_app_lam_pi_lam_inv
#print axioms Rcic.Domain.Model.PiInversion.botOnly_app_lam_pi_bvar0_lam
#print axioms Rcic.Domain.Model.PiInversion.beta_linear_unsound_interp
#print axioms Rcic.Domain.Model.PiInversion.not_betaRhsGap_of_valOK
#print axioms Rcic.Domain.Model.PiInversion.zeta_unsound_interp
#print axioms Rcic.Domain.Model.PiInversion.not_zetaRhsGap_of_valOK
#print axioms Rcic.Domain.Model.PiInversion.valOK_empty_of_seqModel
#print axioms Rcic.Domain.Model.PiInversion.valOK_empty_of_seqModel_zeta
#print axioms Rcic.Domain.Model.PiInversion.seqVal_total_of_seqModel
#print axioms Rcic.Domain.Model.PiInversion.tyConvT_total_of_seqModel
#print axioms Rcic.Domain.Model.PiInversion.seq_zeta_of_substFactorizes
#print axioms Rcic.Domain.Model.PiInversion.substFactorizes_app_of_directed
#print axioms Rcic.Domain.Model.PiInversion.eiConsts_eqNListClose
#print axioms Rcic.Domain.Model.PiInversion.eiDelta_emptyEnv
#print axioms Rcic.Domain.Model.PiInversion.fden_lift
#print axioms Rcic.Domain.Model.PiInversion.fden_instantiate
#print axioms Rcic.Domain.Model.PiInversion.fden_zeta
#print axioms Rcic.Domain.Model.PiInversion.fden_beta_lhs
#print axioms Rcic.Domain.Model.PiInversion.fden_letE_zetaBetaObs
#print axioms Rcic.Domain.Model.PiInversion.fden_app_lam_pi_bvar0_lam
#print axioms Rcic.Domain.Model.PiInversion.fseq_pi_dom_inv
#print axioms Rcic.Domain.Model.PiInversion.fseq_sort_inv
#print axioms Rcic.Domain.Model.PiInversion.not_fseq_pi_sort
#print axioms Rcic.Domain.Model.PiInversion.fseq_pi_cod_sort_inv
#print axioms Rcic.Domain.Model.PiInversion.fseq_zetaLocal_of_fzetaValOK
#print axioms Rcic.Domain.Model.PiInversion.fundamental_convT_fseq
#print axioms Rcic.Domain.Model.PiInversion.fundamental_tyConvT_fseq
#print axioms Rcic.Domain.Model.PiInversion.sortRow_of_fseqModel
#print axioms Rcic.Domain.Model.PiInversion.piDomFSEq_of_fseqModel
#print axioms Rcic.Domain.Model.PiInversion.not_tyConvT_pi_sort_of_fseqModel
#print axioms Rcic.Domain.Model.PiInversion.isBotT_of_interp_sort_succ
#print axioms Rcic.Domain.Model.PiInversion.isBotT_of_fden_sort_succ
#print axioms Rcic.Domain.Model.PiInversion.interp_app_lam_pi_bvar0_dom_bot
#print axioms Rcic.Domain.Model.PiInversion.fden_app_lam_pi_bvar0_dom_bot
#print axioms Rcic.Domain.Model.PiInversion.polyPiBeta_unsound_fden
#print axioms Rcic.Domain.Model.PiInversion.not_fbetaRhsGap_of_fvalOK
#print axioms Rcic.Domain.Model.PiInversion.fvalOK_empty_of_fbetaRhsGap
#print axioms Rcic.Domain.Model.PiInversion.not_fseqModelSupply
