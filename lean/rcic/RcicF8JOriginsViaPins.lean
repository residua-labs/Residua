import rcic.RcicF8JOriginsVia
import rcic.RcicF8JOriginPins
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JOrigins.ViaPins
open F8Occurrences PEqTProofFront PEqLeafTPropPins

abbrev input := JOrigins.Pins.liveInput
abbrev roots := JOrigins.Pins.liveRoots
abbrev result := JOrigins.Pins.liveResult

def target : LCtx := [.assumption (.sort .zero)]
def targetWf : CtxWfT emptyEnv 0 target :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

/-- A genuine non-identity weakening witness for the SOURCE empty context. -/
def via : CtxWfVia emptyEnv 0 [] :=
  .wk (.assumption (.sort .zero)) 0 (.ofWf targetWf)

theorem target_longer : via.target.length = ([] : LCtx).length + 1 := rfl

theorem not_ofWf (hΓ : CtxWfT emptyEnv 0 []) : via ≠ .ofWf hΓ := by
  intro he
  have hl := congrArg (fun v : CtxWfVia emptyEnv 0 [] => v.target.length) he
  change 1 = 0 at hl
  exact Nat.noConfusion hl

theorem actual_weakening : via.ρ.map (.bvar 0) = .bvar 1 := rfl

theorem nonidentity_input : q ≠ p := JOrigins.Pins.live_input_nonidentity

theorem actual_dispatch :
    J3.dispatchVia EnvWfT.empty roots via input J3.Pins.flippedCert = some result := rfl

def actual_origins : ValleyOrigins EnvWfT.empty input result.valley :=
  dispatch_originsVia .empty roots via input J3.Pins.flippedCert

theorem actual_origins_exact : actual_origins = JOrigins.Pins.liveMap :=
  (valleyOrigins_subsingleton .empty input ⟨source_unique input rfl⟩ result.valley).elim _ _

theorem source_address_exact :
    (actual_origins.2.1 PUnit.unit).1 = JOrigins.Pins.livePath := by
  rw [actual_origins_exact]
  exact JOrigins.Pins.live_address

theorem actual_site_exact :
    proofSite JOrigins.Pins.liveSite = site J3.Pins.reversedTile.step PUnit.unit :=
  JOrigins.Pins.live_site_exact

theorem live_occurrence : (occurrences J3.Pins.reversedTile.step).length = 1 :=
  JOrigins.Pins.live_emitted_occurrence

theorem actual_step_still_original : J3.Pins.reversedTile.step = J3.Pins.movedTile.step :=
  J3.Pins.reversed_does_not_reverse_step

theorem both_endpoints_retained : result.valley.ty₁ = J3.Pins.moved.valley.ty₂ ∧
    result.valley.ty₂ = J3.Pins.moved.valley.ty₁ := ⟨rfl,rfl⟩

theorem exact_eleven_leaves : result.valley.leaves.length = 11 :=
  J3.Pins.reversed_eleven

theorem strict_all : ∀ l ∈ result.valley.leaves, SubOf l (.cv input) := result.strict

theorem actual_decorator :
    withOriginsVia .empty roots via input J3.Pins.flippedCert =
      some ⟨result, actual_origins⟩ := rfl

theorem source_literal_not_root_member : (Jd.cv input) ∉ roots :=
  J3.Pins.flipped_not_member

theorem caller_is_original : J3.Pins.reversedTile.X = [.cv input] := rfl

theorem caller_not_ambient : J3.Pins.reversedTile.X ≠ roots :=
  J3.Pins.reversed_not_ambient

theorem return_edge (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([.cv input] ++ Z) (result.valley.leaves ++ Z) := J3.result_edge result Z

/-- The exact ofWf output AND its source certificate, not just endpoints. -/
theorem full_ofWf_agreement :
    withOriginsVia .empty roots (.ofWf CtxWfT.nil) input J3.Pins.flippedCert =
      withOriginsWf .empty roots CtxWfT.nil input J3.Pins.flippedCert :=
  withOriginsVia_ofWf .empty roots CtxWfT.nil input J3.Pins.flippedCert

theorem unchanged_acceptance :
    (withOriginsVia .empty roots via input J3.Pins.flippedCert).isSome = J3.supported input :=
  withOriginsVia_coverage .empty roots via input J3.Pins.flippedCert

theorem live_partial_contract : JContractViaPWithOrigins (n := 0) EnvWfT.empty (j3Via EnvWfT.empty) :=
  j3Via_bothContracts .empty

theorem index_irr_not_translated :
    NoProofOccurrences (JOrigins.Pins.indexResult.valley.left.val J3.Pins.cl J3.Pins.ss) ∧
    NoProofOccurrences (JOrigins.Pins.indexResult.valley.right.val J3.Pins.cl J3.Pins.ss) :=
  dispatchedVia_no_source .empty via JOrigins.Pins.indexOnly JOrigins.Pins.indexCert
    JOrigins.Pins.indexResult rfl JOrigins.Pins.index_no_translated_source

theorem typing_irr_not_translated :
    NoProofOccurrences (JOrigins.Pins.typingResult.valley.left.val J3.Pins.cl J3.Pins.ss) ∧
    NoProofOccurrences (JOrigins.Pins.typingResult.valley.right.val J3.Pins.cl J3.Pins.ss) :=
  dispatchedVia_no_source .empty via JOrigins.Pins.typingRefl JOrigins.Pins.typingCert
    JOrigins.Pins.typingResult rfl JOrigins.Pins.typing_no_translated_source

theorem typing_leaf_not_erased : JOrigins.Pins.typingResult.valley.leaves =
    List.replicate 4 (Jd.ty JOrigins.Pins.typingWithIrr) :=
  JOrigins.Pins.typing_input_still_retained

/-- A LIVE but wrong site: genuine typing data, reversed proof pair. -/
def actualSite : ProofSite emptyEnv 0 := site J3.Pins.reversedTile.step PUnit.unit

def wrongSite : ProofSite emptyEnv 0 where
  context := actualSite.context
  left := actualSite.right
  right := actualSite.left
  leftProp := actualSite.rightProp
  rightProp := actualSite.leftProp
  leftPropTy := actualSite.rightPropTy
  rightPropTy := actualSite.leftPropTy
  leftTy := actualSite.rightTy
  rightTy := actualSite.leftTy

def weakSite (s : ProofSite emptyEnv 0) : Prop :=
  s.leftProp = actualSite.leftProp ∧ s.rightProp = actualSite.rightProp

def exactSite (s : ProofSite emptyEnv 0) : Prop := s = actualSite

theorem mutant_site_accepts : weakSite wrongSite := ⟨rfl,rfl⟩

theorem exact_site_refuses : ¬ exactSite wrongSite := by
  intro he
  have hh := congrArg ProofSite.left he
  exact nonidentity_input hh

def truncatedLeaves : List (Jd emptyEnv 0) := result.valley.leaves.take 3

def weakInventory (ls : List (Jd emptyEnv 0)) : Prop := ∀ l ∈ ls, SubOf l (.cv input)
def exactInventory (ls : List (Jd emptyEnv 0)) : Prop := ls = result.valley.leaves

theorem mutant_inventory_accepts : weakInventory truncatedLeaves := by
  intro l hl
  exact result.strict l (List.mem_of_mem_take hl)

theorem exact_inventory_refuses : ¬ exactInventory truncatedLeaves := by
  intro he
  have hh := congrArg List.length he
  change 3 = 11 at hh
  exact (by decide : (3 : Nat) ≠ 11) hh

/-- Reuse WK-1a's real bad-context tooth: no made-up arbitrary morphism admitted. -/
theorem mutant_context_accepts : Nonempty (CtxWfViaMut emptyEnv 0 XTileQ1.illCtx) :=
  mutant_accepts_illCtx

theorem exact_context_refuses : ¬ Nonempty (CtxWfVia emptyEnv 0 XTileQ1.illCtx) :=
  illCtx_no_via

theorem live_mutants :
    weakSite wrongSite ∧ ¬ exactSite wrongSite ∧
    weakInventory truncatedLeaves ∧ ¬ exactInventory truncatedLeaves ∧
    Nonempty (CtxWfViaMut emptyEnv 0 XTileQ1.illCtx) ∧
    ¬ Nonempty (CtxWfVia emptyEnv 0 XTileQ1.illCtx) :=
  ⟨mutant_site_accepts,exact_site_refuses,mutant_inventory_accepts,
    exact_inventory_refuses,mutant_context_accepts,exact_context_refuses⟩

end Rcic.Declarative.F8Measure.JOrigins.ViaPins
