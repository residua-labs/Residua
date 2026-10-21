import rcic.RcicF8JOrigins
import rcic.RcicF8JTransportPins
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JOrigins.Pins
open F8Occurrences PEqTProofFront PEqLeafTPropPins

abbrev liveInput := J3.Pins.flipped
abbrev liveRoots := J3.Pins.roots
abbrev liveResult := J3.Pins.reversed

def livePath : IrrOcc liveInput := .symm (.tyConv J3.Pins.aliasUp .irr)
def liveSite : IrrSite liveRoots := livePath.site liveInput J3.Pins.flippedCert

def liveMap : ValleyOrigins EnvWfT.empty liveInput liveResult.valley :=
  swap_origins J3.Pins.moved
    (reindex_origins J3.Pins.base .zero J3.Pins.aliasUp J3.Pins.changedCert
      (irr_origins .empty (P_ty []) (p_ty []) (q_ty []) J3.Pins.sourceCert))

theorem live_input_nonidentity : q ≠ p := Ne.symm IrrPins.nonidentity
theorem live_host : liveSite.host = aliasP := rfl
theorem live_core : proofSite liveSite = core (IrrOcc.irr
    (hP := P_ty (E := emptyEnv) (n := 0) []) (hp := p_ty []) (hq := q_ty [])) := rfl

theorem live_address : (liveMap.2.1 PUnit.unit).1 = livePath := by
  simp only [liveMap, swap_origins, reindex_origins, irr_origins,
    StarOrigins.retarget, StarOrigins.reindex, J3.Pins.moved, J3.Pins.base,
    J3.Result.reindex, J3.irrResult, Valley.conv, J1.irrValley, EvParStar.val,
    parRedTStar_conv]
  rfl

theorem live_site_exact : proofSite liveSite = site J3.Pins.reversedTile.step PUnit.unit :=
  by
    have heq := (liveMap.2.1 PUnit.unit).2.down
    rw [live_address] at heq
    exact (site_core J3.Pins.flippedCert livePath).trans heq

theorem live_classified_leaves :
    ∀ l ∈ liveSite.leaves, SubOf l (.cv liveInput) :=
  livePath.site_strict J3.Pins.flippedCert

theorem live_site_edge (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([.cv liveInput] ++ Z) (liveSite.leaves ++ Z) :=
  livePath.site_edge J3.Pins.flippedCert Z

theorem live_emitted_occurrence :
    (occurrences J3.Pins.reversedTile.step).length = 1 := rfl

theorem live_inner_index (side : Side) :
    match J3.Pins.reversedTile.status PUnit.unit side with
    | .answered req _ => req.index = P
    | .admissible .. => False := by
  simpa only [J3.Pins.reversedTile, J3.Pins.reversed, J3.Result.swap,
    J3.Certified.recaller, J3.StepCertificate.recaller, J3.StepCertificate.tile,
    J3.Pins.movedTile, Valley.symm, J3.Pins.moved, J3.Result.reindex,
    J3.Pins.base, J3.irrResult, Valley.conv, J1.irrValley, EvParStar.val,
    parRedTStar_conv, J3.Certified.reindex, J3.StepCertificate.reindex]
    using J3.Pins.moved_inner_index side

theorem host_not_inner_index : liveSite.host ≠ P := alias_nonliteral

theorem live_dispatch_exact :
    J3.dispatchWf EnvWfT.empty liveRoots CtxWfT.nil liveInput J3.Pins.flippedCert =
      some liveResult := rfl

theorem live_contract :
    (∀ l ∈ liveResult.valley.leaves, SubOf l (.cv liveInput)) ∧
    Nonempty (ValleyOrigins EnvWfT.empty liveInput liveResult.valley) :=
  dispatched_contract .empty CtxWfT.nil liveInput J3.Pins.flippedCert
    liveResult live_dispatch_exact

/-! Real irr hidden in a TYPE-INDEX field, then the same irr inside a TYPING premise.
The same Fable/Devin input classification is NOT extended to those proof subtrees. -/
def constP : Expr Nat := .lam P P
def constPTy : HasTyT emptyEnv 0 [] constP (.pi P (.sort .zero)) :=
  .lam [] P .zero P (.sort .zero) (P_ty []) (P_ty [.assumption P])
def Fp : Expr Nat := .app constP p
def Fq : Expr Nat := .app constP q

def betaP : ConvT emptyEnv 0 [] Fp P (.sort .zero) :=
  .beta [] P P p (.sort .zero) .zero (P_ty [])
    (P_ty [.assumption P]) (p_ty [])
def upP : ConvT emptyEnv 0 [] P Fp (.sort .zero) := .symm [] Fp P _ betaP

def indexWithIrr : ConvT emptyEnv 0 [] Fp Fq (.sort .zero) :=
  .app [] constP constP p q P (.sort .zero)
    (.refl [] constP (.pi P (.sort .zero)) constPTy) IrrPins.source

theorem irr_in_index : Child (.cv IrrPins.source) (.cv indexWithIrr) :=
  .tail _ (.head _)

def termRefl : ConvT emptyEnv 0 [] p p P := .refl [] p P (p_ty [])
def promotedRefl : ConvT emptyEnv 0 [] p p Fp :=
  .tyConv [] p p P Fp .zero termRefl upP
def indexOnly : ConvT emptyEnv 0 [] p p Fq :=
  .tyConv [] p p Fp Fq .zero promotedRefl indexWithIrr
def indexRoots : List (Jd emptyEnv 0) := [.cv indexOnly]
def indexCert : ∃ r ∈ indexRoots, SubEq (.cv indexOnly) r := ⟨_, .head _, .inl rfl⟩

theorem actual_irr_inside_index_input : SubOf (.cv IrrPins.source) (.cv indexOnly) :=
  .trans (.child irr_in_index) (.child (.tail _ (.head _)))

theorem index_no_translated_source (o : IrrOcc indexOnly) : False := by
  cases o with
  | tyConv _ o =>
      cases o with
      | tyConv _ o => exact refl_no_source (p_ty []) o

def indexResult : J3.Result EnvWfT.empty indexRoots indexOnly :=
  let p1 := J3.reflResult EnvWfT.empty (p_ty [])
    (certOfChild (y := .cv promotedRefl) (.head _)
      (certOfChild (y := .cv indexOnly) (.head _) indexCert))
  let p2 := p1.reindex .zero upP (certOfChild (y := .cv indexOnly) (.head _) indexCert)
  p2.reindex .zero indexWithIrr indexCert

theorem index_dispatch_exact :
    J3.dispatchWf EnvWfT.empty indexRoots CtxWfT.nil indexOnly indexCert =
      some indexResult := rfl

theorem index_no_output_occurrences :
    NoProofOccurrences (indexResult.valley.left.val J3.Pins.cl J3.Pins.ss) ∧
    NoProofOccurrences (indexResult.valley.right.val J3.Pins.cl J3.Pins.ss) :=
  ⟨True.intro, True.intro⟩

def typingWithIrr : HasTyT emptyEnv 0 [] p Fq :=
  .conv [] p Fp Fq .zero
    (.conv [] p P Fp .zero (p_ty []) upP) indexWithIrr

theorem actual_irr_inside_typing : SubOf (.cv IrrPins.source) (.ty typingWithIrr) :=
  .trans (.child irr_in_index) (.child (.tail _ (.head _)))

def typingRefl : ConvT emptyEnv 0 [] p p Fq := .refl [] p Fq typingWithIrr

theorem typing_no_translated_source (o : IrrOcc typingRefl) : False :=
  refl_no_source typingWithIrr o

def typingRoots : List (Jd emptyEnv 0) := [.cv typingRefl]
def typingCert : ∃ r ∈ typingRoots, SubEq (.cv typingRefl) r := ⟨_, .head _, .inl rfl⟩
def typingResult : J3.Result EnvWfT.empty typingRoots typingRefl :=
  J3.reflResult .empty typingWithIrr typingCert

theorem typing_input_still_retained : typingResult.valley.leaves =
    List.replicate 4 (Jd.ty typingWithIrr) := rfl

theorem typing_dispatch_exact :
    J3.dispatchWf EnvWfT.empty typingRoots CtxWfT.nil typingRefl typingCert =
      some typingResult := rfl

theorem typing_no_output_occurrences :
    NoProofOccurrences (typingResult.valley.left.val J3.Pins.cl J3.Pins.ss) ∧
    NoProofOccurrences (typingResult.valley.right.val J3.Pins.cl J3.Pins.ss) :=
  ⟨True.intro, True.intro⟩

/-- Entire original typing data may contain irr; this says NOTHING about erasing leaves. -/
def typing_contract : ValleyOrigins EnvWfT.empty typingRefl typingResult.valley :=
  refl_origins .empty typingWithIrr typingCert

end Rcic.Declarative.F8Measure.JOrigins.Pins
