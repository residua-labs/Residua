import rcic.RcicF8JTransport
import rcic.RcicF8JBasePins
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J3.Pins
open PEqTProofFront PEqLeafTPropPins F8Occurrences

def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
def ss : EnvMembersSubstStable emptyEnv := envMembersSubstStable_of_envWfT EnvWfT.empty

def aliasDown : ConvT emptyEnv 0 [] aliasP P (.sort .zero) :=
  .beta [] (.sort .zero) (.bvar 0) P (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl) (P_ty [])
def aliasUp : ConvT emptyEnv 0 [] P aliasP (.sort .zero) :=
  .symm [] aliasP P (.sort .zero) aliasDown
def changed : ConvT emptyEnv 0 [] p q aliasP :=
  .tyConv [] p q P aliasP .zero IrrPins.source aliasUp
def flipped : ConvT emptyEnv 0 [] q p aliasP := .symm [] p q aliasP changed
def envelope : ConvT emptyEnv 0 [] p q aliasP := .symm [] q p aliasP flipped
def roots : List (Jd emptyEnv 0) := [.cv envelope]

def changedCert : ∃ r ∈ roots, SubEq (.cv changed) r :=
  ⟨_, .head _, .inr (SubOf.trans (y := Jd.cv flipped) (.child (.head _)) (.child (.head _)))⟩
def sourceCert : ∃ r ∈ roots, SubEq (.cv IrrPins.source) r :=
  certOfChild (y := .cv changed) (.head _) changedCert
def flippedCert : ∃ r ∈ roots, SubEq (.cv flipped) r :=
  ⟨_, .head _, .inr (.child (.head _))⟩

theorem flipped_not_member : (.cv flipped : Jd emptyEnv 0) ∉ roots := by
  intro h
  have heq : (Jd.cv flipped : Jd emptyEnv 0) = .cv envelope := by simpa [roots] using h
  have hlt := child_wt_lt (x := Jd.cv flipped) (y := Jd.cv envelope) (.head _)
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

def base : Result EnvWfT.empty roots IrrPins.source :=
  irrResult .empty (P_ty []) (p_ty []) (q_ty []) sourceCert
def moved : Result EnvWfT.empty roots changed := base.reindex .zero aliasUp changedCert
def reversed : Result EnvWfT.empty roots flipped := moved.swap

theorem endpoints_differ : p ≠ q := IrrPins.nonidentity
theorem indices_differ : aliasP ≠ P := alias_nonliteral
theorem moved_exact_shared : moved.valley =
    base.valley.conv (indexField .zero aliasUp changedCert) := rfl
theorem reversed_exact_shared : reversed.valley = moved.valley.symm := rfl

theorem moved_inventory : moved.valley.leaves =
    [Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty []), Jd.ty (q_ty []), .cv aliasUp,
      Jd.ty (q_ty []), .cv aliasUp, Jd.ty (p_ty []), .cv aliasUp,
      Jd.ty (q_ty []), .cv aliasUp] := rfl

theorem moved_eleven : moved.valley.leaves.length = 11 := rfl
theorem reversed_eleven : reversed.valley.leaves.length = 11 := rfl

def movedTile : DTile roots := moved.leftTiles.1.tile
def reversedTile : DTile roots := reversed.rightTiles.1.tile

theorem moved_tile_removed : movedTile.X = [.cv changed] := rfl
theorem reversed_tile_removed : reversedTile.X = [.cv flipped] := rfl

theorem reversed_not_ambient : reversedTile.X ≠ roots := by
  intro heq
  have hm : (Jd.cv flipped : Jd emptyEnv 0) ∈ roots := heq ▸ List.mem_cons_self ..
  exact flipped_not_member hm

theorem moved_tile_exact : movedTile.step =
    ParRedT.conv [] p q P aliasP (IrrPins.producer.val cl ss)
      (.of [] P aliasP .zero aliasUp) := rfl

theorem reversed_does_not_reverse_step : reversedTile.step = movedTile.step := rfl

theorem moved_leg_exact : moved.valley.left.val cl ss =
    .tail movedTile.step (.refl [] q aliasP
      (hasTyT_of_tyConvT (q_ty []) (.of [] P aliasP .zero aliasUp))) := rfl

theorem reversed_leg_exact : reversed.valley.right.val cl ss = moved.valley.left.val cl ss := rfl

theorem moved_live_occurrence : (occurrences movedTile.step).length = 1 := rfl

theorem moved_inner_index (side : Side) :
    match movedTile.status PUnit.unit side with
    | .answered req _ => req.index = P
    | .admissible .. => False := by
  cases side <;>
    simp only [movedTile, moved, Result.reindex, base, irrResult, J1.irrValley,
      EvParStar.val, Certified.reindex, Certified.recaller,
      StepCertificate.tile, StepCertificate.reindex, StepCertificate.recaller,
      J1.irrTile, statusOfAnswered, ProofIndexPayload.requests,
      ProofIndexPayload.answers, J1.irrPayload, rootRequests, rootAnswers, EvTy.val, EvTc.val, cl, ss] <;> rfl

theorem moved_inner_answer (side : Side) :
    HEq (movedTile.status PUnit.unit side)
      ((J1.irrTile cl ss (P_ty []) (p_ty []) (q_ty []) sourceCert).status PUnit.unit side) := by
  cases side <;>
    simp only [movedTile, moved, Result.reindex, base, irrResult, J1.irrValley,
      EvParStar.val, Certified.reindex, Certified.recaller,
      StepCertificate.tile, StepCertificate.reindex, StepCertificate.recaller,
      J1.irrTile, statusOfAnswered, ProofIndexPayload.requests,
      ProofIndexPayload.answers, J1.irrPayload, rootRequests, rootAnswers, EvTy.val, EvTc.val, cl, ss] <;> rfl

theorem all_strict : ∀ l ∈ reversed.valley.leaves, SubOf l (.cv flipped) := reversed.strict
theorem result_edge_with_frame (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([.cv flipped] ++ Z) (reversed.valley.leaves ++ Z) := result_edge reversed Z

theorem original_recursive_edge (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([Jd.cv changed] ++ Z) ([Jd.cv IrrPins.source] ++ Z) :=
  original_child_edge (x := Jd.cv IrrPins.source) (y := Jd.cv changed) (.head _) Z

theorem dispatched : (dispatchWf EnvWfT.empty roots CtxWfT.nil flipped flippedCert).isSome = true :=
  dispatchWf_coverage EnvWfT.empty CtxWfT.nil flipped flippedCert

def joinedByTrans : ConvT emptyEnv 0 [] p p aliasP :=
  .trans [] p q p aliasP changed flipped

theorem trans_not_claimed : (dispatchWf EnvWfT.empty [Jd.cv joinedByTrans]
    CtxWfT.nil joinedByTrans ⟨_, .head _, .inl rfl⟩).isSome = false :=
  dispatchWf_coverage EnvWfT.empty CtxWfT.nil joinedByTrans ⟨_, .head _, .inl rfl⟩

theorem original_index_child_need_not_dispatch : supported aliasUp = false := rfl
end Rcic.Declarative.F8Measure.J3.Pins
