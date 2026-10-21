import rcic.RcicF8IrrOM
import rcic.RcicPEqLeafTPropPins

namespace Rcic.Declarative.F8Measure.IrrPins
open F8Occurrences PEqTProofFront PEqLeafTPropPins

private def cl : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h
private def ss : EnvMembersSubstStable emptyEnv := fun _ _ h => Option.noConfusion h

def source : ConvT emptyEnv 0 [] p q P := .irr [] P p q (P_ty []) (p_ty []) (q_ty [])
def root : Jd emptyEnv 0 := .cv source
def payload : ProofIndexPayload [root] [] p q P :=
  literalIrrPayload (P_ty []) (p_ty []) (q_ty [])
def producer : EvPar [root] [] p q P :=
  literalIrrProducer (P_ty []) (p_ty []) (q_ty [])

theorem original_children : producer.leaves = root.children := rfl
theorem original_three : producer.leaves = [Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty [])] := rfl
theorem nonidentity : p ≠ q := by intro h; cases h
theorem output_exact : producer.val cl ss =
    ParRedT.peq [] p q P (peqLeafT_reconcile_propIndex (P_ty []) (.refl [] P) (p_ty []) (q_ty [])).1 :=
  literalIrrProducer_val cl ss (P_ty []) (p_ty []) (q_ty [])
theorem output_conv_exact :
    (peqLeafT_reconcile_propIndex (P_ty (E := emptyEnv) (n := 0) [])
      (.refl [] P) (p_ty []) (q_ty [])).2 = source :=
  literalIrrProducer_conv_exact (P_ty []) (p_ty []) (q_ty [])
theorem dm_step : Rcic.Syn.DMStep (producer.leaves.map Jd.wt) ([root].map Jd.wt) :=
  literalIrrProducer_dm (P_ty []) (p_ty []) (q_ty [])
theorem answer_left : EvPar.proofIndexLazyAnswer payload .left = EvTc.refl [] P := rfl
theorem answer_right : EvPar.proofIndexLazyAnswer payload .right = EvTc.refl [] P := rfl
theorem answer_no_atoms (side : Side) : (EvPar.proofIndexLazyAnswer payload side).leaves = [] := rfl
theorem original_index (side : Side) : (EvPar.proofIndexRequests cl ss payload PUnit.unit side).index = P :=
  EvPar.proofIndex_request_index cl ss payload PUnit.unit side
def complete_answers : AnsweredOrigins (producer.val cl ss) (EvPar.proofIndexRequests cl ss payload) :=
  EvPar.proofIndexAnswers cl ss payload

/-- An input type chain, not a reconstructed output admitted as an atom. -/
def aliasRoot : Jd emptyEnv 0 := .tc (alias_chain (n := 0))
def extendedRoot : List (Jd emptyEnv 0) := [root, aliasRoot]
def inclusion : ∀ r ∈ [root], r ∈ extendedRoot := by
  intro r hr
  rcases List.mem_cons.mp hr with heq | hnil
  · subst r; exact .head _
  · exact False.elim (List.not_mem_nil _ hnil)
def widened : EvPar extendedRoot [] p q P := producer.widen inclusion
theorem widening_keeps_output : widened.val cl ss = producer.val cl ss :=
  producer.val_widen inclusion cl ss
theorem widening_keeps_leaves : widened.leaves = producer.leaves :=
  producer.leaves_widen inclusion
theorem widening_keeps_size : widened.size = producer.size := producer.size_widen inclusion

def aliasEvidence : EvTc extendedRoot [] aliasP P :=
  .lit alias_chain ⟨aliasRoot, .tail _ (.head _), Or.inl rfl⟩
/-- Nonliteral-index exercise of the same constructor. Endpoint retyping is
LAZY; none of the materialized retyped endpoints is an EvTy.lit input. -/
def aliasPayload : ProofIndexPayload extendedRoot [] p q aliasP where
  proposition := P
  propTy := (payload.widen inclusion).propTy
  chain := aliasEvidence
  leftTy := .rety (payload.widen inclusion).leftTy (.symm aliasEvidence)
  rightTy := .rety (payload.widen inclusion).rightTy (.symm aliasEvidence)
def aliasProducer : EvPar extendedRoot [] p q aliasP := .proofIndex aliasPayload

theorem alias_index (side : Side) :
    (EvPar.proofIndexRequests cl ss aliasPayload PUnit.unit side).index = aliasP :=
  EvPar.proofIndex_request_index cl ss aliasPayload PUnit.unit side
theorem alias_nonliteral_index : aliasP ≠ P := alias_nonliteral
theorem alias_answer_original (side : Side) : EvPar.proofIndexLazyAnswer aliasPayload side = aliasEvidence := rfl
theorem alias_materialization_exact : aliasProducer.val cl ss =
    ParRedT.peq [] p q aliasP
      (peqLeafT_reconcile_propIndex (aliasPayload.propTy.val cl ss)
        (aliasPayload.chain.val cl ss) (aliasPayload.leftTy.val cl ss)
        (aliasPayload.rightTy.val cl ss)).1 := rfl
def alias_complete_answers : AnsweredOrigins (aliasProducer.val cl ss)
    (EvPar.proofIndexRequests cl ss aliasPayload) := EvPar.proofIndexAnswers cl ss aliasPayload

/-- A deliberately fabricated typing with the same endpoints but extra casts. -/
def paddedTyping : Nat → HasTyT emptyEnv 0 [] p P
  | 0 => p_ty []
  | k + 1 => .conv [] p P P .zero (paddedTyping k)
      (.refl [] P (.sort .zero) (P_ty []))
theorem padded_larger : root.wt < (Jd.ty (paddedTyping 32)).wt := by decide
/-- Endpoint equality alone cannot supply the literal-source witness. -/
theorem padded_not_literal_source : ¬ ∃ r ∈ [root], SubEq (Jd.ty (paddedTyping 32)) r := by
  rintro ⟨r, hr, hs⟩
  rcases List.mem_cons.mp hr with heq | hnil
  · subst r
    exact Nat.not_le_of_lt padded_larger (subEq_wt_le hs)
  · exact List.not_mem_nil _ hnil

theorem root_not_strict : ¬ SubOf root root := subOf_irrefl _
def tile : DTile [root] := literalIrrTile cl ss (P_ty []) (p_ty []) (q_ty [])
theorem tile_output_exact : tile.step = producer.val cl ss := rfl
theorem tile_nonempty_occurrences : (F8Occurrences.occurrences tile.step).length = 1 := rfl
theorem tile_edge : OM3_edge [root] producer.leaves :=
  literalIrrTile_edge (P_ty []) (p_ty []) (q_ty [])
end Rcic.Declarative.F8Measure.IrrPins
