import rcic.RcicF8JEndpoints
import rcic.RcicF8EvParStar
import rcic.RcicParRedTPins

set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JEndpoints.Pins
private def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def ss : EnvMembersSubstStable emptyEnv := envMembersSubstStable_of_envWfT EnvWfT.empty

abbrev one : Level := .succ .zero
abbrev other : Level := .max one .zero

def localCtx : LCtx := [.letBinding (.sort one) (.sort .zero)]
def localCtxWf : CtxWfT emptyEnv 0 localCtx :=
  .letBinding [] (.sort one) (.succ one) (.sort .zero) .nil
    (.sort [] one) (.sort [] .zero)
def localValueTy : HasTyT emptyEnv 0 localCtx (.sort .zero) (.sort one) :=
  .sort localCtx .zero
def localSource : ConvT emptyEnv 0 localCtx (.bvar 0) (.sort .zero) (.sort one) :=
  .zetaLocal localCtx 0 (.sort one) (.sort .zero) rfl rfl localValueTy
def localRoot : List (Jd emptyEnv 0) := [.cv localSource]
def localPacket : Packet localRoot localSource :=
  zetaLocalPacket (Γ := localCtx) 0 (.sort one) (.sort .zero) rfl rfl localValueTy
    ⟨.cv localSource, .head _, .inl rfl⟩
theorem local_exact :
    extractWf EnvWfT.empty localRoot localCtxWf localSource
      ⟨.cv localSource, .head _, .inl rfl⟩ = some localPacket := rfl
theorem local_nonidentity : Expr.bvar 0 ≠ (Expr.sort .zero : Expr Nat) := by decide
theorem local_left_no_leaves : localPacket.left.leaves = [] := rfl
theorem local_total_inventory : localPacket.leaves = [.ty localValueTy] := rfl
theorem local_left_exact : localPacket.left.val cl ss = HasTyT.bvar localCtx 0 (.sort one) rfl := rfl
theorem local_right_exact : localPacket.right.val cl ss = localValueTy := rfl
theorem local_edge (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([.cv localSource] ++ Z) (localPacket.leaves ++ Z) := localPacket.edge Z

/-- A real non-reflexive legacy iota with both original typed endpoints. -/
def iotaSource : ConvT pinLoopEnvT 1 pinLoopCtx wLoopLhs wLoopRhs loopMx :=
  .iota pinLoopCtx wLoopLhs wLoopRhs loopMx (.of wLoopK) loopLhsITyT loopRhsTyT
def iotaOut : Packet [Jd.cv iotaSource] iotaSource :=
  iotaPacket (.of wLoopK) loopLhsITyT loopRhsTyT ⟨_, .head _, .inl rfl⟩
theorem iota_exact : extract iotaSource ⟨_, .head _, .inl rfl⟩ = some iotaOut := rfl
theorem iota_nonidentity : wLoopLhs ≠ wLoopRhs := by decide
theorem iota_inventory : iotaOut.leaves = [.ty loopLhsITyT, .ty loopRhsTyT] := rfl
theorem iota_original_left (hcl : EnvClosed pinLoopEnvT)
    (hinst : EnvMembersSubstStable pinLoopEnvT) : iotaOut.left.val hcl hinst = loopLhsITyT := rfl
theorem iota_original_right (hcl : EnvClosed pinLoopEnvT)
    (hinst : EnvMembersSubstStable pinLoopEnvT) : iotaOut.right.val hcl hinst = loopRhsTyT := rfl

/-- No literal member assumption: the admitted root is a proper symm parent. -/
def sourceTyping : HasTyT emptyEnv 0 [] (.sort .zero) (.sort one) := .sort [] .zero
def baseSource : ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort one) :=
  .refl [] (.sort .zero) (.sort one) sourceTyping
def levelChange : ConvT emptyEnv 0 [] (.sort one) (.sort other) (.sort (.succ one)) :=
  .sorts [] one other (fun _ => rfl)
def changedSource : ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort other) :=
  .tyConv [] (.sort .zero) (.sort .zero) (.sort one) (.sort other) (.succ one)
    baseSource levelChange
def wrappingSource : ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort other) :=
  .symm [] (.sort .zero) (.sort .zero) (.sort other) changedSource
def ambient : List (Jd emptyEnv 0) := [.cv wrappingSource]
theorem changed_cert : ∃ r ∈ ambient, SubEq (.cv changedSource) r :=
  ⟨.cv wrappingSource, .head _, .inr (.child (.head _))⟩
theorem changed_not_member : (Jd.cv changedSource) ∉ ambient := by
  intro hx
  have heq := List.mem_singleton.mp hx
  cases heq

def changedBase : Packet ambient baseSource :=
  reflPacket sourceTyping (originalChildCert changed_cert (.head _))
def changedPacket : Packet ambient changedSource :=
  changedBase.reindex (.succ one) levelChange changed_cert

theorem changed_extract_exact :
    extractWf EnvWfT.empty ambient CtxWfT.nil changedSource changed_cert = some changedPacket := rfl
theorem changed_index_nonliteral : (Expr.sort one : Expr Nat) ≠ .sort other := by decide
theorem changed_inventory : changedPacket.leaves =
    [.ty sourceTyping, .cv levelChange, .ty sourceTyping, .cv levelChange] := rfl
theorem changed_has_four_leaves : changedPacket.leaves.length = 4 := rfl
theorem changed_left_materializes : changedPacket.left.val cl ss =
    HasTyT.conv [] (.sort .zero) (.sort one) (.sort other) (.succ one)
      sourceTyping levelChange := rfl
theorem changed_right_materializes : changedPacket.right.val cl ss =
    HasTyT.conv [] (.sort .zero) (.sort one) (.sort other) (.succ one)
      sourceTyping levelChange := rfl
theorem original_change_not_solved : supported levelChange = false := rfl
theorem change_packet_supported : supported changedSource = true := rfl
theorem changed_edge (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([.cv changedSource] ++ Z) (changedPacket.leaves ++ Z) := changedPacket.edge Z

/-- Exact recursion handles both branches and an internal retyping, without a J callback. -/
def composedSource : ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort other) :=
  .trans [] (.sort .zero) (.sort .zero) (.sort .zero) (.sort other)
    wrappingSource changedSource
theorem composed_extract_some :
    (extractWf EnvWfT.empty [Jd.cv composedSource] CtxWfT.nil composedSource
      ⟨_, .head _, .inl rfl⟩).isSome = true := rfl

def widenedPacket : Packet (ambient ++ [.cv baseSource]) changedSource :=
  changedPacket.widen (fun _ hx => List.mem_append.mpr (.inl hx))
theorem widened_inventory : widenedPacket.leaves = changedPacket.leaves := rfl

/-- Canonical false-unconditional-J fixture stays outside the supported domain. -/
theorem bad_literal_none :
    extract XTileQ1.conv_sort0 JTileS0.original_literal = none := rfl

def unsupportedTree : ConvT emptyEnv 0 [] (.sort one) (.sort other) (.sort (.succ one)) :=
  .trans [] (.sort one) (.sort one) (.sort other) (.sort (.succ one))
    (.refl [] (.sort one) (.sort (.succ one)) (.sort [] one)) levelChange
theorem one_unsupported_branch_none :
    extract (R := [Jd.cv unsupportedTree]) unsupportedTree ⟨.cv unsupportedTree, .head _, .inl rfl⟩ = none := rfl

end Rcic.Declarative.F8Measure.JEndpoints.Pins
