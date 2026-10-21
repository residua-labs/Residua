import rcic.RcicF8JBase
import rcic.RcicPEqLeafTPropPins
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J1.Pins
open PEqTProofFront PEqLeafTPropPins

def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
def ss : EnvMembersSubstStable emptyEnv := envMembersSubstStable_of_envWfT EnvWfT.empty

def reflTyping : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero
def reflLiteral : ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .refl [] _ _ reflTyping
def reflRoots : List (Jd emptyEnv 0) := [.cv reflLiteral]
def reflCert : ∃ r ∈ reflRoots, SubEq (Jd.cv reflLiteral) r := ⟨_, .head _, .inl rfl⟩
def reflOut : Result EnvWfT.empty reflRoots reflLiteral := reflResult .empty reflTyping reflCert

theorem refl_exact : reflOut.valley.left.val cl ss = .refl [] _ _ reflTyping := rfl
theorem refl_inventory : reflOut.valley.leaves = List.replicate 4 (Jd.ty reflTyping) := rfl
theorem refl_dispatch : dispatchWf EnvWfT.empty reflRoots CtxWfT.nil reflLiteral reflCert =
    some reflOut := rfl

def wrapper : ConvT emptyEnv 0 [] q p P := .symm [] p q P IrrPins.source
def roots : List (Jd emptyEnv 0) := [.cv wrapper]
theorem source_child : Child (Jd.cv IrrPins.source) (Jd.cv wrapper) := .head _
def sourceCert : ∃ r ∈ roots, SubEq (Jd.cv IrrPins.source) r :=
  ⟨_, .head _, .inr (.child source_child)⟩

theorem source_not_member : Jd.cv IrrPins.source ∉ roots := by
  intro h
  have heq : Jd.cv IrrPins.source = Jd.cv wrapper := by simpa [roots] using h
  have hl := child_wt_lt source_child
  rw [heq] at hl
  exact Nat.lt_irrefl _ hl

def out : Result EnvWfT.empty roots IrrPins.source :=
  irrResult .empty (P_ty []) (p_ty []) (q_ty []) sourceCert

def tile : DTile roots := irrTile cl ss (P_ty []) (p_ty []) (q_ty []) sourceCert

theorem emitted_exact : tile.step = IrrPins.producer.val cl ss := rfl
theorem removed_original : tile.X = [Jd.cv IrrPins.source] := rfl
theorem removed_not_ambient : tile.X ≠ roots := by
  intro h
  have hh : Jd.cv IrrPins.source ∈ roots := h ▸ (List.mem_cons_self ..)
  exact source_not_member hh

theorem complete_inventory : out.valley.leaves =
    [Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty []), Jd.ty (q_ty []),
     Jd.ty (q_ty []), Jd.ty (p_ty []), Jd.ty (q_ty [])] := rfl

theorem inventory_not_just_step : out.valley.leaves.length ≠ 3 := by decide

theorem left_exact : out.valley.left.val cl ss =
    .tail tile.step (.refl [] q P (q_ty [])) := rfl

theorem right_exact : out.valley.right.val cl ss = .refl [] q P (q_ty []) := rfl

theorem left_typing_exact : out.valley.ty₁.val cl ss = p_ty [] := rfl

theorem right_typing_exact : out.valley.ty₂.val cl ss = q_ty [] := rfl

theorem shared_fixture_exact : out.valley.left.val cl ss = pinValley.left.val cl ss := rfl

theorem live_occurrence : (F8Occurrences.occurrences tile.step).length = 1 := rfl

theorem answered_both (side : F8Occurrences.Side) :
    (irrPayload (P_ty []) (p_ty []) (q_ty []) sourceCert).lazyAnswer side =
      EvTc.refl [] P := rfl

theorem strict_all : ∀ ℓ ∈ out.valley.leaves, SubOf ℓ (Jd.cv IrrPins.source) := out.strict

theorem edge_with_frame (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([Jd.cv IrrPins.source] ++ Z) (out.valley.leaves ++ Z) := result_edge .empty out Z

theorem dispatched : dispatchWf .empty roots CtxWfT.nil IrrPins.source sourceCert =
    some out := rfl

def wrapperCert : ∃ r ∈ roots, SubEq (Jd.cv wrapper) r := ⟨_, .head _, .inl rfl⟩

theorem unimplemented_symm : dispatchWf .empty roots CtxWfT.nil wrapper wrapperCert = none := rfl

theorem widened_inventory : (out.valley.widen (R' := roots ++ reflRoots)
    (fun x hx => List.mem_append_left _ hx)).leaves = out.valley.leaves :=
  Valley.leaves_widen _ _

theorem no_generated_literal :
    ¬ ∃ r ∈ [IrrPins.root], SubEq (Jd.ty (IrrPins.paddedTyping 32)) r :=
  IrrPins.padded_not_literal_source

end Rcic.Declarative.F8Measure.J1.Pins
