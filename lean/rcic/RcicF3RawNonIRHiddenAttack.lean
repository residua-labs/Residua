import rcic.RcicIndGroupNonIR
import rcic.RcicF3PiSmallCompile

/-!
# Raw occurrence is stronger than normalized noninterference

The local fields `x : F` and `y : (fun _ : F => F) x` have explicit typed
derivations and pass the recursive-field scanner. The second raw expression
mentions x, although the reader erases that occurrence by beta reduction.
This is a local typing/scanner witness, not an EnvWfT group certificate.
It does not refute semantic independence of the normalized fields.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawNonIRHiddenAttack
open Rcic.Declarative

def member : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
noncomputable def env (f : Nat) : ResolvedEnv := extendEnv emptyEnv f member
def family (f : Nat) : Expr Nat := .const f []
def hidden (f : Nat) : Expr Nat := .app (.lam (family f) (family f)) (.bvar 0)
def rawFields (f : Nat) : List (Expr Nat) := [family f, hidden f]
def normalFields (f : Nat) : List (Expr Nat) := [family f, family f]

noncomputable def family_typed (f : Nat) (Γ : LCtx) :
    HasTyT (env f) 0 Γ (family f) (.sort (.succ .zero)) :=
  .const Γ f [] member (by
    change (if f = f then some member else none) = some member
    rw [if_pos rfl]) rfl rfl

noncomputable def context_typed (f : Nat) : CtxWfT (env f) 0 [.assumption (family f)] :=
  .assumption [] (family f) (.succ .zero) .nil (family_typed f [])

noncomputable def hidden_typed (f : Nat) :
    HasTyT (env f) 0 [.assumption (family f)] (hidden f) (.sort (.succ .zero)) :=
  .app [.assumption (family f)] (.lam (family f) (family f)) (.bvar 0)
    (family f) (.sort (.succ .zero))
    (.lam [.assumption (family f)] (family f) (.succ .zero)
      (family f) (.sort (.succ .zero)) (family_typed f _)
      (family_typed f _))
    (.bvar [.assumption (family f)] 0 (family f) rfl)

theorem raw_not_nonIR (f : Nat) : ¬ NonIRFieldList (env f) f (rawFields f) := by
  intro h
  have he := h ⟨0, by change 0 < 2; decide⟩
    ⟨1, by change 1 < 2; decide⟩ (by change 0 < 1; decide) familyVisible_const
  change true = false at he
  cases he

theorem normal_nonIR (f : Nat) : NonIRFieldList (env f) f (normalFields f) := by
  intro j k _ _
  have hk := List.getElem_mem k.isLt
  change (normalFields f)[k.val] ∈ [family f, family f] at hk
  rcases List.mem_cons.mp hk with he | he
  · rw [he]
    rfl
  · rw [List.mem_singleton.mp he]
    rfl

/-- The exact scanner successes are checked at independently relabelled
families. The terminal argument vector is empty in this local fixture. -/
theorem read_and_scan : ∀ f ∈ [1, 2, 987],
    piTelescopeFuel (env f) 16 (hidden f) = some ([], family f) ∧
    fieldShapesFuel (env f) 16 f 0 0 0 0 (rawFields f) =
      some [.recursive 0, .recursive 0] := by
  decide

def Witness : Prop := ∀ f ∈ [1, 2, 987],
  Nonempty (CtxWfT (env f) 0 [.assumption (family f)]) ∧
  Nonempty (HasTyT (env f) 0 [.assumption (family f)] (hidden f)
    (.sort (.succ .zero))) ∧
  piTelescopeFuel (env f) 16 (hidden f) = some ([], family f) ∧
  fieldShapesFuel (env f) 16 f 0 0 0 0 (rawFields f) =
    some [.recursive 0, .recursive 0] ∧
  ¬ NonIRFieldList (env f) f (rawFields f) ∧
  NonIRFieldList (env f) f (normalFields f)

theorem component_witness : Witness := by
  intro f hf
  exact ⟨⟨context_typed f⟩, ⟨hidden_typed f⟩, (read_and_scan f hf).1,
    (read_and_scan f hf).2, raw_not_nonIR f, normal_nonIR f⟩

theorem nonrefutable (P : Premises4) :
    ¬ (Witness → (Premises4 → False)) :=
  fun h => h component_witness P

end Rcic.F3.PSet.RawNonIRHiddenAttack
