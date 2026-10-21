import rcic.RcicSynBelowScoped
import rcic.RcicTypedGroupPins

/-!
# Step 4c-S1a: inhabited native scope and ambient-guard tooth

The positive consumer uses the admitted Nat group and a nonempty native context.
The negative consumer rejects that same environment/context under an empty
ambient environment; deleting the inclusion guard wrongly accepts it.
These checks do not assert an inhabitant of `AllBelowScoped`. `closure_claim = 0`.
-/

namespace Rcic.Syn.BelowScopedPins

open Rcic.Declarative

/-- A native context whose domain typing actually reads the Nat family member. -/
def natCtx : CtxWfT natEnvU 0 [.assumption (.const 0 [])] :=
  .assumption [] (.const 0 []) (.succ .zero) .nil (natConstTyT rfl)

/-- Unconditional inhabitant of the full scope interface at a real admitted group. -/
def natScope : ScopedCtx natEnvU natEnvU 0 [.assumption (.const 0 [])] :=
  ⟨natEnvUWfT, envExt_refl natEnvU, natCtx⟩

/-- Consuming the scope produces the expected nonempty canonical disposition. -/
theorem natScope_can : natScope.can id = [.keep] := rfl

/-- The existing disposition-validity contract consumes the concrete native scope. -/
theorem natScope_canDispForHom :
    DispForHom id natEnvU 0 [.assumption (.const 0 [])] [.keep] :=
  natScope.canDispForHom levelHom_id

/-- The fixed ambient table cannot cover Nat members when its environment is empty. -/
theorem natScope_emptyAmbient_rejected :
    ¬ Nonempty (ScopedCtx emptyEnv natEnvU 0 [.assumption (.const 0 [])]) := by
  rintro ⟨S⟩
  have h := S.ext 0 natFamMember rfl
  cases h

/-- Deliberately weakened guard used only to expose the ambient-inclusion mutant. -/
structure WithoutAmbientGuard (_Eₐ E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  env : EnvWfT E
  ctx : CtxWfT E n Γ

/-- Removing `ext` wrongly accepts the exact environment/context rejected above. -/
def emptyAmbient_mutant :
    WithoutAmbientGuard emptyEnv natEnvU 0 [.assumption (.const 0 [])] :=
  ⟨natEnvUWfT, natCtx⟩

/-- Paired tooth: positive acceptance by the mutant and rejection by the approved interface. -/
theorem ambientGuard_tooth :
    Nonempty (WithoutAmbientGuard emptyEnv natEnvU 0 [.assumption (.const 0 [])]) ∧
    ¬ Nonempty (ScopedCtx emptyEnv natEnvU 0 [.assumption (.const 0 [])]) :=
  ⟨⟨emptyAmbient_mutant⟩, natScope_emptyAmbient_rejected⟩

end Rcic.Syn.BelowScopedPins
