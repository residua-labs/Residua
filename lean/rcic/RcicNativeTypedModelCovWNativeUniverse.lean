import rcic.RcicNativeTypedModelCovWIrrelShape

/-!
# Two native Pi types in one universe with different universe domains

Both displayed types inhabit Sort 3. Native Pi injectivity and native sort
separation distinguish them, independently of any observation relation.
This module supplies the native half of the code-completeness measurement.
No normalization or confluence hypothesis is used. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelCovWIrrelAudit

def covWNativeUniverseA : Expr Nat :=
  .pi (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))

def covWNativeUniverseB : Expr Nat :=
  .pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero)))

def covWNativeUniverseLevel : Level := .succ (.succ (.succ .zero))

def covWNativeUniverseA_ty (n : Nat) (Γ : LCtx) :
    HasTyT emptyEnv n Γ covWNativeUniverseA (.sort covWNativeUniverseLevel) :=
  .conv Γ _ (.sort (.imax (.succ (.succ .zero)) covWNativeUniverseLevel))
    (.sort covWNativeUniverseLevel) _
    (.pi Γ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort (.succ (.succ .zero))) covWNativeUniverseLevel
      (.sort Γ (.succ .zero)) (.sort _ (.succ (.succ .zero))))
    (.sorts Γ _ _ (fun _ => rfl))

def covWNativeUniverseB_ty (n : Nat) (Γ : LCtx) :
    HasTyT emptyEnv n Γ covWNativeUniverseB (.sort covWNativeUniverseLevel) :=
  .conv Γ _ (.sort (.imax covWNativeUniverseLevel covWNativeUniverseLevel))
    (.sort covWNativeUniverseLevel) _
    (.pi Γ (.sort (.succ (.succ .zero))) covWNativeUniverseLevel
      (.sort (.succ (.succ .zero))) covWNativeUniverseLevel
      (.sort Γ (.succ (.succ .zero))) (.sort _ (.succ (.succ .zero))))
    (.sorts Γ _ _ (fun _ => rfl))

theorem covWNativeUniverse_not_tyConv (n : Nat) :
    ¬ Nonempty (TyConvT emptyEnv n [] covWNativeUniverseA covWNativeUniverseB) := by
  rintro ⟨h⟩
  obtain ⟨⟨hd⟩, _⟩ :=
    (Ann.typedRowsWf_of_envWfT_semPrefix (.empty : EnvWfT emptyEnv) trivial n).piRow
      (.nil : CtxWfT emptyEnv n []) h
  have he := covWIrrel_native_sort_separation (.empty : EnvWfT emptyEnv)
    trivial (.nil : CtxWfT emptyEnv n []) hd
  have hn := he (fun _ => some 0)
  change (some 1 : Option Nat) = some 2 at hn
  cases hn

theorem covWNativeUniverse_not_conv (n : Nat) (u : Level) :
    ¬ Nonempty (ConvT emptyEnv n [] covWNativeUniverseA covWNativeUniverseB (.sort u)) := by
  rintro ⟨h⟩
  exact covWNativeUniverse_not_tyConv n ⟨.of [] _ _ u h⟩

theorem covWNativeUniverse_native_inhabited (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] covWNativeUniverseA (.sort covWNativeUniverseLevel)) ∧
    Nonempty (HasTyT emptyEnv n [] covWNativeUniverseB (.sort covWNativeUniverseLevel)) ∧
    ¬ Nonempty (TyConvT emptyEnv n [] covWNativeUniverseA covWNativeUniverseB) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨covWNativeUniverseA_ty n []⟩,
    ⟨covWNativeUniverseB_ty n []⟩, covWNativeUniverse_not_tyConv n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_UNIVERSE_ROOTS
#print axioms covWNativeUniverseA
#print axioms covWNativeUniverseB
#print axioms covWNativeUniverseLevel
#print axioms covWNativeUniverseA_ty
#print axioms covWNativeUniverseB_ty
#print axioms covWNativeUniverse_not_tyConv
#print axioms covWNativeUniverse_not_conv
#print axioms covWNativeUniverse_native_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_UNIVERSE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
