import rcic.RcicAnnLR3Head

/-!
# The certified head parameter shared by the LR3 cone

The logical relation depends on these proved head laws, so a later richer
positive apartness language can supply another instance of the same cone.
The concrete instance below is built from the actual contextual head and
positive normal derivations.  The interface supplies no transport, coverage,
totality, or semantic-environment theorem.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

structure HeadLayerA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) where
  step : LCtxA → ExprA → ExprA → ExprA → Prop
  normal : LCtxA → ExprA → Prop
  deterministic : ∀ {Γ : LCtxA} {a b c T U : ExprA},
    step Γ a b T → step Γ a c U → b = c
  normal_excludes : ∀ {Γ : LCtxA} {a b T : ExprA},
    normal Γ a → step Γ a b T → False
  normal_sort : ∀ (Γ : LCtxA) (l : Level), normal Γ (.sort l)
  normal_pi : ∀ (Γ : LCtxA) (D : ExprA) (u : Level) (C : ExprA) (v : Level),
    normal Γ (.pi D u C v)
  normal_lam : ∀ (Γ : LCtxA) (D : ExprA) (u : Level) (b : ExprA),
    normal Γ (.lam D u b)
  sound : EnvClosedA E → IotaLiftA I → IotaRecHeadA E I → IotaSubstA I →
    ∀ {Γ : LCtxA}, CtxWfA E I n Γ → ∀ {a b T : ExprA},
      step Γ a b T → Nonempty (ConvA E I n Γ a b T)

/-- Actual proved instance: no algebraic law is left as a caller premise. -/
def contextualHeadLayerA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    HeadLayerA3 E I n where
  step := HeadA3 E I n
  normal := NormalA3 E I n
  deterministic := headA3_deterministic
  normal_excludes := normalA3_no_head
  normal_sort := fun _ l => .sort l
  normal_pi := fun _ D u C v => .pi D u C v
  normal_lam := fun _ D u b => .lam D u b
  sound := HeadA3.conv

#print axioms HeadLayerA3
#print axioms contextualHeadLayerA3

end Rcic.Declarative.Ann.LR3
