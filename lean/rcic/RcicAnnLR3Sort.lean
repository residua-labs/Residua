import rcic.RcicAnnLR3Chain
import rcic.RcicAnnSortSynthesisA3

/-!
# The new typed-chain sort key

The normalization witnesses of relational synthesis are the new `WhTyA3`
witnesses for the supplied `HeadLayerA3`, including their positive normal
endpoints. The head layer is an explicit parameter throughout, so extending
its positive certificates does not require another logical-relation copy.
The old fuel-indexed inference and old Prop key do not enter these definitions.
-/

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

set_option autoImplicit false

abbrev InferA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (e T : ExprA) : Prop :=
  LR3Sort.InferA3 E (WhTyA3 E I n H) Γ e T

abbrev SortOfA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (A : ExprA) (l : Level) : Prop :=
  LR3Sort.SortOfA3 E (WhTyA3 E I n H) Γ A l

abbrev IsPropTyA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (A : ExprA) : Prop :=
  LR3Sort.IsPropTyA3 E (WhTyA3 E I n H) Γ A

private theorem synthesis_whnf_det (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : LR3Sort.WhnfDetA3 (WhTyA3 E I n H) := by
  intro Γ a b c hb hc
  exact whTyA3_det (H := H) hb hc

private theorem synthesis_sort_refl (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : LR3Sort.SortReflA3 (WhTyA3 E I n H) := by
  intro Γ l
  exact whTyA3_sort (H := H) Γ l

/-- The concrete sort-synthesis datum exposes its actual new typed chain. -/
theorem sortOfA3_spec (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (A : ExprA) (l : Level) :
    SortOfA3 E I n H Γ A l ↔
      ∃ T, InferA3 E I n H Γ A T ∧ WhTyA3 E I n H Γ T (.sort l) := Iff.rfl

theorem inferA3_det {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n)
    {Γ : LCtxA} {e T U : ExprA}
    (h : InferA3 E I n H Γ e T) (h' : InferA3 E I n H Γ e U) : T = U :=
  LR3Sort.InferA3.det (synthesis_whnf_det E I n H) h h'

theorem sortOfA3_det {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n)
    {Γ : LCtxA} {A : ExprA} {l l' : Level}
    (h : SortOfA3 E I n H Γ A l) (h' : SortOfA3 E I n H Γ A l') : l = l' :=
  LR3Sort.SortOfA3.det (synthesis_whnf_det E I n H) h h'

theorem sortOfA3_sort (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (l : Level) : SortOfA3 E I n H Γ (.sort l) (.succ l) :=
  LR3Sort.SortOfA3.sort (synthesis_sort_refl E I n H) Γ l

theorem sortOfA3_pi (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    SortOfA3 E I n H Γ (.pi D u C v) (.imax u v) :=
  LR3Sort.SortOfA3.pi (synthesis_sort_refl E I n H) Γ D u C v

theorem isPropTyA3_iff_of_sort {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n)
    {Γ : LCtxA} {A : ExprA} {l : Level} (h : SortOfA3 E I n H Γ A l) :
    IsPropTyA3 E I n H Γ A ↔ isZero l = true :=
  LR3Sort.isPropTyA3_iff_of_sort (synthesis_whnf_det E I n H) h

theorem not_isPropTyA3_of_sort {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n)
    {Γ : LCtxA} {A : ExprA} {l : Level}
    (h : SortOfA3 E I n H Γ A l) (hz : isZero l = false) :
    ¬ IsPropTyA3 E I n H Γ A :=
  LR3Sort.not_isPropTyA3_of_sort (synthesis_whnf_det E I n H) h hz

theorem not_isPropTyA3_sort (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (l : Level) : ¬ IsPropTyA3 E I n H Γ (.sort l) :=
  LR3Sort.not_isPropTyA3_sort (synthesis_whnf_det E I n H)
    (synthesis_sort_refl E I n H) Γ l

theorem isPropTyA3_pi_iff (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    IsPropTyA3 E I n H Γ (.pi D u C v) ↔ isZero v = true :=
  LR3Sort.isPropTyA3_pi_iff (synthesis_whnf_det E I n H)
    (synthesis_sort_refl E I n H) Γ D u C v

#print axioms sortOfA3_spec
#print axioms inferA3_det
#print axioms sortOfA3_det
#print axioms sortOfA3_sort
#print axioms sortOfA3_pi
#print axioms isPropTyA3_iff_of_sort
#print axioms not_isPropTyA3_of_sort
#print axioms not_isPropTyA3_sort
#print axioms isPropTyA3_pi_iff

end Rcic.Declarative.Ann.LR3
