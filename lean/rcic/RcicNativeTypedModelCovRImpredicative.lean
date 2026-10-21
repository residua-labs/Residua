import Lean

/-!
# Prop-valued quantification over realization predicates

This checks the candidate quantifier before selecting any semantic closure
conditions. The predicate space can live in an arbitrary Type universe; its
universal quantification still lives in Prop. No normalization or candidate
adequacy is inferred from this universe check. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

universe u

def covRQuantifyCandidate {α : Type u}
    (Valid Body : (α → Prop) → Prop) : Prop :=
  ∀ P : α → Prop, Valid P → Body P

theorem covRQuantifyCandidate_true {α : Type u}
    (Valid : (α → Prop) → Prop) :
    covRQuantifyCandidate Valid (fun _ => True) :=
  fun _ _ => True.intro

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_IMPREDICATIVE_ROOTS
#print axioms covRQuantifyCandidate
#print axioms covRQuantifyCandidate_true
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_IMPREDICATIVE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
