import rcic.RcicStepArmsEnvWf
import rcic.RcicDT0709EnvWf

/-!
# The current unguarded `PiRowInjT` front is uninhabited

`TyConvT.refl` accepts every expression without typing evidence.
The current `PiRowInjT` nevertheless demands typed `ConvT` witnesses
for the domain and codomain of every pair of Pi expressions related
by `TyConvT`.  Apply it in the empty context to the reflexive relation
on `pi (bvar 0) (sort 0)`.  Its domain witness, together with the
existing endpoint theorem, would type `bvar 0` in the empty context;
the existing variable-inversion theorem rules this out.

This refutes that particular unguarded row contract, even when the
environment and context are well formed.  It is not a counterexample
to Pi injectivity with typed Pi inputs.  No definition or consumer of
`PiRowInjT` is changed here.
-/

namespace Rcic.Declarative

/-- The contradiction uses an ill-typed Pi expression admitted by
    `TyConvT.refl`; adding context well-formedness alone cannot exclude it. -/
theorem no_piRowInjT_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    ¬ Nonempty (PiRowInjT E) := by
  rintro ⟨hrow⟩
  have hpi : TyConvT E 0 []
      (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 0) (.sort .zero)) :=
    .refl [] (.pi (.bvar 0) (.sort .zero))
  obtain ⟨u, _v, ⟨hdom⟩, _⟩ := hrow hpi
  obtain ⟨ht⟩ := (DT009T_endpoints_envWfT hW CtxWfT.nil hdom).1
  obtain ⟨_A, hlookup, _⟩ := hasTyTInv_bvar ht rfl
  cases hlookup

/-- Concrete empty-environment pin for the existing row definition. -/
theorem pin_no_piRowInjT_empty : ¬ Nonempty (PiRowInjT emptyEnv) :=
  no_piRowInjT_of_envWfT EnvWfT.empty

#print axioms no_piRowInjT_of_envWfT
#print axioms pin_no_piRowInjT_empty

end Rcic.Declarative
