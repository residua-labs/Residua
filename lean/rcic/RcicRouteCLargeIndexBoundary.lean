import rcic.RcicAnnFamHeight
import rcic.RcicAnnCtorSem

/-!
# Route C, R2: the unchanged small-index hypothesis cannot be removed

The landed family `F : (x : Sort 1) → Sort 1`, with `x` declared as an
index, already supplies an admitted counterexample to the existing relation.
This module composes that receipt with every other hypothesis of
`envSemA_of_envWfA_groups`, including its recursor clause. The environment
contains only the family, so the recursor clause is supplied without any
large-elimination premise. The closed term `F (Sort 0) : Sort 1` is related
to nothing by the old relation, at every height.

This is a refutation of deleting `SmallIndexProfileA` while retaining the
old conclusion. It does not refute a redesigned family relation whose index
walk has an independently justified height, or claim a new row supplier.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.RouteCLargeIndex

/-- The actual admitted group, with its sole binder declared as an index. -/
def envWf : EnvWfA noIotaA (pinFamFEnvA 0) :=
  pinFamFEnvWfA 0 pinFamF0ViewA

/-- Every member of this environment is the family; there is no recursor. -/
theorem noRec : NoRecA (pinFamFEnvA 0) := by
  intro r m hm hr
  rw [pinFamF_ind hm] at hr
  cases hr

/-- The recursor hypothesis of the requested theorem is actually supplied. -/
theorem recSem (n : Nat) (ρ₀ : Nat → Nat) :
    EnvSemRecA (pinFamFEnvA 0) noIotaA n ρ₀ :=
  envSemRecA_of_noRec noRec

/-- All hypotheses of `envSemA_of_envWfA_groups` except its small-index
profile, at the concrete positive valuation `fun _ => 1`. -/
theorem remaining_premises (n : Nat) :
    Nonempty (EnvWfA noIotaA (pinFamFEnvA 0)) ∧
    IotaLiftA noIotaA ∧ IotaSubstA noIotaA ∧ IotaLevelsA noIotaA ∧
    EnvNormCtorTypeA (pinFamFEnvA 0) ∧ EnvNormClosedA (pinFamFEnvA 0) ∧
    IotaRecHeadA (pinFamFEnvA 0) noIotaA ∧ PosValA (fun _ => 1) ∧
    EnvSemRecA (pinFamFEnvA 0) noIotaA n (fun _ => 1) :=
  ⟨⟨envWf⟩, noIotaA_lift, noIotaA_subst, noIotaA_levels,
    envWfA_normCtorType envWf, envWfA_normClosed envWf,
    noIotaA_recHead _, posValA_one, recSem n (fun _ => 1)⟩

/-- The application is typed in the empty, well-formed context. Neither a
context assumption nor a semantic interpretation is needed to type it. -/
theorem closed_application (n : Nat) :
    Nonempty (CtxWfA (pinFamFEnvA 0) noIotaA n []) ∧
    Nonempty (HasTyA (pinFamFEnvA 0) noIotaA n [] pinFamFAppA
      (.sort (.succ .zero))) :=
  ⟨⟨.nil⟩, ⟨pinFamFAppTy (pinFamF_members 0) n []⟩⟩

/-- The existing fixed-height family walk cannot relate this typed closed
application to any term, regardless of the outer height chosen. -/
theorem closed_application_unrelated (n k : Nat) (B : ExprA) :
    ¬ LRRelA (pinFamFEnvA 0) noIotaA n (fun _ => 1) k []
      (.sort (.succ .zero)) pinFamFAppA B :=
  pinFamF0App_refuted n (fun _ => 1) k [] B

/-- An explicit inhabited counterexample to the old semantic conclusion. -/
theorem inhabited_boundary (n : Nat) :
    Nonempty (EnvWfA noIotaA (pinFamFEnvA 0)) ∧
    Nonempty (CtxWfA (pinFamFEnvA 0) noIotaA n []) ∧
    Nonempty (HasTyA (pinFamFEnvA 0) noIotaA n [] pinFamFAppA
      (.sort (.succ .zero))) ∧
    NoRecA (pinFamFEnvA 0) ∧
    EnvSemRecA (pinFamFEnvA 0) noIotaA n (fun _ => 1) ∧
    ¬ SmallIndexProfileA (pinFamFEnvA 0) ∧
    ¬ EnvSemA (pinFamFEnvA 0) noIotaA n (fun _ => 1) :=
  ⟨⟨envWf⟩, (closed_application n).1, (closed_application n).2, noRec,
    recSem n (fun _ => 1), pinFamF0_not_small, pinFamF0_envSem_false posValA_one⟩

/-- The literal analogue with the small-index hypothesis removed. Naming
this proposition records the exact failed statement; it is not a supplier. -/
def GroupsWithoutSmallIndex : Prop :=
  ∀ (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat),
    EnvWfA I E → IotaLiftA I → IotaSubstA I → IotaLevelsA I →
    EnvNormCtorTypeA E → EnvNormClosedA E → IotaRecHeadA E I →
    PosValA ρ₀ → EnvSemRecA E I n ρ₀ → EnvSemA E I n ρ₀

/-- All remaining hypotheses have concrete witnesses, so the failure is
unconditional. The contradiction is the landed large-index receipt. -/
theorem not_groupsWithoutSmallIndex : ¬ GroupsWithoutSmallIndex := by
  intro h
  exact pinFamF0_envSem_false posValA_one
    (h (pinFamFEnvA 0) noIotaA 0 (fun _ => 1) envWf noIotaA_lift
      noIotaA_subst noIotaA_levels (envWfA_normCtorType envWf)
      (envWfA_normClosed envWf) (noIotaA_recHead _) posValA_one
      (recSem 0 (fun _ => 1)))

-- BEGIN RCIC_ROUTE_C_LARGE_INDEX_ROOTS
#print axioms envWf
#print axioms noRec
#print axioms recSem
#print axioms remaining_premises
#print axioms closed_application
#print axioms closed_application_unrelated
#print axioms inhabited_boundary
#print axioms GroupsWithoutSmallIndex
#print axioms not_groupsWithoutSmallIndex
-- END RCIC_ROUTE_C_LARGE_INDEX_ROOTS

end Rcic.Declarative.Ann.RouteCLargeIndex
