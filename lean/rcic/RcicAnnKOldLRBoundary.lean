import rcic.RcicAnnKEqPositive

/-!
# An inhabited expansion boundary after the new contextual K step

The new `Head` has an actual K step from the admitted Eq fixture's neutral
call to a Type-level pi.  The reduct has an explicitly constructed old
logical relation with itself.  Nevertheless the unchanged old logical
relation cannot expand across this new step: it still normalizes through
the old `IotaIfaceA.fn`, where the source is stuck.

This is a failure of that particular composition.  It is not an
impossibility theorem for a logical relation rebuilt over contextual K.
-/

namespace Rcic.Declarative.Ann.KOldLRBoundary

open Rcic.Declarative EqLargeFixture

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- The explicit sort-Prop relation used in both domains and codomains. -/
def propRel (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (a b : ExprA) : Prop :=
  PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
    Nonempty (HasTyA E I n Γ a (.sort .zero)) ∧
    Nonempty (HasTyA E I n Γ b (.sort .zero)) ∧
    Nonempty (ConvA E I n Γ a b (.sort .zero)) ∧ PropEqA E I n Γ a b

section Reduct

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
variable {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}

/-- Structural equality of the actual pi reduct, with no semantic
environment assumption and no choice of lower relations. -/
theorem resultEqKA (hk : ht ρ₀ .zero < k) :
    EqKA E I n ρ₀ k LE LT Γ result result := by
  refine .pi (D := .sort .zero) (C := .sort .zero)
    (D' := .sort .zero) (C' := .sort .zero)
    (u := one) (v := one) (u' := one) (v' := one)
    (whTyA_of_hasTy (resultTyped (E := E) (I := I) (n := n) (Γ := Γ)))
    (whTyA_of_hasTy (resultTyped (E := E) (I := I) (n := n) (Γ := Γ)))
    (eqNA_refl _) (eqNA_refl _)
    ⟨.sort Γ .zero⟩ ⟨.sort _ .zero⟩ ⟨.sort Γ .zero⟩ ⟨.sort _ .zero⟩
    (fun ρ => propRel E I n (wkCtxA ρ Γ)) ?_ ?_ ?_ ⟨.refl Γ result⟩
  · intro ρ _
    simp only [wkExprA_sort]
    exact .sortP (whTyA_of_hasTy (.sort _ .zero)) rfl
  · intro ρ _
    simp only [wkExprA_sort]
    exact .sort (whTyA_of_hasTy (.sort _ .zero))
      (whTyA_of_hasTy (.sort _ .zero)) hk (eqNA_refl _) ⟨.refl _ _⟩
  · intro ρ _ a a' _
    simp only [wkExprA_sort]
    exact .sort (whTyA_of_hasTy (.sort _ .zero))
      (whTyA_of_hasTy (.sort _ .zero)) hk (eqNA_refl _) ⟨.refl _ _⟩

/-- The pi reduct is also a valid old semantic type, not only self-equal. -/
theorem resultTyKA (hk : ht ρ₀ .zero < k) :
    ∃ R, TyKA E I n ρ₀ k LE LT Γ result R := by
  have hnp : ¬ IsPropTy E I Γ result :=
    fun h => absurd ((isPropTy_pi_iff E I Γ (.sort .zero) one (.sort .zero) one).mp h)
      (by decide)
  refine ⟨_, .pi (D := .sort .zero) (C := .sort .zero) (u := one) (v := one)
    (whTyA_of_hasTy (resultTyped (E := E) (I := I) (n := n) (Γ := Γ))) hnp
    ⟨.sort Γ .zero⟩ ⟨.sort _ .zero⟩
    (fun ρ => propRel E I n (wkCtxA ρ Γ)) ?_
    (fun ρ _ => propRel E I n (wkCtxA ρ Γ)) ?_ ?_⟩
  · intro ρ _
    simp only [wkExprA_sort]
    exact .sortP (whTyA_of_hasTy (.sort _ .zero)) rfl
  · intro ρ _ a a' _
    simp only [wkExprA_sort]
    exact .sortP (whTyA_of_hasTy (.sort _ .zero)) rfl
  · intro ρ _ a a' _
    simp only [wkExprA_sort]
    exact .sort (whTyA_of_hasTy (.sort _ .zero))
      (whTyA_of_hasTy (.sort _ .zero)) hk (eqNA_refl _) ⟨.refl _ _⟩

theorem resultLREq (hk : ht ρ₀ .zero < k) :
    LREqA E I n ρ₀ k Γ result result := by
  rw [LREqA_eq]
  exact resultEqKA hk

theorem resultLRTy (hk : ht ρ₀ .zero < k) :
    ∃ R, LRTyA E I n ρ₀ k Γ result R := by
  rw [LRTyA_eq]
  exact resultTyKA hk

/-- The reduct is actually related to itself as an element of `Sort 1`. -/
theorem resultRelated (hk : ht ρ₀ one < k) :
    LRRelA E I n ρ₀ k Γ (.sort one) result result := by
  have hlow : ht ρ₀ .zero < ht ρ₀ one := by
    rw [ht_succ]
    exact Nat.lt_succ_self _
  refine ⟨(fun a b =>
    LREqA E I n ρ₀ (ht ρ₀ one) Γ a b ∧
    (∃ R, LRTyA E I n ρ₀ (ht ρ₀ one) Γ a R) ∧
    (∃ R, LRTyA E I n ρ₀ (ht ρ₀ one) Γ b R) ∧
    Nonempty (HasTyA E I n Γ a (.sort one)) ∧
    Nonempty (HasTyA E I n Γ b (.sort one)) ∧
    Nonempty (ConvA E I n Γ a b (.sort one))), ?_, ?_⟩
  · rw [LRTyA_eq]
    exact .sortT (whTyA_of_hasTy (.sort Γ one)) rfl hk
  · exact ⟨resultLREq hlow, resultLRTy hlow, resultLRTy hlow,
      ⟨resultTyped⟩, ⟨resultTyped⟩, ⟨.refl Γ result (.sort one) resultTyped⟩⟩

end Reduct

/-- The source's existing typing is supplied by the new K soundness theorem. -/
theorem sourceTyped : Nonempty (HasTyA env (iotaIfaceA env) 0 context
    (call (.bvar 0)) (.sort one)) := by
  obtain ⟨hc⟩ := KEqPositive.eqFrame_sound
  exact ⟨convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc⟩

/-- Old structural type equality still rejects this source against the pi
reduct, at every height and valuation, even though the new K Head steps. -/
theorem sourceNotEq {ρ₀ : Nat → Nat} {k : Nat} :
    ¬ LREqA env (iotaIfaceA env) 0 ρ₀ k context (call (.bvar 0)) result := by
  intro heq
  rw [LREqA_eq] at heq
  obtain ⟨ht⟩ := sourceTyped
  exact eqKA_tripleLike_typi_false (D := .sort .zero) (u := one)
    (C := .sort .zero) (v := one) rfl (whTyA_of_hasTy ht)
    (tripleLikeA_of_stuck callStuck) heq

theorem sourceNotRelated {ρ₀ : Nat → Nat} {k : Nat} :
    ¬ LRRelA env (iotaIfaceA env) 0 ρ₀ k context (.sort one)
      (call (.bvar 0)) result :=
  fun h => sourceNotEq (LREqA_of_sortRel h)

/-- A concrete positive height for the old relation at the reduct. -/
abbrev height : Nat := ht (fun _ => 1) one + 1

/-- The exact failed expansion implication has an inhabited premise. -/
theorem expansionAtStep_false :
    ¬ (LRRelA env (iotaIfaceA env) 0 (fun _ => 1) height context (.sort one)
        result result →
      LRRelA env (iotaIfaceA env) 0 (fun _ => 1) height context (.sort one)
        (call (.bvar 0)) result) :=
  fun h => sourceNotRelated (h (resultRelated (Nat.lt_succ_self _)))

/-- All premises of the post-K expansion test are supplied: admission,
context, closed proof inhabitant, actual new Head step, its result-type
conversion, both endpoint typings, and the old semantic relation of the
reduct.  Only expansion into the unchanged old relation fails. -/
theorem inhabited_expansion_boundary :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter) domain) ∧
    KStage.Head env (iotaIfaceA env) 0 context
      (call (.bvar 0)) result KEqPositive.eqShape.resultType ∧
    Nonempty (TyConvA env (iotaIfaceA env) 0 context
      KEqPositive.eqShape.resultType (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (call (.bvar 0)) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context result (.sort one)) ∧
    LRRelA env (iotaIfaceA env) 0 (fun _ => 1) height context (.sort one) result result ∧
    ¬ LRRelA env (iotaIfaceA env) 0 (fun _ => 1) height context (.sort one)
      (call (.bvar 0)) result :=
  ⟨wf, ⟨contextWf⟩, ⟨reflTyped .nil parameterTyped⟩, KEqPositive.eqHead,
    ⟨motiveTypeConv contextWf parameterTyped majorTyped⟩, sourceTyped, ⟨resultTyped⟩,
    resultRelated (Nat.lt_succ_self _), sourceNotRelated⟩

#print axioms propRel
#print axioms resultEqKA
#print axioms resultTyKA
#print axioms resultLREq
#print axioms resultLRTy
#print axioms resultRelated
#print axioms sourceTyped
#print axioms sourceNotEq
#print axioms sourceNotRelated
#print axioms height
#print axioms expansionAtStep_false
#print axioms inhabited_expansion_boundary

end Rcic.Declarative.Ann.KOldLRBoundary
