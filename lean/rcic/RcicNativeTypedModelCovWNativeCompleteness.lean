import rcic.RcicNativeTypedModelCovWNativeCore
import rcic.RcicNativeTypedModelCovWNativeUniverse

/-!
# Exact finite observations do not determine native types

The two Pi types below share one native universe, every tagged observation,
and therefore every public observed compact. Their domains are Sort 1 and
Sort 2, which native Pi injectivity distinguishes. This tests full equality
of observation sets, not merely the shared bottom observation.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelKFragmentAudit TypedModelCovWIrrelAudit

theorem covWNative_empty_sort_shape {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT emptyEnv n Γ) {ρ : EnvWIrrel} {l : Level} {c : CptWIrrel}
    (h : ApproxTKWNative emptyEnv n Γ ρ (.sort l) c) :
    c = .bot ∨ c = sortCodeWIrrel l := by
  generalize heq : (Expr.sort l : Expr Nat) = e at h
  cases h with
  | bot => exact Or.inl rfl
  | sort => cases heq; exact Or.inr rfl
  | bvar => cases heq
  | const => cases heq
  | recursor => cases heq
  | pi => cases heq
  | lam => cases heq
  | app => cases heq
  | appSpine => cases heq
  | delta => cases heq
  | letE => cases heq
  | lit => cases heq
  | iota w _ =>
      have hh := w.hrec
      simp [emptyEnv] at hh
  | recursorPropK w _ _ _ _ _ _ =>
      have hh := w.hrec
      simp [emptyEnv] at hh
  | eta he _ _ _ _ =>
      cases heq
      exact (covWIrrel_native_not_sort_and_pi (.empty : EnvWfT emptyEnv)
        trivial hΓ (.sort Γ l) he).elim

theorem covWNative_empty_sort_transport {n : Nat} {Γ Δ : LCtx}
    (hΓ : CtxWfT emptyEnv n Γ) {ρ τ : EnvWIrrel} {l k : Level} {c : CptWIrrel}
    (hk : sortCodeWIrrel l = sortCodeWIrrel k)
    (h : ApproxTKWNative emptyEnv n Γ ρ (.sort l) c) :
    ApproxTKWNative emptyEnv n Δ τ (.sort k) c := by
  rcases covWNative_empty_sort_shape hΓ h with rfl | rfl
  · exact .bot _ _ _
  · rw [hk]
    exact .sort _ _ _

theorem covWNativeUniverse_to_B {n : Nat} {ρ : EnvWIrrel} {c : CptWIrrel}
    (h : ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseA c) :
    ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseB c := by
  change ApproxTKWNative emptyEnv n [] ρ
    (.pi (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))) c at h
  generalize heq : (Expr.pi (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) : Expr Nat) = e at h
  cases h with
  | bot => exact .bot _ _ _
  | pi hA ht hb =>
      cases heq
      refine .pi (covWNative_empty_sort_transport .nil (by rfl) hA) ht ?_
      intro s hs
      exact covWNative_empty_sort_transport
        (.assumption [] _ _ .nil (.sort [] (.succ .zero))) rfl (hb s hs)
  | bvar => cases heq
  | sort => cases heq
  | const => cases heq
  | recursor => cases heq
  | lam => cases heq
  | app => cases heq
  | appSpine => cases heq
  | delta => cases heq
  | letE => cases heq
  | lit => cases heq
  | iota w _ =>
      have hh := w.hrec
      simp [emptyEnv] at hh
  | recursorPropK w _ _ _ _ _ _ =>
      have hh := w.hrec
      simp [emptyEnv] at hh
  | eta he _ _ _ _ =>
      cases heq
      exact (covWIrrel_native_not_sort_and_pi (.empty : EnvWfT emptyEnv)
        trivial .nil (covWNativeUniverseA_ty n []) he).elim

theorem covWNativeUniverse_to_A {n : Nat} {ρ : EnvWIrrel} {c : CptWIrrel}
    (h : ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseB c) :
    ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseA c := by
  change ApproxTKWNative emptyEnv n [] ρ
    (.pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero)))) c at h
  generalize heq : (Expr.pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero))) : Expr Nat) = e at h
  cases h with
  | bot => exact .bot _ _ _
  | pi hA ht hb =>
      cases heq
      refine .pi (covWNative_empty_sort_transport .nil (by rfl) hA) ht ?_
      intro s hs
      exact covWNative_empty_sort_transport
        (.assumption [] _ _ .nil (.sort [] (.succ (.succ .zero)))) rfl (hb s hs)
  | bvar => cases heq
  | sort => cases heq
  | const => cases heq
  | recursor => cases heq
  | lam => cases heq
  | app => cases heq
  | appSpine => cases heq
  | delta => cases heq
  | letE => cases heq
  | lit => cases heq
  | iota w _ =>
      have hh := w.hrec
      simp [emptyEnv] at hh
  | recursorPropK w _ _ _ _ _ _ =>
      have hh := w.hrec
      simp [emptyEnv] at hh
  | eta he _ _ _ _ =>
      cases heq
      exact (covWIrrel_native_not_sort_and_pi (.empty : EnvWfT emptyEnv)
        trivial .nil (covWNativeUniverseB_ty n []) he).elim

theorem covWNativeUniverse_all_tagged (n : Nat) (ρ : EnvWIrrel) (c : CptWIrrel) :
    ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseA c ↔
    ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseB c :=
  ⟨covWNativeUniverse_to_B, covWNativeUniverse_to_A⟩

theorem covWNativeUniverse_all_observations (n : Nat) (ρ : EnvWIrrel) (c : CptT) :
    CovWNativeObservation emptyEnv n [] ρ covWNativeUniverseA c ↔
    CovWNativeObservation emptyEnv n [] ρ covWNativeUniverseB c := by
  constructor
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, covWNativeUniverse_to_B ho⟩
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, covWNativeUniverse_to_A ho⟩

def covWNativeUniverseCode : CptWIrrel := .pi .sort [([], .sort)]

theorem covWNativeUniverse_code (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWNative emptyEnv n [] ρ covWNativeUniverseA covWNativeUniverseCode := by
  refine .pi (.sort _ _ (.succ .zero)) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .sort _ _ (.succ (.succ .zero))

theorem covWNativeUniverse_code_typed :
    CTyS emptyEnv (covWIrrelErase covWNativeUniverseCode) .sort := by
  change CTyS emptyEnv (.pi .sort [([], .sort)]) .sort
  rw [CTyS]
  refine Or.inr (.pi .sort ?_)
  intro s hs
  obtain rfl := List.mem_singleton.mp hs
  exact .sort

/-- Even the closed, common-universe version of code completeness is an
additional proposition. The antecedent compares every finite observation. -/
def CovWNativeCodesDetermineTypes : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (A B : Expr Nat) (l : Level),
    EnvWfT E → HasTyT E n [] A (.sort l) → HasTyT E n [] B (.sort l) →
    (∀ c, CovWNativeObservation E n [] EnvWIrrel.bot A c ↔
      CovWNativeObservation E n [] EnvWIrrel.bot B c) →
    Nonempty (ConvT E n [] A B (.sort l))

theorem covWNative_codes_do_not_determine_types : ¬ CovWNativeCodesDetermineTypes := by
  intro hc
  exact covWNativeUniverse_not_conv 0 covWNativeUniverseLevel
    (hc emptyEnv 0 covWNativeUniverseA covWNativeUniverseB covWNativeUniverseLevel
      .empty (covWNativeUniverseA_ty 0 []) (covWNativeUniverseB_ty 0 [])
      (covWNativeUniverse_all_observations 0 EnvWIrrel.bot))

theorem covWNative_codes_boundary_inhabited (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    CovWNativeRealized emptyEnv n 2 [] EnvWIrrel.bot SubstT.id ∧
    Nonempty (HasTyT emptyEnv n [] covWNativeUniverseA (.sort covWNativeUniverseLevel)) ∧
    Nonempty (HasTyT emptyEnv n [] covWNativeUniverseB (.sort covWNativeUniverseLevel)) ∧
    ApproxTKWNative emptyEnv n [] EnvWIrrel.bot
      (.sort covWNativeUniverseLevel) .sort ∧
    covWNativeUniverseCode ≠ .bot ∧
    CTyS emptyEnv (covWIrrelErase covWNativeUniverseCode) .sort ∧
    ApproxTKWNative emptyEnv n [] EnvWIrrel.bot covWNativeUniverseA covWNativeUniverseCode ∧
    ApproxTKWNative emptyEnv n [] EnvWIrrel.bot covWNativeUniverseB covWNativeUniverseCode ∧
    (∀ c, CovWNativeObservation emptyEnv n [] EnvWIrrel.bot covWNativeUniverseA c ↔
      CovWNativeObservation emptyEnv n [] EnvWIrrel.bot covWNativeUniverseB c) ∧
    ¬ Nonempty (ConvT emptyEnv n [] covWNativeUniverseA covWNativeUniverseB
      (.sort covWNativeUniverseLevel)) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, covWNative_realized_nil emptyEnv n 2,
    ⟨covWNativeUniverseA_ty n []⟩, ⟨covWNativeUniverseB_ty n []⟩,
    .sort _ _ covWNativeUniverseLevel, (by intro h; cases h),
    covWNativeUniverse_code_typed,
    covWNativeUniverse_code n EnvWIrrel.bot,
    covWNativeUniverse_to_B (covWNativeUniverse_code n EnvWIrrel.bot),
    covWNativeUniverse_all_observations n EnvWIrrel.bot,
    covWNativeUniverse_not_conv n covWNativeUniverseLevel⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_COMPLETENESS_ROOTS
#print axioms covWNative_empty_sort_shape
#print axioms covWNative_empty_sort_transport
#print axioms covWNativeUniverse_to_B
#print axioms covWNativeUniverse_to_A
#print axioms covWNativeUniverse_all_tagged
#print axioms covWNativeUniverse_all_observations
#print axioms covWNativeUniverseCode
#print axioms covWNativeUniverse_code
#print axioms covWNativeUniverse_code_typed
#print axioms CovWNativeCodesDetermineTypes
#print axioms covWNative_codes_do_not_determine_types
#print axioms covWNative_codes_boundary_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_COMPLETENESS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
