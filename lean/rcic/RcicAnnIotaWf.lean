import rcic.RcicAnnIotaLaws
import rcic.RcicAnnEnvWf

/-!
# M2-f (2) — the interface realized: the consumers at the concrete ι

Every ι hypothesis of the fundamental theorem and of the `EnvWfA` consumers
(`IotaLiftA`, `IotaSubstA`, `IotaLevelsA`, `IotaRecHeadA`) is discharged at
`iotaIfaceA E` from `EnvClosedA E` / `EnvLevelsA E` alone. What remains on the ι
side is `EnvSemRecA` — the recursors' clause, M2-f (5)'s content — and, since M2-f (3)
made family applications `fam`-typed, `EnvSemIndA` — the families' and constructors'
clause, M2-f (4)'s —
beside the semantic premises (`PosValA`, `EnvSemA`) the theorems already carried.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the fundamental theorem at the concrete ι: closedness is the only ι-side premise. -/
theorem fundA_iota (hE : EnvClosedA E) (hN : EnvNormClosedA E) (hEN : EnvNormCtorTypeA E)
    (hS : EnvSemA E (iotaIfaceA E) n ρ₀) (hρ : PosValA ρ₀) :
    FundHasTyA E (iotaIfaceA E) n ρ₀ ∧ FundConvA E (iotaIfaceA E) n ρ₀ :=
  fundA hE (iotaFnA_lift hE hN) (iotaFnA_subst hE hN) hEN hN (iotaFnA_recHead E) hS hρ

/-- environment semantics from `EnvWfA` at the concrete ι: `EnvSemIndA` is the
    families' and constructors' clause (M2-f (4)), `EnvSemRecA` the recursors' (M2-f
    (5)). -/
theorem envSemA_of_envWfA_iota (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hInd : EnvSemIndA E (iotaIfaceA E) n ρ₀) (hRec : EnvSemRecA E (iotaIfaceA E) n ρ₀) :
    EnvSemA E (iotaIfaceA E) n ρ₀ :=
  envSemA_of_envWfA hW (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW)) (iotaFnA_recHead E) hρ hInd hRec

/-- row 1 at the concrete ι. -/
theorem sortConvCharA_iota (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hInd : EnvSemIndA E (iotaIfaceA E) n ρ₀) (hRec : EnvSemRecA E (iotaIfaceA E) n ρ₀)
    {Γ : LCtxA} {l₁ l₂ u : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    (h : ConvA E (iotaIfaceA E) n Γ (.sort l₁) (.sort l₂) (.sort u)) : eqN l₁ l₂ :=
  sortConvCharA_wf hW (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW)) (iotaFnA_recHead E) hρ hInd hRec hΓ h

/-- row 2 at the concrete ι. -/
theorem piConvInjA_iota (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hInd : EnvSemIndA E (iotaIfaceA E) n ρ₀) (hRec : EnvSemRecA E (iotaIfaceA E) n ρ₀)
    {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA}
    {v : Level} {D' : ExprA} {u' : Level} {C' : ExprA} {v' w : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    (h : ConvA E (iotaIfaceA E) n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E (iotaIfaceA E) n Γ D D') ∧
      Nonempty (TyConvA E (iotaIfaceA E) n (.assumption D :: Γ) C C') :=
  piConvInjA_wf hW (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW)) (iotaFnA_recHead E) hρ hInd hRec hΓ h

#print axioms fundA_iota
#print axioms envSemA_of_envWfA_iota
#print axioms sortConvCharA_iota
#print axioms piConvInjA_iota

end Rcic.Declarative.Ann
