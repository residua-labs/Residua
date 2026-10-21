import rcic.RcicAnnIotaWf
import rcic.RcicAnnLREnvG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnLRRowsG
/-!
# M2-f (2) — the interface realized: the consumers at the concrete ι

Every ι hypothesis of the fundamental theorem and of the `EnvWfA` consumers
(`IotaLiftA`, `IotaSubstA`, `IotaLevelsA`, `IotaRecHeadA`) is discharged at
`iotaIfaceA E` from `EnvClosedA E` / `EnvLevelsA E` alone. What remains on the ι
side is `EnvSemRecAg` — the recursors' clause, M2-f (5)'s content — and, since M2-f (3)
made family applications `fam`-typed, `EnvSemIndAg` — the families' and constructors'
clause, M2-f (4)'s —
beside the semantic premises (`PosValA`, `EnvSemAg`) the theorems already carried.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the fundamental theorem at the concrete ι: closedness is the only ι-side premise. -/
theorem fundA_iotag (hE : EnvClosedA E) (hN : EnvNormClosedA E) (hEN : EnvNormCtorTypeA E)
    (hS : EnvSemAg E (iotaIfaceA E) n ρ₀) (hρ : PosValA ρ₀) (hK : PropKeyA E (iotaIfaceA E) n) :
    FundHasTyAg E (iotaIfaceA E) n ρ₀ ∧ FundConvAg E (iotaIfaceA E) n ρ₀ :=
  fundAg hE (iotaFnA_lift hE hN) (iotaFnA_subst hE hN) hEN hN (iotaFnA_recHead E) hS hρ hK

/-- environment semantics from `EnvWfA` at the concrete ι: `EnvSemIndAg` is the
    families' and constructors' clause (M2-f (4)), `EnvSemRecAg` the recursors' (M2-f
    (5)). -/
theorem envSemA_of_envWfA_iotag (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hK : PropKeyA E (iotaIfaceA E) n) (hInd : EnvSemIndAg E (iotaIfaceA E) n ρ₀) (hRec : EnvSemRecAg E (iotaIfaceA E) n ρ₀) :
    EnvSemAg E (iotaIfaceA E) n ρ₀ :=
  envSemA_of_envWfAg hW (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW)) (iotaFnA_recHead E) hρ hK hInd hRec

#print axioms fundA_iotag
#print axioms envSemA_of_envWfA_iotag

end Rcic.Declarative.Ann
