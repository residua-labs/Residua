import rcic.RcicTypedGroupPinsVec

/-! # EG-017 supporting pin — an externally fabricated env carries no `EnvWfT`

F-04 class S row (structural): the annex makes no positive "unconstructible"
claim, so the honest Lean face is a refutation pin — an environment assembled
outside the admission discipline cannot be well-formed.

`fabricatedAx99Env` is a single `axiomM` member whose stored type names
`.const 99` — a reference its own env cannot resolve.  Any `EnvWfT` on it
would, by `envWfT_constsIn` (member-scope inversion), place `.const 99`
inside the env; `members 99` computes to `none`, contradiction.  Same shape
as `not_envWfT_vecOnlyEnvU` (RcicTypedGroupPinsVec.lean:1229). -/

namespace Rcic.Declarative

/-- one-member fabricated environment: an `axiomM` at `0` storing
    `.const 99` — resolvable nowhere in its own env. -/
def fabricatedAx99Env : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.axiomM, 0, .const 99 [], none⟩

/-- EG-017: the fabricated env is unconstructible as a `EnvWfT` — its only
    member's stored type names a constant absent from the env itself. -/
theorem not_envWfT_fabricatedAx99Env (hW : EnvWfT fabricatedAx99Env) : False := by
  have hc := envWfT_constsIn hW 0 ⟨.axiomM, 0, .const 99 [], none⟩ rfl
  obtain ⟨m, hm⟩ := hc
  cases hm

end Rcic.Declarative

#print axioms Rcic.Declarative.not_envWfT_fabricatedAx99Env
