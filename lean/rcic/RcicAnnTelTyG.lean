import rcic.RcicAnnTelTy
import rcic.RcicAnnLREnvG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnFamSemG
import rcic.RcicAnnCtorSemG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnRecTelG
import rcic.RcicAnnFrecDomSynG
import rcic.RcicAnnIotaWfG
import rcic.RcicAnnLRRowsG
/-!
# R-NoFunRec-1 step 1 (1c-ε2d): the typed-telescope toolkit

Typed telescopes (`TelTyA`), the λ- and Π-telescope builders' typing and conversion, the λ-wrapped
recursor call's typing and conversion (`hasTyA_recCallFunA`, `convA_recCallFunA`), one typed β-step
(`stepAtA_beta`), telescopes under typed substitutions (`TelTyA.subst`) and the plain-field walks'
conversions, below the minor walk that reads them (moved verbatim from `RcicAnnRecSem`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Tel
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- W-1 (c): A VALID PAIR OF VALUES FOR A MINOR PREMISE'S PLAIN FIELDS is related along the minor's
    telescope. -/
theorem argsRelKA_minorFieldsAg {ρ₀ : Nat → Nat} {k : Nat} (f c : Nat) (ls : List Level) (wF wM : Level)
    (res : List ExprA) {Δ : LCtxA} :
    (ds : List (ExprA × Level)) → (Θ : LCtxA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) →
    (σ σ' : SubstA) → (as as' : List ExprA) → as.length = ds.length → as'.length = ds.length →
    ValidSubstAg E I n ρ₀ k Δ (consListA as σ) (consListA as' σ') (telCtxA ds ++ Θ) →
    ArgsRelKAg E I n ρ₀ k Δ (minorFieldsA f c ls wF wM pl mot fl σ (ds.map plainA) res).1 as as'
  | [], _, _, _, _, _, _, [], [], _, _, _ => .nil _
  | (D, u) :: ds, Θ, pl, mot, fl, σ, σ', a :: as, a' :: as', hl, hl', h => by
      have hl₀ : as.length = ds.length := Nat.succ.inj hl
      have hl₀' : as'.length = ds.length := Nat.succ.inj hl'
      have hc := (h.1 ds.length _ (lookupTypeA_telCtxA_head D u ds Θ)).2
      rw [← hl₀, substA_consListA_cons_liftA] at hc
      have e1 : consListA (a :: as) σ as.length = a := consListA_cons_head a as σ
      have e2 : consListA (a' :: as') σ' as.length = a' := by
        rw [show as.length = as'.length by rw [hl₀, hl₀']]; exact consListA_cons_head a' as' σ'
      rw [e1, e2] at hc
      simp only [List.map, plainA, minorFieldsA]
      refine .cons _ _ _ _ a a' as as' hc ?_
      rw [instantiate0A_minorFieldsA_plain]
      have h' : ValidSubstAg E I n ρ₀ k Δ (consListA as (SubstA.cons a σ)) (consListA as' (SubstA.cons a' σ'))
          (telCtxA ds ++ (.assumption D :: Θ)) := (telCtxA_cons_append (D, u) ds Θ) ▸ h
      exact argsRelKA_minorFieldsAg f c ls wF wM res ds _ pl mot (fl ++ [a]) _ _ as as' hl₀ hl₀' h'

/- (`telCtxA_length` landed upstream in `RcicAnnGroup` — same statement.) -/

end Tel

end Rcic.Declarative.Ann
