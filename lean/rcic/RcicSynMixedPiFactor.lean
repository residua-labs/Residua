import rcic.RcicSynLetBridge

/-!
# BelowC mixed interpreter, part 2 — §6 the (Π) factorization

`research/rcic/sortrow/BELOWC_MIXED_INTERPRETER.md` §6 (docs PR #7477). At the terminal Π of
a Π acquisition, with `b = bit (μ u)`,

    (Π)  e[V] = pi (e[hA; μ, δ; Ω]) (piSlot b (e[hB; μ, binderDisp b :: δ; binderActs (binderDisp b) Ω]))

is `eps_pi_bit` (the original Π clause in one shape) with the pending outer actions pushed
through the Π by `applyActs_pi` and through the pad by `applyActs_shift_piSlot`
(`applyActs_eps_pi`). A λ's regularity is its prescribed Π, so the λ-regularity Π of the
acquisition table is the same equation (`eps_lam_reg`, `applyActs_eps_lam_reg`).

The side identity **(I)** `e[instEnd(hB, ha, hA)] = inst 0 a (piSlot b q)` and the uniform
app-EUT finish (Π-injectivity, argument MCL, the two own instEnd alignments) are
`instEnd_eps_piSlot` and `mixedEUT_app_uniform_finish` of `RcicSynMixedFinish2` (grokF, PR
#7457); they are reused from there once landed, never restated here. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- §6 (Π) under pending outer actions: the actions pass through the Π and, shifted, through
    the pad; under a proof domain the pad is `piSlot true` and the shifted actions become the
    binder's own actions (`applyActs_shift_piSlot`). -/
theorem applyActs_eps_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {B : Expr Nat} {v : Level} (acts : List EAct) (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) (σ : Level → Level) (ρ : List Disp) :
    applyActs acts ((TyP.pi E n Γ A u B v hA hB).eps σ ρ) =
      .pi (applyActs acts (hA.eps σ ρ))
        (piSlot (levelIsZero (σ u))
          (applyActs (binderActs (binderDisp (levelIsZero (σ u))) acts)
            (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))) := by
  rw [eps_pi_bit, applyActs_pi, applyActs_shift_piSlot]

/-- §6 Π acquisition at a λ: the regularity of a λ node is its prescribed Π (definitional),
    erased by (Π). -/
theorem eps_lam_reg {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {body B : Expr Nat} {v : Level} (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B) (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.lam E n Γ A u body B v hA hbody hB).reg.2.eps σ ρ =
      .pi (hA.eps σ ρ)
        (piSlot (levelIsZero (σ u)) (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
  show (TyP.pi E n Γ A u B v hA hB).eps σ ρ = _
  exact eps_pi_bit hA hB σ ρ

/-- The λ-regularity Π under pending outer actions. -/
theorem applyActs_eps_lam_reg {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {body B : Expr Nat} {v : Level} (acts : List EAct) (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B) (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    applyActs acts ((TyP.lam E n Γ A u body B v hA hbody hB).reg.2.eps σ ρ) =
      .pi (applyActs acts (hA.eps σ ρ))
        (piSlot (levelIsZero (σ u))
          (applyActs (binderActs (binderDisp (levelIsZero (σ u))) acts)
            (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))) := by
  show applyActs acts ((TyP.pi E n Γ A u B v hA hB).eps σ ρ) = _
  exact applyActs_eps_pi acts hA hB σ ρ

end Rcic.Syn

#print axioms Rcic.Syn.applyActs_eps_pi
#print axioms Rcic.Syn.eps_lam_reg
#print axioms Rcic.Syn.applyActs_eps_lam_reg
