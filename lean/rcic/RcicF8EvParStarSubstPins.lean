import rcic.RcicF8EvParStar

/-!
# PINS — the lazy substitution nodes on real stars (W-X-SUBST S0 §5, #7107)

The landed one-step star `pinStar` (`irr` producer, then `refl`) is weakened under `x : Sort 1`
and then substituted at `j = 0` by `Sort 0`: the node sits OVER a lazy `wk` — the case a
push-through design cannot materialize — and `.val` lands at the original endpoints because the
stack `ins; sub` computes to the identity on closed terms. Leaf laws by `rfl`/`simp`; the valley
twin on `pinValley`. `closure_claim` 0.
-/

namespace Rcic.Declarative.F8Measure
namespace SubstPins

open Rcic.Declarative.PEqTProofFront Rcic.Declarative.PEqLeafTPropPins IrrPins

private def pinCl : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h
private def pinSS : EnvMembersSubstStable emptyEnv := fun _ _ h => Option.noConfusion h

/-- `Sort 0 : Sort 1` at `[]` — the substituted value's typing. -/
def s01 : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := .sort _ _

/-- the root bundle: the irr root and the value's typing. -/
def R₂ : List (Jd emptyEnv 0) := [IrrPins.root, .ty s01]

def incl : ∀ r ∈ [IrrPins.root], r ∈ R₂ := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact .head _

/-- `x : Sort 1`. -/
def d₁ : LocalDecl := .assumption (.sort (.succ .zero))

/-- the one-step star weakened under `x : Sort 1`. -/
def pinWk : EvParStar R₂ [d₁] (lift 0 1 p) (lift 0 1 q) (lift 0 1 P) :=
  .wk d₁ 0 (pinStar.widen incl)

/-- the value's provenance typing, a literal certified into `R₂`. -/
def hvPin : EvTy R₂ [] (.sort .zero) (.sort (.succ .zero)) :=
  .lit s01 ⟨_, .tail _ (.head _), .inl rfl⟩

/-- PIN — `subst0` over a lazy `wk`: `x := Sort 0` at `j = 0`. -/
def pinSubst0 : EvParStar R₂ []
    (instantiate 0 (lift 0 0 (.sort .zero)) (lift 0 1 p))
    (instantiate 0 (lift 0 0 (.sort .zero)) (lift 0 1 q))
    (instantiate 0 (lift 0 0 (.sort .zero)) (lift 0 1 P)) :=
  .subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 0 pinWk rfl hvPin

/-- the leaf law: the star's leaves (unchanged by `wk`/`widen`), then the value's ONCE. -/
theorem pinSubst0_leaves :
    pinSubst0.leaves = pinStar.leaves ++ [Jd.ty s01] := by
  simp only [pinSubst0, pinWk, EvParStar.leaves, EvParStar.leaves_widen, EvPar.leaves_widen, hvPin,
    EvTy.leaves]

theorem pinSubst0_leaves_explicit :
    pinSubst0.leaves = [Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty []), Jd.ty (q_ty []),
      Jd.ty s01] := rfl

/-- its materialization lands at the ORIGINAL endpoints: the composite action
    (insert at 0, substitute 0) is the identity on the closed `p`, `q`, `P`. -/
def pinSubst0_val : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 [] p q P :=
  pinSubst0.val pinCl pinSS

/-- the stack the node materializes through: insert `x : Sort 1` at 0, then substitute it. -/
def pinMorph : CtxMorph emptyEnv 0 [] [] :=
  .ins (Γ := []) d₁ 0 (.sub (Γ := [d₁]) (t := .sort (.succ .zero)) (v := .sort .zero) 0 rfl s01 .nil)

/-- the materialization is the producer's stacked output followed by `refl` — the exact shape
    `EvParStar.valS` writes (no `PEqT.instantiate_pair`, no `parRedT_substSame`). -/
theorem pinSubst0_val_shape :
    pinSubst0.val pinCl pinSS =
      .tail ((IrrPins.producer.widen incl).valS pinCl pinSS pinMorph)
        (.refl _ _ _ (pinMorph.hasTyT pinCl pinSS (q_ty []))) := rfl

/-- PIN — the valley twin: `pinValley` weakened, then substituted. -/
def pinValleySubst0 : Valley R₂ []
    (instantiate 0 (lift 0 0 (.sort .zero)) (lift 0 1 p))
    (instantiate 0 (lift 0 0 (.sort .zero)) (lift 0 1 q))
    (instantiate 0 (lift 0 0 (.sort .zero)) (lift 0 1 P)) :=
  ((pinValley.widen incl).wk d₁ 0).subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 0 rfl hvPin

theorem pinValleySubst0_leaves :
    ∀ ℓ ∈ pinValleySubst0.leaves, ℓ ∈ pinValley.leaves ++ [Jd.ty s01] := by
  intro ℓ hℓ
  have h := Valley.subst0_leaves (t := .sort (.succ .zero)) (v := .sort .zero) 0
    ((pinValley.widen incl).wk d₁ 0) rfl hvPin ℓ hℓ
  simpa only [Valley.wk_leaves, Valley.leaves_widen, hvPin, EvTy.leaves] using h

end SubstPins
end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.SubstPins.pinSubst0
#print axioms Rcic.Declarative.F8Measure.SubstPins.pinSubst0_leaves
#print axioms Rcic.Declarative.F8Measure.SubstPins.pinSubst0_val
#print axioms Rcic.Declarative.F8Measure.SubstPins.pinSubst0_val_shape
#print axioms Rcic.Declarative.F8Measure.SubstPins.pinValleySubst0
#print axioms Rcic.Declarative.F8Measure.SubstPins.pinValleySubst0_leaves
