import rcic.RcicAnnLRFund

/-!
# M2-f (1) — the ι interface is satisfiable by an oracle that computes

`IotaSubstA` as an `Option` equality was unsatisfiable by any standard ι
(substitution creates ι-redexes); this module pins, on a four-binder recursor
`9` (`pinRecEnvA`, `RcicAnnStep`) and a toy oracle `pinIotaFnA` that fires on
its spine exactly when the major is the constructor `zero` (`litZeroA`):

* the corrected laws hold — `IotaSubstA` (success preservation),
  `IotaRecHeadA` (recursor head, exact telescope arity), `IotaConstHeadA`
  (`IotaLiftA` / `IotaLevelsA` hold too but are not pinned: their proofs invert
  the shape under `liftA` / `instantiateLevelsA`, not the point here);
* the OLD law fails on it: a variable major is no redex, the same spine with
  `zero` substituted is one (`pinIota_not_optionEq`);
* the step function takes the oracle's step at the position (`I.rel`), reduces
  a let-bound major by ζ-local through the major arm (R-MajorStep), and then
  fires ι: `whnfA` of `rec P mz ms x` under `x := zero` is `mz`.

All by `decide` / `rfl` on closed terms; the two interface laws by cases on the
oracle's match. Axioms: none beyond `[propext, Quot.sound]`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- a toy ι on `pinRecEnvA`: the four-argument spine of recursor `9` whose major
    is the constructor `zero` (`litZeroA = const 1 []`) steps to its first minor. -/
def pinIotaFnA : IotaFnA
  | .app (.app (.app (.app (.const 9 []) _P) mz) _ms) (.const 1 []) => some mz
  | _ => none

def pinIotaA : IotaIfaceA := ⟨pinIotaFnA⟩

/-- the spine `rec P mz ms x` with `P mz ms := Sort 0`. -/
def pinRecSpineA (x : ExprA) : ExprA :=
  .app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) x

/-! ## the corrected laws hold -/

/-- the oracle fires exactly on its shape. -/
theorem pinIotaFnA_some {e e' : ExprA} (h : pinIotaFnA e = some e') :
    ∃ P mz ms, e = .app (.app (.app (.app (.const 9 []) P) mz) ms) (.const 1 []) ∧ e' = mz := by
  unfold pinIotaFnA at h
  split at h
  · rename_i P mz ms
    injection h with h
    exact ⟨P, mz, ms, rfl, h.symm⟩
  · exact Option.noConfusion h

/-- SUCCESS PRESERVATION: the shape survives substitution, with the substituted minor. -/
theorem pinIota_subst : IotaSubstA pinIotaA := by
  intro σ e e' h
  obtain ⟨P, mz, ms, rfl, rfl⟩ := pinIotaFnA_some h
  rfl

/-- RECURSOR HEAD AT EXACT ARITY: the shape is the four-argument spine of `9`. -/
theorem pinIota_recHead : IotaRecHeadA pinRecEnvA pinIotaA := by
  intro e e' h
  obtain ⟨P, mz, ms, rfl, rfl⟩ := pinIotaFnA_some h
  exact ⟨9, [], pinRecMemberA, rfl, rfl, rfl, rfl⟩

theorem pinIota_constHead : IotaConstHeadA pinIotaA := by
  intro e hne
  cases h : pinIotaFnA e with
  | none => exact h
  | some e' =>
      exfalso
      obtain ⟨P, mz, ms, rfl, _⟩ := pinIotaFnA_some h
      exact hne 9 [] rfl

/-! ## the old law fails: substitution creates the redex -/

/-- the `Option` equality of M2-e (4) on this oracle: refuted by a variable major
    under the substitution sending every variable to `zero`. -/
theorem pinIota_not_optionEq :
    ¬ (∀ (σ : SubstA) (e : ExprA), (∃ r ls, (appsSpineA e).1 = .const r ls) →
        pinIotaFnA (substA σ e) = (pinIotaFnA e).map (substA σ)) := by
  intro H
  have h := H (fun _ => .const 1 []) (pinRecSpineA (.bvar 0)) ⟨9, [], rfl⟩
  have hne : pinIotaFnA (substA (fun _ => .const 1 []) (pinRecSpineA (.bvar 0))) ≠
      (pinIotaFnA (pinRecSpineA (.bvar 0))).map (substA (fun _ => .const 1 [])) := by decide
  exact hne h

/-! ## the step function takes the oracle's step, and reduces the major first -/

/-- a constructor major: ι fires at the position (`I.rel`). -/
example : pinIotaA.rel pinRecEnvA [] (pinRecSpineA litZeroA) (.sort .zero) := ⟨rfl, by decide⟩
/-- a variable major with no value: normal. -/
example : hStepFnA pinRecEnvA pinIotaFnA [.assumption (.sort .zero)] (pinRecSpineA (.bvar 0)) = none := by
  decide
/-- a LET-BOUND major: the major arm reduces it by ζ-local (R-MajorStep) … -/
example : hStepFnA pinRecEnvA pinIotaFnA [.letBinding (.sort .zero) litZeroA] (pinRecSpineA (.bvar 0)) =
    some (pinRecSpineA litZeroA) := by decide
/-- … and then ι fires: two steps to the minor. -/
example : whnfA pinRecEnvA pinIotaFnA [.letBinding (.sort .zero) litZeroA] 2 (pinRecSpineA (.bvar 0)) =
    some (.sort .zero) := by decide
/-- a β-redex major (C4 P1's pair): the major arm, then ι. -/
example : whnfA pinRecEnvA pinIotaFnA [] 2
    (pinRecSpineA (.app (.lam (.sort .zero) (.succ .zero) (.bvar 0)) litZeroA)) = some (.sort .zero) := by
  decide

#print axioms pinIota_subst
#print axioms pinIota_recHead
#print axioms pinIota_constHead
#print axioms pinIota_not_optionEq

end Rcic.Declarative.Ann
