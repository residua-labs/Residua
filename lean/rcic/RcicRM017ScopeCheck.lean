import rcic.RcicTypedMachineAccept
import rcic.RcicTypedScopeCheckPins

/-!
# RM-017 at `ScopeCheck` — the convAt row gated by the scope test

The typed half of RM-017 (`RM017T_conversion_confirmed`, sealed,
byte-untouched) asks `hP : hW.InScope`. W-2's bridge
`EnvWfT.inScope_of_scopeCheck` (`RcicTypedScopeCheck`) builds the scope's
views from a group's members when the group passes `groupCheckB` with no
`.drecD` field — so the row restates additively with
`hSC : hW.ScopeCheck` as the only premise
(`RM017T_conversion_confirmed_scopeCheck`, the DT-006/007/009
restatement convention). No `InScope` view is written by hand on this
path: `natEnvUWfT_scopeCheck` is the derived test at the real `natEnvU`
fixture, consumed by the pin at `pinConvAtState`'s `rfl` acceptance.

Teeth: the gate is not a vacuous `True` and not a weaker Bool.
`groupCheckBMut` drops the `profileCheckB` conjunct; at the
`loopAny_refused_by_profile` fixture (Loop eliminating into any sort —
read, typed, built, refused by the profile alone) the mutant ACCEPTS
where the real test refuses (`loopAny_accepted_by_mutant`). A gate on
the mutant would `InScope`-admit an environment whose views cannot be
built — the class the premise exists to bar. (The mutant lives in
`Rcic.Machine` here so this branch and the RM-014 leg can land in either
order without colliding on `Rcic.Declarative.groupCheckBMut`.)

Census note (recorded, not exploited): the premise scanner's vocabulary
names `InScope`, `CorrCertsBelow`, `supplies`, `hT`, `TypedRowsWf` — not
`ScopeCheck`. This theorem is gated by the test; how the census records
a `ScopeCheck` premise is a schema question for the data PR that
repoints the row's lean anchor. `closure_claim = 0`.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-- RM-017's conversion-confirmed row at `EnvWfT` + `ScopeCheck`: the
    sealed theorem composed with `EnvWfT.inScope_of_scopeCheck`.
    Statement identical to the sealed half modulo the premise's name. -/
theorem RM017T_conversion_confirmed_scopeCheck {E : ResolvedEnv}
    (hW : EnvWfT E) (hSC : hW.ScopeCheck) {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A l r T : Expr Nat) (htask : s.task = .convAt A l r)
    (htyl : HasTyT E n Γ l T) (htyr : HasTyT E n Γ r T)
    (hacc : kernelStepRaw s = .result (.accepted .conversionConfirmed)) :
    Nonempty (ConvT E n Γ l r T) :=
  RM017T_conversion_confirmed hW (hW.inScope_of_scopeCheck hSC) hΓ s hamb
    A l r T htask htyl htyr hacc

/-- PIN: the wrapper consumed at the real `pinConvAtState` acceptance on
    `natEnvU` (the β pair), the scope supplied by the derived test — no
    hand-written `InScope` view. -/
theorem pin_RM017T_conv_scopeCheck :
    Nonempty (ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM017T_conversion_confirmed_scopeCheck natEnvUWfT natEnvUWfT_scopeCheck
    CtxWfT.nil pinConvAtState rfl _ _ _ _ rfl
    (pinBetaApp natEnvU 1) pinBetaReductTy pin_convAt_acceptance

/-- MUTANT (the weak check): the group scope test with the
    `profileCheckB` conjunct dropped. -/
def groupCheckBMut (C : CheckerT) (E : ResolvedEnv) (f : Nat)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember)) (rr : Nat)
    (rm : CheckedMember) (sk : GroupSkelT) : Bool :=
  famCheckB C E fm sk && ctorsCheckB C E f fm sk ctors sk.ctors &&
  decide (ctors.map Prod.fst = List.range' (f + 1) ctors.length) &&
  recCheckB C E f fm ctors rr rm sk

/-- TOOTH: the mutant wrongly ACCEPTS the group the real test refuses —
    `Rcic.Declarative.loopAny_refused_by_profile`'s fixture, where only
    the profile conjunct fails. Both halves decided by evaluation. -/
theorem loopAny_accepted_by_mutant :
    (groupSkel? synChecker emptyEnv 8 0 loopFamMember [(1, loopMkMember)]
        loopRecAnyMember 0).map
      (groupCheckBMut synChecker emptyEnv 0 loopFamMember
        [(1, loopMkMember)] 2 loopRecAnyMember) = some true ∧
    (groupSkel? synChecker emptyEnv 8 0 loopFamMember [(1, loopMkMember)]
        loopRecAnyMember 0).map
      (groupCheckB synChecker emptyEnv 0 loopFamMember
        [(1, loopMkMember)] 2 loopRecAnyMember) = some false := ⟨rfl, rfl⟩

end Rcic.Machine

#print axioms Rcic.Machine.RM017T_conversion_confirmed_scopeCheck
#print axioms Rcic.Machine.pin_RM017T_conv_scopeCheck
#print axioms Rcic.Machine.groupCheckBMut
#print axioms Rcic.Machine.loopAny_accepted_by_mutant
