import rcic.RcicMachineSoundTyped
import rcic.RcicTypedScopeCheckPins

/-!
# RM-014 at `ScopeCheck` — the whnf row gated by the scope test

The typed half of RM-014 (`RM014T_whnf_typed`, sealed, byte-untouched)
asks `hP : hW.InScope`. W-2's bridge `EnvWfT.inScope_of_scopeCheck`
(`RcicTypedScopeCheck`) builds the scope's views from a group's members
when the group passes `groupCheckB` with no `.drecD` field — so the row
restates additively with `hSC : hW.ScopeCheck` as the only premise
(`RM014T_whnf_typed_scopeCheck`, the DT-006/007/009 restatement
convention). No `InScope` view is written by hand on this path:
`natEnvUWfT_scopeCheck` is the derived test at the real `natEnvU`
fixture, consumed by the pin at `pinWhnfState`'s `rfl` acceptance.

Teeth: the gate is not a vacuous `True` and not a weaker Bool.
`groupCheckBMut` drops the `profileCheckB` conjunct; at the
`loopAny_refused_by_profile` fixture (Loop eliminating into any sort —
read, typed, built, refused by the profile alone) the mutant ACCEPTS
where the real test refuses (`loopAny_accepted_by_mutant`). A gate on
the mutant would `InScope`-admit an environment whose views cannot be
built — the class the premise exists to bar.

Census note (recorded, not exploited): the premise scanner's vocabulary
names `InScope`, `CorrCertsBelow`, `supplies`, `hT`, `TypedRowsWf` — not
`ScopeCheck`. This theorem is gated by the test; how the census records
a `ScopeCheck` premise is a schema question for the data PR that
repoints the row's lean anchor. `closure_claim = 0`.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-- RM-014's typed row at `EnvWfT` + `ScopeCheck`: the sealed theorem
    composed with `EnvWfT.inScope_of_scopeCheck`. Statement identical to
    the sealed half modulo the premise's name. -/
theorem RM014T_whnf_typed_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E)
    (hSC : hW.ScopeCheck) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A e w : Expr Nat) (htask : s.task = .whnfAt A e)
    (hty : HasTyT E n Γ e A)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    Nonempty (HasTyT E n Γ w A) :=
  RM014T_whnf_typed hW (hW.inScope_of_scopeCheck hSC) hΓ s hamb
    A e w htask hty hacc

/-- PIN: the wrapper consumed at the real `pinWhnfState` acceptance on
    `natEnvU`, the scope supplied by the derived test — no hand-written
    `InScope` view. -/
theorem pin_RM014T_whnf_scopeCheck :
    Nonempty (HasTyT natEnvU 1 [] (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM014T_whnf_typed_scopeCheck natEnvUWfT natEnvUWfT_scopeCheck CtxWfT.nil
    pinWhnfState rfl (.sort (.succ .zero)) pinBetaRedex pinBetaReduct rfl
    (pinBetaApp natEnvU 1) pin_RM014T_acceptance

end Rcic.Machine

namespace Rcic.Declarative

/-- MUTANT (the weak check): the group scope test with the
    `profileCheckB` conjunct dropped. -/
def groupCheckBMut (C : CheckerT) (E : ResolvedEnv) (f : Nat)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember)) (rr : Nat)
    (rm : CheckedMember) (sk : GroupSkelT) : Bool :=
  famCheckB C E fm sk && ctorsCheckB C E f fm sk ctors sk.ctors &&
  decide (ctors.map Prod.fst = List.range' (f + 1) ctors.length) &&
  recCheckB C E f fm ctors rr rm sk

/-- TOOTH: the mutant wrongly ACCEPTS the group the real test refuses —
    `loopAny_refused_by_profile`'s fixture, where only the profile
    conjunct fails. Both halves decided by evaluation. -/
theorem loopAny_accepted_by_mutant :
    (groupSkel? synChecker emptyEnv 8 0 loopFamMember [(1, loopMkMember)]
        loopRecAnyMember 0).map
      (groupCheckBMut synChecker emptyEnv 0 loopFamMember
        [(1, loopMkMember)] 2 loopRecAnyMember) = some true ∧
    (groupSkel? synChecker emptyEnv 8 0 loopFamMember [(1, loopMkMember)]
        loopRecAnyMember 0).map
      (groupCheckB synChecker emptyEnv 0 loopFamMember
        [(1, loopMkMember)] 2 loopRecAnyMember) = some false := ⟨rfl, rfl⟩

end Rcic.Declarative

#print axioms Rcic.Machine.RM014T_whnf_typed_scopeCheck
#print axioms Rcic.Machine.pin_RM014T_whnf_scopeCheck
#print axioms Rcic.Declarative.groupCheckBMut
#print axioms Rcic.Declarative.loopAny_accepted_by_mutant
