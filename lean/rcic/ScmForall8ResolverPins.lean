import rcic.ScmForall8Resolver

/-!
SCM-003 resolver-pullback pins reuse the landed two-group fixture: group 0
calls `g1.f0`, resolved to group 1 member 0, which raises `range_violation`.
The wrong-group mutant maps resolved callees into group 0. It consequently
ACCEPTS a prefixpoint omitting the caller's propagated residue. The real
resolver refuses that prefixpoint, and the new leastness lemma proves its
pullback premise impossible. No carrier or row implementation is copied.
`closure_claim = 0`.
-/

namespace Rcic.Scm.RowDerive.Forall8ResolverPins

open Rcic.Scm Rcic.Scm.RowDerive Rcic.Scm.RowDerive.Pins

/-- The landed fixture has a genuine external-call contribution. -/
theorem caller_derived :
    rv ∈ ((deriveRowsCl clgs resG).getD 0 []).getD 0 [] := by decide

def derivedRho (g i : Nat) (r : RaisedRef) : Prop :=
  r ∈ ((deriveRowsCl clgs resG).getD g []).getD i []

/-- Non-vacuity: the derived table supplies the retained prefixpoint premise. -/
theorem derived_prefix_resolved :
    RowPrefixCl clgs resG derivedRho
      (fun n r => ∃ g m, resG n = some (g, m) ∧ derivedRho g m r) := by
  intro g gp hg i f hf r hr
  apply deriveCl_prefix clgs resG g gp hg i f hf r
  apply CoreExpr.Row_mono (fun _ _ h => h) ?_ _ r hr
  intro n r' hx
  obtain ⟨g', m', hres, hm⟩ := hx
  change r' ∈ xrOf (deriveRowsCl clgs resG) resG n
  rw [xrOf_some _ _ _ _ _ hres]
  exact hm

/-- The new theorem fires at a closed, nonempty cross-group instance. -/
theorem caller_in_resolved_prefix : derivedRho 0 0 rv :=
  deriveCl_least_resolved clgs resG derived_prefix_resolved 0 0 rv caller_derived

/-- Keep the callee's own raise, but omit its propagation into the caller. -/
def missingCaller : List Tbl := [[[]], [[rv]]]

def missingRho (g i : Nat) (r : RaisedRef) : Prop :=
  r ∈ (missingCaller.getD g []).getD i []

/-- Mutation: keep the member index but replace the resolved group by 0.
The checker itself is the landed carrier, with only this resolver corrupted. -/
def wrongGroup (resolve : ExtResolve) : ExtResolve :=
  fun n => (resolve n).map (fun gm => (0, gm.2))

def mutantCheck (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl)
    (entry : Nat × Nat) : DeriveOutCl :=
  scmRowsCl 1 gs (wrongGroup resolve) ts entry

/-- Both `ok = 1` and `pfx = 1`: the mutant really accepts the invalid claim. -/
theorem mutant_wrongly_accepts :
    mutantCheck clgs resG missingCaller (0, 0) = okCl missingCaller [] := by rfl

/-- The actual resolver finds the missing caller row at flattened cell 0. -/
theorem resolver_rejects_missing_caller :
    scmRowsCl 1 clgs resG missingCaller (0, 0) =
      okCl missingCaller [] 0 0 := by rfl

/-- A fully supplied positive carrier instance: both groups retain the raise. -/
theorem resolver_accepts_complete :
    scmRowsCl 1 clgs resG [[[rv]], [[rv]]] (0, 0) =
      okCl [[[rv]], [[rv]]] [rv] := by rfl

/-- Semantic tooth: acceptance by the mutant cannot supply the premise of
leastness under the real resolver. The new theorem exposes the lost residue. -/
theorem missing_caller_not_resolved_prefix :
    ¬ RowPrefixCl clgs resG missingRho
      (fun n r => ∃ g m, resG n = some (g, m) ∧ missingRho g m r) := by
  intro hpre
  have h := deriveCl_least_resolved clgs resG hpre 0 0 rv caller_derived
  exact List.not_mem_nil rv h

end Rcic.Scm.RowDerive.Forall8ResolverPins
