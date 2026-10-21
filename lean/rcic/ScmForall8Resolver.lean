import rcic.ScmRowDerive

/-!
SCM-003: specialize landed bundle leastness to the resolver pullback of
the candidate local rows. The external compatibility supplier is constructed;
the genuine candidate-prefixpoint premise remains. `closure_claim = 0`.
-/

namespace Rcic.Scm.RowDerive

/-- Bundle leastness for local rows whose external rows are exactly their
resolver pullback. No independent local/external compatibility premise is
needed: a resolved local fact supplies its own pullback witness. -/
theorem deriveCl_least_resolved
    (gs : List RowGrp) (resolve : ExtResolve)
    {ρ : Nat → Nat → RaisedRef → Prop}
    (hpre : RowPrefixCl gs resolve ρ
      (fun n r => ∃ g m, resolve n = some (g, m) ∧ ρ g m r))
    (g i : Nat) (r : String)
    (h : r ∈ ((deriveRowsCl gs resolve).getD g []).getD i []) :
    ρ g i r :=
  deriveCl_least gs resolve hpre
    (fun _ g' m' _ hres hr => ⟨g', m', hres, hr⟩) g i r h

end Rcic.Scm.RowDerive
