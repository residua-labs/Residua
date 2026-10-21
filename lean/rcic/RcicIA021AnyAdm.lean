import rcic.RcicRecursorCellHT
import rcic.RcicDTMetaTyped

/-!
# IA-021 at every admission record — `MinorDomainsTyped a` for ARBITRARY `a`

The census premise of IA-021 (`MinorDomainsTyped`, `RcicIARecTyped.lean:75`, consumed by
`IA021T_recursor_typed_nonempty :344`) quantifies over an arbitrary
`a : RecursorEliminationAdmitted E r m`, while `IA021T_minorDomains_of_envWfT` (#7002)
supplies it at the canonical cell's `adm` only. The audit on #7065 refused the grant for
that reason.

Measurement: no determinism of admission is needed. `MinorDomainsTyped a` reads `a` only
through `a.minorTypes`, `a.family.parameters` and `a.policy` (via `minorCtxT`), and every
`a` pins all three to the stored recursor type by its own field
`a.recursorType : m.mtype = policyRecursorType a.family a.minorTypes a.policy`.
`recursor_minorType_typed` (`RcicIATypedMinor`) already takes an arbitrary `a` and only
`hT : HasTyT E m.arity [] m.mtype (.sort u)` — the stored type sort-typed in `E`, which
`EnvWfT` supplies for a recursor member (the cell's `hT`, lifted from the derivation
prefix to `E`). So the minor domains are typed for EVERY admission record of the member,
whether or not it is the one `EnvWfT` carries. Two admitted `a`'s may differ in other
fields (views, `selected`); none of that enters `MinorDomainsTyped`.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-- the stored recursor type is sort-typed in `E` itself (the cell's typing field, lifted
    along `E0 ⊆ E`). -/
theorem recursor_storedType_sorted_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM) :
    ∃ u, Nonempty (HasTyT E m.arity [] m.mtype (.sort u)) :=
  ⟨(envWfT_cellHT hW hm hcls).u,
    ⟨hasTyTExt (envWfT_cellHT hW hm hcls).cell.env_extends (envWfT_cellHT hW hm hcls).hT⟩⟩

/-- **IA-021 at every admission record**: under `EnvWfT`, for ANY
    `a : RecursorEliminationAdmitted E r m` of a recursor member, `MinorDomainsTyped a` is
    inhabited — the exact premise shape `IA021T_recursor_typed_nonempty` consumes. -/
theorem IA021T_minorDomains_of_envWfT_any {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM)
    (a : RecursorEliminationAdmitted E r m) : Nonempty (MinorDomainsTyped a) := by
  obtain ⟨u, ⟨hT⟩⟩ := recursor_storedType_sorted_of_envWfT hW hm hcls
  have h : ∀ i : Fin a.minorTypes.length, ∃ w,
      Nonempty (HasTyT E m.arity (minorCtxT a i.val) (a.minorTypes[i.val]) (.sort w)) :=
    fun i => recursor_minorType_typed a hT i.val i.isLt
  obtain ⟨⟨ws, hws⟩⟩ := finChoiceLevel _ _ h
  exact ⟨⟨ws, hws⟩⟩

/-- the consumer's composite, with its `MinorDomainsTyped` premise discharged: at an
    `EnvWfT` recursor member, any admission record with a typed family gives the stored
    recursor type a sort. -/
theorem IA021T_recursor_typed_of_envWfT_any {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM)
    (a : RecursorEliminationAdmitted E r m) (hfamT : FamilyTypedT a.family) :
    Nonempty (Σ' u, HasTyT E m.arity [] m.mtype (.sort u)) :=
  (IA021T_minorDomains_of_envWfT_any hW hm hcls a).elim fun hmin =>
    IA021T_recursor_typed_nonempty a (envClosed_of_envWfT hW) hfamT hmin

end Rcic.Declarative

#print axioms Rcic.Declarative.IA021T_minorDomains_of_envWfT_any
#print axioms Rcic.Declarative.IA021T_recursor_typed_of_envWfT_any
