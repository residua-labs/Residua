import rcic.RcicRecursorCellHT
import rcic.RcicDTMetaTyped

/-!
# IA-021 — the `hT` premise at `EnvWfT`

`recursor_minorType_typed` (`RcicIATypedMinor`) takes `hT : HasTyT E m.arity [] m.mtype
(.sort u)`: the stored recursor type sort-typed in its admission environment. That is a field
of every `GroupMembersT.cons` node (`u`, `hT`), hence of every `EnvWfT` group, and the cell
`RecursorCellHT` carries it (`RecursorCellHT.hT`, at the derivation prefix `E0`). So `EnvWfT`
supplies `hT` the way it supplied the minor domains (`IA021T_minorDomains_of_envWfT`): the
premise is discharged, not assumed.

* `IA021T_hT_of_envWfT` — the typing at the cell prefix `E0`, read off the cell;
* `IA021T_hT_of_envWfT_ext` — the same lifted to `E` (`hasTyTExt`, `E0 ⊆ E`);
* `IA021T_minorType_typed_of_envWfT` — `recursor_minorType_typed` with `hT` supplied: every
  stored minor domain of an `EnvWfT` recursor is sort-typed in its minor context.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-- IA-021's `hT` at `EnvWfT`: the stored recursor type is sort-typed in its derivation prefix. -/
theorem IA021T_hT_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hcls : m.mclass = .recursorM) :
    ∃ u, Nonempty (HasTyT (envWfT_cellHT hW hm hcls).cell.E0 m.arity [] m.mtype (.sort u)) :=
  ⟨(envWfT_cellHT hW hm hcls).u, ⟨(envWfT_cellHT hW hm hcls).hT⟩⟩

/-- the same typing in `E` itself: the prefix is a sub-environment of `E`. -/
theorem IA021T_hT_of_envWfT_ext {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hcls : m.mclass = .recursorM) :
    ∃ u, Nonempty (HasTyT E m.arity [] m.mtype (.sort u)) :=
  ⟨(envWfT_cellHT hW hm hcls).u,
    ⟨hasTyTExt (envWfT_cellHT hW hm hcls).cell.env_extends (envWfT_cellHT hW hm hcls).hT⟩⟩

/-- `recursor_minorType_typed` with its `hT` discharged by `EnvWfT`: every stored minor domain
    of an admitted recursor is sort-typed in its minor context, at the cell. -/
theorem IA021T_minorType_typed_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM) (i : Nat)
    (hi : i < (envWfT_cellHT hW hm hcls).cell.adm.minorTypes.length) :
    ∃ w, Nonempty (HasTyT (envWfT_cellHT hW hm hcls).cell.E0 m.arity
      (minorCtxT (envWfT_cellHT hW hm hcls).cell.adm i)
      ((envWfT_cellHT hW hm hcls).cell.adm.minorTypes[i]'hi) (.sort w)) :=
  recursor_minorType_typed _ (envWfT_cellHT hW hm hcls).hT i hi

end Rcic.Declarative

#print axioms Rcic.Declarative.IA021T_hT_of_envWfT
#print axioms Rcic.Declarative.IA021T_hT_of_envWfT_ext
#print axioms Rcic.Declarative.IA021T_minorType_typed_of_envWfT
