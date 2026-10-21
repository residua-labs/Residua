import rcic.RcicAnnEnvBridgeGroup

/-!
# R-NoDeltaRec-4d-vii — the group scope WITHOUT the `.drecD` gate

`GroupInScopeT` (`RcicAnnEnvBridgeGroup`) is the copy's group scope on the typed side: the
family view, the constructors, the recursor, the profile, the parameter-level bound — and
`hsnd`, the named gate keeping `.drecD`-carrying constructors out, because the
erased↔annotated ι-correspondence needed `EnvNormEraseA`, which a `.drecD` member provably
breaks (`drCtorMemberA_diverge`).

The D-route (`RcicAnnIotaCorrN`/`RcicTypedJD`/`RcicAnnRowsSupplyD`) re-keys that
correspondence on the NORMALIZED constructor type (`normA.getD mtypeA`), where the
correspondence is unconditional — so the scope the D-route consumes carries no `hsnd`.
This module names that variant:

* `GroupInScopeTD`: `GroupInScopeT`'s fields minus `hsnd`. A `GroupInScopeT` is a
  `GroupInScopeTD` (`groupInScopeTD_of_groupInScopeT`); the converse needs `hsnd` back —
  it is NOT claimed.
* `EnvWfT.InScopeD`: `InScope`'s twin reading `GroupInScopeTD`. `drEnvWfT`'s group — whose
  `mk` view carries `.drecD` — is inside it where it is outside `InScope`
  (`dr_skel_bridge_refused` records the `hsnd` refusal).
-/

namespace Rcic.Declarative

/-- `GroupInScopeT` without `hsnd`: the group's typed evidence (views, recursor, profile,
    parameter bound), `.drecD` fields admitted. The fields are `GroupInScopeT`'s verbatim
    up to the missing gate; `hctors`/`hlayout`/`hrr`/`hrm`/`hprof`/`hpb` unchanged. -/
structure GroupInScopeTD (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) : Type where
  fv : FamViewT fm
  htel : TelTyT E fm.arity [] (fv.params ++ fv.indices)
  cs : List (GroupCtorT E f fm fv)
  hctors : (cs.map GroupCtorT.entry).reverse = ctors
  hlayout : cs.reverse.map GroupCtorT.ref = List.range' (f + 1) cs.length
  grec : GroupRecT E f fm fv cs
  hrr : rr = f + 1 + cs.length
  hrm : grec.member = rm
  hprof : GroupProfileT grec
  /-- the family's telescope binder levels are within its arity — `GroupInScopeT.hpb`,
      unchanged. -/
  hpb : ∀ d ∈ fv.params ++ fv.indices, levelBounded fm.arity d.2 = true

/-- a `GroupInScopeT` is a `GroupInScopeTD` — the gate was the only difference. -/
def groupInScopeTD_of_groupInScopeT {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    (g : GroupInScopeT E f fm ctors rr rm) : GroupInScopeTD E f fm ctors rr rm where
  fv := g.fv
  htel := g.htel
  cs := g.cs
  hctors := g.hctors
  hlayout := g.hlayout
  grec := g.grec
  hrr := g.hrr
  hrm := g.hrm
  hprof := g.hprof
  hpb := g.hpb

/-- every group of a derivation is in the D-route's scope — `EnvWfT.InScope`'s twin,
    `GroupInScopeTD` in place of `GroupInScopeT` (the `hsnd` gate dropped). -/
def EnvWfT.InScopeD : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => hE.InScopeD
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.InScopeD
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => hE.InScopeD
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.InScopeD
  | _, .group E f fm ctors rr rm _ hE _ _ _ _ =>
      hE.InScopeD ∧ Nonempty (GroupInScopeTD E f fm ctors rr rm)

/-- `InScope` is `InScopeD` — the D-scope is the wider one. -/
theorem EnvWfT.inScopeD_of_inScope : {E : ResolvedEnv} → (hW : EnvWfT E) →
    hW.InScope → hW.InScopeD
  | _, .empty => id
  | _, .axiom _ _ _ _ hE _ _ _ _ => inScopeD_of_inScope hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => inScopeD_of_inScope hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => inScopeD_of_inScope hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => inScopeD_of_inScope hE
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => fun ⟨hin, ⟨g⟩⟩ =>
      ⟨inScopeD_of_inScope hE hin, ⟨groupInScopeTD_of_groupInScopeT g⟩⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.GroupInScopeTD
#print axioms Rcic.Declarative.EnvWfT.InScopeD
#print axioms Rcic.Declarative.groupInScopeTD_of_groupInScopeT
#print axioms Rcic.Declarative.EnvWfT.inScopeD_of_inScope
