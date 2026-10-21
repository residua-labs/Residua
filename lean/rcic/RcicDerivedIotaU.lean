import rcic.RcicDeclarative

/-!
# R-NoFunRec S2 — `DerivedIotaU`: the union derived-ι relation (option (b))

cc ruling on #6391 (after the S2 additivity check): the frec route must NOT
add a constructor to the sealed `DerivedIota` — five sealed entries
(`devel_iota`, `devel_iota_sort`, `tyHRedA_erase`, `tmChainA_erase`,
`step_to_parRed`) would turn false under a `.ofS` arm. Instead, a NEW
relation alongside it, the way `DerivedIotaT` / `IotaErasesTA` landed
alongside the legacy face (`RcicAnnIotaCorr.lean`): `DerivedIotaU E lhs rhs`
holds when the landing is either `DerivedIota E lhs rhs` (the legacy
`IotaWitness` reading, arm `.ofU`) or an `IotaWitnessS` landing (the typed
root's shape-based reading, arm `.ofUS`, the same endpoints `DerivedIotaT.of`
lands at).

No sealed statement is edited and none is added here (sealing is S7). The
frec theorems (`wIota_derived`, the bridge's `.frec` erasure) are stated over
`DerivedIotaU` and `DerivedIotaT` in S3. The untyped `ParRed`/machine side
not computing frec ι stays the named remainder of
`[rcic_cres_wall_no_fun_rec]` — the RM-side completeness option (a), never
claimed.

`closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-- R-NoFunRec S2 (option (b)): the UNION ι relation — a landing is either
    the legacy untyped-side `DerivedIota` (arm `.ofU`, the `IotaWitness`
    reading) or a typed-root `IotaWitnessS` landing (arm `.ofUS`, the
    `DerivedIotaT` reading). -/
inductive DerivedIotaU (E : ResolvedEnv) : Expr Nat → Expr Nat → Type
  | ofU (w : IotaWitness E) : DerivedIotaU E (iotaLhsOf w) (iotaRhsOf w)
  | ofUS (w : IotaWitnessS E) : DerivedIotaU E (iotaLhsOfS w) (iotaRhsOfS w)

/-! ## intro -/

/-- intro at the legacy relation: every `DerivedIota` landing is a
    `DerivedIotaU` landing. -/
def derivedIotaU_ofDerivedIota {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (d : DerivedIota E lhs rhs) : DerivedIotaU E lhs rhs :=
  match d with
  | .of w => .ofU w

/-- intro at the typed root: every `DerivedIotaT` landing (an `IotaWitnessS`
    by `DerivedIotaT.of`) is a `DerivedIotaU` landing. -/
def derivedIotaU_ofDerivedIotaT {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (t : DerivedIotaT E lhs rhs) : DerivedIotaU E lhs rhs :=
  match t with
  | .of w => .ofUS w

/-- intro at the raw typed witness: an `IotaWitnessS` lands in `DerivedIotaU`
    at its own endpoints — the arm S3's `wIota_derived` states the wall over. -/
def derivedIotaU_ofIotaWitnessS {E : ResolvedEnv} (w : IotaWitnessS E) :
    DerivedIotaU E (iotaLhsOfS w) (iotaRhsOfS w) :=
  .ofUS w

/-! ## elim -/

/-- elim: every `DerivedIotaU` landing is one of the two relations at the same
    endpoints — the case split S3's consumers take. -/
def derivedIotaU_elim {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (u : DerivedIotaU E lhs rhs) :
    DerivedIota E lhs rhs ⊕ DerivedIotaT E lhs rhs :=
  match u with
  | .ofU w => .inl (.of w)
  | .ofUS w => .inr (.of w)

end Rcic.Declarative
