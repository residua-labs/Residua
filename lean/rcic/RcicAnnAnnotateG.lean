import rcic.RcicAnnAnnotate
import rcic.RcicAnnLREnvG
import rcic.RcicAnnTelTyG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnFamSemG
import rcic.RcicAnnCtorSemG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnRecTelG
import rcic.RcicAnnFrecDomSynG
import rcic.RcicAnnFrecWorldG
import rcic.RcicAnnFrecBetaG
import rcic.RcicAnnFrecArmG
import rcic.RcicAnnRecSemG
import rcic.RcicAnnIotaWfG
import rcic.RcicAnnLRRowsG
import rcic.RcicAnnLRStuckDatumG
/-!
# M3-c2 — annotation: the typed judgment's derivations lift to the copy

The bridge's second half. `RcicAnnErase` erases the copy's derivations into the typed judgment
on `main`'s syntax (`RcicTypedJ`); this module goes back. A derivation of `HasTyT` / `ConvT` in
the erased environment lifts, in ANY well-formed annotated context that erases to its context, to
a derivation on the copy of an annotation of its subject (and type), whenever the environment is
one the copy admits (`AnnEnvA`: well-formed at the concrete ι, the small-index profile, Prop
families eliminating into Prop only, struct groups exempt; the premises of the copy's rows).

Each rule is lifted by lifting its premises and rebuilding the copy's rule. The copy's rules
carry more premises than the typed judgment's (the codomain typings, the right-hand typings of the
congruences, both typings of a type conversion). The copy's metatheory supplies them: regularity,
the endpoints of a conversion, functionality, context conversion, level irrelevance. Two lifts of
one term may differ at the `λ` / `Π` annotations. Annotation coherence (`annCohA`, M3-c0) glues
them: two well-typed types with one erasure are convertible.

ι is the one rule whose lift needs a fact proved later. The copy's ι step reads the annotated
redex (`iotaFnA`), and its rule needs the reduct TYPED at the redex's type: ι subject reduction,
the right-hand typing `ConvA.iota` carries as a named M-001 deviation. At a struct group the rule is
`ConvA.structIota` (W-1 (e)), which carries a conversion to the struct arm's reduct as well. So the
hypothesis is ι subject reduction in its conversion form (`IotaSRA`, W-1 (e-2)): a ι step at a typed
redex is a conversion at the redex's type. Nothing else is assumed. `RcicAnnIotaSR` proves it
(`iotaSRA`) and restates the lift without it (`annHasTyT'`, `annConvT'`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the admitted environment, and ι subject reduction -/

namespace AnnEnvA
variable {E : ResolvedEnvA}

/-- **DT-025/A-6 E2 — the GUARDED semantic environment, at the height valuation `fun _ => 1`.**
    Every well-formed annotated environment satisfies `EnvSemAg`: the key agreement comes from
    main's own `C.hS` (S1-g.1, `propKeyA_holds`), the rest is the guarded copy of main's
    environment induction (families, constructors, recursors). -/
theorem hSg (C : AnnEnvA E) (n : Nat) : EnvSemAg E (iotaIfaceA E) n (fun _ => 1) :=
  C.wf.elim fun hW => envSemA_of_envWfA_recStructg hW posValA_one
    (propKeyA_holds C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one) C.small C.propElim

end AnnEnvA

/-! ## (2) every member's type, and every body, typed -/

section Members
variable {I : IotaIfaceA}

end Members

/-! ## (3) closed derivations instantiated and weakened -/

section Inst
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end Inst

section MemberInst
variable {E : ResolvedEnvA} {n : Nat}

end MemberInst

/-! ## (4) the context's lookups typed -/

section Lookup
variable {E : ResolvedEnvA} {n : Nat}

end Lookup

/-! ## (5) erasure inverted at lookups and literals -/

/-! ## (6) retyping across one erasure (annotation coherence at types) -/

section Retype
variable {E : ResolvedEnvA} {n : Nat}

end Retype

/-! ## (7) a concrete ι step is a declarative one -/

/-! ## (8) THE ANNOTATION

Every arm makes its recursive calls before it substitutes anything: a substitution rewrites the
premises' types, and the recursion is structural on the premises. -/

section Annotate
variable {E : ResolvedEnvA} {n : Nat}

end Annotate

end Rcic.Declarative.Ann

