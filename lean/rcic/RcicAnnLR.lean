import rcic.RcicAnnTyRed
import rcic.RcicAnnFamPer
import rcic.RcicAnnPropEq

/-!
# M1-d — the logical relation on the annotated copy, and the KILL CRITERION
# (amended by M1-d (iv): declarative base, typed head reduction)

`TyKA`/`EqKA` are L-RING's `TyK`/`EqK` (`research/rcic/lring-20261003/RcicLR.lean`,
on the face `RcicLR.lean:74–260`) transplanted onto `ExprA`, with the changes
the annotation buys, each named:

1. The PROP CLAUSE is keyed on `IsPropTy` of the type's weak-head normal form —
   a predicate on the SYNTAX (`RcicAnnAlg`: `inferSortA` is deterministic), where
   L-RING keyed it on a universe `u` carried by the derivation (`ht ρ₀ u = 0`)
   and C9 found that key circular with `SortConvChar`. It takes PRIORITY: an
   impredicative pi that is a proposition is related by the prop clause, and
   the `pi` clause carries `¬ IsPropTy` so that no pi is covered by two clauses
   with different relations; a stuck type may be covered by both the prop and
   the stuck clause, whose relations COINCIDE (typed and convertible at the
   normal form), so uniqueness holds by `rfl` there and the fundamental theorem
   never has to decide `IsPropTy` for a neutral type. For a pi it decides it by
   `isZero v` (`isPropTy_pi_iff`), a Boolean on the annotation.
2. The relation has NO universe index. What the fundamental theorem needs of
   a type's sort it reads from the TYPINGS the term relations carry
   (`Nonempty (HasTyA Γ a (sort l))` in the sort clause) and from the
   annotations; `EqKA.sort` carries `=ₙ` of the two levels, which is where the
   row `SortConvChar` for `ConvA` comes out. (M1-d (iv) struck the
   `SortOfWhnfA` datum: nothing read it, the fundamental theorem's `app` arm
   could not produce it without soundness of synthesis, and neutrals would
   need it on both sides.)
3. Reduction is TYPED head reduction (`WhTyA`, `RcicAnnTyRed`), L-RING C4's
   shape: every step is a `ConvA` with its rule's premises and an `hStepFnA`
   step, so chains erase to `whnfA` and normal forms are unique (`whTyA_det`)
   — the kill criterion's determinism, now through erasure. Each step sits at
   its own sort, so a step can be prepended at whatever sort it comes with
   (head expansion) without any uniqueness of sorts.
   (M1-d (i)–(iii) read the function `whnfA` directly; with a DECLARATIVE base
   the escape to the normal form needs the step's premises — see 5.)
4. (M2-f (3).) Inductive families have the `fam` clause: a Type-level family
   application `I ls xs` is valid with the LEAST FIXED POINT `LfpWA (FamPhiWA …) []`
   as its term relation (L-RING C3–C7 on the copy, `RcicAnnFam`): two terms are
   related when both reduce to the same constructor with `ArgsRelA`-related
   arguments and coherent indices, or both to stuck terms; the clause carries
   the Kripke data `Rs`/`RsF` (the field and index domains valid under every
   world), the diagonal spine datum `hxsD`, the normal form's weak-head
   normality `hn` (as `prop` carries it — the kill criterion still reads no ι
   hypothesis) and `¬ IsPropTy` (a Prop-sorted family application is the prop
   clause's, R-PropOutOfTower; no Prop disjunct in `FamPhiA`). `EqKA.fam` relates
   two family applications of the same family at `=ₙ` levels with arguments
   related along the family's telescope. `StuckA` excludes family heads
   (`isShapeHeadA E`), so the fam and stuck clauses are disjoint. (M2-f (3b).)
   Both clauses carry the family's result sort `hsh` (the Prop boundary of a
   family application is read off it, `isPropTy_famApp_iff`) and the DOMAIN
   EQUALITIES at `=ₙ` level lists and related prefixes: `hFldFeq` for the index
   domains, `hFldeq` for the constructors' plain field domains (EqKA, under
   every world), with `hFldRec` relating the two domains of a recursive position
   (`RecDomRelA`). A walk instantiates the rest of its telescope with the LEFT
   arguments, so swapping or composing walks reads a position at `D[pre']` where
   it was read at `D[pre]`; these data make the two relations one (transport),
   which is what PER, transport across related carriers, and their joint
   induction (`RcicAnnLRPer`, `eqKA_transport_per`) consume. They quantify over
   both Πs rather than producing the second (its existence is rigidity,
   `applyTelA_pi_transfer_levels`): no existential around the relation, so no
   nested occurrence and no extra recursor motive.
5. The BASE RELATIONS are DECLARATIVE: every term relation carries the two
   typings and a `ConvA` at the clause's normal form; every `EqKA` clause
   carries a `TyConvA`. (M1-d (i)–(iii) carried `AlgEq`, "so that the rows
   fall out by inversion"; M1-d (iv) measured that (a) the fundamental
   theorem's `trans` arm needs the base relation TRANSITIVE and algorithmic
   equality is transitive only after a declarative-base pass — Annex 23
   `:75977`, the two-instance route of Abel–Öhman–Vezzosi 2018 / Pujet–Tabareau
   POPL23 — and (b) the rows do not come from inverting the base at all: they
   come from the STRUCTURE of `EqKA.pi` (`hDeq`, `hC`, `=ₙ` annotations), which
   the declarative base already delivers, impredicative pis included since
   type equality has no prop clause. `AlgEq` remains the algorithm
   (`RcicAnnAlg`, `RcicAnnAlgWk`), for decidability later.)
6. Every term relation, and every `EqKA` datum, is stated AT THE NORMAL FORMS
   the clause names (`A'`, `sort l`, `pi D u C v`, `N`), not at `A`/`B`: a type
   and its weak-head normal form then get the SAME relation syntactically.
7. Pis are related with `=ₙ` ANNOTATIONS (`hu`, `hv`), not identical ones:
   `const r ls ≅ const r ls'` for `=ₙ` level lists unfolds to bodies whose
   annotations differ exactly so. The pi clauses also carry the typings of the
   domain and of the codomain under its binder (`hDty`, `hCty`): `HasTyA.app`
   needs them to type an application of a related function, and inversion of
   the pi's own typing is not available without the rows.
8. `EqKA.pi`'s codomain datum is ONE-SIDED: `RD ρ a a' → EqKA (C[a]) (C'[a])`,
   Abel–Öhman–Vezzosi's `[G≡G']` with "`a` in the domain" witnessed by any
   `RD ρ a a'`; not the two-sided `EqKA (C[a]) (C'[a'])` of M1-d (iv).
   Measured (M2-b (ii)): with the two-sided datum, transporting the term
   relation along `EqKA` (`eqKA_transport`) needs `RD ρ a a` from `RD ρ a a'`
   in the pi case, i.e. the PER properties, whose pi cases need the transport:
   a cycle. One-sided, transport is by induction on `EqKA` alone, before any
   PER property; the two-sided form is derivable afterwards from `hCeq` and
   the PER properties. [M2-f (3b): the `fam` clause brings the cycle back at
   families — moving the carrier along related indices flips and composes the
   index walks, which needs the index relations' PER — so transport and PER are
   ONE induction now (`eqKA_transport_per`); the one-sided datum still keeps the
   pi case of transport free of PER.]
9. (M1-d (vi), R-PropOutOfTower; M2-e (0) is the measurement.) The sort clause
   splits on `isZero l`: `sortT` relates the elements of a Type-level sort at the
   sort's own height `ht l` (the lower relations `LE`/`LT` there — the
   predicative discipline, and what makes the relation of a type independent of
   the height it is validated at); `sortP` relates two propositions as elements
   of a `Prop`-level sort LEVEL-FREE and STRUCTURE-FREE: each a valid type with
   a triple-like normal form (`PropValidA`), both typed at the sort, and
   convertible there. `EqKA.stuck` relates any two TRIPLE-LIKE normal forms
   (`TripleLikeA`: a proposition or a non-shape-headed type) by conversion, so
   a propositional domain's equality exists at any height. (M2-g′.) The
   structure of propositions as elements of `Prop` is kept BELOW the relation:
   `sortP` also carries `PropEqA` (`RcicAnnPropEq` — same structure, by typed
   reduction and conversion only, no height and no relation), so validity
   carries it to a `Prop` variable and the rows at `sort 0` invert it. The
   planned top layer (a conjunct proved after the tower) was measured circular
   at exactly that variable.

THE KILL CRITERION (R-Direction (2)): `TyKA_unique` — the term relation is a
function of the type — must be proved with NO ring-form premise. It is proved
below from `whTyA_det`, `not_isPropTy_sort`, the `¬ IsPropTy` exclusions and
the shapes alone. Nothing in this file assumes `SortConvChar`, `PiConvInj`,
`FamAppConvInj`, type uniqueness, or a hypothesis equivalent to one.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (3) the relation at one height, lower heights as parameters -/

abbrev LowEqTA (k : Nat) : Type :=
  (j : Nat) → j < k → LCtxA → ExprA → ExprA → Prop
abbrev LowTyTA (k : Nat) : Type :=
  (j : Nat) → j < k → LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop

/-- a valid proposition-as-type: a typed chain to a triple-like normal form
    (level-free; `TyKA.prop`/`TyKA.stuck` are its two faces). -/
def PropValidA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (a : ExprA) : Prop :=
  ∃ N, WhTyA E I n Γ a N ∧ TripleLikeA E I Γ N

mutual
/-- type equality at height `k`: both sides reduce (typed) to shapes that agree.
    No prop clause: type equality is STRUCTURAL for every type, propositions
    included (the rows come from here). The pi clause carries the typings of
    both domains and both codomains under their binders. -/
inductive EqKA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) : LCtxA → ExprA → ExprA → Prop
  | sort {Γ : LCtxA} {A B : ExprA} {l l' : Level}
      (hA : WhTyA E I n Γ A (.sort l)) (hB : WhTyA E I n Γ B (.sort l'))
      (hk : ht ρ₀ l < k) (hl : eqN l l')
      (hc : Nonempty (TyConvA E I n Γ A B)) : EqKA E I n ρ₀ k LE LT Γ A B
  | pi {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
      (hA : WhTyA E I n Γ A (.pi D u C v)) (hB : WhTyA E I n Γ B (.pi D' u' C' v'))
      (hu : eqN u u') (hv : eqN v v')
      (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
      (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
      (hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
      (hC'ty : Nonempty (HasTyA E I n (.assumption D' :: Γ) C' (.sort v')))
      (RD : WkSpecA → ExprA → ExprA → Prop)
      (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
      (hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
      (hc : Nonempty (TyConvA E I n Γ A B)) : EqKA E I n ρ₀ k LE LT Γ A B
  /-- M2-f (3), (3c): two applications of the same family at `=ₙ` levels,
      `I ls (ps ++ is)` and `I ls' (ps' ++ is')`, `ps`/`ps'` the family's `nparamsA`
      PARAMETERS. The LEFT application's data, as in `TyKA.fam` — its constructor-field
      relations `Rs` and index relations `RsF` at its parameters, valid (`hFld`,
      `hFldF`), the field and index domains at `=ₙ` levels and related prefixes related
      (`hFldeq`, `hFldFeq`), the recursive domains related (`hFldRec`) — and the CROSS
      data, at one level list and the same left prefix: the constructor-field domains
      of the two instances related (`hXFld`), the recursive domains and the results as
      family applications with related indices (`hXRec`, `hXRes`; `hXResR` the results
      of the RIGHT list of a left walk), the index domains related (`hXFeq`) — the `fam`
      analogue of `pi`'s `hDeq` / `hC`. The indices related along the left telescope
      (`hxs`). No parameter domain is ever walked (L-RING D2; `RcicAnnFamHeight`); the
      right instance's data are the left's carried across the parameters (`RcicAnnLRPer`).
      M2-f (6): the PARAMETERS convertible (`hpar`), pointwise at the left instances with the
      domain instances convertible, at every bounded list `=ₙ` the left's — a conversion, so
      height-free; row (3)'s parameter part, and what moves the parameter coherence of the fixed
      point (`FamPhiA`) across the two applications. R-NoFunRec-1 step 1 (1b): the left
      application's inner data, as in `TyKA.fam` (`hFldI`, `hFldIeq`, `hFldIRec`), and across the
      parameters, at every extension of the world, a function-recursive field's inner domains related
      (`hXFldI`) and its codomains cross-related (`hXRecI`). R-NoFunRec-1 step 1 (1c-ε2d-L1): and the
      declared Π-domains of a function-recursive field type-convertible, across `=ₙ` levels (`hFldIdom`)
      and across the parameters (`hXFldIdom`), at the world; carried, not read yet. -/
  | fam {Γ : LCtxA} {A B : ExprA} {r : Nat} {ls ls' : List Level} {ps ps' is is' : List ExprA}
      {m : CheckedMemberA} {u₀ : Level}
      (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
      (hB : WhTyA E I n Γ B (foldAppsA (.const r ls') (ps' ++ is')))
      (hnA : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
      (hnB : hStepFnA E I.fn Γ (foldAppsA (.const r ls') (ps' ++ is')) = none)
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hsh : piBodyA m.mtypeA = .sort u₀) (hls : eqNList ls ls')
      (hps : ps.length = m.nparamsA) (hps' : ps'.length = m.nparamsA)
      (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
      (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (RsI : InnerRelsA)
      (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
          (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
            (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
      (hFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          eqNListB n ls lsF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          ArgsRelPA (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
            (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
      (hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          RecDomRelA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) D D')
      (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' →
          ArgsRelPA (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          applyTelA pre' TF' = some (.pi D' uD' C' vC') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hXRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) D D')
      (hXRes : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA)
          (R R' : ExprA),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre' →
          applyTelA pre T = some R → applyTelA pre T' = some R' →
          RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R R')
      (hXResR : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds : List FieldShape) (T T' T'' : ExprA) (pre pre' : List ExprA)
          (R' R'' : ExprA),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre' →
          applyTelA pre' T' = some R' → applyTelA pre' T'' = some R'' →
          RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R' R'')
      (hXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF' →
          ArgsRelPA (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre TF' = some (.pi D' uD' C' vC') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hxs : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF →
          ArgsRelPA (RsF [] ls) m.nparamsA ps TF is is')
      (hc : Nonempty (TyConvA E I n Γ A B))
      (hpar : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ lsX : List Level, eqNListB n ls lsX →
          ParConvA E I n (wkCtxA ρ Γ) (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA)
            (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)))
      (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          TyKA E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
            (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
      (hFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
      (hFldIRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
          RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
            ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
      (hXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
      (hXRecI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs (wkExprA ρ' D') = some C₁' →
          RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
            ((ps.map (wkExprA ρ)).map (wkExprA ρ')) ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
      (hFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
      (hXFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D')) :
      EqKA E I n ρ₀ k LE LT Γ A B
  | stuck {Γ : LCtxA} {A B N N' : ExprA}
      (hA : WhTyA E I n Γ A N) (hB : WhTyA E I n Γ B N')
      (hN : TripleLikeA E I Γ N) (hN' : TripleLikeA E I Γ N')
      (hc : Nonempty (TyConvA E I n Γ A B)) : EqKA E I n ρ₀ k LE LT Γ A B

/-- type validity at height `k`, with the TERM relation as index. -/
inductive TyKA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) : LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  /-- THE PROP CLAUSE, keyed on the syntax of the normal form: any two terms
      typed there and convertible — which `ConvA.irr` grants to any two typed
      terms. No Kripke data: this is exactly what the pi clause would demand of
      an impredicative pi and cannot have (L-RING M2). -/
  | prop {Γ : LCtxA} {A A' : ExprA}
      (hA : WhTyA E I n Γ A A') (hn : hStepFnA E I.fn Γ A' = none)
      (hP : IsPropTy E I Γ A') :
      TyKA E I n ρ₀ k LE LT Γ A (fun a b =>
        Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
        Nonempty (ConvA E I n Γ a b A'))
  /-- a Type-level sort: its elements are related as types at the sort's own
      height `ht l`, with the lower relations. -/
  | sortT {Γ : LCtxA} {A : ExprA} {l : Level}
      (hA : WhTyA E I n Γ A (.sort l)) (hz : isZero l = false) (hk : ht ρ₀ l < k) :
      TyKA E I n ρ₀ k LE LT Γ A (fun a b =>
        LE (ht ρ₀ l) hk Γ a b ∧
        (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
        (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
        Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
        Nonempty (ConvA E I n Γ a b (.sort l)))
  /-- a `Prop`-level sort: two propositions are related iff each is a valid
      type with a triple-like normal form, both are typed at the sort, they
      are convertible there, and they have the same STRUCTURE (`PropEqA`,
      M2-g′: stated below the relation, so level-free and height-free;
      R-PropOutOfTower keeps the heights out, `RcicAnnPropEq` the structure in). -/
  | sortP {Γ : LCtxA} {A : ExprA} {l : Level}
      (hA : WhTyA E I n Γ A (.sort l)) (hz : isZero l = true) :
      TyKA E I n ρ₀ k LE LT Γ A (fun a b =>
        PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
        Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
        Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b)
  | pi {Γ : LCtxA} {A D C : ExprA} {u v : Level}
      (hA : WhTyA E I n Γ A (.pi D u C v))
      (hnp : ¬ IsPropTy E I Γ (.pi D u C v))
      (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
      (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
      (RD : WkSpecA → ExprA → ExprA → Prop)
      (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
      (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
      (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
      TyKA E I n ρ₀ k LE LT Γ A (fun f g =>
        (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
          RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
        Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
        Nonempty (ConvA E I n Γ f g (.pi D u C v)))
  /-- M2-f (3), (3c), THE FAM CLAUSE: a Type-level application `I ls (ps ++ is)` of a
      family of `E`, `ps` its `nparamsA` PARAMETERS, at the normal form carried
      weak-head normal and not a proposition; its sort `u` from the family's telescope.
      The term relation is the least fixed point of `FamPhiA` at that carrier, with the
      Kripke data at the carrier's (weakened) parameters and at level lists `=ₙ` the
      carrier's: `Rs ρ c lsC i prev` the relation of constructor `c`'s PLAIN field after
      the prefix `prev` (the parameters, then fields), valid under every world whenever
      the field prefix is related (`hFld`); `RsF ρ lsF i prev` the same for the family's
      indices (`hFldF`); the field and index domains at `=ₙ` level lists and related
      prefixes related (`hFldeq`, `hFldFeq`), the two domains of a recursive position
      family applications with related indices (`hFldRec`), the diagonal index datum
      (`hxsD`). No parameter domain and no other universe instance is demanded at the
      clause's height (L-RING D2; M2-f (3c)-0 measured both over-demands on the clause of
      M2-f (3b)); the index domains are, at the carrier's levels — `RcicAnnFamHeight` pins
      the repaired clause's acceptance and the large-index boundary that remains.
      R-NoFunRec-1 step 1 (1b), A FUNCTION-RECURSIVE FIELD: `RsI ρ c lsC i prev` the relations of its
      inner binders (`innerRelsA`: at an extension `ρ'` of the world, read at `ρ ∘ ρ'`), valid at every
      such extension whenever the field prefix is related at the world and the inner prefix along the
      field's weakened domain (`hFldI`); the inner domains of two `=ₙ` level instances related
      (`hFldIeq`), and after all inner binders the two codomains related recursive domains
      (`hFldIRec`). R-NoFunRec-1 step 1 (1c-ε2d-L1): and the declared Π-domains of the field at two `=ₙ`
      level instances type-convertible at the world (`hFldIdom`); carried, not read yet. -/
  | fam {Γ : LCtxA} {A : ExprA} {r : Nat} {ls : List Level} {ps is : List ExprA}
      {m : CheckedMemberA} {u u₀ : Level}
      (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
      (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
      (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hsh : piBodyA m.mtypeA = .sort u₀) (hps : ps.length = m.nparamsA)
      (hu : applyTelA (ps ++ is) (instantiateLevelsA ls m.mtypeA) = some (.sort u))
      (hz : isZero u = false)
      (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
      (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (RsI : InnerRelsA)
      (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
          (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
            (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
      (hFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          eqNListB n ls lsF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          ArgsRelPA (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
            (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
      (hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          RecDomRelA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) D D')
      (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' →
          ArgsRelPA (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          applyTelA pre' TF' = some (.pi D' uD' C' vC') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hxsD : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF →
          ArgsRelPA (RsF [] ls) m.nparamsA ps TF is is)
      (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          TyKA E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
            (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
      (hFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          EqKA E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
      (hFldIRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
          RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
            ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
      (hFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D')) :
      TyKA E I n ρ₀ k LE LT Γ A (fun a b =>
        LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] (foldAppsA (.const r ls) (ps ++ is)) a b)
  | stuck {Γ : LCtxA} {A N : ExprA}
      (hA : WhTyA E I n Γ A N) (hN : StuckA E I Γ N) :
      TyKA E I n ρ₀ k LE LT Γ A (fun a b =>
        Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
        Nonempty (ConvA E I n Γ a b N))
end

/-! ## (4) tying the knot over heights -/

mutual
def LREqA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) :
    (k : Nat) → LCtxA → ExprA → ExprA → Prop
  | k => EqKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j)
  termination_by k => k
  decreasing_by all_goals assumption
def LRTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) :
    (k : Nat) → LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | k => TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j)
  termination_by k => k
  decreasing_by all_goals assumption
end

theorem LREqA_eq (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) :
    LREqA E I n ρ₀ k =
      EqKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) := by
  rw [LREqA]

theorem LRTyA_eq (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) :
    LRTyA E I n ρ₀ k =
      TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) := by
  rw [LRTyA]

/-! ## (5) THE KILL CRITERION: the term relation is a function of the type

Stated through `TyKA.rec` with an explicit motive (L-RING's device). The four
clauses exclude each other by: `whTyA_det` (one normal form, through erasure),
the shapes (`sort` ≠ `pi`, neither stuck), and `IsPropTy` vs `¬ IsPropTy` — with
`not_isPropTy_sort` for the sort/prop pair. No row, no uniqueness of types, no
hypothesis about `ConvA` is consumed. -/

theorem TyKA_unique {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {LE : LowEqTA k} {LT : LowTyTA k} :
    {Γ : LCtxA} → {A : ExprA} → {R R' : ExprA → ExprA → Prop} →
    TyKA E I n ρ₀ k LE LT Γ A R → TyKA E I n ρ₀ k LE LT Γ A R' → R = R' :=
  fun {_Γ _A _R _R'} h h' =>
  TyKA.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ∀ (R' : ExprA → ExprA → Prop),
      TyKA E I n ρ₀ k LE LT Γ A R' → R = R')
    -- EqKA minors: sort, pi, fam, stuck
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    -- TyKA.prop
    (fun hA hn hP _ h' => by
      cases h' with
      | prop hA' hn' _ =>
          have e := whTyA_det hA hA' hn hn'
          cases e
          rfl
      | sortT hA' _ _ =>
          have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
          subst e
          exact absurd hP (not_isPropTy_sort _ _ _ _)
      | sortP hA' _ =>
          have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
          subst e
          exact absurd hP (not_isPropTy_sort _ _ _ _)
      | pi hA' hnp' _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' hn (hStepFnA_pi _ _ _ _ _ _ _)
          subst e
          exact absurd hP hnp'
      | fam hA' hn' hnp' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' hn hn'
          subst e
          exact absurd hP hnp'
      | stuck hA' hN' =>
          have e := whTyA_det hA hA' hn hN'.1
          subst e
          rfl)
    -- TyKA.sortT
    (fun hA hz hk _ h' => by
      cases h' with
      | sortT hA' _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          rfl
      | sortP hA' hz' =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          rw [hz] at hz'
          cases hz'
      | prop hA' hn' hP' =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) hn'
          subst e
          exact absurd hP' (not_isPropTy_sort _ _ _ _)
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | fam hA' hn' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) hn'
          exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
      | stuck hA' hN' =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) hN'.1
          subst e
          exact (stuckA_not_sort hN').elim)
    -- TyKA.sortP
    (fun hA hz _ h' => by
      cases h' with
      | sortP hA' _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          rfl
      | sortT hA' hz' _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          rw [hz] at hz'
          cases hz'
      | prop hA' hn' hP' =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) hn'
          subst e
          exact absurd hP' (not_isPropTy_sort _ _ _ _)
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | fam hA' hn' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) hn'
          exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
      | stuck hA' hN' =>
          have e := whTyA_det hA hA' (hStepFnA_sort _ _ _ _) hN'.1
          subst e
          exact (stuckA_not_sort hN').elim)
    -- TyKA.pi
    (fun hA _hnp _hDty _hCty RD hD RC hC _hCeq ihD ihC _ihCeq _ h' => by
      cases h' with
      | pi hA' _ _ _ RD' hD' RC' hC' _ =>
          have e := whTyA_det hA hA' (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
          funext f g
          apply propext
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_, h2, h3, h4⟩
            have hRD : RD ρ = RD' ρ := ihD ρ hρ _ (hD' ρ hρ)
            have hr' : RD ρ a a' := by rw [hRD]; exact hr
            have hRC : RC ρ a = RC' ρ a := ihC ρ hρ a a' hr' _ (hC' ρ hρ a a' hr)
            rw [← hRC]; exact h1 ρ hρ a a' hr'
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_, h2, h3, h4⟩
            have hRD : RD ρ = RD' ρ := ihD ρ hρ _ (hD' ρ hρ)
            have hr' : RD' ρ a a' := by rw [← hRD]; exact hr
            have hRC : RC ρ a = RC' ρ a := ihC ρ hρ a a' hr _ (hC' ρ hρ a a' hr')
            rw [hRC]; exact h1 ρ hρ a a' hr'
      | prop hA' hn' hP' =>
          have e := whTyA_det hA hA' (hStepFnA_pi _ _ _ _ _ _ _) hn'
          subst e
          exact absurd hP' _hnp
      | sortT hA' _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | sortP hA' _ =>
          have e := whTyA_det hA hA' (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | fam hA' hn' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' (hStepFnA_pi _ _ _ _ _ _ _) hn'
          exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | stuck hA' hN' =>
          have e := whTyA_det hA hA' (hStepFnA_pi _ _ _ _ _ _ _) hN'.1
          subst e
          exact (stuckA_not_pi hN').elim)
    -- TyKA.fam
    (fun hA hn hnp hm hind _hsh hps hu _hz _Rs _RsF _RsI hFld hFldF _hFldeq _hFldRec _hFldFeq _hxsD hFldI
        _hFldIeq _hFldIRec _hFldIdom ihFld ihFldF _ihFldeq _ihFldFeq ihFldI _ihFldIeq _ h' => by
      cases h' with
      | prop hA' hn' hP' =>
          have e := whTyA_det hA hA' hn hn'
          subst e
          exact absurd hP' hnp
      | sortT hA' _ _ =>
          have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
          exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
      | sortP hA' _ =>
          have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
          exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' hn (hStepFnA_pi _ _ _ _ _ _ _)
          exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | fam hA' hn' _ hm' hind' _ hps' hu' _ Rs' RsF' RsI' hFld' hFldF' _ _ _ _ hFldI' _ =>
          have e := whTyA_det hA hA' hn hn'
          obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
          subst er; subst els
          rw [hm] at hm'
          injection hm' with em
          subst em
          obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps, hps'])
          subst eps; subst eis
          rw [hu] at hu'
          injection hu' with eu
          injection eu with eu
          subst eu
          funext a b
          apply propext
          constructor
          · refine lfpWA_le_of (ps := _) (ls₀ := _)
              (fun ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT h1 h2
                  hTD =>
                ihFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT h1
                  hTD _ (hFld' ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h2 hTD))
              (fun ρ hρ lsF TF pre pre' D uD C vC hlF hTF h1 h2 hTD =>
                ihFldF ρ hρ lsF TF pre pre' D uD C vC hlF hTF h1 hTD _
                  (hFldF' ρ hρ lsF TF pre pre' D uD C vC hlF hTF h2 hTD))
              (fun ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT h1
                  h2 hTD ρ' hρ' ys ys' B uB C' vB hy1 hy2 hB => by
                rw [Nat.zero_add, List.nil_append]
                exact ihFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA
                  hlC hT h1 hTD ρ' hρ' ys ys' B uB C' vB hy1 hB _
                  (hFldI' ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h2 hTD ρ' hρ' ys ys' B uB C' vB hy2 hB))
              (wkOk₀A_nil _ _ _ _) (by rw [map_wkExprA_nil]; exact carrierParamsA_famApp hps _)
              (by rw [carrierLevelsA_foldAppsA]; exact eqNListA_refl _)
          · refine lfpWA_le_of (ps := _) (ls₀ := _)
              (fun ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT h1 h2
                  hTD =>
                (ihFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT h2
                  hTD _ (hFld' ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h1 hTD)).symm)
              (fun ρ hρ lsF TF pre pre' D uD C vC hlF hTF h1 h2 hTD =>
                (ihFldF ρ hρ lsF TF pre pre' D uD C vC hlF hTF h2 hTD _
                  (hFldF' ρ hρ lsF TF pre pre' D uD C vC hlF hTF h1 hTD)).symm)
              (fun ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT h1
                  h2 hTD ρ' hρ' ys ys' B uB C' vB hy1 hy2 hB => by
                rw [Nat.zero_add, List.nil_append]
                exact (ihFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA
                  hlC hT h2 hTD ρ' hρ' ys ys' B uB C' vB hy2 hB _
                  (hFldI' ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h1 hTD ρ' hρ' ys ys' B uB C' vB hy1 hB)).symm)
              (wkOk₀A_nil _ _ _ _) (by rw [map_wkExprA_nil]; exact carrierParamsA_famApp hps _)
              (by rw [carrierLevelsA_foldAppsA]; exact eqNListA_refl _)
      | stuck hA' hN' =>
          have e := whTyA_det hA hA' hn hN'.1
          exact (stuckA_not_fam hN' (by rw [← e, foldAppsA_const_head]) hm hind).elim)
    -- TyKA.stuck
    (fun hA hN _ h' => by
      cases h' with
      | stuck hA' hN' =>
          have e := whTyA_det hA hA' hN.1 hN'.1
          cases e
          rfl
      | prop hA' hn' _ =>
          have e := whTyA_det hA hA' hN.1 hn'
          subst e
          rfl
      | sortT hA' _ _ =>
          have e := whTyA_det hA hA' hN.1 (hStepFnA_sort _ _ _ _)
          subst e
          exact (stuckA_not_sort hN).elim
      | sortP hA' _ =>
          have e := whTyA_det hA hA' hN.1 (hStepFnA_sort _ _ _ _)
          subst e
          exact (stuckA_not_sort hN).elim
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' hN.1 (hStepFnA_pi _ _ _ _ _ _ _)
          subst e
          exact (stuckA_not_pi hN).elim
      | fam hA' hn' _ hm' hind' _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA hA' hN.1 hn'
          exact (stuckA_not_fam hN (by rw [e, foldAppsA_const_head]) hm' hind').elim)
    h _R' h'

/-- the knotted form. -/
theorem LRTyA_unique {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R R' : ExprA → ExprA → Prop}
    (h : LRTyA E I n ρ₀ k Γ A R) (h' : LRTyA E I n ρ₀ k Γ A R') : R = R' := by
  rw [LRTyA_eq] at h h'
  exact TyKA_unique h h'

/-! ## (6) non-vacuity: each clause is inhabited, on closed terms -/

/-- a type whose synthesised sort is NOT `0` at some fuel is not a proposition
    (determinism of `inferSortA` across fuels). -/
theorem not_isPropTy_of_inferSortA {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA}
    {A : ExprA} {fuel : Nat} {l : Level}
    (h : inferSortA E I.fn fuel Γ A = some l) (hl : isZero l = false) : ¬ IsPropTy E I Γ A := by
  intro ⟨f', l', h', h0⟩
  have e := inferSortA_det E I.fn h h'
  subst e
  rw [hl] at h0
  cases h0

/-- `ω := ∀ (Z : Sort 0), Z`, annotated: domain sort `1`, codomain sort `0`. -/
def omegaA : ExprA := .pi (.sort .zero) (.succ .zero) (.bvar 0) .zero

/-- `ω` IS a proposition for the key: `imax 1 0 =ₙ 0`. Where L-RING's Prop clause
    was non-cumulative at `∀ (Z : Prop), Z → Z` (C8/M2), the key here is read
    off the annotation. -/
theorem omegaA_isPropTy : IsPropTy emptyEnvA noIotaA [] omegaA :=
  ⟨1, .imax (.succ .zero) .zero, by decide, rfl⟩

/-- and `Π (x : Sort 0), Sort 0` (`pinPiA`, codomain sort `1`) is not. -/
theorem pinPiA_not_isPropTy : ¬ IsPropTy emptyEnvA noIotaA [] pinPiA :=
  fun h => absurd ((isPropTy_pi_iff _ _ _ _ _ _ _).mp h) (by decide)

/-- `ω` typed: `∀ (Z : Sort 0), Z : Sort (imax 1 0)`. -/
def omegaA_ty (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    HasTyA E I n [] omegaA (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] (.sort .zero) (.succ .zero) (.bvar 0) .zero (.sort [] .zero)
    (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))

/-- the prop clause, inhabited: `ω`. -/
example (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) :
    ∃ R, TyKA emptyEnvA noIotaA 0 ρ₀ k LE LT [] omegaA R :=
  ⟨_, .prop (whTyA_of_hasTy (omegaA_ty _ _ _)) rfl omegaA_isPropTy⟩

/-- the `Prop`-sort clause, inhabited: `Sort 0`, at any height. -/
example (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) :
    ∃ R, TyKA emptyEnvA noIotaA 0 ρ₀ k LE LT [] (.sort .zero) R :=
  ⟨_, .sortP (whTyA_of_hasTy (.sort [] .zero)) rfl⟩

/-- the Type-sort clause, inhabited: `Sort 1` at height `2`. -/
example (LE : LowEqTA 2) (LT : LowTyTA 2) :
    ∃ R, TyKA emptyEnvA noIotaA 0 (fun _ => 0) 2 LE LT [] (.sort (.succ .zero)) R :=
  ⟨_, .sortT (whTyA_of_hasTy (.sort [] (.succ .zero))) rfl (by decide)⟩

/-- the stuck clause, inhabited: a variable of type `Sort 1` is a stuck type
    that is not a proposition. -/
example (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) :
    ∃ R, TyKA emptyEnvA noIotaA 0 ρ₀ k LE LT [.assumption (.sort (.succ .zero))] (.bvar 0) R :=
  ⟨_, .stuck (whTyA_of_hasTy (.bvar _ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (.sort _ _)))
    ⟨rfl, by simp [appsSpineA, isShapeHeadA]⟩⟩

#print axioms not_isPropTy_of_inferSortA
#print axioms omegaA_isPropTy
#print axioms pinPiA_not_isPropTy
#print axioms TyKA_unique
#print axioms LRTyA_unique

end Rcic.Declarative.Ann
