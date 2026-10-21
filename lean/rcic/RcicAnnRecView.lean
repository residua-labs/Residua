import rcic.RcicAnnGroup

/-!
# M2-f (5a) — the recursor's view: 05 §11–§13 built from the group's views

05 §1 admits an inductive group as ONE atomic extension: the family, its constructors, then the
derived recursor (§3: member `0` the family, `1..k` the constructors in candidate order, `k + 1` the
recursor). The recursor is DERIVED (§13), so its view has no freedom beyond the elimination policy
(§10–§11): its stored type is the type BUILT from the family's and the constructors' views,

  `Π params, Π (motive : Π indices, Π (x : F params indices), Sort wM),
    Π minor_0 … Π minor_{k-1}, Π indices, Π (major : F params indices), motive indices major`,

each minor (§12) the constructor's fields left to right, an induction hypothesis `motive idx x`
after each directly recursive field (`Π ys, motive idx (x ys)` after a function-recursive one), and the
conclusion `motive res (c params fields)`; `wM` is the
fresh universe `param fm.arity` (AnySort, recursor arity `fm.arity + 1`) or `zero` (PropOnly, arity
`fm.arity`).

The whole type is ONE `piTelA` over its binders (`recDomsA`), so a walk along it is the generic
`applyTelA_piTelA`. A minor's telescope is a state machine over the parameter locals, the motive,
the field locals and the plain substitution (`minorFieldsA`): its field domains are
`ctorFieldsA`'s, by the same formulas, with the induction hypotheses interleaved, which is what lets
the ι reduct (05 §14, `rhsArgsA`) walk it (M2-f (5b)).

Laws here: the counts and the body the concrete ι reads (`piCountA_recTypeA`,
`piBodyA_recTypeA`, the major's domain last), the motive's sort at its binder, and level
instantiation through the builder.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the minor premise's telescope (05 §12) -/

/-- a function-recursive field's induction hypothesis (05 §12), in the minor's context right after the
    field `x` (the variable `j` binders up): the field's inner binders under the plain substitution, each
    under the earlier ones, then the motive at the indices and at `x` applied to the `m` inner variables
    (R-NoFunRec-1 step 1 (1c)). -/
def frecIHA (wM : Level) : ExprA → Nat → SubstA → List (ExprA × Level) → List ExprA → Nat → ExprA × Level
  | mot, j, σ, [], idx, m =>
      (foldAppsA mot (idx.map (substA σ) ++ [foldAppsA (.bvar j) ((List.range m).reverse.map ExprA.bvar)]), wM)
  | mot, j, σ, (D, u) :: ds, idx, m =>
      let r := frecIHA wM (liftA 0 1 mot) (j + 1) σ.up ds idx m
      (.pi (substA σ D) u r.1 r.2, .imax u r.2)

theorem frecIHA_snd (wM : Level) (idx : List ExprA) (m : Nat) :
    (ds : List (ExprA × Level)) → (mot : ExprA) → (j : Nat) → (σ : SubstA) →
    (frecIHA wM mot j σ ds idx m).2 = frecLevelA wM ds
  | [], _, _, _ => rfl
  | (_, _) :: ds, mot, j, σ => by
      simp only [frecIHA, frecLevelA, frecIHA_snd wM idx m ds]

/-- a minor premise's fields with their induction hypotheses, then its conclusion, in the minor's
    context: `pl` the parameter locals at the current depth, `mot` the motive, `fl` the field locals
    so far, `σ` the plain context (the parameters, then the earlier plain fields) into the current
    one; `c` the constructor, `ls` the family's canonical levels, `wF` the family's sort, `wM` the
    motive's. After a directly recursive field its induction hypothesis `mot idx x` (05 §12), after a
    function-recursive one `Π (B :: Bs), mot idx (x ys)` (`frecIHA`); the conclusion
    `mot res (c (pl ++ fl))`. -/
def minorFieldsA (f c : Nat) (ls : List Level) (wF wM : Level) :
    List ExprA → ExprA → List ExprA → SubstA → List FieldA → List ExprA → ExprA × Level
  | pl, mot, fl, σ, [], res =>
      (foldAppsA mot (res.map (substA σ) ++ [foldAppsA (.const c ls) (pl ++ fl)]), wM)
  | pl, mot, fl, σ, .plain D u :: fs, res =>
      let r := minorFieldsA f c ls wF wM (pl.map (liftA 0 1)) (liftA 0 1 mot)
        (fl.map (liftA 0 1) ++ [.bvar 0]) σ.up fs res
      (.pi (substA σ D) u r.1 r.2, .imax u r.2)
  | pl, mot, fl, σ, .drec idx :: fs, res =>
      let r := minorFieldsA f c ls wF wM (pl.map (liftA 0 2)) (liftA 0 2 mot)
        (fl.map (liftA 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res
      (.pi (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) wF
        (.pi (foldAppsA (liftA 0 1 mot) ((idx.map (substA σ)).map (liftA 0 1) ++ [.bvar 0])) wM r.1 r.2)
        (.imax wM r.2),
        .imax wF (.imax wM r.2))
  | pl, mot, fl, σ, .frec B uB Bs idx :: fs, res =>
      let d := frecDomA f ls wF pl σ ((B, uB) :: Bs) idx
      let ih := frecIHA wM (liftA 0 1 mot) 0 σ.shift1 ((B, uB) :: Bs) idx (Bs.length + 1)
      let r := minorFieldsA f c ls wF wM (pl.map (liftA 0 2)) (liftA 0 2 mot)
        (fl.map (liftA 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res
      (.pi d.1 d.2 (.pi ih.1 ih.2 r.1 r.2) (.imax ih.2 r.2), .imax d.2 (.imax ih.2 r.2))
  | pl, mot, fl, σ, .drecD D idx :: fs, res =>
      let r := minorFieldsA f c ls wF wM (pl.map (liftA 0 2)) (liftA 0 2 mot)
        (fl.map (liftA 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res
      (.pi (substA σ D) wF
        (.pi (foldAppsA (liftA 0 1 mot) ((idx.map (substA σ)).map (liftA 0 1) ++ [.bvar 0])) wM r.1 r.2)
        (.imax wM r.2),
        .imax wF (.imax wM r.2))

/-- the minor telescope's sort: independent of the state. -/
def minorLevelA (wF wM : Level) : List FieldA → Level
  | [] => wM
  | .plain _ u :: fs => .imax u (minorLevelA wF wM fs)
  | .drec _ :: fs => .imax wF (.imax wM (minorLevelA wF wM fs))
  | .frec B uB Bs _ :: fs =>
      .imax (frecLevelA wF ((B, uB) :: Bs)) (.imax (frecLevelA wM ((B, uB) :: Bs)) (minorLevelA wF wM fs))
  | .drecD _ _ :: fs => .imax wF (.imax wM (minorLevelA wF wM fs))

theorem minorFieldsA_snd (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    (minorFieldsA f c ls wF wM pl mot fl σ fs res).2 = minorLevelA wF wM fs
  | [], _, _, _, _ => rfl
  | .plain _ _ :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, minorLevelA, minorFieldsA_snd f c ls wF wM res fs]
  | .drec _ :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, minorLevelA, minorFieldsA_snd f c ls wF wM res fs]
  | .frec _ _ _ _ :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, minorLevelA, minorFieldsA_snd f c ls wF wM res fs, frecDomA_snd,
        frecIHA_snd]
  | .drecD _ _ :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, minorLevelA, minorFieldsA_snd f c ls wF wM res fs]

/-! ## (2) the recursor's binders and type (05 §11, §13) -/

/-- a constructor's data for its minor: reference, fields, result indices. -/
abbrev MinorDataA : Type := Nat × List FieldA × List ExprA

/-- the family application over its locals, in the context of the parameters and `ni` indices:
    `F ls (params ++ indices)`, the indices innermost. -/
def famLocalsA (f : Nat) (ls : List Level) (np ni : Nat) : ExprA :=
  foldAppsA (.const f ls) ((paramLocalsA np).map (liftA 0 ni) ++ paramLocalsA ni)

/-- the motive's type in the context of the parameters (05 §11):
    `Π indices, Π (x : F ls (params ++ indices)), Sort wM`, with its sort. -/
def motTyA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level)) (wF wM : Level) :
    ExprA × Level :=
  piTelA indices (.pi (famLocalsA f ls params.length indices.length) wF (.sort wM) (.succ wM))
    (.imax wF (.succ wM))

/-- a constructor's minor premise type in the context of the parameters and the motive (05 §12):
    the parameter locals one binder deep, the motive the innermost local, no field yet, the
    parameters' plain context shifted past the motive. -/
def minorTyA (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat) (cd : MinorDataA) : ExprA × Level :=
  minorFieldsA f cd.1 ls wF wM ((paramLocalsA np).map (liftA 0 1)) (.bvar 0) [] SubstA.id.shift1
    cd.2.1 cd.2.2

/-- the minors' telescope: the `j`-th minor lifted past the `j` earlier ones (it mentions none of
    them). -/
def minorDomsA (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat) :
    Nat → List MinorDataA → List (ExprA × Level)
  | _, [] => []
  | j, cd :: cds => (liftA 0 j (minorTyA f ls wF wM np cd).1, (minorTyA f ls wF wM np cd).2) ::
      minorDomsA f ls wF wM np (j + 1) cds

/-- the recursor's body in the context of all its binders: `motive indices major` — the motive
    past the `k` minors, `ni` indices and the major; the index locals one binder deep. -/
def recBodyA (ni k : Nat) : ExprA :=
  foldAppsA (.bvar (ni + k + 1)) ((paramLocalsA ni).map (liftA 0 1) ++ [.bvar 0])

/-- the recursor's binders in 05 §11's order: the parameters, the motive, the minors in
    constructor order, the indices (lifted past the motive and the minors), the major. -/
def recDomsA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level)) (wF wM : Level)
    (cds : List MinorDataA) : List (ExprA × Level) :=
  params ++ [motTyA f ls params indices wF wM] ++ minorDomsA f ls wF wM params.length 0 cds ++
    liftDomsA 0 (cds.length + 1) indices ++
    [(liftA indices.length (cds.length + 1) (famLocalsA f ls params.length indices.length), wF)]

/-- THE RECURSOR'S TYPE built from the views (05 §13), one telescope over `recDomsA`. -/
def recTypeA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level)) (wF wM : Level)
    (cds : List MinorDataA) : ExprA :=
  (piTelA (recDomsA f ls params indices wF wM cds) (recBodyA indices.length cds.length) wM).1

/-! ## (3) the counts and the body the concrete ι reads -/

theorem minorDomsA_length (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat) :
    (j : Nat) → (cds : List MinorDataA) → (minorDomsA f ls wF wM np j cds).length = cds.length
  | _, [] => rfl
  | j, _ :: cds => by
      simp only [minorDomsA, List.length_cons, minorDomsA_length f ls wF wM np (j + 1) cds]

theorem recDomsA_length (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    (recDomsA f ls params indices wF wM cds).length =
      params.length + 1 + cds.length + indices.length + 1 := by
  simp only [recDomsA, List.length_append, List.length_singleton, minorDomsA_length,
    liftDomsA_length]

theorem piCountA_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → piCountA (piTelA ds B w).1 = ds.length + piCountA B
  | [] => by simp [piTelA]
  | (D, u) :: ds => by
      simp only [piTelA, piCountA, piCountA_piTelA B w ds, List.length_cons]
      omega

theorem piCountA_foldAppsA_of_not_pi : (h : ExprA) → (ys : List ExprA) →
    (∀ D u C v, h ≠ .pi D u C v) → piCountA (foldAppsA h ys) = 0
  | h, [], hh => by
      cases h with
      | pi D u C v => exact absurd rfl (hh D u C v)
      | _ => rfl
  | h, y :: ys, _ => piCountA_foldAppsA_of_not_pi (.app h y) ys (fun _ _ _ _ e => ExprA.noConfusion e)

theorem piCountA_foldAppsA_bvar (i : Nat) (xs : List ExprA) : piCountA (foldAppsA (.bvar i) xs) = 0 :=
  piCountA_foldAppsA_of_not_pi _ xs (fun _ _ _ _ e => ExprA.noConfusion e)

/-- the recursor type's telescope count: `nparams + 1 + nMinors + nindices + 1` (05 §13). -/
theorem piCountA_recTypeA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    piCountA (recTypeA f ls params indices wF wM cds) =
      params.length + 1 + cds.length + indices.length + 1 := by
  rw [recTypeA, piCountA_piTelA, recDomsA_length, recBodyA, piCountA_foldAppsA_bvar]

theorem piBodyA_foldAppsA_bvar (i : Nat) (xs : List ExprA) :
    piBodyA (foldAppsA (.bvar i) xs) = foldAppsA (.bvar i) xs := by
  apply piBodyA_of_not_pi
  intro D u C v h
  have := congrArg (fun e => (appsSpineA e).1) h
  simp only [appsSpineA_foldAppsA] at this
  exact ExprA.noConfusion this

/-- the recursor type's body is `motive indices major` (05 §13). -/
theorem piBodyA_recTypeA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    piBodyA (recTypeA f ls params indices wF wM cds) = recBodyA indices.length cds.length := by
  rw [recTypeA, piBodyA_piTelA, recBodyA, piBodyA_foldAppsA_bvar]

theorem paramLocalsA_length : (n : Nat) → (paramLocalsA n).length = n
  | 0 => rfl
  | n + 1 => by simp only [paramLocalsA, List.length_cons, paramLocalsA_length n]

/-- the body's spine: the motive applied to the `ni` index locals and the major. -/
theorem appsSpineA_recBodyA (ni k : Nat) :
    (appsSpineA (recBodyA ni k)).2.length = ni + 1 := by
  simp only [recBodyA, appsSpineA_foldAppsA, List.length_append, List.length_map,
    paramLocalsA_length, List.length_singleton]
  simp [appsSpineA]

/-- the major's domain is the last binder's: `F ls (params ++ indices)` (05 §13). -/
theorem piDomsA_recTypeA_getLast (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    (piDomsA (recTypeA f ls params indices wF wM cds)).getLast? =
      some (liftA indices.length (cds.length + 1) (famLocalsA f ls params.length indices.length)) := by
  rw [recTypeA, piDomsA_piTelA, recBodyA]
  have hb : piDomsA (foldAppsA (.bvar (indices.length + cds.length + 1))
      ((paramLocalsA indices.length).map (liftA 0 1) ++ [.bvar 0])) = [] := by
    apply piDomsA_of_not_pi
    intro D u C v h
    have := congrArg (fun e => (appsSpineA e).1) h
    simp only [appsSpineA_foldAppsA] at this
    exact ExprA.noConfusion this
  rw [hb, List.append_nil, recDomsA]
  simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append, List.getLast?_singleton]
  rfl

theorem piDomListA_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → piDomListA (piTelA ds B w).1 = ds ++ piDomListA B
  | [] => rfl
  | (D, u) :: ds => by simp only [piTelA, piDomListA, List.cons_append, piDomListA_piTelA B w ds]

theorem piDomListA_foldAppsA_bvar (i : Nat) (xs : List ExprA) :
    piDomListA (foldAppsA (.bvar i) xs) = [] := by
  cases h : foldAppsA (.bvar i) xs with
  | pi D u C v =>
      have := congrArg (fun e => (appsSpineA e).1) h
      simp only [appsSpineA_foldAppsA] at this
      exact ExprA.noConfusion this
  | _ => rfl

/-- the recursor type's binders, with their sorts, are `recDomsA`'s (O1-b-1). -/
theorem piDomListA_recTypeA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    piDomListA (recTypeA f ls params indices wF wM cds) = recDomsA f ls params indices wF wM cds := by
  rw [recTypeA, piDomListA_piTelA, recBodyA, piDomListA_foldAppsA_bvar, List.append_nil]

/-- reversed, the major binder comes first, annotated with the family's sort `wF`. -/
theorem piDomListA_recTypeA_reverse (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    (piDomListA (recTypeA f ls params indices wF wM cds)).reverse =
      (liftA indices.length (cds.length + 1) (famLocalsA f ls params.length indices.length), wF) ::
        (params ++ [motTyA f ls params indices wF wM] ++ minorDomsA f ls wF wM params.length 0 cds ++
          liftDomsA 0 (cds.length + 1) indices).reverse := by
  rw [piDomListA_recTypeA, recDomsA, List.reverse_append]
  rfl

/-- the major's domain is headed by the family. -/
theorem appsSpineA_majorDom (f : Nat) (ls : List Level) (np ni a : Nat) :
    (appsSpineA (liftA ni a (famLocalsA f ls np ni))).1 = .const f ls := by
  rw [famLocalsA, liftA_foldAppsA, appsSpineA_foldAppsA]
  rfl

/-- O1-b-2, THE UNIT TEST IS COMPLETE ON BUILT RECURSOR TYPES: the recursor type 05 §13 builds for a
    group with one constructor without fields and no index, over a family whose sort is zero at every
    valuation, passes `unitGroupA` at the recursor's own reference. -/
theorem unitGroupA_of_recTypeA {r f : Nat} {m : CheckedMemberA} {ls : List Level}
    {params : List (ExprA × Level)} {wF wM : Level} {cd : MinorDataA}
    (hst : m.mtypeA = recTypeA f ls params [] wF wM [cd]) (hnf : cd.2.1 = []) (hr : r = f + 2)
    (hz : levelIsZero wF = true) : unitGroupA r m = true := by
  obtain ⟨c, fs, res⟩ := cd
  simp only at hnf
  subst hnf hr
  have hL : (piDomListA m.mtypeA).reverse =
      (liftA 0 2 (famLocalsA f ls params.length 0), wF) ::
        (liftA 0 0 (minorTyA f ls wF wM params.length (c, [], res)).1,
          (minorTyA f ls wF wM params.length (c, [], res)).2) ::
        (motTyA f ls params [] wF wM) :: params.reverse := by
    rw [hst, piDomListA_recTypeA_reverse]
    simp [minorDomsA, liftDomsA]
  unfold unitGroupA
  rw [hL]
  simp only [minorTyA, minorFieldsA, foldAppsA_append, foldAppsA]
  simp [appsSpineA_majorDom, hz, motTyA, piTelA, liftA]

/-! ## (4) the motive's binder and its sort -/

theorem piBodyA_motTyA (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) : piBodyA (motTyA f ls params indices wF wM).1 = .sort wM := by
  rw [motTyA, piBodyA_piTelA]
  rfl

/-- the motive's type is the binder right after the parameters. -/
theorem piDomsA_recTypeA_motive (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (cds : List MinorDataA) :
    (piDomsA (recTypeA f ls params indices wF wM cds))[params.length]? =
      some (motTyA f ls params indices wF wM).1 := by
  rw [recTypeA, piDomsA_piTelA, recDomsA]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp

/-! ## (5) level instantiation passes through the builder -/

theorem map_instantiateLevelsA_liftA_paramLocalsA (ls : List Level) :
    (n : Nat) → ((paramLocalsA n).map (liftA 0 1)).map (instantiateLevelsA ls) =
      (paramLocalsA n).map (liftA 0 1)
  | 0 => rfl
  | n + 1 => by
      simp only [paramLocalsA, List.map, map_instantiateLevelsA_liftA_paramLocalsA ls n]
      congr 1
      simp [liftA, instantiateLevelsA]

theorem instantiateLevelsA_recBodyA (ls : List Level) (ni k : Nat) :
    instantiateLevelsA ls (recBodyA ni k) = recBodyA ni k := by
  rw [recBodyA, instantiateLevelsA_foldAppsA]
  simp only [List.map_append, List.map_cons, List.map_nil, map_instantiateLevelsA_liftA_paramLocalsA]
  rfl

/-- level instantiation of the built recursor type is the telescope of the instantiated binders
    over the (level-free) body. -/
theorem instantiateLevelsA_recTypeA (ms : List Level) (f : Nat) (ls : List Level)
    (params indices : List (ExprA × Level)) (wF wM : Level) (cds : List MinorDataA) :
    instantiateLevelsA ms (recTypeA f ls params indices wF wM cds) =
      (piTelA (instDomsA ms (recDomsA f ls params indices wF wM cds))
        (recBodyA indices.length cds.length) (instLevel ms wM)).1 := by
  have h := congrArg Prod.fst (instantiateLevelsA_piTelA ms (recBodyA indices.length cds.length) wM
    (recDomsA f ls params indices wF wM cds))
  simp only at h
  rw [recTypeA, h, instantiateLevelsA_recBodyA]

/-! ## (6) the group's recursor -/

/-- the elimination policy (05 §10–§11): the motive's universe is the fresh `param a` (AnySort,
    recursor arity `a + 1`) or `zero` (PropOnly, arity `a`). Either is admitted for every family
    (05 §10 picks one; admitting both is a superset of 05's derivation): the recursors' clause
    restricts Prop families to PropOnly by the separate premise `PropElimOnlyA` (M2-f (0)
    Decision (2)), never by the judgment. -/
inductive RecElimA : Type
  | anySort
  | propOnly

def RecElimA.extra : RecElimA → Nat
  | .anySort => 1
  | .propOnly => 0

def RecElimA.motiveLevel (a : Nat) : RecElimA → Level
  | .anySort => .param a
  | .propOnly => .zero

/-- a group constructor's minor data: reference, fields, result indices. -/
def GroupCtorA.minorData {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) : MinorDataA :=
  (c.ref, c.view.fields, c.view.res)

/-- the recursor type a group derives under a policy: built from the family view and the
    constructors in candidate order (the group list's head is added last, so candidate order is
    the list reversed), at the family's canonical levels. -/
def groupRecTypeA {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    (fv : FamViewA fm) (cs : List (GroupCtorA I E f fm fv)) (elim : RecElimA) : ExprA :=
  recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort (elim.motiveLevel fm.arity)
    (cs.reverse.map GroupCtorA.minorData)

/-- a group's recursor (05 §11–§13): the member, its checks at the DerivationScope (the base, the
    family and the constructors, 05 §4), the elimination policy, and the stored type BUILT from the
    views. The parameter count is the family's; the member's own is `0`. -/
structure GroupRecA (I : IotaIfaceA) (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA)
    (fv : FamViewA fm) (cs : List (GroupCtorA I E f fm fv)) : Type where
  member : CheckedMemberA
  hcls : member.mclass = .recursorM
  hnobody : member.bodyA = none
  hnp : member.nparamsA = 0
  elim : RecElimA
  harity : member.arity = fm.arity + elim.extra
  stored : member.mtypeA = groupRecTypeA fv cs elim
  hclT : ∀ k, liftA k 1 member.mtypeA = member.mtypeA
  u : Level
  hT : HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I member.arity [] member.mtypeA (.sort u)
  hlvl : exprLevelsBoundedA member.arity member.mtypeA = true

/-- the environment after a group with its recursor: the group's, then the recursor at
    `f + 1 + k` (05 §3: member `k + 1` of the group). -/
def groupRecEnvA {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (cs : List (GroupCtorA I E f fm fv)) (rec : GroupRecA I E f fm fv cs) : ResolvedEnvA :=
  extendEnvA (groupEnvA E f fm (cs.map GroupCtorA.entry)) (f + 1 + cs.length) rec.member

#print axioms minorFieldsA_snd
#print axioms recDomsA_length
#print axioms piCountA_piTelA
#print axioms piCountA_foldAppsA_of_not_pi
#print axioms piCountA_recTypeA
#print axioms piBodyA_recTypeA
#print axioms appsSpineA_recBodyA
#print axioms piDomsA_recTypeA_getLast
#print axioms appsSpineA_majorDom
#print axioms piBodyA_motTyA
#print axioms piDomsA_recTypeA_motive
#print axioms instantiateLevelsA_recBodyA
#print axioms instantiateLevelsA_recTypeA
#print axioms unitGroupA_of_recTypeA

end Rcic.Declarative.Ann
