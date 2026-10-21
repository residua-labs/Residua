import rcic.RcicAnnTel
import rcic.RcicIotaShapeAdapter

/-!
# R-NoFunRec S6 segment 2: the FUN-RECURSIVE field fragment — rigidity for `.recursive (n+1)`

The adapter's `DirectFieldFrag` (`RcicIotaShapeAdapter.lean:121`) is the per-field rigidity
under which the semantic analyser (`fieldAnalyze`) agrees with the syntactic one
(`analyzeField`). Its `noInner` clause (:140) EXCLUDES function-recursive fields by design:
a Π-telescope whose tail is the canonical family application is exactly `.recursive inner`
with `inner > 0` — the frec shape. So the DIRECT certificates (`EnvCorrEraseCert`,
`EnvCorrAnnCert`) cannot carry a frec field, and the union erase direction's frec arm
(S6 segment 3, `RcicAnnIotaCorrUA.lean`) needs the sibling fragment defined here:

* `FunRecFrag` — `DirectFieldFrag`'s shape with `noInner` replaced by `canonTail` (the
  Π-tail IS the canonical family app) and `innerClean` (the inner binders are family-free);
* `fieldAnalyze_of_funRecFrag` — the semantic read at such a field is
  `.permitted (.recursive (piCount T)) (familyIdx nparams (piTailOf T))`;
* `piTelE_piDomsOf` / `funRecArg_eq_recCallFunS` — the schema agreement at one frec field:
  the fuel-bounded `funRecArg` (what `IotaWitnessS.hschema`'s `iotaOpenRhs` builds) IS the
  syntactic `recCallFunS` (what the copy's ι walk `rhsArgsS` builds) — 05 §14's
  `fun ys => rec … (f ys)` both ways.

Plan: `research/rcic/nofunrec/S6_PLAN.md` §3 A2a. `closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ## the Π-telescope bridge: the adapter's `piDomsOf`/`piTailOf` are `piTelE`'s pair -/

/-- `piTelE` (`RcicAnnTel.lean:36`) and `piDomsOf`/`piTailOf`
    (`RcicIotaShapeAdapter.lean:93/:98`) are the same structural Π-decomposition. -/
theorem piTelE_piDomsOf : ∀ T : Expr Nat,
    piTelE T = (piDomsOf T, piTailOf T)
  | .pi A B => by
      have ih := piTelE_piDomsOf B
      simp only [piTelE, ih, piDomsOf, piTailOf]
  | .bvar _ | .sort _ | .lit _ | .const _ _ | .app _ _ | .lam _ _ | .letE _ _ _ => rfl

/-! ## the fragment -/

/-- The FUN-RECURSIVE field fragment: `DirectFieldFrag`'s sibling at `.recursive (n+1)`.
    `depth` is the field's position in the constructor telescope, as threaded by
    `fieldShapesFuel` starting at `nparams`. The differences from `DirectFieldFrag`:
    `canonTail` asserts the Π-tail IS the canonical family application (what
    `DirectFieldFrag.noInner` forbids), and `innerClean` replaces the whole-field legacy
    scan — the inner binders are family-free, made honest by `rigid` (δ cannot surface
    the family). -/
structure FunRecFrag (E : ResolvedEnv)
    (fuel fam nuniv nparams nindices depth : Nat) (T : Expr Nat) : Prop where
  /-- δ never fires inside `T`. -/
  rigid : noTransparentB E T = true
  /-- `T`'s Π-tail is whnf-stable, so `piTelescopeFuel` returns the
      syntactic decomposition `piDomsOf`/`piTailOf`. -/
  stableTail : headStableB (piTailOf T) = true
  /-- fuel covers the telescope descent, the domain scan, the index scan,
      and the whole-field occurrence scan (each burns one unit up front). -/
  fuelBound : esize T + piCount T + 3 ≤ fuel
  /-- the Π-tail is the canonical family application — the shape analyser's
      positive clause, at the frec position (`top = piCount T + depth - 1`
      as in `fieldAnalyze`, since `doms.length = piCount T`). -/
  canonTail : properShapeB fam nuniv nparams nindices (piCount T + depth - 1)
      (piTailOf T) = true
  /-- the inner binders are family-free (the any-form of
      `.all fun D => !occursConst fam D`). -/
  innerClean : (piDomsOf T).any (fun D => occursConst fam D) = false

/-! ## the semantic read at a frec field -/

/-- `fieldAnalyze_of_directFrag`'s frec sibling: on a `FunRecFrag` field the semantic
    analyser permits the field at its structural shape — `.recursive (piCount T)` at the
    tail's indices. At `piCount T ≥ 1` this is the function-recursive shape
    (`FieldShape.kind? = none` there); at `piCount T = 0` it degenerates to the direct
    fragment's positive clause. -/
theorem fieldAnalyze_of_funRecFrag {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (h : FunRecFrag E fuel fam nuniv nparams nindices depth T) :
    fieldAnalyze E fuel fam nuniv nparams nindices depth T =
      .permitted (.recursive (piCount T)) (familyIdx nparams (piTailOf T)) := by
  obtain ⟨hrigid, hstable, hfuelB, hcanon, hclean⟩ := h
  cases fuel with
  | zero => exact absurd hfuelB (by omega)
  | succ f' =>
      have hpi := piTelescopeFuel_of_tailStable (E := E) (T := T) (fuel := f')
        (noTransparentB_piTail T hrigid) hstable (by
          have := piDomsOf_length T
          omega)
      have hdoms := domainsContainFuel_of_noTransparent (E := E)
        (fam := fam) (fuel := f') (piDomsOf T)
        (fun D hD => noTransparentB_piDom T D hrigid hD)
        (fun D hD => by
          have h1 := esize_piDom_le T D hD
          have h2 := piDomsOf_length T
          have := hfuelB
          have := esize_pos T
          omega)
      have hpf := properFamilyFuel_of_noTransparent (E := E) (fam := fam)
        (nuniv := nuniv) (nindices := nindices)
        (top := (piDomsOf T).length + depth - 1)
        (fuel := f') (body := piTailOf T)
        (noTransparentB_piTail T hrigid)
        (fun x hx => by
          have hfold : piTailOf T = foldApps (appsSpine (piTailOf T)).1
              (appsSpine (piTailOf T)).2 :=
            (foldApps_appsSpine _).symm
          have hsz := esize_mem_drop_spine_le
            (f := (appsSpine (piTailOf T)).1)
            (args := (appsSpine (piTailOf T)).2) (n := nparams) hx
          rw [← hfold] at hsz
          have hle := esize_piTail_le T
          have := hfuelB
          omega)
      simp only [fieldAnalyze]
      rw [hpi]
      dsimp only
      rw [hdoms, hclean]
      dsimp only
      rw [hpf]
      simp only [piDomsOf_length]
      rw [hcanon]

/-! ## the schema agreement at one frec field -/

/-- `recPrefix` (a `List.take`) commutes with a pointwise lift. -/
theorem recPrefix_map_lift (preMajor : List (Expr Nat)) (nparams nMinors m : Nat) :
    (recPrefix preMajor nparams nMinors).map (lift 0 m) =
      recPrefix (preMajor.map (lift 0 m)) nparams nMinors := by
  simp only [recPrefix, List.map_take]

/-- The frec field's schema agreement: the fuel-bounded `funRecArg` (what `IotaWitnessS`'s
    `iotaOpenRhs` builds through `iotaArgs`' `.recursive inner` arm) IS the syntactic
    `recCallFunS` (what the copy's ι walk `rhsArgsS` builds) at a `FunRecFrag` field —
    05 §14's `fun ys => rec … (f ys)` both ways, at the structural inner arity. -/
theorem funRecArg_eq_recCallFunS {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {A : Expr Nat}
    (h : FunRecFrag E fuel fam nuniv nparams nindices depth A)
    {rec : Expr Nat} {preMajor : List (Expr Nat)} {nMinors : Nat} {f : Expr Nat} :
    funRecArg E fuel rec preMajor nparams nMinors f A (piCount A) =
      some (Ann.recCallFunS rec preMajor nparams nMinors f A) := by
  obtain ⟨hrigid, hstable, hfuelB, _, _⟩ := h
  have hpi := piTelescopeFuel_of_tailStable (E := E) (T := A) (fuel := fuel)
    (noTransparentB_piTail A hrigid) hstable (by omega)
  have hlen := piDomsOf_length A
  have htel := piTelE_piDomsOf A
  simp only [funRecArg, hpi]
  rw [if_pos hlen]
  simp only [Ann.recCallFunS, htel, hlen, recCallField, recPrefix_map_lift]

/-! ## segment 3a: the shape bridge — fired syntactic read = semantic analysis, per field -/

/-- inversion of the fired read at `.nonrecursive`: the family does not occur. -/
theorem occursConst_false_of_fieldShapeE_nonrec {fam : Nat} {T : Expr Nat}
    (hs : fieldShapeE fam T = some FieldShape.nonrecursive) :
    occursConst fam T = false := by
  unfold fieldShapeE at hs
  split at hs
  · rename_i hcond
    cases hoc : occursConst fam T <;> simp_all
  · split at hs
    · simp at hs
    · simp at hs

/-- inversion of the fired read at `.recursive inner`: the inner arity, the clean inner
    binders with a family-app tail, and the family's occurrence. -/
theorem fieldShapeE_recursive_inv {fam : Nat} {T : Expr Nat} {inner : Nat}
    (hs : fieldShapeE fam T = some (.recursive inner)) :
    (piTelE T).1.length = inner ∧
      ((piTelE T).1.all (fun D => !(occursConst fam D)) &&
        isFamilyApp fam (piTelE T).2) = true ∧ occursConst fam T = true := by
  unfold fieldShapeE at hs
  split at hs
  · simp at hs
  · rename_i hocc
    have hoccT : occursConst fam T = true := by
      cases hb : occursConst fam T <;> simp_all
    split at hs
    · rename_i hcond
      injection hs with hlen
      injection hlen with hlen
      exact ⟨hlen, hcond, hoccT⟩
    · simp at hs

/-- the fragment a fired field needs, keyed by its FIRED shape: DIRECT at plain/direct,
    FUN-RECURSIVE at `.recursive (n+1)`. At a `none` shape the copy's ι refuses the field,
    so nothing is demanded. -/
def FieldFrag (E : ResolvedEnv) (fuel fam nuniv nparams nindices depth : Nat)
    (T : Expr Nat) : Prop :=
  match fieldShapeE fam T with
  | some .nonrecursive => DirectFieldFrag E fuel fam nuniv nparams nindices depth T
  | some (.recursive 0) => DirectFieldFrag E fuel fam nuniv nparams nindices depth T
  | some (.recursive (_ + 1)) => FunRecFrag E fuel fam nuniv nparams nindices depth T
  | none => True

/-- the fired shape's inner arity IS the structural Π-count (telescope bridge). -/
theorem piCount_eq_of_fieldShapeE_recursive {fam : Nat} {T : Expr Nat} {inner : Nat}
    (hs : fieldShapeE fam T = some (.recursive inner)) : piCount T = inner := by
  have h1 := (fieldShapeE_recursive_inv hs).1
  have hbridge := piTelE_piDomsOf T
  have hlen := piDomsOf_length T
  rw [hbridge, hlen] at h1
  exact h1

/-- pointwise: at a `FieldFrag` field the semantic analyser permits the field AT THE FIRED
    SYNTACTIC SHAPE — the per-field agreement the frec arm of the union erase direction
    needs (the adapter's `fieldAnalyze_of_directFrag` covers the first two shapes through
    the legacy kind; `fieldAnalyze_of_funRecFrag` covers the third). -/
theorem fieldAnalyze_of_fieldFrag {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (h : FieldFrag E fuel fam nuniv nparams nindices depth T) {s : FieldShape}
    (hs : fieldShapeE fam T = some s) :
    ∃ idx, fieldAnalyze E fuel fam nuniv nparams nindices depth T = .permitted s idx := by
  unfold FieldFrag at h
  rw [hs] at h
  cases s with
  | nonrecursive =>
      dsimp only at h
      have hoc := occursConst_false_of_fieldShapeE_nonrec hs
      have haf : analyzeField fam T = some RecKind.plain := by
        simp only [analyzeField, hoc, Bool.not_false, if_true]
      obtain ⟨h1, _⟩ := fieldAnalyze_of_directFrag h
      have h2 := h1 _ haf
      simp only [shapeOfKind] at h2
      exact ⟨_, h2⟩
  | recursive n =>
      obtain ⟨hlen, hcond, hocc⟩ := fieldShapeE_recursive_inv hs
      have hcond' : ((piTelE T).1.all (fun D => !(occursConst fam D)) = true ∧
          isFamilyApp fam (piTelE T).2 = true) := by
        rw [← Bool.and_eq_true]; exact hcond
      have hpc := piCount_eq_of_fieldShapeE_recursive hs
      cases n with
      | zero =>
          dsimp only at h
          have hfa' : isFamilyApp fam (piTailOf T) = true := by
            have hbridge := piTelE_piDomsOf T
            rw [hbridge] at hcond'
            dsimp only at hcond'
            exact hcond'.2
          rw [piTailOf_eq_self_of_piCount_zero hpc] at hfa'
          have haf : analyzeField fam T = some RecKind.directRec := by
            simp only [analyzeField]
            rw [if_neg (by rw [hocc]; simp), if_pos hfa']
          obtain ⟨h1, _⟩ := fieldAnalyze_of_directFrag h
          have h2 := h1 _ haf
          simp only [shapeOfKind] at h2
          exact ⟨_, h2⟩
      | succ n =>
          dsimp only at h
          have h2 := fieldAnalyze_of_funRecFrag h
          have hpcn : piCount T = n + 1 := by omega
          rw [hpcn] at h2
          exact ⟨_, h2⟩

/-- the per-field fragment list over a constructor's erased post-parameter domains,
    threading the field position as `fieldShapesFuel` does. -/
def FieldFragList (E : ResolvedEnv) (fuel fam nuniv nparams nindices : Nat) :
    Nat → List (Expr Nat) → Prop
  | _, [] => True
  | depth, T :: Ts => FieldFrag E fuel fam nuniv nparams nindices depth T ∧
      FieldFragList E fuel fam nuniv nparams nindices (depth + 1) Ts

/-- the fold: on a fragment-clean domain list whose fired read RESOLVES, the semantic
    shape list IS the fired one — `IotaWitnessS.hshapes` at the fired shapes. -/
theorem fieldShapesFuel_eq_fieldShapesE {E : ResolvedEnv}
    {fuel fam nuniv nparams nindices : Nat} :
    ∀ (doms : List (Expr Nat)) (depth : Nat),
      FieldFragList E fuel fam nuniv nparams nindices depth doms →
      ∀ shapes, fieldShapesE fam doms = some shapes →
        fieldShapesFuel E fuel fam nuniv nparams nindices depth doms = some shapes := by
  intro doms depth
  induction doms generalizing depth with
  | nil => intro _ shapes hs; exact hs
  | cons T Ts ih =>
      intro ⟨hT, hTs⟩ shapes hs
      cases hsT : fieldShapeE fam T with
      | none => simp only [fieldShapesE, hsT] at hs; exact Option.noConfusion hs
      | some s =>
          cases hsRest : fieldShapesE fam Ts with
          | none => simp only [fieldShapesE, hsT, hsRest] at hs; exact Option.noConfusion hs
          | some ss =>
              simp only [fieldShapesE, hsT, hsRest] at hs
              injection hs with hsShapes
              subst hsShapes
              obtain ⟨idx, hfa⟩ := fieldAnalyze_of_fieldFrag hT hsT
              simp only [fieldShapesFuel, hfa]
              have hrest := ih (depth + 1) hTs ss hsRest
              rw [hrest]
              rfl

#print axioms Rcic.Declarative.fieldAnalyze_of_fieldFrag
#print axioms Rcic.Declarative.fieldShapesFuel_eq_fieldShapesE

end Rcic.Declarative
