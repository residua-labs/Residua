import rcic.RcicAnnStep
import rcic.RcicLevelCalc
import rcic.RcicIndGroupJudgment

/-!
# Telescope algebra on the copy (M2-f (2), split out for M2-f (3))

The Π-telescope operations 05 §11–14's ι and the `fam` clause read: the leading
domains and the body (`piDomsA` / `piBodyA`, main's `peelPis` through erasure),
application along a telescope (`applyTelA`, main's `applyTel`; defined in `RcicAnnStep`, whose struct
arm reads it, W-1 (a)), the family's
index arguments (`familyIdxA`), the recursor prefix and the 05 §14 recursive calls
(`recPrefixA`, `recCallFieldA`, the λ-wrapped `recCallFunA` at a function-recursive field,
`recCallsA`), the type-directed ι right-hand side (`rhsArgsA`; main's `rhsArgs` on admitted input
where every field has a kind), the guard at a recursive field (`spineHeadConstA`, `shapeGuardA`)
and the field walk (`fieldsTelA`), the field kinds THROUGH ERASURE (`ctorKindsA`, main's
`analyzeFields`), the field shapes THROUGH ERASURE (`ctorShapesA`, admission's `FieldShape` read on
the syntax, which the relation and ι read; section (0), R-NoFunRec-1 step 1 (1c-γ)), and the head
reference of a spine (`spineHeadRefA`). Section (3)
is the erasure correspondence with `RcicDeclarative`. Placed below the relation
(`RcicAnnLR`) so that the `fam` clause can read it; `RcicAnnIota` builds the
concrete ι on it.
-/

namespace Rcic.Declarative

/-! ## (0) the field shapes, read on the syntax (R-NoFunRec-1 step 1 (1b))

Admission's `FieldShape` (`RcicIndGroupJudgment`) read syntactically: a field is `nonrecursive` when
the family does not occur in it, and `recursive k` when it is a Π-telescope of `k` family-free domains
ending in a family application with family-free arguments. `main`'s ι reads `analyzeField`: the same
reading at `recursive 0`, and no kind at `recursive (k+1)` (`analyzeField_eq_shape`). -/

/-- the leading Π-domains and the body, read on the syntax. -/
def piTelE : Expr Nat → List (Expr Nat) × Expr Nat
  | .pi A B => (A :: (piTelE B).1, (piTelE B).2)
  | e => ([], e)

/-- a field's shape, read on the syntax. -/
def fieldShapeE (fam : Nat) (T : Expr Nat) : Option FieldShape :=
  if !(occursConst fam T) then some .nonrecursive
  else if (piTelE T).1.all (fun D => !(occursConst fam D)) && isFamilyApp fam (piTelE T).2 then
    some (.recursive (piTelE T).1.length)
  else none

def fieldShapesE (fam : Nat) : List (Expr Nat) → Option (List FieldShape)
  | [] => some []
  | T :: Ts =>
      match fieldShapeE fam T, fieldShapesE fam Ts with
      | some s, some ss => some (s :: ss)
      | _, _ => none

/-- the kind `main`'s ι reads at a shape: none at a function-recursive one. -/
def FieldShape.kind? : FieldShape → Option RecKind
  | .nonrecursive => some .plain
  | .recursive 0 => some .directRec
  | .recursive (_ + 1) => none

/-- the three readings of a shape — non-recursive, directly recursive, function-recursive — as an
    eliminator whose cases are named for them. -/
@[elab_as_elim]
def FieldShape.cases3 {motive : FieldShape → Sort _} (s : FieldShape) (plain : motive .nonrecursive)
    (directRec : motive (.recursive 0)) (funRec : (k : Nat) → motive (.recursive (k + 1))) : motive s :=
  match s with
  | .nonrecursive => plain
  | .recursive 0 => directRec
  | .recursive (k + 1) => funRec k

/-- the kinds of a list of shapes, when each has one. -/
def shapesKinds : List FieldShape → Option (List RecKind)
  | [] => some []
  | s :: ss =>
      match s.kind?, shapesKinds ss with
      | some k, some ks => some (k :: ks)
      | _, _ => none

/-- the shape of a kind. -/
def RecKind.shape : RecKind → FieldShape
  | .plain => .nonrecursive
  | .directRec => .recursive 0

theorem fieldShapeE_flat {fam : Nat} {T : Expr Nat} (hpt : piTelE T = ([], T))
    (hoc : occursConst fam T = true) :
    fieldShapeE fam T = if isFamilyApp fam T then some (.recursive 0) else none := by
  unfold fieldShapeE
  rw [hoc, hpt]
  rfl

theorem ite_bind_kind (b : Bool) :
    (if b = true then some RecKind.directRec else none) =
      (if b = true then some (FieldShape.recursive 0) else none).bind FieldShape.kind? := by
  cases b <;> rfl

theorem analyzeField_flat {fam : Nat} {T : Expr Nat} (hpt : piTelE T = ([], T)) :
    analyzeField fam T = (fieldShapeE fam T).bind FieldShape.kind? := by
  cases hoc : occursConst fam T with
  | false =>
      unfold analyzeField fieldShapeE
      rw [hoc]
      rfl
  | true =>
      rw [fieldShapeE_flat hpt hoc]
      unfold analyzeField
      rw [hoc]
      show (if isFamilyApp fam T = true then some RecKind.directRec else none) = _
      exact ite_bind_kind (isFamilyApp fam T)

/-- `main`'s analysis is the kind of the shape. -/
theorem analyzeField_eq_shape (fam : Nat) (T : Expr Nat) :
    analyzeField fam T = (fieldShapeE fam T).bind FieldShape.kind? := by
  cases T with
  | pi A B =>
      cases hoc : occursConst fam (.pi A B) with
      | false =>
          unfold analyzeField fieldShapeE
          rw [hoc]
          rfl
      | true =>
          unfold analyzeField fieldShapeE
          have hf : isFamilyApp fam (.pi A B) = false := rfl
          simp only [hoc, hf, piTelE, List.length_cons, Bool.not_true, Bool.false_eq_true, ite_false]
          split <;> rfl
  | _ => exact analyzeField_flat rfl

theorem analyzeFields_eq_shapes (fam : Nat) : (Ts : List (Expr Nat)) →
    analyzeFields fam Ts = (fieldShapesE fam Ts).bind shapesKinds
  | [] => rfl
  | T :: Ts => by
      simp only [analyzeFields, fieldShapesE, analyzeField_eq_shape, analyzeFields_eq_shapes fam Ts]
      cases fieldShapeE fam T with
      | none => rfl
      | some s =>
          cases fieldShapesE fam Ts with
          | none =>
              show (match s.kind?, (none : Option (List RecKind)) with
                | some k, some ks => some (k :: ks) | _, _ => none) = none
              cases s.kind? <;> rfl
          | some ss => rfl

/-- a list of shapes with kinds is those kinds' shapes. -/
theorem shapesKinds_eq_map : {ss : List FieldShape} → {ks : List RecKind} → shapesKinds ss = some ks →
    ss = ks.map RecKind.shape
  | [], ks, h => by
      cases h
      rfl
  | s :: ss, ks, h => by
      simp only [shapesKinds] at h
      cases hs : s.kind? with
      | none => rw [hs] at h; exact Option.noConfusion h
      | some k =>
          cases hss : shapesKinds ss with
          | none => rw [hs, hss] at h; exact Option.noConfusion h
          | some ks' =>
              rw [hs, hss] at h
              cases h
              have e : s = k.shape := by
                cases s with
                | nonrecursive => cases hs; rfl
                | recursive i =>
                    cases i with
                    | zero => cases hs; rfl
                    | succ i => exact Option.noConfusion hs
              rw [List.map_cons, e, shapesKinds_eq_map hss]

end Rcic.Declarative

namespace Rcic.Declarative.Ann

open Rcic.Declarative

deriving instance DecidableEq for RecKind

/-! ## (1) telescope algebra on the copy -/

/-- the leading Π-domains of an annotated type. -/
def piDomsA : ExprA → List ExprA
  | .pi A _ B _ => A :: piDomsA B
  | _ => []

/-- the step's major-domain reader is the last leading Π-domain (O1-a). -/
theorem lastPiDomA_eq : (T : ExprA) → lastPiDomA T = (piDomsA T).getLast?
  | .pi A _ B _ => by
      show (match lastPiDomA B with | some D => some D | none => some A) = (A :: piDomsA B).getLast?
      rw [lastPiDomA_eq B]
      cases h : piDomsA B with
      | nil => rfl
      | cons D Ds =>
          rw [List.getLast?_cons_cons]
          cases h2 : (D :: Ds).getLast? with
          | none => simp at h2
          | some x => rfl
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the body under all leading Π-binders. -/
def piBodyA : ExprA → ExprA
  | .pi _ _ B _ => piBodyA B
  | e => e

/-- the index arguments of a family application `I params idx` (main's `familyIdx`). -/
def familyIdxA (nparams : Nat) (A : ExprA) : List ExprA := (appsSpineA A).2.drop nparams

/-- the recursor prefix: parameters, motive, minors (main's `recPrefix`). -/
def recPrefixA (preMajor : List ExprA) (nparams nMinors : Nat) : List ExprA :=
  preMajor.take (nparams + 1 + nMinors)

/-- 05 §14 direct recursive call: `rec params motive minors field_indices field`. -/
def recCallFieldA (rec : ExprA) (preMajor : List ExprA) (nparams nMinors : Nat) (f A : ExprA) :
    ExprA :=
  foldAppsA rec (recPrefixA preMajor nparams nMinors ++ familyIdxA nparams A ++ [f])

/-- 05 §14 function-recursive call (R-NoFunRec-1 step 1 (1c-γ)): admission's λ-wrapper (`funRecArg`) on
    the copy's syntax. The field's inner binders are read off its domain. Under them comes the direct
    call at the domain's body, with the field applied to the inner variables and the prefix lifted
    past them. -/
def recCallFunA (rec : ExprA) (preMajor : List ExprA) (nparams nMinors : Nat) (f A : ExprA) : ExprA :=
  lamTelA (piDomListA A)
    (recCallFieldA rec (preMajor.map (liftA 0 (piDomListA A).length)) nparams nMinors
      (foldAppsA (liftA 0 (piDomListA A).length f)
        ((List.range (piDomListA A).length).reverse.map ExprA.bvar)) (piBodyA A))

/-- what follows a field in the ι right-hand side, by its shape: the recursor call at a directly
    recursive field (05 §14), the λ-wrapped call at a function-recursive one, nothing at a
    non-recursive one. -/
def recCallsA (rec : ExprA) (preMajor : List ExprA) (nparams nMinors : Nat) (f A : ExprA) :
    FieldShape → List ExprA
  | .nonrecursive => []
  | .recursive 0 => [recCallFieldA rec preMajor nparams nMinors f A]
  | .recursive (_ + 1) => [recCallFunA rec preMajor nparams nMinors f A]

/-- type-directed ι right-hand-side arguments (main's `rhsArgs` on admitted input where every field
    has a kind): `T` is the remaining constructor telescope after the parameters and the fields
    already applied; each field is followed by its `recCallsA`. Total: `[]` off the
    shape `fieldsTelA` admits. -/
def rhsArgsA (rec : ExprA) (preMajor : List ExprA) (nparams nMinors : Nat) :
    List ExprA → List FieldShape → ExprA → List ExprA
  | f :: fs, k :: ks, .pi A _ B _ =>
      f :: (recCallsA rec preMajor nparams nMinors f A k ++
        rhsArgsA rec preMajor nparams nMinors fs ks (instantiate0A f B))
  | _, _, _ => []

/-- the spine head is a constant (05 family application `I params idx`). -/
def spineHeadConstA (e : ExprA) : Bool :=
  match (appsSpineA e).1 with
  | .const _ _ => true
  | _ => false

/-- the guard at a field, by its shape: a directly recursive domain must be constant-headed (05 §8;
    main's `directRecConstHead`), a function-recursive one a Π-telescope of exactly its inner binders
    over a constant-headed body. There `familyIdxA` commutes with substitution. -/
def shapeGuardA (A : ExprA) : FieldShape → Bool
  | .nonrecursive => true
  | .recursive 0 => spineHeadConstA A
  | .recursive (k + 1) => (piDomListA A).length == k + 1 && spineHeadConstA (piBodyA A)

/-- the fields walk the constructor telescope: a Π at every field, the guard at
    each, exactly as many shapes as fields. -/
def fieldsTelA : List ExprA → List FieldShape → ExprA → Bool
  | [], [], _ => true
  | f :: fs, k :: ks, .pi A _ B _ => shapeGuardA A k && fieldsTelA fs ks (instantiate0A f B)
  | _, _, _ => false

/-! ### (2′) the field walk's TREE-SIDE shadow

`shapeGuardA`/`fieldsTelA`/`recCallsA`/`recCallFunA`/`rhsArgsA` read annotated syntax, but their
erasures are functions of the erased data alone: `piTelE` is `piDomListA`/`piBodyA` through
`erase`, `spineHeadConst` is `spineHeadConstA`, `lamTelescope` is `lamTelA`, `instantiate0` is
`instantiate0A`, `lift` is `liftA`.  The `S`-suffixed definitions are exactly those erasures —
the annotation-direction correspondence (`iotaFnA_of_witnessS`, `RcicAnnIotaCorr`) compares
`iotaRhsOfS`'s schema instance against `rhsArgsS` tree-side, where equality on `Expr Nat` is
decidable, so the recognizer CHECKS agreement rather than assuming it. -/

/-- the tree-side `shapeGuardA`: the same three-way shape case split, on erased syntax. -/
def shapeGuardS (A : Expr Nat) : FieldShape → Bool
  | .nonrecursive => true
  | .recursive 0 => spineHeadConst A
  | .recursive (k + 1) => (piTelE A).1.length == k + 1 && spineHeadConst (piTelE A).2

/-- the tree-side `fieldsTelA`. -/
def fieldsTelS : List (Expr Nat) → List FieldShape → Expr Nat → Bool
  | [], [], _ => true
  | f :: fs, k :: ks, .pi A B => shapeGuardS A k && fieldsTelS fs ks (instantiate0 f B)
  | _, _, _ => false

/-- the tree-side `recCallFunA`: the λ-wrapped call at a function-recursive field
    (R-NoFunRec-1 step 1 (1c-γ)), on erased syntax — `lamTelescope` over `piTelE`'s domains. -/
def recCallFunS (rec : Expr Nat) (preMajor : List (Expr Nat)) (nparams nMinors : Nat)
    (f A : Expr Nat) : Expr Nat :=
  lamTelescope (piTelE A).1
    (recCallField rec (preMajor.map (lift 0 (piTelE A).1.length)) nparams nMinors
      (foldApps (lift 0 (piTelE A).1.length f)
        ((List.range (piTelE A).1.length).reverse.map Expr.bvar)) (piTelE A).2)

/-- the tree-side `recCallsA`. -/
def recCallsS (rec : Expr Nat) (preMajor : List (Expr Nat)) (nparams nMinors : Nat)
    (f A : Expr Nat) : FieldShape → List (Expr Nat)
  | .nonrecursive => []
  | .recursive 0 => [recCallField rec preMajor nparams nMinors f A]
  | .recursive (_ + 1) => [recCallFunS rec preMajor nparams nMinors f A]

/-- the tree-side `rhsArgsA`: the ι right-hand-side argument walk on erased syntax. -/
def rhsArgsS (rec : Expr Nat) (preMajor : List (Expr Nat)) (nparams nMinors : Nat) :
    List (Expr Nat) → List FieldShape → Expr Nat → List (Expr Nat)
  | f :: fs, k :: ks, .pi A B =>
      f :: (recCallsS rec preMajor nparams nMinors f A k ++
        rhsArgsS rec preMajor nparams nMinors fs ks (instantiate0 f B))
  | _, _, _ => []

/-- the field kinds of a constructor, THROUGH ERASURE: main's `analyzeFields` (05
    §8–12 `AnalyzeField`) on the erased Π-domains after the parameters. -/
def ctorKindsA (fam nparams : Nat) (T : ExprA) : Option (List RecKind) :=
  analyzeFields fam (((piDomsA T).drop nparams).map erase)

/-- the field shapes of a constructor, THROUGH ERASURE (R-NoFunRec-1 step 1 (1b)): admission's
    `FieldShape` read on the erased Π-domains after the parameters — what the relation reads. -/
def ctorShapesA (fam nparams : Nat) (T : ExprA) : Option (List FieldShape) :=
  fieldShapesE fam (((piDomsA T).drop nparams).map erase)

/-- the head constant's reference, if the spine is constant-headed. -/
def spineHeadRefA (e : ExprA) : Option Nat :=
  match (appsSpineA e).1 with
  | .const c _ => some c
  | _ => none

/-- every constructor member's `normA`, when it carries one, is `const`-headed at its `piBody`
    (R-NoDeltaRec-4d-iii): the read-back's rigidity reads the normed type's shape. -/
def EnvNormCtorTypeA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .constructorM →
    ∀ T, m.normA = some T → ∃ f ls, (appsSpineA (piBodyA T)).1 = .const f ls

/-! ## (2) inversions -/

theorem spineHeadConstA_true {A : ExprA} (h : spineHeadConstA A = true) :
    ∃ r ls, (appsSpineA A).1 = .const r ls := by
  unfold spineHeadConstA at h
  split at h
  · rename_i r ls hr
    exact ⟨r, ls, hr⟩
  · exact Bool.noConfusion h

theorem spineHeadConstA_of_const {A : ExprA} {r : Nat} {ls : List Level}
    (h : (appsSpineA A).1 = .const r ls) : spineHeadConstA A = true := by
  unfold spineHeadConstA
  rw [h]

/-- a constant-headed spine is no Π. -/
theorem piBodyA_of_const {e : ExprA} {r : Nat} {ls : List Level} (h : (appsSpineA e).1 = .const r ls) :
    piBodyA e = e ∧ piDomListA e = [] := by
  cases e with
  | pi _ _ _ _ => exact absurd h (by simp [appsSpineA])
  | bvar _ => exact absurd h (by simp [appsSpineA])
  | sort _ => exact absurd h (by simp [appsSpineA])
  | lam _ _ _ => exact absurd h (by simp [appsSpineA])
  | letE _ _ _ => exact absurd h (by simp [appsSpineA])
  | lit _ => exact absurd h (by simp [appsSpineA])
  | const _ _ => exact ⟨rfl, rfl⟩
  | app _ _ => exact ⟨rfl, rfl⟩

theorem spineHeadRefA_some {e : ExprA} {c : Nat} (h : spineHeadRefA e = some c) :
    ∃ ls, (appsSpineA e).1 = .const c ls := by
  unfold spineHeadRefA at h
  split at h
  · rename_i c' ls hc
    injection h with h
    subst h
    exact ⟨ls, hc⟩
  · exact Option.noConfusion h

theorem spineHeadRefA_of_const {e : ExprA} {c : Nat} {ls : List Level}
    (h : (appsSpineA e).1 = .const c ls) : spineHeadRefA e = some c := by
  unfold spineHeadRefA
  rw [h]

theorem fieldsTelA_cons {f : ExprA} {fs : List ExprA} {k : FieldShape} {ks : List FieldShape}
    {T : ExprA} (h : fieldsTelA (f :: fs) (k :: ks) T = true) :
    ∃ A u B v, T = .pi A u B v ∧ shapeGuardA A k = true ∧
      fieldsTelA fs ks (instantiate0A f B) = true := by
  cases T with
  | pi A u B v => exact ⟨A, u, B, v, rfl, boolAnd_left h, boolAnd_right h⟩
  | bvar _ => exact Bool.noConfusion h
  | sort _ => exact Bool.noConfusion h
  | const _ _ => exact Bool.noConfusion h
  | app _ _ => exact Bool.noConfusion h
  | lam _ _ _ => exact Bool.noConfusion h
  | letE _ _ _ => exact Bool.noConfusion h
  | lit _ => exact Bool.noConfusion h

/-! ## (3) erasure: the telescope algebra is main's, through `erase`

Each operation on the copy erases to the tree's (`RcicDeclarative`): `appsSpineA` to
`appsSpine`, `foldAppsA` to `foldApps`, `applyTelA` to `applyTel`, `piDomsA` /
`piBodyA` to `peelPis` at the Π-count, `familyIdxA` / `recPrefixA` /
`recCallFieldA` to theirs, and `rhsArgsA` to `rhsArgs` on the shape `fieldsTelA`
admits. `ctorKindsA` is main's `analyzeFields` on the erased domains by definition. -/

theorem appsSpineA_erase : (e : ExprA) →
    appsSpine (erase e) = (erase (appsSpineA e).1, (appsSpineA e).2.map erase)
  | .app f x => by
      show appsSpine (.app (erase f) (erase x)) = _
      simp only [appsSpine, appsSpineA, appsSpineA_erase f, List.map_append, List.map_cons,
        List.map_nil]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem foldAppsA_erase (f : ExprA) : (xs : List ExprA) →
    erase (foldAppsA f xs) = foldApps (erase f) (xs.map erase)
  | [] => rfl
  | x :: xs => by
      show erase (foldAppsA (.app f x) xs) = foldApps (.app (erase f) (erase x)) (xs.map erase)
      rw [foldAppsA_erase (.app f x) xs]
      rfl

theorem applyTelA_erase : (as : List ExprA) → (T : ExprA) →
    (applyTelA as T).map erase = applyTel (as.map erase) (erase T)
  | [], _ => rfl
  | a :: as, .pi A u B v => by
      show (applyTelA as (instantiate0A a B)).map erase =
        applyTel (as.map erase) (instantiate0 (erase a) (erase B))
      rw [← erase_instantiate0A]
      exact applyTelA_erase as _
  | _ :: _, .bvar _ => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const _ _ => rfl
  | _ :: _, .app _ _ => rfl
  | _ :: _, .lam _ _ _ => rfl
  | _ :: _, .letE _ _ _ => rfl
  | _ :: _, .lit _ => rfl

/-- the leading domains and the body erase to `peelPis` at the Π-count. -/
theorem piDomsA_erase_peelPis : (T : ExprA) →
    peelPis (piCountA T) (erase T) = some ((piDomsA T).map erase, erase (piBodyA T))
  | .pi A u B v => by
      show peelPis (piCountA B + 1) (.pi (erase A) (erase B)) =
        some (erase A :: (piDomsA B).map erase, erase (piBodyA B))
      simp only [peelPis, piDomsA_erase_peelPis B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem ctorKindsA_eq (fam nparams : Nat) (T : ExprA) :
    ctorKindsA fam nparams T = analyzeFields fam (((piDomsA T).map erase).drop nparams) := by
  unfold ctorKindsA
  rw [List.map_drop]

/-- the kinds `main` reads are the relation's shapes where each has a kind (`main` reads none at a
    function-recursive field; ι reads the shapes, R-NoFunRec-1 step 1 (1c-γ)). -/
theorem ctorKindsA_eq_shapes (fam nparams : Nat) (T : ExprA) :
    ctorKindsA fam nparams T = (ctorShapesA fam nparams T).bind shapesKinds := by
  unfold ctorKindsA ctorShapesA
  exact analyzeFields_eq_shapes fam _

/-- types that erase equally have the same erased leading domains (R-NoDeltaRec-4d-iii: a
    constructor's `normA` against its stored type under `EnvNormEraseA`). -/
theorem piDomsA_map_erase_of_erase {T T' : ExprA} (h : erase T = erase T') :
    (piDomsA T).map erase = (piDomsA T').map erase := by
  have h1 := piDomsA_erase_peelPis T
  have h2 := piDomsA_erase_peelPis T'
  rw [← piCountA_erase, h, piCountA_erase] at h1
  exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).1

/-- the shapes read through erasure agree on types that erase equally. -/
theorem ctorShapesA_of_erase {fam nparams : Nat} {T T' : ExprA} (h : erase T = erase T') :
    ctorShapesA fam nparams T = ctorShapesA fam nparams T' := by
  unfold ctorShapesA
  rw [List.map_drop, List.map_drop, piDomsA_map_erase_of_erase h]

theorem ctorShapesA_of_kinds {fam nparams : Nat} {T : ExprA} {ks : List RecKind}
    (h : ctorKindsA fam nparams T = some ks) : ctorShapesA fam nparams T = some (ks.map RecKind.shape) := by
  rw [ctorKindsA_eq_shapes] at h
  cases hs : ctorShapesA fam nparams T with
  | none => rw [hs] at h; exact Option.noConfusion h
  | some ss =>
      rw [hs] at h
      rw [shapesKinds_eq_map h]

theorem familyIdxA_erase (n : Nat) (A : ExprA) :
    (familyIdxA n A).map erase = familyIdx n (erase A) := by
  unfold familyIdxA familyIdx
  rw [appsSpineA_erase A, List.map_drop]

theorem recPrefixA_erase (pre : List ExprA) (n m : Nat) :
    (recPrefixA pre n m).map erase = recPrefix (pre.map erase) n m := by
  unfold recPrefixA recPrefix
  rw [List.map_take]

theorem recCallFieldA_erase (rec : ExprA) (pre : List ExprA) (n m : Nat) (f A : ExprA) :
    erase (recCallFieldA rec pre n m f A) =
      recCallField (erase rec) (pre.map erase) n m (erase f) (erase A) := by
  unfold recCallFieldA recCallField
  rw [foldAppsA_erase, List.map_append, List.map_append, recPrefixA_erase, familyIdxA_erase]
  rfl

/-- on the shape `fieldsTelA` admits, where every field has a kind, `rhsArgsA` erases to main's
    `rhsArgs`. -/
theorem rhsArgsA_erase (rec : ExprA) (pre : List ExprA) (n m : Nat) (fs : List ExprA) :
    (ks : List RecKind) → (T : ExprA) → fieldsTelA fs (ks.map RecKind.shape) T = true →
    (rhsArgsA rec pre n m fs (ks.map RecKind.shape) T).map erase =
      rhsArgs (erase rec) (pre.map erase) n m (fs.map erase) ks (erase T) := by
  induction fs with
  | nil =>
      intro ks T h
      cases ks with
      | nil => rfl
      | cons k ks => exact Bool.noConfusion h
  | cons f fs ih =>
      intro ks T h
      cases ks with
      | nil => exact Bool.noConfusion h
      | cons k ks =>
          obtain ⟨A, u, B, v, rfl, _, ht⟩ := fieldsTelA_cons h
          cases k with
          | plain =>
              show erase f :: (rhsArgsA rec pre n m fs (ks.map RecKind.shape) (instantiate0A f B)).map erase =
                erase f :: rhsArgs (erase rec) (pre.map erase) n m (fs.map erase) ks
                  (instantiate0 (erase f) (erase B))
              rw [← erase_instantiate0A, ih ks _ ht]
          | directRec =>
              show erase f :: erase (recCallFieldA rec pre n m f A) ::
                  (rhsArgsA rec pre n m fs (ks.map RecKind.shape) (instantiate0A f B)).map erase =
                erase f :: recCallField (erase rec) (pre.map erase) n m (erase f) (erase A) ::
                  rhsArgs (erase rec) (pre.map erase) n m (fs.map erase) ks
                    (instantiate0 (erase f) (erase B))
              rw [← erase_instantiate0A, ih ks _ ht, recCallFieldA_erase]

/-- the erased Π-telescope: `piDomListA`'s domains and `piBodyA` are `piTelE` through
    `erase` — the annotation sorts the erased walk ignores. -/
theorem erase_piTelE : (A : ExprA) →
    ((piDomListA A).map fun p => erase p.1) = (piTelE (erase A)).1 ∧
      erase (piBodyA A) = (piTelE (erase A)).2
  | .pi A u B v => by
      obtain ⟨ihd, ihb⟩ := erase_piTelE B
      show (erase A :: ((piDomListA B).map fun p => erase p.1)) =
            (piTelE (.pi (erase A) (erase B))).1 ∧
          erase (piBodyA B) = (piTelE (.pi (erase A) (erase B))).2
      rw [piTelE]
      exact ⟨by rw [ihd], ihb⟩
  | .bvar _ => ⟨rfl, rfl⟩
  | .sort _ => ⟨rfl, rfl⟩
  | .const _ _ => ⟨rfl, rfl⟩
  | .app _ _ => ⟨rfl, rfl⟩
  | .lam _ _ _ => ⟨rfl, rfl⟩
  | .letE _ _ _ => ⟨rfl, rfl⟩
  | .lit _ => ⟨rfl, rfl⟩

/-- `spineHeadConstA` erases to `spineHeadConst`. -/
theorem spineHeadConstA_erase (A : ExprA) :
    spineHeadConstA A = spineHeadConst (erase A) := by
  unfold spineHeadConstA spineHeadConst
  rw [appsSpineA_erase]
  cases (appsSpineA A).1 <;> rfl

/-- `shapeGuardA` erases to `shapeGuardS`. -/
theorem shapeGuardA_erase (A : ExprA) (s : FieldShape) :
    shapeGuardA A s = shapeGuardS (erase A) s := by
  cases s with
  | nonrecursive => rfl
  | recursive k =>
      cases k with
      | zero => exact spineHeadConstA_erase A
      | succ k =>
          show ((piDomListA A).length == k + 1 && spineHeadConstA (piBodyA A)) =
            (((piTelE (erase A)).1.length == k + 1) && spineHeadConst (piTelE (erase A)).2)
          obtain ⟨ihd, ihb⟩ := erase_piTelE A
          rw [← ihd, List.length_map, ← ihb, spineHeadConstA_erase]

/-- `fieldsTelA` erases to `fieldsTelS`. -/
theorem fieldsTelA_erase : (fs : List ExprA) → (ss : List FieldShape) → (T : ExprA) →
    fieldsTelA fs ss T = fieldsTelS (fs.map erase) ss (erase T)
  | [], [], _ => rfl
  | f :: fs, s :: ss, T => by
      cases T with
      | pi A u B v =>
          have e : erase (ExprA.pi A u B v) = .pi (erase A) (erase B) := rfl
          rw [e]
          show (shapeGuardA A s && fieldsTelA fs ss (instantiate0A f B)) =
            fieldsTelS (erase f :: fs.map erase) (s :: ss) (.pi (erase A) (erase B))
          simp only [List.map_cons, fieldsTelS]
          rw [shapeGuardA_erase, fieldsTelA_erase fs ss (instantiate0A f B),
            erase_instantiate0A]
      | bvar _ => rfl
      | sort _ => rfl
      | const _ _ => rfl
      | app _ _ => rfl
      | lam _ _ _ => rfl
      | letE _ _ _ => rfl
      | lit _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl

/-- `lamTelA` erases to `lamTelescope`, forgetting the binder sorts. -/
theorem erase_lamTelA : (ds : List (ExprA × Level)) → (b : ExprA) →
    erase (lamTelA ds b) = lamTelescope (ds.map fun p => erase p.1) (erase b)
  | [], b => rfl
  | (D, u) :: ds, b => by
      show erase (.lam D u (lamTelA ds b)) =
        lamTelescope (erase D :: ds.map (fun p => erase p.1)) (erase b)
      simp only [erase, lamTelescope]
      exact congrArg (Expr.lam (erase D)) (erase_lamTelA ds b)

/-- `recCallFunA` erases to `recCallFunS` — the λ-wrapped call at a function-recursive
    field on the erased syntax. -/
theorem recCallFunA_erase (recA : ExprA) (pre : List ExprA) (np nm : Nat) (f A : ExprA) :
    erase (recCallFunA recA pre np nm f A) =
      recCallFunS (erase recA) (pre.map erase) np nm (erase f) (erase A) := by
  obtain ⟨ihd, ihb⟩ := erase_piTelE A
  have hlen : (piDomListA A).length = (piTelE (erase A)).1.length := by
    rw [← ihd, List.length_map]
  have hpre' : ((pre.map (liftA 0 (piTelE (erase A)).1.length)).map erase) =
      (pre.map erase).map (lift 0 (piTelE (erase A)).1.length) := by
    simp only [List.map_map]
    exact List.map_congr_left fun x _ => erase_liftA x _ _
  have hbv : (((List.range (piTelE (erase A)).1.length).reverse.map ExprA.bvar).map erase) =
      (List.range (piTelE (erase A)).1.length).reverse.map Expr.bvar := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    rfl
  unfold recCallFunA recCallFunS
  rw [hlen, erase_lamTelA, ihd, recCallFieldA_erase, foldAppsA_erase, erase_liftA, ihb,
    hpre', hbv]

/-- `recCallsA` erases to `recCallsS`. -/
theorem recCallsA_erase (recA : ExprA) (pre : List ExprA) (np nm : Nat) (f A : ExprA)
    (s : FieldShape) :
    (recCallsA recA pre np nm f A s).map erase =
      recCallsS (erase recA) (pre.map erase) np nm (erase f) (erase A) s := by
  cases s with
  | nonrecursive => rfl
  | recursive k =>
      cases k with
      | zero => simp only [recCallsA, List.map_cons, List.map_nil, recCallsS,
          recCallFieldA_erase]
      | succ k => simp only [recCallsA, List.map_cons, List.map_nil, recCallsS,
          recCallFunA_erase]

/-- `rhsArgsA` erases to `rhsArgsS` — at EVERY shape, not only the kinds: this is the
    annotation direction's right-hand side read on the erased data alone. -/
theorem rhsArgsA_eraseS (rec : ExprA) (pre : List ExprA) (n m : Nat) :
    (fs : List ExprA) → (ss : List FieldShape) → (T : ExprA) →
    (rhsArgsA rec pre n m fs ss T).map erase =
      rhsArgsS (erase rec) (pre.map erase) n m (fs.map erase) ss (erase T)
  | [], [], _ => rfl
  | f :: fs, s :: ss, T => by
      cases T with
      | pi A u B v =>
          show ((f :: (recCallsA rec pre n m f A s ++
                rhsArgsA rec pre n m fs ss (instantiate0A f B))).map erase) =
            rhsArgsS (erase rec) (pre.map erase) n m
              (erase f :: fs.map erase) (s :: ss) (.pi (erase A) (erase B))
          simp only [List.map_cons, List.map_append, recCallsA_erase, rhsArgsS,
            rhsArgsA_eraseS rec pre n m fs ss (instantiate0A f B), erase_instantiate0A]
      | bvar _ => rfl
      | sort _ => rfl
      | const _ _ => rfl
      | app _ _ => rfl
      | lam _ _ _ => rfl
      | letE _ _ _ => rfl
      | lit _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl

#print axioms fieldsTelA_cons
#print axioms appsSpineA_erase
#print axioms applyTelA_erase
#print axioms piDomsA_erase_peelPis
#print axioms recCallFieldA_erase
#print axioms rhsArgsA_erase
#print axioms analyzeField_eq_shape
#print axioms analyzeFields_eq_shapes
#print axioms shapesKinds_eq_map
#print axioms ctorKindsA_eq_shapes
#print axioms ctorShapesA_of_kinds

end Rcic.Declarative.Ann
