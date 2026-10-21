import rcic.RcicTypedCheck
import rcic.RcicAnnViewTySem
import rcic.RcicAnnSemPrefixRows
import rcic.RcicLevelDec
import rcic.RcicUniverseClass

/-!
# W-2 — the copy's scope from a group's members, by a test

The three rows hold over every `EnvWfT` environment in the copy's scope with no other hypothesis
(D-sem: `Ann.sortConvCharT_semPrefix` and the two after it). The scope (`EnvWfT.InScope`) asks, at each
group, for structured views typed in 05 §4's scopes (`GroupInScopeT`). Before W-2 nothing produced them:
every in-scope environment was a pin with views written by hand.

This module builds the views from a group's members and checks them with a test (`groupCheckB`). A
derivation whose groups pass the test is in the scope (`EnvWfT.inScope_of_scopeCheck`), so the three rows
hold over it (`sortConvCharT_scopeCheck`, `piConvInjT_scopeCheck`, `famAppConvInjT_scopeCheck`).

* (2) A syntactic checker for the typed judgment (`checkT`, in `RcicTypedCheck`): each rule read off the
  term, with no reduction and no conversion, a numeral through its expansion (W-3). Its answer carries
  the derivation, so it is sound by construction.
  The test runs with a checker (`CheckerT`, W-3, W-4). A checker answers with its evidence (typings,
  conversions, the level order), so every checker is sound by its type. `synChecker` is `checkT`'s;
  `RcicTypedConv` adds one with conversion.
* (3) The test reads a skeleton (the views' syntax) against the members.
  - The family's stored type is its telescope, its sort is uniform, and its domains are typed in the base.
  - Each constructor's type is typed with the family present, and its stored type is the one the views
    build. Its mirrors convert to the family's parameters. Its fields and result indices are typed in
    the plain context, in the base. Each plain field's level is within the family's sort. Conversions
    and the level order are the checker's.
  - The recursor's stored type is the one the views build, typed with the constructors present.
  - The constructors' references follow the family's.
  - (O2) holds by the checker's level order; (O1) is read on the views.
* (4) The views built from a passing test, every typing the checker's (`groupInScopeT_of_check`).
* (6) A reader (`groupSkel?`) reads a skeleton off the members. It is not trusted: the test re-checks
  what it returns.

Why a checker. L-K1 types a constructor's fields with the family and the earlier constructors present.
The views type them in the base, before the family exists. Moving a derivation from the larger
environment to the smaller is environment strengthening, which the tree does not have for `HasTyT`: a
conversion step can pass through a term that names the family. A checker builds its derivation in the
environment and context it is given, so a field it types is typed in the base. In the same way it types a
field that follows a recursive field directly in the plain context, without that field's variable, so no
context strengthening is needed.

What the test refuses.
* A field that names the family but is not the family at the parameter locals: a negative or nested
  occurrence, R-NoFunRec, R-NoDeltaRec. As a recursive field its type is not the views' recursive field;
  as a plain field it has no typing in the base.
* A field whose type names a recursive field's variable (Measured 4): it has no form in the plain context.
* A group outside the profiles: `profileCheckB` fails.
* A typing, conversion or level order the checker does not answer. `synChecker` answers none that needs
  a conversion step, and orders levels by `geq` (sound; its completeness is walled, H-6b).

(1) W-2 (a), the general agreement: L-K1's builders compute the views' types.
* Its minor over the views' constructor telescope is the views' minor (`minorFromTelescope_ctorFieldsT`,
  `derivedMinor_eq`), with each recursive field read as admission reads it (`piTelescopeFuel_famApp`).
* Its constructor type over `ctorDomsT` is `ctorTypeT` (`ctorFieldTelescope_eq`).
* Its recursor signature over the views' minors is `recTypeT` (`policyRecursorType_eq`).

So wherever L-K1's fields and field shapes are the views', the test's two stored-type checks ask for what
L-K1 already builds.
-/

namespace Rcic.Declarative

/-! ## (1) L-K1's builders compute the views' types -/

/-! ### the minor -/

/-- a field's shape as L-K1 reads it: a plain field is non-recursive, a directly recursive one is
    `recursive 0`. -/
def FieldT.shapeT : FieldT → FieldShape
  | .plain _ _ => .nonrecursive
  | .drec _ => .recursive 0
  | .drecD _ _ => .recursive 0

/-- a lift one binder up commutes past a lift by one at `0`. -/
theorem lift_succ_lift_one (c d : Nat) (e : Expr Nat) : lift (c + 1) d (lift 0 1 e) = lift 0 1 (lift c d e) := by
  rw [lift_lift_permute 1 d c 0 (Nat.zero_le c), Nat.add_comm 1 c]

theorem SubstT.lift_up (c d : Nat) (σ : SubstT) :
    (fun i => lift (c + 1) d (σ.up i)) = SubstT.up (fun i => lift c d (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact lift_succ_lift_one c d (σ i)

theorem SubstT.lift_shift1 (c d : Nat) (σ : SubstT) :
    (fun i => lift (c + 1) d (σ.shift1 i)) = SubstT.shift1 (fun i => lift c d (σ i)) := by
  funext i
  exact lift_succ_lift_one c d (σ i)

/-- a lift commutes with a parallel substitution: it moves onto the substitution's images. -/
theorem lift_substT (d : Nat) : (e : Expr Nat) → (c : Nat) → (σ : SubstT) →
    lift c d (substT σ e) = substT (fun i => lift c d (σ i)) e
  | .bvar _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .app f x, c, σ => by
      show Expr.app (lift c d (substT σ f)) (lift c d (substT σ x)) = _
      rw [lift_substT d f c σ, lift_substT d x c σ]; rfl
  | .lam a b, c, σ => by
      show Expr.lam (lift c d (substT σ a)) (lift (c + 1) d (substT σ.up b)) = _
      rw [lift_substT d a c σ, lift_substT d b (c + 1) σ.up, SubstT.lift_up]; rfl
  | .pi a b, c, σ => by
      show Expr.pi (lift c d (substT σ a)) (lift (c + 1) d (substT σ.up b)) = _
      rw [lift_substT d a c σ, lift_substT d b (c + 1) σ.up, SubstT.lift_up]; rfl
  | .letE a w b, c, σ => by
      show Expr.letE (lift c d (substT σ a)) (lift c d (substT σ w)) (lift (c + 1) d (substT σ.up b)) = _
      rw [lift_substT d a c σ, lift_substT d w c σ, lift_substT d b (c + 1) σ.up, SubstT.lift_up]; rfl
  | .lit _, _, _ => rfl

theorem map_lift_succ_lift_one (c d : Nat) (xs : List (Expr Nat)) :
    (xs.map (lift 0 1)).map (lift (c + 1) d) = (xs.map (lift c d)).map (lift 0 1) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  exact lift_succ_lift_one c d x

/-- a lift commutes with the constructor telescope builder. -/
theorem lift_ctorFieldsT (f : Nat) (ls : List Level) (d : Nat) (res : List (Expr Nat)) :
    (fs : List FieldT) → (c : Nat) → (pl : List (Expr Nat)) → (σ : SubstT) →
    lift c d (ctorFieldsT f ls pl σ fs res) =
      ctorFieldsT f ls (pl.map (lift c d)) (fun i => lift c d (σ i)) fs res
  | [], c, pl, σ => by
      simp only [ctorFieldsT]
      rw [foldApps_lift, List.map_append, List.map_map]
      congr 2
      apply List.map_congr_left
      intro x _
      exact lift_substT d x c σ
  | .plain D u :: fs, c, pl, σ => by
      show Expr.pi (lift c d (substT σ D)) (lift (c + 1) d (ctorFieldsT f ls (pl.map (lift 0 1)) σ.up fs res)) = _
      rw [lift_substT d D c σ, lift_ctorFieldsT f ls d res fs (c + 1), SubstT.lift_up, map_lift_succ_lift_one]
      rfl
  | .drec idx :: fs, c, pl, σ => by
      show Expr.pi (lift c d (foldApps (.const f ls) (pl ++ idx.map (substT σ))))
          (lift (c + 1) d (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res)) = _
      rw [lift_ctorFieldsT f ls d res fs (c + 1), SubstT.lift_shift1, map_lift_succ_lift_one, foldApps_lift,
        List.map_append, List.map_map]
      have hidx : idx.map (lift c d ∘ substT σ) = idx.map (substT (fun i => lift c d (σ i))) :=
        List.map_congr_left (fun x _ => lift_substT d x c σ)
      rw [hidx]
      rfl
  | .drecD D _ :: fs, c, pl, σ => by
      show Expr.pi (lift c d (substT σ D))
          (lift (c + 1) d (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res)) = _
      rw [lift_substT d D c σ, lift_ctorFieldsT f ls d res fs (c + 1), SubstT.lift_shift1,
        map_lift_succ_lift_one]
      rfl

theorem lift_two_lift_two (c d : Nat) (e : Expr Nat) :
    lift (c + 1 + 1) d (lift 0 2 e) = lift 0 2 (lift c d e) := by
  rw [lift_lift_permute 2 d c 0 (Nat.zero_le c), Nat.add_comm 2 c]

theorem SubstT.lift_shift1_shift1 (c d : Nat) (σ : SubstT) :
    (fun i => lift (c + 1 + 1) d (σ.shift1.shift1 i)) = SubstT.shift1 (SubstT.shift1 (fun i => lift c d (σ i))) := by
  funext i
  show lift (c + 1 + 1) d (lift 0 1 (lift 0 1 (σ i))) = lift 0 1 (lift 0 1 (lift c d (σ i)))
  rw [lift_succ_lift_one (c + 1) d, lift_succ_lift_one c d]

theorem map_lift_two_lift_two (c d : Nat) (xs : List (Expr Nat)) :
    (xs.map (lift 0 2)).map (lift (c + 1 + 1) d) = (xs.map (lift c d)).map (lift 0 2) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  exact lift_two_lift_two c d x

/-- a lift commutes with the minor premise builder. -/
theorem lift_minorFieldsT (f k : Nat) (ls : List Level) (d : Nat) (res : List (Expr Nat)) :
    (fs : List FieldT) → (c : Nat) → (pl : List (Expr Nat)) → (mot : Expr Nat) → (fl : List (Expr Nat)) →
    (σ : SubstT) →
    lift c d (minorFieldsT f k ls pl mot fl σ fs res) =
      minorFieldsT f k ls (pl.map (lift c d)) (lift c d mot) (fl.map (lift c d)) (fun i => lift c d (σ i)) fs res
  | [], c, pl, mot, fl, σ => by
      simp only [minorFieldsT]
      rw [foldApps_lift, List.map_append, List.map_map, List.map_cons, List.map_nil, foldApps_lift, lift,
        List.map_append]
      have hres : res.map (lift c d ∘ substT σ) = res.map (substT (fun i => lift c d (σ i))) :=
        List.map_congr_left (fun x _ => lift_substT d x c σ)
      rw [hres]
  | .plain D u :: fs, c, pl, mot, fl, σ => by
      show Expr.pi (lift c d (substT σ D))
          (lift (c + 1) d (minorFieldsT f k ls (pl.map (lift 0 1)) (lift 0 1 mot) (fl.map (lift 0 1) ++ [.bvar 0])
            σ.up fs res)) = _
      rw [lift_substT d D c σ, lift_minorFieldsT f k ls d res fs (c + 1), SubstT.lift_up, map_lift_succ_lift_one,
        lift_succ_lift_one, List.map_append, map_lift_succ_lift_one]
      rfl
  | .drec idx :: fs, c, pl, mot, fl, σ => by
      show Expr.pi (lift c d (foldApps (.const f ls) (pl ++ idx.map (substT σ))))
          (Expr.pi (lift (c + 1) d (foldApps (lift 0 1 mot) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0])))
            (lift (c + 1 + 1) d (minorFieldsT f k ls (pl.map (lift 0 2)) (lift 0 2 mot)
              (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res))) = _
      rw [lift_minorFieldsT f k ls d res fs (c + 1 + 1), SubstT.lift_shift1_shift1, map_lift_two_lift_two,
        lift_two_lift_two, List.map_append, map_lift_two_lift_two, foldApps_lift, foldApps_lift, List.map_append,
        List.map_append, lift_succ_lift_one, map_lift_succ_lift_one, List.map_map]
      have hidx : idx.map (lift c d ∘ substT σ) = idx.map (substT (fun i => lift c d (σ i))) :=
        List.map_congr_left (fun x _ => lift_substT d x c σ)
      rw [hidx]
      rfl
  | .drecD D idx :: fs, c, pl, mot, fl, σ => by
      show Expr.pi (lift c d (substT σ D))
          (Expr.pi (lift (c + 1) d (foldApps (lift 0 1 mot) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0])))
            (lift (c + 1 + 1) d (minorFieldsT f k ls (pl.map (lift 0 2)) (lift 0 2 mot)
              (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res))) = _
      rw [lift_substT d D c σ, lift_minorFieldsT f k ls d res fs (c + 1 + 1), SubstT.lift_shift1_shift1,
        map_lift_two_lift_two, lift_two_lift_two, List.map_append, map_lift_two_lift_two, foldApps_lift,
        List.map_append, map_lift_succ_lift_one, lift_succ_lift_one, List.map_map, List.map_map]
      have hidx : idx.map ((lift 0 1 ∘ lift c d) ∘ substT σ) =
          idx.map (lift 0 1 ∘ substT (fun i => lift c d (σ i))) :=
        List.map_congr_left fun x _ => by
          show lift 0 1 (lift c d (substT σ x)) = lift 0 1 (substT (fun i => lift c d (σ i)) x)
          rw [lift_substT]
      rw [hidx]
      rw [← List.map_map]
      rfl

/-- the constructor application with one more field local, past one binder. -/
theorem lift_one_acc (k : Nat) (ls : List Level) (pl fl : List (Expr Nat)) :
    Expr.app (lift 0 1 (foldApps (.const k ls) (pl ++ fl))) (.bvar 0) =
      foldApps (.const k ls) (pl.map (lift 0 1) ++ (fl.map (lift 0 1) ++ [.bvar 0])) := by
  rw [foldApps_lift, List.map_append, ← List.append_assoc, foldApps_snoc]; rfl

/-- the same past the field's binder and its induction hypothesis's. -/
theorem lift_two_acc (k : Nat) (ls : List Level) (pl fl : List (Expr Nat)) :
    Expr.app (lift 0 2 (foldApps (.const k ls) (pl ++ fl))) (.bvar 1) =
      foldApps (.const k ls) (pl.map (lift 0 2) ++ (fl.map (lift 0 2) ++ [.bvar 1])) := by
  rw [foldApps_lift, List.map_append, ← List.append_assoc, foldApps_snoc]; rfl

theorem lift_one_one (e : Expr Nat) : lift 0 1 (lift 0 1 e) = lift 0 2 e :=
  lift_lift_merge 1 1 0 0 (Nat.le_refl 0) (Nat.zero_le _) e

/-- a family member is not unfolded: its class is not transparent. -/
theorem transparentBody_family {E : ResolvedEnv} (v : PolicyFamilyView E) (ls : List Level) :
    transparentBody E v.ref ls = none := by
  simp [transparentBody, v.present, v.hasClass, transparent]

/-- admission reads an application of a family that is not unfolded as itself, with no binder, once
    its bound reaches one head step. -/
theorem piTelescopeFuel_famApp {E : ResolvedEnv} {f : Nat} {ls : List Level} (args : List (Expr Nat))
    (hf : transparentBody E f ls = none) {fuel : Nat} (hfuel : 2 ≤ fuel) :
    piTelescopeFuel E fuel (foldApps (.const f ls) args) = some ([], foldApps (.const f ls) args) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
  have hsp : appsSpine (foldApps (.const f ls) args) = (.const f ls, args) := by
    rw [appsSpine_foldApps, appsSpine_const, List.nil_append]
  have hw : whnfFuel E (k + 1) (foldApps (.const f ls) args) = some (foldApps (.const f ls) args) := by
    simp only [whnfFuel, hsp, hf]
  simp only [piTelescopeFuel, hw]
  rcases List.eq_nil_or_concat args with rfl | ⟨xs, x, rfl⟩
  · rfl
  · rw [List.concat_eq_append, foldApps_snoc]

/-- L-K1's minor builder over the views' constructor telescope is the views' minor: the field binders,
    the induction hypothesis after each directly recursive field, and the motive at the constructor
    application. A recursive field is read as admission reads it, at a bound of at least one head step;
    the family is not unfolded. `hnd` keeps the correspondence in the δ-reached-free scope until the
    field reader produces `drecD` and carries its unfold evidence (R-NoDeltaRec-4a). -/
theorem minorFromTelescope_ctorFieldsT {E : ResolvedEnv} {fuel : Nat} (f k : Nat) (ls : List Level)
    (np : Nat) (res : List (Expr Nat)) (hf : transparentBody E f ls = none) (hfuel : 2 ≤ fuel) :
    (fs : List FieldT) → (∀ d ∈ fs, d.isDrecD = false) → (pl : List (Expr Nat)) → pl.length = np →
    (M : Expr Nat) → (fl : List (Expr Nat)) → (σ : SubstT) →
    minorFromTelescope E fuel np M (foldApps (.const k ls) (pl ++ fl)) (fs.map FieldT.shapeT)
        (ctorFieldsT f ls pl σ fs res) =
      some (minorFieldsT f k ls pl M fl σ fs res)
  | [], _, pl, hpl, M, fl, σ => by
      simp only [List.map_nil, ctorFieldsT, minorFromTelescope, minorFieldsT]
      rw [familyIdx_foldApps_const hpl, foldApps_snoc]
  | .plain D u :: fs, hnd, pl, hpl, M, fl, σ => by
      show minorFromTelescope E fuel np M (foldApps (.const k ls) (pl ++ fl))
          (.nonrecursive :: fs.map FieldT.shapeT)
          (.pi (substT σ D) (ctorFieldsT f ls (pl.map (lift 0 1)) σ.up fs res)) = _
      simp only [minorFromTelescope]
      rw [lift_one_acc, minorFromTelescope_ctorFieldsT f k ls np res hf hfuel fs
        (fun d hd => hnd d (List.mem_cons_of_mem _ hd)) (pl.map (lift 0 1))
        (by rw [List.length_map, hpl]) (lift 0 1 M) _ σ.up]
      rfl
  | .drec idx :: fs, hnd, pl, hpl, M, fl, σ => by
      show minorFromTelescope E fuel np M (foldApps (.const k ls) (pl ++ fl))
          (.recursive 0 :: fs.map FieldT.shapeT)
          (.pi (foldApps (.const f ls) (pl ++ idx.map (substT σ)))
            (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res)) = _
      have hA : lift 0 1 (foldApps (.const f ls) (pl ++ idx.map (substT σ))) =
          foldApps (.const f ls) (pl.map (lift 0 1) ++ (idx.map (substT σ)).map (lift 0 1)) := by
        rw [foldApps_lift, List.map_append]; rfl
      have hpl1 : (pl.map (lift 0 1)).length = np := by rw [List.length_map, hpl]
      have hih : funIHType E fuel np (foldApps (.const f ls) (pl ++ idx.map (substT σ))) M 0 =
          some (foldApps (lift 0 1 M) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0])) := by
        simp only [funIHType, hA, piTelescopeFuel_famApp _ hf hfuel, List.length_nil, ↓reduceIte,
          lift_zero, familyIdx_foldApps_const hpl1]
        rfl
      have hpl2 : (pl.map (lift 0 1)).map (lift 0 1) = pl.map (lift 0 2) := by
        rw [List.map_map]; exact List.map_congr_left (fun x _ => lift_one_one x)
      simp only [minorFromTelescope, hih]
      rw [lift_two_acc, lift_ctorFieldsT, hpl2, minorFromTelescope_ctorFieldsT f k ls np res hf hfuel fs
        (fun d hd => hnd d (List.mem_cons_of_mem _ hd)) (pl.map (lift 0 2))
        (by rw [List.length_map, hpl]) (lift 0 2 M) _ (fun i => lift 0 1 (σ.shift1 i))]
      rfl
  | .drecD D _ :: fs, hnd, _, _, _, _, _ =>
      Bool.noConfusion (hnd (.drecD D _) (List.mem_cons_self _ _))

/-! ### the constructor -/

theorem policyPi_append (xs ys : List (Expr Nat)) (body : Expr Nat) :
    policyPi (xs ++ ys) body = policyPi xs (policyPi ys body) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Expr.pi x) ih

/-- the domains of the views' constructor telescope: a plain field's domain moved into the full
    context, a directly recursive field's family application at the parameter locals. -/
def ctorDomsT (f : Nat) (ls : List Level) : List (Expr Nat) → SubstT → List FieldT → List (Expr Nat)
  | _, _, [] => []
  | pl, σ, .plain D _ :: fs => substT σ D :: ctorDomsT f ls (pl.map (lift 0 1)) σ.up fs
  | pl, σ, .drec idx :: fs =>
      foldApps (.const f ls) (pl ++ idx.map (substT σ)) :: ctorDomsT f ls (pl.map (lift 0 1)) σ.shift1 fs
  | pl, σ, .drecD D _ :: fs =>
      substT σ D :: ctorDomsT f ls (pl.map (lift 0 1)) σ.shift1 fs

/-- the plain context into the context after the fields. -/
def ctorEndSubstT : SubstT → List FieldT → SubstT
  | σ, [] => σ
  | σ, .plain _ _ :: fs => ctorEndSubstT σ.up fs
  | σ, .drec _ :: fs => ctorEndSubstT σ.shift1 fs
  | σ, .drecD _ _ :: fs => ctorEndSubstT σ.shift1 fs

theorem ctorDomsT_length (f : Nat) (ls : List Level) :
    (fs : List FieldT) → (pl : List (Expr Nat)) → (σ : SubstT) → (ctorDomsT f ls pl σ fs).length = fs.length
  | [], _, _ => rfl
  | .plain _ _ :: fs, pl, σ => by
      simp only [ctorDomsT, List.length_cons, ctorDomsT_length f ls fs]
  | .drec _ :: fs, pl, σ => by
      simp only [ctorDomsT, List.length_cons, ctorDomsT_length f ls fs]
  | .drecD _ _ :: fs, pl, σ => by
      simp only [ctorDomsT, List.length_cons, ctorDomsT_length f ls fs]

theorem map_lift_succ_merge (k : Nat) (pl : List (Expr Nat)) :
    (pl.map (lift 0 1)).map (lift 0 k) = pl.map (lift 0 (k + 1)) := by
  rw [List.map_map]
  exact List.map_congr_left (fun x _ => by
    show lift 0 k (lift 0 1 x) = _
    rw [lift_lift_merge k 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm])

/-- THE VIEWS' CONSTRUCTOR TELESCOPE IS A TELESCOPE OVER `ctorDomsT`: its result is the family at the
    parameter locals past every field and the result indices moved into the full context. -/
theorem ctorFieldsT_policyPi (f : Nat) (ls : List Level) (res : List (Expr Nat)) :
    (fs : List FieldT) → (pl : List (Expr Nat)) → (σ : SubstT) →
    ctorFieldsT f ls pl σ fs res =
      policyPi (ctorDomsT f ls pl σ fs)
        (foldApps (.const f ls) (pl.map (lift 0 fs.length) ++ res.map (substT (ctorEndSubstT σ fs))))
  | [], pl, σ => by
      show foldApps _ _ = foldApps (Expr.const f ls) (pl.map (lift 0 0) ++ res.map (substT σ))
      rw [show pl.map (lift 0 0) = pl from
        (List.map_congr_left (fun x _ => lift_zero 0 x)).trans (List.map_id pl)]
  | .plain D u :: fs, pl, σ => by
      show Expr.pi _ (ctorFieldsT f ls (pl.map (lift 0 1)) σ.up fs res) = Expr.pi _ _
      rw [ctorFieldsT_policyPi f ls res fs, map_lift_succ_merge]
      rfl
  | .drec idx :: fs, pl, σ => by
      show Expr.pi _ (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res) = Expr.pi _ _
      rw [ctorFieldsT_policyPi f ls res fs, map_lift_succ_merge]
      rfl
  | .drecD _ _ :: fs, pl, σ => by
      show Expr.pi _ (ctorFieldsT f ls (pl.map (lift 0 1)) σ.shift1 fs res) = Expr.pi _ _
      rw [ctorFieldsT_policyPi f ls res fs, map_lift_succ_merge]
      rfl

theorem policyLocals_map_lift (np k : Nat) :
    (policyLocals np).map (lift 0 k) = policyParameterLocals np k := by
  simp only [policyLocals, policyParameterLocals, List.map_map]
  exact List.map_congr_left (fun i _ => by
    show lift 0 k (Expr.bvar i) = Expr.bvar (i + k)
    simp only [lift, Nat.zero_le, if_true])

/-- THE CONSTRUCTOR AGREES (05 §6–§8): an L-K1 constructor view whose parameters are the mirrors, whose
    fields are the views' telescope's domains and whose result indices are the views' moved into the
    full context has the views' field telescope, and its stored type is the views' constructor type. -/
theorem ctorFieldTelescope_eq {E : ResolvedEnv} {family : PolicyFamilyView E} {member : CheckedMember}
    (c : PolicyConstructorView E family member) {f : Nat} {ls : List Level}
    {mirrors : List (Expr Nat × Level)} {fs : List FieldT} {res : List (Expr Nat)}
    (href : family.ref = f) (hls : policyFamilyLevels family = ls)
    (hpar : c.parameters = mirrors.map Prod.fst)
    (hfld : c.fields = ctorDomsT f ls (policyLocals mirrors.length) SubstT.id fs)
    (hres : c.resultIndices = res.map (substT (ctorEndSubstT SubstT.id fs))) :
    ctorFieldTelescope c = ctorFieldsT f ls (policyLocals mirrors.length) SubstT.id fs res ∧
      member.mtype = ctorTypeT f ls mirrors fs res := by
  have hnp : c.parameters.length = mirrors.length := by rw [hpar, List.length_map]
  have hnf : c.fields.length = fs.length := by rw [hfld, ctorDomsT_length]
  have htel : ctorFieldTelescope c = ctorFieldsT f ls (policyLocals mirrors.length) SubstT.id fs res := by
    rw [ctorFieldsT_policyPi, policyLocals_map_lift, ← hnf, ← hfld, ← hres, ← hnp, ← href, ← hls]
    rfl
  refine ⟨htel, ?_⟩
  rw [c.storedType, ctorTypeT, ← hpar, policyPi_append]
  exact congrArg (policyPi c.parameters) htel

/-! ### the recursor -/

theorem minorDomsT_length (f : Nat) (ls : List Level) (np : Nat) :
    (j : Nat) → (cds : List MinorDataT) → (minorDomsT f ls np j cds).length = cds.length
  | _, [] => rfl
  | j, _ :: cds => by
      simp only [minorDomsT, List.length_cons, minorDomsT_length f ls np (j + 1) cds]

/-- `List.mapIdx` runs an accumulator: after it, the lifted domains at the accumulator's size. -/
theorem mapIdx_go_lift (a : Nat) : (ds : List (Expr Nat)) → (acc : Array (Expr Nat)) →
    List.mapIdx.go (fun j T => lift j a T) ds acc = acc.toList ++ liftDomsT acc.size a ds
  | [], acc => (List.append_nil _).symm
  | D :: ds, acc => by
      show List.mapIdx.go (fun j T => lift j a T) ds (acc.push (lift acc.size a D)) = _
      rw [mapIdx_go_lift a ds, Array.push_toList, Array.size_push, List.append_assoc]
      rfl

theorem mapIdx_lift_eq_liftDomsT (a : Nat) (ds : List (Expr Nat)) :
    ds.mapIdx (fun j T => lift j a T) = liftDomsT 0 a ds :=
  mapIdx_go_lift a ds #[]

theorem policyLocals_add (np q : Nat) :
    policyLocals (np + q) = (policyLocals np).map (lift 0 q) ++ policyLocals q := by
  rw [policyLocals_map_lift]
  simp only [policyLocals, policyParameterLocals]
  rw [Nat.add_comm np q, List.range_add, List.reverse_append, List.map_append, List.map_reverse,
    List.map_map, ← List.map_reverse]
  congr 1
  exact List.map_congr_left (fun i _ => by
    show Expr.bvar (q + i) = Expr.bvar (i + q)
    rw [Nat.add_comm])

theorem policyLocals_map_lift_above (q c a : Nat) (h : q ≤ c) :
    (policyLocals q).map (lift c a) = policyLocals q := by
  simp only [policyLocals, List.map_map]
  exact List.map_congr_left (fun i hi => by
    have hi' : i < q := List.mem_range.mp (List.mem_reverse.mp hi)
    show lift c a (Expr.bvar i) = Expr.bvar i
    simp only [lift]
    rw [if_neg (Nat.not_le.mpr (Nat.lt_of_lt_of_le hi' h))])

theorem policyParameterLocals_lift (np q a : Nat) :
    (policyParameterLocals np q).map (lift q a) = policyParameterLocals np (a + q) := by
  simp only [policyParameterLocals, List.map_map]
  exact List.map_congr_left (fun i _ => by
    show lift q a (Expr.bvar (i + q)) = Expr.bvar (i + (a + q))
    simp only [lift, if_pos (Nat.le_add_left q i)]
    congr 1
    omega)

theorem policyParameterLocals_length (np k : Nat) : (policyParameterLocals np k).length = np := by
  simp only [policyParameterLocals, List.length_map, List.length_reverse, List.length_range]

/-- the major premise's domain. -/
theorem policyMajor_eq (f : Nat) (ls : List Level) (np q k : Nat) :
    foldApps (.const f ls) (policyParameterLocals np (k + 1 + q) ++ policyLocals q) =
      lift q (k + 1) (famLocalsT f ls np q) := by
  rw [famLocalsT, foldApps_lift, List.map_append, policyLocals_map_lift_above q q (k + 1) (Nat.le_refl q),
    policyLocals_map_lift, policyParameterLocals_lift]
  rfl

/-- the recursor's body. -/
theorem policyResult_eq (q k : Nat) :
    foldApps (.bvar (k + q + 1)) ((List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0]) =
      recBodyT q k := by
  rw [recBodyT, policyLocals_map_lift, Nat.add_comm k q]
  rfl

/-- THE MOTIVE AGREES (05 §11). -/
theorem policyMotiveType_eq {E : ResolvedEnv} (family : PolicyFamilyView E) {f : Nat} {ls : List Level}
    {params indices : List (Expr Nat × Level)} (policy : EliminationPolicy)
    (href : family.ref = f) (hls : policyFamilyLevels family = ls)
    (hpar : family.parameters = params.map Prod.fst) (hidx : family.indices = indices.map Prod.fst) :
    policyMotiveType family policy =
      motTyT f ls params indices (policyMotiveLevel family.member.arity policy) := by
  have hnp : family.parameters.length = params.length := by rw [hpar, List.length_map]
  have hq : family.indices.length = indices.length := by rw [hidx, List.length_map]
  rw [policyMotiveType, motTyT, famLocalsT, ← policyLocals_add, ← hnp, ← hq, ← hidx, ← href, ← hls]

/-- THE RECURSOR TYPE AGREES (05 §13): L-K1's signature over the views' minors is the views'. -/
theorem policyRecursorType_eq {E : ResolvedEnv} (family : PolicyFamilyView E) {f : Nat} {ls : List Level}
    {params indices : List (Expr Nat × Level)} (policy : EliminationPolicy) (cds : List MinorDataT)
    (href : family.ref = f) (hls : policyFamilyLevels family = ls)
    (hpar : family.parameters = params.map Prod.fst) (hidx : family.indices = indices.map Prod.fst) :
    policyRecursorType family (minorDomsT f ls params.length 0 cds) policy =
      recTypeT f ls params indices (policyMotiveLevel family.member.arity policy) cds := by
  have hnp : family.parameters.length = params.length := by rw [hpar, List.length_map]
  have hq : family.indices.length = indices.length := by rw [hidx, List.length_map]
  simp only [policyRecursorType, recTypeT, recDomsT, policyPi_append, minorDomsT_length, policyPi]
  rw [policyMotiveType_eq family policy href hls hpar hidx]
  rw [hnp, hq, href, hls, hidx, ← hpar, mapIdx_lift_eq_liftDomsT, policyMajor_eq, policyResult_eq]

/-! ### the derived minor -/

/-- THE MINOR AGREES (05 §12): at a constructor whose field telescope is the views', L-K1's minor over
    the views' shapes is the views' minor, lifted past the minors before it, at any bound of at least one
    head step. -/
theorem derivedMinor_eq {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) {f : Nat} {ls : List Level}
    {np : Nat} {fs : List FieldT} {res : List (Expr Nat)} {fuel : Nat} (hfuel : 2 ≤ fuel)
    (href : a.family.ref = f) (hls : policyFamilyLevels a.family = ls)
    (hnp : a.family.parameters.length = np)
    (htel : ctorFieldTelescope (a.constructorViews i) = ctorFieldsT f ls (policyLocals np) SubstT.id fs res)
    (hnd : ∀ d ∈ fs, d.isDrecD = false) :
    derivedMinor a i fuel (fs.map FieldT.shapeT) =
      some (lift 0 i.val (minorTyT f ls np (f + 1 + i.val, fs, res))) := by
  have hf : transparentBody E f ls = none := href ▸ transparentBody_family a.family ls
  have h := minorFromTelescope_ctorFieldsT f (f + 1 + i.val) ls np res hf hfuel fs hnd
    (policyParameterLocals np (1 + i.val))
    (policyParameterLocals_length np _) (.bvar i.val) [] (fun j => lift 0 (1 + i.val) (SubstT.id j))
  rw [List.append_nil] at h
  simp only [derivedMinor]
  rw [htel, lift_ctorFieldsT, policyLocals_map_lift, href, hls, hnp, h]
  simp only [minorTyT]
  rw [lift_minorFieldsT, map_lift_succ_merge, policyLocals_map_lift, List.map_nil, Nat.add_comm i.val 1]
  have hσ : (fun j => lift 0 i.val (SubstT.id.shift1 j)) = (fun j => lift 0 (1 + i.val) (SubstT.id j)) := by
    funext j
    show lift 0 i.val (lift 0 1 (Expr.bvar j)) = lift 0 (1 + i.val) (Expr.bvar j)
    rw [lift_lift_merge i.val 1 0 0 (Nat.le_refl 0) (Nat.zero_le _)]
  have hM : lift 0 i.val (Expr.bvar 0 : Expr Nat) = .bvar i.val := by
    simp only [lift, Nat.zero_le, if_true, Nat.zero_add]
  rw [hσ, hM]


/-! ## (2) a certified checker

`checkT` and `synCheck` are in `RcicTypedCheck`, below the typed environment judgment's pins. -/

/-- `geq` read as the level order: sound for `leN` (its completeness is walled, H-6b). -/
theorem leN_of_geq {s u : Level} (h : geq s u 0 = true) : leN u s := fun ρ x y hx hy => by
  have := geq_le s u 0 ρ y x hy hx h
  omega

/-- A CHECKER the test runs with. Its answers carry their evidence, so every checker is sound by its
    type:
    - `check`: a term at a given type, with the derivation;
    - `conv`: a conversion between two types, with its chain (W-4: the mirrors);
    - `levelLe`: the level order, with its soundness (W-4: the field and index levels).
    `sortOf` is the level the reader asks for a domain; it is not trusted, since the test re-checks what
    the reader returns with `check`. -/
structure CheckerT : Type where
  check : (E : ResolvedEnv) → (n : Nat) → (Γ : LCtx) → (e T : Expr Nat) → Option (HasTyT E n Γ e T)
  sortOf : ResolvedEnv → Nat → LCtx → Expr Nat → Option Level
  conv : (E : ResolvedEnv) → (n : Nat) → (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)
  levelLe : Level → Level → Bool
  levelLe_sound : ∀ u s, levelLe u s = true → leN u s

/-- the derivation behind a passing check. -/
def CheckerT.der (C : CheckerT) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (h : (C.check E n Γ e T).isSome = true) : HasTyT E n Γ e T :=
  (C.check E n Γ e T).get h

/-- two types convertible as written. -/
def synConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Option (TyConvT E n Γ A B) :=
  if h : A = B then some (h ▸ .refl Γ A) else none

/-- W-2's checker: `checkT`, types compared as written, levels ordered by `geq`. -/
def synChecker : CheckerT where
  check := synCheck
  sortOf E n Γ e :=
    match inferT E n Γ e with
    | some (.sort u) => some u
    | _ => none
  conv := synConv
  levelLe u s := geq s u 0
  levelLe_sound _ _ h := leN_of_geq h

/-- a telescope checked domain by domain at its recorded sort. -/
def telCheckB (C : CheckerT) (E : ResolvedEnv) (n : Nat) : LCtx → List (Expr Nat × Level) → Bool
  | _, [] => true
  | Γ, (D, u) :: ds => (C.check E n Γ D (.sort u)).isSome && telCheckB C E n (.assumption D :: Γ) ds

def telTyT_of_check {C : CheckerT} {E : ResolvedEnv} {n : Nat} :
    (Γ : LCtx) → (ds : List (Expr Nat × Level)) → telCheckB C E n Γ ds = true → TelTyT E n Γ ds
  | Γ, [], _ => .nil Γ
  | Γ, (D, u) :: ds, h => by
      simp only [telCheckB, Bool.and_eq_true] at h
      exact .cons Γ D u ds (C.der h.1) (telTyT_of_check _ ds h.2)

/-- arguments checked along a Π-telescope down to a sort: a full application. -/
def argsCheckB (C : CheckerT) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Expr Nat → List (Expr Nat) → Bool
  | .sort _, [] => true
  | .pi A B, a :: as => (C.check E n Γ a A).isSome && argsCheckB C E n Γ (instantiate0 a B) as
  | _, _ => false

def argsTyT_of_check {C : CheckerT} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (T : Expr Nat) → (as : List (Expr Nat)) → argsCheckB C E n Γ T as = true → ArgsTyT E n Γ T as
  | .sort l, [], _ => .nil l
  | .pi A B, a :: as, h => by
      simp only [argsCheckB, Bool.and_eq_true] at h
      exact .cons A B a as (C.der h.1) (argsTyT_of_check _ as h.2)
  | .bvar _, [], h => absurd h (by simp [argsCheckB])
  | .const _ _, [], h => absurd h (by simp [argsCheckB])
  | .app _ _, [], h => absurd h (by simp [argsCheckB])
  | .lam _ _, [], h => absurd h (by simp [argsCheckB])
  | .pi _ _, [], h => absurd h (by simp [argsCheckB])
  | .letE _ _ _, [], h => absurd h (by simp [argsCheckB])
  | .lit _, [], h => absurd h (by simp [argsCheckB])
  | .bvar _, _ :: _, h => absurd h (by simp [argsCheckB])
  | .sort _, _ :: _, h => absurd h (by simp [argsCheckB])
  | .const _ _, _ :: _, h => absurd h (by simp [argsCheckB])
  | .app _ _, _ :: _, h => absurd h (by simp [argsCheckB])
  | .lam _ _, _ :: _, h => absurd h (by simp [argsCheckB])
  | .letE _ _ _, _ :: _, h => absurd h (by simp [argsCheckB])
  | .lit _, _ :: _, h => absurd h (by simp [argsCheckB])

/-- a constructor's fields checked in the plain context. -/
def fieldsCheckB (C : CheckerT) (E : ResolvedEnv) (n : Nat) (idxTel : Nat → Expr Nat) :
    LCtx → Nat → List FieldT → List (Expr Nat) → Bool
  | Γ, k, [], res => argsCheckB C E n Γ (idxTel k) res
  | Γ, k, .plain D u :: fs, res =>
      (C.check E n Γ D (.sort u)).isSome && fieldsCheckB C E n idxTel (.assumption D :: Γ) (k + 1) fs res
  | Γ, k, .drec idx :: fs, res => argsCheckB C E n Γ (idxTel k) idx && fieldsCheckB C E n idxTel Γ k fs res
  | Γ, k, .drecD _ idx :: fs, res => argsCheckB C E n Γ (idxTel k) idx && fieldsCheckB C E n idxTel Γ k fs res

def fieldsTyT_of_check {C : CheckerT} {E : ResolvedEnv} {n : Nat} {idxTel : Nat → Expr Nat} :
    (Γ : LCtx) → (k : Nat) → (fs : List FieldT) → (res : List (Expr Nat)) →
    fieldsCheckB C E n idxTel Γ k fs res = true → FieldsTyT E n idxTel Γ k fs res
  | Γ, k, [], res, h => .nil Γ k res (argsTyT_of_check _ res h)
  | Γ, k, .plain D u :: fs, res, h => by
      simp only [fieldsCheckB, Bool.and_eq_true] at h
      exact .plain Γ k D u fs res (C.der h.1) (fieldsTyT_of_check _ _ fs res h.2)
  | Γ, k, .drec idx :: fs, res, h => by
      simp only [fieldsCheckB, Bool.and_eq_true] at h
      exact .drec Γ k idx fs res (argsTyT_of_check _ idx h.1) (fieldsTyT_of_check _ _ fs res h.2)
  | Γ, k, .drecD D idx :: fs, res, h => by
      simp only [fieldsCheckB, Bool.and_eq_true] at h
      exact .drecD Γ k D idx fs res (argsTyT_of_check _ idx h.1) (fieldsTyT_of_check _ _ fs res h.2)

/-- the δ-reached evidence check (R-NoDeltaRec-4c): each `.drecD D idx` field's SURFACE domain
    types in the family's scope at the family's sort, in the plain context of the fields before
    it — the checker's `check` — and converts there to the family application at the parameters
    and the field's own indices — `conv`; and the indices are level-bounded at the family's
    arity (they occur in no stored type). `pre` accumulates the fields already walked, the
    `drecD` binder leaving the plain context as `drec` does. -/
def drecDsCheckB (C : CheckerT) (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (params : List (Expr Nat × Level)) (u : Level) : List FieldT → List FieldT → Bool
  | _, [] => true
  | pre, .plain D w :: fs => drecDsCheckB C E f fm params u (pre ++ [.plain D w]) fs
  | pre, .drec idx :: fs => drecDsCheckB C E f fm params u (pre ++ [.drec idx]) fs
  | pre, .drecD D idx :: fs =>
      (C.check (extendEnv E f fm) fm.arity (plainCtxT pre (telCtxT params)) D (.sort u)).isSome &&
      (C.conv (extendEnv E f fm) fm.arity (plainCtxT pre (telCtxT params)) D
        (foldApps (.const f (canonLevels fm.arity))
          ((policyLocals params.length).map (lift 0 (plainIdxT pre 0)) ++ idx))).isSome &&
      idx.all (exprLevelsBounded fm.arity) &&
      drecDsCheckB C E f fm params u (pre ++ [.drecD D idx]) fs

/-! ## (3) the test -/

/-- a constructor's view syntax: mirrors, fields in the plain context, result indices, and the sort
    of its type in ConstructorScope. -/
structure CtorSkelT : Type where
  mirrors : List (Expr Nat × Level)
  fields : List FieldT
  res : List (Expr Nat)
  u : Level

/-- a group's view syntax: the family's parameters, indices and sort, the constructors in candidate
    order, the recursor's elimination policy and the sort of its type in DerivationScope. -/
structure GroupSkelT : Type where
  params : List (Expr Nat × Level)
  indices : List (Expr Nat × Level)
  sort : Level
  ctors : List CtorSkelT
  elim : EliminationPolicy
  urec : Level

/-- the family's index telescope read from a skeleton. -/
def GroupSkelT.idxTel (sk : GroupSkelT) : Expr Nat := policyPi (sk.indices.map Prod.fst) (.sort sk.sort)

/-- the family: its stored type is the telescope, its sort uniform, its domains typed in the base,
    and the domains' recorded sorts level-bounded at the family's arity (R-NoDeltaRec-4d-iii: the
    erased telescope `policyPi` carries no binder levels, so the bound the copy's family member
    needs is read here, off the skeleton). -/
def famCheckB (C : CheckerT) (E : ResolvedEnv) (fm : CheckedMember) (sk : GroupSkelT) : Bool :=
  decide (fm.mtype = policyPi ((sk.params ++ sk.indices).map Prod.fst) (.sort sk.sort)) &&
  (levelIsZero sk.sort || levelNeverZero sk.sort) &&
  telCheckB C E fm.arity [] (sk.params ++ sk.indices) &&
  (sk.params ++ sk.indices).all (fun d => levelBounded fm.arity d.2)

/-- a plain field's level within the family's sort (05 §7), by the checker's level order. -/
def univCheckB (C : CheckerT) (s : Level) : FieldT → Bool
  | .plain _ u => levelIsZero s || (levelNeverZero s && C.levelLe u s)
  | .drec _ => true
  | .drecD _ _ => true

/-- a constructor's mirrors against the family's parameters: each converted by the checker in the
    parameters before it, at a level `decEqN` equates (05 §6.1). -/
def mirrorsCheckB (C : CheckerT) (E : ResolvedEnv) (n : Nat) :
    LCtx → List (Expr Nat × Level) → List (Expr Nat × Level) → Bool
  | _, [], [] => true
  | Γ, (M, um) :: ms, (P, up) :: ps =>
      (C.conv E n Γ M P).isSome && decEqN um up && mirrorsCheckB C E n (.assumption P :: Γ) ms ps
  | _, _, _ => false

def mirrorsConvT_of_check {C : CheckerT} {E : ResolvedEnv} {n : Nat} :
    (Γ : LCtx) → (ms ps : List (Expr Nat × Level)) → mirrorsCheckB C E n Γ ms ps = true →
    MirrorsConvT E n Γ ms ps
  | Γ, [], [], _ => .nil Γ
  | Γ, (M, um) :: ms, (P, up) :: ps, h => by
      simp only [mirrorsCheckB, Bool.and_eq_true] at h
      exact .cons Γ M um P up ms ps ((C.conv E n Γ M P).get h.1.1) (decEqN_sound um up h.1.2)
        (mirrorsConvT_of_check _ ms ps h.2)
  | _, [], _ :: _, h => absurd h (by simp [mirrorsCheckB])
  | _, _ :: _, [], h => absurd h (by simp [mirrorsCheckB])

/-- one constructor: its member checks, its type typed in ConstructorScope, its stored type BUILT
    from its view, its mirrors converted to the family's parameters, the fields typed in the plain
    context in the base, each plain field's level within the family's sort. -/
def ctorCheckB (C : CheckerT) (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (sk : GroupSkelT)
    (c : Nat × CheckedMember) (k : CtorSkelT) : Bool :=
  decide (c.2.mclass = .constructorM) && decide (c.2.body = none) && decide (c.2.arity = fm.arity) &&
  decide (lift 0 1 c.2.mtype = c.2.mtype) && exprLevelsBounded c.2.arity c.2.mtype &&
  (C.check (extendEnv E f fm) c.2.arity [] c.2.mtype (.sort k.u)).isSome &&
  decide (c.2.mtype = ctorTypeT f (canonLevels fm.arity) k.mirrors k.fields k.res) &&
  mirrorsCheckB C E fm.arity [] k.mirrors sk.params &&
  fieldsCheckB C E fm.arity (fun j => lift 0 j sk.idxTel) (telCtxT sk.params) 0 k.fields k.res &&
  k.fields.all (univCheckB C sk.sort) && drecDsCheckB C E f fm sk.params sk.sort [] k.fields

def ctorsCheckB (C : CheckerT) (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (sk : GroupSkelT) :
    List (Nat × CheckedMember) → List CtorSkelT → Bool
  | [], [] => true
  | c :: cs, k :: ks => ctorCheckB C E f fm sk c k && ctorsCheckB C E f fm sk cs ks
  | _, _ => false

/-- the minors' data the test reads: reference, fields, result indices, in candidate order. -/
def skelMinorData : List (Nat × CheckedMember) → List CtorSkelT → List MinorDataT
  | c :: cs, k :: ks => (c.1, k.fields, k.res) :: skelMinorData cs ks
  | _, _ => []

/-- a unit group (one constructor without fields, no index) and a struct group (one constructor, no
    index, at least one field, every field plain with a level zero at every valuation), decided. -/
def unitSkelB (sk : GroupSkelT) : Bool :=
  decide (sk.ctors.length = 1) && sk.indices.isEmpty && sk.ctors.all (fun k => k.fields.isEmpty)

def structFieldB : FieldT → Bool
  | .plain _ u => levelIsZero u
  | .drec _ => false
  | .drecD _ _ => false

def structSkelB (sk : GroupSkelT) : Bool :=
  decide (sk.ctors.length = 1) && sk.indices.isEmpty &&
    sk.ctors.all (fun k => !k.fields.isEmpty && k.fields.all structFieldB)

/-- the two profiles, decided: (O2) by the checker's level order, (O1) on the views. -/
def profileCheckB (C : CheckerT) (sk : GroupSkelT) : Bool :=
  sk.indices.all (fun d => levelIsZero sk.sort || C.levelLe d.2 sk.sort) &&
  (decide (sk.elim = .propOnly) || !levelIsZero sk.sort || sk.ctors.isEmpty || unitSkelB sk || structSkelB sk)

/-- the recursor: its member checks, its stored type the views' recursor type, typed in
    DerivationScope. -/
def recCheckB (C : CheckerT) (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) (sk : GroupSkelT) : Bool :=
  decide (rm.mclass = .recursorM) && decide (rm.body = none) &&
  decide (rm.arity = policyRecursorArity fm.arity sk.elim) &&
  decide (lift 0 1 rm.mtype = rm.mtype) && exprLevelsBounded rm.arity rm.mtype &&
  decide (rm.mtype = recTypeT f (canonLevels fm.arity) sk.params sk.indices
    (policyMotiveLevel fm.arity sk.elim) (skelMinorData ctors sk.ctors)) &&
  (C.check (groupEnvT E f fm ctors.reverse) rm.arity [] rm.mtype (.sort sk.urec)).isSome &&
  decide (rr = f + 1 + ctors.length)

/-- THE SCOPE TEST at one group, with a checker. -/
def groupCheckB (C : CheckerT) (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) (sk : GroupSkelT) : Bool :=
  famCheckB C E fm sk && ctorsCheckB C E f fm sk ctors sk.ctors &&
  decide (ctors.map Prod.fst = List.range' (f + 1) ctors.length) &&
  recCheckB C E f fm ctors rr rm sk && profileCheckB C sk

/-! ## (4) the views built from a passing test -/

theorem uniformProp_of_levelIsZero {l : Level} (h : levelIsZero l = true) : UniformProp l :=
  (levelUniformZero_iff l).mp h

def famViewT_of_check {C : CheckerT} {E : ResolvedEnv} {fm : CheckedMember} (sk : GroupSkelT)
    (h : famCheckB C E fm sk = true) : FamViewT fm where
  params := sk.params
  indices := sk.indices
  sort := sk.sort
  stored := by
    simp only [famCheckB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  profile := by
    simp only [famCheckB, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.1.1.2 with h0 | hp
    · exact Or.inl (uniformProp_of_levelIsZero h0)
    · exact Or.inr ((levelUniformPositive_iff _).mp hp)

theorem closed_of_check {e : Expr Nat} (h : lift 0 1 e = e) (k : Nat) : lift k 1 e = e :=
  lift_closed_gen e 0 h k 1 (Nat.zero_le k)

theorem ctorCheckB_spec {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {sk : GroupSkelT}
    {c : Nat × CheckedMember} {k : CtorSkelT} (h : ctorCheckB C E f fm sk c k = true) :
    c.2.mclass = .constructorM ∧ c.2.body = none ∧ c.2.arity = fm.arity ∧
    lift 0 1 c.2.mtype = c.2.mtype ∧ exprLevelsBounded c.2.arity c.2.mtype = true ∧
    (C.check (extendEnv E f fm) c.2.arity [] c.2.mtype (.sort k.u)).isSome = true ∧
    c.2.mtype = ctorTypeT f (canonLevels fm.arity) k.mirrors k.fields k.res ∧
    mirrorsCheckB C E fm.arity [] k.mirrors sk.params = true ∧
    fieldsCheckB C E fm.arity (fun j => lift 0 j sk.idxTel) (telCtxT sk.params) 0 k.fields k.res = true ∧
    k.fields.all (univCheckB C sk.sort) = true ∧
    drecDsCheckB C E f fm sk.params sk.sort [] k.fields = true := by
  simp only [ctorCheckB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- the δ-evidence a passing check locates at any `drecD` position. -/
theorem drecDsCheckB_at {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {params : List (Expr Nat × Level)} {u : Level} {D : Expr Nat} {idx : List (Expr Nat)}
    {fsRest : List FieldT} :
    (pre fsMid : List FieldT) →
    drecDsCheckB C E f fm params u pre (fsMid ++ FieldT.drecD D idx :: fsRest) = true →
    (C.check (extendEnv E f fm) fm.arity (plainCtxT (pre ++ fsMid) (telCtxT params)) D
      (.sort u)).isSome = true ∧
    (C.conv (extendEnv E f fm) fm.arity (plainCtxT (pre ++ fsMid) (telCtxT params)) D
      (foldApps (.const f (canonLevels fm.arity))
        ((policyLocals params.length).map (lift 0 (plainIdxT (pre ++ fsMid) 0)) ++ idx))).isSome
      = true ∧
    ∀ x ∈ idx, exprLevelsBounded fm.arity x = true
  | pre, [], h => by
      simp only [List.nil_append, drecDsCheckB, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨⟨⟨hc, hcv⟩, hb⟩, _⟩ := h
      rw [List.append_nil]
      exact ⟨hc, hcv, hb⟩
  | pre, f' :: fsMid, h => by
      rw [show pre ++ (f' :: fsMid) = (pre ++ [f']) ++ fsMid by
        rw [← List.singleton_append, List.append_assoc]]
      cases f' with
      | plain D₀ w =>
          exact drecDsCheckB_at (pre ++ [.plain D₀ w]) fsMid (by simpa only [drecDsCheckB] using h)
      | drec idx₀ =>
          exact drecDsCheckB_at (pre ++ [.drec idx₀]) fsMid (by simpa only [drecDsCheckB] using h)
      | drecD D₀ idx₀ =>
          exact drecDsCheckB_at (pre ++ [.drecD D₀ idx₀]) fsMid (by
            simp only [drecDsCheckB, Bool.and_eq_true] at h; exact h.2)

/-- the view's `drecD` evidence, read off the check's `drecDsCheckB` conjunct. -/
theorem drecDTypedT_of_check {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {sk : GroupSkelT} {hf : famCheckB C E fm sk = true} {c : Nat × CheckedMember} {k : CtorSkelT}
    (h : ctorCheckB C E f fm sk c k = true) :
    DrecDTypedT E f fm (famViewT_of_check sk hf) k.fields := by
  intro fsPre D idx fsRest hfs
  obtain ⟨hc, hcv, hb⟩ := drecDsCheckB_at [] fsPre (hfs ▸ (ctorCheckB_spec h).2.2.2.2.2.2.2.2.2.2)
  simp only [List.nil_append] at hc hcv
  exact ⟨⟨C.der hc⟩, ⟨(C.conv _ _ _ _ _).get hcv⟩, hb⟩

/-- one constructor built from a passing check, against the family view read from the skeleton. -/
def groupCtorT_of_check {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} (sk : GroupSkelT)
    (hf : famCheckB C E fm sk = true) (c : Nat × CheckedMember) (k : CtorSkelT)
    (h : ctorCheckB C E f fm sk c k = true) : GroupCtorT E f fm (famViewT_of_check sk hf) where
  ref := c.1
  member := c.2
  hcls := (ctorCheckB_spec h).1
  hnobody := (ctorCheckB_spec h).2.1
  harity := (ctorCheckB_spec h).2.2.1
  hclT := closed_of_check (ctorCheckB_spec h).2.2.2.1
  u := k.u
  hT := C.der (ctorCheckB_spec h).2.2.2.2.2.1
  hlvl := (ctorCheckB_spec h).2.2.2.2.1
  view :=
    { mirrors := k.mirrors
      fields := k.fields
      res := k.res
      stored := (ctorCheckB_spec h).2.2.2.2.2.2.1
      mirrorsConv := mirrorsConvT_of_check [] _ _ (ctorCheckB_spec h).2.2.2.2.2.2.2.1
      typed := fieldsTyT_of_check _ _ _ _ (ctorCheckB_spec h).2.2.2.2.2.2.2.2.1
      univ := fun D u hD => by
        have hu := List.all_eq_true.mp (ctorCheckB_spec h).2.2.2.2.2.2.2.2.2.1 _ hD
        simp only [univCheckB, Bool.or_eq_true, Bool.and_eq_true] at hu
        rcases hu with h0 | ⟨hp, hg⟩
        · exact Or.inl (uniformProp_of_levelIsZero h0)
        · exact Or.inr ⟨(levelUniformPositive_iff _).mp hp, C.levelLe_sound _ _ hg⟩
      drecD_typed := drecDTypedT_of_check h }

/-- the constructors in candidate order, built from passing checks: their entries are the group's, and
    their minors' data and fields the skeleton's. -/
def ctorsOfCheck {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} (sk : GroupSkelT)
    (hf : famCheckB C E fm sk = true) :
    (cs : List (Nat × CheckedMember)) → (ks : List CtorSkelT) → ctorsCheckB C E f fm sk cs ks = true →
    { l : List (GroupCtorT E f fm (famViewT_of_check sk hf)) //
      l.map GroupCtorT.entry = cs ∧ l.map GroupCtorT.minorData = skelMinorData cs ks ∧
      l.map (fun c => c.view.fields) = ks.map CtorSkelT.fields }
  | [], [], _ => ⟨[], rfl, rfl, rfl⟩
  | c :: cs, k :: ks, h =>
      have h' : ctorCheckB C E f fm sk c k = true ∧ ctorsCheckB C E f fm sk cs ks = true := by
        simpa only [ctorsCheckB, Bool.and_eq_true] using h
      let r := ctorsOfCheck sk hf cs ks h'.2
      ⟨groupCtorT_of_check sk hf c k h'.1 :: r.1,
        by rw [List.map_cons, r.2.1]; rfl,
        by rw [List.map_cons, r.2.2.1]; rfl,
        by rw [List.map_cons, r.2.2.2]; rfl⟩
  | [], _ :: _, h => absurd h (by simp [ctorsCheckB])
  | _ :: _, [], h => absurd h (by simp [ctorsCheckB])

theorem recCheckB_spec {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} {sk : GroupSkelT}
    (h : recCheckB C E f fm ctors rr rm sk = true) :
    rm.mclass = .recursorM ∧ rm.body = none ∧ rm.arity = policyRecursorArity fm.arity sk.elim ∧
    lift 0 1 rm.mtype = rm.mtype ∧ exprLevelsBounded rm.arity rm.mtype = true ∧
    rm.mtype = recTypeT f (canonLevels fm.arity) sk.params sk.indices
      (policyMotiveLevel fm.arity sk.elim) (skelMinorData ctors sk.ctors) ∧
    (C.check (groupEnvT E f fm ctors.reverse) rm.arity [] rm.mtype (.sort sk.urec)).isSome = true ∧
    rr = f + 1 + ctors.length := by
  simp only [recCheckB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- the recursor built from a passing check, over the constructors (the list's head added last). -/
def groupRecT_of_check {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} (sk : GroupSkelT)
    (hf : famCheckB C E fm sk = true) (l : List (GroupCtorT E f fm (famViewT_of_check sk hf)))
    (hentry : l.map GroupCtorT.entry = ctors) (hmd : l.map GroupCtorT.minorData = skelMinorData ctors sk.ctors)
    (h : recCheckB C E f fm ctors rr rm sk = true) : GroupRecT E f fm (famViewT_of_check sk hf) l.reverse where
  member := rm
  hcls := (recCheckB_spec h).1
  hnobody := (recCheckB_spec h).2.1
  elim := sk.elim
  harity := (recCheckB_spec h).2.2.1
  stored := by
    rw [(recCheckB_spec h).2.2.2.2.2.1, groupRecTypeT, List.reverse_reverse, hmd]
    rfl
  hclT := closed_of_check (recCheckB_spec h).2.2.2.1
  u := sk.urec
  hT := by
    rw [List.map_reverse, hentry]
    exact C.der (recCheckB_spec h).2.2.2.2.2.2.1
  hlvl := (recCheckB_spec h).2.2.2.2.1

theorem famCheckB_tel {C : CheckerT} {E : ResolvedEnv} {fm : CheckedMember} {sk : GroupSkelT}
    (h : famCheckB C E fm sk = true) : telCheckB C E fm.arity [] (sk.params ++ sk.indices) = true := by
  simp only [famCheckB, Bool.and_eq_true] at h
  exact h.1.2

/-- the skeleton's domain levels are bounded at the family's arity, by the family check. -/
theorem famCheckB_levels {C : CheckerT} {E : ResolvedEnv} {fm : CheckedMember} {sk : GroupSkelT}
    (h : famCheckB C E fm sk = true) : ∀ d ∈ sk.params ++ sk.indices, levelBounded fm.arity d.2 = true := by
  simp only [famCheckB, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2

theorem groupCheckB_spec {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} {sk : GroupSkelT}
    (h : groupCheckB C E f fm ctors rr rm sk = true) :
    famCheckB C E fm sk = true ∧ ctorsCheckB C E f fm sk ctors sk.ctors = true ∧
    ctors.map Prod.fst = List.range' (f + 1) ctors.length ∧ recCheckB C E f fm ctors rr rm sk = true ∧
    profileCheckB C sk = true := by
  simp only [groupCheckB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- (O2) and (O1) on the views built from a passing test. -/
theorem groupProfileT_of_check {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} (sk : GroupSkelT)
    (hf : famCheckB C E fm sk = true) (l : List (GroupCtorT E f fm (famViewT_of_check sk hf)))
    (hentry : l.map GroupCtorT.entry = ctors) (hmd : l.map GroupCtorT.minorData = skelMinorData ctors sk.ctors)
    (hfs : l.map (fun c => c.view.fields) = sk.ctors.map CtorSkelT.fields)
    (h : recCheckB C E f fm ctors rr rm sk = true) (hp : profileCheckB C sk = true) :
    GroupProfileT (groupRecT_of_check sk hf l hentry hmd h) := by
  simp only [profileCheckB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  obtain ⟨hO2, hO1⟩ := hp
  have hlen : l.length = sk.ctors.length := by
    have := congrArg List.length hfs
    simpa only [List.length_map] using this
  -- every constructor's fields are some skeleton constructor's
  have hmem : ∀ c ∈ l, ∃ k ∈ sk.ctors, c.view.fields = k.fields := by
    intro c hc
    have : c.view.fields ∈ sk.ctors.map CtorSkelT.fields := hfs ▸ List.mem_map_of_mem _ hc
    obtain ⟨k, hk, hkf⟩ := List.mem_map.mp this
    exact ⟨k, hk, hkf.symm⟩
  refine ⟨?_, ?_⟩
  · intro v hv ρ x y hx hy hy0
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    have hd' := List.all_eq_true.mp hO2 d hd
    simp only [Bool.or_eq_true] at hd'
    have hy' : eval ρ sk.sort = some y := hy
    rcases hd' with h0 | hg
    · have hz := (levelIsZero_iff _).mp h0 ρ
      rw [hy'] at hz
      have hy00 : y = 0 := Option.some.inj hz
      omega
    · have := C.levelLe_sound d.2 sk.sort hg ρ x y hx hy'
      omega
  · intro hprop hne hnu hns
    show sk.elim = .propOnly
    rcases hO1 with (((hpo | hnz) | hemp) | hu) | hs
    · exact hpo
    · have hz : levelIsZero sk.sort = true := (levelUniformZero_iff sk.sort).mpr hprop
      rw [hnz] at hz
      exact absurd hz Bool.false_ne_true
    · apply absurd _ hne
      rw [List.isEmpty_iff] at hemp
      rw [hemp, List.length_nil, List.length_eq_zero] at hlen
      rw [hlen]; rfl
    · apply absurd _ hnu
      simp only [unitSkelB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true] at hu
      obtain ⟨⟨h1, h2⟩, h3⟩ := hu
      refine ⟨by rw [List.length_reverse, hlen, h1], h2, fun c hc => ?_⟩
      obtain ⟨k, hk, hkf⟩ := hmem c (List.mem_reverse.mp hc)
      rw [hkf]
      exact h3 k hk
    · apply absurd _ hns
      simp only [structSkelB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
        Bool.not_eq_true'] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      refine ⟨by rw [List.length_reverse, hlen, h1], h2, fun c hc => ?_⟩
      obtain ⟨k, hk, hkf⟩ := hmem c (List.mem_reverse.mp hc)
      rw [hkf]
      obtain ⟨hne', hall⟩ := h3 k hk
      refine ⟨fun he => by rw [he] at hne'; exact absurd hne' (by decide), fun F hF => ?_⟩
      have hF' := hall F hF
      cases F with
      | plain D u => exact ⟨D, u, rfl, uniformProp_of_levelIsZero hF'⟩
      | drec _ => simp [structFieldB] at hF'
      | drecD _ _ => simp [structFieldB] at hF'

/-- `ctorsOfCheck`'s third map-equality, member-by-member: a produced view's fields are its
    skeleton's. -/
theorem viewFields_of_ctorsOfCheck {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {sk : GroupSkelT} {hf : famCheckB C E fm sk = true} {cs : List (Nat × CheckedMember)}
    {ks : List CtorSkelT} {h : ctorsCheckB C E f fm sk cs ks = true}
    {c : GroupCtorT E f fm (famViewT_of_check sk hf)}
    (hc : c ∈ (ctorsOfCheck sk hf cs ks h).1) :
    ∃ k ∈ ks, c.view.fields = k.fields := by
  have hm := (ctorsOfCheck sk hf cs ks h).2.2.2
  obtain ⟨k, hk, hfk⟩ := List.mem_map.mp (hm ▸ List.mem_map_of_mem _ hc)
  exact ⟨k, hk, hfk.symm⟩

/-- THE GROUP IN THE COPY'S SCOPE, from a passing test: no view written by hand, every typing the
    checker's. The copy-side bridge keeps its `drecD`-free gate — `hsnd` is read off the skeleton
    (the scope test itself certifies `drecD` evidence; `hsnd` is the `EnvNormEraseA` gate — the
    erased↔annotated lift needs normalized and stored constructor types erasing equally, which a
    `.drecD` member breaks (`drCtorMemberA_diverge`)). -/
def groupInScopeT_of_check {C : CheckerT} {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} (sk : GroupSkelT)
    (hsndK : ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false)
    (h : groupCheckB C E f fm ctors rr rm sk = true) : GroupInScopeT E f fm ctors rr rm :=
  let hs := groupCheckB_spec h
  let r := ctorsOfCheck (f := f) sk hs.1 ctors sk.ctors hs.2.1
  have hl : r.1.length = ctors.length := by
    have := congrArg List.length r.2.1
    rwa [List.length_map] at this
  { fv := famViewT_of_check sk hs.1
    htel := telTyT_of_check [] _ (famCheckB_tel hs.1)
    cs := r.1.reverse
    hctors := by rw [List.map_reverse, List.reverse_reverse, r.2.1]
    hlayout := by
      rw [List.reverse_reverse, List.length_reverse, hl]
      have hm : List.map GroupCtorT.ref r.1 = List.map Prod.fst (List.map GroupCtorT.entry r.1) := by
        rw [List.map_map]; rfl
      exact hm.trans ((congrArg (List.map Prod.fst) r.2.1).trans hs.2.2.1)
    grec := groupRecT_of_check sk hs.1 r.1 r.2.1 r.2.2.1 hs.2.2.2.1
    hrr := (recCheckB_spec hs.2.2.2.1).2.2.2.2.2.2.2.trans (by rw [List.length_reverse, hl])
    hrm := rfl
    hprof := groupProfileT_of_check sk hs.1 r.1 r.2.1 r.2.2.1 r.2.2.2 hs.2.2.2.1 hs.2.2.2.2
    hpb := famCheckB_levels hs.1
    hsnd := fun c hc d hd => by
      rw [List.mem_reverse] at hc
      obtain ⟨k, hk, hfk⟩ := viewFields_of_ctorsOfCheck hc
      rw [hfk] at hd; exact hsndK k hk d hd }

/-! ## (5) along a derivation, and the three rows -/

/-- THE SCOPE TEST along a derivation: at each group, a checker and a view skeleton that pass the
    test. With a computable checker the test at a group is decided by evaluation. -/
def EnvWfT.ScopeCheck : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => hE.ScopeCheck
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.ScopeCheck
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => hE.ScopeCheck
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.ScopeCheck
  | _, .group E f fm ctors rr rm _ hE _ _ _ _ =>
      hE.ScopeCheck ∧ ∃ (C : CheckerT) (sk : GroupSkelT),
        groupCheckB C E f fm ctors rr rm sk = true ∧
        ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false

/-- W-2 (b): THE COPY'S SCOPE FROM THE TEST. A derivation passing the test is in the copy's scope; its
    views are built from the members, every typing by the checker. -/
theorem EnvWfT.inScope_of_scopeCheck : {E : ResolvedEnv} → (hW : EnvWfT E) → hW.ScopeCheck → hW.InScope
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ hE _ _ _ _, h => hE.inScope_of_scopeCheck h
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, h => hE.inScope_of_scopeCheck h
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, h => hE.inScope_of_scopeCheck h
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, h => hE.inScope_of_scopeCheck h
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, h => by
      obtain ⟨h1, _, sk, hsk⟩ := h
      exact ⟨hE.inScope_of_scopeCheck h1, ⟨groupInScopeT_of_check sk hsk.2 hsk.1⟩⟩

open Ann in
/-- the copy's environment over a derivation that passes the test, with no other hypothesis. -/
theorem annEnvA_of_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = E ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_semPrefix hW (hW.inScope_of_scopeCheck hC)).imp fun _ h => ⟨h.1, h.2.1⟩

/-- ROW 1 over every `EnvWfT` environment that passes the test. -/
theorem sortConvCharT_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l₁ l₂ : Level} {T : Expr Nat}
    (h : ConvT E n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ :=
  Ann.sortConvCharT_semPrefix hW (hW.inScope_of_scopeCheck hC) hΓ h

/-- ROW 2 over every `EnvWfT` environment that passes the test. -/
theorem piConvInjT_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A' B' T : Expr Nat} (h : ConvT E n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  Ann.piConvInjT_semPrefix hW (hW.inScope_of_scopeCheck hC) hΓ h

/-- ROW 3 over every `EnvWfT` environment that passes the test. -/
theorem famAppConvInjT_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (h : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧ ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' :=
  Ann.famAppConvInjT_semPrefix hW (hW.inScope_of_scopeCheck hC) hΓ hm hind h

/-- THE THREE ROWS IN THE LEDGER'S FORM (E-TyConvRows-3: a type-conversion chain as premise, existence
    conclusions; M3-b's `TypedRowsWf`) over every `EnvWfT` environment that passes the test. -/
theorem typedRowsWf_of_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) (n : Nat) :
    TypedRowsWf E n :=
  Ann.typedRowsWf_of_envWfT_semPrefix hW (hW.inScope_of_scopeCheck hC) n

/-! ## (6) reading a skeleton off the members

The reader is not trusted: the test re-checks everything it returns. It reads the plain fields first
and the directly recursive fields literally at the parameter locals, with no index. -/

/-- every leading Π binder. -/
def peelPisAll : Expr Nat → List (Expr Nat) × Expr Nat
  | .pi A B => ((A :: (peelPisAll B).1), (peelPisAll B).2)
  | e => ([], e)

/-- a telescope's sorts by the checker. -/
def telLevels? (C : CheckerT) (E : ResolvedEnv) (n : Nat) : LCtx → List (Expr Nat) → Option (List Level)
  | _, [] => some []
  | Γ, D :: ds =>
      match C.sortOf E n Γ D with
      | some u => (telLevels? C E n (.assumption D :: Γ) ds).map (u :: ·)
      | none => none

/-- the full context's variable `k` in the plain context; `recs` flags the fields so far, the latest
    first (`true`: directly recursive, absent from the plain context). -/
def plainVar? : List Bool → Nat → Option Nat
  | [], k => some k
  | true :: _, 0 => none
  | false :: _, 0 => some 0
  | true :: rs, k + 1 => plainVar? rs k
  | false :: rs, k + 1 => (plainVar? rs k).map (· + 1)

/-- a term of the full context moved into the plain context, when it names no recursive field. -/
def unshift? (recs : List Bool) : Nat → Expr Nat → Option (Expr Nat)
  | c, .bvar k => if k < c then some (.bvar k) else (plainVar? recs (k - c)).map (fun i => .bvar (i + c))
  | _, .sort l => some (.sort l)
  | _, .const r ls => some (.const r ls)
  | c, .app f x =>
      match unshift? recs c f, unshift? recs c x with
      | some f', some x' => some (.app f' x')
      | _, _ => none
  | c, .lam a b =>
      match unshift? recs c a, unshift? recs (c + 1) b with
      | some a', some b' => some (.lam a' b')
      | _, _ => none
  | c, .pi a b =>
      match unshift? recs c a, unshift? recs (c + 1) b with
      | some a', some b' => some (.pi a' b')
      | _, _ => none
  | c, .letE a v b =>
      match unshift? recs c a, unshift? recs c v, unshift? recs (c + 1) b with
      | some a', some v', some b' => some (.letE a' v' b')
      | _, _, _ => none
  | _, .lit t => some (.lit t)

/-- the index arguments of a directly recursive field: the family at its canonical levels with the
    parameter locals first. -/
def recIdx? (f : Nat) (ls : List Level) (np j : Nat) (D : Expr Nat) : Option (List (Expr Nat)) :=
  match appsSpine D with
  | (.const r ls', args) =>
      if r = f ∧ ls' = ls ∧ args.take np = policyParameterLocals np j then some (args.drop np) else none
  | _ => none

/-- a constructor's fields in the plain context: a directly recursive field's indices and a plain
    field's domain moved there, a plain field at the checker's sort. A field whose domain does not
    head-match the family but whose δ-normal form does (`fuel`-bounded weak-head reduction through
    transparent heads) is recorded `.drecD` — surface domain kept — agreeing with admission's
    δ-reached read (R-NoDeltaRec-4b). The scope test certifies it (`drecDsCheckB`, -4c); the
    copy-side bridge keeps its `drecD`-free gate (`GroupInScopeT.hsnd`). -/
def fieldsOf? (C : CheckerT) (E : ResolvedEnv) (n f : Nat) (ls : List Level) (np fuel : Nat) :
    LCtx → List Bool → List (Expr Nat) → Option (List FieldT)
  | _, _, [] => some []
  | Γ, recs, D :: ds =>
      match recIdx? f ls np recs.length D with
      | some idx' =>
          match idx'.mapM (unshift? recs 0) with
          | some idx => (fieldsOf? C E n f ls np fuel Γ (true :: recs) ds).map (.drec idx :: ·)
          | none => none
      | none =>
          match unshift? recs 0 D with
          | some D' =>
              match whnfFuel E fuel D with
              | some Dw =>
                  match recIdx? f ls np recs.length Dw with
                  | some idx' =>
                      match idx'.mapM (unshift? recs 0) with
                      | some idx =>
                          (fieldsOf? C E n f ls np fuel Γ (true :: recs) ds).map (.drecD D' idx :: ·)
                      | none => none
                  | none =>
                      match C.sortOf E n Γ D' with
                      | some u =>
                          (fieldsOf? C E n f ls np fuel (.assumption D' :: Γ) (false :: recs) ds).map
                            (.plain D' u :: ·)
                      | none => none
              | none =>
                  match C.sortOf E n Γ D' with
                  | some u =>
                      (fieldsOf? C E n f ls np fuel (.assumption D' :: Γ) (false :: recs) ds).map
                        (.plain D' u :: ·)
                  | none => none
          | none => none

def FieldT.isRec : FieldT → Bool
  | .drec _ => true
  | .drecD _ _ => true
  | .plain _ _ => false

def ctorSkel? (C : CheckerT) (E : ResolvedEnv) (fuel : Nat) (f : Nat) (fm : CheckedMember)
    (params : List (Expr Nat × Level)) (c : CheckedMember) : Option CtorSkelT :=
  match fieldsOf? C E fm.arity f (canonLevels fm.arity) params.length fuel (telCtxT params) []
      ((peelPisAll c.mtype).1.drop params.length),
    C.sortOf (extendEnv E f fm) c.arity [] c.mtype with
  | some fs, some u =>
      match ((appsSpine (peelPisAll c.mtype).2).2.drop params.length).mapM
          (unshift? (fs.reverse.map FieldT.isRec) 0) with
      | some res => some ⟨((peelPisAll c.mtype).1.take params.length).zip (params.map Prod.snd), fs, res, u⟩
      | none => none
  | _, _ => none

/-- a group's skeleton read off its members at `np` parameters. -/
def groupSkel? (C : CheckerT) (E : ResolvedEnv) (fuel : Nat) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rm : CheckedMember) (np : Nat) : Option GroupSkelT :=
  match (peelPisAll fm.mtype).2, telLevels? C E fm.arity [] (peelPisAll fm.mtype).1 with
  | .sort l, some lvls =>
      match ctors.mapM (fun c => ctorSkel? C E fuel f fm (((peelPisAll fm.mtype).1.zip lvls).take np) c.2),
          C.sortOf (groupEnvT E f fm ctors.reverse) rm.arity [] rm.mtype with
      | some ks, some ur =>
          some ⟨((peelPisAll fm.mtype).1.zip lvls).take np, ((peelPisAll fm.mtype).1.zip lvls).drop np, l, ks,
            if rm.arity = fm.arity + 1 then .anySort else .propOnly, ur⟩
      | _, _ => none
  | _, _ => none

end Rcic.Declarative

#print axioms Rcic.Declarative.lift_succ_lift_one
#print axioms Rcic.Declarative.SubstT.lift_up
#print axioms Rcic.Declarative.SubstT.lift_shift1
#print axioms Rcic.Declarative.lift_substT
#print axioms Rcic.Declarative.map_lift_succ_lift_one
#print axioms Rcic.Declarative.lift_ctorFieldsT
#print axioms Rcic.Declarative.lift_two_lift_two
#print axioms Rcic.Declarative.SubstT.lift_shift1_shift1
#print axioms Rcic.Declarative.map_lift_two_lift_two
#print axioms Rcic.Declarative.lift_minorFieldsT
#print axioms Rcic.Declarative.lift_one_acc
#print axioms Rcic.Declarative.lift_two_acc
#print axioms Rcic.Declarative.lift_one_one
#print axioms Rcic.Declarative.minorFromTelescope_ctorFieldsT
#print axioms Rcic.Declarative.policyPi_append
#print axioms Rcic.Declarative.ctorDomsT_length
#print axioms Rcic.Declarative.map_lift_succ_merge
#print axioms Rcic.Declarative.ctorFieldsT_policyPi
#print axioms Rcic.Declarative.policyLocals_map_lift
#print axioms Rcic.Declarative.ctorFieldTelescope_eq
#print axioms Rcic.Declarative.minorDomsT_length
#print axioms Rcic.Declarative.mapIdx_go_lift
#print axioms Rcic.Declarative.mapIdx_lift_eq_liftDomsT
#print axioms Rcic.Declarative.policyLocals_add
#print axioms Rcic.Declarative.policyLocals_map_lift_above
#print axioms Rcic.Declarative.policyParameterLocals_lift
#print axioms Rcic.Declarative.policyParameterLocals_length
#print axioms Rcic.Declarative.policyMajor_eq
#print axioms Rcic.Declarative.policyResult_eq
#print axioms Rcic.Declarative.policyMotiveType_eq
#print axioms Rcic.Declarative.policyRecursorType_eq
#print axioms Rcic.Declarative.derivedMinor_eq
#print axioms Rcic.Declarative.CheckerT.der
#print axioms Rcic.Declarative.synConv
#print axioms Rcic.Declarative.telTyT_of_check
#print axioms Rcic.Declarative.argsTyT_of_check
#print axioms Rcic.Declarative.fieldsTyT_of_check
#print axioms Rcic.Declarative.mirrorsConvT_of_check
#print axioms Rcic.Declarative.uniformProp_of_levelIsZero
#print axioms Rcic.Declarative.leN_of_geq
#print axioms Rcic.Declarative.famViewT_of_check
#print axioms Rcic.Declarative.closed_of_check
#print axioms Rcic.Declarative.ctorCheckB_spec
#print axioms Rcic.Declarative.groupCtorT_of_check
#print axioms Rcic.Declarative.ctorsOfCheck
#print axioms Rcic.Declarative.recCheckB_spec
#print axioms Rcic.Declarative.groupRecT_of_check
#print axioms Rcic.Declarative.famCheckB_tel
#print axioms Rcic.Declarative.groupCheckB_spec
#print axioms Rcic.Declarative.groupProfileT_of_check
#print axioms Rcic.Declarative.groupInScopeT_of_check
#print axioms Rcic.Declarative.EnvWfT.inScope_of_scopeCheck
#print axioms Rcic.Declarative.annEnvA_of_scopeCheck
#print axioms Rcic.Declarative.sortConvCharT_scopeCheck
#print axioms Rcic.Declarative.piConvInjT_scopeCheck
#print axioms Rcic.Declarative.famAppConvInjT_scopeCheck
#print axioms Rcic.Declarative.typedRowsWf_of_scopeCheck
