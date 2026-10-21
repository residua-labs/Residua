import rcic.RcicTypedInvert
import rcic.RcicIotaShapeAdapter
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec

/-!
# IA-018 / IA-020 on the typed root: the minor context map is sound, minor conclusions are typed
(tymig segment D)

05 §12: "Because IH binders are inserted, a `MinorContextMap` rewrites all later field types, result
indices, and constructor arguments into the expanded minor context. Copying old de Bruijn bytes
without this weakening map is invalid." The minor conclusion is `M rewritten_result_indices
(constructor params rewritten_fields)`. GM-IND-004 (`docs/rcic/GLOBAL_MUTANT_REGISTRY.md:57`):
"Minor-context IH insertion fails to shift later de Bruijn references."

On `main` the map is the `lift 0 1` that `minorFromTelescope` (`RcicIndGroupJudgment.lean:662`)
applies to the remaining telescope after a recursive field (the IH binder is inserted there), plus
the `lift 0 2` on the motive and the constructor accumulation. `derivedMinor` (`:688`) is the
derived minor premise, and `MinorPremisesMatch` (`:700`) says it IS the recursor's stored minor
domain. The statements live at the recursor's ADMISSION CELL: its elimination admission `a`,
`MinorPremisesMatch a`, and the cell's typing of the stored recursor type in DerivationScope.
`GroupMembersT.cons`'s `hT` (`RcicTypedEnv.lean:144`) carries exactly that typing.

* `hasTyT_policyPi_inv` (D1) — a sort-typed telescope `policyPi ds body` has every domain
  sort-typed in its prefix context and the body sort-typed under all of them. It iterates the typed
  Π-inversion `hasTyTInv_pi`, no row.
* `recursor_minorType_typed` — at the cell, every stored minor domain is sort-typed in its minor
  context `minorCtxT a i` (the parameters, the motive, and the earlier minors), read off
  `recursorType` with D1, Π-inversion at the motive, and D1 again.
* `IA018T_minor_context_map_sound` (D2) — every binder of every derived minor is sort-typed in its
  EXPANDED context. The binders are the fields as the map rewrites them and the inserted IH binders.
* `IA020T_minor_conclusions_typed` (D3) — every derived minor's conclusion (its non-Π tail
  `piTailOf`, the motive at the rewritten result indices applied to the constructor at the
  rewritten fields) is sort-typed in the full minor context.

Pins (D4): List's cell (`listGroupU`, cons: the IH is inserted and the constructor arguments are
shifted past it) and Vec's cell (`vecGroupU`, vcons: the result index `succ n` is shifted past the
IH too), with the cons conclusion and binder count by evaluation.

Tooth (GM-IND-004): `minorFromTelescopeNoShift` is `minorFromTelescope` with the shift of the
remaining telescope past the IH binder DROPPED. At Vec's vcons it computes a minor different from the
stored one (`decide`), so `MinorPremisesMatch` fails for it, while the real derivation matches.

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-! ## (1) D1: typed telescope inversion -/

theorem policyPrefixContext_cons_succ (A : Expr Nat) (ds : List (Expr Nat)) (i : Nat)
    (Γ : LCtx) :
    policyPrefixContext (A :: ds) (i + 1) ++ Γ =
      policyPrefixContext ds i ++ (LocalDecl.assumption A :: Γ) := by
  simp [policyPrefixContext, List.take_succ_cons, List.reverse_cons, List.map_append,
    List.append_assoc]

/-- D1: a sort-typed Π-telescope has every domain sort-typed in its prefix context and its body
    sort-typed under the whole telescope. Iterated `hasTyTInv_pi`; no row, no environment premise. -/
theorem hasTyT_policyPi_inv {E : ResolvedEnv} {n : Nat} :
    (ds : List (Expr Nat)) → {Γ : LCtx} → {body : Expr Nat} → {u : Level} →
    HasTyT E n Γ (policyPi ds body) (.sort u) →
    (∀ (i : Nat) (hi : i < ds.length), ∃ w,
        Nonempty (HasTyT E n (policyPrefixContext ds i ++ Γ) (ds[i]'hi) (.sort w))) ∧
    ∃ v, Nonempty (HasTyT E n (policyPrefixContext ds ds.length ++ Γ) body (.sort v))
  | [], Γ, body, u, h => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ⟨u, ⟨h⟩⟩⟩
  | A :: ds, Γ, body, u, h => by
      obtain ⟨uA, v, hA, hB, _⟩ := hasTyTInv_pi h rfl
      obtain ⟨hdoms, hbody⟩ := hasTyT_policyPi_inv ds hB
      refine ⟨fun i hi => ?_, ?_⟩
      · cases i with
        | zero => exact ⟨uA, ⟨hA⟩⟩
        | succ j =>
            obtain ⟨w, hw⟩ := hdoms j (Nat.lt_of_succ_lt_succ hi)
            refine ⟨w, ?_⟩
            rw [policyPrefixContext_cons_succ]
            exact hw
      · obtain ⟨w, hw⟩ := hbody
        refine ⟨w, ?_⟩
        show Nonempty (HasTyT E n (policyPrefixContext (A :: ds) (ds.length + 1) ++ Γ) body _)
        rw [policyPrefixContext_cons_succ]
        exact hw

/-- the maximal Π-peel reassembles the term. -/
theorem policyPi_piDomsOf_piTailOf : (e : Expr Nat) → policyPi (piDomsOf e) (piTailOf e) = e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .pi A B => by
      simp only [piDomsOf, piTailOf, policyPi]
      rw [policyPi_piDomsOf_piTailOf B]
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-! ## (2) the recursor cell's minor contexts -/

/-- the context of minor `i` inside the recursor type: the earlier minors, the motive, the
    parameters (innermost first). -/
def minorCtxT {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Nat) : LCtx :=
  policyPrefixContext a.minorTypes i ++
    (LocalDecl.assumption (policyMotiveType a.family a.policy) ::
      (policyPrefixContext a.family.parameters a.family.parameters.length ++ []))

/-- at the cell, every stored minor domain is sort-typed in its minor context: `recursorType`
    unfolds the stored type to the parameters, the motive and the minors; D1 at the parameters,
    Π-inversion at the motive, D1 at the minors. -/
theorem recursor_minorType_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) {u : Level}
    (hT : HasTyT E m.arity [] m.mtype (.sort u)) (i : Nat) (hi : i < a.minorTypes.length) :
    ∃ w, Nonempty (HasTyT E m.arity (minorCtxT a i) (a.minorTypes[i]'hi) (.sort w)) := by
  rw [a.recursorType] at hT
  dsimp only [policyRecursorType] at hT
  obtain ⟨_, ⟨v₁, ⟨hB₁⟩⟩⟩ := hasTyT_policyPi_inv _ hT
  obtain ⟨_, _, _, hRest, _⟩ := hasTyTInv_pi hB₁ rfl
  exact (hasTyT_policyPi_inv _ hRest).1 i hi

/-! ## (3) the rows -/

/-- IA-018's shape at constructor `i` of an admitted recursor: the derived minor exists, and every
    binder of it is sort-typed in its expanded minor context. -/
def MinorBindersTypedT {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) : Prop :=
  ∃ shapes fuel M, derivedMinor a i fuel shapes = some M ∧
    ∀ (j : Nat) (hj : j < (piDomsOf M).length), ∃ w,
      Nonempty (HasTyT E m.arity (policyPrefixContext (piDomsOf M) j ++ minorCtxT a i)
        ((piDomsOf M)[j]'hj) (.sort w))

/-- IA-020's shape at constructor `i`: the derived minor exists, and its conclusion (non-Π tail) is
    sort-typed in the full minor context. -/
def MinorConclTypedT {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) : Prop :=
  ∃ shapes fuel M, derivedMinor a i fuel shapes = some M ∧
    ∃ v, Nonempty (HasTyT E m.arity
      (policyPrefixContext (piDomsOf M) (piDomsOf M).length ++ minorCtxT a i)
      (piTailOf M) (.sort v))

/-- IA-018 typed: at an admitted recursor cell, every binder of every derived minor is sort-typed
    in its expanded minor context. The binders are the fields as the minor context map rewrites
    them, and the inserted IH binders. `MinorPremisesMatch` identifies the derived minor with the
    stored minor domain; the cell's typing of the stored recursor type does the rest. -/
theorem IA018T_minor_context_map_sound {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h12 : MinorPremisesMatch a) {u : Level}
    (hT : HasTyT E m.arity [] m.mtype (.sort u)) (i : Fin a.constructors.length) :
    MinorBindersTypedT a i := by
  unfold MinorBindersTypedT
  have hi : i.val < a.minorTypes.length := by rw [a.minorCount]; exact i.isLt
  obtain ⟨shapes, fuel, _, hd⟩ := h12 i
  obtain ⟨w, ⟨hM⟩⟩ := recursor_minorType_typed a hT i.val hi
  rw [List.getElem?_eq_getElem hi] at hd
  refine ⟨shapes, fuel, a.minorTypes[i.val]'hi, hd, ?_⟩
  have hM' : HasTyT E m.arity (minorCtxT a i) (policyPi (piDomsOf (a.minorTypes[i.val]'hi))
      (piTailOf (a.minorTypes[i.val]'hi))) (.sort w) := by
    rw [policyPi_piDomsOf_piTailOf]
    exact hM
  exact (hasTyT_policyPi_inv _ hM').1

/-- IA-020 typed: at an admitted recursor cell, every derived minor's conclusion (its non-Π tail)
    is sort-typed in the full minor context: the earlier minors, the motive, the parameters, and the
    minor's own fields and IH binders. -/
theorem IA020T_minor_conclusions_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h12 : MinorPremisesMatch a) {u : Level}
    (hT : HasTyT E m.arity [] m.mtype (.sort u)) (i : Fin a.constructors.length) :
    MinorConclTypedT a i := by
  unfold MinorConclTypedT
  have hi : i.val < a.minorTypes.length := by rw [a.minorCount]; exact i.isLt
  obtain ⟨shapes, fuel, _, hd⟩ := h12 i
  obtain ⟨w, ⟨hM⟩⟩ := recursor_minorType_typed a hT i.val hi
  rw [List.getElem?_eq_getElem hi] at hd
  refine ⟨shapes, fuel, a.minorTypes[i.val]'hi, hd, ?_⟩
  have hM' : HasTyT E m.arity (minorCtxT a i) (policyPi (piDomsOf (a.minorTypes[i.val]'hi))
      (piTailOf (a.minorTypes[i.val]'hi))) (.sort w) := by
    rw [policyPi_piDomsOf_piTailOf]
    exact hM
  exact (hasTyT_policyPi_inv _ hM').2

/-! ## (4) D4: pins at real recursor cells -/

/-- PIN (IA-018T, List's cons): the cons minor's binders (the head field, the tail field, the IH)
    sort-typed in the expanded context, at List's real recursor cell. -/
theorem pin_IA018T_listCons : MinorBindersTypedT listGroupU ⟨1, by decide⟩ :=
  IA018T_minor_context_map_sound listGroupU listMinorMatchU listRecTypeTyT.2 ⟨1, by decide⟩

/-- PIN (IA-020T, List's cons): the cons minor's conclusion `M (cons A x xs)` sort-typed in the full
    minor context. -/
theorem pin_IA020T_listCons : MinorConclTypedT listGroupU ⟨1, by decide⟩ :=
  IA020T_minor_conclusions_typed listGroupU listMinorMatchU listRecTypeTyT.2 ⟨1, by decide⟩

/-- PIN (IA-018T, Vec's vcons): three fields and the IH. The result index `succ n` sits past the IH. -/
theorem pin_IA018T_vecCons : MinorBindersTypedT vecGroupU ⟨1, by decide⟩ :=
  IA018T_minor_context_map_sound vecGroupU vecMinorMatchU vecRecTypeTyT.2 ⟨1, by decide⟩

/-- PIN (IA-020T, Vec's vcons): its conclusion `M (succ n) (vcons A n a v)` sort-typed in the full
    minor context. -/
theorem pin_IA020T_vecCons : MinorConclTypedT vecGroupU ⟨1, by decide⟩ :=
  IA020T_minor_conclusions_typed vecGroupU vecMinorMatchU vecRecTypeTyT.2 ⟨1, by decide⟩

/-- SECOND INSTRUMENT (D4): List's cons minor, by evaluation. It has three binders (head, tail, IH),
    and its conclusion is the motive (`bvar 4` there) at the constructor applied to the parameter and
    the two fields, all shifted past the IH: `M (cons A x xs)`. -/
theorem pin_IA018T_listCons_shape :
    (derivedMinor listGroupU ⟨1, by decide⟩ 8 [.nonrecursive, .recursive 0]).map
        (fun M => (piDomsOf M).length) = some 3 ∧
    (derivedMinor listGroupU ⟨1, by decide⟩ 8 [.nonrecursive, .recursive 0]).map piTailOf =
      some (.app (.bvar 4) (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
        (.bvar 1))) := by
  constructor <;> decide

/-! ## (5) GM-IND-004: the no-shift mutant -/

/-- GM-IND-004's mutant: `minorFromTelescope` with the shift of the remaining telescope past the
    inserted IH binder DROPPED (`B` where the real derivation has `lift 0 1 B`). Everything else is
    the real derivation verbatim, `funIHType` reused. -/
def minorFromTelescopeNoShift (E : ResolvedEnv) (fuel nparams : Nat) (M ctorAcc : Expr Nat) :
    List FieldShape → Expr Nat → Option (Expr Nat)
  | [], T => some (.app (foldApps M (familyIdx nparams T)) ctorAcc)
  | .nonrecursive :: ss, .pi A B =>
      (minorFromTelescopeNoShift E fuel nparams (lift 0 1 M)
        (.app (lift 0 1 ctorAcc) (.bvar 0)) ss B).map
        fun rest => .pi A rest
  | .recursive inner :: ss, .pi A B =>
      match funIHType E fuel nparams A M inner with
      | none => none
      | some ih =>
          (minorFromTelescopeNoShift E fuel nparams (lift 0 2 M)
            (.app (lift 0 2 ctorAcc) (.bvar 1)) ss B).map
            fun rest => .pi A (.pi ih rest)
  | _, _ => none

/-- `derivedMinor` through the mutant. -/
def derivedMinorNoShift {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) : Option (Expr Nat) :=
  let c := a.constructorViews i
  let shift := 1 + i.val
  let M := Expr.bvar i.val
  let ctorAcc := foldApps
    (.const (a.family.ref + 1 + i.val) (policyFamilyLevels a.family))
    (policyParameterLocals a.family.parameters.length shift)
  minorFromTelescopeNoShift E fuel a.family.parameters.length M ctorAcc shapes
    (lift 0 shift (ctorFieldTelescope c))

/-- TOOTH (GM-IND-004): at Vec's vcons, with the cell's own shapes and fuel, the real derivation
    produces the stored minor and the no-shift mutant does not. The vcons result index `succ n` is
    read one binder off. So `MinorPremisesMatch` refuses the mutant's minor, and IA-018T's premise
    cannot be met by it. -/
theorem tooth_GM_IND_004_vecCons :
    derivedMinor vecGroupU ⟨1, by decide⟩ 8 [.nonrecursive, .nonrecursive, .recursive 0] =
      vecGroupU.minorTypes[1]? ∧
    derivedMinorNoShift vecGroupU ⟨1, by decide⟩ 8 [.nonrecursive, .nonrecursive, .recursive 0] ≠
      vecGroupU.minorTypes[1]? := by
  constructor <;> decide

end Rcic.Declarative

#print axioms Rcic.Declarative.policyPrefixContext_cons_succ
#print axioms Rcic.Declarative.hasTyT_policyPi_inv
#print axioms Rcic.Declarative.policyPi_piDomsOf_piTailOf
#print axioms Rcic.Declarative.recursor_minorType_typed
#print axioms Rcic.Declarative.IA018T_minor_context_map_sound
#print axioms Rcic.Declarative.IA020T_minor_conclusions_typed
#print axioms Rcic.Declarative.pin_IA018T_listCons
#print axioms Rcic.Declarative.pin_IA020T_listCons
#print axioms Rcic.Declarative.pin_IA018T_vecCons
#print axioms Rcic.Declarative.pin_IA020T_vecCons
#print axioms Rcic.Declarative.pin_IA018T_listCons_shape
#print axioms Rcic.Declarative.tooth_GM_IND_004_vecCons
