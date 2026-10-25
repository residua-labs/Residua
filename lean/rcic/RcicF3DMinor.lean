import rcic.RcicF3DNorm

/-!
# F3 D-6: the minor premises of a group with δ-hidden fields

The recursor's minor for a constructor reads each recursive field through
`funIHType`, which normalizes the field: the induction hypothesis is the
motive at the **normal form's** indices and the field. `minor_sem` reads the
minor semantically with fields headed by the family; here the field list and
its normal forms are threaded together:

- `ShapesNorm`: admission's shapes against a field list and its normal forms
  (`shapesNorm_of_fieldShapesFuel`); it is stable under lifting
  (`ShapesNorm.lift`) and yields `ShapesMatch` on the normal forms and the
  agreement of the minor's arguments (`ShapesNorm.ihArgs_eq`);
- `minor_sem_norm`: the semantic minor, the induction hypotheses keyed on the
  normal forms (generalizing `minor_sem`, where the normal form is the field);
- `minor_ok_recD`: the minor obligation of the recursor's membership, with
  the stage induction's hypotheses on the normalized fields.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-! ### shapes against fields and their normal forms -/

/-- Admission's shapes against a field list and its normal forms: a
non-recursive shape on a family-free field (its own normal form), a directly
recursive shape on a field mentioning the family whose normal form at the
bound is headed by the family. -/
def ShapesNorm (E : ResolvedEnv) (fuel f : Nat) (ss : List FieldShape) (Fs Fs' : List (Expr Nat)) : Prop :=
  ss.length = Fs.length ∧ Fs'.length = Fs.length ∧
  ∀ (k : Nat) (s : FieldShape) (A A' : Expr Nat), ss[k]? = some s → Fs[k]? = some A → Fs'[k]? = some A' →
    (s = .nonrecursive ∧ occursConst f A = false ∧ A' = A) ∨
    (s = .recursive 0 ∧ occursConst f A = true ∧ RecHead f A' ∧ piTelescopeFuel E fuel A = some ([], A'))

theorem ShapesNorm.get {E : ResolvedEnv} {fuel f : Nat} {ss : List FieldShape} {Fs Fs' : List (Expr Nat)}
    (h : ShapesNorm E fuel f ss Fs Fs') {k : Nat} {s : FieldShape} {A' : Expr Nat} (hs : ss[k]? = some s)
    (hA' : Fs'[k]? = some A') : ∃ A, Fs[k]? = some A ∧
      ((s = .nonrecursive ∧ occursConst f A = false ∧ A' = A) ∨
        (s = .recursive 0 ∧ occursConst f A = true ∧ RecHead f A' ∧ piTelescopeFuel E fuel A = some ([], A'))) := by
  have hk : k < Fs.length := by rw [← h.2.1]; exact (List.getElem?_eq_some_iff.mp hA').1
  exact ⟨Fs[k], List.getElem?_eq_getElem hk, h.2.2 k s _ A' hs (List.getElem?_eq_getElem hk) hA'⟩

/-- The shapes match the normal forms. -/
theorem ShapesNorm.toMatch {E : ResolvedEnv} {fuel f : Nat} {ss : List FieldShape} {Fs Fs' : List (Expr Nat)}
    (h : ShapesNorm E fuel f ss Fs Fs') : ShapesMatch f ss Fs' := by
  refine ⟨h.1.trans h.2.1.symm, fun k s A' hs hA' => ?_⟩
  obtain ⟨A, _, hc⟩ := h.get hs hA'
  rcases hc with ⟨hs, ho, rfl⟩ | ⟨hs, _, hhd, _⟩
  · exact Or.inl ⟨hs, ho⟩
  · refine Or.inr ⟨hs, hhd, ?_⟩
    obtain ⟨ls, args, rfl⟩ := hhd
    rw [occursConst_foldApps]
    simp only [occursConst, decide_True, Bool.true_or]

/-- The minor's arguments are the same for the fields and their normal forms. -/
theorem ShapesNorm.ihArgs_eq {E : ResolvedEnv} {fuel f : Nat} {ss : List FieldShape} {Fs Fs' : List (Expr Nat)}
    (h : ShapesNorm E fuel f ss Fs Fs') (g : PSet.{4} → PSet.{4}) (xs : List PSet.{4}) :
    ihArgs f g Fs' xs = ihArgs f g Fs xs := by
  refine (ihArgs_congr_occ f g Fs Fs' xs h.2.1 fun k hk hk' => ?_).symm
  have hk0 : k < ss.length := by rw [h.1]; exact hk
  obtain ⟨A, hA, hc⟩ := h.get (List.getElem?_eq_getElem hk0) (List.getElem?_eq_getElem hk')
  rw [List.getElem?_eq_getElem hk] at hA
  cases Option.some.inj hA
  rcases hc with ⟨_, ho, he⟩ | ⟨_, ho, hhd, _⟩
  · rw [he]
  · obtain ⟨ls, args, he⟩ := hhd
    rw [he, occursConst_foldApps, ho]
    simp only [occursConst, decide_True, Bool.true_or]

/-- Shapes against lifted fields and lifted normal forms. -/
theorem ShapesNorm.lift {E : ResolvedEnv} (hcl : EnvClosed E) {fuel f : Nat} {ss : List FieldShape}
    {Fs Fs' : List (Expr Nat)} (h : ShapesNorm E fuel f ss Fs Fs') (s c : Nat) :
    ShapesNorm E fuel f ss (liftFields s Fs c) (liftFields s Fs' c) := by
  refine ⟨by rw [liftFields_length']; exact h.1, by rw [liftFields_length', liftFields_length']; exact h.2.1,
    fun k sh A A' hs hA hA' => ?_⟩
  rw [liftFields_getElem?] at hA hA'
  cases hA0 : Fs[k]? with
  | none => rw [hA0] at hA; cases hA
  | some B =>
      cases hA0' : Fs'[k]? with
      | none => rw [hA0'] at hA'; cases hA'
      | some B' =>
          rw [hA0] at hA
          rw [hA0'] at hA'
          cases Option.some.inj hA
          cases Option.some.inj hA'
          rcases h.2.2 k sh B B' hs hA0 hA0' with ⟨h1, ho, rfl⟩ | ⟨h1, ho, hhd, hp⟩
          · exact Or.inl ⟨h1, by rw [occursConst_lift]; exact ho, rfl⟩
          · exact Or.inr ⟨h1, by rw [occursConst_lift]; exact ho, hhd.lift _ _,
              piTelescopeFuel_lift_nil E hcl (c + k) s fuel hp⟩

/-- Admission's shapes, read as `ShapesNorm` against the normalized fields. -/
theorem shapesNorm_of_fieldShapesFuel {E : ResolvedEnv} {f nu np nq fuel : Nat} (hFF : FamFreeBodies E f) :
    (Fs : List (Expr Nat)) → (depth : Nat) → (shapes : List FieldShape) →
    fieldShapesFuel E fuel f nu np nq depth Fs = some shapes →
    (∀ s, s ∈ shapes → s = .nonrecursive ∨ s = .recursive 0) →
    ShapesNorm E fuel f shapes Fs (Fs.map (normField E fuel f))
  | [], _, shapes, hs, _ => by
      have e : shapes = [] := (Option.some.inj hs).symm
      subst e
      exact ⟨rfl, rfl, fun k s A A' h1 _ _ => by cases k <;> cases h1⟩
  | A :: Fs, depth, shapes, hs, hsh => by
      unfold fieldShapesFuel at hs
      cases ha : fieldAnalyze E fuel f nu np nq depth A with
      | permitted s idx =>
          rw [ha] at hs
          cases hr : fieldShapesFuel E fuel f nu np nq (depth + 1) Fs with
          | none => rw [hr] at hs; cases hs
          | some rest =>
              rw [hr] at hs
              have e : shapes = s :: rest := (Option.some.inj hs).symm
              subst e
              obtain ⟨hl1, hl2, hm⟩ := shapesNorm_of_fieldShapesFuel hFF Fs (depth + 1) rest hr
                (fun s' hs' => hsh s' (List.mem_cons_of_mem _ hs'))
              refine ⟨by rw [List.length_cons, List.length_cons, hl1],
                by rw [List.map_cons, List.length_cons, List.length_cons, hl2], fun k sh B B' h1 h2 h3 => ?_⟩
              cases k with
              | zero =>
                  rw [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
                  rw [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h3
                  subst h1; subst h2; subst h3
                  rcases hsh s (List.mem_cons_self _ _) with rfl | rfl
                  · have h0 := fieldAnalyze_nonrec_free ha
                    exact Or.inl ⟨rfl, h0, normField_free h0⟩
                  · obtain ⟨body, hw, hpt, _, fu, hpf⟩ := fieldAnalyze_rec0 ha
                    obtain ⟨ls, args, hsp⟩ := properFamilyFuel_true_head hpf
                    have hb : body = foldApps (.const f ls) args := by rw [← foldApps_appsSpine body, hsp]
                    have hocc : occursConst f A = true := by
                      rw [hb] at hw
                      exact occursConst_of_whnf_head hFF hw
                    refine Or.inr ⟨rfl, hocc, ⟨ls, args, ?_⟩, ?_⟩
                    · rw [normField_of_whnf hocc hw, hb]
                    · rw [normField_of_whnf hocc hw]
                      exact hpt
              | succ k =>
                  rw [List.getElem?_cons_succ] at h1 h2
                  rw [List.map_cons, List.getElem?_cons_succ] at h3
                  exact hm k sh B B' h1 h2 h3
      | unresolved => rw [ha] at hs; cases hs
      | refused _ => rw [ha] at hs; cases hs

/-! ### the semantic minor, keyed on the normal forms -/

/-- **The semantic minor with normalized recursive fields.** An element of the
derived minor type, applied to fitting fields followed after each recursive
field by an element of the motive at the field's normal form's indices and
the field, lands in the motive at the end's indices and the accumulated
constructor value. -/
theorem minor_sem_norm (M : Interp.{4}) (σ : Nat → Nat) (E : ResolvedEnv) (hcl : EnvClosed E) (fuel np : Nat)
    {f : Nat} (g : PSet.{4} → PSet.{4}) :
    (ss : List FieldShape) → (Fs Fs' : List (Expr Nat)) → (Tend Mx acc R : Expr Nat) → (ρ : Nat → PSet.{4}) →
    (F : PSet.{4}) → (xs : List PSet.{4}) →
    (∀ (k : Nat) (s : FieldShape) (A A' : Expr Nat), ss[k]? = some s → Fs[k]? = some A → Fs'[k]? = some A' →
      s = .nonrecursive ∨ (s = .recursive 0 ∧ RecHead f A' ∧ piTelescopeFuel E fuel A = some ([], A'))) →
    ss.length = Fs.length → Fs'.length = Fs.length →
    minorFromTelescope E fuel np Mx acc ss (policyPi Fs Tend) = some R →
    F ∈ Ed M (den M σ ρ R) → TelFits M σ Fs ρ xs → IHOk M σ np (den M σ ρ Mx) g ss Fs' ρ xs →
    fapps F (shArgs g ss xs) ∈ Ed M (fapp (fapps (den M σ ρ Mx) ((familyIdx np Tend).map (den M σ (push xs ρ))))
      (fapps (den M σ ρ acc) xs))
  | [], [], [], Tend, Mx, acc, R, ρ, F, [], _, _, _, hR, hF, _, _ => by
      simp only [policyPi, minorFromTelescope, Option.some.injEq] at hR
      subst hR
      have hF' : F ∈ Ed M (fapp (den M σ ρ (foldApps Mx (familyIdx np Tend))) (den M σ ρ acc)) := hF
      rw [den_foldApps] at hF'
      exact hF'
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, hl', _, _, _, _ => absurd hl' (Nat.succ_ne_zero _)
  | [], _ :: _, _, _, _, _, _, _, _, _, _, hl, _, _, _, _, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, _, _, _, _, _, _, hl, _, _, _, _, _ => absurd hl (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, hl', _, _, _, _ => absurd hl'.symm (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, _ :: _, _, _, _, _, _, _, [], _, _, _, _, _, hx, _ => hx.elim
  | .nonrecursive :: ss, A :: Fs, A' :: Fs', Tend, Mx, acc, R, ρ, F, x :: xs, hsh, hl, hl', hR, hF, ⟨hx, hfs⟩,
      ⟨_, hih⟩ => by
      have hR' : (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 1 Mx)
          (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss (policyPi Fs Tend)).map (fun rest => .pi A rest) =
          some R := hR
      obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR'
      have h1 := app_mem M (fun y y' hy => den_congr M σ R' (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl)))
        hF hx
      have ih := minor_sem_norm M σ E hcl fuel np g ss Fs Fs' Tend _ _ R' (vcons x ρ) (fapp F x) xs
        (fun k s B B' h1 h2 h3 => hsh (k + 1) s B B' (by simp only [List.getElem?_cons_succ]; exact h1)
          (by simp only [List.getElem?_cons_succ]; exact h2) (by simp only [List.getElem?_cons_succ]; exact h3))
        (Nat.succ.inj hl) (Nat.succ.inj hl') hR'' h1 hfs (by rw [den_lift01]; exact hih)
      have e : den M σ (vcons x ρ) (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) = fapp (den M σ ρ acc) x := by
        show fapp (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 acc)) x = _
        rw [den_lift01]
      rw [den_lift01, e] at ih
      exact ih
  | .recursive inner :: ss, A :: Fs, A' :: Fs', Tend, Mx, acc, R, ρ, F, x :: xs, hsh, hl, hl', hR, hF, ⟨hx, hfs⟩,
      ⟨hgx, hih⟩ => by
      rcases hsh 0 (.recursive inner) A A' List.getElem?_cons_zero List.getElem?_cons_zero List.getElem?_cons_zero
        with h0 | ⟨h0, hA, hpt⟩
      · exact absurd h0 (by intro h; cases h)
      · cases h0
        have hR1 : (match funIHType E fuel np A Mx 0 with
            | none => none
            | some ih => (minorFromTelescope E fuel np (Rcic.Declarative.lift 0 2 Mx)
                (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
                (Rcic.Declarative.lift 0 1 (policyPi Fs Tend))).map fun rest => Expr.pi A (.pi ih rest)) = some R := hR
        cases hih' : funIHType E fuel np A Mx 0 with
        | none => rw [hih'] at hR1; cases hR1
        | some ihT =>
            rw [hih'] at hR1
            obtain ⟨R', hR'', rfl⟩ := Option.map_eq_some'.mp hR1
            have hihT : ihT = foldApps (Rcic.Declarative.lift 0 1 Mx)
                ((familyIdx np A').map (Rcic.Declarative.lift 0 1) ++ [.bvar 0]) := by
              have := funIHType_whnf hcl (np := np) (M := Mx) hpt
              rw [hih'] at this
              exact Option.some.inj this
            have h1 := app_mem M (fun y y' hy => den_congr M σ (.pi ihT R') (vcons_congr (ρ := ρ) (ρ' := ρ) hy
              (fun _ => Equiv.rfl))) hF hx
            have hg : g x ∈ Ed M (den M σ (vcons x ρ) ihT) := by
              rw [hihT, den_foldApps, List.map_append, den_lift01, List.map_map]
              have e : (den M σ (vcons x ρ) ∘ Rcic.Declarative.lift 0 1) = den M σ ρ :=
                funext fun e => den_lift01 M σ x ρ e
              rw [e]
              exact hgx rfl
            have h2 := app_mem M (fun y y' hy => den_congr M σ R' (vcons_congr (ρ := vcons x ρ) (ρ' := vcons x ρ) hy
              (fun _ => Equiv.rfl))) h1 hg
            rw [lift_policyPi, Nat.zero_add] at hR''
            have hxl : xs.length = Fs.length := hfs.length
            have hfs' : TelFits M σ (liftFields 1 Fs 0) (vcons (g x) (vcons x ρ)) xs :=
              (TelFits_liftFields M σ [g x] (vcons x ρ) Fs [] xs).mpr hfs
            have hih2 : IHOk M σ np (den M σ (vcons (g x) (vcons x ρ)) (Rcic.Declarative.lift 0 2 Mx)) g ss
                (liftFields 1 Fs' 0) (vcons (g x) (vcons x ρ)) xs := by
              rw [den_lift02]
              exact (IHOk_liftFields M σ np _ g [g x] (vcons x ρ) ss Fs' [] xs).mpr hih
            have ih := minor_sem_norm M σ E hcl fuel np g ss (liftFields 1 Fs 0) (liftFields 1 Fs' 0)
              (Rcic.Declarative.lift Fs.length 1 Tend) _ _ R' (vcons (g x) (vcons x ρ)) _ xs
              (fun k s B B' h1 h2 h3 => by
                rw [liftFields_getElem?] at h2 h3
                cases hk : Fs[k]? with
                | none => rw [hk] at h2; cases h2
                | some C =>
                    cases hk' : Fs'[k]? with
                    | none => rw [hk'] at h3; cases h3
                    | some C' =>
                        rw [hk] at h2
                        rw [hk'] at h3
                        cases h2
                        cases h3
                        rcases hsh (k + 1) s C C' (by simp only [List.getElem?_cons_succ]; exact h1)
                          (by simp only [List.getElem?_cons_succ]; exact hk)
                          (by simp only [List.getElem?_cons_succ]; exact hk') with h | ⟨h, hC, hpC⟩
                        · exact Or.inl h
                        · exact Or.inr ⟨h, hC.lift _ _, piTelescopeFuel_lift_nil E hcl (0 + k) 1 fuel hpC⟩)
              (by rw [liftFields_length']; exact Nat.succ.inj hl)
              (by rw [liftFields_length', liftFields_length']; exact Nat.succ.inj hl') hR'' h2 hfs' hih2
            rw [den_lift02, familyIdx_lift, List.map_map, ← hxl] at ih
            have e : (den M σ (push xs (vcons (g x) (vcons x ρ))) ∘ Rcic.Declarative.lift xs.length 1) =
                den M σ (push xs (vcons x ρ)) := funext fun e => den_lift_push M σ xs [g x] (vcons x ρ) e
            have e2 : den M σ (vcons (g x) (vcons x ρ)) (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) =
                fapp (den M σ ρ acc) x := by
              show fapp (den M σ (vcons (g x) (vcons x ρ)) (Rcic.Declarative.lift 0 2 acc)) x = _
              rw [den_lift02]
            rw [e, e2] at ih
            exact ih

/-! ### the minor obligation -/

/-- **The minor obligation with δ-hidden recursive fields.** Minor `j`, applied
to fitting fields followed after each recursive field by an element of the
motive at the field's normal form's indices and the field, lands in the
motive at the result indices and the constructor's value. -/
theorem minor_ok_recD {M : Interp.{4}} {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat) (hcl : EnvClosed E)
    (fuelAt : Fin a.constructors.length → Nat) (shapesAt : Fin a.constructors.length → List FieldShape)
    (hsh : ∀ i, ∃ fuel, ShapesNorm E fuel a.family.ref (shapesAt i) (a.constructorViews i).fields
      ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref)) ∧
      derivedMinor a i fuel (shapesAt i) = a.minorTypes[i.val]?)
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal M W4 (σOf vs) (famDataOf a)))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (M.μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam M (σOf vs) (ctorEnd M (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length) ρ0
          (a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (hpsl : ps.length = a.family.parameters.length) (hisl : is.length = a.family.indices.length)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits M (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hisfit : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (j : Nat) (xs : List PSet.{4}) (hcf : CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs)
    (g : PSet.{4} → PSet.{4})
    (hih : IHOkF M (σOf vs) a.family.parameters.length mo g a.family.ref
      (ctorFieldsOf (normFamData a fuelAt) j) (push ps ρ0) xs) :
    fapps (ms.getD j pempty) (ihArgs a.family.ref g (ctorFieldsOf (famDataOf a) j) xs) ∈
      Ed M (fapps mo (is ++ [ctorV M (σOf vs) (famDataOf a) j xs])) := by
  obtain ⟨c, hc, hxs, hri⟩ := hcf
  have hjk : j < a.constructors.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    rwa [famDataOf_ctors_length] at this
  let i : Fin a.constructors.length := ⟨j, hjk⟩
  have hc' : c = ((a.constructorViews i).fields, (a.constructorViews i).resultIndices) := by
    have := famDataOf_ctor a i
    rw [hc] at this; exact Option.some.inj this
  subst hc'
  have hcfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews i).fields := ctorFieldsOf_famDataOf a i
  have hcfo' : ctorFieldsOf (normFamData a fuelAt) j =
      (a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref) :=
    ctorFieldsOf_of_get (normFamData_ctor a fuelAt i)
  rw [hcfo'] at hih
  rw [hcfo]
  obtain ⟨fuel, hsmN, hdmi⟩ := hsh i
  have hsm : ShapesMatch a.family.ref (shapesAt i)
      ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref)) := hsmN.toMatch
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hjm : j < ms.length := by rw [hmsl, a.minorCount]; exact hjk
  have hmj := TelFits_get a.minorTypes _ ms hms j (by rw [a.minorCount]; exact hjk)
  have hmt : derivedMinor a i fuel (shapesAt i) = some (a.minorTypes[j]'(by rw [a.minorCount]; exact hjk)) :=
    hdmi.trans (List.getElem?_eq_getElem _)
  have hρpre : push (ms.take j) (vcons mo (push ps ρ0)) = push (mo :: ms.take j) (push ps ρ0) := rfl
  have htl : (mo :: ms.take j).length = 1 + j := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)]; omega
  rw [hρpre] at hmj
  have hxsl : xs.length = (a.constructorViews i).fields.length := hxs.length
  -- the derived minor, read semantically
  unfold derivedMinor at hmt
  dsimp only at hmt
  rw [show ctorFieldTelescope (a.constructorViews i) = policyPi (a.constructorViews i).fields
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews i).parameters.length (a.constructorViews i).fields.length ++
          (a.constructorViews i).resultIndices)) from rfl, lift_policyPi, Nat.zero_add] at hmt
  have h1 : den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0)) (.bvar j) = mo := by
    show push (mo :: ms.take j) (push ps ρ0) j = mo
    have := push_cons_len_index mo (ms.take j) (push ps ρ0)
    rwa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)] at this
  have hfitL : TelFits M (σOf vs) (liftFields (1 + j) (a.constructorViews i).fields 0)
      (push (mo :: ms.take j) (push ps ρ0)) xs := by
    have := (TelFits_liftFields M (σOf vs) (mo :: ms.take j) (push ps ρ0) (a.constructorViews i).fields [] xs).mpr hxs
    rw [htl] at this; exact this
  have hihL : IHOk M (σOf vs) a.family.parameters.length (den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0)) (.bvar j))
      g (shapesAt i) (liftFields (1 + j) ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref)) 0)
      (push (mo :: ms.take j) (push ps ρ0)) xs := by
    rw [h1]
    have := (IHOk_liftFields M (σOf vs) a.family.parameters.length mo g (mo :: ms.take j) (push ps ρ0) (shapesAt i)
      _ [] xs).mpr (ihOk_of_F M (σOf vs) _ mo g _ (shapesAt i) _ hsm _ xs hih)
    rw [htl] at this; exact this
  have hshL := hsmN.lift hcl (1 + j) 0
  have hmem := minor_sem_norm M (σOf vs) E hcl fuel a.family.parameters.length g (shapesAt i)
    (liftFields (1 + j) (a.constructorViews i).fields 0)
    (liftFields (1 + j) ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref)) 0) _ _ _ _ _ _ xs
    (fun k s A A' h1 h2 h3 => by
      rcases hshL.2.2 k s A A' h1 h2 h3 with ⟨h, _, _⟩ | ⟨h, _, hhd, hp⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hhd, hp⟩)
    (by rw [liftFields_length']; exact hsmN.1) (by rw [liftFields_length', liftFields_length']; exact hsmN.2.1)
    hmt hmj hfitL hihL
  rw [shArgs_eq_ihArgs g a.family.ref (shapesAt i) _ hsm xs (by rw [List.length_map]; exact hxsl)] at hmem
  rw [hsmN.ihArgs_eq g xs] at hmem
  rw [h1] at hmem
  -- the end
  have hidx : (familyIdx a.family.parameters.length (Rcic.Declarative.lift (a.constructorViews i).fields.length (1 + j)
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews i).parameters.length (a.constructorViews i).fields.length ++
          (a.constructorViews i).resultIndices)))).map
      (den M (σOf vs) (push xs (push (mo :: ms.take j) (push ps ρ0)))) =
      (a.constructorViews i).resultIndices.map (den M (σOf vs) (push xs (push ps ρ0))) := by
    rw [familyIdx_lift, familyIdx_foldApps_const, List.drop_append_of_le_length
      (by rw [length_paramLocals, (a.constructorViews i).parameterCount]; exact Nat.le_refl _),
      List.drop_eq_nil_of_le (by rw [length_paramLocals, (a.constructorViews i).parameterCount]; exact Nat.le_refl _),
      List.nil_append,
      List.map_map, ← hxsl]
    exact List.map_congr_left fun e _ => by
      show den M (σOf vs) _ (Rcic.Declarative.lift xs.length (1 + j) e) = _
      rw [← htl, den_lift_push]
  have h3 : den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0))
      (foldApps (.const (a.family.ref + 1 + j) (policyFamilyLevels a.family))
        (policyParameterLocals a.family.parameters.length (1 + j))) =
      fapps (M.μ (a.family.ref + 1 + j) ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) ps := by
    rw [den_foldApps]
    have e1 : push (mo :: ms.take j) (push ps ρ0) = push (ps ++ (mo :: ms.take j)) ρ0 :=
      (push_append ps _ ρ0).symm
    rw [e1, ← hpsl, ← htl, den_paramLocals]
    rfl
  rw [hidx, h3, ← fapps_append] at hmem
  have e1 : Equiv (fapps mo ((a.constructorViews i).resultIndices.map (den M (σOf vs) (push xs (push ps ρ0)))))
      (fapps mo is) := fapps_congr_args mo hri
  have hV := ctorApp_ctorV a vs hfamμ hctorμ ps mo is hpsl hisl hmo hisfit j hjk xs hxsl _
    (mem_congr_right (ed_congr M (fapp_congr e1 Equiv.rfl)) hmem)
  rw [fapps_append]
  exact mem_congr_right (ed_congr M (fapp_congr e1 hV)) hmem

end PSet

end Rcic.F3
