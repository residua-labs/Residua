import rcic.RcicF3MinorRec

/-!
# F3 S5b-3d: the minor obligation with recursive fields

`minor_ok_rec`: minor `j`, applied to fitting fields followed after each
recursive field by an element of the motive at that field's indices and the
field, lands in the motive at the result indices and the constructor's
value. The admitted minor type is read through `minor_sem`; the field shapes
must match the fields (`ShapesMatch`: a non-recursive shape on a
family-free field, a directly recursive shape on a field headed by the
family).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- Shapes match fields: non-recursive on family-free fields, directly
recursive on fields headed by the family. -/
def ShapesMatch (f : Nat) (ss : List FieldShape) (Fs : List (Expr Nat)) : Prop :=
  ss.length = Fs.length ∧ ∀ (k : Nat) (s : FieldShape) (A : Expr Nat), ss[k]? = some s → Fs[k]? = some A →
    (s = .nonrecursive ∧ occursConst f A = false) ∨ (s = .recursive 0 ∧ RecHead f A ∧ occursConst f A = true)

/-- The motive condition at the recursive fields, read off the fields. -/
def IHOkF (M : Interp.{4}) (σ : Nat → Nat) (np : Nat) (mo : PSet.{4}) (g : PSet.{4} → PSet.{4}) (f : Nat) :
    List (Expr Nat) → (Nat → PSet.{4}) → List PSet.{4} → Prop
  | A :: Fs, ρ, x :: xs =>
      (occursConst f A = true → ihAt g A x ∈ Ed M (fapps mo ((familyIdx np A).map (den M σ ρ) ++ [x]))) ∧
        IHOkF M σ np mo g f Fs (vcons x ρ) xs
  | _, _, _ => True

theorem ihOk_of_F (M : Interp.{4}) (σ : Nat → Nat) (np : Nat) (mo : PSet.{4}) (g : PSet.{4} → PSet.{4}) (f : Nat) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → ShapesMatch f ss Fs → (ρ : Nat → PSet.{4}) →
    (xs : List PSet.{4}) → IHOkF M σ np mo g f Fs ρ xs → IHOk M σ np mo g ss Fs ρ xs
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _, _, [], _ => trivial
  | s :: ss, A :: Fs, ⟨hl, hm⟩, ρ, x :: xs, ⟨h1, h2⟩ =>
      ⟨fun hs => by
        rcases hm 0 s A List.getElem?_cons_zero List.getElem?_cons_zero with ⟨hs', _⟩ | ⟨_, hRh, ho⟩
        · rw [hs'] at hs; cases hs
        · obtain ⟨ls, args, hA⟩ := hRh
          subst hA
          rw [ihAt_foldApps (fun _ _ h => Expr.noConfusion h)] at h1
          exact h1 ho,
       ihOk_of_F M σ np mo g f ss Fs ⟨Nat.succ.inj hl, fun k s' A' h1' h2' =>
         hm (k + 1) s' A' (by simp only [List.getElem?_cons_succ]; exact h1')
           (by simp only [List.getElem?_cons_succ]; exact h2')⟩ (vcons x ρ) xs h2⟩

theorem shArgs_eq_ihArgs (g : PSet.{4} → PSet.{4}) (f : Nat) :
    (ss : List FieldShape) → (Fs : List (Expr Nat)) → ShapesMatch f ss Fs → (xs : List PSet.{4}) →
    xs.length = Fs.length → shArgs g ss xs = ihArgs f g Fs xs
  | [], [], _, [], _ => rfl
  | s :: ss, A :: Fs, ⟨hl, hm⟩, x :: xs, hxl => by
      have ih := shArgs_eq_ihArgs g f ss Fs ⟨Nat.succ.inj hl, fun k s' A' h1' h2' =>
         hm (k + 1) s' A' (by simp only [List.getElem?_cons_succ]; exact h1')
           (by simp only [List.getElem?_cons_succ]; exact h2')⟩ xs (Nat.succ.inj hxl)
      rcases hm 0 s A List.getElem?_cons_zero List.getElem?_cons_zero with ⟨rfl, ho⟩ | ⟨rfl, hRh, ho⟩
      · unfold ihArgs; rw [ho, if_neg (by decide), ← ih]; rfl
      · unfold ihArgs; rw [ho, if_pos rfl, ← ih]
        obtain ⟨ls, args, hA⟩ := hRh
        rw [hA, ihAt_foldApps (fun _ _ h => Expr.noConfusion h)]; rfl
  | [], _ :: _, ⟨hl, _⟩, _, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], ⟨hl, _⟩, _, _ => (Nat.succ_ne_zero _ hl).elim
  | [], [], _, _ :: _, hxl => (Nat.succ_ne_zero _ hxl).elim
  | _ :: _, _ :: _, _, [], hxl => (Nat.succ_ne_zero _ hxl.symm).elim

theorem ShapesMatch.lift {f : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)} (h : ShapesMatch f ss Fs)
    (s c : Nat) : ∀ (k : Nat) (sh : FieldShape) (A : Expr Nat), ss[k]? = some sh → (liftFields s Fs c)[k]? = some A →
      sh = .nonrecursive ∨ (sh = .recursive 0 ∧ RecHead f A) := by
  intro k sh A h1 h2
  rw [liftFields_getElem?] at h2
  cases hk : Fs[k]? with
  | none => rw [hk] at h2; cases h2
  | some B =>
      rw [hk] at h2
      cases h2
      rcases h.2 k sh B h1 hk with ⟨h, _⟩ | ⟨h, hB, _⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hB.lift _ _⟩

/-- **The minor obligation with recursive fields.** -/
theorem minor_ok_rec {M : Interp.{4}} {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (hop : ∀ ls, transparentBody E a.family.ref ls = none)
    (hshapes : ∀ i : Fin a.constructors.length, ∃ fuel shapes, ShapesMatch a.family.ref shapes
      (a.constructorViews i).fields ∧ derivedMinor a i fuel shapes = a.minorTypes[i.val]?)
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
    (hih : IHOkF M (σOf vs) a.family.parameters.length mo g a.family.ref (ctorFieldsOf (famDataOf a) j)
      (push ps ρ0) xs) :
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
  rw [hcfo] at hih ⊢
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hjm : j < ms.length := by rw [hmsl, a.minorCount]; exact hjk
  have hmj := TelFits_get a.minorTypes _ ms hms j (by rw [a.minorCount]; exact hjk)
  obtain ⟨fuel, shapes, hsm, hdm⟩ := hshapes i
  have hmt : derivedMinor a i fuel shapes = some (a.minorTypes[j]'(by rw [a.minorCount]; exact hjk)) :=
    hdm.trans (List.getElem?_eq_getElem _)
  have hρpre : push (ms.take j) (vcons mo (push ps ρ0)) = push (mo :: ms.take j) (push ps ρ0) := rfl
  have htl : (mo :: ms.take j).length = 1 + j := by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)]; omega
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
      g shapes (liftFields (1 + j) (a.constructorViews i).fields 0) (push (mo :: ms.take j) (push ps ρ0)) xs := by
    rw [h1]
    have := (IHOk_liftFields M (σOf vs) a.family.parameters.length mo g (mo :: ms.take j) (push ps ρ0) shapes
      (a.constructorViews i).fields [] xs).mpr
      (ihOk_of_F M (σOf vs) _ mo g _ shapes _ hsm _ xs hih)
    rw [htl] at this; exact this
  have hmem := minor_sem M (σOf vs) E fuel a.family.parameters.length hop g shapes
    (liftFields (1 + j) (a.constructorViews i).fields 0) _ _ _ _ _ _ xs
    (hsm.lift (1 + j) 0) (by rw [liftFields_length']; exact hsm.1) hmt hmj hfitL hihL
  rw [shArgs_eq_ihArgs g a.family.ref shapes _ hsm xs hxsl] at hmem
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
