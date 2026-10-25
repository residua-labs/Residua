import rcic.RcicF3Lvl

/-!
# F3 S5a-8: the recursor's value is an element of its type

`famDataOf a` reads a group's data off its recursor's admission.
`recVal_mem`: for a group whose constructors have only non-recursive fields,
the recursor's value (the telescope abstraction over its stored type ending
in `recEnd`) is an element of its type, given the family's and the
constructors' values at the family instance, the group's level bounds, and
(for `Prop` large elimination) that the non-revealed fields are proofs.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- The list of the values of a function on `Fin n`. -/
def ofFin {α : Type} : (n : Nat) → (Fin n → α) → List α
  | 0, _ => []
  | n + 1, f => f ⟨0, Nat.succ_pos n⟩ :: ofFin n (fun i => f i.succ)

theorem ofFin_length {α : Type} : (n : Nat) → (f : Fin n → α) → (ofFin n f).length = n
  | 0, _ => rfl
  | n + 1, f => by simp [ofFin, ofFin_length n]

theorem ofFin_get {α : Type} : (n : Nat) → (f : Fin n → α) → (i : Fin n) → (ofFin n f)[i.val]? = some (f i)
  | 0, _, i => i.elim0
  | n + 1, f, ⟨0, _⟩ => by simp [ofFin]
  | n + 1, f, ⟨i + 1, hi⟩ => by
      simp only [ofFin, List.getElem?_cons_succ]
      exact ofFin_get n (fun i => f i.succ) ⟨i, by omega⟩

/-- A group's data, read off its recursor's admission. -/
def famDataOf {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    FamData where
  fref := a.family.ref
  params := a.family.parameters
  indices := a.family.indices
  resLevel := a.family.resultLevel
  ctors := ofFin a.constructors.length fun i => ((a.constructorViews i).fields, (a.constructorViews i).resultIndices)
  policy := a.policy

theorem famDataOf_ctors_length {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : (famDataOf a).ctors.length = a.constructors.length :=
  ofFin_length _ _

theorem famDataOf_ctor {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) :
    (famDataOf a).ctors[i.val]? = some ((a.constructorViews i).fields, (a.constructorViews i).resultIndices) :=
  ofFin_get _ _ i

theorem mapIdx_go_lift (s : Nat) : ∀ (l : List (Expr Nat)) (arr : Array (Expr Nat)),
    List.mapIdx.go (fun j T => Rcic.Declarative.lift j s T) l arr = arr.toList ++ liftFields s l arr.size
  | [], arr => by simp [List.mapIdx.go, liftFields]
  | A :: l, arr => by
      show List.mapIdx.go _ l (arr.push _) = _
      rw [mapIdx_go_lift s l (arr.push _)]
      simp [liftFields, Array.push_toList]

theorem mapIdx_lift_eq_liftFields (s : Nat) (Ds : List (Expr Nat)) :
    Ds.mapIdx (fun j T => Rcic.Declarative.lift j s T) = liftFields s Ds 0 := by
  show List.mapIdx.go _ Ds #[] = _
  rw [mapIdx_go_lift]
  rfl

/-- The recursor's stored type as one telescope. -/
theorem policyRecursorType_eq {E : ResolvedEnv} (fam : PolicyFamilyView E) (mins : List (Expr Nat)) (policy : EliminationPolicy) :
    policyRecursorType fam mins policy =
      policyPi (fam.parameters ++ policyMotiveType fam policy ::
        (mins ++ (liftFields (mins.length + 1) fam.indices 0 ++
          [foldApps (.const fam.ref (policyFamilyLevels fam))
            (policyParameterLocals fam.parameters.length (mins.length + 1 + fam.indices.length) ++
              policyLocals fam.indices.length)])))
        (foldApps (.bvar (mins.length + fam.indices.length + 1))
          ((List.range fam.indices.length).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])) := by
  unfold policyRecursorType
  dsimp only
  rw [policyPi_append, mapIdx_lift_eq_liftFields]
  show _ = policyPi fam.parameters (Expr.pi _ (policyPi (mins ++ _) _))
  rw [policyPi_append, policyPi_append]
  rfl

/-- A value fitting a telescope at position `j`. -/
theorem TelFits_get {M : Interp.{T}} {σ : Nat → Nat} : (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    (xs : List PSet.{T}) → TelFits M σ Ds ρ xs → (j : Nat) → (hj : j < Ds.length) →
    xs.getD j pempty ∈ Ed M (den M σ (push (xs.take j) ρ) (Ds[j]'hj))
  | A :: Ds, ρ, x :: xs, ⟨hx, _⟩, 0, _ => hx
  | A :: Ds, ρ, x :: xs, ⟨_, h⟩, j + 1, hj => by
      have := TelFits_get Ds (vcons x ρ) xs h j (by simpa using hj)
      simpa [push] using this

theorem den_policyLocals (M : Interp.{T}) (σ : Nat → Nat) (is : List PSet.{T}) (R : Nat → PSet.{T}) :
    (policyLocals is.length).map (den M σ (push is R)) = is := by
  unfold policyLocals
  rw [List.map_map]
  exact lastVals_push is R

/-- A value in the type of a family application fits the family's telescope and
lies in the fibre's type value. -/
theorem fam_app_fits {M : Interp.{T}} (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData) {F : PSet.{T}}
    (hF : Equiv F (piLam M σ (famEnd M W σ fd) (fun _ => pempty) (famType fd))) (ps is : List PSet.{T})
    (hlen : (ps ++ is).length = (fd.params ++ fd.indices).length) {z : PSet.{T}}
    (hz : z ∈ Ed M (fapps F (ps ++ is))) :
    TelFits M σ (fd.params ++ fd.indices) (fun _ => pempty) (ps ++ is) ∧
      z ∈ Ed M (famEnd M W σ fd (push (ps ++ is) (fun _ => pempty))) := by
  have hz' := mem_congr_right (ed_congr M (fapps_congr hF _)) hz
  have hne : ¬ Equiv (fapps (piLam M σ (famEnd M W σ fd) (fun _ => pempty) (famType fd)) (ps ++ is)) pempty :=
    fun h0 => not_mem_pempty (mem_congr_right ((ed_congr M h0).trans (ed_pempty M)) hz')
  have hfit := fits_of_fapps_ne M σ (famEnd_resp M W σ fd) (.sort fd.resLevel) _ _ _ hlen hne
  exact ⟨hfit, mem_congr_right (ed_congr M (fapps_piLam M σ (famEnd_resp M W σ fd) (.sort fd.resLevel)
    _ _ _ hfit)) hz'⟩

theorem famEnd_type_mem {M : Interp.{T}} (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData)
    (ps is : List PSet.{T}) (his : is.length = fd.indices.length) (h0 : evalTotal σ fd.resLevel ≠ 0)
    {z : PSet.{T}} (hz : z ∈ Ed M (famEnd M W σ fd (push (ps ++ is) (fun _ => pempty)))) :
    ∃ j xs, CtorFits M σ fd.ctors (push ps (fun _ => pempty)) is j xs ∧ Equiv z (dataVal j xs) := by
  unfold famEnd cond at hz
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue h => exact absurd h h0
  | isFalse _ =>
      rw [hd] at hz
      rw [push_append, ← his, shiftρ_push, lastVals_push] at hz
      have hz' := mem_congr_right (ed_tyv M (TypeFib_dich M W _ σ _ _ _)) hz
      obtain ⟨_, ⟨j, xs, hc, he⟩, hi⟩ := mem_sep.mp hz'
      exact ⟨j, xs, hc, hi.symm.trans he⟩

theorem famEnd_prop_mem {M : Interp.{T}} (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData)
    (ps is : List PSet.{T}) (his : is.length = fd.indices.length) (h0 : evalTotal σ fd.resLevel = 0)
    {z : PSet.{T}} (hz : z ∈ Ed M (famEnd M W σ fd (push (ps ++ is) (fun _ => pempty)))) :
    (∃ j xs, CtorFits M σ fd.ctors (push ps (fun _ => pempty)) is j xs) ∧ Equiv z pempty := by
  unfold famEnd cond at hz
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isFalse h => exact absurd h0 h
  | isTrue _ =>
      rw [hd] at hz
      rw [push_append, ← his, shiftρ_push, lastVals_push] at hz
      exact mem_tv.mp (mem_congr_right (ed_tyv M (dich_tv _)) hz)

theorem ed_famEnd_no_pempty {M : Interp.{T}} (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData)
    (h0 : evalTotal σ fd.resLevel ≠ 0) (ρ : Nat → PSet.{T}) : ¬ pempty ∈ Ed M (famEnd M W σ fd ρ) := by
  unfold famEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue h => exact absurd h h0
  | isFalse _ =>
      intro hz
      have hz' := mem_congr_right (ed_tyv M (TypeFib_dich M W _ σ _ _ _)) hz
      obtain ⟨_, ⟨j, xs, _, he⟩, hi⟩ := mem_sep.mp hz'
      exact dataVal_ne_pempty j xs (he.symm.trans hi)

/-- A telescope abstraction whose end value is always `∅` applies to `∅`. -/
theorem fapps_piLam_pempty (M : Interp.{T}) (σ : Nat → Nat) {g : (Nat → PSet.{T}) → PSet.{T}}
    (hg : EnvResp g) (hg0 : ∀ ρ, Equiv (g ρ) pempty) (b : Expr Nat) (Ds : List (Expr Nat))
    (ρ : Nat → PSet.{T}) (xs : List PSet.{T}) (hl : xs.length = Ds.length) (hb : ∀ ρ', piLam M σ g ρ' b = g ρ') :
    Equiv (fapps (piLam M σ g ρ (policyPi Ds b)) xs) pempty := by
  cases hm : M.dec (Equiv (fapps (piLam M σ g ρ (policyPi Ds b)) xs) pempty) with
  | isTrue h => exact h
  | isFalse hne =>
      have hfit := fits_of_fapps_ne M σ hg b Ds ρ xs hl hne
      have e := fapps_piLam M σ hg b Ds ρ xs hfit
      rw [hb] at e
      exact e.trans (hg0 _)

theorem liftFields_length' (s : Nat) : (Ds : List (Expr Nat)) → (c : Nat) → (liftFields s Ds c).length = Ds.length
  | [], _ => rfl
  | _ :: Ds, c => by simp [liftFields, liftFields_length' s Ds (c + 1)]

theorem den_recResult (M : Interp.{T}) (σ : Nat → Nat) (mo z : PSet.{T}) (ms is : List PSet.{T})
    (R : Nat → PSet.{T}) :
    den M σ (vcons z (push is (push ms (vcons mo R))))
      (foldApps (.bvar (ms.length + is.length + 1))
        ((List.range is.length).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])) =
      fapps mo (is ++ [z]) := by
  rw [den_foldApps]
  have h1 : den M σ (vcons z (push is (push ms (vcons mo R)))) (.bvar (ms.length + is.length + 1)) = mo := by
    show push is (push ms (vcons mo R)) (ms.length + is.length) = mo
    rw [push_ge]
    have := push_ge ms (vcons mo R) 0
    rw [Nat.zero_add] at this
    rw [this]; rfl
  rw [h1, List.map_append, List.map_map]
  congr 1
  have h2 : ((fun e => den M σ (vcons z (push is (push ms (vcons mo R)))) e) ∘ fun i => Expr.bvar (i + 1)) =
      push is (push ms (vcons mo R)) := rfl
  rw [h2]
  show lastVals is.length (push is (push ms (vcons mo R))) ++ [z] = is ++ [z]
  rw [lastVals_push]

theorem Fapp_den (M : Interp.{T}) (σ : Nat → Nat) (fref : Nat) (lsF : List Level) (ps is : List PSet.{T})
    (R : Nat → PSet.{T}) :
    den M σ (push is (push ps R)) (foldApps (.const fref lsF) (policyLocals (ps.length + is.length))) =
      fapps (M.μ fref (lsF.map (evalTotal σ))) (ps ++ is) := by
  rw [den_foldApps]
  have e : push is (push ps R) = push (ps ++ is) R := (push_append ps is R).symm
  rw [e, show ps.length + is.length = (ps ++ is).length by simp, den_policyLocals]
  rfl

/-- In a `Type` family, `∅` is not in the type of a family application. -/
theorem fam_app_no_pempty {M : Interp.{T}} (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData) {F : PSet.{T}}
    (hF : Equiv F (piLam M σ (famEnd M W σ fd) (fun _ => pempty) (famType fd))) (ps is : List PSet.{T})
    (hlen : (ps ++ is).length = (fd.params ++ fd.indices).length) (h0 : evalTotal σ fd.resLevel ≠ 0) :
    ¬ pempty ∈ Ed M (fapps F (ps ++ is)) := fun h =>
  ed_famEnd_no_pempty W σ fd h0 _ (fam_app_fits W σ fd hF ps is hlen h).2

theorem push_take_cons (mo : PSet.{T}) (ms : List PSet.{T}) (j : Nat) (R : Nat → PSet.{T}) :
    push (ms.take j) (vcons mo R) = push (mo :: ms.take j) R := rfl

theorem push_cons_len_index (mo : PSet.{T}) (ys : List PSet.{T}) (R : Nat → PSet.{T}) :
    push (mo :: ys) R ys.length = mo := by
  show push ys (vcons mo R) ys.length = mo
  have := push_ge ys (vcons mo R) 0
  rw [Nat.zero_add] at this
  rw [this]; rfl

theorem piLam_foldApps_const (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T})
    (ρ : Nat → PSet.{T}) (r : Nat) (ls : List Level) : (as : List (Expr Nat)) →
    piLam M σ g ρ (foldApps (.const r ls) as) = g ρ := by
  suffices h : ∀ (f : Expr Nat), (∀ A B, f ≠ .pi A B) → ∀ as, piLam M σ g ρ (foldApps f as) = g ρ by
    exact h _ (fun _ _ h => Expr.noConfusion h)
  intro f hf as
  induction as generalizing f with
  | nil =>
      cases f with
      | pi A B => exact absurd rfl (hf A B)
      | _ => rfl
  | cons a as ih => exact ih (.app f a) (fun _ _ h => Expr.noConfusion h)

theorem length_paramLocals (np nf : Nat) : (policyParameterLocals np nf).length = np := by
  simp [policyParameterLocals]

/-- The derived minor of a constructor with only non-recursive fields, explicitly. -/
theorem derivedMinor_nonrec {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) (fuel : Nat)
    (shapes : List FieldShape) (hnr : ∀ s, s ∈ shapes → s = .nonrecursive)
    (hsl : shapes.length = (a.constructorViews i).fields.length) :
    derivedMinor a i fuel shapes = some (policyPi (liftFields (1 + i.val) (a.constructorViews i).fields 0)
      (.app (foldApps (liftIter (a.constructorViews i).fields.length (.bvar i.val))
          ((a.constructorViews i).resultIndices.map
            (Rcic.Declarative.lift (a.constructorViews i).fields.length (1 + i.val))))
        (accAfter (a.constructorViews i).fields.length
          (foldApps (.const (a.family.ref + 1 + i.val) (policyFamilyLevels a.family))
            (policyParameterLocals a.family.parameters.length (1 + i.val)))))) := by
  unfold derivedMinor
  dsimp only
  rw [show ctorFieldTelescope (a.constructorViews i) = policyPi (a.constructorViews i).fields
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews i).parameters.length (a.constructorViews i).fields.length ++
          (a.constructorViews i).resultIndices)) from rfl, lift_policyPi, Nat.zero_add]
  rw [minorFromTelescope_nonrec E fuel _ _ _ shapes _ _ hnr (by rw [hsl, liftFields_length'])]
  have hlc : ∀ c s r (ls : List Level), Rcic.Declarative.lift c s (Expr.const r ls : Expr Nat) = .const r ls :=
    fun _ _ _ _ => rfl
  rw [liftFields_length', lift_foldApps, hlc, familyIdx_foldApps_const, List.map_append, List.drop_append_of_le_length
    (by simp [length_paramLocals, (a.constructorViews i).parameterCount])]
  rw [List.drop_eq_nil_of_le (by simp [length_paramLocals, (a.constructorViews i).parameterCount]), List.nil_append]

/-- A constructor applied to its parameters and fields, at which the motive has
an element, is the constructor's value as the recursor sees it. -/
theorem ctorApp_ctorV {M : Interp.{4}} {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal M W4 (σOf vs) (famDataOf a)))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (M.μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam M (σOf vs) (ctorEnd M (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length) ρ0
          (a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (is : List PSet.{4})
    (hpsl : ps.length = a.family.parameters.length) (hisl : is.length = a.family.indices.length)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hisfit : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (j : Nat) (hjk : j < a.constructors.length) (xs : List PSet.{4})
    (hxsl : xs.length = (a.constructorViews ⟨j, hjk⟩).fields.length) (y : PSet.{4})
    (hy : y ∈ Ed M (fapp (fapps mo is)
      (fapps (M.μ (a.family.ref + 1 + j) ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ xs)))) :
    Equiv (fapps (M.μ (a.family.ref + 1 + j) ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ xs))
      (ctorV M (σOf vs) (famDataOf a) j xs) := by
  let i : Fin a.constructors.length := ⟨j, hjk⟩
  have hst := (a.constructorViews i).storedType
  have hctor := hctorμ i
  rw [hst] at hctor
  have hW := fapps_congr hctor (ps ++ xs)
  have hlenC : (ps ++ xs).length = ((a.constructorViews i).parameters ++ (a.constructorViews i).fields).length := by
    simp [hpsl, hxsl, (a.constructorViews i).parameterCount]
  have hV : Equiv (fapps (M.μ (a.family.ref + 1 + j) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (ps ++ xs)) (ctorV M (σOf vs) (famDataOf a) j xs) := by
    unfold ctorV cond
    cases hd : M.dec (evalTotal (σOf vs) (famDataOf a).resLevel = 0) with
    | isTrue h0 =>
        refine hW.trans (fapps_piLam_pempty M _ (ctorEnd_resp M _ _ _ _) ?_ _ _ ρ0 _ hlenC
          (fun ρ' => piLam_foldApps_const M _ _ ρ' _ _ _))
        intro ρ'
        unfold ctorEnd cond
        rw [hd]
        exact Equiv.rfl
    | isFalse h0 =>
        have hne : ¬ Equiv (fapps (piLam M (σOf vs) (ctorEnd M (σOf vs) (famDataOf a) j
            (a.constructorViews i).fields.length) ρ0 (policyPi ((a.constructorViews i).parameters ++
              (a.constructorViews i).fields) (foldApps (.const a.family.ref (policyFamilyLevels a.family))
                (policyParameterLocals (a.constructorViews i).parameters.length
                  (a.constructorViews i).fields.length ++ (a.constructorViews i).resultIndices)))) (ps ++ xs))
            pempty := by
          intro hW0
          apply not_mem_pempty (x := y)
          refine mem_congr_right ((ed_congr M (fapp_congr Equiv.rfl (hW.trans hW0))).trans ?_) hy
          -- the motive's partial application at `∅`
          have hmi := mem_fapps M (σOf vs) _ a.family.indices (push ps ρ0) mo is hmo hisfit
          cases hm : M.dec (Equiv (fapp (fapps mo is) pempty) pempty) with
          | isTrue h => exact (ed_congr M h).trans (ed_pempty M)
          | isFalse hn =>
              exfalso
              have hdom := mem_dom_of_fapp_ne M (den_resp M (σOf vs) _ _) hmi hn
              have hF := Fapp_den M (σOf vs) a.family.ref (policyFamilyLevels a.family) ps is ρ0
              rw [hpsl, hisl] at hF
              rw [hF] at hdom
              exact fam_app_no_pempty W4 (σOf vs) (famDataOf a) hfamμ ps is
                (by simp [famDataOf, hpsl, hisl]) h0 hdom
        have hfit := fits_of_fapps_ne M (σOf vs) (ctorEnd_resp M _ _ _ _) _ _ ρ0 _ hlenC hne
        have he := fapps_piLam M (σOf vs) (ctorEnd_resp M (σOf vs) (famDataOf a) j
          (a.constructorViews i).fields.length) (foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals (a.constructorViews i).parameters.length
              (a.constructorViews i).fields.length ++ (a.constructorViews i).resultIndices)) _ ρ0 _ hfit
        rw [piLam_foldApps_const] at he
        refine hW.trans (he.trans ?_)
        unfold ctorEnd cond
        rw [hd, push_append, ← hxsl, lastVals_push]
        exact Equiv.rfl
  exact hV

/-- A minor premise maps fitting fields into the motive at the constructor's value. -/
theorem minor_ok {M : Interp.{4}} {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (hshapes : ∀ i : Fin a.constructors.length, ∃ fuel shapes, (∀ s, s ∈ shapes → s = .nonrecursive) ∧
      shapes.length = (a.constructorViews i).fields.length ∧ derivedMinor a i fuel shapes = a.minorTypes[i.val]?)
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
    (j : Nat) (xs : List PSet.{4}) (hcf : CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs) :
    fapps (ms.getD j pempty) xs ∈ Ed M (fapps mo (is ++ [ctorV M (σOf vs) (famDataOf a) j xs])) := by
  obtain ⟨c, hc, hxs, hri⟩ := hcf
  have hjk : j < a.constructors.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    rwa [famDataOf_ctors_length] at this
  let i : Fin a.constructors.length := ⟨j, hjk⟩
  have hc' : c = ((a.constructorViews i).fields, (a.constructorViews i).resultIndices) := by
    have := famDataOf_ctor a i
    rw [hc] at this; exact Option.some.inj this
  subst hc'
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hjm : j < ms.length := by rw [hmsl, a.minorCount]; exact hjk
  -- the minor premise's type
  have hmj := TelFits_get a.minorTypes _ ms hms j (by rw [a.minorCount]; exact hjk)
  obtain ⟨fuel, shapes, hnr, hsl, hdm⟩ := hshapes i
  have hder := derivedMinor_nonrec a i fuel shapes hnr hsl
  rw [hder] at hdm
  have hmt : a.minorTypes[j]'(by rw [a.minorCount]; exact hjk) = _ :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hdm.symm)
  rw [hmt] at hmj
  -- the environment before the minor premise
  have hρpre : push (ms.take j) (vcons mo (push ps ρ0)) = push (mo :: ms.take j) (push ps ρ0) := rfl
  have htl : (mo :: ms.take j).length = 1 + j := by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)]; omega
  rw [hρpre] at hmj
  have hxsl : xs.length = (a.constructorViews i).fields.length := hxs.length
  -- fitting the lifted fields
  have hfitL : TelFits M (σOf vs) (liftFields (1 + j) (a.constructorViews i).fields 0)
      (push (mo :: ms.take j) (push ps ρ0)) xs := by
    have := (TelFits_liftFields M (σOf vs) (mo :: ms.take j) (push ps ρ0) (a.constructorViews i).fields [] xs).mpr hxs
    rw [htl] at this; exact this
  have hmem := mem_fapps M (σOf vs) _ _ _ _ xs hmj hfitL
  -- the end of the minor type
  have hend : den M (σOf vs) (push xs (push (mo :: ms.take j) (push ps ρ0)))
      (.app (foldApps (liftIter (a.constructorViews i).fields.length (.bvar j))
          ((a.constructorViews i).resultIndices.map
            (Rcic.Declarative.lift (a.constructorViews i).fields.length (1 + j))))
        (accAfter (a.constructorViews i).fields.length
          (foldApps (.const (a.family.ref + 1 + j) (policyFamilyLevels a.family))
            (policyParameterLocals a.family.parameters.length (1 + j))))) =
      fapp (fapps mo ((a.constructorViews i).resultIndices.map (den M (σOf vs) (push xs (push ps ρ0)))))
        (fapps (M.μ (a.family.ref + 1 + j) ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ xs)) := by
    show fapp (den M (σOf vs) _ (foldApps _ _)) (den M (σOf vs) _ (accAfter _ _)) = _
    rw [← hxsl, den_accAfter, den_foldApps, den_liftIter, List.map_map]
    have h1 : den M (σOf vs) (push (mo :: ms.take j) (push ps ρ0)) (.bvar j) = mo := by
      show push (mo :: ms.take j) (push ps ρ0) j = mo
      have := push_cons_len_index mo (ms.take j) (push ps ρ0)
      rwa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm)] at this
    have h2 : (den M (σOf vs) (push xs (push (mo :: ms.take j) (push ps ρ0))) ∘
        Rcic.Declarative.lift xs.length (1 + j)) = den M (σOf vs) (push xs (push ps ρ0)) := by
      funext e
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
    rw [h1, h2, h3, fapps_append]
  rw [hend] at hmem
  -- comparing with the goal
  rw [fapps_append]
  have e1 : Equiv (fapps mo ((a.constructorViews i).resultIndices.map (den M (σOf vs) (push xs (push ps ρ0)))))
      (fapps mo is) := fapps_congr_args mo hri
  have hV := ctorApp_ctorV a vs hfamμ hctorμ ps mo is hpsl hisl hmo hisfit j hjk xs hxsl _
    (mem_congr_right (ed_congr M (fapp_congr e1 Equiv.rfl)) hmem)
  exact mem_congr_right (ed_congr M (fapp_congr e1 hV)) hmem

theorem ihArgs_famDataOf_free {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {M : Interp.{4}}
    (a : RecursorEliminationAdmitted E r m)
    (hfree : ∀ (i : Fin a.constructors.length) (T : Expr Nat), T ∈ (a.constructorViews i).fields →
      occursConst a.family.ref T = false) {σ : Nat → Nat} {ρp : Nat → PSet.{4}} {is : List PSet.{4}} {j : Nat}
    {xs : List PSet.{4}} (hcf : CtorFits M σ (famDataOf a).ctors ρp is j xs) (g : PSet.{4} → PSet.{4}) :
    ihArgs (famDataOf a).fref g (ctorFieldsOf (famDataOf a) j) xs = xs := by
  obtain ⟨c, hc, hf, _⟩ := hcf
  have hjk : j < a.constructors.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    rwa [famDataOf_ctors_length] at this
  have hc' := famDataOf_ctor a ⟨j, hjk⟩
  rw [hc] at hc'
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields, (a.constructorViews ⟨j, hjk⟩).resultIndices) :=
    Option.some.inj hc'
  have hcf : ctorFieldsOf (famDataOf a) j = c.1 := by
    unfold ctorFieldsOf; rw [List.getD_eq_getElem?_getD, hc]; rfl
  rw [hcf]
  refine ihArgs_free _ g c.1 xs (fun A hA => ?_) hf.length
  rw [hcc] at hA
  exact hfree ⟨j, hjk⟩ A hA

/-- An element of a proposition of the model is `∅`. -/
theorem ed_of_mem_U0 (M : Interp.{4}) {X : PSet.{4}} (hX : X ∈ U W4 0) {y : PSet.{4}} (hy : y ∈ Ed M X) :
    Equiv y pempty := by
  obtain ⟨S, hS, hXS⟩ := mem_sImage_tyv.mp hX
  have hSp := mem_propSets.mp hS
  have hy' := mem_congr_right ((ed_congr M hXS).trans (ed_tyv M (Or.inl hSp))) hy
  exact hSp y hy'

/-- Under elimination into `Prop`, the motive's value at fitting indices and a
member of the family is a proposition: its elements are `∅`. -/
theorem motive_prop_elem {M : Interp.{4}} (hU : M.U = U W4) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) (vs : List Nat) (ps : List PSet.{4}) (mo : PSet.{4})
    (is : List PSet.{4}) (z : PSet.{4}) (hpsl : ps.length = a.family.parameters.length)
    (hisl : is.length = a.family.indices.length) (hpol : a.policy = .propOnly)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hisfit : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (hzm : z ∈ Ed M (fapps (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ is))) :
    ∀ y, y ∈ Ed M (fapps mo (is ++ [z])) → Equiv y pempty := by
  intro y hy
  have hmt : policyMotiveType a.family a.policy = policyPi (a.family.indices ++
      [foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyLocals (a.family.parameters.length + a.family.indices.length))]) (.sort .zero) := by
    rw [hpol, policyPi_append]; rfl
  rw [hmt] at hmo
  have hzF : z ∈ Ed M (den M (σOf vs) (push is (push ps ρ0))
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyLocals (a.family.parameters.length + a.family.indices.length)))) := by
    have hF := Fapp_den M (σOf vs) a.family.ref (policyFamilyLevels a.family) ps is ρ0
    rw [hpsl, hisl] at hF
    rw [hF]; exact hzm
  have hX := mem_fapps M (σOf vs) (.sort .zero) _ (push ps ρ0) mo (is ++ [z]) hmo
    (TelFits.append hisfit ⟨hzF, trivial⟩)
  have hX' : fapps mo (is ++ [z]) ∈ U W4 0 := by
    have : den M (σOf vs) (push (is ++ [z]) (push ps ρ0)) (.sort .zero) = tyv (M.U 0) := rfl
    rw [this, hU] at hX
    exact mem_congr_right (ed_tyv M (U4_dich 0)) hX
  exact ed_of_mem_U0 M hX' hy

/-- The recursor's value is an element of its type, given the minor obligation. -/
theorem recVal_mem_gen {M : Interp.{4}} (hU : M.U = U W4) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal M W4 (σOf vs) (famDataOf a)))
    (hsafe : evalTotal (σOf vs) a.family.resultLevel = 0 → a.policy = .anySort → ∀ c, (famDataOf a).ctors = [c] →
      ∀ ps is xs, TelFits M (σOf vs) a.family.parameters ρ0 ps →
        CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is 0 xs → LEq xs (recon c is))
    (hpfree : evalTotal (σOf vs) a.family.resultLevel = 0 → a.policy = .anySort →
      ∀ ps is xs, TelFits M (σOf vs) a.family.parameters ρ0 ps →
        CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is 0 xs →
      ∀ (i : Fin a.constructors.length) (T : Expr Nat), T ∈ (a.constructorViews i).fields →
        occursConst a.family.ref T = false)
    (g : List PSet.{4} → PSet.{4} → PSet.{4})
    (hg : evalTotal (σOf vs) a.family.resultLevel ≠ 0 → ∀ ms x, g ms x = recCore M (famDataOf a) ms x)
    (hminH : ∀ (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4}),
      TelFits M (σOf vs) a.family.parameters ρ0 ps →
      ps.length = a.family.parameters.length → is.length = a.family.indices.length →
      mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)) →
      TelFits M (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms →
      TelFits M (σOf vs) a.family.indices (push ps ρ0) is →
      ∀ j xs, CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs →
        fapps (ms.getD j pempty) (ihArgs (famDataOf a).fref (g ms)
          (ctorFieldsOf (famDataOf a) j) xs) ∈ Ed M (fapps mo (is ++ [ctorV M (σOf vs) (famDataOf a) j xs]))) :
    piLam M (σOf vs) (recEnd M (σOf vs) (famDataOf a)) ρ0 m.mtype ∈ Ed M (den M (σOf vs) ρ0 m.mtype) := by
  have hk : a.minorTypes.length = a.constructors.length := a.minorCount
  have hkf : (famDataOf a).ctors.length = a.constructors.length := famDataOf_ctors_length a
  rw [a.recursorType, policyRecursorType_eq]
  refine piLam_mem M _ (recEnd_resp M _ _) _ ρ0 ?_
  refine piGood_policyPi_fits M _ _ _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, rest, rfl, hps, hrest⟩ := TelFits_split _ _ ρ0 zs hz
  obtain ⟨mo, rest', rfl, hmo, hrest'⟩ : ∃ mo rest', rest = mo :: rest' ∧
      mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)) ∧
      TelFits M (σOf vs) (a.minorTypes ++ (liftFields (a.minorTypes.length + 1) a.family.indices 0 ++ _))
        (vcons mo (push ps ρ0)) rest' := by
    cases rest with
    | nil => exact absurd hrest id
    | cons mo rest' => exact ⟨mo, rest', rfl, hrest.1, hrest.2⟩
  obtain ⟨ms, rest'', rfl, hms, hrest''⟩ := TelFits_split _ _ _ rest' hrest'
  obtain ⟨is, zl, rfl, his, hzl⟩ := TelFits_split _ _ _ rest'' hrest''
  have hisfit : TelFits M (σOf vs) a.family.indices (push ps ρ0) is := by
    have hmsl0 : ms.length = a.minorTypes.length := hms.length
    have := (TelFits_liftFields M (σOf vs) (mo :: ms) (push ps ρ0) a.family.indices [] is).mp
    apply this
    show TelFits M (σOf vs) (liftFields (ms.length + 1) a.family.indices 0) (push ms (vcons mo (push ps ρ0))) is
    rw [hmsl0]; exact his
  obtain ⟨z, rfl, hzm⟩ : ∃ z, zl = [z] ∧ z ∈ Ed M (den M (σOf vs) (push is (push ms (vcons mo (push ps ρ0))))
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals a.family.parameters.length (a.minorTypes.length + 1 + a.family.indices.length) ++
          policyLocals a.family.indices.length))) := by
    match zl, hzl with
    | [z], ⟨hz, _⟩ => exact ⟨z, rfl, hz⟩
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hisl : is.length = a.family.indices.length := by rw [his.length, liftFields_length']
  have hpsl : ps.length = a.family.parameters.length := hps.length
  -- the result
  have hres := den_recResult M (σOf vs) mo z ms is (push ps ρ0)
  rw [hmsl, hisl, ← push_cons_eq] at hres
  rw [hres]
  -- the major premise's type
  have hmajT : den M (σOf vs) (push is (push ms (vcons mo (push ps ρ0))))
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals a.family.parameters.length (a.minorTypes.length + 1 + a.family.indices.length) ++
          policyLocals a.family.indices.length)) =
      fapps (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ is) := by
    have e1 : push is (push ms (vcons mo (push ps ρ0))) = push (ps ++ (mo :: (ms ++ is))) ρ0 := by
      rw [push_append]
      show push is (push ms (vcons mo (push ps ρ0))) = push (ms ++ is) (vcons mo (push ps ρ0))
      rw [push_append]
    have e2 : a.minorTypes.length + 1 + a.family.indices.length = (mo :: (ms ++ is)).length := by
      simp [hmsl, hisl]; omega
    have hA : (policyParameterLocals a.family.parameters.length
        (a.minorTypes.length + 1 + a.family.indices.length)).map
        (den M (σOf vs) (push is (push ms (vcons mo (push ps ρ0))))) = ps := by
      rw [e1, e2, ← hpsl]; exact den_paramLocals M _ ps _ ρ0
    have hB : (policyLocals a.family.indices.length).map
        (den M (σOf vs) (push is (push ms (vcons mo (push ps ρ0))))) = is := by
      rw [← hisl]; exact den_policyLocals M _ is _
    rw [den_foldApps, List.map_append, hA, hB]
    rfl
  rw [hmajT] at hzm
  have hfit := fam_app_fits W4 (σOf vs) (famDataOf a) hfamμ ps is
    (by simp [famDataOf, hpsl, hisl]) hzm
  -- now the recursor's end obligation
  refine (recEnd_mem M (σOf vs) (famDataOf a) ps mo ms is z ρ0 (by rw [hmsl, hk, hkf])
    (by simpa [famDataOf] using hisl)
    (CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is)
    (fun j xs ⟨c, hc, _, _⟩ => by
      have := (List.getElem?_eq_some_iff.mp hc).1; exact this) ?_ ?_ (g ms) (fun h0 x => hg h0 ms x) ?_ ?_ ?_ ?_ ?_ ?_)
  · intro h0
    obtain ⟨j, xs, hc, he⟩ := famEnd_type_mem W4 (σOf vs) (famDataOf a) ps is
      (by simpa [famDataOf] using hisl) h0 hfit.2
    obtain ⟨c, hcj, hcf, _⟩ := hc
    refine ⟨j, xs, ⟨c, hcj, hcf, by assumption⟩, he, ?_⟩
    unfold nfOf; rw [hcj]; exact hcf.length
  · intro h0
    exact famEnd_prop_mem W4 (σOf vs) (famDataOf a) ps is (by simpa [famDataOf] using hisl) h0 hfit.2
  · exact hminH ps mo ms is hps hpsl hisl hmo hms hisfit
  · intro j xs hcf
    obtain ⟨c, hc, hf, _⟩ := hcf
    unfold nfOf; rw [hc]; exact hf.length
  · intro h0 hpol y hy
    exact motive_prop_elem hU a vs ps mo is z hpsl hisl hpol hmo hisfit hzm y hy
  · exact fun h0 hpol c hc xs hcf => hsafe h0 hpol c hc ps is xs hps hcf
  · intro h0 hpol c hcs xs hcf A hA
    have hk0 : 0 < a.constructors.length := by rw [← famDataOf_ctors_length a, hcs]; exact Nat.zero_lt_one
    have hc00 := famDataOf_ctor a ⟨0, hk0⟩
    rw [hcs] at hc00
    have hc0 : c = ((a.constructorViews ⟨0, hk0⟩).fields, (a.constructorViews ⟨0, hk0⟩).resultIndices) :=
      Option.some.inj hc00
    rw [hc0] at hA
    exact hpfree h0 hpol ps is xs hps hcf ⟨0, hk0⟩ A hA
  · intro h0 hpol
    have hpol' : a.policy = .anySort := hpol
    have hs : EliminationSelection a.family.resultLevel a.constructors.length
        (∀ i, (a.constructorViews i).AllFieldsSafe) .anySort := by
      rw [← hpol']; exact a.selected
    rw [famDataOf_ctors_length]
    rcases (EliminationSelection.anySort_iff _ _ _).mp hs with ht | ⟨_, hk0 | ⟨hk1, _⟩⟩
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp (ht (σOf vs)))
    · omega
    · omega


/-- **The recursor's value is an element of its type** (non-recursive constructors). -/
theorem recVal_mem {M : Interp.{4}} (hU : M.U = U W4) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (hshapes : ∀ i : Fin a.constructors.length, ∃ fuel shapes, (∀ s, s ∈ shapes → s = .nonrecursive) ∧
      shapes.length = (a.constructorViews i).fields.length ∧ derivedMinor a i fuel shapes = a.minorTypes[i.val]?)
    (hfamμ : Equiv (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal M W4 (σOf vs) (famDataOf a)))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (M.μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam M (σOf vs) (ctorEnd M (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length) ρ0
          (a.constructors[i.val]).mtype))
    (hsafe : evalTotal (σOf vs) a.family.resultLevel = 0 → a.policy = .anySort → ∀ c, (famDataOf a).ctors = [c] →
      ∀ ps is xs, TelFits M (σOf vs) a.family.parameters ρ0 ps →
        CtorFits M (σOf vs) (famDataOf a).ctors (push ps ρ0) is 0 xs → LEq xs (recon c is))
    (hfree : ∀ (i : Fin a.constructors.length) (T : Expr Nat), T ∈ (a.constructorViews i).fields →
      occursConst a.family.ref T = false) :
    piLam M (σOf vs) (recEnd M (σOf vs) (famDataOf a)) ρ0 m.mtype ∈ Ed M (den M (σOf vs) ρ0 m.mtype) :=
  recVal_mem_gen hU a vs hfamμ hsafe (fun _ _ _ _ _ _ _ => hfree) (recCore M (famDataOf a)) (fun _ _ _ => rfl)
    (fun ps mo ms is _ hpsl hisl hmo hms hisfit j xs hcf => by
      rw [ihArgs_famDataOf_free a hfree hcf]
      exact minor_ok a vs hshapes hfamμ hctorμ ps mo ms is hpsl hisl hmo hms hisfit j xs hcf)

end PSet

end Rcic.F3
