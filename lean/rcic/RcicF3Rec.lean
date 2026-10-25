import rcic.RcicF3RecCore

/-!
# F3 S5a-5: the recursor

`recEnd` is the recursor's end value, read at the environment after
parameters, motive, minors, indices and major premise:

- for a `Type` family it decodes the major premise `dataVal j xs` (its tag by
  `findIdx`, its fields by `untup`) and applies the `j`-th minor to the fields;
- for a `Prop` family with large elimination and one constructor it applies
  the minor to the fields reconstructed from the indices (`recon`: a field
  revealed in the result indices is read there, any other field is `∅`);
- otherwise (`Prop` with elimination into `Prop`) it is `∅`.

`recEnd_mem` proves the end obligation from semantic facts about the
recursor's telescope (the major premise lies in the family's fibre, each
minor maps fitting fields into the motive at the constructor's value, the
motive is `Prop`-valued under `propOnly`, the reconstruction agrees with
fitting fields); `RcicF3Minor` derives these facts from the admitted syntax.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- The first position of `e` in `es`. -/
def posOf (e : Expr Nat) : List (Expr Nat) → Option Nat
  | [] => none
  | e' :: es => if e' = e then some 0 else (posOf e es).map (· + 1)

/-- Field `i` of a constructor with `nf` fields, reconstructed from the indices. -/
def reconField (ri : List (Expr Nat)) (nf i : Nat) (is : List PSet.{T}) : PSet.{T} :=
  match posOf (.bvar (nf - 1 - i)) ri with
  | some p => is.getD p pempty
  | none => pempty

/-- All fields of a constructor, reconstructed from the indices. -/
def recon (c : List (Expr Nat) × List (Expr Nat)) (is : List PSet.{T}) : List PSet.{T} :=
  (List.range c.1.length).map fun i => reconField c.2 c.1.length i is

/-- The end value of a `Prop` family's recursor. -/
def propRecEnd (fd : FamData) (minor0 : PSet.{T}) (is : List PSet.{T}) : PSet.{T} :=
  match fd.policy, fd.ctors with
  | .anySort, [c] => fapps minor0 (recon c is)
  | _, _ => pempty

/-- The minors in the recursor's environment after `q` indices and the major, in order. -/
def minorsOf (q k : Nat) (ρ : Nat → PSet.{T}) : List PSet.{T} := (List.range k).map fun j => ρ (q + k - j)

/-- The recursor's end value. -/
noncomputable def recEnd (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{T}) : PSet.{T} :=
  cond M.dec (evalTotal σ fd.resLevel = 0)
    (propRecEnd fd (ρ (fd.indices.length + fd.ctors.length))
      (lastVals fd.indices.length (shiftρ 1 ρ)))
    (recCore M fd (minorsOf fd.indices.length fd.ctors.length ρ) (ρ 0))

theorem minorsOf_congr (q k : Nat) {ρ ρ' : Nat → PSet.{T}} (h : ∀ i, Equiv (ρ i) (ρ' i)) :
    LEq (minorsOf q k ρ) (minorsOf q k ρ') := by
  unfold minorsOf
  induction List.range k with
  | nil => trivial
  | cons i r ih => exact ⟨h _, ih⟩

theorem reconField_congr (ri : List (Expr Nat)) (nf i : Nat) {is is' : List PSet.{T}} (h : LEq is is') :
    Equiv (reconField ri nf i is) (reconField ri nf i is') := by
  unfold reconField
  cases posOf (.bvar (nf - 1 - i)) ri with
  | none => exact Equiv.rfl
  | some p =>
      show Equiv (is.getD p pempty) (is'.getD p pempty)
      induction is generalizing is' p with
      | nil => cases is' with
        | nil => exact Equiv.rfl
        | cons _ _ => exact h.elim
      | cons x xs ih => cases is' with
        | nil => exact h.elim
        | cons y ys =>
            cases p with
            | zero => exact h.1
            | succ p => exact ih h.2 p

theorem recon_congr (c : List (Expr Nat) × List (Expr Nat)) {is is' : List PSet.{T}} (h : LEq is is') :
    LEq (recon c is) (recon c is') := by
  unfold recon
  induction List.range c.1.length with
  | nil => trivial
  | cons i r ih => exact ⟨reconField_congr c.2 c.1.length i h, ih⟩

theorem recEnd_resp (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) : EnvResp (recEnd M σ fd) := by
  intro ρ ρ' h
  unfold recEnd
  refine cond_congr Iff.rfl ?_ ?_
  · unfold propRecEnd
    have hl := lastVals_congr fd.indices.length (ρ := shiftρ 1 ρ) (ρ' := shiftρ 1 ρ') (fun i => h (i + 1))
    cases fd.policy with
    | anySort =>
        match fd.ctors with
        | [] => exact Equiv.rfl
        | [c] => exact (fapps_congr (h _) _).trans (fapps_congr_args _ (recon_congr c hl))
        | _ :: _ :: _ => exact Equiv.rfl
    | propOnly => exact Equiv.rfl
  · exact recCore_congr M fd (minorsOf_congr _ _ h) _ _ (h 0)

/-- The value of constructor `j` at fields `xs`, as the recursor sees it. -/
def ctorV (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (j : Nat) (xs : List PSet.{T}) : PSet.{T} :=
  cond M.dec (evalTotal σ fd.resLevel = 0) pempty (dataVal j xs)

theorem LEq_append : {xs xs' : List PSet.{T}} → LEq xs xs' → {ys ys' : List PSet.{T}} → LEq ys ys' →
    LEq (xs ++ ys) (xs' ++ ys')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, ⟨h, hs⟩, _, _, h' => ⟨h, LEq_append hs h'⟩

theorem push_cons_eq (ps : List PSet.{T}) (mo : PSet.{T}) (ms is : List PSet.{T}) (z : PSet.{T})
    (ρ : Nat → PSet.{T}) :
    push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ = vcons z (push is (push ms (vcons mo (push ps ρ)))) := by
  rw [push_append]
  show push (ms ++ (is ++ [z])) (vcons mo (push ps ρ)) = _
  rw [push_append, push_append]
  rfl

theorem recEnv_indices (ps : List PSet.{T}) (mo : PSet.{T}) (ms is : List PSet.{T}) (z : PSet.{T})
    (ρ : Nat → PSet.{T}) :
    lastVals is.length (shiftρ 1 (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) = is := by
  rw [push_cons_eq]
  exact lastVals_push is _

theorem recEnv_minor (ps : List PSet.{T}) (mo : PSet.{T}) (ms is : List PSet.{T}) (z : PSet.{T})
    (ρ : Nat → PSet.{T}) (j : Nat) (hj : j < ms.length) :
    push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ (is.length + ms.length - j) = ms[j] := by
  rw [push_cons_eq, show is.length + ms.length - j = (is.length + ms.length - j - 1) + 1 by omega]
  show push is (push ms (vcons mo (push ps ρ))) (is.length + ms.length - j - 1) = _
  rw [show is.length + ms.length - j - 1 = (ms.length - 1 - j) + is.length by omega, push_ge,
    push_lt ms _ _ (by omega)]
  congr 1
  omega

/-- **The recursor's end obligation**, from semantic facts about its telescope. -/

theorem minorsOf_env (ps : List PSet.{T}) (mo : PSet.{T}) (ms is : List PSet.{T}) (z : PSet.{T})
    (ρ : Nat → PSet.{T}) {q k : Nat} (hms : ms.length = k) (his : is.length = q) :
    minorsOf q k (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) = ms := by
  subst hms his
  apply List.ext_getElem
  · simp [minorsOf]
  · intro j h1 h2
    simp only [minorsOf, List.getElem_map, List.getElem_range]
    exact recEnv_minor ps mo ms is z ρ j h2

theorem recEnd_mem (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (ps : List PSet.{T}) (mo : PSet.{T})
    (ms is : List PSet.{T}) (z : PSet.{T}) (ρ : Nat → PSet.{T})
    (hms : ms.length = fd.ctors.length) (his : is.length = fd.indices.length)
    (CF : Nat → List PSet.{T} → Prop) (hCF : ∀ j xs, CF j xs → j < fd.ctors.length)
    (hmajT : evalTotal σ fd.resLevel ≠ 0 →
      ∃ j xs, CF j xs ∧ Equiv z (dataVal j xs) ∧ xs.length = nfOf fd j)
    (hmajP : evalTotal σ fd.resLevel = 0 → (∃ j xs, CF j xs) ∧ Equiv z pempty)
    (g : PSet.{T} → PSet.{T}) (hg : evalTotal σ fd.resLevel ≠ 0 → ∀ x, g x = recCore M fd ms x)
    (hmin : ∀ j xs, CF j xs → fapps (ms.getD j pempty) (ihArgs fd.fref g (ctorFieldsOf fd j) xs) ∈
      Ed M (fapps mo (is ++ [ctorV M σ fd j xs])))
    (hlen : ∀ j xs, CF j xs → xs.length = nfOf fd j)
    (hpo : evalTotal σ fd.resLevel = 0 → fd.policy = .propOnly →
      ∀ y, y ∈ Ed M (fapps mo (is ++ [z])) → Equiv y pempty)
    (hsafe : evalTotal σ fd.resLevel = 0 → fd.policy = .anySort → ∀ c, fd.ctors = [c] →
      ∀ xs, CF 0 xs → LEq xs (recon c is))
    (hsafeFree : evalTotal σ fd.resLevel = 0 → fd.policy = .anySort → ∀ c, fd.ctors = [c] →
      ∀ xs, CF 0 xs → ∀ A, A ∈ c.1 → occursConst fd.fref A = false)
    (hsel : evalTotal σ fd.resLevel = 0 → fd.policy = .anySort → fd.ctors.length ≤ 1)
    (hch : evalTotal σ fd.resLevel ≠ 0 → ∀ j xs, CF j xs →
      ihChildL fd.fref (dataVal j xs) (ctorFieldsOf fd j) xs) :
    recEnd M σ fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) ∈ Ed M (fapps mo (is ++ [z])) := by
  have hz : push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ 0 = z := by rw [push_cons_eq]; rfl
  have hiv : lastVals fd.indices.length (shiftρ 1 (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) = is := by
    rw [← his]; exact recEnv_indices ps mo ms is z ρ
  have hmv : ∀ j, j < fd.ctors.length →
      push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ (fd.indices.length + fd.ctors.length - j) = ms.getD j pempty := by
    intro j hj
    rw [← his, ← hms, recEnv_minor ps mo ms is z ρ j (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ms.length by omega)]
  have zctor : ∀ (j : Nat) (xs : List PSet.{T}) (F : PSet.{T}), Equiv (fapps mo (is ++ [ctorV M σ fd j xs]))
      (fapps mo (is ++ [z])) → F ∈ Ed M (fapps mo (is ++ [ctorV M σ fd j xs])) → F ∈ Ed M (fapps mo (is ++ [z])) :=
    fun _ _ _ e h => mem_congr_right (ed_congr M e) h
  unfold recEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue h0 =>
      show propRecEnd fd _ _ ∈ _
      rw [hiv]
      obtain ⟨⟨j, xs, hc⟩, hz0⟩ := hmajP h0
      have hcv : ∀ j xs, Equiv (ctorV M σ fd j xs) z := by
        intro j xs
        unfold ctorV cond
        rw [hd]
        exact hz0.symm
      have hm := zctor j xs _ (fapps_congr_args mo (LEq_append (LEq.refl is) ⟨hcv j xs, trivial⟩))
        (hmin j xs hc)
      cases hpol : fd.policy with
      | propOnly =>
          have e : propRecEnd fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ
              (fd.indices.length + fd.ctors.length)) is = pempty := by
            unfold propRecEnd; rw [hpol]
          rw [e]
          exact mem_congr_left (hpo h0 hpol _ hm) hm
      | anySort =>
          have hle := hsel h0 hpol
          have hjk := hCF j xs hc
          cases hcs : fd.ctors with
          | nil => rw [hcs] at hjk; exact absurd hjk (Nat.not_lt_zero _)
          | cons c cs =>
            cases cs with
            | cons _ _ => rw [hcs] at hle; simp at hle
            | nil =>
              have hj0 : j = 0 := by rw [hcs] at hjk; simp at hjk; omega
              subst hj0
              have hrec := hsafe h0 hpol c hcs xs hc
              have hfr : ihArgs fd.fref g (ctorFieldsOf fd 0) xs = xs := by
                refine ihArgs_free _ _ _ _ (fun A hA => hsafeFree h0 hpol c hcs xs hc A ?_) ?_
                · unfold ctorFieldsOf at hA; rw [hcs] at hA; exact hA
                · rw [hlen 0 xs hc]; unfold nfOf ctorFieldsOf; rw [hcs]; rfl
              rw [hfr] at hm
              have hm0 := hmv 0 (by rw [hcs]; exact Nat.zero_lt_one)
              rw [Nat.sub_zero, hcs] at hm0
              have hm0' : push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ (fd.indices.length + 1) =
                  ms.getD 0 pempty := hm0
              have e : propRecEnd fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ
                  (fd.indices.length + 1)) is = fapps (ms.getD 0 pempty) (recon c is) := by
                unfold propRecEnd; rw [hpol, hm0', hcs]
              show propRecEnd fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ (fd.indices.length + 1)) is ∈ _
              rw [e]
              exact mem_congr_left (fapps_congr_args _ hrec) hm
  | isFalse h0 =>
      have hgr : g = recCore M fd ms := funext (hg h0)
      subst hgr
      obtain ⟨j, xs, hc, hzd, hlen'⟩ := hmajT h0
      have hjk := hCF j xs hc
      show recCore M fd (minorsOf fd.indices.length fd.ctors.length (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ))
        (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ 0) ∈ _
      rw [minorsOf_env ps mo ms is z ρ hms his, hz]
      have hcv : Equiv (ctorV M σ fd j xs) z := by
        unfold ctorV cond
        rw [hd]
        exact hzd.symm
      exact mem_congr_left (recCore_data M fd ms hzd hjk hlen'
        (ihChildL_congr' hzd.symm (ctorFieldsOf fd j) xs (hch h0 j xs hc))).symm
        (zctor j xs _ (fapps_congr_args mo (LEq_append (LEq.refl is) ⟨hcv, trivial⟩)) (hmin j xs hc))

end PSet

end Rcic.F3
