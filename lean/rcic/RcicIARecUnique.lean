import rcic.RcicTypedScopeCheck

/-!
# IA-021, the "unique" half: the recursor admission derives is determined (IA-rec segment C)

05 §13 (`docs/rcic/05_INDUCTIVE_ADMISSION.md:255`): "The derived recursor type is checked in the
private derivation scope. Derivation must be unique." IA-021 (`05:364`): "recursor well typed and
unique". This module is the unique half. The typed half is segments A and D.

Admission's recursor is `RecursorEliminationAdmitted` (`RcicInductivePolicy.lean:220`), with its minors
fixed by `MinorPremisesMatch` (`RcicIndGroupJudgment.lean:700`). Two such admissions at the same
`(E, r)` agree on the recursor:

* `recursorAdmitted_familyRef_eq`: the family. A family at a different ref would sit inside the other
  admission's constructor block, where every member is a constructor.
* `IA021T_recursor_unique`: with the same parameter count and the same policy, the stored types and
  arities are equal. The constructors are the members after the family; their telescopes are read off
  their stored types; the field shapes do not depend on the analysis bound (`fieldShapesFuel_agree`),
  and neither does the derived minor (`derivedMinor_agree`, new).
* `IA021T_policy_unique`: the policies are equal, except at a singleton `Prop` family whose two
  admissions read the all-fields-safe test differently (W3). That test reads the fields' recorded
  levels. On the typed root they are typed levels, which agree only up to sort uniqueness on the
  prefix scope (typed Row 1). No row is assumed here.

The parameter count is a premise because it is a candidate datum (05 §2), not an admission output.
`RecursorEliminationAdmitted` records no candidate. An empty family `I : Type → Type` is admitted with 0
and with 1 parameter, and the two recursor types differ (`RcicIARecUniquePins`).

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) telescope and spine injectivity -/

/-- two telescopes of the same length are equal exactly when their domains and bodies are. -/
theorem policyPi_inj_length : (xs ys : List (Expr Nat)) → {X Y : Expr Nat} →
    xs.length = ys.length → policyPi xs X = policyPi ys Y → xs = ys ∧ X = Y
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | x :: xs, y :: ys, _, _, hl, h => by
      simp only [policyPi] at h
      injection h with h1 h2
      obtain ⟨h3, h4⟩ := policyPi_inj_length xs ys (Nat.succ.inj hl) h2
      exact ⟨by rw [h1, h3], h4⟩
  | [], _ :: _, _, _, hl, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], _, _, hl, _ => (Nat.succ_ne_zero _ hl).elim

/-- telescopes whose bodies are not Π-types are equal exactly when their domains and bodies are. -/
theorem policyPi_inj_notPi : (xs ys : List (Expr Nat)) → {X Y : Expr Nat} →
    (∀ A B, X ≠ .pi A B) → (∀ A B, Y ≠ .pi A B) →
    policyPi xs X = policyPi ys Y → xs = ys ∧ X = Y
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], y :: ys, _, _, hX, _, h => absurd h (hX _ _)
  | x :: xs, [], _, _, _, hY, h => absurd h.symm (hY _ _)
  | x :: xs, y :: ys, _, _, hX, hY, h => by
      simp only [policyPi] at h
      injection h with h1 h2
      obtain ⟨h3, h4⟩ := policyPi_inj_notPi xs ys hX hY h2
      exact ⟨by rw [h1, h3], h4⟩

theorem foldApps_notPi : (xs : List (Expr Nat)) → {h : Expr Nat} → (∀ A B, h ≠ .pi A B) →
    ∀ A B, foldApps h xs ≠ .pi A B
  | [], _, hh => hh
  | _ :: xs, _, _ => foldApps_notPi xs (fun _ _ he => Expr.noConfusion he)

theorem sort_notPi (l : Level) : ∀ A B, (Expr.sort l : Expr Nat) ≠ .pi A B :=
  fun _ _ h => Expr.noConfusion h

/-! ## (2) the derived minor does not depend on the analysis bound -/

theorem funIHType_mono (E : ResolvedEnv) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {nparams : Nat} {A M : Expr Nat} {inner : Nat} {ih : Expr Nat}
    (h : funIHType E fuel nparams A M inner = some ih) :
    funIHType E fuel' nparams A M inner = some ih := by
  unfold funIHType at h ⊢
  cases hp : piTelescopeFuel E fuel (lift 0 1 A) with
  | none => rw [hp] at h; exact Option.noConfusion h
  | some p => rw [hp] at h; rw [piTelescopeFuel_mono E hle hp]; exact h

theorem minorFromTelescope_mono (E : ResolvedEnv) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (nparams : Nat) : (shapes : List FieldShape) → {M ctorAcc T R : Expr Nat} →
    minorFromTelescope E fuel nparams M ctorAcc shapes T = some R →
    minorFromTelescope E fuel' nparams M ctorAcc shapes T = some R
  | [], M, ctorAcc, T, R, h => by simpa only [minorFromTelescope] using h
  | .nonrecursive :: ss, M, ctorAcc, T, R, h => by
      cases T with
      | pi A B =>
          simp only [minorFromTelescope] at h ⊢
          cases hr : minorFromTelescope E fuel nparams (lift 0 1 M) (.app (lift 0 1 ctorAcc) (.bvar 0)) ss B with
          | none => rw [hr] at h; exact Option.noConfusion h
          | some rest =>
              rw [hr] at h
              rw [minorFromTelescope_mono E hle nparams ss hr]
              exact h
      | _ => simp only [minorFromTelescope] at h; exact Option.noConfusion h
  | .recursive inner :: ss, M, ctorAcc, T, R, h => by
      cases T with
      | pi A B =>
          simp only [minorFromTelescope] at h ⊢
          cases hih : funIHType E fuel nparams A M inner with
          | none => rw [hih] at h; exact Option.noConfusion h
          | some ih =>
              rw [hih] at h
              rw [funIHType_mono E hle hih]
              cases hr : minorFromTelescope E fuel nparams (lift 0 2 M) (.app (lift 0 2 ctorAcc) (.bvar 1)) ss
                  (lift 0 1 B) with
              | none => rw [hr] at h; exact Option.noConfusion h
              | some rest =>
                  rw [hr] at h
                  simp only
                  rw [minorFromTelescope_mono E hle nparams ss hr]
                  exact h
      | _ => simp only [minorFromTelescope] at h; exact Option.noConfusion h

/-- the derived minor (05 §12) at two analysis bounds, when both answer, is one term. -/
theorem derivedMinor_agree {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    {fuel₁ fuel₂ : Nat} {shapes : List FieldShape} {M₁ M₂ : Expr Nat}
    (h₁ : derivedMinor a i fuel₁ shapes = some M₁) (h₂ : derivedMinor a i fuel₂ shapes = some M₂) :
    M₁ = M₂ := by
  unfold derivedMinor at h₁ h₂
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact Option.some.inj ((minorFromTelescope_mono E hle _ shapes h₁).symm.trans h₂)
  · exact Option.some.inj (h₁.symm.trans (minorFromTelescope_mono E hle _ shapes h₂))

/-! ## (3) two admissions at one `(E, r)` -/

/-- the family: a family at another ref would be inside the other admission's constructor block. -/
theorem recursorAdmitted_familyRef_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m') :
    a.family.ref = a'.family.ref := by
  have inside : ∀ {m₁ m₂ : CheckedMember} (b : RecursorEliminationAdmitted E r m₁)
      (b' : RecursorEliminationAdmitted E r m₂), b.family.ref < b'.family.ref → False := by
    intro m₁ m₂ b b' hlt
    have hr := b.recursorRef
    have hr' := b'.recursorRef
    have hi : b'.family.ref - b.family.ref - 1 < b.constructors.length := by omega
    have hpos := b.constructorsPresent ⟨_, hi⟩
    have hcls := (b.constructorViews ⟨_, hi⟩).hasClass
    have heq : b.family.ref + 1 + (b'.family.ref - b.family.ref - 1) = b'.family.ref := by omega
    rw [heq, b'.family.present] at hpos
    have hm := Option.some.inj hpos
    have hfcls := b'.family.hasClass
    rw [hm] at hfcls
    rw [hfcls] at hcls
    exact MemberClass.noConfusion hcls
  rcases Nat.lt_trichotomy a.family.ref a'.family.ref with h | h | h
  · exact absurd h (fun h => inside a a' h)
  · exact h
  · exact absurd h (fun h => inside a' a h)

theorem recursorAdmitted_ctorCount_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m') :
    a.constructors.length = a'.constructors.length := by
  have hr := a.recursorRef
  have hr' := a'.recursorRef
  have hf := recursorAdmitted_familyRef_eq a a'
  omega

theorem recursorAdmitted_familyMember_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m') :
    a.family.member = a'.family.member := by
  have h := a.family.present
  rw [recursorAdmitted_familyRef_eq a a', a'.family.present] at h
  exact (Option.some.inj h).symm

/-- the family's parameters, indices and sort, given the parameter count. -/
theorem recursorAdmitted_familyTel_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (hnp : a.family.parameters.length = a'.family.parameters.length) :
    a.family.parameters = a'.family.parameters ∧ a.family.indices = a'.family.indices ∧
      a.family.resultLevel = a'.family.resultLevel := by
  have h := a.family.storedType
  rw [recursorAdmitted_familyMember_eq a a', a'.family.storedType] at h
  obtain ⟨hds, hb⟩ := policyPi_inj_notPi _ _ (sort_notPi _) (sort_notPi _) h
  obtain ⟨hps, his⟩ := List.append_inj hds.symm hnp
  injection hb with hl
  exact ⟨hps, his, hl.symm⟩

theorem recursorAdmitted_ctor_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (j : Nat) (hj : j < a.constructors.length) (hj' : j < a'.constructors.length) :
    a.constructors[j] = a'.constructors[j] := by
  have h := a.constructorsPresent ⟨j, hj⟩
  rw [recursorAdmitted_familyRef_eq a a', a'.constructorsPresent ⟨j, hj'⟩] at h
  exact (Option.some.inj h).symm

/-- constructor `j`'s fields, and its telescope after the parameters, agree. -/
theorem recursorAdmitted_ctorTel_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (hnp : a.family.parameters.length = a'.family.parameters.length)
    (j : Nat) (hj : j < a.constructors.length) (hj' : j < a'.constructors.length) :
    (a.constructorViews ⟨j, hj⟩).fields = (a'.constructorViews ⟨j, hj'⟩).fields ∧
      ctorFieldTelescope (a.constructorViews ⟨j, hj⟩) = ctorFieldTelescope (a'.constructorViews ⟨j, hj'⟩) := by
  have hmt : (a.constructors[j]'hj).mtype = (a'.constructors[j]'hj').mtype := by
    rw [recursorAdmitted_ctor_eq a a' j hj hj']
  have hst := ((a.constructorViews ⟨j, hj⟩).storedType.symm.trans hmt).trans
    (a'.constructorViews ⟨j, hj'⟩).storedType
  have hc := (a.constructorViews ⟨j, hj⟩).parameterCount
  have hc' := (a'.constructorViews ⟨j, hj'⟩).parameterCount
  obtain ⟨hds, _⟩ := policyPi_inj_notPi _ _ (foldApps_notPi _ (fun _ _ h => Expr.noConfusion h))
    (foldApps_notPi _ (fun _ _ h => Expr.noConfusion h)) hst
  obtain ⟨hps, hfs⟩ := List.append_inj hds (by rw [hc, hc', hnp])
  refine ⟨hfs, ?_⟩
  rw [policyPi_append, policyPi_append] at hst
  exact (policyPi_inj_length _ _ (by rw [hc, hc', hnp]) hst).2

/-- the derived minor reads only the family's ref, arity and parameter count, and the constructor's
    telescope after its parameters: two admissions at one `(E, r)` derive the same minor. -/
theorem recursorAdmitted_derivedMinor_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (hnp : a.family.parameters.length = a'.family.parameters.length)
    (j : Nat) (hj : j < a.constructors.length) (hj' : j < a'.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) :
    derivedMinor a ⟨j, hj⟩ fuel shapes = derivedMinor a' ⟨j, hj'⟩ fuel shapes := by
  simp only [derivedMinor, (recursorAdmitted_ctorTel_eq a a' hnp j hj hj').2,
    recursorAdmitted_familyRef_eq a a', hnp, policyFamilyLevels, recursorAdmitted_familyMember_eq a a']

/-- the minors: each is the derived one, which does not depend on the admission or the bound. -/
theorem recursorAdmitted_minorTypes_eq {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (h12 : MinorPremisesMatch a) (h12' : MinorPremisesMatch a')
    (hnp : a.family.parameters.length = a'.family.parameters.length) :
    a.minorTypes = a'.minorTypes := by
  have hk := recursorAdmitted_ctorCount_eq a a'
  obtain ⟨_, his, _⟩ := recursorAdmitted_familyTel_eq a a' hnp
  apply List.ext_getElem?
  intro j
  by_cases hj : j < a.constructors.length
  · have hj' : j < a'.constructors.length := hk ▸ hj
    obtain ⟨shapes, fuel, hsh, hd⟩ := h12 ⟨j, hj⟩
    obtain ⟨shapes', fuel', hsh', hd'⟩ := h12' ⟨j, hj'⟩
    rw [← (recursorAdmitted_ctorTel_eq a a' hnp j hj hj').1, ← recursorAdmitted_familyRef_eq a a',
      ← recursorAdmitted_familyMember_eq a a', ← hnp, ← his] at hsh'
    have hs := fieldShapesFuel_agree E hsh hsh'
    rw [← hs, ← recursorAdmitted_derivedMinor_eq a a' hnp j hj hj'] at hd'
    have hjm : j < a.minorTypes.length := by rw [a.minorCount]; exact hj
    have hjm' : j < a'.minorTypes.length := by rw [a'.minorCount]; exact hj'
    rw [List.getElem?_eq_getElem hjm] at hd
    rw [List.getElem?_eq_getElem hjm'] at hd'
    rw [List.getElem?_eq_getElem hjm, List.getElem?_eq_getElem hjm',
      derivedMinor_agree a ⟨j, hj⟩ hd hd']
  · have h1 : a.minorTypes.length ≤ j := by rw [a.minorCount]; omega
    have h2 : a'.minorTypes.length ≤ j := by rw [a'.minorCount]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-- 05 §13's signature reads the family only through its ref, arity, parameters and indices. -/
theorem policyRecursorType_congr {E E' : ResolvedEnv} (v : PolicyFamilyView E) (v' : PolicyFamilyView E')
    (href : v.ref = v'.ref) (harity : v.member.arity = v'.member.arity)
    (hps : v.parameters = v'.parameters) (his : v.indices = v'.indices)
    (ms : List (Expr Nat)) (p : EliminationPolicy) :
    policyRecursorType v ms p = policyRecursorType v' ms p := by
  simp only [policyRecursorType, policyMotiveType, policyFamilyLevels, href, harity, hps, his]

/-- **IA-021, unique (05 §13).** Two recursor admissions at the same `(E, r)`, with the same
    parameter count (the candidate's datum, 05 §2) and the same elimination policy, derive the same
    recursor: equal stored types and equal arities. -/
theorem IA021T_recursor_unique {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (h12 : MinorPremisesMatch a) (h12' : MinorPremisesMatch a')
    (hnp : a.family.parameters.length = a'.family.parameters.length)
    (hpol : a.policy = a'.policy) :
    m.mtype = m'.mtype ∧ m.arity = m'.arity := by
  obtain ⟨hps, his, _⟩ := recursorAdmitted_familyTel_eq a a' hnp
  have hmem := recursorAdmitted_familyMember_eq a a'
  refine ⟨?_, ?_⟩
  · rw [a.recursorType, a'.recursorType, recursorAdmitted_minorTypes_eq a a' h12 h12' hnp, hpol]
    exact policyRecursorType_congr _ _ (recursorAdmitted_familyRef_eq a a') (by rw [hmem]) hps his _ _
  · rw [a.recursorArity, a'.recursorArity, hpol, hmem]

/-- **IA-021, the policy (05 §10 inside §13).** Two recursor admissions at one `(E, r)` with the same
    parameter count select the same policy, unless the family is a singleton `Prop` and the two
    admissions read its all-fields-safe test differently (W3). -/
theorem IA021T_policy_unique {E : ResolvedEnv} {r : Nat} {m m' : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (a' : RecursorEliminationAdmitted E r m')
    (hnp : a.family.parameters.length = a'.family.parameters.length) :
    a.policy = a'.policy ∨
      (UniformProp a.family.resultLevel ∧ a.constructors.length = 1 ∧
        ¬ ((∀ i, (a.constructorViews i).AllFieldsSafe) ↔ (∀ i, (a'.constructorViews i).AllFieldsSafe))) := by
  obtain ⟨_, _, hl⟩ := recursorAdmitted_familyTel_eq a a' hnp
  have hk := recursorAdmitted_ctorCount_eq a a'
  have hsel := a.selected
  have hsel' := a'.selected
  rw [← hl] at hsel'
  have disj : ¬ (UniformProp a.family.resultLevel ∧ UniformType a.family.resultLevel) :=
    fun ⟨hp, ht⟩ => by have h1 := hp (fun _ => 0); have h2 := ht (fun _ => 0); omega
  generalize a.policy = p at hsel ⊢
  generalize a'.policy = p' at hsel' ⊢
  cases p <;> cases p'
  · exact .inl rfl
  · obtain ⟨hp, hk1⟩ := (EliminationSelection.propOnly_iff _ _ _).mp hsel'
    rcases (EliminationSelection.anySort_iff _ _ _).mp hsel with ht | ⟨_, hk0 | ⟨hk1', hs⟩⟩
    · exact absurd ⟨hp, ht⟩ disj
    · exfalso; rcases hk1 with h | ⟨h, _⟩ <;> omega
    · refine .inr ⟨hp, hk1', fun hiff => ?_⟩
      rcases hk1 with h | ⟨_, hns⟩
      · omega
      · exact hns (hiff.mp hs)
  · obtain ⟨hp, hk1⟩ := (EliminationSelection.propOnly_iff _ _ _).mp hsel
    rcases (EliminationSelection.anySort_iff _ _ _).mp hsel' with ht | ⟨_, hk0 | ⟨hk1', hs'⟩⟩
    · exact absurd ⟨hp, ht⟩ disj
    · exfalso; rcases hk1 with h | ⟨h, _⟩ <;> omega
    · refine .inr ⟨hp, by omega, fun hiff => ?_⟩
      rcases hk1 with h | ⟨_, hns⟩
      · omega
      · exact hns (hiff.mpr hs')
  · exact .inl rfl

end Rcic.Declarative

#print axioms Rcic.Declarative.policyPi_inj_length
#print axioms Rcic.Declarative.policyPi_inj_notPi
#print axioms Rcic.Declarative.derivedMinor_agree
#print axioms Rcic.Declarative.recursorAdmitted_familyRef_eq
#print axioms Rcic.Declarative.recursorAdmitted_minorTypes_eq
#print axioms Rcic.Declarative.IA021T_recursor_unique
#print axioms Rcic.Declarative.IA021T_policy_unique
