import rcic.RcicF3RecMem

/-!
# F3 S5a-9: ι

A `DerivedIota` witness at a recursor admitted by `a` is aligned with `a`
(`iota_align`: its parameter, minor and index counts and its family are
`a`'s), and for a constructor with only family-free fields its right-hand
side is the minor applied to the fields (`rhsArgs_plain`).
`recEnd_type_eq`: for a `Type` family the recursor's end value at a major
premise `dataVal j xs` is the `j`-th minor applied to `xs`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

theorem piCount_policyPi : (D : List (Expr Nat)) → (b : Expr Nat) →
    piCount (policyPi D b) = D.length + piCount b
  | [], b => by simp [policyPi]
  | A :: D, b => by
      show piCount (policyPi D b) + 1 = _
      rw [piCount_policyPi D b]; simp; omega

theorem piCount_foldApps (f : Expr Nat) (hf : ∀ A B, f ≠ .pi A B) :
    (as : List (Expr Nat)) → piCount (foldApps f as) = 0 := by
  intro as
  induction as generalizing f with
  | nil =>
      cases f with
      | pi A B => exact absurd rfl (hf A B)
      | _ => rfl
  | cons a as ih => exact ih (.app f a) (fun _ _ h => Expr.noConfusion h)

theorem peelPis_policyPi : (D : List (Expr Nat)) → (b : Expr Nat) →
    peelPis D.length (policyPi D b) = some (D, b)
  | [], b => rfl
  | A :: D, b => by
      show (match peelPis D.length (policyPi D b) with
        | some (ds, r) => some (A :: ds, r)
        | none => none) = _
      rw [peelPis_policyPi D b]

theorem foldApps_bvar_inj {x y : Nat} {as bs : List (Expr Nat)}
    (h : foldApps (.bvar x) as = foldApps (.bvar y) bs) : x = y ∧ as = bs := by
  have h1 := congrArg appsSpine h
  rw [appsSpine_foldApps, appsSpine_foldApps] at h1
  simp [appsSpine] at h1
  exact h1

/-- A `DerivedIota` witness at a recursor admitted by `a` is aligned with `a`. -/
theorem iota_align {E E0 : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E0 r m) (w : IotaWitness E) (hrec : w.recRef = r)
    (hm : w.recMember = m) :
    w.nparams = a.family.parameters.length ∧ w.nMinors = a.constructors.length ∧
      w.nindices = a.family.indices.length ∧ w.familyRef = a.family.ref := by
  have hty := a.recursorType
  rw [policyRecursorType_eq] at hty
  have hk : a.minorTypes.length = a.constructors.length := a.minorCount
  have hpc := w.hnmin
  rw [hm, hty, piCount_policyPi, piCount_foldApps _ (fun _ _ h => Expr.noConfusion h)] at hpc
  simp only [List.length_append, List.length_cons, liftFields_length', List.length_singleton,
    List.length_nil] at hpc
  have hpr := w.hpeelRec
  rw [hm, hty] at hpr
  have hlen : w.nparams + 1 + w.nMinors + w.nindices + 1 =
      (a.family.parameters ++ policyMotiveType a.family a.policy ::
        (a.minorTypes ++ (liftFields (a.minorTypes.length + 1) a.family.indices 0 ++
          [foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals a.family.parameters.length (a.minorTypes.length + 1 + a.family.indices.length) ++
              policyLocals a.family.indices.length)]))).length := by
    simp only [List.length_append, List.length_cons, liftFields_length', List.length_singleton,
      List.length_nil] at hpc ⊢
    omega
  rw [hlen, peelPis_policyPi] at hpr
  have hbody : w.recBody = foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1))
      ((List.range a.family.indices.length).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0]) := by
    have := (Option.some.inj hpr)
    exact (congrArg Prod.snd this).symm
  rw [w.hrecBody] at hbody
  obtain ⟨h1, h2⟩ := foldApps_bvar_inj hbody
  have hq : w.nindices = a.family.indices.length := by
    have := congrArg List.length h2
    simpa using this
  have hmin : w.nMinors = a.constructors.length := by omega
  have hnp : w.nparams = a.family.parameters.length := by omega
  refine ⟨hnp, hmin, hq, ?_⟩
  have h3 := w.hrecIdx
  rw [hrec, a.recursorRef, hmin] at h3
  omega

/-- A list of family-free fields is analyzed as plain. -/
theorem analyzeFields_plain (f : Nat) : (fs : List (Expr Nat)) → (∀ T, T ∈ fs → occursConst f T = false) →
    analyzeFields f fs = some (fs.map fun _ => RecKind.plain)
  | [], _ => rfl
  | T :: fs, h => by
      have hT := h T (List.mem_cons_self _ _)
      have ih := analyzeFields_plain f fs (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
      simp only [analyzeFields, analyzeField, hT, ih]
      rfl

/-- With only plain kinds, the right-hand side's arguments are the fields. -/
theorem rhsArgs_plain (rec : Expr Nat) (pre : List (Expr Nat)) (np nM : Nat) :
    (fs : List (Expr Nat)) → (ks : List RecKind) → (∀ k, k ∈ ks → k = .plain) → (Tl : Expr Nat) →
    rhsArgs rec pre np nM fs ks Tl = fs
  | [], _, _, _ => by cases ‹List RecKind› <;> rfl
  | f :: fs, [], _, Tl => by
      show f :: rhsArgs rec pre np nM fs [] Tl = f :: fs
      rw [rhsArgs_plain rec pre np nM fs [] (fun _ h => absurd h (List.not_mem_nil _)) Tl]
  | f :: fs, k :: ks, hk, Tl => by
      have hk0 : k = .plain := hk k (List.mem_cons_self _ _)
      subst hk0
      have hks : ∀ k, k ∈ ks → k = .plain := fun k h => hk k (List.mem_cons_of_mem _ h)
      cases Tl with
      | pi A B =>
          show f :: rhsArgs rec pre np nM fs ks (instantiate0 f B) = f :: fs
          rw [rhsArgs_plain rec pre np nM fs ks hks]
      | bvar _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]
      | sort _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]
      | const _ _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]
      | app _ _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]
      | lam _ _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]
      | letE _ _ _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]
      | lit _ => show f :: rhsArgs rec pre np nM fs ks _ = f :: fs; rw [rhsArgs_plain rec pre np nM fs ks hks]

theorem ctorFieldsOf_famDataOf {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) :
    ctorFieldsOf (famDataOf a) i.val = (a.constructorViews i).fields := by
  unfold ctorFieldsOf
  rw [List.getD_eq_getElem?_getD, famDataOf_ctor a i]
  rfl

/-- A substitution that commutes with applications and keeps constant heads. -/
def HomSub (I : Expr Nat → Expr Nat) : Prop :=
  (∀ f a, I (.app f a) = .app (I f) (I a)) ∧ ∀ r ls, ∃ ls', I (.const r ls) = .const r ls'

theorem homSub_instantiate (c : Nat) (a : Expr Nat) : HomSub (instantiate c a) :=
  ⟨fun _ _ => rfl, fun _ ls => ⟨ls, rfl⟩⟩

theorem homSub_instantiateLevels (ls : List Level) : HomSub (instantiateLevels ls) :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨_, rfl⟩⟩

theorem HomSub.comp {I J : Expr Nat → Expr Nat} (hI : HomSub I) (hJ : HomSub J) : HomSub (J ∘ I) := by
  refine ⟨fun f a => by simp only [Function.comp, hI.1, hJ.1], fun r ls => ?_⟩
  obtain ⟨ls1, h1⟩ := hI.2 r ls
  obtain ⟨ls2, h2⟩ := hJ.2 r ls1
  exact ⟨ls2, by simp only [Function.comp, h1, h2]⟩

theorem HomSub.map_foldApps {I : Expr Nat → Expr Nat} (hI : HomSub I) : (h : Expr Nat) → (as : List (Expr Nat)) →
    I (foldApps h as) = foldApps (I h) (as.map I)
  | _, [] => rfl
  | h, a :: as => by
      show I (foldApps (Expr.app h a) as) = foldApps (Expr.app (I h) (I a)) (as.map I)
      rw [HomSub.map_foldApps hI (Expr.app h a) as, hI.1]

/-- Instantiating every domain of a telescope. -/
def instFields (a : Expr Nat) : Nat → List (Expr Nat) → List (Expr Nat)
  | _, [] => []
  | c, D :: Ds => instantiate c a D :: instFields (Rcic.Declarative.lift 0 1 a) (c + 1) Ds

theorem instFields_length (a : Expr Nat) : (c : Nat) → (Ds : List (Expr Nat)) → (instFields a c Ds).length = Ds.length
  | _, [] => rfl
  | c, _ :: Ds => by simp [instFields, instFields_length _ (c + 1) Ds]

theorem instantiate_policyPi : (Ds : List (Expr Nat)) → (a b : Expr Nat) → (c : Nat) →
    ∃ b', instantiate c a (policyPi Ds b) = policyPi (instFields a c Ds) b'
  | [], _, b, c => ⟨instantiate c _ b, rfl⟩
  | D :: Ds, a, b, c => by
      obtain ⟨b', hb'⟩ := instantiate_policyPi Ds (Rcic.Declarative.lift 0 1 a) b (c + 1)
      exact ⟨b', by show Expr.pi _ (instantiate (c + 1) (Rcic.Declarative.lift 0 1 a) (policyPi Ds b)) = _; rw [hb']; rfl⟩

theorem analyzeField_plain_iff {f : Nat} {A : Expr Nat} (h : analyzeField f A = some .plain) :
    occursConst f A = false := by
  unfold analyzeField at h
  cases ho : occursConst f A with
  | false => rfl
  | true =>
      rw [ho] at h
      simp only [Bool.not_true] at h
      cases hf : isFamilyApp f A <;> rw [hf] at h <;> simp at h

theorem analyzeField_rec {f : Nat} {A : Expr Nat} (h : analyzeField f A = some .directRec) :
    occursConst f A = true := by
  unfold analyzeField at h
  cases ho : occursConst f A with
  | true => rfl
  | false => rw [ho] at h; simp at h

theorem analyzeFields_get {f : Nat} : {Fs : List (Expr Nat)} → {ks : List RecKind} →
    analyzeFields f Fs = some ks → (k : Nat) → (kk : RecKind) → ks[k]? = some kk →
    ∃ F, Fs[k]? = some F ∧ analyzeField f F = some kk
  | [], ks, h, k, kk, hk => by
      have : ks = [] := by simpa [analyzeFields] using h.symm
      subst this; simp at hk
  | F :: Fs, ks, h, k, kk, hk => by
      cases hF : analyzeField f F with
      | none => simp [analyzeFields, hF] at h
      | some kF =>
        cases hFs : analyzeFields f Fs with
        | none => simp [analyzeFields, hF, hFs] at h
        | some ks' =>
          have e : ks = kF :: ks' := by simp [analyzeFields, hF, hFs] at h; exact h.symm
          subst e
          cases k with
          | zero =>
              rw [List.getElem?_cons_zero, Option.some.injEq] at hk
              subst hk
              exact ⟨F, List.getElem?_cons_zero, hF⟩
          | succ k =>
              rw [List.getElem?_cons_succ] at hk
              obtain ⟨F', h1, h2⟩ := analyzeFields_get hFs k kk hk
              exact ⟨F', by rw [List.getElem?_cons_succ]; exact h1, h2⟩

/-- For a `Type` family, the recursor's end value at a constructor's data value
is the matching minor applied to its fields. -/
theorem recEnd_type_eq (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (ps : List PSet.{T}) (mo : PSet.{T})
    (ms is : List PSet.{T}) (z : PSet.{T}) (ρ : Nat → PSet.{T})
    (hms : ms.length = fd.ctors.length) (his : is.length = fd.indices.length)
    (h0 : evalTotal σ fd.resLevel ≠ 0) (j : Nat) (hj : j < fd.ctors.length) (xs : List PSet.{T})
    (hxs : xs.length = nfOf fd j) (hz : Equiv z (dataVal j xs))
    (hfree : ∀ A, A ∈ ctorFieldsOf fd j → occursConst fd.fref A = false) :
    Equiv (recEnd M σ fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) (fapps (ms.getD j pempty) xs) := by
  have hz' : push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ 0 = z := by rw [push_cons_eq]; rfl
  unfold recEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue h => exact absurd h h0
  | isFalse _ =>
      show Equiv (recCore M fd (minorsOf fd.indices.length fd.ctors.length
        (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ 0)) _
      rw [minorsOf_env ps mo ms is z ρ hms his, hz']
      refine (recCore_data M fd ms hz hj hxs).trans ?_
      rw [ihArgs_free _ _ _ _ hfree (by rw [hxs, nfOf_eq])]
      exact Equiv.rfl

/-- The Prop-family recursor end value under elimination into Prop is `∅`. -/
theorem recEnd_propOnly (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{T})
    (h0 : evalTotal σ fd.resLevel = 0) (hp : fd.policy = .propOnly) : recEnd M σ fd ρ = pempty := by
  unfold recEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isFalse h => exact absurd h0 h
  | isTrue _ => show propRecEnd fd _ _ = pempty; unfold propRecEnd; rw [hp]

/-- The single-constructor `Prop`-family recursor end value under large
elimination: the minor applied to the fields reconstructed from the indices. -/
theorem recEnd_prop_single (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (ps : List PSet.{T}) (mo : PSet.{T})
    (ms is : List PSet.{T}) (z : PSet.{T}) (ρ : Nat → PSet.{T})
    (hms : ms.length = fd.ctors.length) (his : is.length = fd.indices.length)
    (h0 : evalTotal σ fd.resLevel = 0) (hp : fd.policy = .anySort) (c : List (Expr Nat) × List (Expr Nat))
    (hc : fd.ctors = [c]) :
    Equiv (recEnd M σ fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) (fapps (ms.getD 0 pempty) (recon c is)) := by
  have hmv : push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ (fd.indices.length + fd.ctors.length) =
      ms.getD 0 pempty := by
    have := recEnv_minor ps mo ms is z ρ 0 (by rw [hms, hc]; exact Nat.zero_lt_one)
    rw [Nat.sub_zero] at this
    rw [← his, ← hms, this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < ms.length by rw [hms, hc]; exact Nat.zero_lt_one)]
  have hiv : lastVals fd.indices.length (shiftρ 1 (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) = is := by
    rw [← his]; exact recEnv_indices ps mo ms is z ρ
  unfold recEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isFalse h => exact absurd h0 h
  | isTrue _ =>
      show Equiv (propRecEnd fd _ _) _
      rw [hmv, hiv]
      unfold propRecEnd
      rw [hp, hc]
      exact Equiv.rfl

/-- The Prop-family recursor end value with one field-less constructor. -/
theorem recEnd_prop_nofields (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) (ps : List PSet.{T}) (mo : PSet.{T})
    (ms is : List PSet.{T}) (z : PSet.{T}) (ρ : Nat → PSet.{T})
    (hms : ms.length = fd.ctors.length) (his : is.length = fd.indices.length)
    (h0 : evalTotal σ fd.resLevel = 0) (hp : fd.policy = .anySort) (ri : List (Expr Nat))
    (hc : fd.ctors = [([], ri)]) :
    Equiv (recEnd M σ fd (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ)) (ms.getD 0 pempty) := by
  have hmv : push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ (fd.indices.length + fd.ctors.length) =
      ms.getD 0 pempty := by
    have := recEnv_minor ps mo ms is z ρ 0 (by rw [hms, hc]; exact Nat.zero_lt_one)
    rw [Nat.sub_zero] at this
    rw [← his, ← hms, this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < ms.length by rw [hms, hc]; exact Nat.zero_lt_one)]
  unfold recEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isFalse h => exact absurd h0 h
  | isTrue _ =>
      show Equiv (propRecEnd fd _ _) _
      rw [hmv]
      unfold propRecEnd
      rw [hp, hc]
      exact Equiv.rfl

theorem piLam_foldApps (M : Interp.{T}) (σ : Nat → Nat) (g : (Nat → PSet.{T}) → PSet.{T})
    (ρ : Nat → PSet.{T}) (f : Expr Nat) (hf : ∀ A B, f ≠ .pi A B) (as : List (Expr Nat)) :
    piLam M σ g ρ (foldApps f as) = g ρ := by
  induction as generalizing f with
  | nil =>
      cases f with
      | pi A B => exact absurd rfl (hf A B)
      | _ => rfl
  | cons a as ih => exact ih (.app f a) (fun _ _ h => Expr.noConfusion h)

theorem list_split4 {α : Type _} (l : List α) (a b c : Nat) (h : l.length = a + 1 + b + c) (dflt : α) :
    l = l.take a ++ l.getD a dflt :: ((l.drop (a + 1)).take b ++ l.drop (a + 1 + b)) := by
  have h1 : l = l.take a ++ l.drop a := (List.take_append_drop a l).symm
  have h2 : l.drop a = l.getD a dflt :: l.drop (a + 1) := by
    have hl : a < l.length := by omega
    rw [List.drop_eq_getElem_cons hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have h3 : l.drop (a + 1) = (l.drop (a + 1)).take b ++ l.drop (a + 1 + b) := by
    have e : l.drop (a + 1 + b) = (l.drop (a + 1)).drop b := by rw [List.drop_drop]
    rw [e]
    exact (List.take_append_drop b _).symm
  conv => lhs; rw [h1, h2, h3]

theorem fapps_den_append_singleton (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (f : Expr Nat)
    (pre : List (Expr Nat)) (x : Expr Nat) :
    den M σ ρ (foldApps f (pre ++ [x])) = fapps (den M σ ρ f) (pre.map (den M σ ρ) ++ [den M σ ρ x]) := by
  rw [den_foldApps, List.map_append]
  rfl

theorem rhs_eq_ed_pempty {M : Interp.{T}} {X lhs rhs : PSet.{T}} (ml : lhs ∈ Ed M X) (mr : rhs ∈ Ed M X)
    (h0 : Equiv lhs pempty) : Equiv lhs rhs := by
  have h0m : pempty ∈ Ed M X := mem_congr_left h0 ml
  rcases dich_ed M X with hall | hn
  · exact h0.trans (hall rhs mr).symm
  · exact absurd h0m hn

/-- The recursor's major premise domain. -/
def recMajorOf {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    Expr Nat :=
  foldApps (.const a.family.ref (policyFamilyLevels a.family))
    (policyParameterLocals a.family.parameters.length (a.minorTypes.length + 1 + a.family.indices.length) ++
      policyLocals a.family.indices.length)

/-- The recursor's domains before the major premise. -/
def recPreDomsOf {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    List (Expr Nat) :=
  a.family.parameters ++ policyMotiveType a.family a.policy ::
    (a.minorTypes ++ liftFields (a.minorTypes.length + 1) a.family.indices 0)

/-- The recursor's result. -/
def recResultOf {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    Expr Nat :=
  foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1))
    ((List.range a.family.indices.length).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])

theorem recType_eq {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    m.mtype = policyPi (recPreDomsOf a ++ [recMajorOf a]) (recResultOf a) := by
  rw [a.recursorType, policyRecursorType_eq]
  unfold recPreDomsOf recMajorOf recResultOf
  simp only [List.append_assoc, List.cons_append]

theorem recPreDomsOf_length {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) :
    (recPreDomsOf a).length = a.family.parameters.length + 1 + a.constructors.length + a.family.indices.length := by
  unfold recPreDomsOf
  simp [liftFields_length', a.minorCount]
  omega

/-- The major premise domain's denotation. -/
theorem den_recMajor (M : Interp.{T}) (σ : Nat → Nat) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (ps : List PSet.{T}) (mo : PSet.{T}) (ms is : List PSet.{T})
    (R : Nat → PSet.{T}) (hpsl : ps.length = a.family.parameters.length)
    (hmsl : ms.length = a.minorTypes.length) (hisl : is.length = a.family.indices.length) :
    den M σ (push (ps ++ mo :: (ms ++ is)) R) (recMajorOf a) =
      fapps (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal σ))) (ps ++ is) := by
  unfold recMajorOf
  have e2 : a.minorTypes.length + 1 + a.family.indices.length = (mo :: (ms ++ is)).length := by
    simp [hmsl, hisl]; omega
  have hA : (policyParameterLocals a.family.parameters.length
      (a.minorTypes.length + 1 + a.family.indices.length)).map (den M σ (push (ps ++ mo :: (ms ++ is)) R)) = ps := by
    rw [e2, ← hpsl]; exact den_paramLocals M σ ps _ R
  have hB : (policyLocals a.family.indices.length).map (den M σ (push (ps ++ mo :: (ms ++ is)) R)) = is := by
    have e1 : push (ps ++ mo :: (ms ++ is)) R = push is (push ms (vcons mo (push ps R))) := by
      rw [push_append]
      show push (ms ++ is) (vcons mo (push ps R)) = _
      rw [push_append]
    rw [e1, ← hisl]; exact den_policyLocals M σ is _
  rw [den_foldApps, List.map_append, hA, hB]
  rfl

end PSet

end Rcic.F3
