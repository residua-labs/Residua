import rcic.RcicIotaShapeStable
import rcic.RcicIndGroupJudgment

namespace Rcic.Declarative

/-- Admission's canonical ι schema, computed in an arbitrary extension environment. -/
def iotaSchemaAtIn {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (E' : ResolvedEnv) (a : RecursorEliminationAdmitted E r m)
    (i : Fin a.constructors.length) (fuel : Nat) (shapes : List FieldShape) :
    Option (Expr Nat) :=
  let c := a.constructorViews i
  let nf := c.fields.length
  let np := a.family.parameters.length
  let q := a.family.indices.length
  let k := a.constructors.length
  iotaOpenRhs E' fuel
      (.const r (policyRecursorLevels a.family.member.arity a.policy))
      (.bvar (nf + q + (k - 1 - i.val)))
    (preMajorBvars np k q nf) np k shapes (fieldBvars nf)
    (lift 0 (nf + 1 + k + q) (ctorFieldTelescope c))

theorem iotaSchemaAtIn_self {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) :
    iotaSchemaAtIn E a i fuel shapes = iotaSchemaAt a i fuel shapes := rfl

private def descendingBvars : Nat → List (Expr Nat)
  | 0 => []
  | n + 1 => .bvar n :: descendingBvars n

private def majorArgsN : Nat → Nat → Nat → List (Expr Nat)
  | 0, _, q => descendingBvars q
  | np + 1, k, q => .bvar (np + q + k + 1) :: majorArgsN np k q

private theorem descendingBvars_eq (n : Nat) :
    descendingBvars n = (List.range n).reverse.map Expr.bvar := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descendingBvars, List.range_succ, ih]

private theorem majorArgsN_eq (np k q : Nat) :
    majorArgsN np k q =
      (List.range np).reverse.map (fun i => Expr.bvar (i + q + k + 1)) ++
        (List.range q).reverse.map Expr.bvar := by
  induction np with
  | zero => simp [majorArgsN, descendingBvars_eq]
  | succ np ih => simp [majorArgsN, List.range_succ, ih, Nat.add_assoc]

private theorem majorArgsN_length (np k q : Nat) :
    (majorArgsN np k q).length = np + q := by
  rw [majorArgsN_eq]
  simp

private theorem majorArgsN_inj (k : Nat) :
    ∀ {np q np' q' : Nat}, majorArgsN np k q = majorArgsN np' k q' →
      np = np' ∧ q = q' := by
  intro np
  induction np with
  | zero =>
      intro q np' q' h
      cases np' with
      | zero =>
          have hl := congrArg List.length h
          simp only [majorArgsN_length, Nat.zero_add] at hl
          exact ⟨rfl, hl⟩
      | succ np' =>
          cases q with
          | zero => simp [majorArgsN, descendingBvars] at h
          | succ q =>
              have hl := congrArg List.length h
              simp only [majorArgsN_length, Nat.zero_add, Nat.succ_add] at hl
              simp only [majorArgsN, descendingBvars] at h
              have hh : q = np' + q' + k + 1 := by
                injection h with hb _
                exact Expr.bvar.inj hb
              omega
  | succ np ih =>
      intro q np' q' h
      cases np' with
      | zero =>
          cases q' with
          | zero => simp [majorArgsN, descendingBvars] at h
          | succ q' =>
              have hl := congrArg List.length h
              simp only [majorArgsN_length, Nat.succ_add, Nat.zero_add] at hl
              simp only [majorArgsN, descendingBvars] at h
              have hh : np + q + k + 1 = q' := by
                injection h with hb _
                exact Expr.bvar.inj hb
              omega
      | succ np' =>
          simp only [majorArgsN] at h
          injection h with _ ht
          have hn := ih ht
          exact ⟨congrArg Nat.succ hn.1, hn.2⟩

private theorem majorTyExpr_data_eq
    {familyRef familyRef' : Nat} {ls ls' : List Level}
    {np k q np' k' q' : Nat} (hk : k = k')
    (h : majorTyExpr familyRef ls np k q =
      majorTyExpr familyRef' ls' np' k' q') :
    familyRef = familyRef' ∧ ls = ls' ∧ np = np' ∧ q = q' := by
  subst k'
  have hs := congrArg appsSpine h
  simp only [majorTyExpr, appsSpine_foldApps_const] at hs
  have hh := congrArg Prod.fst hs
  have ha := congrArg Prod.snd hs
  injection hh with href hls
  rw [← majorArgsN_eq, ← majorArgsN_eq] at ha
  have hn := majorArgsN_inj k ha
  exact ⟨href, hls, hn.1, hn.2⟩

theorem policyPi_eq_foldr (xs : List (Expr Nat)) (body : Expr Nat) :
    policyPi xs body = xs.foldr Expr.pi body := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [policyPi, List.foldr_cons, ih]

private theorem policyPi_append' (xs ys : List (Expr Nat)) (body : Expr Nat) :
    policyPi (xs ++ ys) body = policyPi xs (policyPi ys body) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Expr.pi x) ih

theorem peelPis_policyPi (xs : List (Expr Nat)) (body : Expr Nat) :
    peelPis xs.length (policyPi xs body) = some (xs, body) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons, policyPi, peelPis, ih]

theorem piCount_policyPi (xs : List (Expr Nat)) (body : Expr Nat) :
    piCount (policyPi xs body) = xs.length + piCount body := by
  induction xs with
  | nil => simp [policyPi]
  | cons x xs ih => simp only [policyPi, piCount, List.length_cons, ih]; omega

theorem piCount_foldApps_of_zero (f : Expr Nat) (xs : List (Expr Nat))
    (hf : piCount f = 0) : piCount (foldApps f xs) = 0 := by
  induction xs generalizing f with
  | nil => exact hf
  | cons x xs ih => exact ih (.app f x) rfl

private def policyRecursorDoms {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : List (Expr Nat) :=
  let k := a.minorTypes.length
  let q := a.family.indices.length
  let major := foldApps (.const a.family.ref (policyFamilyLevels a.family))
    (policyParameterLocals a.family.parameters.length (k + 1 + q) ++ policyLocals q)
  a.family.parameters ++ [policyMotiveType a.family a.policy] ++ a.minorTypes ++
    a.family.indices.mapIdx (fun j T => lift j (k + 1) T) ++ [major]

private def policyRecursorBody {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Expr Nat :=
  let k := a.minorTypes.length
  let q := a.family.indices.length
  foldApps (.bvar (k + q + 1))
    ((List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])

private theorem policyRecursorType_eq_tel {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    policyRecursorType a.family a.minorTypes a.policy =
      policyPi (policyRecursorDoms a) (policyRecursorBody a) := by
  simp only [policyRecursorType, policyRecursorDoms, policyRecursorBody,
    policyPi_append', policyPi]

private theorem policyRecursorDoms_length {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    (policyRecursorDoms a).length = a.family.parameters.length + 1 +
      a.constructors.length + a.family.indices.length + 1 := by
  simp only [policyRecursorDoms, List.length_append, List.length_cons, List.length_nil,
    List.length_mapIdx, a.minorCount]

private theorem policyRecursorDoms_last {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    (policyRecursorDoms a)[(policyRecursorDoms a).length - 1]? = some
      (majorTyExpr a.family.ref (policyFamilyLevels a.family)
        a.family.parameters.length a.constructors.length a.family.indices.length) := by
  let dsPrefix := a.family.parameters ++ [policyMotiveType a.family a.policy] ++
    a.minorTypes ++
      a.family.indices.mapIdx (fun j T => lift j (a.constructors.length + 1) T)
  have hd : policyRecursorDoms a = dsPrefix ++
      [majorTyExpr a.family.ref (policyFamilyLevels a.family)
        a.family.parameters.length a.constructors.length a.family.indices.length] := by
    simp [policyRecursorDoms, dsPrefix, majorTyExpr, policyParameterLocals, policyLocals,
      a.minorCount]
    apply congrArg (fun args => foldApps
      (.const a.family.ref (policyFamilyLevels a.family)) args)
    rw [show (fun i : Nat => Expr.bvar i) = Expr.bvar from rfl]
    change _ ++ (List.map Expr.bvar (List.range a.family.indices.length)).reverse =
      _ ++ (List.map Expr.bvar (List.range a.family.indices.length)).reverse
    apply congrArg (fun xs => xs ++
      (List.map Expr.bvar (List.range a.family.indices.length)).reverse)
    apply congrArg List.reverse
    apply List.map_congr_left
    intro i hi
    congr 1
    omega
  rw [hd]
  simp

theorem extendEnv_extends_of_fresh {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hfresh : E.members r = none) :
    ∀ r' m', E.members r' = some m' → (extendEnv E r m).members r' = some m' := by
  intro r' m' h
  simp only [extendEnv]
  split
  · next heq =>
      subst r'
      rw [hfresh] at h
      cases h
  · exact h

private theorem IotaWitnessS.recData_eq {E : ResolvedEnv}
    (w₁ w₂ : IotaWitnessS E)
    (href : w₁.recRef = w₂.recRef) (hmember : w₁.recMember = w₂.recMember) :
    w₁.familyRef = w₂.familyRef ∧ w₁.famMember = w₂.famMember ∧
      w₁.nparams = w₂.nparams ∧ w₁.nindices = w₂.nindices ∧
      w₁.nMinors = w₂.nMinors := by
  have hcount :
      w₁.nparams + 1 + w₁.nMinors + w₁.nindices + 1 =
        w₂.nparams + 1 + w₂.nMinors + w₂.nindices + 1 := by
    rw [w₁.hnmin, w₂.hnmin, hmember]
  have hpos :
      w₁.nparams + 1 + w₁.nMinors + w₁.nindices =
        w₂.nparams + 1 + w₂.nMinors + w₂.nindices := by omega
  have hp₂ := w₂.hpeelRec
  rw [← hmember, ← hcount, w₁.hpeelRec] at hp₂
  have hpair := Option.some.inj hp₂
  have hdom := congrArg Prod.fst hpair
  change w₁.recDoms = w₂.recDoms at hdom
  have hm₁ : w₁.recDoms[w₁.nparams + 1 + w₁.nMinors + w₁.nindices]? = some
      (majorTyExpr w₁.familyRef ((List.range w₁.famMember.arity).map Level.param)
        w₁.nparams w₁.nMinors w₁.nindices) := by
    simpa only [majorTyExpr] using w₁.hmajorTy
  have hm₂ : w₂.recDoms[w₂.nparams + 1 + w₂.nMinors + w₂.nindices]? = some
      (majorTyExpr w₂.familyRef ((List.range w₂.famMember.arity).map Level.param)
        w₂.nparams w₂.nMinors w₂.nindices) := by
    simpa only [majorTyExpr] using w₂.hmajorTy
  rw [hpos, hdom, hm₂] at hm₁
  injection hm₁ with hmajor
  have hs := congrArg appsSpine hmajor
  simp only [majorTyExpr, appsSpine_foldApps_const] at hs
  have hhead := congrArg Prod.fst hs
  injection hhead with hfamily _
  have hk : w₁.nMinors = w₂.nMinors := by
    have hre : w₁.familyRef + 1 + w₁.nMinors =
        w₂.familyRef + 1 + w₂.nMinors := by
      rw [← w₁.hrecIdx, href, w₂.hrecIdx]
    omega
  have hdata := majorTyExpr_data_eq hk hmajor.symm
  have hfamMember : w₁.famMember = w₂.famMember := by
    have h₁ := w₁.hfam
    rw [hdata.1, w₂.hfam] at h₁
    exact Option.some.inj h₁.symm
  exact ⟨hdata.1, hfamMember, hdata.2.2.1, hdata.2.2.2, hk⟩

theorem IotaWitnessS.recData_admitted
    {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (hext : ∀ r' m', (extendEnv E r m).members r' = some m' →
      E'.members r' = some m')
    (w : IotaWitnessS E') (hr : w.recRef = r) (hm : w.recMember = m) :
    w.familyRef = a.family.ref ∧ w.famMember = a.family.member ∧
      w.nparams = a.family.parameters.length ∧
      w.nindices = a.family.indices.length ∧
      w.nMinors = a.constructors.length := by
  have hbodyZero : piCount (policyRecursorBody a) = 0 := by
    apply piCount_foldApps_of_zero
    rfl
  have hcount : w.nparams + 1 + w.nMinors + w.nindices + 1 =
      (policyRecursorDoms a).length := by
    calc
      w.nparams + 1 + w.nMinors + w.nindices + 1 = piCount w.recMember.mtype := w.hnmin
      _ = piCount m.mtype := by rw [hm]
      _ = piCount (policyRecursorType a.family a.minorTypes a.policy) := by rw [a.recursorType]
      _ = piCount (policyPi (policyRecursorDoms a) (policyRecursorBody a)) := by
        rw [policyRecursorType_eq_tel]
      _ = (policyRecursorDoms a).length := by
        rw [piCount_policyPi, hbodyZero, Nat.add_zero]
  have hpos : w.nparams + 1 + w.nMinors + w.nindices =
      (policyRecursorDoms a).length - 1 := by
    have hlen := policyRecursorDoms_length a
    omega
  have hp := w.hpeelRec
  rw [hm, a.recursorType, policyRecursorType_eq_tel, hcount,
    peelPis_policyPi] at hp
  have hpair := Option.some.inj hp
  have hdom := congrArg Prod.fst hpair
  change policyRecursorDoms a = w.recDoms at hdom
  have hmajorPolicy :
      (policyRecursorDoms a)[(policyRecursorDoms a).length - 1]? = some
        (majorTyExpr a.family.ref (policyFamilyLevels a.family)
          a.family.parameters.length a.constructors.length a.family.indices.length) := by
    let dsPrefix := a.family.parameters ++ [policyMotiveType a.family a.policy] ++
      a.minorTypes ++
        a.family.indices.mapIdx (fun j T => lift j (a.constructors.length + 1) T)
    have hd : policyRecursorDoms a = dsPrefix ++
        [majorTyExpr a.family.ref (policyFamilyLevels a.family)
          a.family.parameters.length a.constructors.length a.family.indices.length] := by
      simp [policyRecursorDoms, dsPrefix, majorTyExpr, policyParameterLocals, policyLocals,
        a.minorCount]
      apply congrArg (fun args => foldApps
        (.const a.family.ref (policyFamilyLevels a.family)) args)
      rw [show (fun i : Nat => Expr.bvar i) = Expr.bvar from rfl]
      change _ ++ (List.map Expr.bvar (List.range a.family.indices.length)).reverse =
        _ ++ (List.map Expr.bvar (List.range a.family.indices.length)).reverse
      apply congrArg (fun xs => xs ++
        (List.map Expr.bvar (List.range a.family.indices.length)).reverse)
      apply congrArg List.reverse
      apply List.map_congr_left
      intro i hi
      congr 1
      omega
    rw [hd]
    simp
  have hmajorW : w.recDoms[w.nparams + 1 + w.nMinors + w.nindices]? = some
      (majorTyExpr w.familyRef ((List.range w.famMember.arity).map Level.param)
        w.nparams w.nMinors w.nindices) := by
    simpa only [majorTyExpr] using w.hmajorTy
  rw [hpos, ← hdom, hmajorPolicy] at hmajorW
  injection hmajorW with hmajor
  have hs := congrArg appsSpine hmajor
  simp only [majorTyExpr, appsSpine_foldApps_const] at hs
  have hhead := congrArg Prod.fst hs
  injection hhead with hfamily _
  have hk : w.nMinors = a.constructors.length := by
    have hwref : r = w.familyRef + 1 + w.nMinors := hr.symm.trans w.hrecIdx
    have haref := a.recursorRef
    omega
  have hdata := majorTyExpr_data_eq hk hmajor.symm
  have hfamilyNe : a.family.ref ≠ r := by
    have haref := a.recursorRef
    omega
  have hfamPresent : E'.members a.family.ref = some a.family.member := by
    apply hext
    simp only [extendEnv]
    rw [if_neg hfamilyNe]
    exact a.family.present
  have hfm := w.hfam
  rw [hdata.1, hfamPresent] at hfm
  have hmember := Option.some.inj hfm.symm
  exact ⟨hdata.1, hmember, hdata.2.2.1, hdata.2.2.2, hk⟩

/-- R-NoFunRec-1 B2: the typed environment's recursor/index obligation. Its witness
 domain is the shape witnesses (`IotaWitnessS`), and its coverage comes from
 admission's own constructor list and descriptor. -/
structure RecursorGroupIdxAdmittedT {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a) : Type where
  /-- The descriptor's analysis is the same in every extension. -/
  stable : ∀ (i : Fin a.constructors.length) (E' : ResolvedEnv),
    (∀ r' m', E.members r' = some m' → E'.members r' = some m') →
      fieldShapesFuel E' (h14.fuelAt i) a.family.ref a.family.member.arity
          a.family.parameters.length a.family.indices.length
          a.family.parameters.length (a.constructorViews i).fields =
            some (h14.shapesAt i) ∧
        iotaSchemaAtIn E' a i (h14.fuelAt i) (h14.shapesAt i) =
          iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i)
  /-- Every constructor's rule instantiates in the canonical equation context,
  and that instance is the checked equation. -/
  covered : ∀ i : Fin a.constructors.length,
    Σ' (w : IotaWitnessS (extendEnv E r m)),
      w.recRef = r ∧ w.recMember = m ∧ w.ctorIdx = i.val ∧
      w.preMajor = preMajorBvars a.family.parameters.length a.constructors.length
        a.family.indices.length (a.constructorViews i).fields.length ∧
      w.fields = fieldBvars (a.constructorViews i).fields.length ∧
      w.shapes = h14.shapesAt i ∧
      iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) = some w.schema

private theorem iotaSchemaAt_exists {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (h14 : IotaDescriptorClause E a) (i : Fin a.constructors.length) :
    ∃ schema, iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) = some schema := by
  have ht := h14.typed i
  unfold IotaEquationTyped at ht
  cases heq : equationDoms a i with
  | none =>
      simp only [heq] at ht
      nomatch ht
  | some doms =>
      simp only [heq] at ht
      cases hs : iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) with
      | none =>
          simp only [hs] at ht
          nomatch ht
      | some schema => exact ⟨schema, rfl⟩

def descriptorSchema {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) : Expr Nat :=
  (iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i)).getD (.bvar 0)

theorem descriptorSchema_spec {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) :
    iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) =
      some (descriptorSchema a h14 i) := by
  rcases iotaSchemaAt_exists a h14 i with ⟨schema, hs⟩
  simp [descriptorSchema, hs]

def recIdxCtorB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) : Bool :=
  exprClosedAt 0 a.constructors[i.val].mtype &&
  iotaWitnessStableB E (h14.fuelAt i) (a.constructorViews i).fields
    (fieldBvars (a.constructorViews i).fields.length)
    (lift 0 ((a.constructorViews i).fields.length + 1 + a.constructors.length + a.family.indices.length)
      (ctorFieldTelescope (a.constructorViews i))) &&
  iotaWitnessStableB (extendEnv E r m) (h14.fuelAt i)
    (a.constructorViews i).fields
    (fieldBvars (a.constructorViews i).fields.length)
    (lift 0 ((a.constructorViews i).fields.length + 1 + a.constructors.length + a.family.indices.length)
      (ctorFieldTelescope (a.constructorViews i))) &&
  exprClosedAt (a.family.parameters.length + 1 + a.constructors.length +
    a.family.indices.length + (a.constructorViews i).fields.length)
    (descriptorSchema a h14 i)

/-- Decidable sufficient condition for descriptor stability and construction of every
canonical shape witness. -/
def recIdxAdmittedTB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a) : Bool :=
  (E.members r).isNone &&
  (match m.mclass with | .recursorM => true | _ => false) &&
  exprClosedAt 0 m.mtype &&
  (List.range a.constructors.length).all fun j =>
    if hj : j < a.constructors.length then recIdxCtorB a h14 ⟨j, hj⟩ else false

/-- Every shape witness for the admitted recursor reads the admitted constructor
index, field shapes, and canonical equation schema. -/
theorem RecursorGroupIdxAdmittedT.bound
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {h14 : IotaDescriptorClause E a}
    (adm : RecursorGroupIdxAdmittedT a h14) {E' : ResolvedEnv}
    (hext : ∀ r' m', (extendEnv E r m).members r' = some m' →
      E'.members r' = some m')
    (w : IotaWitnessS E') (hr : w.recRef = r) (hm : w.recMember = m) :
    ∃ i : Fin a.constructors.length, w.ctorIdx = i.val ∧
      w.shapes = h14.shapesAt i ∧
      iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) = some w.schema := by
  have hadm := w.recData_admitted a hext hr hm
  have hiLt : w.ctorIdx < a.constructors.length := by
    rw [← hadm.2.2.2.2]
    exact w.hidx
  let i : Fin a.constructors.length := ⟨w.ctorIdx, hiLt⟩
  rcases adm.covered i with
    ⟨cw, hcwr, hcwm, hcwi, hcwpre, hcwfields, hcwshapes, hcwschema⟩
  let cw' : IotaWitnessS E' := extWitnessS hext cw
  have hcwr' : cw'.recRef = r := by exact hcwr
  have hcwm' : cw'.recMember = m := by exact hcwm
  have hcwi' : cw'.ctorIdx = i.val := by exact hcwi
  have hrecRef : w.recRef = cw'.recRef := hr.trans hcwr'.symm
  have hrecMember : w.recMember = cw'.recMember := hm.trans hcwm'.symm
  have hdata := w.recData_eq cw' hrecRef hrecMember
  have hctorRef : w.ctorRef = cw'.ctorRef := by
    rw [w.hctorIdx, cw'.hctorIdx, hdata.1, hcwi']
  have hctorMember : w.ctorMember = cw'.ctorMember := by
    have hw := w.hctor
    rw [hctorRef, cw'.hctor] at hw
    exact Option.some.inj hw.symm
  have hfieldLen : w.fields.length = cw'.fields.length := by
    have hcount := congrArg (fun cm => piCount cm.mtype) hctorMember
    change piCount w.ctorMember.mtype = piCount cw'.ctorMember.mtype at hcount
    have hwpar := w.hnpar
    have hcwpar := cw'.hnpar
    omega
  have hp := cw'.hpeel
  rw [← hctorMember, ← hdata.2.2.1, ← hfieldLen, w.hpeel] at hp
  have hpair := Option.some.inj hp
  have hctorDoms := congrArg Prod.fst hpair
  have hctorResult := congrArg Prod.snd hpair
  change w.ctorDoms = cw'.ctorDoms at hctorDoms
  change w.ctorResult = cw'.ctorResult at hctorResult
  have hcshapes := cw'.hshapes
  rw [← hdata.1, ← hdata.2.2.1, ← hdata.2.2.2.1,
    ← hdata.2.1, ← hctorDoms] at hcshapes
  have hshapes : w.shapes = cw'.shapes :=
    fieldShapesFuel_agree E' w.hshapes hcshapes
  have hctorIdxVal : w.ctorIdx = cw'.ctorIdx := by
    rw [hcwi']
  have hcschema := cw'.hschema
  rw [← hrecRef, ← hrecMember, ← hfieldLen, ← hdata.2.2.2.1,
    ← hdata.2.2.2.2, ← hctorIdxVal, ← hdata.2.2.1, ← hshapes,
    ← hctorDoms, ← hctorResult] at hcschema
  have hschema : w.schema = cw'.schema :=
    iotaOpenRhs_agree E' w.hschema hcschema
  refine ⟨i, rfl, ?_, ?_⟩
  · exact hshapes.trans (by exact hcwshapes)
  · rw [hschema]
    exact hcwschema

/-- The decidable closure-and-canonical-witness check constructs the typed
recursor/index obligation. -/
def RecursorGroupIdxAdmittedT.ofCheck
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (hcheck : recIdxAdmittedTB a h14 = true) :
    RecursorGroupIdxAdmittedT a h14 := by
  simp only [recIdxAdmittedTB, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hfreshB := hcheck.1.1.1
  have hrecKB := hcheck.1.1.2
  have hrecK : m.mclass = MemberClass.recursorM := by
    cases hmc : m.mclass <;> simp [hmc] at hrecKB ⊢
  have hrecScope := hcheck.1.2
  have hrecClosed : lift 0 1 m.mtype = m.mtype :=
    lift_id_of_exprClosedAt_zero hrecScope 0
  have hallB := hcheck.2
  have hall : ∀ i : Fin a.constructors.length,
      exprClosedAt 0 a.constructors[i.val].mtype = true ∧
      iotaWitnessStableB E (h14.fuelAt i) (a.constructorViews i).fields
        (fieldBvars (a.constructorViews i).fields.length)
        (lift 0 ((a.constructorViews i).fields.length + 1 + a.constructors.length + a.family.indices.length)
          (ctorFieldTelescope (a.constructorViews i))) = true ∧
      iotaWitnessStableB (extendEnv E r m) (h14.fuelAt i)
        (a.constructorViews i).fields
        (fieldBvars (a.constructorViews i).fields.length)
        (lift 0 ((a.constructorViews i).fields.length + 1 + a.constructors.length + a.family.indices.length)
          (ctorFieldTelescope (a.constructorViews i))) = true ∧
      exprClosedAt (a.family.parameters.length + 1 + a.constructors.length +
        a.family.indices.length + (a.constructorViews i).fields.length)
        (descriptorSchema a h14 i) = true := by
    intro i
    have hb := (List.all_eq_true.mp hallB) i.val (List.mem_range.mpr i.isLt)
    simp only [i.isLt, dite_true] at hb
    have hfin : (⟨i.val, i.isLt⟩ : Fin a.constructors.length) = i := Fin.ext rfl
    rw [hfin] at hb
    simp only [recIdxCtorB, Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨⟨⟨hclosed, hbase⟩, hextended⟩, hscope⟩
    exact ⟨hclosed, hbase, hextended, hscope⟩
  have hfresh : E.members r = none := by
    cases hmem : E.members r with
    | none => rfl
    | some member => simp [hmem] at hfreshB
  have hextBase := extendEnv_extends_of_fresh (m := m) hfresh
  have stable : ∀ (i : Fin a.constructors.length) (E' : ResolvedEnv),
      (∀ r' m', E.members r' = some m' → E'.members r' = some m') →
        fieldShapesFuel E' (h14.fuelAt i) a.family.ref a.family.member.arity
            a.family.parameters.length a.family.indices.length
            a.family.parameters.length (a.constructorViews i).fields =
              some (h14.shapesAt i) ∧
          iotaSchemaAtIn E' a i (h14.fuelAt i) (h14.shapesAt i) =
            iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) := by
    intro i E' hext
    have hs := iotaWitnessS_hstable_of_constsMemberFuel
      (h14.analyzed i) (descriptorSchema_spec a h14 i) (hall i).2.1 E' hext
    exact ⟨hs.1, hs.2.trans (descriptorSchema_spec a h14 i).symm⟩
  refine { stable := stable, covered := ?_ }
  intro i
  let c := a.constructorViews i
  let np := a.family.parameters.length
  let q := a.family.indices.length
  let k := a.constructors.length
  let nf := c.fields.length
  let ctorResult := foldApps (.const a.family.ref (policyFamilyLevels a.family))
    (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices)
  let tel := lift 0 (nf + 1 + k + q) (ctorFieldTelescope c)
  let schema := descriptorSchema a h14 i
  have hctorPresent : (extendEnv E r m).members (a.family.ref + 1 + i.val) =
      some a.constructors[i.val] := hextBase _ _ (a.constructorsPresent i)
  have hfamPresent : (extendEnv E r m).members a.family.ref = some a.family.member :=
    hextBase _ _ a.family.present
  have hshapeSchema := stable i (extendEnv E r m) hextBase
  have hshapes : fieldShapesFuel (extendEnv E r m) (h14.fuelAt i)
      a.family.ref a.family.member.arity np q np c.fields = some (h14.shapesAt i) := by
    exact hshapeSchema.1
  have hschema : iotaOpenRhs (extendEnv E r m) (h14.fuelAt i)
      (.const r (canonRecLevels m.arity))
      (.bvar (nf + q + (k - 1 - i.val)))
      (preMajorBvars np k q nf) np k (h14.shapesAt i) (fieldBvars nf) tel =
        some schema := by
    have hs := hshapeSchema.2.trans (descriptorSchema_spec a h14 i)
    simpa only [iotaSchemaAtIn, policyRecursorLevels, canonRecLevels,
      a.recursorArity, tel, nf, np, q, k] using hs
  have hwstable := iotaWitnessS_hstable_of_constsMemberFuel hshapes hschema (hall i).2.2.1
  have hctorPi : piCount a.constructors[i.val].mtype = np + nf := by
    rw [c.storedType, piCount_policyPi]
    have hz : piCount ctorResult = 0 := by
      apply piCount_foldApps_of_zero
      rfl
    rw [hz, Nat.add_zero]
    simp only [List.length_append, c.parameterCount, np, nf]
  have hfamPi : piCount a.family.member.mtype = np + q := by
    rw [a.family.storedType, piCount_policyPi, List.length_append]
    change a.family.parameters.length + a.family.indices.length + 0 = np + q
    rw [Nat.add_zero]
  have hrecPi : piCount m.mtype = np + 1 + k + q + 1 := by
    rw [a.recursorType, policyRecursorType_eq_tel, piCount_policyPi]
    have hz : piCount (policyRecursorBody a) = 0 := by
      apply piCount_foldApps_of_zero
      rfl
    rw [hz, Nat.add_zero, policyRecursorDoms_length]
  have hctorPeel : peelPis (np + nf) a.constructors[i.val].mtype =
      some (c.parameters ++ c.fields, ctorResult) := by
    rw [c.storedType]
    have hlen : np + nf = (c.parameters ++ c.fields).length := by
      simp [np, nf, c.parameterCount]
    rw [hlen]
    exact peelPis_policyPi (c.parameters ++ c.fields) ctorResult
  have hrecPeel : peelPis (np + 1 + k + q + 1) m.mtype =
      some (policyRecursorDoms a, policyRecursorBody a) := by
    rw [a.recursorType, policyRecursorType_eq_tel, ← policyRecursorDoms_length]
    exact peelPis_policyPi _ _
  have hrecBody : policyRecursorBody a =
      foldApps (.bvar (k + q + 1))
        ((List.range q).reverse.map (fun j => Expr.bvar (j + 1)) ++ [.bvar 0]) := by
    simp [policyRecursorBody, a.minorCount, k, q]
  have hmajor : (policyRecursorDoms a)[np + 1 + k + q]? = some
      (foldApps (.const a.family.ref ((List.range a.family.member.arity).map Level.param))
        ((List.range np).reverse.map (fun j => Expr.bvar (j + q + k + 1)) ++
          (List.range q).reverse.map (fun j => Expr.bvar j))) := by
    have hl := policyRecursorDoms_last a
    rw [policyRecursorDoms_length] at hl
    simpa only [policyFamilyLevels, majorTyExpr, np, q, k] using hl
  have hctorFamily : isFamilyApp a.family.ref ctorResult = true := by
    simp only [ctorResult, isFamilyApp, appsSpine_foldApps_const, decide_True,
      Bool.true_and, List.all_eq_true]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      rfl
    · have hf := c.noFamilyInIndices x hx
      simp [hf]
  have hdrop : (c.parameters ++ c.fields).drop np = c.fields := by
    rw [show np = c.parameters.length by exact c.parameterCount.symm]
    simp
  have hctorTel : ctorFieldTelRaw np (c.parameters ++ c.fields) ctorResult =
      ctorFieldTelescope c := by
    unfold ctorFieldTelRaw ctorFieldTelescope
    rw [hdrop]
    change c.fields.foldr Expr.pi ctorResult = policyPi c.fields ctorResult
    exact (policyPi_eq_foldr c.fields ctorResult).symm
  refine ⟨{
    recRef := r
    ctorRef := a.family.ref + 1 + i.val
    ls := canonRecLevels m.arity
    lsC := policyFamilyLevels a.family
    recMember := m
    ctorMember := a.constructors[i.val]
    hrec := by simp [extendEnv]
    hctor := hctorPresent
    hrecK := hrecK
    hctorK := c.hasClass
    preMajor := preMajorBvars np k q nf
    fields := fieldBvars nf
    ctorParams := fieldBvars np
    familyRef := a.family.ref
    famMember := a.family.member
    hfam := hfamPresent
    hfamK := a.family.hasClass
    nparams := np
    nindices := q
    nMinors := k
    ctorIdx := i.val
    hctorParams := by simp [fieldBvars]
    hnpar := by simpa [fieldBvars] using hctorPi.symm
    hnidx := hfamPi.symm
    hnmin := hrecPi.symm
    hidx := i.isLt
    hctorIdx := rfl
    hrecIdx := a.recursorRef
    hpre := by simp [preMajorBvars]
    ctorDoms := c.parameters ++ c.fields
    ctorResult := ctorResult
    hpeel := by simpa [fieldBvars] using hctorPeel
    hfamApp := hctorFamily
    recDoms := policyRecursorDoms a
    recBody := policyRecursorBody a
    hpeelRec := hrecPeel
    hrecBody := hrecBody
    hmajorTy := hmajor
    hrecClosed := hrecClosed
    hctorClosed := lift_id_of_exprClosedAt_zero (hall i).1 0
    hlsLen := by simp [canonRecLevels]
    fuel := h14.fuelAt i
    shapes := h14.shapesAt i
    hshapes := by simpa only [hdrop] using hshapes
    schema := schema
    hschema := by simpa [fieldBvars, hctorTel, tel] using hschema
    hstable := by
      intro E' hext
      simpa [fieldBvars, hdrop, hctorTel, tel] using hwstable E' hext
    hschemaScope := by
      simpa [fieldBvars, np, q, k, nf, schema] using (hall i).2.2.2
  }, rfl, rfl, rfl, rfl, rfl, rfl, descriptorSchema_spec a h14 i⟩

/-- R-NoFunRec-1 B2, step 2d-2b: the typed environment's recursor/index obligation, as a
family over the member's admission. At a `.recursor` admission it is
`RecursorGroupIdxAdmittedT a h14` — the typed counterpart, ranging over shape witnesses
(`IotaWitnessS`) with coverage from admission's own descriptor `h14`. At every other
member (family, constructor) it is `PUnit`. The legacy obligation
`m.mclass = .recursorM → RecursorGroupIdxAdmitted E r m` of `EnvWf.indMember` is
unchanged and still used by the legacy `EnvWf`. -/
def IdxAdmittedT {E : ResolvedEnv} {r : Nat} {m : CheckedMember} :
    IndGroupAdmitted E r m → Type
  | .recursor a _ _ _ _ _ h14 => RecursorGroupIdxAdmittedT a h14
  | _ => PUnit

/-- Non-vacuity at a recursor member: `m.mclass = .recursorM` forces the admission to be
the `.recursor` case — the family case contradicts the class through `view.member = m`
and `view.hasClass`, the constructor case through `view.hasClass` directly. So
`IdxAdmittedT hadm` there is the real coverage obligation `RecursorGroupIdxAdmittedT a h14`,
not `PUnit`. -/
theorem IdxAdmittedT.recursor_cases {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hadm : IndGroupAdmitted E r m) (hclass : m.mclass = .recursorM) :
    ∃ (a : RecursorEliminationAdmitted E r m) (hfresh : E.members r = none)
      (h04 : CtorCensus E a.family.ref r)
      (h07 : ∀ i, FieldUniverseAdmitted (a.constructorViews i))
      (h08 : ∀ i, CtorFieldsPermitted (a.constructorViews i))
      (h12 : MinorPremisesMatch a) (h14 : IotaDescriptorClause E a),
      hadm = .recursor a hfresh h04 h07 h08 h12 h14 ∧
        IdxAdmittedT hadm = RecursorGroupIdxAdmittedT a h14 := by
  cases hadm with
  | family hfresh view href hm hProfile =>
      have hc := view.hasClass
      rw [hm] at hc
      rw [hc] at hclass
      nomatch hclass
  | constructor family view hfresh h04 hContig h07 h08 =>
      rw [view.hasClass] at hclass
      nomatch hclass
  | recursor a hfresh h04 h07 h08 h12 h14 =>
      exact ⟨a, hfresh, h04, h07, h08, h12, h14, rfl, rfl⟩

end Rcic.Declarative
