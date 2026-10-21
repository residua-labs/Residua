import rcic.RcicTypedIdxAdmitted
import rcic.RcicIotaWitnessTyped
import rcic.RcicRecursorCellHT

/-!
# DT-019 S2 (a) — the LEGACY ι witness read against admission

`IotaWitness.recData_admitted`: a legacy `IotaWitness` at an admitted recursor
reads the same family/parameter/index/minor data as admission's
`RecursorEliminationAdmitted` — the legacy twin of
`IotaWitnessS.recData_admitted` (`RcicTypedIdxAdmitted`), same proof on the
fields the two witness structures share (`hpeelRec`, `hmajorTy`, `hnmin`,
`hrecIdx`, `hfam`). The helpers that proof reads are `private` there, so they
are repeated here verbatim (file-local names, no clash, nothing exported twice).

`RecursorCellT.ctorMember_eqL` / `ctorData_eqL`: the cell's constructor lemmas
(`RcicIotaWitnessTyped`) for a legacy witness.

`hasTyT_exprClosedAt`: a typed term's bound variables are below its context's
length (the scope certificate `IotaWitnessS.hschemaScope` needs, read off
admission's typed equation).

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) private helpers, repeated from `RcicTypedIdxAdmitted` (file-local there) -/

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

private theorem policyPi_append' (xs ys : List (Expr Nat)) (body : Expr Nat) :
    policyPi (xs ++ ys) body = policyPi xs (policyPi ys body) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Expr.pi x) ih

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


/-! ## (2) the legacy witness against admission -/

/-- the legacy twin of `IotaWitnessS.recData_admitted`: same fields, same proof. -/
theorem IotaWitness.recData_admitted
    {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (hext : ∀ r' m', (extendEnv E r m).members r' = some m' →
      E'.members r' = some m')
    (w : IotaWitness E') (hr : w.recRef = r) (hm : w.recMember = m) :
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

/-- the witness's constructor is admission's `i`-th constructor (legacy witness;
    `RecursorCellT.ctorMember_eq`'s proof). -/
theorem RecursorCellT.ctorMember_eqL {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellT E r m) (w : IotaWitness E)
    (hf : w.familyRef = c.adm.family.ref)
    (i : Fin c.adm.constructors.length) (hi : i.val = w.ctorIdx) :
    w.ctorMember = c.adm.constructors[i] := by
  have hp := c.adm.constructorsPresent i
  have he := c.env_extends _ _ hp
  have hcref : w.ctorRef = c.adm.family.ref + 1 + i.val := by
    rw [w.hctorIdx, hf, ← hi]
  have hc := w.hctor
  rw [hcref] at hc
  exact Option.some.inj (hc.symm.trans he)

/-- the witness's peeled domains and result are the view's (legacy witness;
    `RecursorCellT.ctorData_eq`'s proof). -/
theorem RecursorCellT.ctorData_eqL {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellT E r m) (w : IotaWitness E)
    (i : Fin c.adm.constructors.length)
    (hcm : w.ctorMember = c.adm.constructors[i]) :
    w.ctorDoms = (c.adm.constructorViews i).parameters ++
        (c.adm.constructorViews i).fields ∧
      w.ctorResult =
        foldApps (.const c.adm.family.ref (policyFamilyLevels c.adm.family))
          (policyParameterLocals (c.adm.constructorViews i).parameters.length
            (c.adm.constructorViews i).fields.length ++
            (c.adm.constructorViews i).resultIndices) := by
  have hst : w.ctorMember.mtype =
      policyPi ((c.adm.constructorViews i).parameters ++
        (c.adm.constructorViews i).fields)
        (foldApps (.const c.adm.family.ref (policyFamilyLevels c.adm.family))
          (policyParameterLocals (c.adm.constructorViews i).parameters.length
            (c.adm.constructorViews i).fields.length ++
            (c.adm.constructorViews i).resultIndices)) := by
    rw [hcm]
    exact (c.adm.constructorViews i).storedType
  have hpc : piCount w.ctorMember.mtype =
      ((c.adm.constructorViews i).parameters ++
        (c.adm.constructorViews i).fields).length := by
    rw [hst, piCount_policyPi,
      piCount_foldApps_of_zero
        (.const c.adm.family.ref (policyFamilyLevels c.adm.family)) _ rfl,
      Nat.add_zero]
  have hpeel := w.hpeel
  rw [w.hnpar, hpc, hst, peelPis_policyPi] at hpeel
  have hpair := Option.some.inj hpeel
  exact ⟨(congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩

/-! ## (3) typing bounds the free variables -/

theorem lookupType_lt {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType Γ i = some A) : i < Γ.length := by
  unfold lookupType at h
  cases hg : Γ.get? i with
  | none => rw [hg] at h; cases h
  | some d =>
      have := List.get?_eq_some.1 hg
      exact this.1

/-- a typed term is closed at its context's length. -/
theorem hasTyT_exprClosedAt {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → exprClosedAt Γ.length e = true
  | _, _, _, .sort _ _ => rfl
  | _, _, _, .bvar _ i _ h => by
      simp only [exprClosedAt, decide_eq_true_eq]
      exact lookupType_lt h
  | _, _, _, .const _ _ _ _ _ _ _ => rfl
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      simp only [exprClosedAt, Bool.and_eq_true]
      exact ⟨hasTyT_exprClosedAt hA, hasTyT_exprClosedAt hB⟩
  | _, _, _, .lam _ _ _ _ _ hA hb => by
      simp only [exprClosedAt, Bool.and_eq_true]
      exact ⟨hasTyT_exprClosedAt hA, hasTyT_exprClosedAt hb⟩
  | _, _, _, .app _ _ _ _ _ hf ha => by
      simp only [exprClosedAt, Bool.and_eq_true]
      exact ⟨hasTyT_exprClosedAt hf, hasTyT_exprClosedAt ha⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => by
      simp only [exprClosedAt, Bool.and_eq_true]
      exact ⟨⟨hasTyT_exprClosedAt hA, hasTyT_exprClosedAt hv⟩, hasTyT_exprClosedAt hb⟩
  | _, _, _, .lit _ _ _ _ => rfl
  | _, _, _, .conv _ _ _ _ _ h _ => hasTyT_exprClosedAt h

end Rcic.Declarative

#print axioms Rcic.Declarative.IotaWitness.recData_admitted
#print axioms Rcic.Declarative.RecursorCellT.ctorMember_eqL
#print axioms Rcic.Declarative.RecursorCellT.ctorData_eqL
#print axioms Rcic.Declarative.hasTyT_exprClosedAt
