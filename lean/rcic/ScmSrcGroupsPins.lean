import rcic.ScmSrcGroups

/-! Pins on the regrouped table (#6029). -/

open Rcic.Declarative
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/-! ## Structural pin carried from V1–V3 -/

theorem srcLenG : srcMembersG.length = 168 := by decide

theorem srcNoAxiomG : srcMembersG.all (fun p =>
    p.2.mclass != .axiomM && p.2.mclass != .opaqueM) = true := by decide

/-! ## R-NoFunRec (#6151) incidence on the regrouped table.

Main's ι takes a constructor's field kinds from `analyzeFields`
(`IotaWitness.hkinds`, RcicDeclarative.lean:796). A function-recursive
field (`Π y, I idx(y)`, 05 §8/§12) gets no kind, so no `IotaWitness`
exists for its constructor and ι derives no rule for it. L-K1's admission
is unaffected: it admits these fields (`ScmSrcGroupsAdm`), and the 05 §14
evidence for CCT and ValueAt states their ι equations (`ScmSrcGroupsRec`,
`ScmSrcGroupsRecVA`). Main's ι does not compute the recursor on them.

Measured here: exactly four of the 64 constructors are affected:
`cctSum` 103 and `cctRec` 104 (CCT), `vaList` 139 and `vaR` 142
(ValueAt). `noIotaWitness_funRec` proves that no ι witness on `srcEnvG`
has one of them. Routing: main's ι, recorded by #6151; not L-K1's
judgment, and not this segment's to lift.

`srcKindsVsShapesG` measures the other gap #6151 names, R-NoDeltaRec, and finds no incidence. -/

/-- Index of the first domain to which main's ι gives no field kind. -/
def firstNoKind (f : Nat) (ds : List (Expr Nat)) : Option Nat :=
  ds.findIdx? fun T => (analyzeField f T).isNone

/-- `(constructor slot, family Π-count, first no-kind position)` for every constructor of `srcMembersG` that has a no-kind domain. -/
def noKindCtors : List (Nat × Nat × Nat) :=
  srcMembersG.filterMap fun (r, m) =>
    if m.mclass = .constructorM then
      match memberFamRef m with
      | some f =>
        match peelPis (piCount m.mtype) m.mtype, srcMembersG.lookup f with
        | some (ds, _), some fm =>
            (firstNoKind f ds).map fun i => (r, piCount fm.mtype, i)
        | _, _ => none
      | none => none
    else none

/-- Every constructor's result head is a member of the table and its whole telescope peels, so `noKindCtors` skips none. -/
theorem srcCtorPeelG : srcMembersG.all (fun (_, m) =>
    !(decide (m.mclass = .constructorM)) ||
    ((match memberFamRef m with
      | some f => (srcMembersG.lookup f).isSome
      | none => false) &&
     (peelPis (piCount m.mtype) m.mtype).isSome)) = true := by decide

theorem noKindCtors_eq : noKindCtors =
    [(103, 2, 14), (104, 2, 14), (139, 2, 13), (142, 2, 20)] := by decide

private theorem analyzeFields_findIdx_none {f start : Nat}
    {ds : List (Expr Nat)} {ks : List RecKind}
    (hk : analyzeFields f ds = some ks) :
    List.findIdx? (fun T => (analyzeField f T).isNone) ds start = none := by
  induction ds generalizing ks start with
  | nil => rfl
  | cons T Ts ih =>
      cases hT : analyzeField f T with
      | none => simp [analyzeFields, hT] at hk
      | some k =>
          cases hks : analyzeFields f Ts with
          | none => simp [analyzeFields, hT, hks] at hk
          | some ks' =>
              simp only [List.findIdx?, hT, Option.isNone_some,
                Bool.false_eq_true, if_false]
              exact ih hks

private theorem firstNoKindFrom_lt_of_drop {f start k i : Nat}
    {ds : List (Expr Nat)} {ks : List RecKind}
    (hk : analyzeFields f (ds.drop k) = some ks)
    (hi : List.findIdx? (fun T => (analyzeField f T).isNone) ds start = some i) :
    i < start + k := by
  induction k generalizing start ds i ks with
  | zero =>
      simp only [List.drop_zero] at hk
      rw [analyzeFields_findIdx_none hk] at hi
      contradiction
  | succ k ih =>
      cases ds with
      | nil => simp [List.findIdx?] at hi
      | cons T Ts =>
          simp only [List.drop_succ_cons] at hk
          cases hT : analyzeField f T with
          | none =>
              simp [List.findIdx?, hT] at hi
              subst i
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ k)
          | some rk =>
              simp only [List.findIdx?, hT, Option.isNone_some,
                Bool.false_eq_true, if_false] at hi
              have hlt := ih hk hi
              simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hlt

theorem firstNoKind_lt_of_drop {f k i : Nat} {ds : List (Expr Nat)}
    {ks : List RecKind}
    (hk : analyzeFields f (ds.drop k) = some ks)
    (hi : firstNoKind f ds = some i) : i < k := by
  have hlt := firstNoKindFrom_lt_of_drop (start := 0) hk hi
  simpa using hlt

private def fullDoms (m : CheckedMember) : List (Expr Nat) :=
  match peelPis (piCount m.mtype) m.mtype with
  | some (ds, _) => ds
  | none => []

private def fullResult (m : CheckedMember) : Expr Nat :=
  match peelPis (piCount m.mtype) m.mtype with
  | some (_, r) => r
  | none => .sort .zero

private theorem noIotaWitnessAt (w : IotaWitness srcEnvG)
    (r f i : Nat) (m fm : CheckedMember)
    (href : w.ctorRef = r)
    (hmem : srcEnvG.members r = some m)
    (hpeel : peelPis (piCount m.mtype) m.mtype =
      some (fullDoms m, fullResult m))
    (hfirst : firstNoKind f (fullDoms m) = some i)
    (hhead : ∀ f', isFamilyApp f' (fullResult m) = true → f' = f)
    (hfmem : srcEnvG.members f = some fm)
    (hfcount : piCount fm.mtype = 2)
    (hi : 2 ≤ i) : False := by
  have hwmem : srcEnvG.members r = some w.ctorMember := by
    simpa [href] using w.hctor
  have hm : w.ctorMember = m := by
    rw [hmem] at hwmem
    exact (Option.some.inj hwmem).symm
  have hp : peelPis (piCount m.mtype) m.mtype =
      some (w.ctorDoms, w.ctorResult) := by
    rw [← hm, ← w.hnpar]
    exact w.hpeel
  have hpair : (w.ctorDoms, w.ctorResult) =
      (fullDoms m, fullResult m) :=
    Option.some.inj (hp.symm.trans hpeel)
  have hds : w.ctorDoms = fullDoms m := congrArg Prod.fst hpair
  have hresult : w.ctorResult = fullResult m := congrArg Prod.snd hpair
  have hfamily : w.familyRef = f :=
    hhead w.familyRef (by simpa [hresult] using w.hfamApp)
  have hwfam : srcEnvG.members f = some w.famMember := by
    simpa [hfamily] using w.hfam
  have hfm : w.famMember = fm := by
    rw [hfmem] at hwfam
    exact (Option.some.inj hwfam).symm
  have hnidx : w.nparams + w.nindices = 2 := by
    simpa [hfm, hfcount] using w.hnidx
  have hnp : w.nparams ≤ 2 := by
    calc
      w.nparams ≤ w.nparams + w.nindices := Nat.le_add_right _ _
      _ = 2 := hnidx
  have hk : analyzeFields f ((fullDoms m).drop w.nparams) = some w.kinds := by
    simpa [hfamily, hds] using w.hkinds
  have hlt := firstNoKind_lt_of_drop hk hfirst
  exact (Nat.not_lt_of_ge hi) (Nat.lt_of_lt_of_le hlt hnp)

theorem noIotaWitness_funRec (w : IotaWitness srcEnvG)
    (h : w.ctorRef ∈ [103, 104, 139, 142]) : False := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at h
  rcases h with h103 | h104 | h139 | h142
  · exact noIotaWitnessAt w 103 96 14 mCctSum mCCT h103 rfl rfl rfl
      (by
        intro f' hf
        have hs := hf
        simp [fullResult, isFamilyApp, appsSpine] at hs
        exact hs.1.symm)
      rfl rfl (by decide)
  · exact noIotaWitnessAt w 104 96 14 mCctRec mCCT h104 rfl rfl rfl
      (by
        intro f' hf
        have hs := hf
        simp [fullResult, isFamilyApp, appsSpine] at hs
        exact hs.1.symm)
      rfl rfl (by decide)
  · exact noIotaWitnessAt w 139 133 13 mVaList mValueAt h139 rfl rfl rfl
      (by
        intro f' hf
        have hs := hf
        simp [fullResult, isFamilyApp, appsSpine] at hs
        exact hs.1.symm)
      rfl rfl (by decide)
  · exact noIotaWitnessAt w 142 133 20 mVaR mValueAt h142 rfl rfl rfl
      (by
        intro f' hf
        have hs := hf
        simp [fullResult, isFamilyApp, appsSpine] at hs
        exact hs.1.symm)
      rfl rfl (by decide)

/-- ι's field kind, read as an admission shape. -/
def kindShape : RecKind → FieldShape
  | .plain => .nonrecursive
  | .directRec => .recursive 0

/-- Admission's function-recursive shape: an inner Π telescope. -/
def isFunRecShape : FieldShape → Bool
  | .recursive (_ + 1) => true
  | _ => false

/-- Wherever main's ι reads kinds for a constructor, they agree field by field with L-K1's admission shapes. Wherever ι reads none, admission sees a function-recursive field. So no field of this table is recursive only after δ: R-NoDeltaRec (#6151) has no incidence here. -/
theorem srcKindsVsShapesG : srcMembersG.all (fun (_, m) =>
    !(decide (m.mclass = .constructorM)) ||
    match memberFamRef m with
    | none => false
    | some f =>
      match srcMembersG.lookup f with
      | none => false
      | some fm =>
        match analyzeFields f (ctorDom m),
            fieldShapesFuel srcEnvG 96 f 0 0 (piCount fm.mtype) 0 (ctorDom m) with
        | some ks, some ss => ks.map kindShape == ss
        | none, some ss => ss.any isFunRecShape
        | _, none => false) = true := by decide

end Rcic.Scm.SrcG
