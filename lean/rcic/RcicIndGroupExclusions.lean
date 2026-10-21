/-
L-K1 segment 1 refusals (#6075). The four environments are the original
member bytes, not a retyping:

* `ExBool` — `ba894b9180` `RcicPropBoolCore` (two Prop constructors,
  motive `Sort 1`). Refused by 05 §10.
* `ExUniv` — `2c28cb8d13` `RcicUniverseRetractionProbe` (`U : Sort 1`,
  `c : Sort 1 → U`). The canonical telescope is refused by 05 §7.
* `ExAlias` — `2c28cb8d13` `RcicNegativeAliasProbe` (transparent
  `Alias := U → Sort 1`). Refused by 05 §§8–9.
* `Rcic.Scm.SrcTV` — `babd0a56e3` `srcEnvV1` slots 11 / 43. Refused
  by 04 §1 contiguity.

`EnvWf natEnvU` is `natEnvUWfAt`. Sort conversion is not proved.
-/
import rcic.RcicIndGroupAdmitted
import rcic.RcicIndGroupFixtureWf
import rcic.RcicInvertFamily
import rcic.RcicSrcEnvV1

namespace Rcic.Declarative

theorem uniformProp_zero : UniformProp .zero := by
  intro _
  simp [evalTotal]

theorem not_uniformType_zero : ¬ UniformType .zero := by
  intro h
  have := h (fun _ => 0)
  simp [evalTotal] at this

theorem not_uniformProp_succ_zero : ¬ UniformProp (.succ .zero) := by
  intro h
  have := h (fun _ => 0)
  simp [evalTotal] at this

theorem not_leN_ssz_sz : ¬ leN (.succ (.succ .zero)) (.succ .zero) := by
  intro h
  have hx : eval (fun _ => none) (.succ (.succ .zero)) = some 2 := by simp [eval]
  have hy : eval (fun _ => none) (.succ .zero) = some 1 := by simp [eval]
  have := h (fun _ => none) 2 1 hx hy
  omega

theorem policyPi_eq_sort {xs : List (Expr Nat)} {body : Expr Nat} {l : Level}
    (h : policyPi xs body = .sort l) : xs = [] ∧ body = .sort l := by
  cases xs with
  | nil => exact ⟨rfl, h⟩
  | cons _ _ =>
      simp only [policyPi] at h
      nomatch h

theorem piResult_policyPi (xs : List (Expr Nat)) (b : Expr Nat) :
    piResult (policyPi xs b) = piResult b := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp only [policyPi, piResult, ih]

theorem appsSpine_fold_head (f : Expr Nat) (as : List (Expr Nat)) :
    (appsSpine (foldApps f as)).1 = (appsSpine f).1 := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
      simpa only [foldApps, appsSpine] using ih (.app f a)

theorem spineHead_bvar_fold (i : Nat) (as : List (Expr Nat)) :
    spineHeadRef (foldApps (.bvar i) as) = none := by
  simp only [spineHeadRef, appsSpine_fold_head, appsSpine]

/-- Heads reached from a bare bvar by application only. -/
def HeadBvar : Expr Nat → Prop
  | .bvar _ => True
  | .app f _ => HeadBvar f
  | _ => False

theorem foldApps_headBvar {f : Expr Nat} (hf : HeadBvar f) (as : List (Expr Nat)) :
    HeadBvar (foldApps f as) := by
  induction as generalizing f with
  | nil =>
      simp only [foldApps]
      exact hf
  | cons _ _ ih =>
      exact ih (by
        simp only [HeadBvar]
        exact hf)

theorem piResult_headBvar {e : Expr Nat} (h : HeadBvar e) : piResult e = e := by
  cases e with
  | bvar _ => rfl
  | app _ _ => rfl
  | pi _ _ => simp [HeadBvar] at h
  | sort _ => simp [HeadBvar] at h
  | const _ _ => simp [HeadBvar] at h
  | lam _ _ => simp [HeadBvar] at h
  | letE _ _ _ => simp [HeadBvar] at h
  | lit _ => simp [HeadBvar] at h

theorem spine_piResult_bvar (i : Nat) (as : List (Expr Nat)) :
    spineHeadRef (piResult (foldApps (.bvar i) as)) = none := by
  have hb : HeadBvar (foldApps (.bvar i) as) :=
    foldApps_headBvar (by simp [HeadBvar]) as
  rw [piResult_headBvar hb]
  exact spineHead_bvar_fold i as

/-- A 05 §13 skeleton ends in the motive application, never in a constant. -/
theorem policyRecursor_not_const {E : ResolvedEnv} (family : PolicyFamilyView E)
    (minors : List (Expr Nat)) (p : EliminationPolicy) :
    spineHeadRef (piResult (policyRecursorType family minors p)) = none := by
  unfold policyRecursorType
  simp only [piResult_policyPi, piResult]
  refine spine_piResult_bvar _ _

/-- No parameters and no indices: a PropOnly skeleton opens with the
motive `Π (_ : I), Sort 0`. The minor telescope is irrelevant. -/
theorem propOnly_opens_motive {E : ResolvedEnv} (family : PolicyFamilyView E)
    (minors : List (Expr Nat))
    (hpar : family.parameters = []) (hind : family.indices = []) :
    ∃ rest, policyRecursorType family minors .propOnly =
      .pi (.pi (foldApps (.const family.ref (policyFamilyLevels family)) [])
            (.sort .zero)) rest := by
  unfold policyRecursorType policyMotiveType policyMotiveLevel
  simp only [hpar, hind, List.length_nil, Nat.add_zero, policyPi,
    policyLocals, policyParameterLocals, List.range_zero, List.reverse_nil,
    List.map_nil, List.append_nil, foldApps]
  exact ⟨
      policyPi minors
        (.pi
          (foldApps (.const family.ref (policyFamilyLevels family))
            (policyParameterLocals 0 (minors.length + 1)))
          (.app (.bvar (minors.length + 1)) (.bvar 0))),
      rfl⟩

/-! ## BoolP : Prop, two constructors, motive in Sort 1. -/

namespace ExBool

def boolP : Expr Nat := .const 0 []
def boolTrue : Expr Nat := .const 1 []
def boolFalse : Expr Nat := .const 2 []

def boolFamMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def boolTrueMember : CheckedMember := ⟨.constructorM, 0, boolP, none⟩
def boolFalseMember : CheckedMember := ⟨.constructorM, 0, boolP, none⟩

def boolMotiveType : Expr Nat := .pi boolP (.sort (.succ .zero))
def boolMinorTrueType : Expr Nat := .app (.bvar 0) boolTrue
def boolMinorFalseType : Expr Nat := .app (.bvar 1) boolFalse

def boolRecType : Expr Nat :=
  .pi boolMotiveType
    (.pi boolMinorTrueType
      (.pi boolMinorFalseType
        (.pi boolP (.app (.bvar 3) (.bvar 0)))))

def boolRecMember : CheckedMember := ⟨.recursorM, 0, boolRecType, none⟩

def boolPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 0 boolFamMember) 1 boolTrueMember)
    2 boolFalseMember

def boolEnv : ResolvedEnv := extendEnv boolPrefix 3 boolRecMember

theorem boolRec_bytes :
    boolRecMember.mtype =
      .pi (.pi (.const 0 []) (.sort (.succ .zero)))
        (.pi (.app (.bvar 0) (.const 1 []))
          (.pi (.app (.bvar 1) (.const 2 []))
            (.pi (.const 0 []) (.app (.bvar 3) (.bvar 0))))) := rfl

theorem boolPrefix_members (n : Nat) :
    boolPrefix.members n =
      if n = 2 then some boolFalseMember
      else if n = 1 then some boolTrueMember
      else if n = 0 then some boolFamMember
      else none := rfl

theorem boolEnv_rec_member :
    boolEnv.members 3 = some boolRecMember := rfl

theorem bool_only_inductive {n : Nat} {m : CheckedMember}
    (hm : boolPrefix.members n = some m) (hc : m.mclass = .inductiveM) :
    n = 0 ∧ m = boolFamMember := by
  rw [boolPrefix_members] at hm
  by_cases h2 : n = 2
  · rw [if_pos h2] at hm
    cases hm
    rw [boolFalseMember] at hc
    cases hc
  · rw [if_neg h2] at hm
    by_cases h1 : n = 1
    · rw [if_pos h1] at hm
      cases hm
      rw [boolTrueMember] at hc
      cases hc
    · rw [if_neg h1] at hm
      by_cases h0 : n = 0
      · rw [if_pos h0] at hm
        cases hm
        exact ⟨h0, rfl⟩
      · rw [if_neg h0] at hm
        cases hm

end ExBool

/-- `not_exBool_recursor` for any prefix whose members are among
`boolPrefix`'s. The only environment read is `family.present`. -/
def not_exBool_sub {E : ResolvedEnv}
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E.members k = some cm → ExBool.boolPrefix.members k = some cm)
    (h : IndGroupAdmitted E 3 ExBool.boolRecMember) : Empty := by
  cases h with
  | family _ view _ hm _ =>
      have hc := view.hasClass
      rw [hm] at hc
      rw [ExBool.boolRecMember] at hc
      cases hc
  | constructor _ view _ _ _ _ _ =>
      have hc := view.hasClass
      rw [ExBool.boolRecMember] at hc
      cases hc
  | recursor a _ _ _ _ _ _ =>
      have ⟨href, hmem⟩ :=
        ExBool.bool_only_inductive (hsub a.family.present) a.family.hasClass
      have hs := a.family.storedType
      rw [hmem, ExBool.boolFamMember] at hs
      have ⟨hcat, hbody⟩ := policyPi_eq_sort hs.symm
      have hpar : a.family.parameters = [] :=
        (List.append_eq_nil.mp hcat).1
      have hind : a.family.indices = [] :=
        (List.append_eq_nil.mp hcat).2
      have hres : a.family.resultLevel = .zero := by
        injection hbody
      have hk : a.constructors.length = 2 := by
        have hr := a.recursorRef
        rw [href] at hr
        omega
      have hsel := a.selected
      have hprop : UniformProp a.family.resultLevel := by
        rw [hres]
        exact uniformProp_zero
      have hmany : 1 < a.constructors.length := by omega
      have hpol : a.policy = .propOnly :=
        EliminationSelection.deterministic hsel
          (.multipleProp hprop hmany)
      have ht := a.recursorType
      rw [hpol] at ht
      have hbad : False := by
        obtain ⟨_, hshape⟩ :=
          propOnly_opens_motive a.family a.minorTypes hpar hind
        rw [hshape] at ht
        simp only [hmem, href, ExBool.boolFamMember, ExBool.boolRecMember,
          policyFamilyLevels, List.range_zero, List.map_nil, foldApps] at ht
        injection ht with hdom _
        injection hdom with _ hsort
        injection hsort with hlev
        cases hlev
      exact False.elim hbad

def not_exBool_recursor
    (h : IndGroupAdmitted ExBool.boolPrefix 3 ExBool.boolRecMember) : Empty :=
  not_exBool_sub (fun {_ _} hk => hk) h

/-! ## U : Sort 1, constructor Sort 1 → U. Canonical 05 §7 telescope. -/

namespace ExUniv

def u1 : Level := .succ .zero
def u2 : Level := .succ u1
def familyMember : CheckedMember := ⟨.inductiveM, 0, .sort u1, none⟩
def U : Expr Nat := .const 0 []
def fieldType : Expr Nat := .sort u1
def ctor : CheckedMember := ⟨.constructorM, 0, .pi fieldType U, none⟩
def familyPrefix : ResolvedEnv := extendEnv emptyEnv 0 familyMember
def ctorPrefix : ResolvedEnv := extendEnv familyPrefix 1 ctor

theorem ctor_bytes :
    ctor = (⟨.constructorM, 0, .pi (.sort (.succ .zero)) (.const 0 []), none⟩ :
      CheckedMember) := rfl

theorem prefix_bytes :
    ctorPrefix =
      extendEnv (extendEnv emptyEnv 0
        ⟨.inductiveM, 0, .sort (.succ .zero), none⟩) 1 ctor := rfl

def family : PolicyFamilyView ctorPrefix where
  ref := 0
  member := familyMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := u1
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fieldTy : HasTy ctorPrefix 0 [] fieldType (.sort u2) :=
  HasTy.sort [] u1

def ctorView : PolicyConstructorView ctorPrefix family ctor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [fieldType]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => u2
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem field_refused : ¬ FieldUniverseAdmitted ctorView := by
  intro h
  have h0 := h ⟨0, by decide⟩
  have hlev : ctorView.fieldLevel ⟨0, by decide⟩ = u2 := by
    unfold PolicyConstructorView.fieldLevel PolicyConstructorView.fieldIndex
    simp [ctorView]
  rw [hlev] at h0
  rcases h0 with hp | ⟨_, hl⟩
  · exact not_uniformProp_succ_zero hp
  · exact not_leN_ssz_sz hl

/- `EnvWf ctorPrefix n → False` is not stated. `FieldUniverseAdmitted`
reads `domainsTyped`, and `HasTy.conv` can ascribe `Sort 1` any sort
convertible with `Sort 2`. Closing that conversion is `SortConvChar`,
which #6075 does not prove. `groupArityCoherent` and
`exprFamCanonical` both accept this constructor. -/

end ExUniv

/-! ## Transparent Alias := U → Sort 1, with U : Sort 2. -/

namespace ExAlias

def u1 : Level := .succ .zero
def u2 : Level := .succ u1
def aliasLevel : Level := .imax u2 u2
def U : Expr Nat := .const 0 []
def F : Expr Nat := .pi U (.sort u1)
def Alias : Expr Nat := .const 10 []
def familyMember : CheckedMember := ⟨.inductiveM, 0, .sort u2, none⟩
def aliasMember : CheckedMember :=
  ⟨.definitionM, 0, .sort aliasLevel, some F⟩
def familyPrefix : ResolvedEnv := extendEnv emptyEnv 0 familyMember
def aliasPrefix : ResolvedEnv := extendEnv familyPrefix 10 aliasMember
def ctor : CheckedMember := ⟨.constructorM, 0, .pi Alias U, none⟩
def ctorPrefix : ResolvedEnv := extendEnv aliasPrefix 1 ctor

theorem alias_bytes :
    aliasMember =
      (⟨.definitionM, 0,
        .sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero))),
        some (.pi (.const 0 []) (.sort (.succ .zero)))⟩ : CheckedMember) := rfl

theorem ctor_bytes :
    ctor = (⟨.constructorM, 0, .pi (.const 10 []) (.const 0 []), none⟩ :
      CheckedMember) := rfl

theorem prefix_bytes :
    (ctorPrefix.members 0, ctorPrefix.members 10, ctorPrefix.members 1) =
      (some familyMember, some aliasMember, some ctor) := rfl

theorem negative :
    fieldAnalyze ctorPrefix 16 0 0 0 0 0 Alias =
      .refused .negativeOccurrence := rfl

/-- 05 §§8–9 read the transparent body at slot 10 and then the family
constant. Any environment with that same alias member refuses `Alias`. -/
theorem negative_at {E : ResolvedEnv}
    (h10 : E.members 10 = some aliasMember) :
    fieldAnalyze E 16 0 0 0 0 0 Alias =
      .refused .negativeOccurrence := by
  unfold fieldAnalyze
  simp only [Alias]
  unfold piTelescopeFuel whnfFuel
  simp only [appsSpine, transparentBody, h10, transparent, aliasMember,
    instantiateLevels, instLevel, F, foldApps, domainsContainFuel,
    containsFamilyFuel]
  rfl

theorem alias_members (n : Nat) :
    ctorPrefix.members n =
      if n = 1 then some ctor
      else if n = 10 then some aliasMember
      else if n = 0 then some familyMember
      else none := rfl

theorem alias_only_inductive {n : Nat} {m : CheckedMember}
    (hm : ctorPrefix.members n = some m) (hc : m.mclass = .inductiveM) :
    n = 0 ∧ m = familyMember := by
  rw [alias_members] at hm
  by_cases h1 : n = 1
  · rw [if_pos h1] at hm
    cases hm
    unfold ctor at hc
    cases hc
  · rw [if_neg h1] at hm
    by_cases h10 : n = 10
    · rw [if_pos h10] at hm
      cases hm
      unfold aliasMember at hc
      cases hc
    · rw [if_neg h10] at hm
      by_cases h0 : n = 0
      · rw [if_pos h0] at hm
        cases hm
        exact ⟨h0, rfl⟩
      · rw [if_neg h0] at hm
        cases hm

end ExAlias

def not_exAlias_sub {E : ResolvedEnv}
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E.members k = some cm → ExAlias.ctorPrefix.members k = some cm)
    (h : IndGroupAdmitted E 1 ExAlias.ctor) : Empty := by
  cases h with
  | family _ view _ hm _ =>
      have hc := view.hasClass
      rw [hm] at hc
      unfold ExAlias.ctor at hc
      cases hc
  | recursor a _ _ _ _ _ _ =>
      have ht := a.recursorType
      have hhead :
          spineHeadRef (piResult ExAlias.ctor.mtype) = some 0 := rfl
      rw [ht] at hhead
      rw [policyRecursor_not_const a.family a.minorTypes a.policy] at hhead
      cases hhead
  | constructor fam view _ _ _ _ h08 =>
      have ⟨href, hmem⟩ :=
        ExAlias.alias_only_inductive (hsub fam.present) fam.hasClass
      have hs := fam.storedType
      rw [hmem, ExAlias.familyMember] at hs
      have ⟨hcat, _⟩ := policyPi_eq_sort hs.symm
      have hpar : fam.parameters = [] := (List.append_eq_nil.mp hcat).1
      have hind : fam.indices = [] := (List.append_eq_nil.mp hcat).2
      have hfields : view.fields = [ExAlias.Alias] := by
        have hvp : view.parameters = [] := by
          have hlen := view.parameterCount
          rw [hpar] at hlen
          exact List.length_eq_zero.mp hlen
        have hvi : view.resultIndices = [] := by
          have hlen := view.indexCount
          rw [hind] at hlen
          exact List.length_eq_zero.mp hlen
        have hst := view.storedType
        unfold ExAlias.ctor at hst
        simp only [hvp, hvi, href, hmem, ExAlias.familyMember, ExAlias.U,
          ExAlias.Alias, policyFamilyLevels, List.range_zero, List.map_nil,
          policyParameterLocals, List.reverse_nil, List.append_nil, foldApps,
          policyPi, List.length_nil] at hst
        cases hfs : view.fields with
        | nil =>
            simp only [hfs, policyPi] at hst
            nomatch hst
        | cons A rest =>
            cases rest with
            | cons _ _ =>
                simp only [hfs, policyPi] at hst
                nomatch hst
            | nil =>
                simp only [hfs, policyPi] at hst
                injection hst with hA _
                have hA' : A = ExAlias.Alias := by
                  unfold ExAlias.Alias
                  exact hA.symm
                rw [hA']
      have hbad : False := by
        have hvp : view.parameters = [] := by
          have hlen := view.parameterCount
          rw [hpar] at hlen
          exact List.length_eq_zero.mp hlen
        rcases h08 ⟨0, by rw [hfields]; decide⟩ with ⟨shape, fuel, idxs, ha⟩
        simp only [hfields, List.getElem_cons_zero, href, hmem,
          ExAlias.familyMember, hpar, hind, Nat.add_zero, Nat.zero_add,
          List.length_nil] at ha
        have hTy := view.domainsTyped.hasType
          ⟨0, by rw [hfields, hvp]; decide⟩
        have hTyA : HasTy E fam.member.arity [] ExAlias.Alias
            (.sort (view.domainsTyped.levels ⟨0, by rw [hfields, hvp]; decide⟩)) := by
          simpa [hfields, hvp, policyPrefixContext, List.take_zero, List.map,
            List.append_nil] using hTy
        have ⟨m10, hmem10, _, _⟩ := hasTyConstInv hTyA rfl
        have hpre : ExAlias.ctorPrefix.members 10 = some m10 := hsub hmem10
        have halias : ExAlias.ctorPrefix.members 10 = some ExAlias.aliasMember := by
          have hs := ExAlias.prefix_bytes
          exact congrArg (fun p : _ × _ × _ => p.2.1) hs
        rw [halias] at hpre
        cases hpre
        exact FieldPermitted.not_refused ⟨fuel, idxs, ha⟩
          ⟨16, ExAlias.negative_at hmem10⟩
      exact False.elim hbad

def not_exAlias_ctor
    (h : IndGroupAdmitted ExAlias.ctorPrefix 1 ExAlias.ctor) : Empty :=
  not_exAlias_sub (fun {_ _} hk => hk) h

private theorem exAlias_not_admitted {E0 : ResolvedEnv}
    (_hfresh : E0.members 1 = none)
    (h : IndGroupAdmitted E0 1 ExAlias.ctor)
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E0.members k = some cm → ExAlias.ctorPrefix.members k = some cm) : False :=
  Empty.elim (not_exAlias_sub hsub h)

/-! ## 04 §1 accept: Nat's zero constructor sits in the slot after the family. -/

theorem no_open_unit {k c : Nat} (hl : k < c) (hr : c < k + 1) : False :=
  Nat.lt_irrefl k (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hr))

theorem natZero_contiguous :
    CtorContiguous (extendEnv emptyEnv 0 natFamMember) 1 natZeroMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (no_open_unit hl hr)
  · intro c h
    rcases h with ⟨cm, hm, hc, _⟩
    have hmem : (extendEnv emptyEnv 0 natFamMember).members c =
        if c = 0 then some natFamMember else none := rfl
    rw [hmem] at hm
    by_cases hz : c = 0
    · rw [if_pos hz] at hm
      cases hm
      unfold natFamMember at hc
      cases hc
    · rw [if_neg hz] at hm
      cases hm

/-! ## 04 §1 refusal: ValueAt at slot 11, constructors at 43 and 44. -/

open Rcic.Scm.SrcTV

theorem src_va_slots :
    (srcEnvV1.members 11, srcEnvV1.members 12, srcEnvV1.members 43,
      srcEnvV1.members 44) =
      (some mVA, some mBytesI, some mVaB0, some mVaB1) := rfl

theorem src_va_family : memberFamRef mVaB0 = some 11 := rfl

theorem not_srcVa_contiguous (h : CtorContiguous srcEnvV1 43 mVaB0) : False := by
  rcases h with ⟨f, hf, _, hfwd, _⟩
  have hf11 : f = 11 := Option.some.inj (hf.symm.trans src_va_family)
  subst hf11
  have h12 := hfwd 12 (by decide) (by decide)
  rcases h12 with ⟨cm, hm, hc, _⟩
  have hmem : srcEnvV1.members 12 = some mBytesI := by
    have hs := src_va_slots
    exact (congrArg (fun p => p.2.1) hs)
  rw [hmem] at hm
  cases hm
  unfold mBytesI mDef at hc
  cases hc

/-! ## Positive controls.

`posNat` is the fixture Nat group: two Type constructors, AnySort
recursor, one direct-recursive field. `PosFun` admits one
function-positive field (`Π (_ : Sort 0), F`). `PosProof` admits a
singleton Prop constructor whose only field is a proof field.
`PosProp` admits the two-constructor Prop group at PropOnly.
`PosList` admits the fixture ListU constructors and recursor after
the #6070 codomain raise (`Sort (succ (param 0))`); the original
codomain `param 0` is mixed, so it is not a 05 §5 profile. -/

def posNat : IndGroupAdmitted natEnvPrefix 3 natRecMemberU :=
  natGroupRecursor

namespace PosFun

def famMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def field : Expr Nat := .pi (.sort .zero) (.const 0 [])
def ctorMember : CheckedMember := ⟨.constructorM, 0, .pi field (.const 0 []), none⟩
def preEnv : ResolvedEnv := extendEnv emptyEnv 0 famMember

def family : PolicyFamilyView preEnv where
  ref := 0
  member := famMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fieldTy : HasTy preEnv 0 [] field (.sort (.succ .zero)) :=
  HasTy.conv (n := 0) [] field
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ .zero))
    (HasTy.pi (n := 0) [] (.sort .zero) (.succ .zero) (.const 0 []) (.succ .zero)
      (HasTy.sort (n := 0) [] .zero)
      (HasTy.const (n := 0) [.assumption (.sort .zero)] 0 [] famMember
        rfl rfl (fun _ h => nomatch h)))
    (Conv.sorts (n := 0) [] _ _ (eqN_imax_diag _))

def ctorView : PolicyConstructorView preEnv family ctorMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [field]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact fieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem univOk : FieldUniverseAdmitted ctorView :=
  fun _ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem analyzed :
    fieldAnalyze preEnv 12 0 0 0 0 0 field =
      .permitted (.recursive 1) [] := rfl

theorem fields : CtorFieldsPermitted ctorView := by
  intro j
  have ht := j.isLt
  simp only [ctorView, List.length_cons, List.length_nil] at ht
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 1, 12, [], analyzed⟩

theorem members (n : Nat) :
    preEnv.members n = if n = 0 then some famMember else none := rfl

theorem before : CtorBeforeRecursors preEnv ctorMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [members] at hm
  by_cases h0 : rr = 0
  · rw [if_pos h0] at hm
    cases hm
    unfold famMember at hk
    cases hk
  · rw [if_neg h0] at hm
    cases hm

theorem contig : CtorContiguous preEnv 1 ctorMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (no_open_unit hl hr)
  · intro c h
    rcases h with ⟨cm, hm, hc, _⟩
    rw [members] at hm
    by_cases h0 : c = 0
    · rw [if_pos h0] at hm
      cases hm
      unfold famMember at hc
      cases hc
    · rw [if_neg h0] at hm
      cases hm

def admitted : IndGroupAdmitted preEnv 1 ctorMember :=
  .constructor family ctorView rfl before contig univOk fields

end PosFun

namespace PosProof

/-- `Q : Prop`, `P : Prop`, `c : Q → P`. The field `Q` is a proof field. -/
def qMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def pMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def field : Expr Nat := .const 0 []
def ctorMember : CheckedMember :=
  ⟨.constructorM, 0, .pi field (.const 1 []), none⟩
def preEnv : ResolvedEnv :=
  extendEnv (extendEnv emptyEnv 0 qMember) 1 pMember

def family : PolicyFamilyView preEnv where
  ref := 1
  member := pMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fieldTy : HasTy preEnv 0 [] field (.sort .zero) :=
  HasTy.const [] 0 [] qMember rfl rfl (fun _ h => nomatch h)

def ctorView : PolicyConstructorView preEnv family ctorMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [field]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact fieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem univOk : FieldUniverseAdmitted ctorView :=
  fun _ => Or.inl uniformProp_zero

theorem analyzed :
    fieldAnalyze preEnv 8 1 0 0 0 0 field =
      .permitted .nonrecursive [] := rfl

theorem fields : CtorFieldsPermitted ctorView := by
  intro j
  have ht := j.isLt
  simp only [ctorView, List.length_cons, List.length_nil] at ht
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.nonrecursive, 8, [], analyzed⟩

theorem safe : ctorView.AllFieldsSafe := by
  intro j
  have ht := j.isLt
  simp only [ctorView, List.length_cons, List.length_nil] at ht
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inl uniformProp_zero

theorem anySort :
    EliminationSelection .zero 1 ctorView.AllFieldsSafe .anySort :=
  .singletonProp uniformProp_zero rfl safe

theorem members (n : Nat) :
    preEnv.members n =
      if n = 1 then some pMember
      else if n = 0 then some qMember
      else none := rfl

theorem before : CtorBeforeRecursors preEnv ctorMember := by
  refine ⟨1, rfl, ?_⟩
  intro rr rm hm hk _
  rw [members] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    unfold pMember at hk
    cases hk
  · rw [if_neg h1] at hm
    by_cases h0 : rr = 0
    · rw [if_pos h0] at hm
      cases hm
      unfold qMember at hk
      cases hk
    · rw [if_neg h0] at hm
      cases hm

theorem contig : CtorContiguous preEnv 2 ctorMember := by
  refine ⟨1, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (no_open_unit hl hr)
  · intro c h
    rcases h with ⟨cm, hm, hc, _⟩
    rw [members] at hm
    by_cases h1 : c = 1
    · rw [if_pos h1] at hm
      cases hm
      unfold pMember at hc
      cases hc
    · rw [if_neg h1] at hm
      by_cases h0 : c = 0
      · rw [if_pos h0] at hm
        cases hm
        unfold qMember at hc
        cases hc
      · rw [if_neg h0] at hm
        cases hm

def admitted : IndGroupAdmitted preEnv 2 ctorMember :=
  .constructor family ctorView rfl before contig univOk fields

end PosProof

/-! ## PosProp : two Prop constructors, PropOnly recursor.

Same family bytes as `ExBool` (slots 0–2). The refused recursor stores a
motive in `Sort 1`. 05 §10's multi-constructor Prop rule stores the
motive in `Sort 0`, and both ι equations are the minor premises. -/

namespace PosProp

open ExBool

def motiveType : Expr Nat := .pi boolP (.sort .zero)

def recType : Expr Nat :=
  .pi motiveType
    (.pi boolMinorTrueType
      (.pi boolMinorFalseType
        (.pi boolP (.app (.bvar 3) (.bvar 0)))))

def recMember : CheckedMember := ⟨.recursorM, 0, recType, none⟩

def family : PolicyFamilyView boolPrefix where
  ref := 0
  member := boolFamMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def ctorTrue : PolicyConstructorView boolPrefix family boolTrueMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

def ctorFalse : PolicyConstructorView boolPrefix family boolFalseMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

def group : RecursorEliminationAdmitted boolPrefix 3 recMember where
  family := family
  constructors := [boolTrueMember, boolFalseMember]
  constructorViews
    | ⟨0, _⟩ => ctorTrue
    | ⟨1, _⟩ => ctorFalse
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [boolMinorTrueType, boolMinorFalseType]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp uniformProp_zero (by decide)
  recursorArity := rfl
  recursorType := rfl

theorem census : CtorCensus boolPrefix 0 3 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [boolPrefix_members] at hc
    by_cases h2 : c = 2
    · rw [if_pos h2] at hc
      cases hc
      exact ⟨by omega, by omega⟩
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hc
        cases hc
        exact ⟨by omega, by omega⟩
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          rw [boolFamMember] at hk
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc
  · intro h
    have hc : c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨boolTrueMember, by rw [boolPrefix_members]; rfl, rfl, rfl⟩
    · exact ⟨boolFalseMember, by rw [boolPrefix_members]; rfl, rfl, rfl⟩

theorem minorMatch : MinorPremisesMatch group := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => exact ⟨[], 0, rfl, rfl⟩

def shapes : Fin group.constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []

def eqEnv : ResolvedEnv := extendEnv boolPrefix 3 recMember

def iotaCtx : LCtx :=
  [.assumption boolMinorFalseType, .assumption boolMinorTrueType,
    .assumption motiveType]

def lhsTrue : Expr Nat := .app (.bvar 2) (.const 1 [])
def lhsFalse : Expr Nat := .app (.bvar 2) (.const 2 [])

def iotaTrueTy : HasTy eqEnv 0 iotaCtx (.bvar 1) lhsTrue :=
  HasTy.bvar iotaCtx 1 lhsTrue rfl

def iotaFalseTy : HasTy eqEnv 0 iotaCtx (.bvar 0) lhsFalse :=
  HasTy.bvar iotaCtx 0 lhsFalse rfl

def iotaTrue : IotaEquationTyped group ⟨0, by decide⟩ 0 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact iotaTrueTy

def iotaFalse : IotaEquationTyped group ⟨1, by decide⟩ 0 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact iotaFalseTy

def iotaClause : IotaDescriptorClause boolPrefix group where
  signatureOnly := rfl
  shapesAt := shapes
  fuelAt := fun _ => 0
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => iotaTrue
    | ⟨1, _⟩ => iotaFalse

def admitted : IndGroupAdmitted boolPrefix 3 recMember :=
  .recursor group rfl census
    (fun i =>
      match i with
      | ⟨0, _⟩ => fun j => j.elim0
      | ⟨1, _⟩ => fun j => j.elim0)
    (fun i =>
      match i with
      | ⟨0, _⟩ => fun j => j.elim0
      | ⟨1, _⟩ => fun j => j.elim0)
    minorMatch iotaClause

end PosProp

/-! ## PosList : fixture ListU, codomain raised to a uniform Type.

`listUNilMember` / `listUConsMember` / `listURecMember` are the fixture
bytes (`const` heads 8 / 9 / 10). Only the family declaration changes:
`listUFamType` ends in `Sort (param 0)`, and `param 0` is mixed, so
05 §5 has no profile. #6070 stores `Sort (succ (param 0))`, which is
uniform Type. Slots stay 8–11. The root is `natEnvPrefix`, not `natEnv`: slot 3 is
`natRecMember`, whose motive is a fixed `Sort 1`, and 05 §11 does not
admit it. Constructor and recursor expressions are not retyped. -/

namespace PosList

theorem param_mixed (i : Nat) : MixedUniverse (.param i) := by
  constructor
  · intro h
    have := h (fun _ => 1)
    simp [evalTotal] at this
  · intro h
    have := h (fun _ => 0)
    simp [evalTotal] at this

theorem uniformType_succ_param (i : Nat) : UniformType (.succ (.param i)) := by
  intro _
  simp only [evalTotal]
  omega

theorem leN_param_succ (i : Nat) : leN (.param i) (.succ (.param i)) := by
  intro ρ x y hx hy
  simp only [eval] at hx hy
  cases hρ : ρ i with
  | none => simp [hρ] at hx
  | some k =>
      simp only [hρ, Option.map] at hx hy
      have hx' : k = x := by injection hx
      have hy' : k + 1 = y := by injection hy
      omega

def raisedType : Expr Nat :=
  .pi (.sort (.param 0)) (.sort (.succ (.param 0)))

def raisedFam : CheckedMember := ⟨.inductiveM, 1, raisedType, none⟩

def paramSort : Expr Nat := .sort (.param 0)
def hdField : Expr Nat := .bvar 0
def tlField : Expr Nat := .app (.const 8 [.param 0]) (.bvar 1)

theorem nil_bytes : listUNilMember.mtype = listUNilType := rfl
theorem cons_bytes : listUConsMember.mtype = listUConsType := rfl
theorem rec_bytes : listURecMember.mtype = listURecType := rfl

def listPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv natEnvPrefix 8 raisedFam) 9 listUNilMember)
    10 listUConsMember

def family : PolicyFamilyView listPrefix where
  ref := 8
  member := raisedFam
  present := rfl
  hasClass := rfl
  parameters := [paramSort]
  indices := []
  resultLevel := .succ (.param 0)
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.param 0)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact HasTy.sort (n := 1) [] (.param 0)
  }

def nilView : PolicyConstructorView listPrefix family listUNilMember where
  hasClass := rfl
  arity := rfl
  parameters := [paramSort]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.param 0)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact HasTy.sort (n := 1) [] (.param 0)
  }
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    simp only [hi, policyPrefixContext]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

def consCtx0 : LCtx := [.assumption paramSort]
def consCtx1 : LCtx := [.assumption hdField, .assumption paramSort]

def consHdTy : HasTy listPrefix 1 consCtx0 hdField (.sort (.param 0)) :=
  HasTy.bvar (n := 1) consCtx0 0 (.sort (.param 0)) rfl

def consFamTy (Γ : LCtx) :
    HasTy listPrefix 1 Γ (.const 8 [.param 0]) raisedType :=
  HasTy.const (n := 1) Γ 8 [.param 0] raisedFam rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by
      simp only [List.mem_singleton] at hl
      exact hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def consTlTy : HasTy listPrefix 1 consCtx1 tlField (.sort (.succ (.param 0))) :=
  HasTy.app (n := 1) consCtx1 (.const 8 [.param 0]) (.bvar 1)
    paramSort (.sort (.succ (.param 0)))
    (consFamTy consCtx1)
    (HasTy.bvar (n := 1) consCtx1 1 paramSort rfl)

def consView : PolicyConstructorView listPrefix family listUConsMember where
  hasClass := rfl
  arity := rfl
  parameters := [paramSort]
  fields := [hdField, tlField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ (.param 0)
      | ⟨1, _⟩ => .param 0
      | ⟨2, _⟩ => .succ (.param 0)
    bounded := fun j => by
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
    hasType := fun j => by
      match j with
      | ⟨0, _⟩ =>
          simp only [policyPrefixContext]
          exact HasTy.sort (n := 1) [] (.param 0)
      | ⟨1, _⟩ =>
          simp only [policyPrefixContext]
          exact consHdTy
      | ⟨2, _⟩ =>
          simp only [policyPrefixContext]
          exact consTlTy
  }
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    simp only [hi, policyPrefixContext]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

def minorNil : Expr Nat :=
  .app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))

def minorCons : Expr Nat :=
  .pi (.bvar 2)
    (.pi (.app (.const 8 [.param 0]) (.bvar 3))
      (.pi (.app (.bvar 3) (.bvar 0))
        (.app (.bvar 4)
          (.app (.app (.app (.const 10 [.param 0]) (.bvar 5))
              (.bvar 2)) (.bvar 1)))))

def group : RecursorEliminationAdmitted listPrefix 11 listURecMember where
  family := family
  constructors := [listUNilMember, listUConsMember]
  constructorViews
    | ⟨0, _⟩ => nilView
    | ⟨1, _⟩ => consView
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [minorNil, minorCons]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType (uniformType_succ_param 0)
  recursorArity := rfl
  recursorType := rfl

theorem prefixMem (n : Nat) :
    listPrefix.members n =
      if n = 10 then some listUConsMember
      else if n = 9 then some listUNilMember
      else if n = 8 then some raisedFam
      else natEnvPrefix.members n := rfl

theorem natZeroFamily : memberFamRef natZeroMember = some 0 := rfl
theorem natSuccFamily : memberFamRef natSuccMember = some 0 := rfl
theorem nilFamily : memberFamRef listUNilMember = some 8 := rfl
theorem consFamily : memberFamRef listUConsMember = some 8 := rfl

theorem census : CtorCensus listPrefix 8 11 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, hf⟩
    rw [prefixMem] at hc
    by_cases h10 : c = 10
    · rw [if_pos h10] at hc
      cases hc
      exact ⟨by omega, by omega⟩
    · by_cases h9 : c = 9
      · rw [if_neg h10, if_pos h9] at hc
        cases hc
        exact ⟨by omega, by omega⟩
      · by_cases h8 : c = 8
        · rw [if_neg h10, if_neg h9, if_pos h8] at hc
          cases hc
          rw [raisedFam] at hk
          cases hk
        · rw [if_neg h10, if_neg h9, if_neg h8] at hc
          rw [natPrefixMem] at hc
          by_cases h2 : c = 2
          · rw [if_pos h2] at hc
            cases hc
            rw [natSuccFamily] at hf
            injection hf with h
            omega
          · by_cases h1 : c = 1
            · rw [if_neg h2, if_pos h1] at hc
              cases hc
              rw [natZeroFamily] at hf
              injection hf with h
              omega
            · by_cases h0 : c = 0
              · rw [if_neg h2, if_neg h1, if_pos h0] at hc
                cases hc
                rw [natFamMember] at hk
                cases hk
              · rw [if_neg h2, if_neg h1, if_neg h0] at hc
                cases hc
  · intro h
    have hc : c = 9 ∨ c = 10 := by omega
    rcases hc with rfl | rfl
    · exact ⟨listUNilMember, by rw [prefixMem]; rfl, rfl, nilFamily⟩
    · exact ⟨listUConsMember, by rw [prefixMem]; rfl, rfl, consFamily⟩

theorem hdShape :
    fieldAnalyze listPrefix 8 8 1 1 0 1 hdField =
      .permitted .nonrecursive [] := rfl

theorem tlShape :
    fieldAnalyze listPrefix 8 8 1 1 0 2 tlField =
      .permitted (.recursive 0) [] := rfl

theorem minorMatch : MinorPremisesMatch group := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => exact ⟨[.nonrecursive, .recursive 0], 8, rfl, rfl⟩

def shapes : Fin group.constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.nonrecursive, .recursive 0]

def eqEnv : ResolvedEnv := extendEnv listPrefix 11 listURecMember

def domA : Expr Nat := paramSort
def domP : Expr Nat :=
  .pi (.app (.const 8 [.param 0]) (.bvar 0)) (.sort (.param 1))
def domMn : Expr Nat := minorNil
def domMc : Expr Nat := minorCons
def domHd : Expr Nat := .bvar 3
def domTl : Expr Nat := .app (.const 8 [.param 0]) (.bvar 4)

def nilCtx : LCtx :=
  [.assumption domMc, .assumption domMn, .assumption domP, .assumption domA]

def consCtx : LCtx :=
  [.assumption domTl, .assumption domHd, .assumption domMc, .assumption domMn,
    .assumption domP, .assumption domA]

def nilLhs : Expr Nat :=
  .app (.bvar 2) (.app (.const 9 [.param 0]) (.bvar 3))

def consLhs : Expr Nat :=
  .app (.bvar 4)
    (foldApps (.const 10 [.param 0]) [.bvar 5, .bvar 1, .bvar 0])

def recHead : Expr Nat := .const 11 [.param 0, .param 1]

def recApp : Expr Nat :=
  foldApps recHead [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]

def consRhs : Expr Nat :=
  .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) recApp

private def happ {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTy eqEnv 2 Γ f (.pi A B))
    (ha : HasTy eqEnv 2 Γ a A) :
    HasTy eqEnv 2 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app (n := 2) Γ f a A B hf ha

def nilIotaTy : HasTy eqEnv 2 nilCtx (.bvar 1) nilLhs :=
  HasTy.bvar (n := 2) nilCtx 1 nilLhs rfl

def consIotaTy : HasTy eqEnv 2 consCtx consRhs consLhs := by
  have hmc : HasTy eqEnv 2 consCtx (.bvar 2) (lift 0 3 domMc) :=
    HasTy.bvar (n := 2) consCtx 2 _ rfl
  have hhd : HasTy eqEnv 2 consCtx (.bvar 1) (lift 0 2 domHd) :=
    HasTy.bvar (n := 2) consCtx 1 _ rfl
  have htl : HasTy eqEnv 2 consCtx (.bvar 0) (lift 0 1 domTl) :=
    HasTy.bvar (n := 2) consCtx 0 _ rfl
  have h1 := happ hmc hhd
  have h2 := happ h1 htl
  have hA : HasTy eqEnv 2 consCtx (.bvar 5) (lift 0 6 domA) :=
    HasTy.bvar (n := 2) consCtx 5 _ rfl
  have hP : HasTy eqEnv 2 consCtx (.bvar 4) (lift 0 5 domP) :=
    HasTy.bvar (n := 2) consCtx 4 _ rfl
  have hMn : HasTy eqEnv 2 consCtx (.bvar 3) (lift 0 4 domMn) :=
    HasTy.bvar (n := 2) consCtx 3 _ rfl
  have hMc : HasTy eqEnv 2 consCtx (.bvar 2) (lift 0 3 domMc) :=
    HasTy.bvar (n := 2) consCtx 2 _ rfl
  have hRec0 : HasTy eqEnv 2 consCtx recHead
      (instantiateLevels [.param 0, .param 1] listURecType) :=
    HasTy.const (n := 2) consCtx 11 [.param 0, .param 1] listURecMember
      rfl rfl (by
        intro l hl
        simp only [List.mem_cons, List.mem_singleton] at hl
        rcases hl with rfl | hl
        · exact ⟨0, Or.inl rfl⟩
        · rcases hl with rfl | hl
          · exact ⟨0, Or.inl rfl⟩
          · cases hl)
  have hRec1 := happ hRec0 hA
  have hRec2 := happ hRec1 hP
  have hRec3 := happ hRec2 hMn
  have hRec4 := happ hRec3 hMc
  have hRec5 := happ hRec4 htl
  have h3 := happ h2 hRec5
  exact h3

def nilIota : IotaEquationTyped group ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact nilIotaTy

def consIota : IotaEquationTyped group ⟨1, by decide⟩ 8
    [.nonrecursive, .recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact consIotaTy

def iotaClause : IotaDescriptorClause listPrefix group where
  signatureOnly := rfl
  shapesAt := shapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => nilIota
    | ⟨1, _⟩ => consIota

theorem nilUniverse : FieldUniverseAdmitted nilView :=
  fun j => j.elim0

theorem consUniverse : FieldUniverseAdmitted consView := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨uniformType_succ_param 0, leN_param_succ 0⟩
  | ⟨1, _⟩ => exact Or.inr ⟨uniformType_succ_param 0, leN_refl _⟩

theorem nilFields : CtorFieldsPermitted nilView :=
  fun j => j.elim0

theorem consFields : CtorFieldsPermitted consView := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], hdShape⟩
  | ⟨1, _⟩ => exact ⟨.recursive 0, 8, [], tlShape⟩

def admitted : IndGroupAdmitted listPrefix 11 listURecMember :=
  .recursor group rfl census
    (fun i =>
      match i with
      | ⟨0, _⟩ => nilUniverse
      | ⟨1, _⟩ => consUniverse)
    (fun i =>
      match i with
      | ⟨0, _⟩ => nilFields
      | ⟨1, _⟩ => consFields)
    minorMatch iotaClause

end PosList

/-! ## `EnvWf` of the AnySort Nat group.

The prefix is `natEnvWfPrefixAt`. The recursor step is `natGroupRecursor`,
not the index-admission bundle: 05 §§6–14 are that inhabitant.
`natRecMember` (fixed `Sort 1`, arity 0) is not this fact. -/

def natEnvUWfAt (n : Nat) : EnvWf natEnvU n :=
  .indMember _ 3 natRecMemberU (natEnvWfPrefixAt n) rfl (Or.inr (Or.inr rfl))
    rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
    (fun _ => natURecAdmitted) natGroupRecursor

theorem pin_envWf_natU : Nonempty (EnvWf natEnvU 1) :=
  ⟨natEnvUWfAt 1⟩

theorem pin_envWf_natU_reduces_to_idxAdm :
    RecursorGroupIdxAdmitted natEnvPrefix 3 natRecMemberU →
      Nonempty (EnvWf natEnvU 1) :=
  fun _ => ⟨natEnvUWfAt 1⟩

/-! ## Positive `EnvWf`.

Each control's `IndGroupAdmitted` inhabitant is the `hadm` premise.
Families are inductive, so `harity` is `rfl`; constructors are not. -/

def posFunFamAdmitted : IndGroupAdmitted emptyEnv 0 PosFun.famMember :=
  .family rfl PosFun.family rfl rfl (Or.inr uniformType_succ_zero)

def posFunFamWf (n : Nat) : EnvWf PosFun.preEnv n :=
  .indMember _ 0 PosFun.famMember (.empty n) rfl (Or.inl rfl) rfl
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (fun h => absurd h (by decide)) posFunFamAdmitted

def posFunEnv : ResolvedEnv := extendEnv PosFun.preEnv 1 PosFun.ctorMember

def posFunWf (n : Nat) : EnvWf posFunEnv n :=
  .indMember _ 1 PosFun.ctorMember (posFunFamWf n) rfl (Or.inr (Or.inl rfl))
    rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) PosFun.admitted

theorem pin_envWf_posFun : Nonempty (EnvWf posFunEnv 1) := ⟨posFunWf 1⟩

def posProofQView : PolicyFamilyView (extendEnv emptyEnv 0 PosProof.qMember) where
  ref := 0
  member := PosProof.qMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def posProofQAdmitted : IndGroupAdmitted emptyEnv 0 PosProof.qMember :=
  .family rfl posProofQView rfl rfl (Or.inl uniformProp_zero)

def posProofPAdmitted :
    IndGroupAdmitted (extendEnv emptyEnv 0 PosProof.qMember) 1 PosProof.pMember :=
  .family rfl PosProof.family rfl rfl (Or.inl uniformProp_zero)

def posProofQWf (n : Nat) : EnvWf (extendEnv emptyEnv 0 PosProof.qMember) n :=
  .indMember _ 0 PosProof.qMember (.empty n) rfl (Or.inl rfl) rfl
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (fun h => absurd h (by decide)) posProofQAdmitted

def posProofPWf (n : Nat) : EnvWf PosProof.preEnv n :=
  .indMember _ 1 PosProof.pMember (posProofQWf n) rfl (Or.inl rfl) rfl
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (fun h => absurd h (by decide)) posProofPAdmitted

def posProofEnv : ResolvedEnv := extendEnv PosProof.preEnv 2 PosProof.ctorMember

def posProofWf (n : Nat) : EnvWf posProofEnv n :=
  .indMember _ 2 PosProof.ctorMember (posProofPWf n) rfl (Or.inr (Or.inl rfl))
    rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) PosProof.admitted

theorem pin_envWf_posProof : Nonempty (EnvWf posProofEnv 1) := ⟨posProofWf 1⟩

/-! PropOnly Bool. The prefix is the original `ExBool` slots 0–2.
The recursor is `PosProp.recMember` (`Sort 0` motive), not `boolRecMember`. -/

def posPropFamOnly : ResolvedEnv := extendEnv emptyEnv 0 ExBool.boolFamMember

def posPropFamTrue : ResolvedEnv :=
  extendEnv posPropFamOnly 1 ExBool.boolTrueMember

def posPropFamView (E : ResolvedEnv) (h : E.members 0 = some ExBool.boolFamMember) :
    PolicyFamilyView E where
  ref := 0
  member := ExBool.boolFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def posPropTrueView (E : ResolvedEnv) (h : E.members 0 = some ExBool.boolFamMember) :
    PolicyConstructorView E (posPropFamView E h) ExBool.boolTrueMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

def posPropFalseView (E : ResolvedEnv) (h : E.members 0 = some ExBool.boolFamMember) :
    PolicyConstructorView E (posPropFamView E h) ExBool.boolFalseMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

theorem posPropFamOnly_members (c : Nat) :
    posPropFamOnly.members c =
      if c = 0 then some ExBool.boolFamMember else none := rfl

theorem posPropFamTrue_members (c : Nat) :
    posPropFamTrue.members c =
      if c = 1 then some ExBool.boolTrueMember
      else if c = 0 then some ExBool.boolFamMember
      else none := rfl

theorem posPropTrueBefore : CtorBeforeRecursors posPropFamOnly ExBool.boolTrueMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [posPropFamOnly_members] at hm
  by_cases h0 : rr = 0
  · rw [if_pos h0] at hm
    cases hm
    unfold ExBool.boolFamMember at hk
    cases hk
  · rw [if_neg h0] at hm
    cases hm

theorem posPropTrueContig : CtorContiguous posPropFamOnly 1 ExBool.boolTrueMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (no_open_unit hl hr)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [posPropFamOnly_members] at hm
    by_cases h0 : c = 0
    · rw [if_pos h0] at hm
      cases hm
      unfold ExBool.boolFamMember at hc
      cases hc
    · rw [if_neg h0] at hm
      cases hm

theorem posPropFalseBefore :
    CtorBeforeRecursors posPropFamTrue ExBool.boolFalseMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [posPropFamTrue_members] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    unfold ExBool.boolTrueMember at hk
    cases hk
  · by_cases h0 : rr = 0
    · rw [if_neg h1, if_pos h0] at hm
      cases hm
      unfold ExBool.boolFamMember at hk
      cases hk
    · rw [if_neg h1, if_neg h0] at hm
      cases hm

theorem posPropFalseContig : CtorContiguous posPropFamTrue 2 ExBool.boolFalseMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 := by omega
    subst hc
    exact ⟨ExBool.boolTrueMember, by rw [posPropFamTrue_members]; rfl, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, href⟩
    rw [posPropFamTrue_members] at hm
    by_cases h1 : c = 1
    · subst h1
      exact ⟨by decide, by decide⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hm
        cases hm
        unfold ExBool.boolFamMember at hc
        cases hc
      · rw [if_neg h1, if_neg h0] at hm
        cases hm

def posPropFamAdmitted : IndGroupAdmitted emptyEnv 0 ExBool.boolFamMember :=
  .family rfl (posPropFamView posPropFamOnly rfl) rfl rfl (Or.inl uniformProp_zero)

def posPropTrueAdmitted :
    IndGroupAdmitted posPropFamOnly 1 ExBool.boolTrueMember :=
  .constructor (posPropFamView posPropFamOnly rfl)
    (posPropTrueView posPropFamOnly rfl) rfl posPropTrueBefore posPropTrueContig
    (fun j => j.elim0) (fun j => j.elim0)

def posPropFalseAdmitted :
    IndGroupAdmitted posPropFamTrue 2 ExBool.boolFalseMember :=
  .constructor (posPropFamView posPropFamTrue rfl)
    (posPropFalseView posPropFamTrue rfl) rfl posPropFalseBefore posPropFalseContig
    (fun j => j.elim0) (fun j => j.elim0)

def posPropFamWf (n : Nat) : EnvWf posPropFamOnly n :=
  .indMember _ 0 ExBool.boolFamMember (.empty n) rfl (Or.inl rfl) rfl
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (fun h => absurd h (by decide)) posPropFamAdmitted

def posPropTrueWf (n : Nat) : EnvWf posPropFamTrue n :=
  .indMember _ 1 ExBool.boolTrueMember (posPropFamWf n) rfl (Or.inr (Or.inl rfl))
    rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) posPropTrueAdmitted

def posPropPrefixWf (n : Nat) : EnvWf ExBool.boolPrefix n :=
  .indMember _ 2 ExBool.boolFalseMember (posPropTrueWf n) rfl (Or.inr (Or.inl rfl))
    rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) posPropFalseAdmitted

def posPropRecIdx :
    RecursorGroupIdxAdmitted ExBool.boolPrefix 3 PosProp.recMember :=
  .ofAdmitted rfl

def posPropEnv : ResolvedEnv := extendEnv ExBool.boolPrefix 3 PosProp.recMember

def posPropWf (n : Nat) : EnvWf posPropEnv n :=
  .indMember _ 3 PosProp.recMember (posPropPrefixWf n) rfl (Or.inr (Or.inr rfl))
    rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
    (fun _ => posPropRecIdx) PosProp.admitted

theorem pin_envWf_posProp : Nonempty (EnvWf posPropEnv 1) := ⟨posPropWf 1⟩

/-! ## ListU `EnvWf`, rooted at `natEnvPrefix`.

`PosList.admitted` is the recursor step. The family and constructors are
added one member at a time over that same root, so the prefix does not
contain `natRecMember`. -/

def posListFamOnly : ResolvedEnv :=
  extendEnv natEnvPrefix 8 PosList.raisedFam

def posListFamNil : ResolvedEnv :=
  extendEnv posListFamOnly 9 listUNilMember

def posListFamView (E : ResolvedEnv) (h : E.members 8 = some PosList.raisedFam) :
    PolicyFamilyView E where
  ref := 8
  member := PosList.raisedFam
  present := h
  hasClass := rfl
  parameters := [PosList.paramSort]
  indices := []
  resultLevel := .succ (.param 0)
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.param 0)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact HasTy.sort (n := 1) [] (.param 0)
  }

def posListNilView (E : ResolvedEnv) (h : E.members 8 = some PosList.raisedFam) :
    PolicyConstructorView E (posListFamView E h) listUNilMember where
  hasClass := rfl
  arity := rfl
  parameters := [PosList.paramSort]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.param 0)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact HasTy.sort (n := 1) [] (.param 0)
  }
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    simp only [hi, policyPrefixContext]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

def posListConsCtx0 : LCtx := [.assumption PosList.paramSort]
def posListConsCtx1 : LCtx :=
  [.assumption PosList.hdField, .assumption PosList.paramSort]

def posListConsHdTy :
    HasTy posListFamNil 1 posListConsCtx0 PosList.hdField (.sort (.param 0)) :=
  HasTy.bvar (n := 1) posListConsCtx0 0 (.sort (.param 0)) rfl

def posListConsFamTy (Γ : LCtx) :
    HasTy posListFamNil 1 Γ (.const 8 [.param 0]) PosList.raisedType :=
  HasTy.const (n := 1) Γ 8 [.param 0] PosList.raisedFam rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by
      simp only [List.mem_singleton] at hl
      exact hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def posListConsTlTy :
    HasTy posListFamNil 1 posListConsCtx1 PosList.tlField
      (.sort (.succ (.param 0))) :=
  HasTy.app (n := 1) posListConsCtx1 (.const 8 [.param 0]) (.bvar 1)
    PosList.paramSort (.sort (.succ (.param 0)))
    (posListConsFamTy posListConsCtx1)
    (HasTy.bvar (n := 1) posListConsCtx1 1 PosList.paramSort rfl)

def posListConsView :
    PolicyConstructorView posListFamNil (posListFamView posListFamNil rfl)
      listUConsMember where
  hasClass := rfl
  arity := rfl
  parameters := [PosList.paramSort]
  fields := [PosList.hdField, PosList.tlField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ (.param 0)
      | ⟨1, _⟩ => .param 0
      | ⟨2, _⟩ => .succ (.param 0)
    bounded := fun j => by
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
    hasType := fun j => by
      match j with
      | ⟨0, _⟩ =>
          simp only [policyPrefixContext]
          exact HasTy.sort (n := 1) [] (.param 0)
      | ⟨1, _⟩ =>
          simp only [policyPrefixContext]
          exact posListConsHdTy
      | ⟨2, _⟩ =>
          simp only [policyPrefixContext]
          exact posListConsTlTy
  }
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    simp only [hi, policyPrefixContext]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

theorem posListFamOnly_members (c : Nat) :
    posListFamOnly.members c =
      if c = 8 then some PosList.raisedFam else natEnvPrefix.members c := rfl

theorem posListFamNil_members (c : Nat) :
    posListFamNil.members c =
      if c = 9 then some listUNilMember
      else if c = 8 then some PosList.raisedFam
      else natEnvPrefix.members c := rfl

theorem posListNilBefore : CtorBeforeRecursors posListFamOnly listUNilMember := by
  refine ⟨8, rfl, ?_⟩
  intro rr rm hm hk _
  rw [posListFamOnly_members] at hm
  by_cases h8 : rr = 8
  · rw [if_pos h8] at hm
    cases hm
    unfold PosList.raisedFam at hk
    cases hk
  · rw [if_neg h8] at hm
    rw [natPrefixMem] at hm
    by_cases h2 : rr = 2
    · rw [if_pos h2] at hm
      cases hm
      unfold natSuccMember at hk
      cases hk
    · by_cases h1 : rr = 1
      · rw [if_neg h2, if_pos h1] at hm
        cases hm
        unfold natZeroMember at hk
        cases hk
      · by_cases h0 : rr = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hm
          cases hm
          unfold natFamMember at hk
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hm
          cases hm

theorem posListNilContig : CtorContiguous posListFamOnly 9 listUNilMember := by
  refine ⟨8, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (no_open_unit hl hr)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, hf⟩
    rw [posListFamOnly_members] at hm
    by_cases h8 : c = 8
    · rw [if_pos h8] at hm
      cases hm
      unfold PosList.raisedFam at hc
      cases hc
    · rw [if_neg h8] at hm
      rw [natPrefixMem] at hm
      by_cases h2 : c = 2
      · rw [if_pos h2] at hm
        cases hm
        rw [PosList.natSuccFamily] at hf
        injection hf with h
        omega
      · by_cases h1 : c = 1
        · rw [if_neg h2, if_pos h1] at hm
          cases hm
          rw [PosList.natZeroFamily] at hf
          injection hf with h
          omega
        · by_cases h0 : c = 0
          · rw [if_neg h2, if_neg h1, if_pos h0] at hm
            cases hm
            unfold natFamMember at hc
            cases hc
          · rw [if_neg h2, if_neg h1, if_neg h0] at hm
            cases hm

theorem posListConsBefore : CtorBeforeRecursors posListFamNil listUConsMember := by
  refine ⟨8, rfl, ?_⟩
  intro rr rm hm hk _
  rw [posListFamNil_members] at hm
  by_cases h9 : rr = 9
  · rw [if_pos h9] at hm
    cases hm
    unfold listUNilMember at hk
    cases hk
  · by_cases h8 : rr = 8
    · rw [if_neg h9, if_pos h8] at hm
      cases hm
      unfold PosList.raisedFam at hk
      cases hk
    · rw [if_neg h9, if_neg h8] at hm
      rw [natPrefixMem] at hm
      by_cases h2 : rr = 2
      · rw [if_pos h2] at hm
        cases hm
        unfold natSuccMember at hk
        cases hk
      · by_cases h1 : rr = 1
        · rw [if_neg h2, if_pos h1] at hm
          cases hm
          unfold natZeroMember at hk
          cases hk
        · by_cases h0 : rr = 0
          · rw [if_neg h2, if_neg h1, if_pos h0] at hm
            cases hm
            unfold natFamMember at hk
            cases hk
          · rw [if_neg h2, if_neg h1, if_neg h0] at hm
            cases hm

theorem posListConsContig : CtorContiguous posListFamNil 10 listUConsMember := by
  refine ⟨8, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 9 := by omega
    subst hc
    exact ⟨listUNilMember, by rw [posListFamNil_members]; rfl, rfl, PosList.nilFamily⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, hf⟩
    rw [posListFamNil_members] at hm
    by_cases h9 : c = 9
    · subst h9
      exact ⟨by decide, by decide⟩
    · by_cases h8 : c = 8
      · rw [if_neg h9, if_pos h8] at hm
        cases hm
        unfold PosList.raisedFam at hc
        cases hc
      · rw [if_neg h9, if_neg h8] at hm
        rw [natPrefixMem] at hm
        by_cases h2 : c = 2
        · rw [if_pos h2] at hm
          cases hm
          rw [PosList.natSuccFamily] at hf
          injection hf with h
          omega
        · by_cases h1 : c = 1
          · rw [if_neg h2, if_pos h1] at hm
            cases hm
            rw [PosList.natZeroFamily] at hf
            injection hf with h
            omega
          · by_cases h0 : c = 0
            · rw [if_neg h2, if_neg h1, if_pos h0] at hm
              cases hm
              unfold natFamMember at hc
              cases hc
            · rw [if_neg h2, if_neg h1, if_neg h0] at hm
              cases hm

theorem posListNilUniv :
    FieldUniverseAdmitted (posListNilView posListFamOnly rfl) :=
  fun j => j.elim0

theorem posListNilFields :
    CtorFieldsPermitted (posListNilView posListFamOnly rfl) :=
  fun j => j.elim0

theorem posListHdShape :
    fieldAnalyze posListFamNil 8 8 1 1 0 1 PosList.hdField =
      .permitted .nonrecursive [] := rfl

theorem posListTlShape :
    fieldAnalyze posListFamNil 8 8 1 1 0 2 PosList.tlField =
      .permitted (.recursive 0) [] := rfl

theorem posListConsUniv : FieldUniverseAdmitted posListConsView := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨PosList.uniformType_succ_param 0, PosList.leN_param_succ 0⟩
  | ⟨1, _⟩ => exact Or.inr ⟨PosList.uniformType_succ_param 0, leN_refl _⟩

theorem posListConsFields : CtorFieldsPermitted posListConsView := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], posListHdShape⟩
  | ⟨1, _⟩ => exact ⟨.recursive 0, 8, [], posListTlShape⟩

def posListFamAdmitted : IndGroupAdmitted natEnvPrefix 8 PosList.raisedFam :=
  .family rfl (posListFamView posListFamOnly rfl) rfl rfl
    (Or.inr (PosList.uniformType_succ_param 0))

def posListNilAdmitted : IndGroupAdmitted posListFamOnly 9 listUNilMember :=
  .constructor (posListFamView posListFamOnly rfl)
    (posListNilView posListFamOnly rfl) rfl posListNilBefore posListNilContig
    posListNilUniv posListNilFields

def posListConsAdmitted : IndGroupAdmitted posListFamNil 10 listUConsMember :=
  .constructor (posListFamView posListFamNil rfl) posListConsView rfl
    posListConsBefore posListConsContig posListConsUniv posListConsFields

def posListFamWf (n : Nat) : EnvWf posListFamOnly n :=
  .indMember _ 8 PosList.raisedFam (natEnvWfPrefixAt n) rfl (Or.inl rfl) rfl
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (fun h => absurd h (by decide)) posListFamAdmitted

def posListNilWf (n : Nat) : EnvWf posListFamNil n :=
  .indMember _ 9 listUNilMember (posListFamWf n) rfl (Or.inr (Or.inl rfl)) rfl
    (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) posListNilAdmitted

def posListPrefixWf (n : Nat) : EnvWf PosList.listPrefix n :=
  .indMember _ 10 listUConsMember (posListNilWf n) rfl (Or.inr (Or.inl rfl)) rfl
    (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) posListConsAdmitted

def posListRecIdx :
    RecursorGroupIdxAdmitted PosList.listPrefix 11 listURecMember :=
  .ofAdmitted rfl

def posListEnv : ResolvedEnv := extendEnv PosList.listPrefix 11 listURecMember

def posListWf (n : Nat) : EnvWf posListEnv n :=
  .indMember _ 11 listURecMember (posListPrefixWf n) rfl (Or.inr (Or.inr rfl))
    rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
    (fun _ => posListRecIdx) PosList.admitted

theorem pin_envWf_posList : Nonempty (EnvWf posListEnv 1) := ⟨posListWf 1⟩

/-! ## `∀ n, ¬ EnvWf` for the four original-byte counterexamples.

`extendEnv` is a function overlay, so `cases` on `EnvWf boolEnv` does not
see the parameter as the constructor index. Walk the derivation instead.
A member present in any prefix is present in the concrete environment
(`hsub`); the refused member is impossible at the step that adds it. -/

private theorem prefix_sub {E0 Target : ResolvedEnv} {r0 : Nat}
    {m0 : CheckedMember} (hfresh : E0.members r0 = none)
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      (extendEnv E0 r0 m0).members k = some cm →
        Target.members k = some cm) :
    ∀ {k : Nat} {cm : CheckedMember},
      E0.members k = some cm → Target.members k = some cm :=
  fun hk => hsub (members_extend_preserved hfresh _ _ hk)

private theorem group_not_singleton {bad m0 : CheckedMember}
    (heq : m0 = bad)
    (hg : bad.mclass = .inductiveM ∨ bad.mclass = .constructorM ∨
      bad.mclass = .recursorM)
    (hs : m0.mclass = .axiomM ∨ m0.mclass = .definitionM ∨
      m0.mclass = .theoremM ∨ m0.mclass = .opaqueM) : False := by
  subst heq
  rcases hg with hg | hg | hg <;>
    rcases hs with hs | hs | hs | hs <;>
    (rw [hg] at hs; cases hs)

/-- A group-class member `bad` at slot `r` cannot sit in any `EnvWf`
whose members are among `Target`'s, once adding `bad` itself is refused
on every such prefix. Later extends keep the member and the subset. -/
def envWf_bad_slot_false {E Target : ResolvedEnv} {n r : Nat}
    {bad : CheckedMember}
    (hg : bad.mclass = .inductiveM ∨ bad.mclass = .constructorM ∨
      bad.mclass = .recursorM)
    (refuse : ∀ {E0 : ResolvedEnv},
      E0.members r = none →
      IndGroupAdmitted E0 r bad →
      (∀ {k : Nat} {cm : CheckedMember},
        E0.members k = some cm → Target.members k = some cm) →
      False) :
    (hE : EnvWf E n) →
    (hm : E.members r = some bad) →
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E.members k = some cm → Target.members k = some cm) →
    False
  | .empty _, hm, _ => by
      simp only [emptyEnv] at hm
      cases hm
  | .axiom E0 r0 A _ hE0 hfresh _ _, hm, hsub =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        injection hm with heq
        exact group_not_singleton heq hg (Or.inl rfl)
      else
        envWf_bad_slot_false hg refuse hE0
          (by
            rw [members_extend_ne E0 r0 ⟨.axiomM, 0, A, none⟩ r hrr] at hm
            exact hm)
          (prefix_sub hfresh hsub)
  | .definition E0 r0 A v _ hE0 hfresh _ _ _ _, hm, hsub =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        injection hm with heq
        exact group_not_singleton heq hg (Or.inr (Or.inl rfl))
      else
        envWf_bad_slot_false hg refuse hE0
          (by
            rw [members_extend_ne E0 r0 ⟨.definitionM, 0, A, some v⟩ r hrr]
              at hm
            exact hm)
          (prefix_sub hfresh hsub)
  | .thm E0 r0 A p hE0 hfresh _ _ _ _, hm, hsub =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        injection hm with heq
        exact group_not_singleton heq hg (Or.inr (Or.inr (Or.inl rfl)))
      else
        envWf_bad_slot_false hg refuse hE0
          (by
            rw [members_extend_ne E0 r0 ⟨.theoremM, 0, A, some p⟩ r hrr] at hm
            exact hm)
          (prefix_sub hfresh hsub)
  | .opaque E0 r0 A v _ hE0 hfresh _ _ _ _, hm, hsub =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        injection hm with heq
        exact group_not_singleton heq hg (Or.inr (Or.inr (Or.inr rfl)))
      else
        envWf_bad_slot_false hg refuse hE0
          (by
            rw [members_extend_ne E0 r0 ⟨.opaqueM, 0, A, some v⟩ r hrr] at hm
            exact hm)
          (prefix_sub hfresh hsub)
  | .indMember E0 r0 m0 hE0 hfresh _ _ _ _ _ _ _ _ hadm, hm, hsub =>
      if hrr : r = r0 then by
        subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        injection hm with heq
        subst heq
        exact refuse hfresh hadm (prefix_sub hfresh hsub)
      else
        envWf_bad_slot_false hg refuse hE0
          (by
            rw [members_extend_ne E0 r0 m0 r hrr] at hm
            exact hm)
          (prefix_sub hfresh hsub)

private theorem exBool_here_sub {E0 : ResolvedEnv}
    (hfresh : E0.members 3 = none)
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E0.members k = some cm → ExBool.boolEnv.members k = some cm) :
    ∀ {k : Nat} {cm : CheckedMember},
      E0.members k = some cm → ExBool.boolPrefix.members k = some cm := by
  intro k cm hk
  have hne : k ≠ 3 := by
    intro hk3
    subst hk3
    rw [hfresh] at hk
    cases hk
  have hEnv := hsub hk
  have hEq : ExBool.boolEnv.members k = ExBool.boolPrefix.members k := by
    simp only [ExBool.boolEnv, members_extend_ne ExBool.boolPrefix 3
      ExBool.boolRecMember k hne]
  rw [hEq] at hEnv
  exact hEnv

private theorem exBool_not_admitted {E0 : ResolvedEnv}
    (hfresh : E0.members 3 = none)
    (h : IndGroupAdmitted E0 3 ExBool.boolRecMember)
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E0.members k = some cm → ExBool.boolEnv.members k = some cm) : False :=
  Empty.elim (not_exBool_sub (exBool_here_sub hfresh hsub) h)

/-- `EnvWf` is `Type`-valued, so the refusal is `→ False`, not `¬`. -/
theorem not_envWf_exBool (n : Nat) (hE : EnvWf ExBool.boolEnv n) : False :=
  envWf_bad_slot_false (Or.inr (Or.inr rfl)) exBool_not_admitted hE
    ExBool.boolEnv_rec_member (fun hk => hk)

private theorem srcVa_not_contig {E : ResolvedEnv}
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E.members k = some cm → srcEnvV1.members k = some cm)
    (h : CtorContiguous E 43 mVaB0) : False := by
  rcases h with ⟨f, hf, _, hfwd, _⟩
  have hf11 : f = 11 := Option.some.inj (hf.symm.trans src_va_family)
  subst hf11
  rcases hfwd 12 (by decide) (by decide) with ⟨cm, hm, hc, _⟩
  have h12 : srcEnvV1.members 12 = some mBytesI := by
    have hs := src_va_slots
    exact congrArg (fun p : _ × _ × _ × _ => p.2.1) hs
  have hmem := hsub hm
  rw [h12] at hmem
  cases hmem
  unfold mBytesI mDef at hc
  cases hc

private theorem srcVa_not_admitted {E0 : ResolvedEnv}
    (_hfresh : E0.members 43 = none)
    (h : IndGroupAdmitted E0 43 mVaB0)
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E0.members k = some cm → srcEnvV1.members k = some cm) : False := by
  cases h with
  | family _ view _ hm _ =>
      have hc := view.hasClass
      rw [hm, mVaB0, mVa] at hc
      cases hc
  | recursor a _ _ _ _ _ _ =>
      have hhead :=
        policyRecursor_not_const a.family a.minorTypes a.policy
      rw [← a.recursorType] at hhead
      have hf : spineHeadRef (piResult mVaB0.mtype) = some 11 := by
        have hfam := src_va_family
        simp only [memberFamRef, mVaB0, mVa] at hfam
        exact hfam
      rw [hf] at hhead
      cases hhead
  | constructor _ _ _ _ hContig _ _ =>
      exact srcVa_not_contig hsub hContig

theorem not_envWf_srcVa (n : Nat) (hE : EnvWf srcEnvV1 n) : False :=
  envWf_bad_slot_false (by rw [mVaB0, mVa]; exact Or.inr (Or.inl rfl))
    srcVa_not_admitted hE
    (by
      have hs := src_va_slots
      exact congrArg (fun p : _ × _ × _ × _ => p.2.2.1) hs)
    (fun hk => hk)

/-- `EnvWf` is `Type`-valued, so the refusal is `→ False`, not `¬`. -/
theorem not_envWf_exAlias (n : Nat) (hE : EnvWf ExAlias.ctorPrefix n) : False :=
  envWf_bad_slot_false (by unfold ExAlias.ctor; exact Or.inr (Or.inl rfl))
    exAlias_not_admitted hE
    (by
      have hs := ExAlias.prefix_bytes
      exact congrArg (fun p : _ × _ × _ => p.2.2) hs)
    (fun hk => hk)

end Rcic.Declarative
