/-
K3c regroup stage 1b-i (head slice), per the K3c regroup stage-1b spec
§0–§2 pilot.  Generic admission machinery for the group-ordered source
environment of `ScmSrcGroups.lean`, plus the §1 family admissions for the
three Type families (N, Bytes, RefT) and the §2 constructor admissions for
`zero`/`succ` (lit-free, machine route).

No sorry/admit/axiom/native_decide; no RcicUntypedConvCollapse/totalConv;
no `Conv.irr`/`Conv.eta`.  Axioms ⊆ {propext, Quot.sound}.
-/
import rcic.ScmSrcGroups
import rcic.RcicIndGroupJudgment
import rcic.RcicMachine

namespace Rcic.Scm.SrcG
open Rcic.Declarative Rcic.Machine

set_option maxRecDepth 8192

/-! ## §0 generic machinery -/

/-- RM-015 wrapper: an `rfl`-checked machine `.infer` run yields the
    `HasTy` derivation. -/
def hasTyOfInfer {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {B : Nat}
    (h : kernelStepRaw ⟨⟨E, n, Γ⟩, .infer e, B⟩ =
      .result (.accepted (.inferredType T))) :
    HasTy E n Γ e T :=
  RM015_infer_sound ⟨⟨E, n, Γ⟩, .infer e, B⟩ e T rfl h

/-- `succ^t zero` (the `natExpand` expansion) types at `N`.  Slots 1/2
    are `mZero`/`mSucc` in every SrcG prefix env. -/
def hasTyNatExpand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc) :
    (t : Nat) → HasTy E n Γ (natExpand t) (.const 0 [])
  | 0 => .const Γ 1 [] mZero h1 rfl (fun _ h => nomatch h)
  | t + 1 =>
      .app Γ (.const 2 []) (natExpand t) (.const 0 []) (.const 0 [])
        (.const Γ 2 [] mSucc h2 rfl (fun _ h => nomatch h))
        (hasTyNatExpand h1 h2 t)

/-- `.lit t : N` — the 02 §8 literal rule over the `N`-expansion. -/
def hasTyLit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (t : Nat) : HasTy E n Γ (.lit t) (.const 0 []) :=
  .lit Γ t (.const 0 []) (hasTyNatExpand h1 h2 t)

/-- `PolicyTelescopeTyping` from a level list: one sort level per domain,
    each level `levelBounded`, each domain typed in its actual prefix
    context. -/
def telTyping {E : ResolvedEnv} {n : Nat} {doms : List (Expr Nat)}
    (ls : List Level) (hlen : ls.length = doms.length)
    (hb : ∀ i : Fin ls.length, levelBounded n ls[i.val] = true)
    (ht : ∀ i : Fin doms.length,
      HasTy E n (policyPrefixContext doms i.val) doms[i.val]
        (.sort (ls[i.val]'(by rw [hlen]; exact i.isLt)))) :
    PolicyTelescopeTyping E n doms where
  levels := fun i => ls[i.val]'(by rw [hlen]; exact i.isLt)
  bounded := fun i => hb ⟨i.val, by rw [hlen]; exact i.isLt⟩
  hasType := ht

/-- A `.const r` whose member stores a bare sort types at that sort. -/
def tyConstSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {m : CheckedMember} {u : Level}
    (hr : E.members r = some m) (ht : m.mtype = .sort u) (ha : m.arity = 0) :
    HasTy E n Γ (.const r []) (.sort u) :=
  ht ▸ (instantiateLevels_nil m.mtype ▸
    HasTy.const Γ r [] m hr (by rw [ha]; rfl) (fun _ h => nomatch h))

/-! ### Generic slot reflection

`foldEnv` turns a distinct-key slot table into a `ResolvedEnv`. The
Bool checks below reflect the judgment's table-wide Props back to
Bool computations over the table itself. -/

def foldEnv (tbl : List (Nat × CheckedMember)) : ResolvedEnv :=
  tbl.foldl (fun E (r, m) => extendEnv E r m) emptyEnv

private theorem foldEnv_go {tbl : List (Nat × CheckedMember)} {c : Nat} :
    (tbl.map (·.1)).Nodup → ∀ (acc : ResolvedEnv),
      (tbl.foldl (fun E (r, m) => extendEnv E r m) acc).members c =
        match tbl.find? (·.1 == c) with
        | some p => some p.2
        | none => acc.members c := by
  induction tbl with
  | nil => intro _ acc; rfl
  | cons p tl ih =>
      intro hnd acc
      rw [List.foldl_cons]
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, htl⟩ := hnd
      rw [ih htl]
      rw [List.find?_cons]
      by_cases h : (p.1 == c)
      · rw [h]
        have hfind : tl.find? (·.1 == c) = none := by
          rw [List.find?_eq_none]
          intro q hq hcon
          have hqe : q.1 = c := beq_iff_eq.mp hcon
          have hpe : p.1 = c := beq_iff_eq.mp h
          have hqmem : c ∈ tl.map (·.1) := hqe ▸ List.mem_map.mpr ⟨q, hq, rfl⟩
          exact hnot (hpe ▸ hqmem)
        rw [hfind]
        show (extendEnv acc p.1 p.2).members c = some p.2
        exact if_pos (beq_iff_eq.mp h).symm
      · have hnf : (p.1 == c) = false := by
          cases hb : (p.1 == c)
          · rfl
          · exact absurd hb h
        rw [hnf]
        cases hfind : tl.find? (·.1 == c) with
        | some q => rfl
        | none =>
            have hc : c ≠ p.1 := by
              intro he
              apply h
              rw [← he]
              exact beq_iff_eq.mpr rfl
            exact if_neg hc

theorem foldEnv_members {tbl : List (Nat × CheckedMember)} {c : Nat}
    (hnd : (tbl.map (·.1)).Nodup) :
    (foldEnv tbl).members c = (tbl.find? (·.1 == c)).map (·.2) := by
  unfold foldEnv
  rw [foldEnv_go hnd]
  cases tbl.find? (·.1 == c) <;> rfl

private def famCtorAtB (f : Nat) (p : Nat × CheckedMember) : Bool :=
  decide (p.2.mclass = .constructorM) && decide (memberFamRef p.2 = some f)

/-- Every slot in the open range `f < c < r` is a constructor of `f`. -/
private def famCtorRangeB (tbl : List (Nat × CheckedMember)) (f r : Nat) : Bool :=
  (List.range r).all (fun c =>
    !(decide (f < c) && decide (c < r)) ||
      match tbl.find? (·.1 == c) with
      | some p => famCtorAtB f p
      | none => false)

/-- Every constructor of `f` in the table sits in the open range. -/
private def famCtorBoundedB (tbl : List (Nat × CheckedMember)) (f r : Nat) : Bool :=
  tbl.all (fun p =>
    !(famCtorAtB f p) || (decide (f < p.1) && decide (p.1 < r)))

/-- No recursor of family `f` occurs in the table. -/
def noRecursorForB (tbl : List (Nat × CheckedMember)) (f : Nat) : Bool :=
  tbl.all (fun p =>
    !(decide (p.2.mclass = .recursorM)) || decide (memberFamRef p.2 ≠ some f))

/-- The slots strictly between family `f` and `r` are exactly `f`'s
constructor group, and `m`'s declared family is `f`. -/
def ctorContiguousB (tbl : List (Nat × CheckedMember)) (r : Nat)
    (m : CheckedMember) : Bool :=
  match memberFamRef m with
  | none => false
  | some f => decide (f < r) && famCtorRangeB tbl f r && famCtorBoundedB tbl f r

/-- `f`'s constructor group is exactly the slots in `(f, r)`. -/
def ctorCensusB (tbl : List (Nat × CheckedMember)) (f r : Nat) : Bool :=
  decide (f + 1 ≤ r) && famCtorRangeB tbl f r && famCtorBoundedB tbl f r

private theorem famCtorRangeB_sound {tbl : List (Nat × CheckedMember)} {f r : Nat}
    (hnd : (tbl.map (·.1)).Nodup)
    (h : famCtorRangeB tbl f r = true) :
    ∀ c, f < c → c < r → IsFamilyCtor (foldEnv tbl) f c := by
  intro c hfc hcr
  unfold famCtorRangeB at h
  rw [List.all_eq_true] at h
  have hb := h c (List.mem_range.mpr hcr)
  rw [Bool.or_eq_true_iff] at hb
  rcases hb with hnf | hb'
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hnf
    rcases hnf with h1 | h2
    · exact absurd hfc h1
    · exact absurd hcr h2
  · cases hf : tbl.find? (·.1 == c) with
    | none => rw [hf] at hb'; simp at hb'
    | some q =>
        rw [hf] at hb'
        simp only [famCtorAtB, Bool.and_eq_true_iff, decide_eq_true_eq] at hb'
        obtain ⟨hclass, hfam⟩ := hb'
        exact ⟨q.2, by rw [foldEnv_members hnd, hf]; rfl, hclass, hfam⟩

private theorem famCtorBoundedB_sound {tbl : List (Nat × CheckedMember)} {f r : Nat}
    (hnd : (tbl.map (·.1)).Nodup)
    (h : famCtorBoundedB tbl f r = true) :
    ∀ c, IsFamilyCtor (foldEnv tbl) f c → f < c ∧ c < r := by
  intro c ⟨cm, hmem, hclass, hfam⟩
  unfold famCtorBoundedB at h
  rw [foldEnv_members hnd] at hmem
  obtain ⟨q, hf, hq2⟩ := Option.map_eq_some'.mp hmem
  subst hq2
  have hqmem : q ∈ tbl := List.mem_of_find?_eq_some hf
  rw [List.all_eq_true] at h
  have hb := h q hqmem
  rw [Bool.or_eq_true_iff] at hb
  rcases hb with hnf | hbound
  · rw [Bool.not_eq_true'] at hnf
    have hguard : famCtorAtB f q = true := by
      simp only [famCtorAtB, Bool.and_eq_true_iff, decide_eq_true_eq]
      exact ⟨hclass, hfam⟩
    rw [hguard] at hnf
    simp at hnf
  · simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hbound
    obtain ⟨h1, h2⟩ := hbound
    have hfq := List.find?_some hf
    have hqkey : q.1 = c := beq_iff_eq.mp hfq
    rw [hqkey] at h1 h2
    exact ⟨h1, h2⟩

theorem noRecursorForB_sound {tbl : List (Nat × CheckedMember)} {f : Nat}
    (hnd : (tbl.map (·.1)).Nodup)
    (h : noRecursorForB tbl f = true) :
    NoRecursorFor (foldEnv tbl) f := by
  intro rr rm hmem hclass
  unfold noRecursorForB at h
  rw [foldEnv_members hnd] at hmem
  obtain ⟨q, hf, hq2⟩ := Option.map_eq_some'.mp hmem
  subst hq2
  have hqmem : q ∈ tbl := List.mem_of_find?_eq_some hf
  rw [List.all_eq_true] at h
  have hb := h q hqmem
  simp only [Bool.or_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at hb
  rcases hb with hnf | hnfam
  · exact absurd hclass hnf
  · exact hnfam

theorem ctorContiguousB_sound {tbl : List (Nat × CheckedMember)} {r : Nat}
    {m : CheckedMember}
    (hnd : (tbl.map (·.1)).Nodup)
    (h : ctorContiguousB tbl r m = true) :
    CtorContiguous (foldEnv tbl) r m := by
  unfold ctorContiguousB at h
  cases hf : memberFamRef m with
  | none => rw [hf] at h; simp at h
  | some f =>
      rw [hf] at h
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
      obtain ⟨⟨hfr, hrange⟩, hbound⟩ := h
      exact ⟨f, hf, hfr,
        famCtorRangeB_sound hnd hrange,
        famCtorBoundedB_sound hnd hbound⟩

theorem ctorCensusB_sound {tbl : List (Nat × CheckedMember)} {f r : Nat}
    (hnd : (tbl.map (·.1)).Nodup)
    (h : ctorCensusB tbl f r = true) :
    CtorCensus (foldEnv tbl) f r := by
  unfold ctorCensusB at h
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
  obtain ⟨⟨hle, hrange⟩, hbound⟩ := h
  refine ⟨hle, fun c => ?_⟩
  constructor
  · intro hmem
    exact famCtorBoundedB_sound hnd hbound c hmem
  · intro ⟨hfc, hcr⟩
    exact famCtorRangeB_sound hnd hrange c hfc hcr

theorem noRec_table1 : NoRecursorFor (foldEnv (srcMembersG.take 1)) 0 :=
  noRecursorForB_sound (by decide) (by decide)

theorem contig_table2 : CtorContiguous (foldEnv (srcMembersG.take 2)) 2 mSucc :=
  ctorContiguousB_sound (by decide) (by decide)

theorem census_table3 : CtorCensus (foldEnv (srcMembersG.take 3)) 0 3 :=
  ctorCensusB_sound (by decide) (by decide)

/-! ### Bool reflection for field permissions and universe bounds -/

/-- `fieldAnalyze` returned `permitted`. -/
def fieldPermittedB (E : ResolvedEnv) (fuel fam nuniv np ni depth : Nat)
    (T : Expr Nat) : Bool :=
  match fieldAnalyze E fuel fam nuniv np ni depth T with
  | .permitted _ _ => true
  | _ => false

theorem fieldPermitted_of_B {E : ResolvedEnv} {fuel fam nuniv np ni depth : Nat}
    {T : Expr Nat} (h : fieldPermittedB E fuel fam nuniv np ni depth T = true) :
    ∃ shape, FieldPermitted E fam nuniv np ni depth T shape := by
  unfold fieldPermittedB at h
  split at h
  · rename_i shape indices hf
    exact ⟨shape, fuel, indices, hf⟩
  · contradiction

/-- Every field of `c` is `permitted` under `fieldAnalyze`. -/
def ctorFieldsPermittedB {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member)
    (fuel : Nat) : Bool :=
  (List.range c.fields.length).all (fun j =>
    if hj : j < c.fields.length then
      fieldPermittedB E fuel family.ref family.member.arity
        family.parameters.length family.indices.length
        (family.parameters.length + j) c.fields[j]
    else false)

theorem ctorFieldsPermitted_of_B {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member)
    (fuel : Nat) (h : ctorFieldsPermittedB c fuel = true) :
    CtorFieldsPermitted c := by
  intro j
  unfold ctorFieldsPermittedB at h
  rw [List.all_eq_true] at h
  have hb := h j.val (List.mem_range.mpr j.isLt)
  rw [dif_pos j.isLt] at hb
  exact fieldPermitted_of_B hb

/-- Decidable fragment of `leN`: syntactic equality, or `.zero`. -/
def leNB (a b : Level) : Bool := decide (a = b) || decide (a = .zero)

theorem leN_of_leNB {a b : Level} (h : leNB a b = true) : leN a b := by
  unfold leNB at h
  cases hb1 : decide (a = b) with
  | true =>
      have hab : a = b := of_decide_eq_true hb1
      subst hab
      exact leN_refl a
  | false =>
      rw [hb1, Bool.false_or] at h
      have haz : a = .zero := of_decide_eq_true h
      subst haz
      intro ρ x y hx hy
      have hx0 : x = 0 := (Option.some.inj hx).symm
      subst hx0
      exact Nat.zero_le y

/-- Uniform-Type `FieldUniverseAdmitted` from a Bool level check. -/
theorem fieldUniverseAdmitted_type_of_B {E : ResolvedEnv}
    {family : PolicyFamilyView E} {member : CheckedMember}
    (c : PolicyConstructorView E family member)
    (hT : UniformType family.resultLevel)
    (h : (List.range c.fields.length).all (fun j =>
      if hj : j < c.fields.length then
        leNB (c.fieldLevel ⟨j, hj⟩) family.resultLevel
      else false) = true) :
    FieldUniverseAdmitted c := by
  intro j
  right
  refine ⟨hT, ?_⟩
  rw [List.all_eq_true] at h
  have hb := h j.val (List.mem_range.mpr j.isLt)
  rw [dif_pos j.isLt] at hb
  exact leN_of_leNB hb

/-- `noFamilyInIndices` from the Bool readout. -/
theorem noFamilyInIndicesB_of {f : Nat} {idxs : List (Expr Nat)}
    (h : idxs.all (fun e => !occursConst f e) = true) :
    ∀ e ∈ idxs, occursConst f e = false := by
  intro e he
  have hb := (List.all_eq_true.mp h) e he
  match hx : occursConst f e with
  | false => rfl
  | true =>
      rw [hx] at hb
      contradiction

/-- Prefix env before slot `r`: the table's slots strictly before `r`,
folded via `extendEnv`. -/
def envPre (r : Nat) : ResolvedEnv := foldEnv (srcMembersG.take r)

/-! ## §1 family admissions -/

def famViewAdmN : PolicyFamilyView (extendEnv (envPre 0) 0 mN) where
  ref := 0
  member := mN
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- §1: the `N` family member is admitted at slot 0. -/
def admFamN : IndGroupAdmitted (envPre 0) 0 mN :=
  .family rfl famViewAdmN rfl rfl (.inr uniformType_succ_zero)

def famViewAdmBytes : PolicyFamilyView (extendEnv (envPre 4) 4 mBytes) where
  ref := 4
  member := mBytes
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- §1: the `Bytes` family member is admitted at slot 4. -/
def admFamBytes : IndGroupAdmitted (envPre 4) 4 mBytes :=
  .family rfl famViewAdmBytes rfl rfl (.inr uniformType_succ_zero)

def famViewAdmRefT : PolicyFamilyView (extendEnv (envPre 8) 8 mRefT) where
  ref := 8
  member := mRefT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- §1: the `RefT` family member is admitted at slot 8. -/
def admFamRefT : IndGroupAdmitted (envPre 8) 8 mRefT :=
  .family rfl famViewAdmRefT rfl rfl (.inr uniformType_succ_zero)

/-! ## §2 constructor admissions (pilots: zero, succ) -/

/-- `N`'s family view inside `(envPre 1)` (the env holding slots < 1). -/
def famViewN1 : PolicyFamilyView (envPre 1) where
  ref := 0
  member := mN
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- `N`'s family view inside `(envPre 2)` (the env holding slots < 2). -/
def famViewN2 : PolicyFamilyView (envPre 2) where
  ref := 0
  member := mN
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _



/-- `zero`'s constructor view: no fields, result `N`. -/
def ctorViewZero : PolicyConstructorView (envPre 1) famViewN1 mZero where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by simp

/-- §2: `zero` is admitted at slot 1. -/
def admCtorZero : IndGroupAdmitted (envPre 1) 1 mZero :=
  .constructor famViewN1 ctorViewZero rfl
    ⟨0, rfl, noRecursorForB_sound (tbl := srcMembersG.take 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 1) (by decide) (by decide))
    (fun j => absurd j.isLt (Nat.not_lt_zero j.val))
    (ctorFieldsPermitted_of_B ctorViewZero 96 (by decide))

/-- `succ`'s constructor view: one field `N`, result `N`.  The field's
    domain typing is the machine's `.infer` in the field's prefix
    context. -/
def ctorViewSucc : PolicyConstructorView (envPre 2) famViewN2 mSucc where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 0 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := telTyping [.succ .zero] rfl
    (fun i => match i with
      | ⟨0, _⟩ => rfl
      | ⟨k+1, h⟩ => absurd (Nat.lt_one_iff.mp h) (Nat.succ_ne_zero k))
    (fun i => match i with
      | ⟨0, _⟩ => hasTyOfInfer (B := 65536) rfl
      | ⟨k+1, h⟩ => absurd (Nat.lt_one_iff.mp h) (Nat.succ_ne_zero k))
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by simp

/-- §2: `succ` is admitted at slot 2. -/
def admCtorSucc : IndGroupAdmitted (envPre 2) 2 mSucc :=
  .constructor famViewN2 ctorViewSucc rfl
    ⟨0, rfl, noRecursorForB_sound (tbl := srcMembersG.take 2) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 2) (by decide) (by decide))
    (fun j => match j with
      | ⟨0, _⟩ => .inr ⟨uniformType_succ_zero, leN_refl _⟩
      | ⟨k+1, h⟩ => absurd (Nat.lt_one_iff.mp h) (Nat.succ_ne_zero k))
    (ctorFieldsPermitted_of_B ctorViewSucc 96 (by decide))

/-- §1: `mDA` family admitted at slot 23. -/
def famViewAdmDA : PolicyFamilyView (extendEnv (envPre 23) 23 mDA) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨2, _⟩ => tyConstSort rfl rfl rfl
      | ⟨3, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 4, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mDA's admission at slot 23. -/
def admFamDA : IndGroupAdmitted (envPre 23) 23 mDA :=
  .family rfl famViewAdmDA rfl rfl (.inl (fun _ => rfl))

/-- §1: `mI` family admitted at slot 30. -/
def famViewAdmI : PolicyFamilyView (extendEnv (envPre 30) 30 mI) where
  ref := 30
  member := mI
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- mI's admission at slot 30. -/
def admFamI : IndGroupAdmitted (envPre 30) 30 mI :=
  .family rfl famViewAdmI rfl rfl (.inr uniformType_succ_zero)

/-- §1: `mBL` family admitted at slot 34. -/
def famViewAdmBL : PolicyFamilyView (extendEnv (envPre 34) 34 mBL) where
  ref := 34
  member := mBL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- mBL's admission at slot 34. -/
def admFamBL : IndGroupAdmitted (envPre 34) 34 mBL :=
  .family rfl famViewAdmBL rfl rfl (.inr uniformType_succ_zero)

/-- §1: `mFT` family admitted at slot 38. -/
def famViewAdmFT : PolicyFamilyView (extendEnv (envPre 38) 38 mFT) where
  ref := 38
  member := mFT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- mFT's admission at slot 38. -/
def admFamFT : IndGroupAdmitted (envPre 38) 38 mFT :=
  .family rfl famViewAdmFT rfl rfl (.inr uniformType_succ_zero)

/-- §1: `mLt` family admitted at slot 42. -/
def famViewAdmLt : PolicyFamilyView (extendEnv (envPre 42) 42 mLt) where
  ref := 42
  member := mLt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mLt's admission at slot 42. -/
def admFamLt : IndGroupAdmitted (envPre 42) 42 mLt :=
  .family rfl famViewAdmLt rfl rfl (.inl (fun _ => rfl))

/-- §1: `mBC` family admitted at slot 46. -/
def famViewAdmBC : PolicyFamilyView (extendEnv (envPre 46) 46 mBC) where
  ref := 46
  member := mBC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨2, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 3, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mBC's admission at slot 46. -/
def admFamBC : IndGroupAdmitted (envPre 46) 46 mBC :=
  .family rfl famViewAdmBC rfl rfl (.inl (fun _ => rfl))

/-- §1: `mDM10` family admitted at slot 50. -/
def famViewAdmDM10 : PolicyFamilyView (extendEnv (envPre 50) 50 mDM10) where
  ref := 50
  member := mDM10
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨2, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 3, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mDM10's admission at slot 50. -/
def admFamDM10 : IndGroupAdmitted (envPre 50) 50 mDM10 :=
  .family rfl famViewAdmDM10 rfl rfl (.inl (fun _ => rfl))

/-- §1: `mND` family admitted at slot 54. -/
def famViewAdmND : PolicyFamilyView (extendEnv (envPre 54) 54 mND) where
  ref := 54
  member := mND
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mND's admission at slot 54. -/
def admFamND : IndGroupAdmitted (envPre 54) 54 mND :=
  .family rfl famViewAdmND rfl rfl (.inl (fun _ => rfl))

/-- §1: `mNEA` family admitted at slot 58. -/
def famViewAdmNEA : PolicyFamilyView (extendEnv (envPre 58) 58 mNEA) where
  ref := 58
  member := mNEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mNEA's admission at slot 58. -/
def admFamNEA : IndGroupAdmitted (envPre 58) 58 mNEA :=
  .family rfl famViewAdmNEA rfl rfl (.inl (fun _ => rfl))

/-- §1: `mIEA` family admitted at slot 61. -/
def famViewAdmIEA : PolicyFamilyView (extendEnv (envPre 61) 61 mIEA) where
  ref := 61
  member := mIEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 30 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mIEA's admission at slot 61. -/
def admFamIEA : IndGroupAdmitted (envPre 61) 61 mIEA :=
  .family rfl famViewAdmIEA rfl rfl (.inl (fun _ => rfl))

/-- §1: `mSL` family admitted at slot 65. -/
def famViewAdmSL : PolicyFamilyView (extendEnv (envPre 65) 65 mSL) where
  ref := 65
  member := mSL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mSL's admission at slot 65. -/
def admFamSL : IndGroupAdmitted (envPre 65) 65 mSL :=
  .family rfl famViewAdmSL rfl rfl (.inl (fun _ => rfl))

/-- §1: `mBLL` family admitted at slot 69. -/
def famViewAdmBLL : PolicyFamilyView (extendEnv (envPre 69) 69 mBLL) where
  ref := 69
  member := mBLL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mBLL's admission at slot 69. -/
def admFamBLL : IndGroupAdmitted (envPre 69) 69 mBLL :=
  .family rfl famViewAdmBLL rfl rfl (.inl (fun _ => rfl))

/-- §1: `mFTL` family admitted at slot 73. -/
def famViewAdmFTL : PolicyFamilyView (extendEnv (envPre 73) 73 mFTL) where
  ref := 73
  member := mFTL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mFTL's admission at slot 73. -/
def admFamFTL : IndGroupAdmitted (envPre 73) 73 mFTL :=
  .family rfl famViewAdmFTL rfl rfl (.inl (fun _ => rfl))

/-- §1: `mBLC` family admitted at slot 77. -/
def famViewAdmBLC : PolicyFamilyView (extendEnv (envPre 77) 77 mBLC) where
  ref := 77
  member := mBLC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mBLC's admission at slot 77. -/
def admFamBLC : IndGroupAdmitted (envPre 77) 77 mBLC :=
  .family rfl famViewAdmBLC rfl rfl (.inl (fun _ => rfl))

/-- §1: `mSEA` family admitted at slot 81. -/
def famViewAdmSEA : PolicyFamilyView (extendEnv (envPre 81) 81 mSEA) where
  ref := 81
  member := mSEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mSEA's admission at slot 81. -/
def admFamSEA : IndGroupAdmitted (envPre 81) 81 mSEA :=
  .family rfl famViewAdmSEA rfl rfl (.inl (fun _ => rfl))

/-- §1: `mFTE` family admitted at slot 84. -/
def famViewAdmFTE : PolicyFamilyView (extendEnv (envPre 84) 84 mFTE) where
  ref := 84
  member := mFTE
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mFTE's admission at slot 84. -/
def admFamFTE : IndGroupAdmitted (envPre 84) 84 mFTE :=
  .family rfl famViewAdmFTE rfl rfl (.inl (fun _ => rfl))

/-- §1: `mNthB` family admitted at slot 88. -/
def famViewAdmNthB : PolicyFamilyView (extendEnv (envPre 88) 88 mNthB) where
  ref := 88
  member := mNthB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨2, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 3, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mNthB's admission at slot 88. -/
def admFamNthB : IndGroupAdmitted (envPre 88) 88 mNthB :=
  .family rfl famViewAdmNthB rfl rfl (.inl (fun _ => rfl))

/-- §1: `mNthF` family admitted at slot 92. -/
def famViewAdmNthF : PolicyFamilyView (extendEnv (envPre 92) 92 mNthF) where
  ref := 92
  member := mNthF
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨2, _⟩ => tyConstSort rfl rfl rfl
      | ⟨3, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 4, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mNthF's admission at slot 92. -/
def admFamNthF : IndGroupAdmitted (envPre 92) 92 mNthF :=
  .family rfl famViewAdmNthF rfl rfl (.inl (fun _ => rfl))

/-- §1: `mCCT` family admitted at slot 96. -/
def famViewAdmCCT : PolicyFamilyView (extendEnv (envPre 96) 96 mCCT) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mCCT's admission at slot 96. -/
def admFamCCT : IndGroupAdmitted (envPre 96) 96 mCCT :=
  .family rfl famViewAdmCCT rfl rfl (.inl (fun _ => rfl))

/-- §1: `mBCT` family admitted at slot 106. -/
def famViewAdmBCT : PolicyFamilyView (extendEnv (envPre 106) 106 mBCT) where
  ref := 106
  member := mBCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- mBCT's admission at slot 106. -/
def admFamBCT : IndGroupAdmitted (envPre 106) 106 mBCT :=
  .family rfl famViewAdmBCT rfl rfl (.inr uniformType_succ_zero)

/-- §1: `mNEL` family admitted at slot 125. -/
def famViewAdmNEL : PolicyFamilyView (extendEnv (envPre 125) 125 mNEL) where
  ref := 125
  member := mNEL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mNEL's admission at slot 125. -/
def admFamNEL : IndGroupAdmitted (envPre 125) 125 mNEL :=
  .family rfl famViewAdmNEL rfl rfl (.inl (fun _ => rfl))

/-- §1: `mNTB` family admitted at slot 129. -/
def famViewAdmNTB : PolicyFamilyView (extendEnv (envPre 129) 129 mNTB) where
  ref := 129
  member := mNTB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 106 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨2, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 3, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mNTB's admission at slot 129. -/
def admFamNTB : IndGroupAdmitted (envPre 129) 129 mNTB :=
  .family rfl famViewAdmNTB rfl rfl (.inl (fun _ => rfl))

/-- §1: `mValueAt` family admitted at slot 133. -/
def famViewAdmValueAt : PolicyFamilyView (extendEnv (envPre 133) 133 mValueAt) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort rfl rfl rfl
      | ⟨1, _⟩ => tyConstSort rfl rfl rfl
      | ⟨n + 2, h⟩ => by
        simp only [List.length_append, List.length_nil, List.length_cons] at h
        omega }

/-- mValueAt's admission at slot 133. -/
def admFamValueAt : IndGroupAdmitted (envPre 133) 133 mValueAt :=
  .family rfl famViewAdmValueAt rfl rfl (.inl (fun _ => rfl))


/-! ### Literal-bearing spine inference

The reference machine refuses `.lit` outright, so `inferSpine` covers
the literal-bearing first-order fragment directly, returning `HasTy`
derivations (sound by construction). A `.pi` arm is included because
the fallback machine cannot type a binder whose codomain carries a
literal (`mCctSum`'s `f` field). -/

/-- Verified inference for the literal-bearing fragment. -/
def inferSpine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc) :
    (e : Expr Nat) → Option (Σ' T, HasTy E n Γ e T)
  | .bvar i =>
      match h : lookupType Γ i with
      | some T => some ⟨T, .bvar Γ i T h⟩
      | none => none
  | .const r [] =>
      match hm : E.members r with
      | some m =>
          if ha : m.arity = 0 then
            some ⟨instantiateLevels [] m.mtype,
              .const Γ r [] m hm ha.symm (fun _ h => nomatch h)⟩
          else none
      | none => none
  | .const _ (_ :: _) => none
  | .lit t => some ⟨.const 0 [], hasTyLit h1 h2 t⟩
  | .pi A B =>
      match inferSpine h1 h2 A with
      | some ⟨.sort u, hA⟩ =>
          match inferSpine (Γ := LocalDecl.assumption A :: Γ) h1 h2 B with
          | some ⟨.sort v, hB⟩ =>
              some ⟨.sort (.imax u v), .pi Γ A u B v hA hB⟩
          | _ => none
      | _ => none
  | .app f a =>
      match inferSpine h1 h2 f with
      | some ⟨.pi A B, hf⟩ =>
          match inferSpine h1 h2 a with
          | some ⟨Ta, ha⟩ =>
              if heq : Ta = A then
                some ⟨instantiate0 a B, .app Γ f a A B hf (heq ▸ ha)⟩
              else none
          | none => none
      | _ => none
  | _ => none

/-- Infer a domain's sort: spine typing first, the machine second. -/
private def inferDomSort {E : ResolvedEnv}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (Γ : LCtx) (e : Expr Nat) :
    Option (Σ' l : Level, Σ' (_ : levelBounded 0 l = true),
      HasTy E 0 Γ e (.sort l)) :=
  match inferSpine (n := 0) h1 h2 e with
  | some ⟨.sort l, ht⟩ =>
      if hb : levelBounded 0 l = true then some ⟨l, hb, ht⟩ else none
  | _ =>
      match hk : kernelStepRaw ⟨⟨E, 0, Γ⟩, .infer e, 65536⟩ with
      | .result (.accepted (.inferredType (.sort l))) =>
          if hb : levelBounded 0 l = true then
            some ⟨l, hb, hasTyOfInfer hk⟩
          else none
      | _ => none

/-- Domain inference at a telescope position. -/
private def inferDomAt {E : ResolvedEnv}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (doms : List (Expr Nat)) (i : Fin doms.length) :
    Option (Σ' l : Level, Σ' (_ : levelBounded 0 l = true),
      HasTy E 0 (policyPrefixContext doms i.val) doms[i.val] (.sort l)) :=
  inferDomSort h1 h2 (policyPrefixContext doms i.val) doms[i.val]

/-- Bool readout of `inferDomAt` at a `Nat` index. -/
private def inferDomB {E : ResolvedEnv}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (doms : List (Expr Nat)) (c : Nat) : Bool :=
  if hc : c < doms.length then
    (inferDomAt h1 h2 doms ⟨c, hc⟩).isSome
  else false

/-- Automated telescope typing: every domain must admit a spine or
machine derivation at a bounded sort. -/
def telTypingAuto {E : ResolvedEnv}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    (doms : List (Expr Nat)) : Option (PolicyTelescopeTyping E 0 doms) :=
  match hall : (List.range doms.length).all (inferDomB h1 h2 doms) with
  | false => none
  | true =>
      have hs : ∀ i : Fin doms.length,
          (inferDomAt h1 h2 doms i).isSome = true := by
        intro i
        rw [List.all_eq_true] at hall
        have hb := hall i.val (List.mem_range.mpr i.isLt)
        unfold inferDomB at hb
        rw [dif_pos i.isLt] at hb
        exact hb
      some {
        levels := fun i => ((inferDomAt h1 h2 doms i).get (hs i)).1
        bounded := fun i => ((inferDomAt h1 h2 doms i).get (hs i)).2.1
        hasType := fun i => ((inferDomAt h1 h2 doms i).get (hs i)).2.2
      }

/-! ## §2 pilot constructor admissions -/

/-- `CCT`'s family view in any env holding its slots. -/
def famViewCCTAt {E : ResolvedEnv}
    (h96 : E.members 96 = some mCCT) (h8 : E.members 8 = some mRefT)
    (h4 : E.members 4 = some mBytes) : PolicyFamilyView E where
  ref := 96
  member := mCCT
  present := h96
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => tyConstSort h8 rfl rfl
      | ⟨1, _⟩ => tyConstSort h4 rfl rfl
      | ⟨n + 2, h⟩ => by
          simp only [List.length_append, List.length_cons, List.length_nil] at h
          omega }

/-- `DM10`'s family view in `envPre 51`. -/
def famViewDM51 : PolicyFamilyView (envPre 51) where
  ref := 50
  member := mDM10
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 51) rfl rfl
    [.const 0 [], .const 0 [], .const 0 []]).get (by decide)

/-- `mCctI`'s constructor view in `envPre 97`. -/
def ctorViewCctI : PolicyConstructorView (envPre 97) (famViewCCTAt rfl rfl rfl) mCctI where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctI
  resultIndices := ctorIdx mCctI
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 97) rfl rfl (ctorDom mCctI)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by decide

/-- `cctI` admitted at slot 97. -/
def admCtorCctI : IndGroupAdmitted (envPre 97) 97 mCctI :=
  .constructor (famViewCCTAt rfl rfl rfl) ctorViewCctI rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 97) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 97) (by decide) (by decide))
    (fun j => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctI 96 (by decide))

/-- `mDmBase`'s constructor view in `envPre 51`. -/
def ctorViewDmBase : PolicyConstructorView (envPre 51) famViewDM51 mDmBase where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDmBase
  resultIndices := ctorIdx mDmBase
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 51) rfl rfl (ctorDom mDmBase)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by decide

/-- `dmBase` admitted at slot 51. -/
def admCtorDmBase : IndGroupAdmitted (envPre 51) 51 mDmBase :=
  .constructor famViewDM51 ctorViewDmBase rfl
    ⟨50, rfl, noRecursorForB_sound (tbl := srcMembersG.take 51) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 51) (by decide) (by decide))
    (fun j => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDmBase 96 (by decide))

/-- `mCctSum`'s constructor view in `envPre 103`. -/
def ctorViewCctSum : PolicyConstructorView (envPre 103) (famViewCCTAt rfl rfl rfl) mCctSum where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctSum
  resultIndices := ctorIdx mCctSum
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 103) rfl rfl (ctorDom mCctSum)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by decide

/-- `cctSum` admitted at slot 103. -/
def admCtorCctSum : IndGroupAdmitted (envPre 103) 103 mCctSum :=
  .constructor (famViewCCTAt rfl rfl rfl) ctorViewCctSum rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 103) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 103) (by decide) (by decide))
    (fun j => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctSum 96 (by decide))

/-! ## §2 constructor admissions: batch 1 -/

def famViewBnil : PolicyFamilyView (envPre 5) where
  ref := 4
  member := mBytes
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 5) rfl rfl
    []).get (by decide)

def ctorViewBnil : PolicyConstructorView (envPre 5) famViewBnil mBnil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBnil
  resultIndices := ctorIdx mBnil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 5) rfl rfl
    (ctorDom mBnil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBnil : IndGroupAdmitted (envPre 5) 5 mBnil :=
  .constructor famViewBnil ctorViewBnil rfl
    ⟨4, rfl, noRecursorForB_sound (tbl := srcMembersG.take 5)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 5)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewBnil uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewBnil 96 (by decide))

def famViewBcons : PolicyFamilyView (envPre 6) where
  ref := 4
  member := mBytes
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 6) rfl rfl
    []).get (by decide)

def ctorViewBcons : PolicyConstructorView (envPre 6) famViewBcons mBcons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBcons
  resultIndices := ctorIdx mBcons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 6) rfl rfl
    (ctorDom mBcons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBcons : IndGroupAdmitted (envPre 6) 6 mBcons :=
  .constructor famViewBcons ctorViewBcons rfl
    ⟨4, rfl, noRecursorForB_sound (tbl := srcMembersG.take 6)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 6)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewBcons uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewBcons 96 (by decide))

def famViewMkRef : PolicyFamilyView (envPre 9) where
  ref := 8
  member := mRefT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 9) rfl rfl
    []).get (by decide)

def ctorViewMkRef : PolicyConstructorView (envPre 9) famViewMkRef mMkRef where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mMkRef
  resultIndices := ctorIdx mMkRef
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 9) rfl rfl
    (ctorDom mMkRef)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorMkRef : IndGroupAdmitted (envPre 9) 9 mMkRef :=
  .constructor famViewMkRef ctorViewMkRef rfl
    ⟨8, rfl, noRecursorForB_sound (tbl := srcMembersG.take 9)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 9)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewMkRef uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewMkRef 96 (by decide))

def famViewDaI : PolicyFamilyView (envPre 24) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 24) rfl rfl
    [.const 0 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewDaI : PolicyConstructorView (envPre 24) famViewDaI mDaI where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaI
  resultIndices := ctorIdx mDaI
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 24) rfl rfl
    (ctorDom mDaI)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorDaI : IndGroupAdmitted (envPre 24) 24 mDaI :=
  .constructor famViewDaI ctorViewDaI rfl
    ⟨23, rfl, noRecursorForB_sound (tbl := srcMembersG.take 24)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 24)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDaI 96 (by decide))

def famViewDaB : PolicyFamilyView (envPre 25) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 25) rfl rfl
    [.const 0 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewDaB : PolicyConstructorView (envPre 25) famViewDaB mDaB where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaB
  resultIndices := ctorIdx mDaB
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 25) rfl rfl
    (ctorDom mDaB)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorDaB : IndGroupAdmitted (envPre 25) 25 mDaB :=
  .constructor famViewDaB ctorViewDaB rfl
    ⟨23, rfl, noRecursorForB_sound (tbl := srcMembersG.take 25)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 25)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDaB 96 (by decide))

def famViewDaS : PolicyFamilyView (envPre 26) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 26) rfl rfl
    [.const 0 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewDaS : PolicyConstructorView (envPre 26) famViewDaS mDaS where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaS
  resultIndices := ctorIdx mDaS
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 26) rfl rfl
    (ctorDom mDaS)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorDaS : IndGroupAdmitted (envPre 26) 26 mDaS :=
  .constructor famViewDaS ctorViewDaS rfl
    ⟨23, rfl, noRecursorForB_sound (tbl := srcMembersG.take 26)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 26)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDaS 96 (by decide))

def famViewDaY : PolicyFamilyView (envPre 27) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 27) rfl rfl
    [.const 0 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewDaY : PolicyConstructorView (envPre 27) famViewDaY mDaY where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaY
  resultIndices := ctorIdx mDaY
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 27) rfl rfl
    (ctorDom mDaY)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorDaY : IndGroupAdmitted (envPre 27) 27 mDaY :=
  .constructor famViewDaY ctorViewDaY rfl
    ⟨23, rfl, noRecursorForB_sound (tbl := srcMembersG.take 27)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 27)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDaY 96 (by decide))

def famViewDaLB : PolicyFamilyView (envPre 28) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 28) rfl rfl
    [.const 0 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewDaLB : PolicyConstructorView (envPre 28) famViewDaLB mDaLB where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaLB
  resultIndices := ctorIdx mDaLB
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 28) rfl rfl
    (ctorDom mDaLB)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorDaLB : IndGroupAdmitted (envPre 28) 28 mDaLB :=
  .constructor famViewDaLB ctorViewDaLB rfl
    ⟨23, rfl, noRecursorForB_sound (tbl := srcMembersG.take 28)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 28)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDaLB 96 (by decide))

def famViewIPos : PolicyFamilyView (envPre 31) where
  ref := 30
  member := mI
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 31) rfl rfl
    []).get (by decide)

def ctorViewIPos : PolicyConstructorView (envPre 31) famViewIPos mIPos where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mIPos
  resultIndices := ctorIdx mIPos
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 31) rfl rfl
    (ctorDom mIPos)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorIPos : IndGroupAdmitted (envPre 31) 31 mIPos :=
  .constructor famViewIPos ctorViewIPos rfl
    ⟨30, rfl, noRecursorForB_sound (tbl := srcMembersG.take 31)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 31)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewIPos uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewIPos 96 (by decide))

def famViewINegS : PolicyFamilyView (envPre 32) where
  ref := 30
  member := mI
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 32) rfl rfl
    []).get (by decide)

def ctorViewINegS : PolicyConstructorView (envPre 32) famViewINegS mINegS where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mINegS
  resultIndices := ctorIdx mINegS
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 32) rfl rfl
    (ctorDom mINegS)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorINegS : IndGroupAdmitted (envPre 32) 32 mINegS :=
  .constructor famViewINegS ctorViewINegS rfl
    ⟨30, rfl, noRecursorForB_sound (tbl := srcMembersG.take 32)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 32)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewINegS uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewINegS 96 (by decide))

def famViewBlNil : PolicyFamilyView (envPre 35) where
  ref := 34
  member := mBL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 35) rfl rfl
    []).get (by decide)

def ctorViewBlNil : PolicyConstructorView (envPre 35) famViewBlNil mBlNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlNil
  resultIndices := ctorIdx mBlNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 35) rfl rfl
    (ctorDom mBlNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBlNil : IndGroupAdmitted (envPre 35) 35 mBlNil :=
  .constructor famViewBlNil ctorViewBlNil rfl
    ⟨34, rfl, noRecursorForB_sound (tbl := srcMembersG.take 35)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 35)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewBlNil uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewBlNil 96 (by decide))

def famViewBlCons : PolicyFamilyView (envPre 36) where
  ref := 34
  member := mBL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 36) rfl rfl
    []).get (by decide)

def ctorViewBlCons : PolicyConstructorView (envPre 36) famViewBlCons mBlCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlCons
  resultIndices := ctorIdx mBlCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 36) rfl rfl
    (ctorDom mBlCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBlCons : IndGroupAdmitted (envPre 36) 36 mBlCons :=
  .constructor famViewBlCons ctorViewBlCons rfl
    ⟨34, rfl, noRecursorForB_sound (tbl := srcMembersG.take 36)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 36)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewBlCons uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewBlCons 96 (by decide))

def famViewFtNil : PolicyFamilyView (envPre 39) where
  ref := 38
  member := mFT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 39) rfl rfl
    []).get (by decide)

def ctorViewFtNil : PolicyConstructorView (envPre 39) famViewFtNil mFtNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtNil
  resultIndices := ctorIdx mFtNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 39) rfl rfl
    (ctorDom mFtNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorFtNil : IndGroupAdmitted (envPre 39) 39 mFtNil :=
  .constructor famViewFtNil ctorViewFtNil rfl
    ⟨38, rfl, noRecursorForB_sound (tbl := srcMembersG.take 39)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 39)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewFtNil uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewFtNil 96 (by decide))

def famViewFtCons : PolicyFamilyView (envPre 40) where
  ref := 38
  member := mFT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 40) rfl rfl
    []).get (by decide)

def ctorViewFtCons : PolicyConstructorView (envPre 40) famViewFtCons mFtCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtCons
  resultIndices := ctorIdx mFtCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 40) rfl rfl
    (ctorDom mFtCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorFtCons : IndGroupAdmitted (envPre 40) 40 mFtCons :=
  .constructor famViewFtCons ctorViewFtCons rfl
    ⟨38, rfl, noRecursorForB_sound (tbl := srcMembersG.take 40)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 40)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewFtCons uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewFtCons 96 (by decide))

def famViewLtBase : PolicyFamilyView (envPre 43) where
  ref := 42
  member := mLt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 43) rfl rfl
    [.const 0 [], .const 0 []]).get (by decide)

def ctorViewLtBase : PolicyConstructorView (envPre 43) famViewLtBase mLtBase where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mLtBase
  resultIndices := ctorIdx mLtBase
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 43) rfl rfl
    (ctorDom mLtBase)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorLtBase : IndGroupAdmitted (envPre 43) 43 mLtBase :=
  .constructor famViewLtBase ctorViewLtBase rfl
    ⟨42, rfl, noRecursorForB_sound (tbl := srcMembersG.take 43)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 43)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewLtBase 96 (by decide))

def famViewLtStep : PolicyFamilyView (envPre 44) where
  ref := 42
  member := mLt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 44) rfl rfl
    [.const 0 [], .const 0 []]).get (by decide)

def ctorViewLtStep : PolicyConstructorView (envPre 44) famViewLtStep mLtStep where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mLtStep
  resultIndices := ctorIdx mLtStep
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 44) rfl rfl
    (ctorDom mLtStep)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorLtStep : IndGroupAdmitted (envPre 44) 44 mLtStep :=
  .constructor famViewLtStep ctorViewLtStep rfl
    ⟨42, rfl, noRecursorForB_sound (tbl := srcMembersG.take 44)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 44)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewLtStep 96 (by decide))

def famViewCatNil : PolicyFamilyView (envPre 47) where
  ref := 46
  member := mBC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 47) rfl rfl
    [.const 4 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewCatNil : PolicyConstructorView (envPre 47) famViewCatNil mCatNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCatNil
  resultIndices := ctorIdx mCatNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 47) rfl rfl
    (ctorDom mCatNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCatNil : IndGroupAdmitted (envPre 47) 47 mCatNil :=
  .constructor famViewCatNil ctorViewCatNil rfl
    ⟨46, rfl, noRecursorForB_sound (tbl := srcMembersG.take 47)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 47)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCatNil 96 (by decide))

def famViewCatCons : PolicyFamilyView (envPre 48) where
  ref := 46
  member := mBC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 48) rfl rfl
    [.const 4 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewCatCons : PolicyConstructorView (envPre 48) famViewCatCons mCatCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCatCons
  resultIndices := ctorIdx mCatCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 48) rfl rfl
    (ctorDom mCatCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCatCons : IndGroupAdmitted (envPre 48) 48 mCatCons :=
  .constructor famViewCatCons ctorViewCatCons rfl
    ⟨46, rfl, noRecursorForB_sound (tbl := srcMembersG.take 48)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 48)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCatCons 96 (by decide))

def famViewDmStep : PolicyFamilyView (envPre 52) where
  ref := 50
  member := mDM10
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 52) rfl rfl
    [.const 0 [], .const 0 [], .const 0 []]).get (by decide)

def ctorViewDmStep : PolicyConstructorView (envPre 52) famViewDmStep mDmStep where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDmStep
  resultIndices := ctorIdx mDmStep
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 52) rfl rfl
    (ctorDom mDmStep)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorDmStep : IndGroupAdmitted (envPre 52) 52 mDmStep :=
  .constructor famViewDmStep ctorViewDmStep rfl
    ⟨50, rfl, noRecursorForB_sound (tbl := srcMembersG.take 52)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 52)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewDmStep 96 (by decide))

def famViewNdBase : PolicyFamilyView (envPre 55) where
  ref := 54
  member := mND
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 55) rfl rfl
    [.const 0 [], .const 4 []]).get (by decide)

def ctorViewNdBase : PolicyConstructorView (envPre 55) famViewNdBase mNdBase where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNdBase
  resultIndices := ctorIdx mNdBase
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 55) rfl rfl
    (ctorDom mNdBase)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNdBase : IndGroupAdmitted (envPre 55) 55 mNdBase :=
  .constructor famViewNdBase ctorViewNdBase rfl
    ⟨54, rfl, noRecursorForB_sound (tbl := srcMembersG.take 55)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 55)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNdBase 96 (by decide))

def famViewNdStep : PolicyFamilyView (envPre 56) where
  ref := 54
  member := mND
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 56) rfl rfl
    [.const 0 [], .const 4 []]).get (by decide)

def ctorViewNdStep : PolicyConstructorView (envPre 56) famViewNdStep mNdStep where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNdStep
  resultIndices := ctorIdx mNdStep
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 56) rfl rfl
    (ctorDom mNdStep)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNdStep : IndGroupAdmitted (envPre 56) 56 mNdStep :=
  .constructor famViewNdStep ctorViewNdStep rfl
    ⟨54, rfl, noRecursorForB_sound (tbl := srcMembersG.take 56)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 56)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNdStep 96 (by decide))

def famViewNeIntro : PolicyFamilyView (envPre 59) where
  ref := 58
  member := mNEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 59) rfl rfl
    [.const 0 [], .const 4 []]).get (by decide)

def ctorViewNeIntro : PolicyConstructorView (envPre 59) famViewNeIntro mNeIntro where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNeIntro
  resultIndices := ctorIdx mNeIntro
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 59) rfl rfl
    (ctorDom mNeIntro)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNeIntro : IndGroupAdmitted (envPre 59) 59 mNeIntro :=
  .constructor famViewNeIntro ctorViewNeIntro rfl
    ⟨58, rfl, noRecursorForB_sound (tbl := srcMembersG.take 59)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 59)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNeIntro 96 (by decide))

def famViewIePos : PolicyFamilyView (envPre 62) where
  ref := 61
  member := mIEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 30 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 62) rfl rfl
    [.const 30 [], .const 4 []]).get (by decide)

def ctorViewIePos : PolicyConstructorView (envPre 62) famViewIePos mIePos where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mIePos
  resultIndices := ctorIdx mIePos
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 62) rfl rfl
    (ctorDom mIePos)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorIePos : IndGroupAdmitted (envPre 62) 62 mIePos :=
  .constructor famViewIePos ctorViewIePos rfl
    ⟨61, rfl, noRecursorForB_sound (tbl := srcMembersG.take 62)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 62)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewIePos 96 (by decide))

def famViewIeNeg : PolicyFamilyView (envPre 63) where
  ref := 61
  member := mIEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 30 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 63) rfl rfl
    [.const 30 [], .const 4 []]).get (by decide)

def ctorViewIeNeg : PolicyConstructorView (envPre 63) famViewIeNeg mIeNeg where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mIeNeg
  resultIndices := ctorIdx mIeNeg
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 63) rfl rfl
    (ctorDom mIeNeg)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorIeNeg : IndGroupAdmitted (envPre 63) 63 mIeNeg :=
  .constructor famViewIeNeg ctorViewIeNeg rfl
    ⟨61, rfl, noRecursorForB_sound (tbl := srcMembersG.take 63)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 63)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewIeNeg 96 (by decide))

def famViewSlNil : PolicyFamilyView (envPre 66) where
  ref := 65
  member := mSL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 66) rfl rfl
    [.const 4 [], .const 0 []]).get (by decide)

def ctorViewSlNil : PolicyConstructorView (envPre 66) famViewSlNil mSlNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mSlNil
  resultIndices := ctorIdx mSlNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 66) rfl rfl
    (ctorDom mSlNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorSlNil : IndGroupAdmitted (envPre 66) 66 mSlNil :=
  .constructor famViewSlNil ctorViewSlNil rfl
    ⟨65, rfl, noRecursorForB_sound (tbl := srcMembersG.take 66)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 66)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewSlNil 96 (by decide))

def famViewSlCons : PolicyFamilyView (envPre 67) where
  ref := 65
  member := mSL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 67) rfl rfl
    [.const 4 [], .const 0 []]).get (by decide)

def ctorViewSlCons : PolicyConstructorView (envPre 67) famViewSlCons mSlCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mSlCons
  resultIndices := ctorIdx mSlCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 67) rfl rfl
    (ctorDom mSlCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorSlCons : IndGroupAdmitted (envPre 67) 67 mSlCons :=
  .constructor famViewSlCons ctorViewSlCons rfl
    ⟨65, rfl, noRecursorForB_sound (tbl := srcMembersG.take 67)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 67)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewSlCons 96 (by decide))

def famViewBllNil : PolicyFamilyView (envPre 70) where
  ref := 69
  member := mBLL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 70) rfl rfl
    [.const 34 [], .const 0 []]).get (by decide)

def ctorViewBllNil : PolicyConstructorView (envPre 70) famViewBllNil mBllNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBllNil
  resultIndices := ctorIdx mBllNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 70) rfl rfl
    (ctorDom mBllNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBllNil : IndGroupAdmitted (envPre 70) 70 mBllNil :=
  .constructor famViewBllNil ctorViewBllNil rfl
    ⟨69, rfl, noRecursorForB_sound (tbl := srcMembersG.take 70)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 70)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewBllNil 96 (by decide))

def famViewBllCons : PolicyFamilyView (envPre 71) where
  ref := 69
  member := mBLL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 71) rfl rfl
    [.const 34 [], .const 0 []]).get (by decide)

def ctorViewBllCons : PolicyConstructorView (envPre 71) famViewBllCons mBllCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBllCons
  resultIndices := ctorIdx mBllCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 71) rfl rfl
    (ctorDom mBllCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBllCons : IndGroupAdmitted (envPre 71) 71 mBllCons :=
  .constructor famViewBllCons ctorViewBllCons rfl
    ⟨69, rfl, noRecursorForB_sound (tbl := srcMembersG.take 71)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 71)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewBllCons 96 (by decide))

def famViewFtlNil : PolicyFamilyView (envPre 74) where
  ref := 73
  member := mFTL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 74) rfl rfl
    [.const 38 [], .const 0 []]).get (by decide)

def ctorViewFtlNil : PolicyConstructorView (envPre 74) famViewFtlNil mFtlNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtlNil
  resultIndices := ctorIdx mFtlNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 74) rfl rfl
    (ctorDom mFtlNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorFtlNil : IndGroupAdmitted (envPre 74) 74 mFtlNil :=
  .constructor famViewFtlNil ctorViewFtlNil rfl
    ⟨73, rfl, noRecursorForB_sound (tbl := srcMembersG.take 74)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 74)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewFtlNil 96 (by decide))

def famViewFtlCons : PolicyFamilyView (envPre 75) where
  ref := 73
  member := mFTL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 75) rfl rfl
    [.const 38 [], .const 0 []]).get (by decide)

def ctorViewFtlCons : PolicyConstructorView (envPre 75) famViewFtlCons mFtlCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtlCons
  resultIndices := ctorIdx mFtlCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 75) rfl rfl
    (ctorDom mFtlCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorFtlCons : IndGroupAdmitted (envPre 75) 75 mFtlCons :=
  .constructor famViewFtlCons ctorViewFtlCons rfl
    ⟨73, rfl, noRecursorForB_sound (tbl := srcMembersG.take 75)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 75)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewFtlCons 96 (by decide))

def famViewBlcNil : PolicyFamilyView (envPre 78) where
  ref := 77
  member := mBLC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 78) rfl rfl
    [.const 34 [], .const 4 []]).get (by decide)

def ctorViewBlcNil : PolicyConstructorView (envPre 78) famViewBlcNil mBlcNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlcNil
  resultIndices := ctorIdx mBlcNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 78) rfl rfl
    (ctorDom mBlcNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBlcNil : IndGroupAdmitted (envPre 78) 78 mBlcNil :=
  .constructor famViewBlcNil ctorViewBlcNil rfl
    ⟨77, rfl, noRecursorForB_sound (tbl := srcMembersG.take 78)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 78)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewBlcNil 96 (by decide))

def famViewBlcCons : PolicyFamilyView (envPre 79) where
  ref := 77
  member := mBLC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 79) rfl rfl
    [.const 34 [], .const 4 []]).get (by decide)

def ctorViewBlcCons : PolicyConstructorView (envPre 79) famViewBlcCons mBlcCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlcCons
  resultIndices := ctorIdx mBlcCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 79) rfl rfl
    (ctorDom mBlcCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorBlcCons : IndGroupAdmitted (envPre 79) 79 mBlcCons :=
  .constructor famViewBlcCons ctorViewBlcCons rfl
    ⟨77, rfl, noRecursorForB_sound (tbl := srcMembersG.take 79)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 79)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewBlcCons 96 (by decide))

def famViewSeIntro : PolicyFamilyView (envPre 82) where
  ref := 81
  member := mSEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 82) rfl rfl
    [.const 4 [], .const 4 []]).get (by decide)

def ctorViewSeIntro : PolicyConstructorView (envPre 82) famViewSeIntro mSeIntro where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mSeIntro
  resultIndices := ctorIdx mSeIntro
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 82) rfl rfl
    (ctorDom mSeIntro)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorSeIntro : IndGroupAdmitted (envPre 82) 82 mSeIntro :=
  .constructor famViewSeIntro ctorViewSeIntro rfl
    ⟨81, rfl, noRecursorForB_sound (tbl := srcMembersG.take 82)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 82)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewSeIntro 96 (by decide))

def famViewFteNil : PolicyFamilyView (envPre 85) where
  ref := 84
  member := mFTE
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 85) rfl rfl
    [.const 38 [], .const 4 []]).get (by decide)

def ctorViewFteNil : PolicyConstructorView (envPre 85) famViewFteNil mFteNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFteNil
  resultIndices := ctorIdx mFteNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 85) rfl rfl
    (ctorDom mFteNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorFteNil : IndGroupAdmitted (envPre 85) 85 mFteNil :=
  .constructor famViewFteNil ctorViewFteNil rfl
    ⟨84, rfl, noRecursorForB_sound (tbl := srcMembersG.take 85)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 85)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewFteNil 96 (by decide))

def famViewFteCons : PolicyFamilyView (envPre 86) where
  ref := 84
  member := mFTE
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 86) rfl rfl
    [.const 38 [], .const 4 []]).get (by decide)

def ctorViewFteCons : PolicyConstructorView (envPre 86) famViewFteCons mFteCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFteCons
  resultIndices := ctorIdx mFteCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 86) rfl rfl
    (ctorDom mFteCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorFteCons : IndGroupAdmitted (envPre 86) 86 mFteCons :=
  .constructor famViewFteCons ctorViewFteCons rfl
    ⟨84, rfl, noRecursorForB_sound (tbl := srcMembersG.take 86)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 86)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewFteCons 96 (by decide))

/-! ## §2 constructor admissions: batch 2 -/

def famViewNthBHere : PolicyFamilyView (envPre 89) where
  ref := 88
  member := mNthB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 89) rfl rfl
    [.const 34 [], .const 0 [], .const 4 []]).get (by decide)

def ctorViewNthBHere : PolicyConstructorView (envPre 89) famViewNthBHere mNthBHere where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthBHere
  resultIndices := ctorIdx mNthBHere
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 89) rfl rfl
    (ctorDom mNthBHere)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNthBHere : IndGroupAdmitted (envPre 89) 89 mNthBHere :=
  .constructor famViewNthBHere ctorViewNthBHere rfl
    ⟨88, rfl, noRecursorForB_sound (tbl := srcMembersG.take 89)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 89)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNthBHere 96 (by decide))

def famViewNthBNext : PolicyFamilyView (envPre 90) where
  ref := 88
  member := mNthB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 90) rfl rfl
    [.const 34 [], .const 0 [], .const 4 []]).get (by decide)

def ctorViewNthBNext : PolicyConstructorView (envPre 90) famViewNthBNext mNthBNext where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthBNext
  resultIndices := ctorIdx mNthBNext
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 90) rfl rfl
    (ctorDom mNthBNext)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNthBNext : IndGroupAdmitted (envPre 90) 90 mNthBNext :=
  .constructor famViewNthBNext ctorViewNthBNext rfl
    ⟨88, rfl, noRecursorForB_sound (tbl := srcMembersG.take 90)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 90)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNthBNext 96 (by decide))

def famViewNthFHere : PolicyFamilyView (envPre 93) where
  ref := 92
  member := mNthF
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 93) rfl rfl
    [.const 38 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewNthFHere : PolicyConstructorView (envPre 93) famViewNthFHere mNthFHere where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthFHere
  resultIndices := ctorIdx mNthFHere
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 93) rfl rfl
    (ctorDom mNthFHere)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNthFHere : IndGroupAdmitted (envPre 93) 93 mNthFHere :=
  .constructor famViewNthFHere ctorViewNthFHere rfl
    ⟨92, rfl, noRecursorForB_sound (tbl := srcMembersG.take 93)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 93)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNthFHere 96 (by decide))

def famViewNthFNext : PolicyFamilyView (envPre 94) where
  ref := 92
  member := mNthF
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 94) rfl rfl
    [.const 38 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewNthFNext : PolicyConstructorView (envPre 94) famViewNthFNext mNthFNext where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthFNext
  resultIndices := ctorIdx mNthFNext
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 94) rfl rfl
    (ctorDom mNthFNext)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNthFNext : IndGroupAdmitted (envPre 94) 94 mNthFNext :=
  .constructor famViewNthFNext ctorViewNthFNext rfl
    ⟨92, rfl, noRecursorForB_sound (tbl := srcMembersG.take 94)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 94)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNthFNext 96 (by decide))

def famViewCctB : PolicyFamilyView (envPre 98) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 98) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctB : PolicyConstructorView (envPre 98) famViewCctB mCctB where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctB
  resultIndices := ctorIdx mCctB
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 98) rfl rfl
    (ctorDom mCctB)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCctB : IndGroupAdmitted (envPre 98) 98 mCctB :=
  .constructor famViewCctB ctorViewCctB rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 98)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 98)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctB 96 (by decide))

def famViewCctStr : PolicyFamilyView (envPre 99) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 99) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctStr : PolicyConstructorView (envPre 99) famViewCctStr mCctStr where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctStr
  resultIndices := ctorIdx mCctStr
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 99) rfl rfl
    (ctorDom mCctStr)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCctStr : IndGroupAdmitted (envPre 99) 99 mCctStr :=
  .constructor famViewCctStr ctorViewCctStr rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 99)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 99)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctStr 96 (by decide))

def famViewCctY : PolicyFamilyView (envPre 100) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 100) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctY : PolicyConstructorView (envPre 100) famViewCctY mCctY where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctY
  resultIndices := ctorIdx mCctY
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 100) rfl rfl
    (ctorDom mCctY)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCctY : IndGroupAdmitted (envPre 100) 100 mCctY :=
  .constructor famViewCctY ctorViewCctY rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 100)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 100)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctY 96 (by decide))

def famViewCctL : PolicyFamilyView (envPre 101) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 101) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctL : PolicyConstructorView (envPre 101) famViewCctL mCctL where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctL
  resultIndices := ctorIdx mCctL
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 101) rfl rfl
    (ctorDom mCctL)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCctL : IndGroupAdmitted (envPre 101) 101 mCctL :=
  .constructor famViewCctL ctorViewCctL rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 101)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 101)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctL 96 (by decide))

def famViewCctP : PolicyFamilyView (envPre 102) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 102) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctP : PolicyConstructorView (envPre 102) famViewCctP mCctP where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctP
  resultIndices := ctorIdx mCctP
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 102) rfl rfl
    (ctorDom mCctP)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCctP : IndGroupAdmitted (envPre 102) 102 mCctP :=
  .constructor famViewCctP ctorViewCctP rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 102)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 102)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctP 96 (by decide))

def famViewCctRec : PolicyFamilyView (envPre 104) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 104) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctRec : PolicyConstructorView (envPre 104) famViewCctRec mCctRec where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctRec
  resultIndices := ctorIdx mCctRec
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 104) rfl rfl
    (ctorDom mCctRec)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorCctRec : IndGroupAdmitted (envPre 104) 104 mCctRec :=
  .constructor famViewCctRec ctorViewCctRec rfl
    ⟨96, rfl, noRecursorForB_sound (tbl := srcMembersG.take 104)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 104)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewCctRec 96 (by decide))

def famViewMkBound : PolicyFamilyView (envPre 107) where
  ref := 106
  member := mBCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 107) rfl rfl
    []).get (by decide)

def ctorViewMkBound : PolicyConstructorView (envPre 107) famViewMkBound mMkBound where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mMkBound
  resultIndices := ctorIdx mMkBound
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 107) rfl rfl
    (ctorDom mMkBound)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorMkBound : IndGroupAdmitted (envPre 107) 107 mMkBound :=
  .constructor famViewMkBound ctorViewMkBound rfl
    ⟨106, rfl, noRecursorForB_sound (tbl := srcMembersG.take 107)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 107)
      (by decide) (by decide))
    (fieldUniverseAdmitted_type_of_B ctorViewMkBound uniformType_succ_zero (by decide))
    (ctorFieldsPermitted_of_B ctorViewMkBound 96 (by decide))

def famViewNelNil : PolicyFamilyView (envPre 126) where
  ref := 125
  member := mNEL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 126) rfl rfl
    [.const 4 [], .const 4 []]).get (by decide)

def ctorViewNelNil : PolicyConstructorView (envPre 126) famViewNelNil mNelNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNelNil
  resultIndices := ctorIdx mNelNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 126) rfl rfl
    (ctorDom mNelNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNelNil : IndGroupAdmitted (envPre 126) 126 mNelNil :=
  .constructor famViewNelNil ctorViewNelNil rfl
    ⟨125, rfl, noRecursorForB_sound (tbl := srcMembersG.take 126)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 126)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNelNil 96 (by decide))

def famViewNelCons : PolicyFamilyView (envPre 127) where
  ref := 125
  member := mNEL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 127) rfl rfl
    [.const 4 [], .const 4 []]).get (by decide)

def ctorViewNelCons : PolicyConstructorView (envPre 127) famViewNelCons mNelCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNelCons
  resultIndices := ctorIdx mNelCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 127) rfl rfl
    (ctorDom mNelCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNelCons : IndGroupAdmitted (envPre 127) 127 mNelCons :=
  .constructor famViewNelCons ctorViewNelCons rfl
    ⟨125, rfl, noRecursorForB_sound (tbl := srcMembersG.take 127)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 127)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNelCons 96 (by decide))

def famViewNtbHere : PolicyFamilyView (envPre 130) where
  ref := 129
  member := mNTB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 106 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 130) rfl rfl
    [.const 34 [], .const 0 [], .const 106 []]).get (by decide)

def ctorViewNtbHere : PolicyConstructorView (envPre 130) famViewNtbHere mNtbHere where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNtbHere
  resultIndices := ctorIdx mNtbHere
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 130) rfl rfl
    (ctorDom mNtbHere)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNtbHere : IndGroupAdmitted (envPre 130) 130 mNtbHere :=
  .constructor famViewNtbHere ctorViewNtbHere rfl
    ⟨129, rfl, noRecursorForB_sound (tbl := srcMembersG.take 130)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 130)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNtbHere 96 (by decide))

def famViewNtbNext : PolicyFamilyView (envPre 131) where
  ref := 129
  member := mNTB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 106 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 131) rfl rfl
    [.const 34 [], .const 0 [], .const 106 []]).get (by decide)

def ctorViewNtbNext : PolicyConstructorView (envPre 131) famViewNtbNext mNtbNext where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNtbNext
  resultIndices := ctorIdx mNtbNext
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 131) rfl rfl
    (ctorDom mNtbNext)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorNtbNext : IndGroupAdmitted (envPre 131) 131 mNtbNext :=
  .constructor famViewNtbNext ctorViewNtbNext rfl
    ⟨129, rfl, noRecursorForB_sound (tbl := srcMembersG.take 131)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 131)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewNtbNext 96 (by decide))

def famViewVaB0 : PolicyFamilyView (envPre 134) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 134) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaB0 : PolicyConstructorView (envPre 134) famViewVaB0 mVaB0 where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaB0
  resultIndices := ctorIdx mVaB0
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 134) rfl rfl
    (ctorDom mVaB0)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaB0 : IndGroupAdmitted (envPre 134) 134 mVaB0 :=
  .constructor famViewVaB0 ctorViewVaB0 rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 134)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 134)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaB0 96 (by decide))

def famViewVaB1 : PolicyFamilyView (envPre 135) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 135) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaB1 : PolicyConstructorView (envPre 135) famViewVaB1 mVaB1 where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaB1
  resultIndices := ctorIdx mVaB1
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 135) rfl rfl
    (ctorDom mVaB1)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaB1 : IndGroupAdmitted (envPre 135) 135 mVaB1 :=
  .constructor famViewVaB1 ctorViewVaB1 rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 135)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 135)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaB1 96 (by decide))

def famViewVaI64 : PolicyFamilyView (envPre 136) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 136) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaI64 : PolicyConstructorView (envPre 136) famViewVaI64 mVaI64 where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaI64
  resultIndices := ctorIdx mVaI64
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 136) rfl rfl
    (ctorDom mVaI64)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaI64 : IndGroupAdmitted (envPre 136) 136 mVaI64 :=
  .constructor famViewVaI64 ctorViewVaI64 rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 136)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 136)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaI64 96 (by decide))

def famViewVaStr : PolicyFamilyView (envPre 137) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 137) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaStr : PolicyConstructorView (envPre 137) famViewVaStr mVaStr where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaStr
  resultIndices := ctorIdx mVaStr
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 137) rfl rfl
    (ctorDom mVaStr)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaStr : IndGroupAdmitted (envPre 137) 137 mVaStr :=
  .constructor famViewVaStr ctorViewVaStr rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 137)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 137)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaStr 96 (by decide))

def famViewVaY : PolicyFamilyView (envPre 138) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 138) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaY : PolicyConstructorView (envPre 138) famViewVaY mVaY where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaY
  resultIndices := ctorIdx mVaY
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 138) rfl rfl
    (ctorDom mVaY)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaY : IndGroupAdmitted (envPre 138) 138 mVaY :=
  .constructor famViewVaY ctorViewVaY rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 138)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 138)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaY 96 (by decide))

def famViewVaList : PolicyFamilyView (envPre 139) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 139) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaList : PolicyConstructorView (envPre 139) famViewVaList mVaList where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaList
  resultIndices := ctorIdx mVaList
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 139) rfl rfl
    (ctorDom mVaList)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaList : IndGroupAdmitted (envPre 139) 139 mVaList :=
  .constructor famViewVaList ctorViewVaList rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 139)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 139)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaList 96 (by decide))

def famViewVaPair : PolicyFamilyView (envPre 140) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 140) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaPair : PolicyConstructorView (envPre 140) famViewVaPair mVaPair where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaPair
  resultIndices := ctorIdx mVaPair
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 140) rfl rfl
    (ctorDom mVaPair)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaPair : IndGroupAdmitted (envPre 140) 140 mVaPair :=
  .constructor famViewVaPair ctorViewVaPair rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 140)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 140)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaPair 96 (by decide))

def famViewVaJ : PolicyFamilyView (envPre 141) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 141) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaJ : PolicyConstructorView (envPre 141) famViewVaJ mVaJ where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaJ
  resultIndices := ctorIdx mVaJ
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 141) rfl rfl
    (ctorDom mVaJ)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaJ : IndGroupAdmitted (envPre 141) 141 mVaJ :=
  .constructor famViewVaJ ctorViewVaJ rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 141)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 141)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaJ 96 (by decide))

def famViewVaR : PolicyFamilyView (envPre 142) where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 142) rfl rfl
    [.const 106 [], .const 4 []]).get (by decide)

def ctorViewVaR : PolicyConstructorView (envPre 142) famViewVaR mVaR where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mVaR
  resultIndices := ctorIdx mVaR
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 142) rfl rfl
    (ctorDom mVaR)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def admCtorVaR : IndGroupAdmitted (envPre 142) 142 mVaR :=
  .constructor famViewVaR ctorViewVaR rfl
    ⟨133, rfl, noRecursorForB_sound (tbl := srcMembersG.take 142)
      (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := srcMembersG.take 142)
      (by decide) (by decide))
    (fun _ => .inl (fun _ => rfl))
    (ctorFieldsPermitted_of_B ctorViewVaR 96 (by decide))

end Rcic.Scm.SrcG


#print axioms Rcic.Scm.SrcG.hasTyOfInfer
#print axioms Rcic.Scm.SrcG.hasTyNatExpand
#print axioms Rcic.Scm.SrcG.hasTyLit
#print axioms Rcic.Scm.SrcG.telTyping
#print axioms Rcic.Scm.SrcG.tyConstSort
#print axioms Rcic.Scm.SrcG.famViewAdmN
#print axioms Rcic.Scm.SrcG.admFamN
#print axioms Rcic.Scm.SrcG.famViewAdmBytes
#print axioms Rcic.Scm.SrcG.admFamBytes
#print axioms Rcic.Scm.SrcG.famViewAdmRefT
#print axioms Rcic.Scm.SrcG.admFamRefT
#print axioms Rcic.Scm.SrcG.famViewAdmDA
#print axioms Rcic.Scm.SrcG.admFamDA
#print axioms Rcic.Scm.SrcG.famViewAdmI
#print axioms Rcic.Scm.SrcG.admFamI
#print axioms Rcic.Scm.SrcG.famViewAdmBL
#print axioms Rcic.Scm.SrcG.admFamBL
#print axioms Rcic.Scm.SrcG.famViewAdmFT
#print axioms Rcic.Scm.SrcG.admFamFT
#print axioms Rcic.Scm.SrcG.famViewAdmLt
#print axioms Rcic.Scm.SrcG.admFamLt
#print axioms Rcic.Scm.SrcG.famViewAdmBC
#print axioms Rcic.Scm.SrcG.admFamBC
#print axioms Rcic.Scm.SrcG.famViewAdmDM10
#print axioms Rcic.Scm.SrcG.admFamDM10
#print axioms Rcic.Scm.SrcG.famViewAdmND
#print axioms Rcic.Scm.SrcG.admFamND
#print axioms Rcic.Scm.SrcG.famViewAdmNEA
#print axioms Rcic.Scm.SrcG.admFamNEA
#print axioms Rcic.Scm.SrcG.famViewAdmIEA
#print axioms Rcic.Scm.SrcG.admFamIEA
#print axioms Rcic.Scm.SrcG.famViewAdmSL
#print axioms Rcic.Scm.SrcG.admFamSL
#print axioms Rcic.Scm.SrcG.famViewAdmBLL
#print axioms Rcic.Scm.SrcG.admFamBLL
#print axioms Rcic.Scm.SrcG.famViewAdmFTL
#print axioms Rcic.Scm.SrcG.admFamFTL
#print axioms Rcic.Scm.SrcG.famViewAdmBLC
#print axioms Rcic.Scm.SrcG.admFamBLC
#print axioms Rcic.Scm.SrcG.famViewAdmSEA
#print axioms Rcic.Scm.SrcG.admFamSEA
#print axioms Rcic.Scm.SrcG.famViewAdmFTE
#print axioms Rcic.Scm.SrcG.admFamFTE
#print axioms Rcic.Scm.SrcG.famViewAdmNthB
#print axioms Rcic.Scm.SrcG.admFamNthB
#print axioms Rcic.Scm.SrcG.famViewAdmNthF
#print axioms Rcic.Scm.SrcG.admFamNthF
#print axioms Rcic.Scm.SrcG.famViewAdmCCT
#print axioms Rcic.Scm.SrcG.admFamCCT
#print axioms Rcic.Scm.SrcG.famViewAdmBCT
#print axioms Rcic.Scm.SrcG.admFamBCT
#print axioms Rcic.Scm.SrcG.famViewAdmNEL
#print axioms Rcic.Scm.SrcG.admFamNEL
#print axioms Rcic.Scm.SrcG.famViewAdmNTB
#print axioms Rcic.Scm.SrcG.admFamNTB
#print axioms Rcic.Scm.SrcG.famViewAdmValueAt
#print axioms Rcic.Scm.SrcG.admFamValueAt
#print axioms Rcic.Scm.SrcG.famViewN1
#print axioms Rcic.Scm.SrcG.famViewN2
#print axioms Rcic.Scm.SrcG.ctorViewZero
#print axioms Rcic.Scm.SrcG.admCtorZero
#print axioms Rcic.Scm.SrcG.ctorViewSucc
#print axioms Rcic.Scm.SrcG.admCtorSucc
#print axioms Rcic.Scm.SrcG.foldEnv
#print axioms Rcic.Scm.SrcG.foldEnv_members
#print axioms Rcic.Scm.SrcG.noRecursorForB
#print axioms Rcic.Scm.SrcG.noRecursorForB_sound
#print axioms Rcic.Scm.SrcG.ctorContiguousB
#print axioms Rcic.Scm.SrcG.ctorContiguousB_sound
#print axioms Rcic.Scm.SrcG.ctorCensusB
#print axioms Rcic.Scm.SrcG.ctorCensusB_sound
#print axioms Rcic.Scm.SrcG.noRec_table1
#print axioms Rcic.Scm.SrcG.contig_table2
#print axioms Rcic.Scm.SrcG.census_table3
#print axioms Rcic.Scm.SrcG.inferSpine
#print axioms Rcic.Scm.SrcG.telTypingAuto
#print axioms Rcic.Scm.SrcG.fieldPermittedB
#print axioms Rcic.Scm.SrcG.fieldPermitted_of_B
#print axioms Rcic.Scm.SrcG.ctorFieldsPermittedB
#print axioms Rcic.Scm.SrcG.ctorFieldsPermitted_of_B
#print axioms Rcic.Scm.SrcG.leNB
#print axioms Rcic.Scm.SrcG.leN_of_leNB
#print axioms Rcic.Scm.SrcG.fieldUniverseAdmitted_type_of_B
#print axioms Rcic.Scm.SrcG.famViewCCTAt
#print axioms Rcic.Scm.SrcG.famViewDM51
#print axioms Rcic.Scm.SrcG.ctorViewCctI
#print axioms Rcic.Scm.SrcG.admCtorCctI
#print axioms Rcic.Scm.SrcG.ctorViewDmBase
#print axioms Rcic.Scm.SrcG.admCtorDmBase
#print axioms Rcic.Scm.SrcG.ctorViewCctSum
#print axioms Rcic.Scm.SrcG.admCtorCctSum
#print axioms Rcic.Scm.SrcG.noFamilyInIndicesB_of
#print axioms Rcic.Scm.SrcG.admCtorBnil
#print axioms Rcic.Scm.SrcG.admCtorBcons
#print axioms Rcic.Scm.SrcG.admCtorMkRef
#print axioms Rcic.Scm.SrcG.admCtorDaI
#print axioms Rcic.Scm.SrcG.admCtorDaB
#print axioms Rcic.Scm.SrcG.admCtorDaS
#print axioms Rcic.Scm.SrcG.admCtorDaY
#print axioms Rcic.Scm.SrcG.admCtorDaLB
#print axioms Rcic.Scm.SrcG.admCtorIPos
#print axioms Rcic.Scm.SrcG.admCtorINegS
#print axioms Rcic.Scm.SrcG.admCtorBlNil
#print axioms Rcic.Scm.SrcG.admCtorBlCons
#print axioms Rcic.Scm.SrcG.admCtorFtNil
#print axioms Rcic.Scm.SrcG.admCtorFtCons
#print axioms Rcic.Scm.SrcG.admCtorLtBase
#print axioms Rcic.Scm.SrcG.admCtorLtStep
#print axioms Rcic.Scm.SrcG.admCtorCatNil
#print axioms Rcic.Scm.SrcG.admCtorCatCons
#print axioms Rcic.Scm.SrcG.admCtorDmStep
#print axioms Rcic.Scm.SrcG.admCtorNdBase
#print axioms Rcic.Scm.SrcG.admCtorNdStep
#print axioms Rcic.Scm.SrcG.admCtorNeIntro
#print axioms Rcic.Scm.SrcG.admCtorIePos
#print axioms Rcic.Scm.SrcG.admCtorIeNeg
#print axioms Rcic.Scm.SrcG.admCtorSlNil
#print axioms Rcic.Scm.SrcG.admCtorSlCons
#print axioms Rcic.Scm.SrcG.admCtorBllNil
#print axioms Rcic.Scm.SrcG.admCtorBllCons
#print axioms Rcic.Scm.SrcG.admCtorFtlNil
#print axioms Rcic.Scm.SrcG.admCtorFtlCons
#print axioms Rcic.Scm.SrcG.admCtorBlcNil
#print axioms Rcic.Scm.SrcG.admCtorBlcCons
#print axioms Rcic.Scm.SrcG.admCtorSeIntro
#print axioms Rcic.Scm.SrcG.admCtorFteNil
#print axioms Rcic.Scm.SrcG.admCtorFteCons
#print axioms Rcic.Scm.SrcG.admCtorNthBHere
#print axioms Rcic.Scm.SrcG.admCtorNthBNext
#print axioms Rcic.Scm.SrcG.admCtorNthFHere
#print axioms Rcic.Scm.SrcG.admCtorNthFNext
#print axioms Rcic.Scm.SrcG.admCtorCctB
#print axioms Rcic.Scm.SrcG.admCtorCctStr
#print axioms Rcic.Scm.SrcG.admCtorCctY
#print axioms Rcic.Scm.SrcG.admCtorCctL
#print axioms Rcic.Scm.SrcG.admCtorCctP
#print axioms Rcic.Scm.SrcG.admCtorCctRec
#print axioms Rcic.Scm.SrcG.admCtorMkBound
#print axioms Rcic.Scm.SrcG.admCtorNelNil
#print axioms Rcic.Scm.SrcG.admCtorNelCons
#print axioms Rcic.Scm.SrcG.admCtorNtbHere
#print axioms Rcic.Scm.SrcG.admCtorNtbNext
#print axioms Rcic.Scm.SrcG.admCtorVaB0
#print axioms Rcic.Scm.SrcG.admCtorVaB1
#print axioms Rcic.Scm.SrcG.admCtorVaI64
#print axioms Rcic.Scm.SrcG.admCtorVaStr
#print axioms Rcic.Scm.SrcG.admCtorVaY
#print axioms Rcic.Scm.SrcG.admCtorVaList
#print axioms Rcic.Scm.SrcG.admCtorVaPair
#print axioms Rcic.Scm.SrcG.admCtorVaJ
#print axioms Rcic.Scm.SrcG.admCtorVaR
