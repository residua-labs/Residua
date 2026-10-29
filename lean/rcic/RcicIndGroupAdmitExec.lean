/-
Executable inductive-group admission (IA-028 W3.1).

A finite slot table is accepted only when its order is the 05 §3 block
and the recursor's stored type is syntactically the `policyRecursorType`
rebuilt from views at a recovered `nparams`. `IndGroupAdmitted` is packaged
inside these checkers, after the Bool reflections, and `acceptIndGroup?`
ends at `EG010T_group_accepted`. `closure_claim` 0.
-/
import rcic.RcicEGTypedGroup
import rcic.ScmSrcGroupsAdm
import rcic.RcicFixtures
import rcic.RcicPinEqEraseWf
import rcic.RcicIotaSRRowsTel
import rcic.RcicIARecUnique

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace Rcic.Declarative

open Rcic.Scm.SrcG (foldEnv foldEnv_members noRecursorForB noRecursorForB_sound
  ctorContiguousB ctorContiguousB_sound ctorCensusB ctorCensusB_sound
  fieldUniverseAdmitted_type_of_B ctorFieldsPermittedB ctorFieldsPermitted_of_B
  leNB noFamilyInIndicesB_of sortTyAtC)

/-! ## Telescopes and spines -/

def splitPi (n : Nat) (T : Expr Nat) : Option (List (Expr Nat) × Expr Nat) :=
  peelPis n T

theorem splitPi_sound (n : Nat) (T : Expr Nat) {ds : List (Expr Nat)} {b : Expr Nat}
    (h : splitPi n T = some (ds, b)) : T = policyPi ds b :=
  policyPi_of_peelPis n T (ds := ds) (b := b) (by simpa [splitPi] using h)

def unfoldApps (e : Expr Nat) : Expr Nat × List (Expr Nat) :=
  appsSpine e

theorem unfoldApps_sound (e : Expr Nat) :
    foldApps (unfoldApps e).1 (unfoldApps e).2 = e := by
  simpa [unfoldApps] using foldApps_appsSpine e

theorem foldApps_not_pi (f : Expr Nat) (xs : List (Expr Nat))
    (hf : match f with | .pi _ _ => False | _ => True) :
    ∀ A B, foldApps f xs ≠ .pi A B :=
  foldApps_notPi xs (h := f) (fun A B h => by
    cases f with
    | pi _ _ => exact hf
    | bvar _ => cases h
    | sort _ => cases h
    | const _ _ => cases h
    | app _ _ => cases h
    | lam _ _ => cases h
    | letE _ _ _ => cases h
    | lit _ => cases h)

/-! ## Bounded structural inference (sort / bvar / const / app / lit) -/

def levelWfB (n : Nat) (l : Level) : Bool :=
  match eval (fun _ => none) l with
  | none => true
  | some k => decide (k < n)

theorem levelWf_one {n : Nat} {l : Level} (h : levelWfB n l = true) :
    ∃ k, eval (fun _ => none) l = none ∨ k < n := by
  unfold levelWfB at h
  cases he : eval (fun _ => none) l with
  | none => exact ⟨0, Or.inl rfl⟩
  | some k =>
      rw [he] at h
      simp only [decide_eq_true_eq] at h
      exact ⟨k, Or.inr h⟩

theorem levelsWf_of {n : Nat} {ls : List Level}
    (h : ls.all (levelWfB n) = true) :
    ∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n := by
  intro l hl
  exact levelWf_one (List.all_eq_true.mp h l hl)

def sameMember (a b : CheckedMember) : Bool :=
  decide (a.mclass = b.mclass) && decide (a.arity = b.arity) &&
    decide (a.mtype = b.mtype) &&
    match a.body, b.body with
    | none, none => true
    | some x, some y => decide (x = y)
    | _, _ => false

theorem sameMember_eq {a b : CheckedMember} (h : sameMember a b = true) : a = b := by
  cases a with
  | mk ca aa ta ba =>
    cases b with
    | mk cb ab tb bb =>
      simp only [sameMember, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hc, ha⟩, ht⟩, hb⟩ := h
      subst hc; subst ha; subst ht
      cases ba <;> cases bb <;> simp_all

structure SortHit (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) where
  l : Level
  bd : levelBounded n l = true
  ty : HasTy E n Γ e (.sort l)

mutual
def exprInfer (fuel : Nat) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) :
    Option (Σ T, HasTy E n Γ e T) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .sort l => some ⟨.sort (.succ l), HasTy.sort Γ l⟩
    | .bvar i =>
        match h : lookupType Γ i with
        | some A => some ⟨A, HasTy.bvar Γ i A h⟩
        | none => none
    | .const r ls =>
        match hm : E.members r with
        | some m =>
            if har : ls.length = m.arity then
              if hw : ls.all (levelWfB n) = true then
                some ⟨instantiateLevels ls m.mtype,
                  HasTy.const Γ r ls m hm har (levelsWf_of hw)⟩
              else none
            else none
        | none => none
    | .lit k =>
        if k ≤ fuel then
          match exprInfer fuel E n Γ (natExpand k) with
          | some ⟨T, h⟩ => some ⟨T, HasTy.lit Γ k T h⟩
          | none => none
        else none
    | .app f a =>
        match exprInfer fuel E n Γ f with
        | some ⟨.pi A B, hf⟩ =>
            match exprCheck fuel E n Γ a A with
            | some ha => some ⟨instantiate0 a B, HasTy.app Γ f a A B hf ha⟩
            | none => none
        | _ => none
    | _ => none

def exprCheck (fuel : Nat) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat) :
    Option (HasTy E n Γ e T) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match exprInfer fuel E n Γ e with
    | some ⟨T', h⟩ => if he : T' = T then some (he ▸ h) else none
    | none => none
end

def inferSort (fuel : Nat) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) :
    Option (SortHit E n Γ e) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .sort l =>
        let lvl := Level.succ l
        if hb : levelBounded n lvl = true then
          some ⟨lvl, hb, HasTy.sort Γ l⟩
        else none
    | .bvar i =>
        match hl : lookupType Γ i with
        | some (.sort l) =>
            if hb : levelBounded n l = true then
              some ⟨l, hb, HasTy.bvar Γ i (.sort l) hl⟩
            else none
        | _ => none
    | .const r ls =>
        match hm : E.members r with
        | some m =>
            match hT : instantiateLevels ls m.mtype with
            | .sort l =>
                if har : ls.length = m.arity then
                  if hw : ls.all (levelWfB n) = true then
                    if hb : levelBounded n l = true then
                      some ⟨l, hb, hT ▸ HasTy.const Γ r ls m hm har (levelsWf_of hw)⟩
                    else none
                  else none
                else none
            | _ => none
        | none => none
    | .app f a =>
        match exprInfer (fuel + 1) E n Γ (.app f a) with
        | some ⟨.sort l, h⟩ =>
            if hb : levelBounded n l = true then
              some ⟨l, hb, h⟩
            else none
        | _ => none
    | _ => none

def sortLevel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e : Expr Nat}
    (o : Option (SortHit E n Γ e)) : Level :=
  match o with
  | some s => s.l
  | none => .zero

@[simp] theorem sortLevel_some {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e : Expr Nat}
    (s : SortHit E n Γ e) : sortLevel (some s) = s.l := rfl

def telOf (fuel : Nat) (E : ResolvedEnv) (n : Nat) (doms : List (Expr Nat)) :
    Option (PolicyTelescopeTyping E n doms) :=
  let inf (k : Nat) (hk : k < doms.length) :=
    inferSort fuel E n (policyPrefixContext doms k) (doms[k]'hk)
  if hall : (List.range doms.length).all (fun k =>
      if hk : k < doms.length then (inf k hk).isSome else false) = true then
    some {
      levels := fun i => sortLevel (inf i.val i.isLt)
      bounded := fun i => by
        have hb := List.all_eq_true.mp hall i.val (List.mem_range.mpr i.isLt)
        simp only [dif_pos i.isLt] at hb
        cases hs : inf i.val i.isLt with
        | none =>
            rw [hs] at hb
            simp at hb
        | some s =>
            change levelBounded n (sortLevel (inf i.val i.isLt)) = true
            rw [hs, sortLevel_some]
            exact s.bd
      hasType := fun i => by
        have hb := List.all_eq_true.mp hall i.val (List.mem_range.mpr i.isLt)
        simp only [dif_pos i.isLt] at hb
        cases hs : inf i.val i.isLt with
        | none =>
            rw [hs] at hb
            simp at hb
        | some s =>
            change HasTy E n (policyPrefixContext doms i.val) (doms[i.val]'i.isLt)
              (.sort (sortLevel (inf i.val i.isLt)))
            rw [hs, sortLevel_some]
            exact s.ty
    }
  else none

/-! ## Views -/

def familyViewAt (E : ResolvedEnv) (fuel np ref : Nat) (m : CheckedMember) :
    Option (PolicyFamilyView E) :=
  if hc : m.mclass = .inductiveM then
    match hm : E.members ref with
    | some m' =>
        if hs : sameMember m' m = true then
          match splitPi (piCount m.mtype) m.mtype with
          | some (doms, .sort u) =>
              if hle : np ≤ doms.length then
                if hb : levelBounded m.arity u = true then
                  let params := doms.take np
                  let idxs := doms.drop np
                  let expected := policyPi (params ++ idxs) (.sort u)
                  if ht : m.mtype = expected then
                    match telOf fuel E m.arity (params ++ idxs) with
                    | some tel =>
                        some {
                          ref := ref
                          member := m
                          present := by
                            have hm' : m' = m := sameMember_eq hs
                            simpa [hm'] using hm
                          hasClass := hc
                          parameters := params
                          indices := idxs
                          resultLevel := u
                          resultBounded := hb
                          storedType := ht
                          domainsTyped := tel
                        }
                    | none => none
                  else none
                else none
              else none
          | _ => none
        else none
    | none => none
  else none

def buildFamilyView? (tbl : List (Nat × CheckedMember))
    (hnd : (tbl.map (·.1)).Nodup) (fuel np ref : Nat) (m : CheckedMember) :
    Option (PolicyFamilyView (foldEnv tbl)) :=
  let _ := hnd
  familyViewAt (foldEnv tbl) fuel np ref m

def mirrorAll (xs ys : List (Expr Nat)) : Bool :=
  decide (xs.length = ys.length) &&
    (List.range xs.length).all fun i =>
      if hx : i < xs.length then
        if hy : i < ys.length then decide (xs[i] = ys[i]) else false
      else false

theorem mirrorAll_len {xs ys : List (Expr Nat)} (h : mirrorAll xs ys = true) :
    xs.length = ys.length := by
  simp only [mirrorAll, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem mirrorAll_of {xs ys : List (Expr Nat)} (h : mirrorAll xs ys = true) :
    ∀ i : Fin xs.length,
      xs[i] = ys[i.val]'(by rw [← mirrorAll_len h]; exact i.isLt) := by
  intro i
  have hlen := mirrorAll_len h
  simp only [mirrorAll, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb := List.all_eq_true.mp h.2 i.val (List.mem_range.mpr i.isLt)
  rw [dif_pos i.isLt] at hb
  have hy : i.val < ys.length := by rw [← hlen]; exact i.isLt
  rw [dif_pos hy] at hb
  exact of_decide_eq_true hb

def buildCtorView? {E : ResolvedEnv} (fuel : Nat) (fam : PolicyFamilyView E)
    (m : CheckedMember) : Option (PolicyConstructorView E fam m) :=
  if hc : m.mclass = .constructorM then
    if har : m.arity = fam.member.arity then
      let np := fam.parameters.length
      match splitPi (piCount m.mtype) m.mtype with
      | some (doms, body) =>
          if hnp : np ≤ doms.length then
            let params := doms.take np
            let fields := doms.drop np
            if hmir : mirrorAll params fam.parameters = true then
              match unfoldApps body with
              | (.const r ls, args) =>
                  if hr : r = fam.ref then
                    if hls : ls = policyFamilyLevels fam then
                      let ploc := policyParameterLocals params.length fields.length
                      if hargs : args = ploc ++ args.drop ploc.length then
                        let ridx := args.drop ploc.length
                        if hq : ridx.length = fam.indices.length then
                          if hpre : args.take ploc.length = ploc then
                            if hnof : ridx.all (fun e => !occursConst fam.ref e) = true then
                              let expected := policyPi (params ++ fields)
                                (foldApps (.const fam.ref (policyFamilyLevels fam))
                                  (ploc ++ ridx))
                              if ht : m.mtype = expected then
                                match telOf fuel E fam.member.arity (params ++ fields) with
                                | some tel =>
                                    some {
                                      hasClass := hc
                                      arity := har
                                      parameters := params
                                      fields := fields
                                      resultIndices := ridx
                                      parameterCount := mirrorAll_len hmir
                                      indexCount := hq
                                      storedType := by
                                        simpa [unfoldApps, hr, hls] using ht
                                      domainsTyped := tel
                                      parameterMirrors := by
                                        intro i
                                        have he := mirrorAll_of hmir i
                                        -- `Conv.refl` is `(Γ) (a)`; `← he` makes both sides `params[i]`.
                                        rw [← he]
                                        exact Conv.refl
                                          (policyPrefixContext params i.val)
                                          params[i]
                                      noFamilyInIndices := noFamilyInIndicesB_of hnof
                                    }
                                | none => none
                              else none
                            else none
                          else none
                        else none
                      else none
                    else none
                  else none
              | _ => none
            else none
          else none
      | none => none
    else none
  else none

def CtorViews {E : ResolvedEnv} (fam : PolicyFamilyView E) :
    List CheckedMember → Type
  | [] => Unit
  | m :: ms => PolicyConstructorView E fam m × CtorViews fam ms

def ctorViewsFuel {E : ResolvedEnv} (fuel : Nat) (fam : PolicyFamilyView E) :
    (ms : List CheckedMember) → Option (CtorViews fam ms)
  | [] => some ()
  | m :: ms =>
      match buildCtorView? fuel fam m, ctorViewsFuel fuel fam ms with
      | some v, some vs => some (v, vs)
      | _, _ => none

def ctorViewAt {E : ResolvedEnv} {fam : PolicyFamilyView E} :
    (ms : List CheckedMember) → CtorViews fam ms →
    (i : Fin ms.length) → PolicyConstructorView E fam ms[i]
  | [], _, i => i.elim0
  | _ :: _, (v, _), ⟨0, _⟩ => v
  | _ :: ms, (_, vs), ⟨j + 1, hj⟩ =>
      ctorViewAt ms vs ⟨j, Nat.lt_of_succ_lt_succ hj⟩

def ctorViews (fuel : Nat) {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (ms : List CheckedMember) :
    Option ((i : Fin ms.length) → PolicyConstructorView E fam ms[i]) :=
  (ctorViewsFuel fuel fam ms).map fun vs i => ctorViewAt ms vs i

/-- Hidden-data Prop (`k = 1`, fields not safe) is refused: the pins are
UniformType or a field-free Prop singleton, and this checker does not invent
`¬ AllFieldsSafe`. -/
def selectElimination? (u : Level) (k : Nat) (safe : Bool) : Option EliminationPolicy :=
  match classifyUniverse u with
  | .mixed => none
  | .uniformType => some .anySort
  | .uniformProp =>
      if k = 0 then some .anySort
      else if k = 1 then
        if safe then some .anySort else none
      else some .propOnly

def fieldSafeB {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) (j : Fin c.fields.length) : Bool :=
  levelUniformZero (c.fieldLevel j) ||
    decide (Expr.bvar (c.fields.length - 1 - j.val) ∈ c.resultIndices)

def ctorSafeB {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) : Bool :=
  (List.range c.fields.length).all fun j =>
    if hj : j < c.fields.length then fieldSafeB c ⟨j, hj⟩ else false

theorem fieldSafe_of {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) (j : Fin c.fields.length)
    (h : fieldSafeB c j = true) : c.FieldSafe j := by
  unfold fieldSafeB at h
  cases hz : levelUniformZero (c.fieldLevel j) with
  | true =>
      left
      exact (levelUniformZero_iff _).mp hz
  | false =>
      right
      rw [hz, Bool.false_or] at h
      exact of_decide_eq_true h

theorem ctorSafe_of {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) (h : ctorSafeB c = true) : c.AllFieldsSafe := by
  intro j
  unfold ctorSafeB at h
  have hb := List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt)
  rw [dif_pos j.isLt] at hb
  exact fieldSafe_of c j hb

def viewsSafeB {E : ResolvedEnv} {fam : PolicyFamilyView E} {ms : List CheckedMember}
    (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i]) : Bool :=
  (List.range ms.length).all fun j =>
    if hj : j < ms.length then ctorSafeB (views ⟨j, hj⟩) else false

theorem viewsSafe_of {E : ResolvedEnv} {fam : PolicyFamilyView E} {ms : List CheckedMember}
    (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i])
    (h : viewsSafeB views = true) : ∀ i, (views i).AllFieldsSafe := by
  intro i
  unfold viewsSafeB at h
  have hb := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  rw [dif_pos i.isLt] at hb
  exact ctorSafe_of (views i) hb

def fieldUnivB {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) : Bool :=
  match classifyUniverse fam.resultLevel with
  | .uniformProp => true
  | .uniformType =>
      (List.range c.fields.length).all fun j =>
        if hj : j < c.fields.length then
          leNB (c.fieldLevel ⟨j, hj⟩) fam.resultLevel
        else false
  | .mixed => false

/-! ## Uniqueness of the nparams that rebuilds the stored recursor -/

def recResult {E : ResolvedEnv} (fam : PolicyFamilyView E) (k : Nat) : Expr Nat :=
  let q := fam.indices.length
  foldApps (.bvar (k + q + 1))
    ((List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])

def recMajor {E : ResolvedEnv} (fam : PolicyFamilyView E) (k : Nat) : Expr Nat :=
  let q := fam.indices.length
  foldApps (.const fam.ref (policyFamilyLevels fam))
    (policyParameterLocals fam.parameters.length (k + 1 + q) ++ policyLocals q)

def recDoms {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (mins : List (Expr Nat)) (pol : EliminationPolicy) : List (Expr Nat) :=
  let k := mins.length
  fam.parameters ++ [policyMotiveType fam pol] ++ mins ++
    (fam.indices.mapIdx (fun j T => lift j (k + 1) T)) ++ [recMajor fam k]

theorem policyRecursorType_as_pi {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (mins : List (Expr Nat)) (pol : EliminationPolicy) :
    policyRecursorType fam mins pol =
      policyPi (recDoms fam mins pol) (recResult fam mins.length) := by
  simp only [policyRecursorType, recDoms, recMajor, recResult, policyPi_append,
    policyPi]

theorem policyPi_inj {xs ys : List (Expr Nat)} {b b' : Expr Nat}
    (hb : ∀ A B, b ≠ .pi A B) (hb' : ∀ A B, b' ≠ .pi A B)
    (h : policyPi xs b = policyPi ys b') : xs = ys ∧ b = b' :=
  policyPi_inj_notPi xs ys hb hb' h

def bvarIx : Expr Nat → Option Nat
  | .bvar i => some i
  | _ => none

@[simp] theorem bvarIx_bvar (i : Nat) : bvarIx (.bvar i) = some i := rfl

def idxList (np q k : Nat) : List Nat :=
  (List.range np).reverse.map (fun i => i + (k + 1 + q)) ++ (List.range q).reverse

theorem idxList_mem (np q k m : Nat) :
    m ∈ idxList np q k ↔ m < q ∨ (k + 1 + q ≤ m ∧ m < k + 1 + q + np) := by
  simp only [idxList, List.mem_append, List.mem_reverse, List.mem_map, List.mem_range]
  constructor
  · intro h
    rcases h with ⟨i, hi, rfl⟩ | hq
    · refine Or.inr ⟨?_, ?_⟩
      · omega
      · omega
    · exact Or.inl hq
  · intro h
    rcases h with hq | ⟨hle, hlt⟩
    · exact Or.inr hq
    · refine Or.inl ⟨m - (k + 1 + q), ?_, ?_⟩
      · omega
      · omega

theorem idxList_q_not_mem (np q k : Nat) : q ∉ idxList np q k := by
  intro h
  rw [idxList_mem] at h
  rcases h with h | h
  · omega
  · omega

theorem idxList_inj {np q np' q' k : Nat}
    (h : idxList np q k = idxList np' q' k) : np = np' ∧ q = q' := by
  have hq : q = q' := by
    cases Nat.lt_or_ge q q' with
    | inl hlt =>
        have hmem : q ∈ idxList np' q' k := (idxList_mem _ _ _ _).mpr (Or.inl hlt)
        rw [← h] at hmem
        exact absurd hmem (idxList_q_not_mem _ _ _)
    | inr hge =>
        cases Nat.lt_or_ge q' q with
        | inl hlt =>
            have hmem : q' ∈ idxList np q k := (idxList_mem _ _ _ _).mpr (Or.inl hlt)
            rw [h] at hmem
            exact absurd hmem (idxList_q_not_mem _ _ _)
        | inr hge' =>
            exact Nat.le_antisymm hge' hge
  have hlen : np + q = np' + q' := by
    have := congrArg List.length h
    simp only [idxList, List.length_append, List.length_reverse, List.length_map,
      List.length_range] at this
    exact this
  exact ⟨by omega, hq⟩

theorem spine_fold (f : Expr Nat) (xs : List (Expr Nat)) :
    appsSpine (foldApps f xs) = ((appsSpine f).1, (appsSpine f).2 ++ xs) :=
  appsSpine_foldApps f xs

theorem spine_fold_const (r : Nat) (U : List Level) (args : List (Expr Nat)) :
    appsSpine (foldApps (.const r U) args) = (.const r U, args) :=
  appsSpine_foldApps_const r U args

theorem map_bvarIx_shift (shift : Nat) (l : List Nat) :
    (l.map (fun i => Expr.bvar (i + shift))).map bvarIx =
      l.map (fun i => some (i + shift)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, bvarIx_bvar]

theorem map_bvarIx_plain (l : List Nat) :
    (l.map Expr.bvar).map bvarIx = l.map some := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, bvarIx_bvar]

theorem bvarIx_comp_shift (shift : Nat) :
    bvarIx ∘ (fun i : Nat => Expr.bvar (i + shift)) = some ∘ (fun i => i + shift) := by
  funext i
  simp [bvarIx_bvar]

theorem bvarIx_comp_plain : bvarIx ∘ Expr.bvar = some := by
  funext i
  simp [bvarIx_bvar]

theorem args_idx (np q k : Nat) :
    (policyParameterLocals np (k + 1 + q) ++ policyLocals q).map bvarIx =
      (idxList np q k).map some := by
  simp only [policyParameterLocals, policyLocals, idxList, List.map_append,
    List.map_reverse, List.map_map, bvarIx_comp_shift, bvarIx_comp_plain]

theorem map_some_inj {l₁ l₂ : List Nat} (h : l₁.map some = l₂.map some) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ <;> simp_all
  | cons a l ih =>
      cases l₂ with
      | nil => simp at h
      | cons b l₂ =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hab, hrest⟩ := h
          injection hab with hab
          subst hab
          exact congrArg (a :: ·) (ih hrest)

theorem major_np_inj {r : Nat} {U : List Level} {np q np' q' k : Nat}
    (h : foldApps (.const r U) (policyParameterLocals np (k + 1 + q) ++ policyLocals q) =
        foldApps (.const r U) (policyParameterLocals np' (k + 1 + q') ++ policyLocals q')) :
    np = np' ∧ q = q' := by
  have hs := congrArg appsSpine h
  simp only [spine_fold_const] at hs
  injection hs with _ hargs
  have hmap := congrArg (List.map bvarIx) hargs
  simp only [args_idx] at hmap
  exact idxList_inj (map_some_inj hmap)

theorem getLast?_snoc {α : Type} (xs : List α) (a : α) :
    (xs ++ [a]).getLast? = some a :=
  List.getLast?_concat xs

theorem checked_nparams_unique {E E' : ResolvedEnv}
    {fam : PolicyFamilyView E} {fam' : PolicyFamilyView E'}
    {mins mins' : List (Expr Nat)} {p p' : EliminationPolicy}
    (hk : mins.length = mins'.length)
    (h : policyRecursorType fam mins p = policyRecursorType fam' mins' p') :
    fam.parameters.length = fam'.parameters.length := by
  have hb : ∀ A B, recResult fam mins.length ≠ .pi A B := by
    intro A B he
    exact foldApps_not_pi (.bvar (mins.length + fam.indices.length + 1))
      ((List.range fam.indices.length).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])
      (by simp) A B (by simpa [recResult] using he)
  have hb' : ∀ A B, recResult fam' mins'.length ≠ .pi A B := by
    intro A B he
    exact foldApps_not_pi (.bvar (mins'.length + fam'.indices.length + 1))
      ((List.range fam'.indices.length).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])
      (by simp) A B (by simpa [recResult] using he)
  have hpi : policyPi (recDoms fam mins p) (recResult fam mins.length) =
      policyPi (recDoms fam' mins' p') (recResult fam' mins'.length) := by
    simpa [policyRecursorType_as_pi] using h
  obtain ⟨hdoms, _⟩ := policyPi_inj hb hb' hpi
  have hlast : recMajor fam mins.length = recMajor fam' mins'.length := by
    have hs := congrArg List.getLast? hdoms
    simp only [recDoms, getLast?_snoc] at hs
    exact Option.some.inj hs
  have hspine := congrArg appsSpine hlast
  simp only [recMajor, spine_fold_const] at hspine
  injection hspine with _hconst hargs
  have hmap := congrArg (List.map bvarIx) hargs
  simp only [args_idx, hk] at hmap
  exact (idxList_inj (map_some_inj hmap)).1

/-! ## Recursor packaging -/

def shapesAt {E : ResolvedEnv} {fam : PolicyFamilyView E} {ms : List CheckedMember}
    (fuel : Nat) (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i]) :
    Option ((i : Fin ms.length) → List FieldShape) :=
  if hall : (List.range ms.length).all (fun j =>
      if hj : j < ms.length then
        (fieldShapesFuel E fuel fam.ref fam.member.arity fam.parameters.length
          fam.indices.length fam.parameters.length (views ⟨j, hj⟩).fields).isSome
      else false) = true then
    some (fun i =>
      match fieldShapesFuel E fuel fam.ref fam.member.arity fam.parameters.length
          fam.indices.length fam.parameters.length (views i).fields with
      | some s => s
      | none => [])
  else none

theorem shapesAt_apply {E : ResolvedEnv} {fam : PolicyFamilyView E}
    {ms : List CheckedMember} {fuel : Nat}
    {views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i]}
    {sh : (i : Fin ms.length) → List FieldShape}
    (h : shapesAt fuel views = some sh) (i : Fin ms.length) {s : List FieldShape}
    (hs : fieldShapesFuel E fuel fam.ref fam.member.arity fam.parameters.length
      fam.indices.length fam.parameters.length (views i).fields = some s) :
    sh i = s := by
  unfold shapesAt at h
  split at h
  · injection h with hfun
    simpa [hs] using congrFun hfun.symm i
  · cases h

def minorExpr {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (fuel : Nat) (c : PolicyConstructorView E fam m) (i : Nat)
    (shapes : List FieldShape) : Option (Expr Nat) :=
  let shift := 1 + i
  let motive := Expr.bvar i
  let ctorAcc := foldApps
    (.const (fam.ref + 1 + i) (policyFamilyLevels fam))
    (policyParameterLocals fam.parameters.length shift)
  minorFromTelescope E fuel fam.parameters.length motive ctorAcc shapes
    (lift 0 shift (ctorFieldTelescope c))

def minorsAt {E : ResolvedEnv} {fam : PolicyFamilyView E} {ms : List CheckedMember}
    (fuel : Nat) (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i])
    (shapes : (i : Fin ms.length) → List FieldShape) : Option (List (Expr Nat)) :=
  let rec go : (j : Nat) → j ≤ ms.length → Option (List (Expr Nat))
    | 0, _ => some []
    | j + 1, hj =>
        match go j (Nat.le_of_succ_le hj) with
        | none => none
        | some acc =>
            match minorExpr fuel (views ⟨j, hj⟩) j (shapes ⟨j, hj⟩) with
            | some t => some (acc ++ [t])
            | none => none
  (go ms.length (Nat.le_refl _)).bind fun mins =>
    if mins.length = ms.length then some mins else none

def keyAbsent (tbl : List (Nat × CheckedMember)) (r : Nat) : Bool :=
  tbl.all fun p => decide (p.1 ≠ r)

theorem find?_none_of_absent {α : Type} {tbl : List (Nat × α)} {r : Nat}
    (h : tbl.all (fun p => decide (p.1 ≠ r)) = true) :
    tbl.find? (fun p => p.1 == r) = none := by
  induction tbl with
  | nil => rfl
  | cons p tl ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [List.find?]
      have hne : (p.1 == r) = false := by
        cases hb : p.1 == r with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb) h.1
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact ih h.2

theorem fresh_of_absent {tbl : List (Nat × CheckedMember)} {r : Nat}
    (hnd : (tbl.map (·.1)).Nodup) (h : keyAbsent tbl r = true) :
    (foldEnv tbl).members r = none := by
  rw [foldEnv_members hnd, find?_none_of_absent h]
  rfl

def foldGo (E : ResolvedEnv) : List (Nat × CheckedMember) → ResolvedEnv
  | [] => E
  | (r, m) :: rest => foldGo (extendEnv E r m) rest

theorem foldGo_foldl (E : ResolvedEnv) (tbl : List (Nat × CheckedMember)) :
    foldGo E tbl = tbl.foldl (fun E (r, m) => extendEnv E r m) E := by
  induction tbl generalizing E with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | mk r m =>
          simp only [foldGo, List.foldl_cons, ih]

theorem foldEnv_nil : foldEnv [] = emptyEnv := rfl

theorem foldEnv_cons (r : Nat) (m : CheckedMember) (rest : List (Nat × CheckedMember)) :
    foldEnv ((r, m) :: rest) = foldGo (extendEnv emptyEnv r m) rest := by
  simp only [foldEnv, List.foldl_cons]
  exact (foldGo_foldl _ _).symm

theorem foldGo_eq_foldEnv (tbl : List (Nat × CheckedMember)) :
    foldGo emptyEnv tbl = foldEnv tbl := by
  simp only [foldEnv, foldGo_foldl]

theorem foldEnv_snoc (xs : List (Nat × CheckedMember)) (r : Nat) (m : CheckedMember) :
    foldEnv (xs ++ [(r, m)]) = extendEnv (foldEnv xs) r m := by
  simp only [foldEnv, List.foldl_append, List.foldl_cons, List.foldl_nil]

def keysOk (f : Nat) (ctors : List (Nat × CheckedMember)) (rr : Nat) : Bool :=
  decide (rr = f + 1 + ctors.length) &&
    (List.range ctors.length).all fun i =>
      match ctors[i]? with
      | some (r, _) => decide (r = f + 1 + i)
      | none => false

structure GroupPrep (tbl : List (Nat × CheckedMember)) where
  f : Nat
  fm : CheckedMember
  ctors : List (Nat × CheckedMember)
  rr : Nat
  rm : CheckedMember
  slots : List (Nat × CheckedMember)
  hslots : slots = (f, fm) :: ctors ++ [(rr, rm)]
  htbl : slots = tbl

theorem dropLast_eq_append_getLast {α : Type} (l : List α) (h : l ≠ []) :
    l = l.dropLast ++ [l.getLast h] := by
  induction l with
  | nil => exact absurd rfl h
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t =>
          have ht : b :: t ≠ [] := by simp
          simpa [List.dropLast, List.getLast] using congrArg (a :: ·) (ih ht)

def posPrep (tbl : List (Nat × CheckedMember)) : Option (GroupPrep tbl) :=
  match tbl with
  | [] => none
  | [_] => none
  | (f, fm) :: c :: cs =>
      let rest : List (Nat × CheckedMember) := c :: cs
      have hrest : rest ≠ [] := List.cons_ne_nil _ _
      let ctors := rest.dropLast
      let last := rest.getLast hrest
      let slots := (f, fm) :: ctors ++ [last]
      if keysOk f ctors last.1 then
        some {
          f := f, fm := fm, ctors := ctors, rr := last.1, rm := last.2
          slots := slots
          hslots := rfl
          htbl := by
            have hr : rest = ctors ++ [last] := dropLast_eq_append_getLast rest hrest
            simp only [slots]
            exact congrArg ((f, fm) :: ·) hr.symm
        }
      else none

def takeNodup {α : Type} {l : List α} (h : l.Nodup) (n : Nat) : (l.take n).Nodup := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      cases l with
      | nil => simp
      | cons a l =>
          simp only [List.take_succ_cons, List.nodup_cons] at h ⊢
          exact ⟨fun hin => h.1 (List.mem_of_mem_take hin), ih h.2⟩

def prefixNodup {tbl : List (Nat × CheckedMember)}
    (hnd : (tbl.map (·.1)).Nodup) (n : Nat) :
    ((tbl.take n).map (·.1)).Nodup := by
  simpa [List.map_take] using takeNodup hnd n

def rebuiltType? (fuel : Nat) (prefixTbl : List (Nat × CheckedMember))
    (hnd : (prefixTbl.map (·.1)).Nodup) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (np : Nat) : Option (Expr Nat) :=
  match familyViewAt (foldEnv prefixTbl) fuel np f fm with
  | none => none
  | some fam =>
      let ms := ctors.map (·.2)
      match ctorViews fuel fam ms with
      | none => none
      | some views =>
          match shapesAt fuel views with
          | none => none
          | some sh =>
              match minorsAt fuel views sh with
              | none => none
              | some mins =>
                  let safe := viewsSafeB views
                  match selectElimination? fam.resultLevel ms.length safe with
                  | none => none
                  | some pol => some (policyRecursorType fam mins pol)

def cmpFull (a b : Expr Nat) : Bool := decide (a = b)

/-- Last Π-domain only. A wrong minor still shares the major. -/
def majorsEq (a b : Expr Nat) : Bool :=
  match splitPi (piCount a) a, splitPi (piCount b) b with
  | some (da, _), some (db, _) =>
      match da.getLast?, db.getLast? with
      | some x, some y => decide (x = y)
      | _, _ => false
  | _, _ => false

/-- Replace only the major premise's argument spine. The major head and
every other domain stay. That spine is the parameter/index split
(`policyParameterLocals` ++ index locals). -/
def retargetMajorSpine (ty : Expr Nat) (spine : List (Expr Nat)) : Expr Nat :=
  match splitPi (piCount ty) ty with
  | some (doms, body) =>
      match doms.getLast? with
      | some major =>
          policyPi (doms.dropLast ++ [foldApps (unfoldApps major).1 spine]) body
      | none => ty
  | none => ty

def eraseSplitSpine (ty : Expr Nat) : Expr Nat :=
  retargetMajorSpine ty []

/-- Skip only the split comparison. A swapped major head still refuses. -/
def splitEq (a b : Expr Nat) : Bool :=
  decide (eraseSplitSpine a = eraseSplitSpine b)

inductive Cmp where
  | full
  | body
  | split

def cmpApply : Cmp → Expr Nat → Expr Nat → Bool
  | .full => cmpFull
  | .body => majorsEq
  | .split => splitEq

def findNp? (fuel : Nat) (prefixTbl : List (Nat × CheckedMember))
    (hnd : (prefixTbl.map (·.1)).Nodup) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rm : CheckedMember) (cmp : Cmp) :
    Option Nat :=
  let rec go (n : Nat) : Option Nat :=
    match n with
    | 0 =>
        match rebuiltType? fuel prefixTbl hnd f fm ctors 0 with
        | some ty => if cmpApply cmp ty rm.mtype then some 0 else none
        | none => none
    | n + 1 =>
        match rebuiltType? fuel prefixTbl hnd f fm ctors (n + 1) with
        | some ty =>
            if cmpApply cmp ty rm.mtype then some (n + 1) else go n
        | none => go n
  go (piCount fm.mtype)

def fieldUnivOf {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) (h : fieldUnivB c = true) :
    FieldUniverseAdmitted c := by
  unfold fieldUnivB at h
  cases hc : classifyUniverse fam.resultLevel with
  | uniformProp =>
      intro j
      exact Or.inl ((classifyUniverse_uniformProp_iff _).mp hc)
  | uniformType =>
      rw [hc] at h
      exact fieldUniverseAdmitted_type_of_B c
        ((classifyUniverse_uniformType_iff _).mp hc) h
  | mixed => simp [hc] at h

/-! ## Slot table facts used only inside admission payloads -/

theorem mem_of_mem_dropLast {α : Type} {a : α} {l : List α} (h : a ∈ l.dropLast) : a ∈ l := by
  induction l with
  | nil => cases h
  | cons x t ih =>
      cases t with
      | nil => cases h
      | cons y t =>
          simp only [List.dropLast] at h
          rcases List.mem_cons.mp h with hx | ht
          · exact List.mem_cons.mpr (Or.inl hx)
          · exact List.mem_cons.mpr (Or.inr (ih ht))

theorem nodup_dropLast {α : Type} {l : List α} (h : l.Nodup) : l.dropLast.Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t =>
          simp only [List.dropLast] at h ⊢
          rw [List.nodup_cons] at h ⊢
          exact ⟨fun hin => h.1 (mem_of_mem_dropLast hin), ih h.2⟩

theorem map_dropLast {α β : Type} (f : α → β) (l : List α) :
    (l.dropLast).map f = (l.map f).dropLast := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t => simp [List.dropLast, ih]

theorem dropLast_append_singleton {α : Type} (xs : List α) (a : α) :
    (xs ++ [a]).dropLast = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.dropLast, ih]

theorem foldGo_append (E : ResolvedEnv) (a b : List (Nat × CheckedMember)) :
    foldGo E (a ++ b) = foldGo (foldGo E a) b := by
  induction a generalizing E with
  | nil => rfl
  | cons p a ih =>
      cases p with
      | mk r m => simp [foldGo, List.cons_append, ih]

theorem nodup_keys_snoc {l : List (Nat × CheckedMember)} {r : Nat} {m : CheckedMember}
    (h : (l.map (·.1)).Nodup) (ha : keyAbsent l r = true) :
    ((l ++ [(r, m)]).map (·.1)).Nodup := by
  unfold List.Nodup
  rw [List.map_append, List.map_singleton, List.pairwise_append]
  refine ⟨h, ?_, ?_⟩
  · simp
  · intro a haMem b hbMem
    simp only [List.mem_singleton] at hbMem
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp haMem
    have hdec := List.all_eq_true.mp ha p hp
    have hne : p.1 ≠ r := of_decide_eq_true hdec
    exact hbMem ▸ hpk ▸ hne

theorem keysOk_ctor {f : Nat} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    (h : keysOk f ctors rr = true) (i : Fin ctors.length) :
    ctors[i].1 = f + 1 + i.val ∧ rr = f + 1 + ctors.length := by
  simp only [keysOk, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.1⟩
  have hb := List.all_eq_true.mp h.2 i.val (List.mem_range.mpr i.isLt)
  have hlt : i.val < ctors.length := i.isLt
  rw [List.getElem?_eq_getElem hlt] at hb
  cases hci : ctors[i.val] with
  | mk r m =>
      simp only [hci, decide_eq_true_eq] at hb
      simpa [hci] using hb

theorem find?_of_key {α : Type} {l : List (Nat × α)} {k : Nat} {a : α}
    (hnd : (l.map (·.1)).Nodup) (hmem : (k, a) ∈ l) :
    l.find? (fun p => p.1 == k) = some (k, a) := by
  induction l with
  | nil => simp at hmem
  | cons p tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.mem_cons] at hmem
      simp only [List.find?]
      cases hmem with
      | inl heq =>
          subst heq
          simp
      | inr htl =>
          have hne : p.1 ≠ k := by
            intro hk
            have hin : k ∈ tl.map (·.1) :=
              List.mem_map.mpr ⟨(k, a), htl, rfl⟩
            exact hnd.1 (hk ▸ hin)
          have hbeq : (p.1 == k) = false := by
            cases hb : p.1 == k with
            | false => rfl
            | true => exact absurd (beq_iff_eq.mp hb) hne
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          exact ih hnd.2 htl

/-- The recovered `nparams` is the length of the family-parameter list, and
that length is the only one whose rebuilt recursor type is the stored type. -/
theorem nparams_unique_of_rebuilt {E E' : ResolvedEnv}
    {fam : PolicyFamilyView E} {fam' : PolicyFamilyView E'}
    {mins mins' : List (Expr Nat)} {p p' : EliminationPolicy}
    {np np' : Nat}
    (hk : mins.length = mins'.length)
    (h : policyRecursorType fam mins p = policyRecursorType fam' mins' p')
    (hp : fam.parameters.length = np) (hp' : fam'.parameters.length = np') :
    np = np' := by
  have hlen := checked_nparams_unique hk h
  omega

abbrev admitFuel : Nat := 96

inductive LevelProfile (u : Level) : Type where
  | prop (h : UniformProp u)
  | typ (h : UniformType u)

def profileOr {u : Level} : LevelProfile u → UniformProp u ∨ UniformType u
  | .prop h => Or.inl h
  | .typ h => Or.inr h

def profileOf (u : Level) : Option (LevelProfile u) :=
  match hc : classifyUniverse u with
  | .uniformProp => some (.prop ((classifyUniverse_uniformProp_iff u).mp hc))
  | .uniformType => some (.typ ((classifyUniverse_uniformType_iff u).mp hc))
  | .mixed => none

def familyAdmitted? (fuel : Nat) (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
    (np : Nat) : Option (IndGroupAdmitted E r m) :=
  match hmem : E.members r with
  | some _ => none
  | none =>
      match familyViewAt (extendEnv E r m) fuel np r m with
      | none => none
      | some v =>
          if href : v.ref = r then
            if hm : sameMember v.member m = true then
              match profileOf v.resultLevel with
              | some hp =>
                  some (.family hmem v href (sameMember_eq hm) (profileOr hp))
              | none => none
            else none
          else none

def ctorAdmitted? (fuel : Nat) (E : ResolvedEnv) (seen : List (Nat × CheckedMember))
    (hE : E = foldEnv seen) (hnd : (seen.map (·.1)).Nodup)
    (r : Nat) (m : CheckedMember) (np f : Nat) (fm : CheckedMember) :
    Option (IndGroupAdmitted E r m) :=
  match hmem : E.members r with
  | some _ => none
  | none =>
      match familyViewAt E fuel np f fm with
      | none => none
      | some fam =>
          match buildCtorView? fuel fam m with
          | none => none
          | some cv =>
              if hnr : noRecursorForB seen f = true then
                if hcc : ctorContiguousB seen r m = true then
                  if hfu : fieldUnivB cv = true then
                    if hfp : ctorFieldsPermittedB cv fuel = true then
                      if hf : memberFamRef m = some f then
                        some (.constructor fam cv hmem
                          ⟨f, hf, hE.symm ▸ noRecursorForB_sound hnd hnr⟩
                          (hE.symm ▸ ctorContiguousB_sound hnd hcc)
                          (fieldUnivOf cv hfu)
                          (ctorFieldsPermitted_of_B cv fuel hfp))
                      else none
                    else none
                  else none
                else none
              else none

structure SelectionHit {E : ResolvedEnv} {fam : PolicyFamilyView E}
    {ms : List CheckedMember}
    (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i])
    (pol : EliminationPolicy) : Type where
  sel : EliminationSelection fam.resultLevel ms.length
    (∀ i, (views i).AllFieldsSafe) pol

def selectionOf {E : ResolvedEnv} {fam : PolicyFamilyView E} {ms : List CheckedMember}
    (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i])
    (pol : EliminationPolicy) : Option (SelectionHit views pol) :=
  match hc : classifyUniverse fam.resultLevel, pol with
  | .uniformType, .anySort =>
      some ⟨.uniformType ((classifyUniverse_uniformType_iff _).mp hc)⟩
  | .uniformProp, .anySort =>
      if hk0 : ms.length = 0 then
        some ⟨.emptyProp ((classifyUniverse_uniformProp_iff _).mp hc) hk0⟩
      else if hk1 : ms.length = 1 then
        if hs : viewsSafeB views = true then
          some ⟨.singletonProp ((classifyUniverse_uniformProp_iff _).mp hc) hk1
            (viewsSafe_of views hs)⟩
        else none
      else none
  | .uniformProp, .propOnly =>
      if hk : 1 < ms.length then
        some ⟨.multipleProp ((classifyUniverse_uniformProp_iff _).mp hc) hk⟩
      else none
  | _, _ => none

theorem prefix_ctor_mem {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {i : Fin ctors.length}
    (hkey : keysOk f ctors (f + 1 + ctors.length) = true) :
    (f + 1 + i.val, ctors[i].2) ∈ (f, fm) :: ctors := by
  have hk := (keysOk_ctor hkey i).1
  have hpair : ctors[i] = (f + 1 + i.val, ctors[i].2) := by
    cases hci : ctors[i] with
    | mk r m =>
        have hr : r = f + 1 + i.val := by simpa [hci] using hk
        simp [hci, hr]
  rw [← hpair]
  exact List.mem_cons_of_mem _ (List.getElem_mem _)

def buildRecAdmitted? (fuel : Nat) (E : ResolvedEnv)
    (prefixTbl : List (Nat × CheckedMember))
    (hnd : (prefixTbl.map (·.1)).Nodup) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember)
    (np : Nat) : Option (RecursorEliminationAdmitted E rr rm) :=
  if _hpre : prefixTbl.map (·.1) = ((f, fm) :: ctors).map (·.1) then
    match familyViewAt E fuel np f fm with
    | none => none
    | some fam =>
        let ms := ctors.map (·.2)
        match ctorViews fuel fam ms with
        | none => none
        | some views =>
            match shapesAt fuel views with
            | none => none
            | some _sh =>
                match minorsAt fuel views _sh with
                | none => none
                | some mins =>
                    if hlen : mins.length = ms.length then
                      let safe := viewsSafeB views
                      match hsel : selectElimination? fam.resultLevel ms.length safe with
                      | none => none
                      | some pol =>
                          if hty : rm.mtype = policyRecursorType fam mins pol then
                            if har : rm.arity = policyRecursorArity fam.member.arity pol then
                              if href : rr = fam.ref + 1 + ms.length then
                                if hkey : keysOk f ctors rr = true then
                                  if hpres : (List.range ms.length).all (fun j =>
                                      if hj : j < ms.length then
                                        match E.members (f + 1 + j) with
                                        | some m' => sameMember m' ms[j]
                                        | none => false
                                      else false) = true then
                                    match selectionOf views pol with
                                    | none => none
                                    | some hit =>
                                        if hfams : fam.ref = f then
                                          if hmc : rm.mclass = .recursorM then
                                          some {
                                            family := fam
                                            constructors := ms
                                            constructorViews := views
                                            constructorsPresent := by
                                              intro i
                                              have hb := List.all_eq_true.mp hpres i.val
                                                (List.mem_range.mpr i.isLt)
                                              rw [dif_pos i.isLt] at hb
                                              cases hm : E.members (f + 1 + i.val) with
                                              | none => simp [hm] at hb
                                              | some m' =>
                                                  rw [hm] at hb
                                                  have he := sameMember_eq hb
                                                  have hi : i.val < ctors.length := by
                                                    simpa [ms, List.length_map] using i.isLt
                                                  have hidx : ms[i.val] = (ctors[i.val]'hi).2 := by
                                                    simp [ms, List.getElem_map, hi]
                                                  simpa [hfams, he, hidx] using hm
                                            recursorRef := href
                                            minorTypes := mins
                                            minorCount := hlen
                                            policy := pol
                                            selected := hit.sel
                                            recursorArity := har
                                            recursorType := hty
                                            recursorMclass := hmc
                                          }
                                          else none
                                        else none
                                  else none
                                else none
                              else none
                            else none
                          else none
                    else none
  else none

/-- `derivedMinor` agrees with the minor list just stored, as a Bool. -/
def minorsMatchB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Nat)
    (sh : (i : Fin a.constructors.length) → List FieldShape) : Bool :=
  (List.range a.constructors.length).all fun j =>
    if hj : j < a.constructors.length then
      match derivedMinor a ⟨j, hj⟩ fuel (sh ⟨j, hj⟩) with
      | some t => decide (a.minorTypes[j]? = some t)
      | none => false
    else false

theorem minorsMatch_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {fuel : Nat}
    {sh : (i : Fin a.constructors.length) → List FieldShape}
    (hsh : ∀ i, fieldShapesFuel E fuel a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length
      a.family.parameters.length (a.constructorViews i).fields = some (sh i))
    (h : minorsMatchB a fuel sh = true) : MinorPremisesMatch a := by
  intro i
  unfold minorsMatchB at h
  have hb := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  rw [dif_pos i.isLt] at hb
  cases hd : derivedMinor a i fuel (sh i) with
  | none => simp [hd] at hb
  | some t =>
      rw [hd] at hb
      have he := of_decide_eq_true hb
      exact ⟨sh i, fuel, hsh i, hd.trans he.symm⟩

def shapesWitness {E : ResolvedEnv} {fam : PolicyFamilyView E} {ms : List CheckedMember}
    (fuel : Nat) (views : (i : Fin ms.length) → PolicyConstructorView E fam ms[i])
    (sh : (i : Fin ms.length) → List FieldShape) (i : Fin ms.length) : Prop :=
  fieldShapesFuel E fuel fam.ref fam.member.arity fam.parameters.length
    fam.indices.length fam.parameters.length (views i).fields = some (sh i)

def iotaTypedAt {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) : Option (IotaEquationTyped a i fuel shapes) :=
  match hdom : equationDoms a i, hsch : iotaSchemaAt a i fuel shapes with
  | some doms, some rhs =>
      match exprCheck (fuel + 32) (extendEnv E r m) m.arity (assumptionCtx doms) rhs
          (iotaEquationType a i) with
      | some hty =>
          some (by
            unfold IotaEquationTyped
            rw [hdom, hsch]
            exact hty)
      | none => none
  | _, _ => none

def iotaClause? {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Nat)
    (sh : (i : Fin a.constructors.length) → List FieldShape)
    (hsh : ∀ i, shapesWitness fuel a.constructorViews sh i)
    (hbody : m.body = none) : Option (IotaDescriptorClause E a) :=
  if hall : (List.range a.constructors.length).all (fun j =>
      if hj : j < a.constructors.length then
        (iotaTypedAt a ⟨j, hj⟩ fuel (sh ⟨j, hj⟩)).isSome
      else false) = true then
    some {
      signatureOnly := hbody
      shapesAt := sh
      fuelAt := fun _ => fuel
      analyzed := fun i => hsh i
      typed := fun i => by
        have hb := List.all_eq_true.mp hall i.val (List.mem_range.mpr i.isLt)
        simp only [dif_pos i.isLt] at hb
        exact (iotaTypedAt a i fuel (sh i)).get hb
    }
  else none

/-- Finish an actual rebuilt recursor admission against the complete environment
table. The local-group guard remains in `buildRecAdmitted?`; its caller may use
a different, complete table here to pay the census over `E`. -/
def finishRecAdmitted? (fuel : Nat) (E : ResolvedEnv)
    (censusTbl : List (Nat × CheckedMember))
    (hnd : (censusTbl.map (·.1)).Nodup) (hE : E = foldEnv censusTbl)
    (rr : Nat) (rm : CheckedMember) (a : RecursorEliminationAdmitted E rr rm) :
    Option (IndGroupAdmitted E rr rm) :=
  match hAt : shapesAt fuel a.constructorViews with
  | none => none
  | some sh =>
      if hshB : (List.range a.constructors.length).all (fun j =>
          if hj : j < a.constructors.length then
            (fieldShapesFuel E fuel a.family.ref a.family.member.arity
              a.family.parameters.length a.family.indices.length
              a.family.parameters.length (a.constructorViews ⟨j, hj⟩).fields).isSome
          else false) = true then
        have hsh : ∀ i, shapesWitness fuel a.constructorViews sh i := by
          intro i
          have hb := List.all_eq_true.mp hshB i.val (List.mem_range.mpr i.isLt)
          simp only [dif_pos i.isLt] at hb
          cases hs : fieldShapesFuel E fuel a.family.ref a.family.member.arity
              a.family.parameters.length a.family.indices.length
              a.family.parameters.length (a.constructorViews i).fields with
          | none =>
              rw [hs] at hb
              simp at hb
          | some s =>
              unfold shapesWitness
              exact (shapesAt_apply hAt i hs).symm ▸ hs
        if hmm : minorsMatchB a fuel sh = true then
          if hbody : rm.body = none then
            match iotaClause? a fuel sh hsh hbody with
            | none => none
            | some h14 =>
                match hfresh : E.members rr with
                | some _ => none
                | none =>
                  let fr := a.family.ref
                  if hcens : ctorCensusB censusTbl fr rr = true then
                    if hfu : (List.range a.constructors.length).all (fun j =>
                        if hj : j < a.constructors.length then
                          fieldUnivB (a.constructorViews ⟨j, hj⟩)
                        else false) = true then
                      if hfp : (List.range a.constructors.length).all (fun j =>
                          if hj : j < a.constructors.length then
                            ctorFieldsPermittedB (a.constructorViews ⟨j, hj⟩) fuel
                          else false) = true then
                        have h04 : CtorCensus E a.family.ref rr := by
                          change CtorCensus E fr rr
                          rw [hE]
                          exact ctorCensusB_sound hnd hcens
                        some (.recursor a hfresh h04
                          (by
                            intro i
                            have hb := List.all_eq_true.mp hfu i.val (List.mem_range.mpr i.isLt)
                            rw [dif_pos i.isLt] at hb
                            exact fieldUnivOf _ hb)
                          (by
                            intro i
                            have hb := List.all_eq_true.mp hfp i.val (List.mem_range.mpr i.isLt)
                            rw [dif_pos i.isLt] at hb
                            exact ctorFieldsPermitted_of_B _ fuel hb)
                          (minorsMatch_of hsh hmm)
                          h14)
                      else none
                    else none
                  else none
          else none
        else none
      else none

def recAdmitted? (fuel : Nat) (E : ResolvedEnv) (prefixTbl : List (Nat × CheckedMember))
    (hnd : (prefixTbl.map (·.1)).Nodup) (hE : E = foldEnv prefixTbl)
    (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (rr : Nat) (rm : CheckedMember) (np : Nat) :
    Option (IndGroupAdmitted E rr rm) :=
  match buildRecAdmitted? fuel E prefixTbl hnd f fm ctors rr rm np with
  | none => none
  | some a => finishRecAdmitted? fuel E prefixTbl hnd hE rr rm a

/-- The original entry point still performs its local-table builder first and
then the same finishing checks, with the original table as the census table. -/
theorem recAdmitted?_shared_finish (fuel : Nat) (E : ResolvedEnv)
    (prefixTbl : List (Nat × CheckedMember))
    (hnd : (prefixTbl.map (·.1)).Nodup) (hE : E = foldEnv prefixTbl)
    (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (rr : Nat) (rm : CheckedMember) (np : Nat) :
    recAdmitted? fuel E prefixTbl hnd hE f fm ctors rr rm np =
      (buildRecAdmitted? fuel E prefixTbl hnd f fm ctors rr rm np).bind
        (finishRecAdmitted? fuel E prefixTbl hnd hE rr rm) := by
  unfold recAdmitted?
  cases buildRecAdmitted? fuel E prefixTbl hnd f fm ctors rr rm np <;> rfl

def chainAppend {S : ResolvedEnv} {fuel : Nat} :
    {E : ResolvedEnv} → {rest1 : List (Nat × CheckedMember)} → {E2 : ResolvedEnv} →
    {rest2 : List (Nat × CheckedMember)} → {E3 : ResolvedEnv} →
    GroupAcceptChain S fuel E rest1 E2 → GroupAcceptChain S fuel E2 rest2 E3 →
    GroupAcceptChain S fuel E (rest1 ++ rest2) E3
  | _, _, _, _, _, .nil _, c2 => c2
  | _, _, _, _, _, .cons E r m rest _ adm hs ha crest, c2 =>
      .cons E r m (rest ++ _) _ adm hs ha (chainAppend crest c2)
  | _, _, _, _, _, .consRec E r m rest _ adm a hcl htel hmin hrec ha crest, c2 =>
      .consRec E r m (rest ++ _) _ adm a hcl htel hmin hrec ha (chainAppend crest c2)
  | _, _, _, _, _, .consRecCheck E r m rest _ adm a hcl htel hchk hrec ha crest, c2 =>
      .consRecCheck E r m (rest ++ _) _ adm a hcl htel hchk hrec ha (chainAppend crest c2)

structure ChainHit (S : ResolvedEnv) (fuel : Nat) (E : ResolvedEnv)
    (ctors : List (Nat × CheckedMember)) : Type where
  env : ResolvedEnv
  chain : GroupAcceptChain S fuel E ctors env
  folded : env = foldGo E ctors

def chainOfCtors (fuel : Nat) (S : ResolvedEnv) (f : Nat) (fm : CheckedMember) (np : Nat)
    (E : ResolvedEnv) (seen : List (Nat × CheckedMember))
    (hE : E = foldEnv seen) (hnd : (seen.map (·.1)).Nodup) :
    (ctors : List (Nat × CheckedMember)) → Option (ChainHit S fuel E ctors)
  | [] => some ⟨E, .nil E, rfl⟩
  | (r, m) :: ctors =>
      if habs : keyAbsent seen r = true then
        match ctorAdmitted? fuel E seen hE hnd r m np f fm with
        | none => none
        | some adm =>
            if hsort : (sortTyAtC E m.arity fuel [] m.mtype).isSome = true then
              if hacc : memberAcceptB S E fuel adm
                  ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1 = true then
                have hE' : extendEnv E r m = foldEnv (seen ++ [(r, m)]) := by
                  rw [hE]
                  symm
                  rw [← foldGo_eq_foldEnv, foldGo_append]
                  simp only [foldGo, foldGo_eq_foldEnv]
                have hnd' := nodup_keys_snoc (m := m) hnd habs
                match chainOfCtors fuel S f fm np (extendEnv E r m)
                    (seen ++ [(r, m)]) hE' hnd' ctors with
                | none => none
                | some hit =>
                    some {
                      env := hit.env
                      chain := .cons E r m ctors hit.env adm hsort hacc hit.chain
                      folded := by
                        rw [foldGo]
                        exact hit.folded
                    }
              else none
            else none
      else none

structure AdmitPack (tbl : List (Nat × CheckedMember)) : Type where
  f : Nat
  fm : CheckedMember
  ctors : List (Nat × CheckedMember)
  rr : Nat
  rm : CheckedMember
  E' : ResolvedEnv
  hlist : (f, fm) :: ctors ++ [(rr, rm)] = tbl
  hclass : groupClassB fm ctors rm = true
  hchain : GroupAcceptChain (extendEnv emptyEnv f fm) admitFuel emptyEnv
    ((f, fm) :: ctors ++ [(rr, rm)]) E'
  henv : E' = foldEnv tbl

def admitIndGroup? (tbl : List (Nat × CheckedMember))
    (hnd : (tbl.map (·.1)).Nodup) : Option (AdmitPack tbl) :=
  match posPrep tbl with
  | none => none
  | some p =>
      let preSlots := (p.f, p.fm) :: p.ctors
      if hpre : (preSlots.map (·.1)).Nodup then
        if hkey : keysOk p.f p.ctors p.rr = true then
          match findNp? admitFuel preSlots hpre p.f p.fm p.ctors p.rm Cmp.full with
          | none => none
          | some np =>
              if hclass : groupClassB p.fm p.ctors p.rm = true then
                  match hmem0 : emptyEnv.members p.f with
                  | some _ => none
                  | none =>
                      match familyAdmitted? admitFuel emptyEnv p.f p.fm np with
                      | none => none
                      | some fadm =>
                          if hsortF : (sortTyAtC emptyEnv p.fm.arity admitFuel [] p.fm.mtype).isSome = true then
                            let S := extendEnv emptyEnv p.f p.fm
                            if haccF : memberAcceptB S emptyEnv admitFuel fadm
                                ((sortTyAtC emptyEnv p.fm.arity admitFuel [] p.fm.mtype).get hsortF).1 = true then
                              have hE1 : S = foldEnv [(p.f, p.fm)] := by
                                simp [S, foldEnv, emptyEnv, extendEnv]
                              have hnd1 : (([(p.f, p.fm)]).map (·.1)).Nodup := by simp
                              match chainOfCtors admitFuel S p.f p.fm np S [(p.f, p.fm)] hE1 hnd1 p.ctors with
                              | none => none
                              | some hitC =>
                                  let Epre := hitC.env
                                  let chC := hitC.chain
                                  have hEpre : Epre = foldGo S p.ctors := hitC.folded
                                  have hEfold : Epre = foldEnv preSlots := by
                                    have hstep : foldGo emptyEnv preSlots = foldGo S p.ctors := by
                                      simp only [preSlots, foldGo_append, foldGo, S]
                                    rw [← foldGo_eq_foldEnv, hstep]
                                    exact hEpre
                                  match recAdmitted? admitFuel Epre preSlots hpre hEfold
                                      p.f p.fm p.ctors p.rr p.rm np with
                                  | none => none
                                  | some radm =>
                                      if hsortR : (sortTyAtC Epre p.rm.arity admitFuel [] p.rm.mtype).isSome = true then
                                        if haccR : memberAcceptB S Epre admitFuel radm
                                            ((sortTyAtC Epre p.rm.arity admitFuel [] p.rm.mtype).get hsortR).1 = true then
                                          let chR : GroupAcceptChain S admitFuel Epre [(p.rr, p.rm)]
                                              (extendEnv Epre p.rr p.rm) :=
                                            .cons Epre p.rr p.rm [] _ radm hsortR haccR (.nil _)
                                          let chTail := chainAppend chC chR
                                          let ch : GroupAcceptChain S admitFuel emptyEnv
                                              ((p.f, p.fm) :: p.ctors ++ [(p.rr, p.rm)])
                                              (extendEnv Epre p.rr p.rm) :=
                                            .cons emptyEnv p.f p.fm (p.ctors ++ [(p.rr, p.rm)]) _
                                              fadm hsortF haccF chTail
                                          have hlist : (p.f, p.fm) :: p.ctors ++ [(p.rr, p.rm)] = tbl :=
                                            p.hslots.symm.trans p.htbl
                                          some {
                                            f := p.f
                                            fm := p.fm
                                            ctors := p.ctors
                                            rr := p.rr
                                            rm := p.rm
                                            E' := extendEnv Epre p.rr p.rm
                                            hlist := hlist
                                            hclass := hclass
                                            hchain := ch
                                            henv := by
                                              -- Rewrite `foldEnv tbl`, not `tbl`: `p : GroupPrep tbl`.
                                              have hslots : preSlots ++ [(p.rr, p.rm)] =
                                                  (p.f, p.fm) :: p.ctors ++ [(p.rr, p.rm)] := by
                                                simp [preSlots]
                                              have hfold : foldEnv (preSlots ++ [(p.rr, p.rm)]) =
                                                  foldEnv tbl :=
                                                congrArg foldEnv (hslots.trans hlist)
                                              rw [← hfold, foldEnv_snoc]
                                              exact congrArg (fun E => extendEnv E p.rr p.rm) hEfold
                                          }
                                        else none
                                      else none
                            else none
                          else none
                else none
        else none
      else none

def envOf {tbl : List (Nat × CheckedMember)} (p : AdmitPack tbl) : EnvWfT (foldEnv tbl) :=
  p.henv ▸ EG010T_group_accepted EnvWfT.empty admitFuel p.hclass p.hchain

def acceptIndGroup? (tbl : List (Nat × CheckedMember))
    (hnd : (tbl.map (·.1)).Nodup) : Option (EnvWfT (foldEnv tbl)) :=
  (admitIndGroup? tbl hnd).map envOf

def acceptIndGroup?_sound {tbl : List (Nat × CheckedMember)}
    (hnd : (tbl.map (·.1)).Nodup)
    (h : (admitIndGroup? tbl hnd).isSome = true) :
    EnvWfT (foldEnv tbl) :=
  let p := (admitIndGroup? tbl hnd).get h
  p.henv ▸ EG010T_group_accepted EnvWfT.empty admitFuel p.hclass p.hchain

/-! ## Pins and teeth

Nat is the stored large-elimination group (`natRecMemberU` at refs 0–3).
Eq is the stored erased group (`eqFamT` / `eqReflT` / `eqRecT` at 63–65).
`tooth_order` is the real checker on a reordered table; `mutant_order`
sorts those same slots and then runs the real checker. `tooth_type` and
`tooth_nparams` are the real checker. `mutant_type` and `mutant_nparams`
stop at the finder: they do not run the admission tail. `mutant_type`
compares only the major domain. `mutant_nparams` skips only the major
argument spine (the parameter/index split) and still compares the major
head and the other domains. -/

def natGroup : List (Nat × CheckedMember) :=
  [(0, natFamMember), (1, natZeroMember), (2, natSuccMember), (3, natRecMemberU)]

def eqGroupTbl : List (Nat × CheckedMember) :=
  [(63, eqFamT), (64, eqReflT), (65, eqRecT)]

def natBadOrder : List (Nat × CheckedMember) :=
  [(0, natFamMember), (2, natSuccMember), (1, natZeroMember), (3, natRecMemberU)]

def natRecTypeBadMinor : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.param 0)))
    (.pi (.app (.bvar 0) (.const 2 []))
      (.pi (.pi (.const 0 [])
            (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))))
        (.pi (.const 0 [])
          (.app (.bvar 3) (.bvar 0)))))

def natRecBadMinor : CheckedMember := ⟨.recursorM, 1, natRecTypeBadMinor, none⟩

def natBadType : List (Nat × CheckedMember) :=
  [(0, natFamMember), (1, natZeroMember), (2, natSuccMember), (3, natRecBadMinor)]

/-- `listFamMember` is `Π (A : Sort 1), Sort 1` (`piCount` 1). No
constructors: both `nparams` 0 and 1 pass the telescope-length guard.
The stored recursor is the `nparams = 0` rebuild with only the major
argument spine replaced, so it is not the rebuilt type at either split. -/
def splitFamPrefix : List (Nat × CheckedMember) :=
  [(0, listFamMember)]

theorem splitFamPrefixNd : (splitFamPrefix.map (·.1)).Nodup := by decide

def splitRebuilt? (np : Nat) : Option (Expr Nat) :=
  rebuiltType? admitFuel splitFamPrefix splitFamPrefixNd 0 listFamMember [] np

/-- The named wrong split: the index reading of a one-binder family. -/
def excludedNparams : Nat := 0

def splitRecType : Expr Nat :=
  match splitRebuilt? excludedNparams with
  | some ty => retargetMajorSpine ty [.bvar 0, .bvar 0]
  | none => .sort .zero

def splitRecMember : CheckedMember := ⟨.recursorM, 0, splitRecType, none⟩

def splitBadNparams : List (Nat × CheckedMember) :=
  [(0, listFamMember), (1, splitRecMember)]

theorem natGroupNd : (natGroup.map (·.1)).Nodup := by decide
theorem eqGroupNd : (eqGroupTbl.map (·.1)).Nodup := by decide
theorem natBadOrderNd : (natBadOrder.map (·.1)).Nodup := by decide
theorem natBadTypeNd : (natBadType.map (·.1)).Nodup := by decide
theorem splitBadNparamsNd : (splitBadNparams.map (·.1)).Nodup := by decide

def fullHit (np : Nat) : Bool :=
  match splitRebuilt? np with
  | some ty => decide (ty = splitRecType)
  | none => false

def weakHit (np : Nat) : Bool :=
  match splitRebuilt? np with
  | some ty => splitEq ty splitRecType
  | none => false

def weakFound? : Option Nat :=
  if h : (splitFamPrefix.map (·.1)).Nodup then
    findNp? admitFuel splitFamPrefix h 0 listFamMember [] splitRecMember Cmp.split
  else none

/-- Family `piCount`, whether each candidate rebuilt, full equality at
0 and at 1, the split weakening at 0 and at 1, the nparams that
weakening finds, and whether the exact checker accepts. -/
def nparamsProbe :
    Nat × Bool × Bool × Bool × Bool × Bool × Bool × Option Nat × Bool :=
  (piCount listFamMember.mtype,
   (splitRebuilt? 0).isSome,
   (splitRebuilt? 1).isSome,
   fullHit 0,
   fullHit 1,
   weakHit 0,
   weakHit 1,
   weakFound?,
   (acceptIndGroup? splitBadNparams splitBadNparamsNd).isSome)

def insertKey (p : Nat × CheckedMember) :
    List (Nat × CheckedMember) → List (Nat × CheckedMember)
  | [] => [p]
  | q :: qs => if p.1 ≤ q.1 then p :: q :: qs else q :: insertKey p qs

def sortKeys : List (Nat × CheckedMember) → List (Nat × CheckedMember)
  | [] => []
  | p :: ps => insertKey p (sortKeys ps)

/-- Drops constructor order: sorts the same slots, then runs the real checker. -/
def mutantOrder? (tbl : List (Nat × CheckedMember)) : Bool :=
  let s := sortKeys tbl
  if h : (s.map (·.1)).Nodup then (acceptIndGroup? s h).isSome else false

/-- Drops every domain except the major. A wrong minor still shares the major. -/
def mutantType? (tbl : List (Nat × CheckedMember))
    (hnd : (tbl.map (·.1)).Nodup) : Bool :=
  match posPrep tbl with
  | none => false
  | some p =>
      let preSlots := (p.f, p.fm) :: p.ctors
      if hpre : (preSlots.map (·.1)).Nodup then
        (findNp? admitFuel preSlots hpre p.f p.fm p.ctors p.rm Cmp.body).isSome
      else false

/-- Skips only the major argument spine. Stops at the finder. -/
def mutantNparams? (tbl : List (Nat × CheckedMember))
    (hnd : (tbl.map (·.1)).Nodup) : Bool :=
  match posPrep tbl with
  | none => false
  | some p =>
      let preSlots := (p.f, p.fm) :: p.ctors
      if hpre : (preSlots.map (·.1)).Nodup then
        (findNp? admitFuel preSlots hpre p.f p.fm p.ctors p.rm Cmp.split).isSome
      else false

end Rcic.Declarative

namespace Rcic.Scm.SrcG
open Rcic.Declarative

kernel_rfl_theorem pin_accept_nat :
    (acceptIndGroup? natGroup natGroupNd).isSome = true

kernel_rfl_theorem pin_accept_eq :
    (acceptIndGroup? eqGroupTbl eqGroupNd).isSome = true

kernel_rfl_theorem tooth_order :
    (acceptIndGroup? natBadOrder natBadOrderNd).isSome = false

kernel_rfl_theorem mutant_order :
    mutantOrder? natBadOrder = true

kernel_rfl_theorem tooth_type :
    (acceptIndGroup? natBadType natBadTypeNd).isSome = false

kernel_rfl_theorem mutant_type :
    mutantType? natBadType natBadTypeNd = true

kernel_rfl_theorem pin_nparams_split :
    nparamsProbe = (1, true, true, false, false, true, false, some excludedNparams, false)

kernel_rfl_theorem tooth_nparams :
    (acceptIndGroup? splitBadNparams splitBadNparamsNd).isSome = false

kernel_rfl_theorem mutant_nparams :
    mutantNparams? splitBadNparams splitBadNparamsNd = true

end Rcic.Scm.SrcG

