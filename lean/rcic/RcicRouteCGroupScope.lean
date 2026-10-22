import rcic.RcicTypedScopeAdmission
import rcic.RcicTypedStrengthen
import rcic.RcicCtxConvT
import rcic.RcicAnnEnvBridgeGroup

/-!
# Route C-2: the group's scope from typed admission records

`RcicTypedScopeAdmission` names the remaining obligations of the admission-to-scope
construction. This module supplies the syntactic half: the full-to-plain
factorization (`CtorPlainFactorT` producer), its stored-type agreement, and its
level-label alignment (`ConstructorPlainLabelsRemaining`), all proved without a
checker. The semantic half (the two `*RetypingRemaining` transports, the header
retyping supplied by swe-routec-c1, and the assembled group theorem) is carried
here as named hypotheses on the assembly theorem — the obligations the report
measured, now discharged where the syntax suffices.

The crux is an inverse law: `unshift?` (the checker's recursive-binder sieve)
and `substT` (the views' plain-context reinsertion) are exact inverses.
`plainVar?` maps a full-context variable to its plain index; `unplainIdx`
below is the inverse index map, and `unshiftSubst` the corresponding
substitution. `substT_unshift` then says: unshifting a full-context term and
substituting it back through the mask is the identity. From it, the recorded
field telescope of an actual constructor view decomposes into `FieldT`s and
result indices (`fieldsOfA`, `fieldsOfA_doms`, `ctorPlainFactorT_of_fields`).

No `synChecker`, no `CheckerT`.
-/

namespace Rcic.Declarative

/-! ## (1) the unshift/subst inverse law -/

/-- the full-context position of the `p`-th plain binder; `recs` flags the
    dropped binders innermost-first, exactly as `plainVar?` reads them. -/
def unplainIdx : List Bool → Nat → Nat
  | [], p => p
  | true :: rs, p => unplainIdx rs p + 1
  | false :: _, 0 => 0
  | false :: rs, p + 1 => unplainIdx rs p + 1

/-- `unplainIdx` inverts `plainVar?`: a surviving full variable `t` at plain
    index `p` sits at full position `t` again. -/
theorem plainVar_unplainIdx : (recs : List Bool) → (t p : Nat) →
    plainVar? recs t = some p → unplainIdx recs p = t
  | [], t, p, h => by
      show p = t
      exact (Option.some.inj h).symm
  | true :: _, 0, _, h => by cases h
  | true :: rs, t + 1, p, h =>
      show unplainIdx rs p + 1 = t + 1 from
        congrArg (· + 1) (plainVar_unplainIdx rs t p h)
  | false :: _, 0, _, h => by cases h; rfl
  | false :: rs, t + 1, p, h => by
      simp only [plainVar?, Option.map_eq_some'] at h
      obtain ⟨q, hq, rfl⟩ := h
      show unplainIdx rs q + 1 = t + 1
      exact congrArg (· + 1) (plainVar_unplainIdx rs t q hq)

/-- the substitution that re-inserts a term of the plain context into the full
    context: plain index `p` (past cutoff `c`) ↦ its surviving full position. -/
def unshiftSubst (recs : List Bool) (c : Nat) : SubstT :=
  fun i => if i < c then .bvar i else .bvar (unplainIdx recs (i - c) + c)

theorem lift_zero_one_bvar (k : Nat) :
    lift 0 1 (Expr.bvar k : Expr Nat) = (Expr.bvar (k + 1) : Expr Nat) := by
  show (if 0 ≤ k then Expr.bvar (k + 1) else Expr.bvar k : Expr Nat) = _
  exact if_pos (Nat.zero_le k)

theorem unshiftSubst_apply_lt {recs : List Bool} {c i : Nat} (h : i < c) :
    unshiftSubst recs c i = .bvar i := if_pos h

theorem unshiftSubst_apply_ge {recs : List Bool} {c i : Nat} (h : ¬i < c) :
    unshiftSubst recs c i = .bvar (unplainIdx recs (i - c) + c) := if_neg h

/-- under one binder the unshift substitution is the unshift substitution at
    the next cutoff. -/
theorem unshiftSubst_up (recs : List Bool) (c : Nat) :
    (unshiftSubst recs c).up = unshiftSubst recs (c + 1) := by
  funext i
  cases i with
  | zero =>
      rw [unshiftSubst_apply_lt (Nat.succ_pos c)]
      rfl
  | succ i =>
      show lift 0 1 (unshiftSubst recs c i) = unshiftSubst recs (c + 1) (i + 1)
      by_cases hi : i < c
      · rw [unshiftSubst_apply_lt hi, unshiftSubst_apply_lt (Nat.succ_lt_succ hi),
          lift_zero_one_bvar]
      · have h1 : ¬i + 1 < c + 1 := by omega
        rw [unshiftSubst_apply_ge hi, unshiftSubst_apply_ge h1, lift_zero_one_bvar]
        congr 1
        have h2 : i + 1 - (c + 1) = i - c := by omega
        rw [h2]; omega

/-- THE INVERSE LAW (sieve side): `substT` through the mask undoes `unshift?`. -/
theorem substT_unshift {recs : List Bool} {c : Nat} :
    (e e' : Expr Nat) → unshift? recs c e = some e' →
      substT (unshiftSubst recs c) e' = e
  | .bvar k, e', h => by
      simp only [unshift?] at h
      by_cases hk : k < c
      · rw [if_pos hk] at h
        cases h
        simp only [substT]
        rw [unshiftSubst_apply_lt hk]
      · rw [if_neg hk] at h
        simp only [Option.map_eq_some'] at h
        obtain ⟨p, hp, rfl⟩ := h
        simp only [substT]
        rw [unshiftSubst_apply_ge (by omega : ¬p + c < c)]
        have hu : unplainIdx recs (p + c - c) = k - c := by
          rw [Nat.add_sub_cancel]
          exact plainVar_unplainIdx recs (k - c) p hp
        rw [hu]
        congr 1
        omega
  | .sort _, _, h => by cases h; rfl
  | .const _ _, _, h => by cases h; rfl
  | .lit _, _, h => by cases h; rfl
  | .app f x, e', h => by
      simp only [unshift?] at h
      cases hf : unshift? recs c f with
      | none => rw [hf] at h; cases h
      | some f' =>
          cases hx : unshift? recs c x with
          | none => rw [hf, hx] at h; cases h
          | some x' =>
              rw [hf, hx] at h
              cases h
              simp only [substT, substT_unshift f f' hf, substT_unshift x x' hx]
  | .lam a b, e', h => by
      simp only [unshift?] at h
      cases ha : unshift? recs c a with
      | none => rw [ha] at h; cases h
      | some a' =>
          cases hb : unshift? recs (c + 1) b with
          | none => rw [ha, hb] at h; cases h
          | some b' =>
              rw [ha, hb] at h
              cases h
              simp only [substT, unshiftSubst_up,
                substT_unshift a a' ha, substT_unshift b b' hb]
  | .pi a b, e', h => by
      simp only [unshift?] at h
      cases ha : unshift? recs c a with
      | none => rw [ha] at h; cases h
      | some a' =>
          cases hb : unshift? recs (c + 1) b with
          | none => rw [ha, hb] at h; cases h
          | some b' =>
              rw [ha, hb] at h
              cases h
              simp only [substT, unshiftSubst_up,
                substT_unshift a a' ha, substT_unshift b b' hb]
  | .letE a v b, e', h => by
      simp only [unshift?] at h
      cases ha : unshift? recs c a with
      | none => rw [ha] at h; cases h
      | some a' =>
          cases hv : unshift? recs c v with
          | none => rw [ha, hv] at h; cases h
          | some v' =>
              cases hb : unshift? recs (c + 1) b with
              | none => rw [ha, hv, hb] at h; cases h
              | some b' =>
                  rw [ha, hv, hb] at h
                  cases h
                  simp only [substT, unshiftSubst_up,
                    substT_unshift a a' ha, substT_unshift v v' hv,
                    substT_unshift b b' hb]

/-- the mask substitution at cutoff zero. -/
def maskSubst (recs : List Bool) : SubstT := fun i => .bvar (unplainIdx recs i)

/-- `unshiftSubst` at cutoff `0` is the mask substitution. -/
theorem unshiftSubst_zero (recs : List Bool) :
    unshiftSubst recs 0 = maskSubst recs := by
  funext i
  rw [unshiftSubst_apply_ge (Nat.not_lt_zero i)]
  simp [maskSubst]

/-- the mask substitution under one binder is the mask of the grown mask, by
    the field kind (`false`: kept, `true`: dropped). -/
theorem maskSubst_cons_false (recs : List Bool) :
    (maskSubst recs).up = maskSubst (false :: recs) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      show lift 0 1 (Expr.bvar (unplainIdx recs i)) =
        Expr.bvar (unplainIdx (false :: recs) (i + 1))
      rw [lift_zero_one_bvar]
      rfl

theorem maskSubst_cons_true (recs : List Bool) :
    (maskSubst recs).shift1 = maskSubst (true :: recs) := by
  funext i
  show lift 0 1 (Expr.bvar (unplainIdx recs i)) =
    Expr.bvar (unplainIdx (true :: recs) i)
  rw [lift_zero_one_bvar]
  rfl

/-- `unshift?` through `unshiftSubst` phrased on the mask substitution. -/
theorem substT_mask_unshift {recs : List Bool} {e e' : Expr Nat}
    (h : unshift? recs 0 e = some e') :
    substT (maskSubst recs) e' = e :=
  unshiftSubst_zero recs ▸ substT_unshift e e' h

/-- the mask substitution of the empty mask is the identity substitution. -/
theorem maskSubst_nil : maskSubst [] = SubstT.id := rfl

/-- `ctorEndSubstT` of a mask substitution grows the mask by the fields' flags
    (innermost first, as `unshift?` and `ctorEndSubstT` agree to read them). -/
theorem ctorEndSubstT_maskSubst (recs : List Bool) :
    (fs : List FieldT) →
      ctorEndSubstT (maskSubst recs) fs =
        maskSubst ((fs.map FieldT.isRec).reverse ++ recs)
  | [] => by simp [ctorEndSubstT]
  | .plain _ _ :: fs => by
      show ctorEndSubstT (maskSubst recs).up fs = _
      rw [maskSubst_cons_false, ctorEndSubstT_maskSubst _ fs]
      simp [FieldT.isRec]
  | .drec _ :: fs => by
      show ctorEndSubstT (maskSubst recs).shift1 fs = _
      rw [maskSubst_cons_true, ctorEndSubstT_maskSubst _ fs]
      simp [FieldT.isRec]
  | .drecD _ _ :: fs => by
      show ctorEndSubstT (maskSubst recs).shift1 fs = _
      rw [maskSubst_cons_true, ctorEndSubstT_maskSubst _ fs]
      simp [FieldT.isRec]

/-- the end substitution from the identity is the mask of all the flags. -/
theorem ctorEndSubstT_id (fs : List FieldT) :
    ctorEndSubstT SubstT.id fs = maskSubst (fs.reverse.map FieldT.isRec) := by
  rw [← maskSubst_nil, ctorEndSubstT_maskSubst]
  simp

/-- a `mapM` of `unshift?` inverts under `substT` of the mask. -/
theorem mapM_unshift_substT {recs : List Bool} :
    (l l' : List (Expr Nat)) →
      l.mapM (unshift? recs 0) = some l' →
        l'.map (substT (maskSubst recs)) = l
  | [], _, h => by cases h; rfl
  | x :: xs, l', h => by
      rw [List.mapM_cons] at h
      obtain ⟨b, hb, hrest⟩ := Option.bind_eq_some.mp h
      obtain ⟨tl', htl, hp⟩ := Option.bind_eq_some.mp hrest
      obtain rfl := Option.some.inj hp
      rw [List.map_cons, substT_mask_unshift hb,
        mapM_unshift_substT xs tl' htl]

/-- the parameter locals lifted past one binder gain one field offset. -/
theorem policyParameterLocals_lift_succ (np j : Nat) :
    (policyParameterLocals np j).map (lift 0 1) =
      policyParameterLocals np (j + 1) := by
  simp only [policyParameterLocals, List.map_map]
  exact List.map_congr_left fun x _ => by
    show lift 0 1 (Expr.bvar (x + j)) = Expr.bvar (x + (j + 1))
    rw [lift_zero_one_bvar, Nat.add_assoc]

/-- `policyLocals` is `policyParameterLocals` at zero stored fields. -/
theorem policyLocals_eq (np : Nat) :
    policyLocals np = policyParameterLocals np 0 := by
  simp [policyLocals, policyParameterLocals]

/-- `recIdx?` unfolds to the full-context spine decomposition of `D`. -/
theorem recIdx?_spec {f : Nat} {ls : List Level} {np j : Nat} {D : Expr Nat}
    {idx' : List (Expr Nat)}
    (h : recIdx? f ls np j D = some idx') :
    ∃ args : List (Expr Nat), appsSpine D = (.const f ls, args) ∧
      args.take np = policyParameterLocals np j ∧ args.drop np = idx' := by
  simp only [recIdx?] at h
  split at h
  next r ls' args heq =>
    by_cases h' : r = f ∧ ls' = ls ∧ args.take np = policyParameterLocals np j
    · rw [if_pos h'] at h
      obtain ⟨rfl, rfl, htk⟩ := h'
      exact ⟨args, heq, htk, Option.some.inj h⟩
    · rw [if_neg h'] at h
      cases h
  next heq => cases h

/-- the stored domain of a `.drec` field is the family applied to parameter
    locals and the unshifted indices — the `ctorDomsT` head shape. -/
theorem drec_head_of_recIdx {f : Nat} {ls : List Level} {np j : Nat}
    {D : Expr Nat} {idx' idx : List (Expr Nat)} {recs : List Bool}
    (hrec : recIdx? f ls np j D = some idx')
    (hidx : idx'.mapM (unshift? recs 0) = some idx)
    (hlen : j = recs.length) :
    D = foldApps (.const f ls)
      (policyParameterLocals np recs.length ++
        idx.map (substT (maskSubst recs))) := by
  obtain ⟨args, hspine, htk, hdrop⟩ := recIdx?_spec hrec
  rw [← hlen, mapM_unshift_substT _ _ hidx, ← hdrop, ← htk,
    List.take_append_drop]
  exact (foldApps_appsSpine D).symm.trans (by rw [hspine])

/-! ## (3) `fieldsOfA`: the factorization producer without a checker

`fieldsOfA` is `fieldsOf?` with the checker's `sortOf` replaced by the recorded
level map `lv` and its `whnfFuel`+`recIdx?` pair replaced by the oracle
`drecIdx?` (supplied by the caller; `whnfFuel`-based for the actual build).
-/

/-- a constructor's fields in the plain context, classified by `recIdx?` and
    the δ-oracle `drecIdx?`, leveled by the recorded map `lv`. -/
def fieldsOfA (f : Nat) (ls : List Level) (np : Nat) (lv : Nat → Level)
    (drecIdx? : Nat → Expr Nat → Option (List (Expr Nat))) :
    List Bool → List (Expr Nat) → Option (List FieldT)
  | _, [] => some []
  | recs, D :: ds =>
      match recIdx? f ls np recs.length D with
      | some idx' =>
          match idx'.mapM (unshift? recs 0) with
          | some idx =>
              (fieldsOfA f ls np lv drecIdx? (true :: recs) ds).map
                (.drec idx :: ·)
          | none => none
      | none =>
          match unshift? recs 0 D with
          | none => none
          | some D' =>
              match drecIdx? recs.length D with
              | some idx' =>
                  match idx'.mapM (unshift? recs 0) with
                  | some idx =>
                      (fieldsOfA f ls np lv drecIdx? (true :: recs) ds).map
                        (.drecD D' idx :: ·)
                  | none => none
              | none =>
                  (fieldsOfA f ls np lv drecIdx? (false :: recs) ds).map
                    (.plain D' (lv recs.length) :: ·)

/-- THE DOMAIN SPEC: `fieldsOfA` factorizes the stored domain list exactly as
    `ctorDomsT` rebuilds it, with the mask substitution as the threaded `σ`
    and the parameter locals at the mask length as `pl`. -/
theorem fieldsOfA_doms (f : Nat) (ls : List Level) (np : Nat) (lv : Nat → Level)
    (drecIdx? : Nat → Expr Nat → Option (List (Expr Nat))) :
    (recs : List Bool) → (ds : List (Expr Nat)) → (fs : List FieldT) →
      fieldsOfA f ls np lv drecIdx? recs ds = some fs →
        ds = ctorDomsT f ls (policyParameterLocals np recs.length)
          (maskSubst recs) fs
  | _, [], _, h => by cases h; rfl
  | recs, D :: ds, fs, h => by
      simp only [fieldsOfA] at h
      split at h
      next idx' hrec =>
          split at h
          next idx hidx =>
              simp only [Option.map_eq_some'] at h
              obtain ⟨fs', hfs', rfl⟩ := h
              show D :: ds =
                foldApps (.const f ls) (policyParameterLocals np recs.length ++
                  idx.map (substT (maskSubst recs))) ::
                ctorDomsT f ls
                  ((policyParameterLocals np recs.length).map (lift 0 1))
                  (maskSubst recs).shift1 fs'
              rw [List.cons.injEq]
              exact ⟨drec_head_of_recIdx hrec hidx rfl, by
                rw [maskSubst_cons_true, policyParameterLocals_lift_succ]
                exact fieldsOfA_doms f ls np lv drecIdx? (true :: recs) ds fs'
                  hfs'⟩
          next hidx => cases h
      next hrec =>
          split at h
          next hD => cases h
          next D' hD =>
              split at h
              next idx' hd =>
                  split at h
                  next idx hidx =>
                      simp only [Option.map_eq_some'] at h
                      obtain ⟨fs', hfs', rfl⟩ := h
                      show D :: ds = substT (maskSubst recs) D' ::
                        ctorDomsT f ls
                          ((policyParameterLocals np recs.length).map (lift 0 1))
                          (maskSubst recs).shift1 fs'
                      rw [List.cons.injEq]
                      exact ⟨(substT_mask_unshift hD).symm, by
                        rw [maskSubst_cons_true, policyParameterLocals_lift_succ]
                        exact fieldsOfA_doms f ls np lv drecIdx? (true :: recs)
                          ds fs' hfs'⟩
                  next hidx => cases h
              next hd =>
                  simp only [Option.map_eq_some'] at h
                  obtain ⟨fs', hfs', rfl⟩ := h
                  show D :: ds = substT (maskSubst recs) D' ::
                    ctorDomsT f ls
                      ((policyParameterLocals np recs.length).map (lift 0 1))
                      (maskSubst recs).up fs'
                  rw [List.cons.injEq]
                  exact ⟨(substT_mask_unshift hD).symm, by
                    rw [maskSubst_cons_false, policyParameterLocals_lift_succ]
                    exact fieldsOfA_doms f ls np lv drecIdx? (false :: recs)
                      ds fs' hfs'⟩

/-- the level written on a `.plain` output of `fieldsOfA` is `lv` at the
    field's global position. -/
theorem fieldsOfA_labels (f : Nat) (ls : List Level) (np : Nat)
    (lv : Nat → Level)
    (drecIdx? : Nat → Expr Nat → Option (List (Expr Nat))) :
    (recs : List Bool) → (ds : List (Expr Nat)) → (fs : List FieldT) →
      fieldsOfA f ls np lv drecIdx? recs ds = some fs →
      ∀ (j : Nat) (D : Expr Nat) (u : Level),
        fs[j]? = some (.plain D u) → u = lv (recs.length + j)
  | recs, [], fs, h => by
      cases h
      intro j D u hj
      simp at hj
  | recs, D₀ :: ds, fs, h => by
      intro j D u hj
      simp only [fieldsOfA] at h
      split at h
      next idx' hrec =>
          split at h
          next idx hidx =>
              simp only [Option.map_eq_some'] at h
              obtain ⟨fs', hfs', rfl⟩ := h
              cases j with
              | zero =>
                  rw [List.getElem?_cons_zero] at hj
                  cases hj
              | succ j =>
                  rw [List.getElem?_cons_succ] at hj
                  have ih := fieldsOfA_labels f ls np lv drecIdx? (true :: recs)
                    ds fs' hfs' j D u hj
                  rw [ih]; congr 1
                  show recs.length + 1 + j = recs.length + (j + 1)
                  omega
          next hidx => cases h
      next hrec =>
          split at h
          next hD => cases h
          next D' hD =>
              split at h
              next idx' hd =>
                  split at h
                  next idx hidx =>
                      simp only [Option.map_eq_some'] at h
                      obtain ⟨fs', hfs', rfl⟩ := h
                      cases j with
                      | zero =>
                          rw [List.getElem?_cons_zero] at hj
                          cases hj
                      | succ j =>
                          rw [List.getElem?_cons_succ] at hj
                          have ih := fieldsOfA_labels f ls np lv drecIdx?
                            (true :: recs) ds fs' hfs' j D u hj
                          rw [ih]; congr 1
                          show recs.length + 1 + j = recs.length + (j + 1)
                          omega
                  next hidx => cases h
              next hd =>
                  simp only [Option.map_eq_some'] at h
                  obtain ⟨fs', hfs', rfl⟩ := h
                  cases j with
                  | zero =>
                      rw [List.getElem?_cons_zero] at hj
                      cases hj
                      rfl
                  | succ j =>
                      rw [List.getElem?_cons_succ] at hj
                      have ih := fieldsOfA_labels f ls np lv drecIdx?
                        (false :: recs) ds fs' hfs' j D u hj
                      rw [ih]; congr 1
                      show recs.length + 1 + j = recs.length + (j + 1)
                      omega

/-! ## (4) the `CtorPlainFactorT` producer and its label alignment -/

/-- the recorded telescope level of `c`'s `k`-th field (defaulting out of
    range), read through `domainsTyped`. -/
def ctorFieldLv {A : ResolvedEnv} {family : PolicyFamilyView A}
    {member : CheckedMember} (c : PolicyConstructorView A family member)
    (k : Nat) : Level :=
  if h : c.parameters.length + k < (c.parameters ++ c.fields).length then
    c.domainsTyped.levels ⟨c.parameters.length + k, h⟩
  else .zero

/-- the recorded level map agrees with `fieldLevel` at every in-range field. -/
theorem ctorFieldLv_eq_fieldLevel {A : ResolvedEnv} {family : PolicyFamilyView A}
    {member : CheckedMember} (c : PolicyConstructorView A family member)
    (j : Fin c.fields.length) :
    ctorFieldLv c j.val = c.fieldLevel j := by
  have hj : c.parameters.length + j.val < (c.parameters ++ c.fields).length := by
    rw [List.length_append]; omega
  unfold ctorFieldLv
  rw [dif_pos hj]
  exact congrArg c.domainsTyped.levels (Fin.ext rfl)

/-- THE FACTORIZATION PRODUCER: a `fieldsOfA` run on the recorded fields, and
    an `unshift?` run on the result indices, give `CtorPlainFactorT` with no
    checker involved. `uP` is the mirror level vector (the caller's
    `fv.params.map Prod.snd`); `drecIdx?` is the caller's δ-read. -/
def ctorPlainFactorT_of {A : ResolvedEnv} {family : PolicyFamilyView A}
    {member : CheckedMember} (c : PolicyConstructorView A family member)
    (uP : List Level) (hP : uP.length = c.parameters.length)
    (drecIdx? : Nat → Expr Nat → Option (List (Expr Nat)))
    {fs : List FieldT}
    (hfs : fieldsOfA family.ref (policyFamilyLevels family) c.parameters.length
      (ctorFieldLv c) drecIdx? [] c.fields = some fs)
    {res : List (Expr Nat)}
    (hres : c.resultIndices.mapM
      (unshift? (fs.reverse.map FieldT.isRec) 0) = some res) :
    CtorPlainFactorT c where
  mirrors := c.parameters.zip uP
  fields := fs
  resultIndices := res
  parameters_eq := by
    have hz : (c.parameters.zip uP).map Prod.fst = c.parameters :=
      List.map_fst_zip c.parameters uP (by omega)
    exact hz.symm
  fields_eq := by
    have hml : (c.parameters.zip uP).length = c.parameters.length := by
      simp [hP]
    rw [hml, policyLocals_eq]
    have hd := fieldsOfA_doms family.ref (policyFamilyLevels family)
      c.parameters.length (ctorFieldLv c) drecIdx? [] c.fields fs hfs
    rw [← maskSubst_nil]
    exact hd
  result_eq := by
    rw [ctorEndSubstT_id]
    exact (mapM_unshift_substT _ _ hres).symm

/-- the produced factorization's label alignment — the syntactic half of
    `ConstructorPlainLabelsRemaining`, here discharged fully. -/
theorem ctorPlainLabelsRemaining_of {A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    (c : PolicyConstructorView A family member)
    (drecIdx? : Nat → Expr Nat → Option (List (Expr Nat)))
    {fs : List FieldT}
    (hfs : fieldsOfA family.ref (policyFamilyLevels family) c.parameters.length
      (ctorFieldLv c) drecIdx? [] c.fields = some fs) :
    ∀ (j : Fin c.fields.length) (D : Expr Nat) (u : Level),
      fs[j.val]? = some (.plain D u) → u = c.fieldLevel j := by
  intro j D u hj
  have hl := fieldsOfA_labels family.ref (policyFamilyLevels family)
    c.parameters.length (ctorFieldLv c) drecIdx? [] c.fields fs hfs j.val D u
    hj
  simp only [List.length_nil, Nat.zero_add] at hl
  exact hl.trans (ctorFieldLv_eq_fieldLevel c j)

/-- a `drecIdx?`-free run never emits `.drecD` — the `hsnd` gate is
    syntactic, not an admission hypothesis. -/
theorem fieldsOfA_noDrecD (f : Nat) (ls : List Level) (np : Nat) (lv : Nat → Level)
    {drecIdx? : Nat → Expr Nat → Option (List (Expr Nat))}
    (hnd : ∀ k e, drecIdx? k e = none) :
    (recs : List Bool) → (ds : List (Expr Nat)) → (fs : List FieldT) →
      fieldsOfA f ls np lv drecIdx? recs ds = some fs →
      ∀ d ∈ fs, d.isDrecD = false
  | _, [], fs, h => by
      cases h
      intro d hd
      cases hd
  | recs, D₀ :: ds, fs, h => by
      simp only [fieldsOfA] at h
      split at h
      next idx' hrec =>
          split at h
          next idx hidx =>
              simp only [Option.map_eq_some'] at h
              obtain ⟨fs', hfs', rfl⟩ := h
              intro d hd
              cases hd with
              | head => rfl
              | tail _ hmem =>
                  exact fieldsOfA_noDrecD f ls np lv hnd (true :: recs) ds fs'
                    hfs' d hmem
          next hidx => cases h
      next hrec =>
          split at h
          next hD => cases h
          next D' hD =>
              split at h
              next idx' hd =>
                  have hnone := hnd recs.length D₀
                  rw [hnone] at hd
                  cases hd
              next hd =>
                  simp only [Option.map_eq_some'] at h
                  obtain ⟨fs', hfs', rfl⟩ := h
                  intro d hd
                  cases hd with
                  | head => rfl
                  | tail _ hmem =>
                      exact fieldsOfA_noDrecD f ls np lv hnd (false :: recs)
                        ds fs' hfs' d hmem

/-! ## (5) the group assembly

`TelTyT`, `MirrorsConvT`, `FieldsTyT` and the scope typings are data: the
`Nonempty`-valued `*Remaining` forms cannot cross `Prop → Type`, so the
inputs below carry the raw evidence those remaining obligations name. The
`fieldsOfA` factorization supplies everything else syntactically. -/

/-- the recorded level list of a family view's parameters. -/
def familyParamLevels {A : ResolvedEnv} (v : PolicyFamilyView A) : List Level :=
  (List.range v.parameters.length).map fun i =>
    if h : i < v.parameters.length then
      v.domainsTyped.levels ⟨i, by rw [List.length_append]; omega⟩
    else .zero

/-- the recorded level list of a family view's indices. -/
def familyIndexLevels {A : ResolvedEnv} (v : PolicyFamilyView A) : List Level :=
  (List.range v.indices.length).map fun i =>
    if h : i < v.indices.length then
      v.domainsTyped.levels ⟨v.parameters.length + i, by
        rw [List.length_append]; omega⟩
    else .zero

/-- the assembled family view: the recorded levels label the stored
    parameters and indices; the sort is the recorded result level. -/
def famViewT_of {A : ResolvedEnv} {fm : CheckedMember} (v : PolicyFamilyView A)
    (hm : v.member = fm) (hprof : UniformProp v.resultLevel ∨ UniformType v.resultLevel) :
    FamViewT fm where
  params := v.parameters.zip (familyParamLevels v)
  indices := v.indices.zip (familyIndexLevels v)
  sort := v.resultLevel
  stored := by
    have hst := v.storedType
    rw [congrArg CheckedMember.mtype hm] at hst
    show fm.mtype = policyPi
      (((v.parameters.zip (familyParamLevels v)) ++
        (v.indices.zip (familyIndexLevels v))).map Prod.fst) (.sort v.resultLevel)
    rw [List.map_append, List.map_fst_zip v.parameters (familyParamLevels v)
      (by simp [familyParamLevels]),
      List.map_fst_zip v.indices (familyIndexLevels v) (by simp [familyIndexLevels])]
    exact hst
  profile := hprof

/-- the recorded levels are arity-bounded: the `hpb` field of
    `GroupInScopeT` comes free from `domainsTyped.bounded`. -/
theorem famViewT_levelBounded {A : ResolvedEnv} {fm : CheckedMember}
    (v : PolicyFamilyView A) (hm : v.member = fm)
    (hprof : UniformProp v.resultLevel ∨ UniformType v.resultLevel) :
    ∀ d ∈ (famViewT_of v hm hprof).params ++ (famViewT_of v hm hprof).indices,
      levelBounded fm.arity d.2 = true := by
  intro d hd
  have hmk : v.member.arity = fm.arity := congrArg CheckedMember.arity hm
  simp only [famViewT_of, List.mem_append] at hd
  rcases hd with hd | hd
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.of_mem_zip hd).2
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk
    have hplt : k < v.parameters.length := by
      simp only [familyParamLevels, List.length_map, List.length_range] at hlt
      exact hlt
    have hb := v.domainsTyped.bounded
      ⟨k, by rw [List.length_append]; omega⟩
    have hg : (familyParamLevels v)[k]'hlt = v.domainsTyped.levels
        ⟨k, by rw [List.length_append]; omega⟩ := by
      simp only [familyParamLevels, List.getElem_map, List.getElem_range,
        dif_pos hplt]
    exact (hget.symm.trans hg).symm ▸ (hmk ▸ hb)
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.of_mem_zip hd).2
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk
    have hilt : k < v.indices.length := by
      simp only [familyIndexLevels, List.length_map, List.length_range] at hlt
      exact hlt
    have hb := v.domainsTyped.bounded
      ⟨v.parameters.length + k, by rw [List.length_append]; omega⟩
    have hg : (familyIndexLevels v)[k]'hlt = v.domainsTyped.levels
        ⟨v.parameters.length + k, by rw [List.length_append]; omega⟩ := by
      simp only [familyIndexLevels, List.getElem_map, List.getElem_range,
        dif_pos hilt]
    exact (hget.symm.trans hg).symm ▸ (hmk ▸ hb)

/-- what one constructor contributes to the group's scope, at raw-evidence
    strength: the admission view `cview` lives at whatever prefix `A`
    admission ran in; the native typings are in `E` / ConstructorScope. -/
structure CtorScopeInputT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (fv : FamViewT fm) (cm : CheckedMember) : Type where
  A : ResolvedEnv
  family : PolicyFamilyView A
  cview : PolicyConstructorView A family cm
  hfm : family.member = fm
  href : family.ref = f
  hsort : family.resultLevel = fv.sort
  factor : CtorPlainFactorT cview
  labels : ConstructorPlainLabelsRemaining factor
  mirrorsConv : MirrorsConvT E fm.arity [] factor.mirrors fv.params
  fieldsTy : FieldsTyT E fm.arity (fun k => lift 0 k fv.idxTel)
    (telCtxT fv.params) 0 factor.fields factor.resultIndices
  univ : FieldUniverseAdmitted cview
  noDrecD : ∀ d ∈ factor.fields, d.isDrecD = false
  nobody : cm.body = none
  clT : ∀ k, lift k 1 cm.mtype = cm.mtype
  u : Level
  hT : HasTyT (extendEnv E f fm) cm.arity [] cm.mtype (.sort u)
  lvl : exprLevelsBounded cm.arity cm.mtype = true

/-- the constructor view from its input. -/
def ctorViewT_of {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {cm : CheckedMember}
    (i : CtorScopeInputT E f fm fv cm) : CtorViewT E f fm fv cm where
  mirrors := i.factor.mirrors
  fields := i.factor.fields
  res := i.factor.resultIndices
  stored := by
    have hst := i.factor.storedType
    have hls : policyFamilyLevels i.family = canonLevels fm.arity := by
      show (List.range i.family.member.arity).map Level.param =
        (List.range fm.arity).map Level.param
      rw [congrArg CheckedMember.arity i.hfm]
    rw [i.href, hls] at hst
    exact hst
  mirrorsConv := i.mirrorsConv
  typed := i.fieldsTy
  univ := by
    intro D u hd
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    have hflen : i.cview.fields.length = i.factor.fields.length := by
      rw [i.factor.fields_eq, ctorDomsT_length]
    have hl := i.labels ⟨j, hflen.symm ▸ hlt⟩ D u hj
    have hu := i.univ ⟨j, hflen.symm ▸ hlt⟩
    subst hl
    exact hu.elim (fun h => Or.inl (i.hsort ▸ h))
      (fun h => Or.inr ⟨i.hsort ▸ h.1, i.hsort ▸ h.2⟩)
  drecD_typed := drecDTypedT_of_absent i.noDrecD

/-- the `GroupCtorT` at a reference. -/
def groupCtorT_of {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} (r : Nat) {cm : CheckedMember}
    (i : CtorScopeInputT E f fm fv cm) : GroupCtorT E f fm fv where
  ref := r
  member := cm
  hcls := i.cview.hasClass
  hnobody := i.nobody
  harity := i.cview.arity.trans (congrArg CheckedMember.arity i.hfm)
  hclT := i.clT
  u := i.u
  hT := i.hT
  hlvl := i.lvl
  view := ctorViewT_of i

/-- what the recursor contributes: `stored` is the `policyRecursorType_eq`
    agreement applied over the built minor data. -/
structure RecScopeInputT (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (fv : FamViewT fm) (cs : List (GroupCtorT E f fm fv)) (rm : CheckedMember) :
    Type where
  nobody : rm.body = none
  clT : ∀ k, lift k 1 rm.mtype = rm.mtype
  elim : EliminationPolicy
  arity : rm.arity = policyRecursorArity fm.arity elim
  stored : rm.mtype = groupRecTypeT cs elim
  u : Level
  hT : HasTyT (groupEnvT E f fm (cs.map GroupCtorT.entry)) rm.arity [] rm.mtype
    (.sort u)
  lvl : exprLevelsBounded rm.arity rm.mtype = true

/-- the `GroupRecT` from its input. -/
def groupRecT_of {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {cs : List (GroupCtorT E f fm fv)} {rm : CheckedMember}
    (hcls : rm.mclass = .recursorM)
    (i : RecScopeInputT E f fm fv cs rm) : GroupRecT E f fm fv cs where
  member := rm
  hcls := hcls
  hnobody := i.nobody
  elim := i.elim
  harity := i.arity
  stored := i.stored
  hclT := i.clT
  u := i.u
  hT := i.hT
  hlvl := i.lvl

/-- the constructor list in layout order: `ctors`'s last entry added last. -/
def ctorList_of {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (fv : FamViewT fm) (ctors : List (Nat × CheckedMember))
    (input : (x : Nat × CheckedMember) → x ∈ ctors →
      CtorScopeInputT E f fm fv x.2) :
    List (GroupCtorT E f fm fv) :=
  ctors.reverse.attach.map fun ⟨x, hx⟩ =>
    groupCtorT_of x.1 (input x (List.mem_reverse.mp hx))

/-- the constructed list's entries are `ctors.reverse`. -/
theorem ctorList_of_entries {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (fv : FamViewT fm) (ctors : List (Nat × CheckedMember))
    (input : (x : Nat × CheckedMember) → x ∈ ctors →
      CtorScopeInputT E f fm fv x.2) :
    (ctorList_of fv ctors input).map GroupCtorT.entry = ctors.reverse := by
  unfold ctorList_of
  rw [List.map_map]
  show ctors.reverse.attach.map (fun x : {a // a ∈ ctors.reverse} =>
      (x.val.1, x.val.2)) = ctors.reverse
  have heta : (fun x : {a // a ∈ ctors.reverse} => (x.val.1, x.val.2)) =
      Subtype.val :=
    funext fun _ => rfl
  rw [heta]
  exact ctors.reverse.attach_map_subtype_val

/-- the constructed list's references, reversed, are the layout. -/
theorem ctorList_of_refs {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (fv : FamViewT fm) (ctors : List (Nat × CheckedMember))
    (input : (x : Nat × CheckedMember) → x ∈ ctors →
      CtorScopeInputT E f fm fv x.2) :
    (ctorList_of fv ctors input).reverse.map GroupCtorT.ref =
      ctors.map Prod.fst := by
  have he := ctorList_of_entries fv ctors input
  have hstep : (ctorList_of fv ctors input).reverse.map GroupCtorT.ref =
      ((ctorList_of fv ctors input).reverse.map GroupCtorT.entry).map
        Prod.fst := by
    rw [List.map_map]
    exact List.map_congr_left fun c _ => rfl
  rw [hstep, List.map_reverse, he, List.reverse_reverse]

/-- every constructed constructor carries no `.drecD`. -/
theorem ctorList_of_noDrecD {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (fv : FamViewT fm) (ctors : List (Nat × CheckedMember))
    (input : (x : Nat × CheckedMember) → x ∈ ctors →
      CtorScopeInputT E f fm fv x.2) :
    ∀ c ∈ ctorList_of fv ctors input,
      ∀ d ∈ c.view.fields, d.isDrecD = false := by
  intro c hc d hd
  simp only [ctorList_of, List.mem_map] at hc
  obtain ⟨a, -, rfl⟩ := hc
  exact (input a.1 (List.mem_reverse.mp a.2)).noDrecD d hd

/-- THE ASSEMBLY: from the family telescope typings, the per-constructor
    inputs, and the recursor input — the group's structured scope. The
    remaining obligations are the raw `TelTyT` / `MirrorsConvT` / `FieldsTyT`
    / scope typings inside the inputs; everything else is syntactic or
    already admission-supplied. -/
theorem groupInScopeT_of {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (fv : FamViewT fm) {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember}
    (htel : TelTyT E fm.arity [] (fv.params ++ fv.indices))
    (input : (x : Nat × CheckedMember) → x ∈ ctors →
      CtorScopeInputT E f fm fv x.2)
    (hrefs : ctors.map Prod.fst = List.range' (f + 1) ctors.length)
    (rinput : RecScopeInputT E f fm fv (ctorList_of fv ctors input) rm)
    (hcls : rm.mclass = .recursorM)
    (hrr : rr = f + 1 + ctors.length)
    (hpb : ∀ d ∈ fv.params ++ fv.indices, levelBounded fm.arity d.2 = true)
    (hprof : GroupProfileT (groupRecT_of hcls rinput)) :
    Nonempty (GroupInScopeT E f fm ctors rr rm) :=
  let cs := ctorList_of fv ctors input
  have hentries : cs.map GroupCtorT.entry = ctors.reverse :=
    ctorList_of_entries fv ctors input
  have hlen : cs.length = ctors.length := by
    have h := congrArg List.length hentries
    rwa [List.length_map, List.length_reverse] at h
  ⟨{ fv := fv
     htel := htel
     cs := cs
     hctors := by rw [hentries, List.reverse_reverse]
     hlayout := by
       show cs.reverse.map GroupCtorT.ref = List.range' (f + 1) cs.length
       rw [ctorList_of_refs, hlen]
       exact hrefs
     grec := groupRecT_of hcls rinput
     hrr := hrr.trans (congrArg (f + 1 + ·) hlen.symm)
     hrm := rfl
     hprof := hprof
     hpb := hpb
     hsnd := ctorList_of_noDrecD fv ctors input }⟩

end Rcic.Declarative
