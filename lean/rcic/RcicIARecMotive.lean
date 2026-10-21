import rcic.RcicIARecTel

/-!
# IA-017 on the typed root, and the recursor's skeleton (IA-rec segment A)

05 §11 (`docs/rcic/05_INDUCTIVE_ADMISSION.md:187-204`): the motive is
`M : Π indices, I params indices → Sort uM`, with `uM` the fresh universe parameter `n` under
`AnySort` (recursor arity `n + 1`) and `zero` under `PropOnly` (arity `n`). IA-017 (`05:360`) asks
that it be well formed.

Admission's recursor is `RecursorEliminationAdmitted` (`RcicInductivePolicy.lean:220`): its stored
type is `policyRecursorType family minorTypes policy` (`:202`), whose motive domain is
`policyMotiveType family policy` (`:191`). Before this module the only Lean on the row was
`instPrefix_recMotive` (`RcicAdmit.lean:1124`), a syntactic identity on the legacy ι witness.

The input is the typed content admission already carries at a recursor cell: `FamilyTypedT a.family`
(the first conjunct of `IndGroupTypedT (.recursor …)`, `RcicTypedEnv.lean:91`), typed at the family's
arity. No minor, no ι equation and no `hT` is read. The family's typings move to the recursor's arity
by `hasTyT_levelMono`.

* `IA017T_motive_well_formed`: the motive type is sort-typed in the parameters' context at the
  recursor's arity, at `motiveSortT` (the imax of the index sorts, the family's sort and `succ uM`);
  `uM` is in the recursor's level context; and it is the stored recursor type's motive domain.
* `IA021T_params_typed`, `IA021T_tail_typed`: the rest of 05 §13's signature that does not depend on
  the minors. The parameters, and the tail after the minors (the index binders lifted past the motive
  and the minors, the major `I params indices`, the body `motive indices major`), sort-typed in their
  contexts. With the motive, every binder of `m.mtype` except the minors is typed. The minors are
  segment D's obligation (forward minor typing); `hT` is assembled there.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) the family's constant and its self-application -/

theorem levelsBounded_policyFamilyLevels {E : ResolvedEnv} (v : PolicyFamilyView E) {n' : Nat}
    (hn : v.member.arity ≤ n') : levelsBounded n' (policyFamilyLevels v) = true :=
  levelsBounded_mono hn _ (levelsBounded_canonRecLevels v.member.arity)

/-- the family constant at its canonical levels is typed at its stored telescope, which is closed,
    so it is typed at that telescope lifted by any amount. -/
def hasTyT_familyConstTel {E : ResolvedEnv} (hcl : EnvClosed E) (v : PolicyFamilyView E) {n' : Nat}
    (hn : v.member.arity ≤ n') (Γ : LCtx) (k : Nat) :
    HasTyT E n' Γ (.const v.ref (policyFamilyLevels v))
      (lift 0 k (policyPi (v.parameters ++ v.indices) (.sort v.resultLevel))) :=
  have hty : instantiateLevels (policyFamilyLevels v) v.member.mtype =
      lift 0 k (policyPi (v.parameters ++ v.indices) (.sort v.resultLevel)) := by
    rw [show policyFamilyLevels v = Ann.canonLevelsA v.member.arity from rfl, Ann.instantiateLevels_canonA,
      ← v.storedType, lift_of_closed _ ((hcl _ _ v.present).1 0)]
  hty ▸ HasTyT.const Γ v.ref (policyFamilyLevels v) v.member v.present
    (by simp only [policyFamilyLevels, List.length_map, List.length_range])
    (levelsBounded_policyFamilyLevels v hn)

/-- `I params indices` over the locals of the family's whole telescope is typed at the family's
    sort, in that telescope's context. -/
def hasTyT_famLocals {E : ResolvedEnv} (hcl : EnvClosed E) (v : PolicyFamilyView E) {n' : Nat}
    (hn : v.member.arity ≤ n') (Γ : LCtx) :
    HasTyT E n' (policyPrefixContext (v.parameters ++ v.indices) (v.parameters ++ v.indices).length ++ Γ)
      (foldApps (.const v.ref (policyFamilyLevels v)) (policyLocals (v.parameters ++ v.indices).length))
      (.sort v.resultLevel) :=
  hasTyT_foldApps_policyLocals _ Γ _ _ (hasTyT_familyConstTel hcl v hn _ _)

/-! ## (2) the family's domains, read off `FamilyTypedT`, at a larger arity -/

theorem familyParamTyped {E : ResolvedEnv} (v : PolicyFamilyView E) (hfamT : FamilyTypedT v)
    {n' : Nat} (hn : v.member.arity ≤ n') (i : Fin v.parameters.length) :
    Nonempty (HasTyT E n' (policyPrefixContext v.parameters i.val) v.parameters[i.val]
      (.sort (v.domainsTyped.levels ⟨i.val, by rw [List.length_append]; omega⟩))) := by
  obtain ⟨h⟩ := hfamT ⟨i.val, by rw [List.length_append]; omega⟩
  have hctx : policyPrefixContext (v.parameters ++ v.indices) i.val =
      policyPrefixContext v.parameters i.val := by
    simp only [policyPrefixContext, List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  have hget : (v.parameters ++ v.indices)[i.val]'(by rw [List.length_append]; omega) =
      v.parameters[i.val] := List.getElem_append_left i.isLt
  rw [hctx, hget] at h
  exact ⟨hasTyT_levelMono hn h⟩

theorem familyIndexTyped {E : ResolvedEnv} (v : PolicyFamilyView E) (hfamT : FamilyTypedT v)
    {n' : Nat} (hn : v.member.arity ≤ n') (j : Fin v.indices.length) :
    Nonempty (HasTyT E n'
      (policyPrefixContext v.indices j.val ++ policyPrefixContext v.parameters v.parameters.length)
      v.indices[j.val]
      (.sort (v.domainsTyped.levels ⟨v.parameters.length + j.val, by rw [List.length_append]; omega⟩))) := by
  obtain ⟨h⟩ := hfamT ⟨v.parameters.length + j.val, by rw [List.length_append]; omega⟩
  have hget : (v.parameters ++ v.indices)[v.parameters.length + j.val]'(by
      rw [List.length_append]; omega) = v.indices[j.val] := by
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  rw [policyPrefixContext_append, hget] at h
  exact ⟨hasTyT_levelMono hn h⟩

/-! ## (3) IA-017: the motive is well formed -/

/-- the motive type's sort: the imax of the index sorts with `imax (family sort) (succ uM)`. -/
def motiveSortT {E : ResolvedEnv} (v : PolicyFamilyView E) (p : EliminationPolicy) : Level :=
  piSortT v.indices.length
    (fun j => v.domainsTyped.levels ⟨v.parameters.length + j.val, by rw [List.length_append]; omega⟩)
    (.imax v.resultLevel (.succ (policyMotiveLevel v.member.arity p)))

/-- the motive's universe is in the recursor's level context. -/
theorem policyMotiveLevel_bounded (n : Nat) (p : EliminationPolicy) :
    levelBounded (policyRecursorArity n p) (policyMotiveLevel n p) = true := by
  cases p
  · exact decide_eq_true (Nat.lt_succ_self n)
  · rfl

theorem family_arity_le_recursor {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : a.family.member.arity ≤ m.arity := by
  rw [a.recursorArity]
  cases a.policy
  · exact Nat.le_succ _
  · exact Nat.le_refl _

/-- the motive type of any family view, at any arity at least the family's. -/
theorem motiveType_typed {E : ResolvedEnv} (hcl : EnvClosed E) (v : PolicyFamilyView E)
    (hfamT : FamilyTypedT v) (p : EliminationPolicy) {n' : Nat} (hn : v.member.arity ≤ n') :
    Nonempty (HasTyT E n' (policyPrefixContext v.parameters v.parameters.length)
      (policyMotiveType v p) (.sort (motiveSortT v p))) := by
  have hlen : (v.parameters ++ v.indices).length = v.parameters.length + v.indices.length :=
    List.length_append _ _
  have hfam := hasTyT_famLocals hcl v hn []
  rw [hlen, List.append_nil, policyPrefixContext_append] at hfam
  have hbody : HasTyT E n'
      (policyPrefixContext v.indices v.indices.length ++
        policyPrefixContext v.parameters v.parameters.length)
      (.pi (foldApps (.const v.ref (policyFamilyLevels v))
          (policyLocals (v.parameters.length + v.indices.length)))
        (.sort (policyMotiveLevel v.member.arity p)))
      (.sort (.imax v.resultLevel (.succ (policyMotiveLevel v.member.arity p)))) :=
    .pi _ _ _ _ _ hfam (.sort _ _)
  exact hasTyT_policyPi_build v.indices _ (familyIndexTyped v hfamT hn) ⟨hbody⟩

/-- **IA-017 on the typed root.** At an admitted recursor (05 §11), from the family's typed content
    alone: the motive type is sort-typed in the parameters' context at the recursor's universe
    arity; the motive's universe `uM` is inside that arity (the fresh parameter `n` under `AnySort`,
    `zero` under `PropOnly`); and this motive type is the stored recursor type's motive domain. -/
theorem IA017T_motive_well_formed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hcl : EnvClosed E) (hfamT : FamilyTypedT a.family) :
    Nonempty (HasTyT E m.arity (policyPrefixContext a.family.parameters a.family.parameters.length)
        (policyMotiveType a.family a.policy) (.sort (motiveSortT a.family a.policy))) ∧
      levelBounded m.arity (policyMotiveLevel a.family.member.arity a.policy) = true ∧
      ∃ rest, m.mtype =
        policyPi a.family.parameters (.pi (policyMotiveType a.family a.policy) rest) := by
  refine ⟨motiveType_typed hcl a.family hfamT a.policy (family_arity_le_recursor a), ?_, ?_⟩
  · rw [a.recursorArity]; exact policyMotiveLevel_bounded _ _
  · exact ⟨_, a.recursorType⟩

/-! ## (4) the rest of the signature that does not read the minors -/

/-- the parameters of the stored recursor type, sort-typed at the recursor's arity. -/
theorem IA021T_params_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hfamT : FamilyTypedT a.family)
    (i : Fin a.family.parameters.length) :
    ∃ u, Nonempty (HasTyT E m.arity (policyPrefixContext a.family.parameters i.val)
      a.family.parameters[i.val] (.sort u)) :=
  ⟨_, familyParamTyped a.family hfamT (family_arity_le_recursor a) i⟩

theorem policyLocals_succ_eq (q : Nat) :
    (List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0] = policyLocals (q + 1) := by
  simp only [policyLocals, List.range_succ_eq_map, List.reverse_cons, List.map_append,
    List.map_reverse, List.map_map, List.map_cons, List.map_nil]
  rfl

theorem policyPrefixContext_snoc (ds : List (Expr Nat)) (x : Expr Nat) :
    policyPrefixContext (ds ++ [x]) (ds.length + 1) =
      .assumption x :: policyPrefixContext ds ds.length := by
  simp only [policyPrefixContext, List.take_length, List.take_of_length_le
    (by simp only [List.length_append, List.length_singleton]; omega : (ds ++ [x]).length ≤ ds.length + 1),
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.map_cons]

/-- the tail of 05 §13 after the minors: the index binders (lifted past the motive and the minors),
    the major `I params indices`, and the body `motive indices major`, sort-typed in the context of
    the parameters, the motive and the minors. It does not read the minors' contents. -/
theorem IA021T_tail_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hcl : EnvClosed E) (hfamT : FamilyTypedT a.family) :
    ∃ T w, m.mtype = policyPi a.family.parameters
        (.pi (policyMotiveType a.family a.policy) (policyPi a.minorTypes T)) ∧
      Nonempty (HasTyT E m.arity
        (policyPrefixContext a.minorTypes a.minorTypes.length ++
          (.assumption (policyMotiveType a.family a.policy) ::
            policyPrefixContext a.family.parameters a.family.parameters.length))
        T (.sort w)) := by
  -- names for the pieces of `policyRecursorType`
  have hn := family_arity_le_recursor a
  generalize hk : a.minorTypes.length = k
  generalize hq : a.family.indices.length = q
  let Mot := policyMotiveType a.family a.policy
  let uM := policyMotiveLevel a.family.member.arity a.policy
  let Γp := policyPrefixContext a.family.parameters a.family.parameters.length
  let Δ : LCtx := policyPrefixContext a.minorTypes k ++ [.assumption Mot]
  have hΔ : Δ.length = k + 1 := by
    simp only [Δ, policyPrefixContext, List.length_append, List.length_map, List.length_reverse,
      List.length_take, List.length_singleton, ← hk, Nat.min_self]
  have hCm : Δ ++ Γp = policyPrefixContext a.minorTypes k ++ (.assumption Mot :: Γp) := by
    simp only [Δ, List.append_assoc, List.singleton_append]
  let famApp := foldApps (.const a.family.ref (policyFamilyLevels a.family)) (policyLocals (a.family.parameters.length + q))
  let is' := liftDomsT 0 (k + 1) a.family.indices
  have his'len : is'.length = q := by rw [length_liftDomsT, hq]
  let major := foldApps (.const a.family.ref (policyFamilyLevels a.family))
    (policyParameterLocals a.family.parameters.length (k + 1 + q) ++ policyLocals q)
  have hmajor : major = lift q (k + 1) famApp := by
    show _ = lift q (k + 1) (foldApps _ (policyLocals (a.family.parameters.length + q)))
    rw [policyLocals_add, ← famLocalsT, ← policyMajor_eq]
  let result := foldApps (.bvar (k + q + 1))
    ((List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])
  have hres : result = foldApps (.bvar (k + q + 1)) (policyLocals (q + 1)) := by
    show foldApps _ _ = _
    rw [policyLocals_succ_eq]
  -- the stored type
  have hstored : m.mtype = policyPi a.family.parameters
      (.pi Mot (policyPi a.minorTypes (policyPi is' (.pi major result)))) := by
    rw [a.recursorType]
    simp only [policyRecursorType, hk, hq, mapIdx_lift_eq_liftDomsT]
  -- (i) the index binders
  have hidx : ∀ j : Fin is'.length, Nonempty (HasTyT E m.arity
      (policyPrefixContext is' j.val ++ (Δ ++ Γp)) is'[j.val]
      (.sort (a.family.domainsTyped.levels ⟨a.family.parameters.length + j.val, by
        have hj := j.isLt; rw [List.length_append]; omega⟩))) := by
    intro j
    have hj : j.val < a.family.indices.length := by rw [hq, ← his'len]; exact j.isLt
    obtain ⟨h⟩ := familyIndexTyped a.family hfamT hn ⟨j.val, hj⟩
    have hw := hasTyT_weakenUnderTel hcl a.family.indices j.val (Nat.le_of_lt hj) Δ h
    rw [hΔ] at hw
    have hget : is'[j.val] = lift j.val (k + 1) a.family.indices[j.val] := by
      show (liftDomsT 0 (k + 1) a.family.indices)[j.val] = _
      rw [getElem_liftDomsT (k + 1) a.family.indices 0 j.val hj, Nat.zero_add]
    simp only [lift] at hw
    rw [hget]
    exact ⟨hw⟩
  -- (ii) the major
  have hfam := hasTyT_famLocals hcl a.family hn []
  rw [List.length_append, List.append_nil, policyPrefixContext_append, hq] at hfam
  have hmaj := hasTyT_weakenUnderTel hcl a.family.indices q (Nat.le_of_eq hq.symm) Δ (Γ := Γp) hfam
  rw [hΔ, ← hq] at hmaj
  rw [hq] at hmaj
  have hmaj' : HasTyT E m.arity (policyPrefixContext is' q ++ (Δ ++ Γp)) major
      (.sort a.family.resultLevel) := by
    rw [hmajor]; simpa only [lift] using hmaj
  -- (iii) the body: the motive variable over the locals of the index binders and the major
  let ds := is' ++ [major]
  have hdslen : ds.length = q + 1 := by
    simp only [ds, List.length_append, List.length_singleton, his'len]
  have hctxB : policyPrefixContext ds ds.length ++ (Δ ++ Γp) =
      .assumption major :: (policyPrefixContext is' q ++ (Δ ++ Γp)) := by
    show policyPrefixContext (is' ++ [major]) (is' ++ [major]).length ++ _ = _
    rw [List.length_append, List.length_singleton, policyPrefixContext_snoc, his'len]
    rfl
  have hmotTy : lift 0 (k + 1) Mot = policyPi ds (.sort uM) := by
    show lift 0 (k + 1) (policyMotiveType a.family a.policy) = _
    simp only [policyMotiveType]
    rw [lift_policyPi]
    simp only [ds, policyPi_append, policyPi, lift, Nat.zero_add, hq]
    rw [hmajor]
  have hlook : lookupType (policyPrefixContext ds ds.length ++ (Δ ++ Γp)) (k + q + 1) =
      some (lift 0 ds.length (policyPi ds (.sort uM))) := by
    rw [hCm, ← List.append_assoc]
    have hL : (policyPrefixContext ds ds.length ++ policyPrefixContext a.minorTypes k).length =
        k + q + 1 := by
      simp only [policyPrefixContext, List.length_append, List.length_map, List.length_reverse,
        List.length_take, hdslen, ← hk, Nat.min_self]
      omega
    have := lookupType_append_assumption
      (policyPrefixContext ds ds.length ++ policyPrefixContext a.minorTypes k) Mot Γp
    rw [hL] at this
    rw [this, ← hmotTy, lift_lift_merge ds.length (k + 1) 0 0 (Nat.le_refl _) (Nat.zero_le _), hdslen]
    congr 2
    omega
  have hbodyT := hasTyT_foldApps_policyLocals (E := E) (n := m.arity) ds (Δ ++ Γp) (.sort uM)
    (.bvar (k + q + 1)) (.bvar _ _ _ hlook)
  rw [hctxB, hdslen, ← hres] at hbodyT
  -- (iv) the Π over the major, then (v) the telescope of index binders
  have htail : HasTyT E m.arity (policyPrefixContext is' q ++ (Δ ++ Γp)) (.pi major result)
      (.sort (.imax a.family.resultLevel uM)) := .pi _ _ _ _ _ hmaj' hbodyT
  have hb : Nonempty (HasTyT E m.arity (policyPrefixContext is' is'.length ++ (Δ ++ Γp))
      (.pi major result) (.sort (.imax a.family.resultLevel uM))) := by
    rw [his'len]; exact ⟨htail⟩
  have hbuild := hasTyT_policyPi_build is' _ hidx hb
  rw [hCm] at hbuild
  exact ⟨_, _, hstored, hbuild⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyT_familyConstTel
#print axioms Rcic.Declarative.hasTyT_famLocals
#print axioms Rcic.Declarative.motiveType_typed
#print axioms Rcic.Declarative.IA017T_motive_well_formed
#print axioms Rcic.Declarative.IA021T_params_typed
#print axioms Rcic.Declarative.IA021T_tail_typed
