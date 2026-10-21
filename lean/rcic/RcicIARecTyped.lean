import rcic.RcicIARecMotive
import rcic.RcicIATypedMinor
import rcic.RcicTypedEnvEntry
import rcic.ScmSrcGroupsKernelRfl
import rcic.ScmSrcGroupsEnvWfT0

/-!
# IA-021's typing composite on the typed root (glm segment 2)

`GroupMembersT.cons`'s premise for a recursor member is
`hT : HasTyT E m.arity [] m.mtype (.sort u)` (`RcicTypedEnv.lean:144`) — the cell's typing of
the stored recursor type, carried as DATA by the judgment. Before this module every route to it
ran the conversion checker (`sortTyAtC`, the srcEnvG route: `tyT3` in
`ScmSrcGroupsEnvWfT0.lean:33`) or a per-instance hand build (`listRecTypeTyT`,
`RcicTypedGroupPinsList.lean:490`). This module derives it from ADMISSION by gluing the
sealed pieces: the parameters and the motive (IA-017), the tail after the minors (the IA-021
skeleton), and — as the one premise admission's typed content does not yet pay — the minor
domains.

The sealed pieces state their conclusions as `Nonempty`, which cannot carry a derivation to
`GroupMembersT.cons`'s data field. So the module has two layers:

* DATA (`def`s, mirroring `hasTyT_familyConstTel`/`hasTyT_famLocals`'s idiom):
  `FamilyTelTypedT` / `MinorDomainsTyped` (the premises), `hasTyT_policyPi_buildD` and the
  `*D` twins of `familyParamTyped`/`familyIndexTyped`/`motiveType_typed`/`IA021T_tail_typed`
  (same statements, the derivation itself instead of its `Nonempty`), and
  `IA021T_recursor_typed` — the composite: admission + `EnvClosed E` + the two data premises
  give `Σ' u, HasTyT E m.arity [] m.mtype (.sort u)`, the `hsort` slot's admission-derived
  replacement.
* PROP (`IA021T_recursor_typed_nonempty`): the same composite stated as existence, gluing the
  SEALED `Nonempty` theorems themselves — `familyParamTyped`, `motiveType_typed`,
  `IA021T_tail_typed` — with `FamilyTypedT` (the Bool-leaf content `memberContentB_of`
  produces) as the family premise.

Pins at Nat's real recursor cell (srcEnvG slot 3): the family telescope premise is trivial
(Nat has no parameters or indices), the two minor domains are HAND-BUILT (zero's minor
`M zero` in the motive's context, succ's minor `Π (n : Nat) (ih : M n), M (succ n)` in the
context of zero's minor and the motive), the composite assembles the whole signature, and the
checker is the second instrument: it returns exactly the derived sort. The tooth: zero's minor
in succ's (off-by-one) context is refused.

Segments 3a+3b (cc ruling on #6458) close the minor premise's status: 3a's tooth shows
admission alone cannot pay it (the finding `[admission_minorTypes_untyped]` is named in the
3a section below), and 3b adds the checker-paid discharge `IA021T_minorDomains_of_check` —
per-minor `sortTyAtC` leaves at each minor's own context — wired into `GroupAcceptChain` as
`consRecCheck`, the alternative `consRec` source.

The forward minor typing — minor domains from the constructors' typed content, not a premise —
is NOT built; that is the honest open route on this row. `closure_claim` 0.
-/

namespace Rcic.Declarative

set_option maxRecDepth 8192

/-! ## (1) the data premises -/

/-- the family telescope's typed content as data: every parameter and index domain typed, in
    its prefix context, at the recorded level — `FamilyTypedT`'s content with the derivation
    instead of its `Nonempty`. -/
structure FamilyTelTypedT {E : ResolvedEnv} (v : PolicyFamilyView E) : Type where
  typed : ∀ i : Fin (v.parameters ++ v.indices).length,
    HasTyT E v.member.arity (policyPrefixContext (v.parameters ++ v.indices) i.val)
      (v.parameters ++ v.indices)[i.val] (.sort (v.domainsTyped.levels i))

/-- the family's typed content from the data telescope (the data premise implies the sealed
    `Nonempty` one). -/
theorem familyTypedT_of_tel {E : ResolvedEnv} {v : PolicyFamilyView E}
    (htel : FamilyTelTypedT v) : FamilyTypedT v :=
  fun i => ⟨htel.typed i⟩

/-- the composite's one premise admission's typed content does not yet pay: every stored minor
    domain typed in its minor context `minorCtxT a i` (the earlier minors, the motive, the
    parameters), at levels recorded as data. -/
structure MinorDomainsTyped {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Type where
  ws : ∀ i : Fin a.minorTypes.length, Level
  typed : ∀ i, HasTyT E m.arity (minorCtxT a i.val) (a.minorTypes[i.val]) (.sort (ws i))

/-! ## (2) the data tower build and the family's domains -/

/-- the tower build's data twin: domains typed in their prefix contexts and the body typed
    under the whole telescope give the Π-tower's derivation, at `piSortT`. The sealed
    `hasTyT_policyPi_build` is the same induction behind `Nonempty`; it cannot hand the
    derivation to a `GroupMembersT.cons` field, so the twin repeats it producing data. -/
def hasTyT_policyPi_buildD {E : ResolvedEnv} {n : Nat} :
    (ds : List (Expr Nat)) → {Γ : LCtx} → {body : Expr Nat} → {w : Level} →
    (ls : Fin ds.length → Level) →
    (∀ i : Fin ds.length,
      HasTyT E n (policyPrefixContext ds i.val ++ Γ) ds[i.val] (.sort (ls i))) →
    HasTyT E n (policyPrefixContext ds ds.length ++ Γ) body (.sort w) →
    HasTyT E n Γ (policyPi ds body) (.sort (piSortT ds.length ls w))
  | [], Γ, body, w, _, _, hb => by
      simpa only [policyPrefixContext, List.take_nil, List.reverse_nil, List.map_nil,
        List.nil_append, policyPi, piSortT, List.length_nil] using hb
  | A :: ds, Γ, body, w, ls, hd, hb => by
      have hctx : ∀ j, policyPrefixContext (A :: ds) (j + 1) ++ Γ =
          policyPrefixContext ds j ++ (.assumption A :: Γ) := by
        intro j
        have h := policyPrefixContext_append [A] ds j
        simp only [List.length_singleton, List.singleton_append] at h
        rw [Nat.add_comm, h]
        simp [policyPrefixContext]
      have hA : HasTyT E n Γ A (.sort (ls ⟨0, Nat.succ_pos _⟩)) := by
        simpa only [policyPrefixContext, List.take_zero, List.reverse_nil, List.map_nil,
          List.nil_append, List.getElem_cons_zero] using hd ⟨0, Nat.succ_pos _⟩
      have hb' : HasTyT E n (policyPrefixContext ds ds.length ++ (.assumption A :: Γ))
          body (.sort w) := by
        rw [← hctx]; exact hb
      have hB := hasTyT_policyPi_buildD ds (Γ := .assumption A :: Γ) (fun i => ls i.succ)
        (fun i => by
          have hi' : HasTyT E n (policyPrefixContext (A :: ds) (i.val + 1) ++ Γ) ds[i.val]
              (.sort (ls i.succ)) := hd i.succ
          rw [hctx] at hi'
          exact hi')
        hb'
      exact .pi Γ A _ (policyPi ds body) _ hA hB

/-- `familyParamTyped`'s data twin. -/
def familyParamTypedD {E : ResolvedEnv} (v : PolicyFamilyView E) (htel : FamilyTelTypedT v)
    {n' : Nat} (hn : v.member.arity ≤ n') (i : Fin v.parameters.length) :
    HasTyT E n' (policyPrefixContext v.parameters i.val) v.parameters[i.val]
      (.sort (v.domainsTyped.levels ⟨i.val, by rw [List.length_append]; omega⟩)) := by
  have h := htel.typed ⟨i.val, by rw [List.length_append]; omega⟩
  have hctx : policyPrefixContext (v.parameters ++ v.indices) i.val =
      policyPrefixContext v.parameters i.val := by
    simp only [policyPrefixContext, List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  have hget : (v.parameters ++ v.indices)[i.val]'(by rw [List.length_append]; omega) =
      v.parameters[i.val] := List.getElem_append_left i.isLt
  rw [hctx, hget] at h
  exact hasTyT_levelMono hn h

/-- `familyIndexTyped`'s data twin. -/
def familyIndexTypedD {E : ResolvedEnv} (v : PolicyFamilyView E) (htel : FamilyTelTypedT v)
    {n' : Nat} (hn : v.member.arity ≤ n') (j : Fin v.indices.length) :
    HasTyT E n'
      (policyPrefixContext v.indices j.val ++ policyPrefixContext v.parameters v.parameters.length)
      v.indices[j.val]
      (.sort (v.domainsTyped.levels ⟨v.parameters.length + j.val, by
        rw [List.length_append]; omega⟩)) := by
  have h := htel.typed ⟨v.parameters.length + j.val, by rw [List.length_append]; omega⟩
  have hget : (v.parameters ++ v.indices)[v.parameters.length + j.val]'(by
      rw [List.length_append]; omega) = v.indices[j.val] := by
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  rw [policyPrefixContext_append, hget] at h
  exact hasTyT_levelMono hn h

/-! ## (3) the motive and the tail, as data -/

/-- `motiveType_typed`'s data twin: the motive type of any family view, at any arity at least
    the family's. -/
def motiveType_typedD {E : ResolvedEnv} (hcl : EnvClosed E) (v : PolicyFamilyView E)
    (htel : FamilyTelTypedT v) (p : EliminationPolicy) {n' : Nat} (hn : v.member.arity ≤ n') :
    HasTyT E n' (policyPrefixContext v.parameters v.parameters.length)
      (policyMotiveType v p) (.sort (motiveSortT v p)) := by
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
  exact hasTyT_policyPi_buildD v.indices _
    (fun j => familyIndexTypedD v htel hn j) hbody

/-- the tail after the minors: its shape, and its derivation. `IA021T_tail_typed`'s data
    twin. -/
structure TailTypedD {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Type where
  T : Expr Nat
  w : Level
  stored : m.mtype = policyPi a.family.parameters
    (.pi (policyMotiveType a.family a.policy) (policyPi a.minorTypes T))
  typed : HasTyT E m.arity
    (policyPrefixContext a.minorTypes a.minorTypes.length ++
      (.assumption (policyMotiveType a.family a.policy) ::
        policyPrefixContext a.family.parameters a.family.parameters.length))
    T (.sort w)

/-- `IA021T_tail_typed`'s data twin: the rest of 05 §13's signature after the minors (the
    index binders lifted past the motive and the minors, the major `I params indices`, the
    body `motive indices major`), typed in the context of the parameters, the motive and the
    minors. It does not read the minors' contents. -/
def IA021T_tail_typedD {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hcl : EnvClosed E)
    (htel : FamilyTelTypedT a.family) : TailTypedD a := by
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
  let famApp := foldApps (.const a.family.ref (policyFamilyLevels a.family))
    (policyLocals (a.family.parameters.length + q))
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
  have hidx : ∀ j : Fin is'.length, HasTyT E m.arity
      (policyPrefixContext is' j.val ++ (Δ ++ Γp)) is'[j.val]
      (.sort (a.family.domainsTyped.levels ⟨a.family.parameters.length + j.val, by
        have hj := j.isLt; rw [List.length_append]; omega⟩)) := by
    intro j
    have hj : j.val < a.family.indices.length := by rw [hq, ← his'len]; exact j.isLt
    have h := familyIndexTypedD a.family htel hn ⟨j.val, hj⟩
    have hw := hasTyT_weakenUnderTel hcl a.family.indices j.val (Nat.le_of_lt hj) Δ h
    rw [hΔ] at hw
    have hget : is'[j.val] = lift j.val (k + 1) a.family.indices[j.val] := by
      show (liftDomsT 0 (k + 1) a.family.indices)[j.val] = _
      rw [getElem_liftDomsT (k + 1) a.family.indices 0 j.val hj, Nat.zero_add]
    simp only [lift] at hw
    rw [hget]
    exact hw
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
  have hb : HasTyT E m.arity (policyPrefixContext is' is'.length ++ (Δ ++ Γp))
      (.pi major result) (.sort (.imax a.family.resultLevel uM)) := by
    rw [his'len]; exact htail
  have hbuild := hasTyT_policyPi_buildD is' _ hidx hb
  rw [hCm] at hbuild
  exact ⟨_, _, hstored, by rw [hk]; exact hbuild⟩

/-! ## (4) the composite -/

/-- **IA-021's typing composite on the typed root.** At an admitted recursor, from
    admission's typed content — the family's parameter telescope, the motive (IA-017), the
    tail after the minors (the IA-021 skeleton) — plus the minor domains, the stored recursor
    type is typed at the empty context at the recursor's arity: exactly the
    `GroupMembersT.cons` premise for the recursor member, as data. Three tower builds: over
    the minor domains in the context of the motive and the parameters, over the motive in the
    parameters' context, over the parameters at the empty context. -/
def IA021T_recursor_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hcl : EnvClosed E)
    (htel : FamilyTelTypedT a.family) (hmin : MinorDomainsTyped a) :
    Σ' u, HasTyT E m.arity [] m.mtype (.sort u) := by
  have hn := family_arity_le_recursor a
  have htail := IA021T_tail_typedD a hcl htel
  -- the minor domains, in the tower build's context shape
  have hdomsM : ∀ i : Fin a.minorTypes.length, HasTyT E m.arity
      (policyPrefixContext a.minorTypes i.val ++
        (.assumption (policyMotiveType a.family a.policy) ::
          policyPrefixContext a.family.parameters a.family.parameters.length))
      (a.minorTypes[i.val]) (.sort (hmin.ws i)) := by
    intro i
    have h := hmin.typed i
    simp only [minorCtxT, List.append_nil] at h
    exact h
  have hinner := hasTyT_policyPi_buildD a.minorTypes hmin.ws hdomsM htail.typed
  -- the motive, in the parameters' context (the singleton tower built directly)
  have hmot := motiveType_typedD hcl a.family htel a.policy hn
  have hmid : HasTyT E m.arity (policyPrefixContext a.family.parameters a.family.parameters.length)
      (.pi (policyMotiveType a.family a.policy) (policyPi a.minorTypes htail.T))
      (.sort (.imax (motiveSortT a.family a.policy)
        (piSortT a.minorTypes.length hmin.ws htail.w))) :=
    .pi _ _ _ _ _ hmot hinner
  -- the parameters, at the empty context
  have hdomsP : ∀ i : Fin a.family.parameters.length, HasTyT E m.arity
      (policyPrefixContext a.family.parameters i.val ++ [])
      (a.family.parameters[i.val])
      (.sort (a.family.domainsTyped.levels ⟨i.val, by
        have hi := i.isLt; rw [List.length_append]; omega⟩)) := by
    intro i
    simpa only [List.append_nil] using familyParamTypedD a.family htel hn i
  have houter := hasTyT_policyPi_buildD a.family.parameters
    (fun i => a.family.domainsTyped.levels ⟨i.val, by
      have hi := i.isLt; rw [List.length_append]; omega⟩)
    hdomsP
    (by simpa only [List.append_nil] using hmid)
  rw [htail.stored]
  exact ⟨_, houter⟩

/-- the same composite stated as existence, gluing the SEALED `Nonempty` pieces themselves —
    `familyParamTyped`, `motiveType_typed`, `IA021T_tail_typed` — with `FamilyTypedT` (the
    Bool-leaf content `memberContentB_of` produces at a real cell) as the family premise. -/
theorem IA021T_recursor_typed_nonempty {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hcl : EnvClosed E)
    (hfamT : FamilyTypedT a.family) (hmin : MinorDomainsTyped a) :
    Nonempty (Σ' u, HasTyT E m.arity [] m.mtype (.sort u)) := by
  have hn := family_arity_le_recursor a
  obtain ⟨T, w, hdef, htail⟩ := IA021T_tail_typed a hcl hfamT
  have hdomsM : ∀ i : Fin a.minorTypes.length, Nonempty (HasTyT E m.arity
      (policyPrefixContext a.minorTypes i.val ++
        (.assumption (policyMotiveType a.family a.policy) ::
          policyPrefixContext a.family.parameters a.family.parameters.length))
      (a.minorTypes[i.val]) (.sort (hmin.ws i))) := by
    intro i
    have h := hmin.typed i
    simp only [minorCtxT, List.append_nil] at h
    exact ⟨h⟩
  have hinner := hasTyT_policyPi_build a.minorTypes (ls := hmin.ws) hdomsM htail
  have hmot := motiveType_typed hcl a.family hfamT a.policy hn
  obtain ⟨hmot⟩ := hmot
  obtain ⟨hinner⟩ := hinner
  have hmid : Nonempty (HasTyT E m.arity
      (policyPrefixContext a.family.parameters a.family.parameters.length)
      (.pi (policyMotiveType a.family a.policy) (policyPi a.minorTypes T))
      (.sort (.imax (motiveSortT a.family a.policy)
        (piSortT a.minorTypes.length hmin.ws w)))) :=
    ⟨.pi _ _ _ _ _ hmot hinner⟩
  have hdomsP : ∀ i : Fin a.family.parameters.length, Nonempty (HasTyT E m.arity
      (policyPrefixContext a.family.parameters i.val ++ [])
      (a.family.parameters[i.val])
      (.sort (a.family.domainsTyped.levels ⟨i.val, by
        have hi := i.isLt; rw [List.length_append]; omega⟩))) := by
    intro i
    simpa only [List.append_nil] using familyParamTyped a.family hfamT hn i
  have houter := hasTyT_policyPi_build a.family.parameters
    (ls := fun i => a.family.domainsTyped.levels ⟨i.val, by
      have hi := i.isLt; rw [List.length_append]; omega⟩)
    hdomsP
    (by simpa only [List.append_nil] using hmid)
  obtain ⟨houter⟩ := houter
  rw [hdef]
  exact ⟨_, houter⟩

/-! ## (5) pins at Nat's real recursor cell (srcEnvG slot 3)

Nat is the smallest real group: no parameters, no indices, `AnySort` (motive at `.param 0`,
recursor arity 1), two constructors. The family telescope premise is trivial (an empty
telescope); the two minor domains are HAND-BUILT — zero's minor `M zero` in the motive's
context, succ's minor `Π (n : Nat) (ih : M n), M (succ n)` in the context of zero's minor and
the motive — and the composite assembles the whole signature from them. The checker is the
second instrument: it returns exactly the derived sort. The tooth: zero's minor in succ's
(off-by-one) context is refused. -/

open Rcic.Scm.SrcG

/-- the prefix before the recursor is closed: `envPre 4` extends it by the fresh slot 3. -/
theorem envClosed_envPre3 : EnvClosed (envPre 3) := by
  have h : envPre 4 = extendEnv (envPre 3) 3 recN := by
    rw [envPre_succ (by decide)]; rfl
  have h4 : EnvClosed (extendEnv (envPre 3) 3 recN) := by
    rw [← h]; exact envClosed_of_envWfT wft4
  exact envClosed_of_extend_fresh h4 rfl

/-- the family's typed content at the recursor cell, from the region's own `famB3` leaf —
    the `Nonempty` premise of the Prop-layer pin. -/
theorem famTyped3 : FamilyTypedT dRec3.1.family := famTypedT_of (fuel := 96) _ famB3

/-- the family telescope premise at Nat's cell: the telescope is empty, so the field is
    vacuous. -/
def natFamTel : FamilyTelTypedT dRec3.1.family :=
  ⟨fun i => absurd i.isLt (by
    have h : (dRec3.1.family.parameters ++ dRec3.1.family.indices).length = 0 := rfl
    omega)⟩

/-- zero's minor `M zero` hand-built in its minor context (the motive alone: no earlier
    minors, no parameters): the motive variable applied to the constructor constant. -/
def natMinorZeroTyT :
    HasTyT (envPre 3) recN.arity (minorCtxT dRec3.1 0) (dRec3.1.minorTypes[0])
      (.sort (.param 0)) := by
  have hz : dRec3.1.minorTypes[0] = .app (.bvar 0) (.const 1 []) := by decide
  rw [hz]
  exact .app _ (.bvar 0) (.const 1 []) (.const 0 []) (.sort (.param 0))
    (.bvar _ 0 (.pi (.const 0 []) (.sort (.param 0))) rfl)
    (.const _ 1 [] mZero rfl rfl rfl)

/-- succ's minor `Π (n : Nat) (ih : M n), M (succ n)` hand-built in its minor context (zero's
    minor, the motive): the IH binder from the motive's own type at the field, the conclusion
    the motive at the constructor applied to the field. -/
def natMinorSuccTyT :
    HasTyT (envPre 3) recN.arity (minorCtxT dRec3.1 1) (dRec3.1.minorTypes[1])
      (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) := by
  have hs : dRec3.1.minorTypes[1] =
      .pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))) := by decide
  rw [hs]
  exact .pi _ (.const 0 []) (.succ .zero)
    (.pi (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))
    (.imax (.param 0) (.param 0))
    (.const _ 0 [] mN rfl rfl rfl)
    (.pi _ (.app (.bvar 2) (.bvar 0)) (.param 0)
      (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))) (.param 0)
      (.app _ (.bvar 2) (.bvar 0) (.const 0 []) (.sort (.param 0))
        (.bvar _ 2 (.pi (.const 0 []) (.sort (.param 0))) rfl)
        (.bvar _ 0 (.const 0 []) rfl))
      (.app _ (.bvar 3) (.app (.const 2 []) (.bvar 1)) (.const 0 []) (.sort (.param 0))
        (.bvar _ 3 (.pi (.const 0 []) (.sort (.param 0))) rfl)
        (.app _ (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
          (.const _ 2 [] mSucc rfl rfl rfl)
          (.bvar _ 1 (.const 0 []) rfl))))

/-- the composite's minor premise paid at Nat's cell: both stored minor domains hand-built
    in their contexts, at their recorded levels. -/
def natMinorDomains : MinorDomainsTyped dRec3.1 where
  ws i := match i with
    | ⟨0, _⟩ => .param 0
    | ⟨1, _⟩ => .imax (.succ .zero) (.imax (.param 0) (.param 0))
    | ⟨k+2, h⟩ => absurd h (by have : dRec3.1.minorTypes.length = 2 := rfl; omega)
  typed i := match i with
    | ⟨0, _⟩ => natMinorZeroTyT
    | ⟨1, _⟩ => natMinorSuccTyT
    | ⟨k+2, h⟩ => absurd h (by have : dRec3.1.minorTypes.length = 2 := rfl; omega)

/-- PIN (IA-021T composite, Nat, data): the recursor's stored type typed at the empty
    context — admission + the family telescope + the hand-built minor domains, no checker on
    the route. -/
def pin_IA021T_natRec : Σ' u, HasTyT (envPre 3) recN.arity [] recN.mtype (.sort u) :=
  IA021T_recursor_typed dRec3.1 envClosed_envPre3 natFamTel natMinorDomains

/-- PIN (IA-021T composite, Nat, Prop layer): the same cell's typing as existence, gluing the
    sealed `Nonempty` pieces, with the family's typed content from the region's own `famB3`
    leaf. -/
theorem pin_IA021T_natRec_nonempty :
    Nonempty (Σ' u, HasTyT (envPre 3) recN.arity [] recN.mtype (.sort u)) :=
  IA021T_recursor_typed_nonempty dRec3.1 envClosed_envPre3 famTyped3 natMinorDomains

-- SECOND INSTRUMENT (Nat): the conversion checker types the same stored type at exactly
-- the sort the composite derives — the admission-derived route and the checker route agree
-- on `u`.
kernel_rfl_theorem pin_IA021T_natRec_checker :
    (sortTyAtC (envPre 3) recN.arity 96 [] recN.mtype).map Sigma.fst = some pin_IA021T_natRec.1

-- TOOTH (off-by-one minor context): zero's minor refused in succ's context — the
-- off-by-one prefix the composite's premise could have read (`minorCtxT a 1` for minor 0).
-- There the motive is one binder too far out: `bvar 0` reads zero's minor, not the motive,
-- and the application is untypable.
kernel_rfl_theorem tooth_IA021T_nat_offByOne :
    (sortTyAtC (envPre 3) recN.arity 96 (minorCtxT dRec3.1 1)
      (dRec3.1.minorTypes[0]'(by have : dRec3.1.minorTypes.length = 2 := rfl; omega))).isSome
      = false

/-! ### 3a: the tooth — the record's `minorTypes` is a free list

Admission-soundness finding `[admission_minorTypes_untyped]` (named per cc's ruling on
#6458): nothing on the acceptance path runs a typing check on the stored minor types.
The record's fields touch `minorTypes` only through `minorCount` (a length) and
`recursorType` (an equation); `IndGroupAdmitted.recursor`'s `h12 : MinorPremisesMatch`
is a SHAPE equation (`derivedMinor = stored`), not a typing check; the Bool acceptance
leaves type the family, the constructors and the iota equations, but never a minor —
`memberScopeB` returns `true` outright at `.recursorM`, and `memberContentB`'s recursor
leaf runs `famTypedB`/`ctorTypedAllB`/`recIdxAdmittedTB`/`iotaEqB`, none of which reads
a minor as a type to check. The only routes that type a stored minor are the whole-type
checker leaf inverted through `recursorType` (`recursor_minorType_typed`), or the
chain's `MinorDomainsTyped` premise. The tooth below is the evidence that the premise
is genuine: an admission record exists whose minors no `MinorDomainsTyped` can cover,
so `admission → MinorDomainsTyped` is refutable, not merely unbuilt. -/

/-- the fabricated recursor member for the tooth: the real `recN` with its stored type
    swapped for the type `policyRecursorType` assembles from garbage minors — the one
    minor-dependent field equation (`recursorType`) is then paid by the swap itself.
    The admission record never requires the recursor member present (only
    `constructorsPresent` covers presence), so a phantom member serves. -/
def toothRecM : CheckedMember :=
  { recN with mtype :=
      policyRecursorType dRec3.1.family [.const 99 [], .const 99 []] dRec3.1.policy }

/-- Nat's admission with the stored minors swapped for same-length `.const 99` garbage:
    every field type of `RecursorEliminationAdmitted` still holds — `minorCount` is a
    length, `recursorType` is paid by the swapped member, the rest do not mention
    `minorTypes` at all. -/
def toothAdmGarbage : RecursorEliminationAdmitted (envPre 3) 3 toothRecM where
  family := dRec3.1.family
  constructors := dRec3.1.constructors
  constructorViews := dRec3.1.constructorViews
  constructorsPresent := dRec3.1.constructorsPresent
  recursorRef := dRec3.1.recursorRef
  minorTypes := [.const 99 [], .const 99 []]
  minorCount := by
    have h2 : dRec3.1.minorTypes.length = 2 := rfl
    have hlen := dRec3.1.minorCount
    rw [h2] at hlen
    simp only [List.length_cons, List.length_nil]
    exact hlen
  policy := dRec3.1.policy
  selected := dRec3.1.selected
  recursorArity := dRec3.1.recursorArity
  recursorType := rfl

/-- TOOTH (3a): `MinorDomainsTyped` is not derivable from admission. The record above
    inhabits every admission field with `.const 99` minors, and `.const 99` names no
    member of `envPre 3` (`hasTyT_constsIn`), so no `ws`/`typed` pair can cover it. The
    premise `consRec` pays by hand is therefore genuine, and the checker-paid discharge
    below is the complete route for checker-admitted groups. -/
theorem IA021T_minorDomains_not_of_admission :
    ∃ (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (a : RecursorEliminationAdmitted E r m), ¬ Nonempty (MinorDomainsTyped a) := by
  refine ⟨envPre 3, 3, toothRecM, toothAdmGarbage, ?_⟩
  rintro ⟨hmd⟩
  have hty := hmd.typed ⟨0, by
    have h : toothAdmGarbage.minorTypes.length = 2 := rfl; omega⟩
  have hc : ConstsIn (envPre 3) (Expr.const 99 []) := hasTyT_constsIn hty
  obtain ⟨m', hm'⟩ := hc
  have hnone : (envPre 3).members 99 = none := rfl
  rw [hnone] at hm'
  exact Option.noConfusion hm'

/-! ### 3b: the checker-paid discharge (C) -/

/-- the complete `MinorDomainsTyped` for checker-admitted groups: every stored minor
    sort-typed by the conversion checker at its own minor context. `sortTyAtC` returns
    the derivation as data (`Option (Σ u, HasTyT …)`), so one `.get` per minor pays both
    the level (`ws`) and the derivation (`typed`) — no hand-built tower, no choice. This
    is the per-minor checker route: costlier than the old single whole-type `cons` leaf
    (k leaves instead of one) but payable wherever nobody hand-builds the minors. -/
def IA021T_minorDomains_of_check {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Nat)
    (h : ∀ i : Fin a.minorTypes.length,
      (sortTyAtC E m.arity fuel (minorCtxT a i.val) (a.minorTypes[i.val])).isSome = true) :
    MinorDomainsTyped a where
  ws i := ((sortTyAtC E m.arity fuel (minorCtxT a i.val) (a.minorTypes[i.val])).get (h i)).1
  typed i :=
    ((sortTyAtC E m.arity fuel (minorCtxT a i.val) (a.minorTypes[i.val])).get (h i)).2

-- the per-minor checker leaves at Nat: both minors accepted by `sortTyAtC` in their own
-- contexts (the contexts the off-by-one tooth showed are misread one binder apart).
kernel_rfl_theorem natMinorChk0 :
    (sortTyAtC (envPre 3) recN.arity 96 (minorCtxT dRec3.1 0)
      (dRec3.1.minorTypes[0]'(by have : dRec3.1.minorTypes.length = 2 := rfl; omega))).isSome
      = true

kernel_rfl_theorem natMinorChk1 :
    (sortTyAtC (envPre 3) recN.arity 96 (minorCtxT dRec3.1 1)
      (dRec3.1.minorTypes[1]'(by have : dRec3.1.minorTypes.length = 2 := rfl; omega))).isSome
      = true

/-- the per-minor leaves packaged for `IA021T_minorDomains_of_check` at Nat's cell. -/
def natMinorChk : ∀ i : Fin dRec3.1.minorTypes.length,
    (sortTyAtC (envPre 3) recN.arity 96 (minorCtxT dRec3.1 i.val)
      (dRec3.1.minorTypes[i.val])).isSome = true
  | ⟨0, _⟩ => natMinorChk0
  | ⟨1, _⟩ => natMinorChk1
  | ⟨k+2, h⟩ => absurd h (by have : dRec3.1.minorTypes.length = 2 := rfl; omega)

/-- PIN (3b, Nat): the checker-paid `MinorDomainsTyped` — both minors' level and
    derivation read off `sortTyAtC`'s own output, no hand-built tower on the route. -/
def natMinorDomainsOfCheck : MinorDomainsTyped dRec3.1 :=
  IA021T_minorDomains_of_check dRec3.1 96 natMinorChk

-- SECOND INSTRUMENT (3b): the checker-paid premise yields the SAME sort as the
-- hand-built one — the composite's `u` agrees across the two minor sources.
kernel_rfl_theorem pin_IA021T_natRec_ofCheck_agree :
    (IA021T_recursor_typed dRec3.1 envClosed_envPre3 natFamTel natMinorDomainsOfCheck).1 =
    (IA021T_recursor_typed dRec3.1 envClosed_envPre3 natFamTel natMinorDomains).1

end Rcic.Declarative

#print axioms Rcic.Declarative.hasTyT_policyPi_buildD
#print axioms Rcic.Declarative.familyParamTypedD
#print axioms Rcic.Declarative.familyIndexTypedD
#print axioms Rcic.Declarative.motiveType_typedD
#print axioms Rcic.Declarative.IA021T_tail_typedD
#print axioms Rcic.Declarative.IA021T_recursor_typed
#print axioms Rcic.Declarative.IA021T_recursor_typed_nonempty
#print axioms Rcic.Declarative.natMinorDomains
#print axioms Rcic.Declarative.pin_IA021T_natRec
#print axioms Rcic.Declarative.pin_IA021T_natRec_nonempty
#print axioms Rcic.Declarative.toothRecM
#print axioms Rcic.Declarative.toothAdmGarbage
#print axioms Rcic.Declarative.IA021T_minorDomains_not_of_admission
#print axioms Rcic.Declarative.IA021T_minorDomains_of_check
#print axioms Rcic.Declarative.natMinorChk
#print axioms Rcic.Declarative.natMinorDomainsOfCheck
