/-
EG-010's GROUP half on the typed root (SWE-2, #6291): the generic theorem
`EG010T_group_accepted`.

`EnvWfT.group` (04 §7) extends an environment by one inductive group —
family, constructors, recursor — each member carrying an `IndGroupAdmitted`,
a stored-type typing `hT`, a ConstructorScope typing for constructor members,
the admission's typed content `IndGroupTypedT`, and the recursor/index
obligation `IdxAdmittedT`. The K3c work paid that bill per instance: the
`ScmSrcGroupsEnvWfT*` regions extracted the admission's views by matching
(`admFamView?`/`admCtorViews?`/`admRecData`), ran the checker's Bool leaves
(`famTypedB`, `ctorTypedB`, `ctorTypedAllB`, `recIdxAdmittedTB`, `iotaEqB`)
and lifted each through its soundness lemma (`famTypedT_of`, `ctorTypedT_of`,
`ctorTypedAll_of`, `idxT_of`, `iotaEqsT_of`).

This file generalizes that construction once: `memberAcceptB` is the one Bool
an accepted member must pass (structural + ConstructorScope + content), and
`GroupAcceptChain` is `GroupMembersT`'s paid-for counterpart — each `cons`
carries the admission, the `sortTyAtC` `.isSome` leaf, and the
`memberAcceptB` leaf at the checker-derived sort. `groupMembersT_of_chain`
lifts the leaves through their existing soundness lemmas (`.get` on the
`sortTyAtC` leaf is `⟨u, hT⟩`); `EG010T_group_accepted` applies
`EnvWfT.group`.

The recursor member's stored-type typing `hT` originally came only from the
`sortTyAtC` checker leaf — the srcEnvG route — NOT from admission. Segment 2
(glm, #6458) landed the admission-derived `hT` (`IA021T_recursor_typed`,
`RcicIARecTyped.lean`), and `consRec` resources the chain's recursor link from
it: the composite's premises (the prefix's closedness, the family telescope,
the minor domains) as fields, `hrec` tying the chain's admission to the
admission the typing derives from; the Bool leaves do not change.
-/
import rcic.RcicIARecTyped
import rcic.ScmSrcGroupsEnvWfTAux
import rcic.ScmSrcGroupsEnvWfT0
import rcic.ScmSrcGroupsKernelRfl
import rcic.RcicTypedGroupPins
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedIdxAdmittedPins

namespace Rcic.Declarative

open Rcic.Scm.SrcG (famTypedB famTypedT_of ctorTypedB ctorTypedT_of ctorTypedAllB
  ctorTypedAll_of iotaEqB iotaEqsT_of finAllB finAllB_of_each sortTyAtC idxT_of
  admFamView? admCtorViews? admRecData)

/-- the admission's freshness field, projected once for `GroupMembersT`. -/
def IndGroupAdmitted.fresh {E : ResolvedEnv} {r : Nat} {m : CheckedMember} :
    IndGroupAdmitted E r m → E.members r = none
  | .family h _ _ _ _ => h
  | .constructor _ _ h _ _ _ _ => h
  | .recursor _ h _ _ _ _ _ => h

/-- the member-structural leaves of `GroupMembersT.cons`, one Bool: no body,
    the stored type closed at 0 (the lift-stability premise), `.inductiveM`
    members an arity, levels bounded, fam-canonical, group-arity-coherent. -/
def memberStructB (E : ResolvedEnv) (m : CheckedMember) : Bool :=
  m.body.isNone && exprClosedAt 0 m.mtype &&
  (match m.mclass with | .inductiveM => isArity m.mtype | _ => true) &&
  exprLevelsBounded m.arity m.mtype && exprFamCanonical E m.mtype &&
  groupArityCoherent E m

theorem memberStructB_of {E : ResolvedEnv} {m : CheckedMember}
    (h : memberStructB E m = true) :
    m.body = none ∧ (∀ k, lift k 1 m.mtype = m.mtype) ∧
    (m.mclass = .inductiveM → isArity m.mtype = true) ∧
    exprLevelsBounded m.arity m.mtype = true ∧ exprFamCanonical E m.mtype = true ∧
    groupArityCoherent E m = true := by
  obtain ⟨mc, ar, mt, bd⟩ := m
  simp only [memberStructB, Bool.and_eq_true] at h
  refine ⟨?_, lift_id_of_exprClosedAt_zero h.1.1.1.1.2, ?_, h.1.1.2, h.1.2, h.2⟩
  · cases bd <;> simp_all
  · intro hmc
    have hmc' : mc = .inductiveM := hmc
    subst hmc'
    exact h.1.1.1.2

/-- the ConstructorScope leaf (05 §4): a constructor member's stored type
    checks in `S` at the very sort `u` its `hT` typing derived — `tyAtC`, the
    exact-type check, so the leaf's `u` is the one `GroupMembersT` needs.
    (The regions' `sortTyAtC` scope leaves infer their own `u'`; the generic
    statement must name `u`.) -/
def memberScopeB (S : ResolvedEnv) (fuel : Nat) (m : CheckedMember) (u : Level) : Bool :=
  match m.mclass with
  | .constructorM => (tyAtC S m.arity fuel [] m.mtype (.sort u)).isSome
  | _ => true

theorem memberScopeB_of {S : ResolvedEnv} {fuel : Nat} {m : CheckedMember} {u : Level}
    (h : memberScopeB S fuel m u = true) :
    m.mclass = .constructorM → Nonempty (HasTyT S m.arity [] m.mtype (.sort u)) := by
  obtain ⟨mc, ar, mt, bd⟩ := m
  intro hmc
  have hmc' : mc = .constructorM := hmc
  subst hmc'
  have h' : (tyAtC S ar fuel [] mt (.sort u)).isSome = true := h
  exact ⟨(tyAtC _ _ _ _ _ _).get h'⟩

/-- the typed-content leaves of `IndGroupTypedT`, plus the recursor's
    `IdxAdmittedT` conjunct, one Bool per admission shape — the same leaves
    the `ScmSrcGroupsEnvWfT*` regions used, matched out of `hadm` directly
    (the `.get` of `admFamView?`/`admCtorViews?`/`admRecData`, inlined). -/
def memberContentB (E : ResolvedEnv) (fuel : Nat) {r : Nat} {m : CheckedMember}
    (hadm : IndGroupAdmitted E r m) : Bool :=
  match hadm with
  | .family _ v _ _ _ => famTypedB (extendEnv E r m) fuel v
  | .constructor f v _ _ _ _ _ => famTypedB E fuel f && ctorTypedB fuel v
  | .recursor a _ _ _ _ _ h14 =>
      famTypedB E fuel a.family && ctorTypedAllB fuel a &&
      recIdxAdmittedTB a h14 &&
      finAllB a.constructors.length
        (iotaEqB (a := a) (h14 := h14) (synCheck (extendEnv E r m) m.arity))

/-- `memberContentB`'s leaf lifts `hadm` to `IdxAdmittedT × IndGroupTypedT`
    (the pair `GroupMembersT.cons` takes separately). The `&&` matcher folds
    a final operand `b` as `decide (b = true)`; `of_decide_eq_true` unwraps. -/
def memberContentB_of {E : ResolvedEnv} {fuel : Nat} {r : Nat} {m : CheckedMember} :
    (hadm : IndGroupAdmitted E r m) →
    memberContentB E fuel hadm = true →
    PProd (IdxAdmittedT hadm) (IndGroupTypedT hadm)
  | .family _ v _ _ _, h =>
      ⟨PUnit.unit, famTypedT_of v h⟩
  | .constructor f v _ _ _ _ _, h => by
      have h' : (famTypedB E fuel f && ctorTypedB fuel v) = true := h
      rw [Bool.and_eq_true] at h'
      exact ⟨PUnit.unit, ⟨famTypedT_of f h'.1, ctorTypedT_of h'.2⟩⟩
  | .recursor a _ _ _ _ _ h14, h => by
      have h' : (famTypedB E fuel a.family && ctorTypedAllB fuel a &&
          recIdxAdmittedTB a h14 &&
          finAllB a.constructors.length (iotaEqB (a := a) (h14 := h14)
            (synCheck (extendEnv E r m) m.arity))) = true := h
      simp only [Bool.and_eq_true] at h'
      exact ⟨idxT_of _ h'.1.2, ⟨famTypedT_of _ h'.1.1.1, ctorTypedAll_of h'.1.1.2,
        iotaEqsT_of h'.2⟩⟩

/-- one group member, paid for: structural + ConstructorScope + content
    leaves. `u` is the sort its `sortTyAtC`-derived typing lives at. -/
def memberAcceptB (S E : ResolvedEnv) (fuel : Nat) {r : Nat} {m : CheckedMember}
    (hadm : IndGroupAdmitted E r m) (u : Level) : Bool :=
  memberStructB E m && memberScopeB S fuel m u && memberContentB E fuel hadm

/-- the paid counterpart of `GroupMembersT`: every member carries its
    admission, the `sortTyAtC` `.isSome` Bool leaf (the `hT` slot — checker
    leaf per the srcEnvG route: `(sortTyAtC …).get h` is `⟨u, hT⟩`, exactly
    `tyT* := (sortTyAtC …).get tyB*`), and the `memberAcceptB` leaf at that
    checker-derived sort. A RECURSOR member may instead pay `consRec`: its
    `hT` derived from ADMISSION (segment 2's composite) rather than the
    checker leaf. -/
inductive GroupAcceptChain (S : ResolvedEnv) (fuel : Nat) :
    ResolvedEnv → List (Nat × CheckedMember) → ResolvedEnv → Type where
  | nil (E : ResolvedEnv) : GroupAcceptChain S fuel E [] E
  | cons (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (rest : List (Nat × CheckedMember)) (E' : ResolvedEnv)
      (hadm : IndGroupAdmitted E r m)
      (hsort : (sortTyAtC E m.arity fuel [] m.mtype).isSome = true)
      (hleaf : memberAcceptB S E fuel hadm
        ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1 = true)
      (hrest : GroupAcceptChain S fuel (extendEnv E r m) rest E') :
      GroupAcceptChain S fuel E ((r, m) :: rest) E'
  /-- the recursor member's `hT` re-sourced from ADMISSION: `IA021T_recursor_typed`
      at the admission's own family telescope and minor domains, replacing the
      `sortTyAtC` leaf for that member. `hrec` ties the chain's admission to the
      admission the typing derives from; the Bool leaf `memberAcceptB` stays, now
      at the admission-derived sort (its scope conjunct ignores `u` at
      `.recursorM`, so the leaf itself is unchanged). -/
  | consRec (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (rest : List (Nat × CheckedMember)) (E' : ResolvedEnv)
      (hadm : IndGroupAdmitted E r m)
      (a : RecursorEliminationAdmitted E r m)
      (hcl : EnvClosed E) (htel : FamilyTelTypedT a.family)
      (hmin : MinorDomainsTyped a)
      (hrec : ∃ (hfresh : E.members r = none)
          (h04 : CtorCensus E a.family.ref r)
          (h07 : ∀ i : Fin a.constructors.length, FieldUniverseAdmitted (a.constructorViews i))
          (h08 : ∀ i : Fin a.constructors.length, CtorFieldsPermitted (a.constructorViews i))
          (h12 : MinorPremisesMatch a)
          (h14 : IotaDescriptorClause E a),
        hadm = IndGroupAdmitted.recursor a hfresh h04 h07 h08 h12 h14)
      (hleaf : memberAcceptB S E fuel hadm (IA021T_recursor_typed a hcl htel hmin).1 = true)
      (hrest : GroupAcceptChain S fuel (extendEnv E r m) rest E') :
      GroupAcceptChain S fuel E ((r, m) :: rest) E'
  /-- 3b: the same admission-derived recursor link with the minor premise PAID BY THE
      CHECKER — per-minor `sortTyAtC` leaves at each minor's own context replace
      `consRec`'s hand-built `MinorDomainsTyped` tower (`IA021T_minorDomains_of_check`).
      Costlier than the hand route and than `cons`'s single whole-type leaf (k leaves
      instead of one), but payable at every checker-admitted group: nobody needs to
      hand-build the minors. Both `consRec` sources exist; the tooth
      `IA021T_minorDomains_not_of_admission` is why a source beyond admission itself
      is required. -/
  | consRecCheck (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (rest : List (Nat × CheckedMember)) (E' : ResolvedEnv)
      (hadm : IndGroupAdmitted E r m)
      (a : RecursorEliminationAdmitted E r m)
      (hcl : EnvClosed E) (htel : FamilyTelTypedT a.family)
      (hchk : ∀ i : Fin a.minorTypes.length,
        (sortTyAtC E m.arity fuel (minorCtxT a i.val) (a.minorTypes[i.val])).isSome = true)
      (hrec : ∃ (hfresh : E.members r = none)
          (h04 : CtorCensus E a.family.ref r)
          (h07 : ∀ i : Fin a.constructors.length, FieldUniverseAdmitted (a.constructorViews i))
          (h08 : ∀ i : Fin a.constructors.length, CtorFieldsPermitted (a.constructorViews i))
          (h12 : MinorPremisesMatch a)
          (h14 : IotaDescriptorClause E a),
        hadm = IndGroupAdmitted.recursor a hfresh h04 h07 h08 h12 h14)
      (hleaf : memberAcceptB S E fuel hadm
        (IA021T_recursor_typed a hcl htel (IA021T_minorDomains_of_check a fuel hchk)).1
          = true)
      (hrest : GroupAcceptChain S fuel (extendEnv E r m) rest E') :
      GroupAcceptChain S fuel E ((r, m) :: rest) E'

/-- `GroupMembersT` from a paid `GroupAcceptChain`: each leaf lifted through
    its existing soundness lemma — `memberStructB_of`, `memberScopeB_of`,
    `memberContentB_of` (`famTypedT_of`/`ctorTypedT_of`/`ctorTypedAll_of`/
    `idxT_of`/`iotaEqsT_of` inside), and `.get` on the `sortTyAtC` leaf for
    the `⟨u, hT⟩` pair; at a `consRec` link the `⟨u, hT⟩` pair is the
    admission-derived composite's own output. -/
def groupMembersT_of_chain {S : ResolvedEnv} {fuel : Nat} :
    {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupAcceptChain S fuel E ms E' → GroupMembersT S E ms E'
  | _, [], _, .nil _ => .nil _
  | E, (r, m) :: rest, E', .cons _ _ _ _ _ hadm hsort hleaf hrest => by
      have hl := hleaf
      simp only [memberAcceptB, Bool.and_eq_true] at hl
      obtain ⟨hb, hcl, har, hlvl, hcan, hcoh⟩ := memberStructB_of hl.1.1
      have hc := memberContentB_of hadm hl.2
      exact .cons E r m rest E' hadm.fresh hb hcl har hlvl hcan hcoh hadm hc.1
        ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1
        ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).2
        (memberScopeB_of hl.1.2) hc.2 (groupMembersT_of_chain hrest)
  | E, (r, m) :: rest, E', .consRec _ _ _ _ _ hadm a hcl htel hmin hrec hleaf hrest => by
      have hl := hleaf
      simp only [memberAcceptB, Bool.and_eq_true] at hl
      obtain ⟨hb, hcl', har, hlvl, hcan, hcoh⟩ := memberStructB_of hl.1.1
      have hc := memberContentB_of hadm hl.2
      exact .cons E r m rest E' hadm.fresh hb hcl' har hlvl hcan hcoh hadm hc.1
        (IA021T_recursor_typed a hcl htel hmin).1
        (IA021T_recursor_typed a hcl htel hmin).2
        (memberScopeB_of hl.1.2) hc.2 (groupMembersT_of_chain hrest)
  | E, (r, m) :: rest, E', .consRecCheck _ _ _ _ _ hadm a hcl htel hchk hrec hleaf hrest => by
      have hl := hleaf
      simp only [memberAcceptB, Bool.and_eq_true] at hl
      obtain ⟨hb, hcl', har, hlvl, hcan, hcoh⟩ := memberStructB_of hl.1.1
      have hc := memberContentB_of hadm hl.2
      exact .cons E r m rest E' hadm.fresh hb hcl' har hlvl hcan hcoh hadm hc.1
        (IA021T_recursor_typed a hcl htel (IA021T_minorDomains_of_check a fuel hchk)).1
        (IA021T_recursor_typed a hcl htel (IA021T_minorDomains_of_check a fuel hchk)).2
        (memberScopeB_of hl.1.2) hc.2 (groupMembersT_of_chain hrest)

/-- the `EnvWfT.group` member-class premises, one Bool. -/
def groupClassB (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (rm : CheckedMember) : Bool :=
  (match fm.mclass with | .inductiveM => true | _ => false) &&
  ctors.all (fun c => match c.2.mclass with | .constructorM => true | _ => false) &&
  (match rm.mclass with | .recursorM => true | _ => false)

theorem groupClassB_of {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    {rm : CheckedMember} (h : groupClassB fm ctors rm = true) :
    fm.mclass = .inductiveM ∧ (∀ c ∈ ctors, c.2.mclass = .constructorM) ∧
    rm.mclass = .recursorM := by
  obtain ⟨fmc, far, fmt, fb⟩ := fm
  obtain ⟨rmc, rar, rmt, rb⟩ := rm
  simp only [groupClassB, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · revert h
    cases fmc <;> simp_all
  · intro c hcm
    obtain ⟨cr, cmm⟩ := c
    obtain ⟨cmc, car, cmt, cb⟩ := cmm
    have hcc := List.all_eq_true.mp h.1.2 ⟨cr, cmc, car, cmt, cb⟩ hcm
    revert hcc
    cases cmc <;> simp_all
  · revert h
    cases rmc <;> simp_all

/-- EG-010's GROUP half: machine acceptance of an inductive group implies the
    `EnvWfT` extension. The group-membership premise is `GroupMembersT` with
    `S = extendEnv E f fm` (ConstructorScope); each member of the chain pays
    with `IndGroupAdmitted` + `sortTyAtC`-derived typing + `memberAcceptB`.
    This is the general form of `ScmSrcGroupsEnvWfT0.wft4` — the theorem the
    per-instance group assembly was a special case of. -/
def EG010T_group_accepted {E : ResolvedEnv} (hE : EnvWfT E) (fuel : Nat)
    {f : Nat} {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    {rr : Nat} {rm : CheckedMember} {E' : ResolvedEnv}
    (hclass : groupClassB fm ctors rm = true)
    (hchain : GroupAcceptChain (extendEnv E f fm) fuel E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    EnvWfT E' :=
  let ⟨hfam, hctors, hrec⟩ := groupClassB_of hclass
  .group E f fm ctors rr rm E' hE hfam hctors hrec (groupMembersT_of_chain hchain)

/-! ## DT-018 census B legs — the `Forall` discharged, the admission necessary

The row's open legs: (a) the legacy `EnvWf` inductive (RcicEnv:420) was
unsealed — now registered in `RcicFoundationSeal`; (b) `prem
Forall+IndGroupAdmitted` — the `∀ k, lift k 1 m.mtype = m.mtype` leaf
inside `DT018_inductive_extension_preserves` (RcicEnv:649) together with
the `IndGroupAdmitted` premise both anchors carry (`EG010T_group_accepted`'s
`GroupAcceptChain` pays `hadm` per link; `IndGroupAdmitted.recursor` itself
carries the `∀ i` census/field clauses).

The Forall is discharged: `memberStructB` already folds `hclT` (as
`exprClosedAt 0`) with `hnobody`/`harity`/`hlvlB`/`hcanon`/`harities` into
ONE decidable Bool — the same leaf `memberAcceptB` pays on the typed
chain route. The admission object is necessary: it is the admission
itself, not a checkable property of `E`/`m`. -/

/-- DT-018 Forall leg discharged: the six member-structural premises of
    `DT018_inductive_extension_preserves` collapse to the single Bool
    `memberStructB E m = true`. Remaining premises are the extension step
    (`hfresh`), the group class (`hind`), the recursor index (`hidxAdm`)
    and the admission (`hadm`). -/
def DT018_inductive_extension_preserves_of_memberStructB
    {E : ResolvedEnv} {n : Nat} {r : Nat} {m : CheckedMember}
    (hE : EnvWf E n) (hfresh : E.members r = none)
    (hind : m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨
      m.mclass = .recursorM)
    (hstruct : memberStructB E m = true)
    (hidxAdm : m.mclass = .recursorM → RecursorGroupIdxAdmitted E r m)
    (hadm : IndGroupAdmitted E r m) :
    EnvWf (extendEnv E r m) n := by
  obtain ⟨hnobody, hclT, harity, hlvlB, hcanon, harities⟩ :=
    memberStructB_of hstruct
  exact DT018_inductive_extension_preserves hE hfresh hind hnobody hclT
    harity hlvlB hcanon harities hidxAdm hadm

/-- PIN: the legacy `EnvWf` at `pinFamEnv` re-derived through the
    discharged route — `pinFamEnv_envWf`'s premises paid by one kernel
    check `memberStructB = true`, the `∀`-leaf never presented. -/
def pin_DT018_pinFamEnv_of_memberStructB (n : Nat) : EnvWf pinFamEnv n :=
  DT018_inductive_extension_preserves_of_memberStructB (.empty n) rfl
    (Or.inl rfl) (by decide) (fun h => absurd h (by decide))
    pinFamGroupAdmitted

/-- NECESSITY (`IndGroupAdmitted`): the premise is the admission object
    itself — it cannot be dropped or derived from the checkable leaves.
    The SAME family member passes `memberStructB` at `pinFamEnv`, yet at
    the OCCUPIED ref 0 no `IndGroupAdmitted` can exist: every constructor
    carries `hfresh`, and `.fresh` extracts `members 0 = none` against the
    occupant. The Bools alone would admit an overwrite; the admission
    object is what carries the step's freshness into the judgment —
    the same freshness `hext` (DT-013) reads. -/
theorem pin_DT018_adm_necessary :
    memberStructB pinFamEnv ⟨.inductiveM, 1, .sort .zero, none⟩ = true ∧
    ∀ m : CheckedMember, IndGroupAdmitted pinFamEnv 0 m → False :=
  ⟨by decide, fun _ hadm => by
    have hf := IndGroupAdmitted.fresh hadm
    simp [pinFamEnv, extendEnv] at hf⟩

end Rcic.Declarative

/-! ## pins

Three exercise sites (the plan's pin list): the srcEnvG Nat group cells
0–3 — the generic route re-derives `EnvWfT (envPre 4)` from the same Bool
leaves the region paid (`famB*`/`ctorB*`/`idxB3`/`iotaAllB3`) plus two
fresh `tyAtC` ConstructorScope evals — `listEnvUT`'s List group, and the
refused `badGroup` as the negative tooth. -/

set_option maxRecDepth 8192

namespace Rcic.Scm.SrcG

open Rcic.Declarative Rcic.Declarative.PosList Rcic.Scm.SrcG

-- ConstructorScope for the two constructor members: `tyAtC` on their
-- stored types in the family-alone env at the `sortTyAtC`-derived sort.
-- (`tyS1`/`tyS2` in the region proved `sortTyAtC`-isSome at the same
-- inputs; `memberScopeB` needs the exact-sort `tyAtC` at `tyT*.1`.)
kernel_rfl_theorem eg010G_scB1 :
    memberScopeB (extendEnv (envPre 0) 0 mN) 96 mZero tyT1.1 = true

kernel_rfl_theorem eg010G_scB2 :
    memberScopeB (extendEnv (envPre 0) 0 mN) 96 mSucc tyT2.1 = true

/-- per-member acceptance for the Nat group, each assembled from the
    region's existing leaves. -/
theorem eg010G_acc0 :
    memberAcceptB (extendEnv (envPre 0) 0 mN) (envPre 0) 96 admFamN tyT0.1 = true := by
  simp only [memberAcceptB, Bool.and_eq_true]
  exact ⟨⟨rfl, rfl⟩, famB0⟩

theorem eg010G_acc1 :
    memberAcceptB (extendEnv (envPre 0) 0 mN) (envPre 1) 96 admCtorZero tyT1.1 = true := by
  simp only [memberAcceptB, Bool.and_eq_true]
  refine ⟨⟨rfl, eg010G_scB1⟩, ?_⟩
  decide

theorem eg010G_acc2 :
    memberAcceptB (extendEnv (envPre 0) 0 mN) (envPre 2) 96 admCtorSucc tyT2.1 = true := by
  simp only [memberAcceptB, Bool.and_eq_true]
  refine ⟨⟨rfl, eg010G_scB2⟩, ?_⟩
  decide

theorem eg010G_acc3 :
    memberAcceptB (extendEnv (envPre 0) 0 mN) (envPre 3) 96 admRecN tyT3.1 = true := by
  simp only [memberAcceptB, Bool.and_eq_true]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  show (famTypedB (envPre 3) 96 dRec3.1.family && ctorTypedAllB 96 dRec3.1 &&
      recIdxAdmittedTB dRec3.1 dRec3.2 &&
      finAllB dRec3.1.constructors.length
        (iotaEqB (a := dRec3.1) (h14 := dRec3.2)
          (synCheck (extendEnv (envPre 3) 3 recN) recN.arity))) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨famB3, ctorB3⟩, idxB3⟩, iotaAllB3⟩

/-- the paid chain over slot cells 0–3 — the group-membership premise the
    `envPre 4` step of `wft_srcEnvG` carried by hand. -/
def eg010G_natChain :
    GroupAcceptChain (extendEnv (envPre 0) 0 mN) 96 (envPre 0)
      [(0, mN), (1, mZero), (2, mSucc), (3, recN)]
      (extendEnv (envPre 3) 3 recN) :=
  .cons (envPre 0) 0 mN _ _ admFamN tyB0 eg010G_acc0
    (.cons (envPre 1) 1 mZero _ _ admCtorZero tyB1 eg010G_acc1
      (.cons (envPre 2) 2 mSucc _ _ admCtorSucc tyB2 eg010G_acc2
        (.cons (envPre 3) 3 recN _ _ admRecN tyB3 eg010G_acc3
          (.nil _))))

/-- PIN: `EG010T_group_accepted` on the Nat group re-derives
    `EnvWfT (envPre 4)` — the group half of `envWfT_srcEnvG` through the
    generic route. -/
def pin_EG010T_srcNatGroup : EnvWfT (envPre 4) :=
  wfTOfExtend (by decide) rfl
    (EG010T_group_accepted (hE := .empty) 96
      (rfl : groupClassB mN [(1, mZero), (2, mSucc)] recN = true) eg010G_natChain)

/-! ### 2b: the recursor link re-sourced from admission (`consRec`) -/

-- the recursor link's Bool leaf at the admission-derived sort: for `.recursorM`
-- the scope conjunct ignores `u`, so this is the region's own content leaf
-- (`eg010G_acc3`'s), unchanged, evaluated at the composite's sort.
theorem eg010G_natAcc3Rec :
    memberAcceptB (extendEnv (envPre 0) 0 mN) (envPre 3) 96 admRecN
      (IA021T_recursor_typed dRec3.1 envClosed_envPre3 natFamTel natMinorDomains).1 = true := by
  simp only [memberAcceptB, Bool.and_eq_true]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  show (famTypedB (envPre 3) 96 dRec3.1.family && ctorTypedAllB 96 dRec3.1 &&
      recIdxAdmittedTB dRec3.1 dRec3.2 &&
      finAllB dRec3.1.constructors.length
        (iotaEqB (a := dRec3.1) (h14 := dRec3.2)
          (synCheck (extendEnv (envPre 3) 3 recN) recN.arity))) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨famB3, ctorB3⟩, idxB3⟩, iotaAllB3⟩

/-- PIN (2b, Nat): the group chain with the recursor link's `hT` RE-SOURCED from
    admission — `consRec` at slot 3, the composite applied at the admission's own
    family telescope and the hand-built minor domains, `hrec` tying the chain's
    admission to the admission the typing derives from. The other three links keep
    the checker route; the Bool leaf at the recursor runs at the admission-derived
    sort. -/
def eg010G_natChainRec :
    GroupAcceptChain (extendEnv (envPre 0) 0 mN) 96 (envPre 0)
      [(0, mN), (1, mZero), (2, mSucc), (3, recN)]
      (extendEnv (envPre 3) 3 recN) :=
  .cons (envPre 0) 0 mN _ _ admFamN tyB0 eg010G_acc0
    (.cons (envPre 1) 1 mZero _ _ admCtorZero tyB1 eg010G_acc1
      (.cons (envPre 2) 2 mSucc _ _ admCtorSucc tyB2 eg010G_acc2
        (.consRec (envPre 3) 3 recN _ _ admRecN dRec3.1 envClosed_envPre3 natFamTel
          natMinorDomains ⟨_, _, _, _, _, _, rfl⟩ eg010G_natAcc3Rec
          (.nil _))))

/-- PIN (2b): `EG010T_group_accepted` on the Nat group with the recursor's `hT`
    admission-derived end to end — the same conclusion as the checker-routed pin
    (`EnvWfT (envPre 4)`), the conversion checker no longer on the recursor
    member's typing route. -/
def pin_EG010T_natGroupRec : EnvWfT (envPre 4) :=
  wfTOfExtend (by decide) rfl
    (EG010T_group_accepted (hE := .empty) 96
      (rfl : groupClassB mN [(1, mZero), (2, mSucc)] recN = true) eg010G_natChainRec)

/-! ### 3b: the same recursor link with the minor premise PAID BY THE CHECKER (`consRecCheck`) -/

-- the recursor link's Bool leaf at the checker-paid composite's sort: the sort agrees
-- with the hand route (`pin_IA021T_natRec_ofCheck_agree`), so this is `eg010G_natAcc3Rec`'s
-- own leaf — the scope conjunct ignores `u` at `.recursorM`.
theorem eg010G_natAcc3RecCheck :
    memberAcceptB (extendEnv (envPre 0) 0 mN) (envPre 3) 96 admRecN
      (IA021T_recursor_typed dRec3.1 envClosed_envPre3 natFamTel natMinorDomainsOfCheck).1
      = true := by
  rw [pin_IA021T_natRec_ofCheck_agree]
  exact eg010G_natAcc3Rec

/-- PIN (3b, Nat): the group chain with the recursor link's minor premise paid by the
    per-minor checker route — `consRecCheck` at slot 3, both minor leaves computed by
    `sortTyAtC` at their own contexts (`natMinorChk`), no hand-built minor tower and no
    whole-type checker leaf on the recursor's typing route. -/
def eg010G_natChainRecCheck :
    GroupAcceptChain (extendEnv (envPre 0) 0 mN) 96 (envPre 0)
      [(0, mN), (1, mZero), (2, mSucc), (3, recN)]
      (extendEnv (envPre 3) 3 recN) :=
  .cons (envPre 0) 0 mN _ _ admFamN tyB0 eg010G_acc0
    (.cons (envPre 1) 1 mZero _ _ admCtorZero tyB1 eg010G_acc1
      (.cons (envPre 2) 2 mSucc _ _ admCtorSucc tyB2 eg010G_acc2
        (.consRecCheck (envPre 3) 3 recN _ _ admRecN dRec3.1 envClosed_envPre3 natFamTel
          natMinorChk ⟨_, _, _, _, _, _, rfl⟩ eg010G_natAcc3RecCheck
          (.nil _))))

/-- PIN (3b): `EG010T_group_accepted` end to end on the checker-paid recursor link —
    the same `EnvWfT (envPre 4)` conclusion, both `consRec` sources now exercised at
    Nat. -/
def pin_EG010T_natGroupRecCheck : EnvWfT (envPre 4) :=
  wfTOfExtend (by decide) rfl
    (EG010T_group_accepted (hE := .empty) 96
      (rfl : groupClassB mN [(1, mZero), (2, mSucc)] recN = true) eg010G_natChainRecCheck)

/-! ### `listEnvUT`: the List group over `natEnvU` -/

-- the `sortTyAtC` `.isSome` leaves for the List group's four members — the
-- `hT` source, checker-derived exactly as the Nat group's `tyB*`.
kernel_rfl_theorem eg010G_listSortB8 :
    (sortTyAtC natEnvU raisedFam.arity 96 [] raisedFam.mtype).isSome = true

kernel_rfl_theorem eg010G_listSortB9 :
    (sortTyAtC listFamOnlyU listUNilMember.arity 96 [] listUNilMember.mtype).isSome = true

kernel_rfl_theorem eg010G_listSortB10 :
    (sortTyAtC listFamNilU listUConsMember.arity 96 [] listUConsMember.mtype).isSome = true

kernel_rfl_theorem eg010G_listSortB11 :
    (sortTyAtC listPrefixU listURecMember.arity 96 [] listURecMember.mtype).isSome = true

-- per-member acceptance for the List group, one kernel eval each — the
-- ConstructorScope check runs at the `sortTyAtC`-derived sort.
kernel_rfl_theorem eg010G_listAcc0 :
    memberAcceptB listFamOnlyU natEnvU 96 listFamAdmittedU
      ((sortTyAtC natEnvU raisedFam.arity 96 [] raisedFam.mtype).get
        eg010G_listSortB8).1 = true

kernel_rfl_theorem eg010G_listAcc1 :
    memberAcceptB listFamOnlyU listFamOnlyU 96 listNilAdmittedU
      ((sortTyAtC listFamOnlyU listUNilMember.arity 96 [] listUNilMember.mtype).get
        eg010G_listSortB9).1 = true

kernel_rfl_theorem eg010G_listAcc2 :
    memberAcceptB listFamOnlyU listFamNilU 96 listConsAdmittedU
      ((sortTyAtC listFamNilU listUConsMember.arity 96 [] listUConsMember.mtype).get
        eg010G_listSortB10).1 = true

kernel_rfl_theorem eg010G_listAcc3 :
    memberAcceptB listFamOnlyU listPrefixU 96 listRecAdmittedU
      ((sortTyAtC listPrefixU listURecMember.arity 96 [] listURecMember.mtype).get
        eg010G_listSortB11).1 = true

def eg010G_listChain :
    GroupAcceptChain listFamOnlyU 96 natEnvU
      [(8, raisedFam), (9, listUNilMember), (10, listUConsMember),
        (11, listURecMember)] listEnvUT :=
  .cons natEnvU 8 raisedFam _ _ listFamAdmittedU eg010G_listSortB8 eg010G_listAcc0
    (.cons listFamOnlyU 9 listUNilMember _ _ listNilAdmittedU eg010G_listSortB9
      eg010G_listAcc1
      (.cons listFamNilU 10 listUConsMember _ _ listConsAdmittedU eg010G_listSortB10
        eg010G_listAcc2
        (.cons listPrefixU 11 listURecMember _ _ listRecAdmittedU eg010G_listSortB11
          eg010G_listAcc3 (.nil _))))

/-- PIN: `EG010T_group_accepted` on the List group re-derives
    `EnvWfT listEnvUT` — the same environment `listEnvUWfT` built
    per-instance. -/
def pin_EG010T_listGroup : EnvWfT listEnvUT :=
  EG010T_group_accepted (hE := natEnvUWfT) 96
    (rfl : groupClassB raisedFam
      [(9, listUNilMember), (10, listUConsMember)] listURecMember = true)
    eg010G_listChain

/-! ### the refused group (negative tooth) -/

/-- `badMkEnv`'s member table — three slots, then nothing. -/
theorem eg010G_badMem (c : Nat) :
    badMkEnv.members c =
      (if c = 2 then some badMkMember
       else if c = 1 then some badFamMember
       else if c = 0 then some badHeadMember
       else none) := by
  simp [badMkEnv, badFamEnv, badBase, extendEnv, emptyEnv]

/-- the census: `mk` at 2 is the family's only constructor before 3. -/
theorem eg010G_badCensus : CtorCensus badMkEnv badGroupAdmitted.family.ref 3 := by
  have hfr : badGroupAdmitted.family.ref = 1 := rfl
  rw [hfr]
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hmem, hclass, _⟩
    rw [eg010G_badMem] at hmem
    by_cases h2 : c = 2
    · rw [if_pos h2] at hmem
      cases hmem
      exact ⟨by omega, by omega⟩
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hmem
        cases hmem
        exact absurd hclass (by decide)
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hmem
          cases hmem
          exact absurd hclass (by decide)
        · rw [if_neg h2, if_neg h1, if_neg h0] at hmem
          cases hmem
  · rintro ⟨h1, h2⟩
    have hc : c = 2 := by omega
    subst hc
    exact ⟨badMkMember, rfl, rfl, rfl⟩

/-- the field is at `Sort 1` — under the family's `Type 1` result level it is
    universe-admitted (the malformedness lives elsewhere). -/
theorem eg010G_badFieldUnivs_view : FieldUniverseAdmitted badMkView := by
  intro j
  obtain ⟨v, hv⟩ := j
  have hlen : badMkView.fields.length = 1 := rfl
  have : v = 0 := by omega
  subst this
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem eg010G_badFieldUnivs (i : Fin badGroupAdmitted.constructors.length) :
    FieldUniverseAdmitted (badGroupAdmitted.constructorViews i) := by
  obtain ⟨v, hv⟩ := i
  have hlen : badGroupAdmitted.constructors.length = 1 := rfl
  have : v = 0 := by omega
  subst this
  exact eg010G_badFieldUnivs_view

/-- `fieldAnalyze` permits the malformed field — its stored `.const 0` is a
    legitimately-typed head member. The δ-body closure failure only surfaces
    inside `recIdxAdmittedTB`'s `iotaWitnessStableB`. -/
theorem eg010G_badFieldsPermitted_view : CtorFieldsPermitted badMkView := by
  intro j
  obtain ⟨v, hv⟩ := j
  have hlen : badMkView.fields.length = 1 := rfl
  have : v = 0 := by omega
  subst this
  exact ⟨_, 96, _, rfl⟩

theorem eg010G_badFieldsPermitted (i : Fin badGroupAdmitted.constructors.length) :
    CtorFieldsPermitted (badGroupAdmitted.constructorViews i) := by
  obtain ⟨v, hv⟩ := i
  have hlen : badGroupAdmitted.constructors.length = 1 := rfl
  have : v = 0 := by omega
  subst this
  exact eg010G_badFieldsPermitted_view

/-- the malformed group DOES carry a recursor-class `IndGroupAdmitted` —
    every declarative clause is constructible. The refusal lives in the
    typed checker's recursor/index leaf, not in the admission record. -/
def badAdmittedRec : IndGroupAdmitted badMkEnv 3 badRecMember :=
  .recursor badGroupAdmitted rfl eg010G_badCensus eg010G_badFieldUnivs
    eg010G_badFieldsPermitted badMinorMatch badIotaClause

/-- PIN (negative tooth): the generic content leaf refuses `badAdmittedRec`
    — `pin_recIdxAdmittedTB_badGroup`'s refusal carries through the `&&`
    chain. The declarative admission is constructible; the machine's typed
    leaves still refuse the group. -/
theorem pin_EG010T_badGroup_content_refused :
    memberContentB badMkEnv 96 badAdmittedRec = false := by
  show (famTypedB badMkEnv 96 badGroupAdmitted.family &&
      ctorTypedAllB 96 badGroupAdmitted &&
      recIdxAdmittedTB badGroupAdmitted badIotaClause &&
      finAllB badGroupAdmitted.constructors.length
        (iotaEqB (a := badGroupAdmitted) (h14 := badIotaClause)
          (synCheck (extendEnv badMkEnv 3 badRecMember) badRecMember.arity))) = false
  rw [pin_recIdxAdmittedTB_badGroup]
  simp

-- companion tooth: a sequence whose last member is not `recursorM` is
-- refused by the class leaf outright.
kernel_rfl_theorem pin_EG010T_groupClass_no_recursor :
    groupClassB mN [(1, mZero), (2, mSucc)] mN = false

/-! ### the unsorted member (hT tooth) -/

/-- a member whose stored type is a bare `.const 99` — not sort-typable
    anywhere: `sortTyAtC` cannot produce a `Σ u, HasTyT … (.sort u)` answer
    for it. -/
def badTyMember : CheckedMember := ⟨.axiomM, 0, .const 99 [], none⟩

kernel_rfl_theorem eg010G_badTy_refused :
    (sortTyAtC badMkEnv badTyMember.arity 96 [] badTyMember.mtype).isSome = false

/-- PIN (hT tooth): a member type the checker does not sort-type cannot pay
    a `GroupAcceptChain` cell — `cons` demands the `sortTyAtC` leaf (`none`
    is not `some`) and `nil` demands an empty tail; a `consRec` link is
    refused too: the composite would have to type the member's stored type,
    and `.const 99` names no member of `badMkEnv` (`hasTyT_constsIn`). -/
theorem pin_EG010T_no_chain_when_unsorted :
    ¬ ∃ E', Nonempty (GroupAcceptChain badMkEnv 96 badMkEnv [(2, badTyMember)] E') := by
  rintro ⟨E', ⟨hchain⟩⟩
  cases hchain with
  | cons _ _ _ _ _ _ hsort _ _ =>
      rw [eg010G_badTy_refused] at hsort
      cases hsort
  | consRec _ _ _ _ _ hadm a hcl htel hmin hrec hleaf hrest =>
      obtain ⟨u, hT⟩ := IA021T_recursor_typed a hcl htel hmin
      obtain ⟨m', hm'⟩ := hasTyT_constsIn hT
      have hnone : badMkEnv.members 99 = none := rfl
      rw [hnone] at hm'
      exact Option.noConfusion hm'
  | consRecCheck _ _ _ _ _ hadm a hcl htel hchk hrec hleaf hrest =>
      obtain ⟨u, hT⟩ := IA021T_recursor_typed a hcl htel (IA021T_minorDomains_of_check a _ hchk)
      obtain ⟨m', hm'⟩ := hasTyT_constsIn hT
      have hnone : badMkEnv.members 99 = none := rfl
      rw [hnone] at hm'
      exact Option.noConfusion hm'

end Rcic.Scm.SrcG

#print axioms Rcic.Declarative.DT018_inductive_extension_preserves_of_memberStructB
#print axioms Rcic.Declarative.pin_DT018_pinFamEnv_of_memberStructB
#print axioms Rcic.Declarative.pin_DT018_adm_necessary
