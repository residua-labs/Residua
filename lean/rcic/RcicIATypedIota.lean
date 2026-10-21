import rcic.RcicDTMetaTyped
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec
import rcic.ScmSrcGroupsEnvWfT

/-!
# IA-023 on the typed root: every ι right-hand side is well typed (tymig segment C)

05 §14: "Every iota right-hand side is independently type-checked against the left-hand side type
before the descriptor becomes part of the checked group." GM-IND-005
(`docs/rcic/GLOBAL_MUTANT_REGISTRY.md:58`): "Derived iota RHS is registered without type checking."

**What this module is: an environment-level EXTRACTION.** Since R-NoFunRec-1 step 0 the typed
environment judgment carries the typing as its own field: a recursor cell of `EnvWfT.group` holds
`IndGroupTypedT`, whose recursor part is `∀ i, IotaEquationTypedT …` (`RcicTypedEnv`). So
`IA023T_every_iota_rhs_typed` does not prove that ι right-hand sides are typable. It extracts, for
every recursor member of every `EnvWfT` environment, what admission established. That is: the
admission cell (`envWfT_recursorCell`, a walk through `EnvWfT` and `GroupMembersT`), the
right-hand side computed by `iotaSchemaAt` at the cell's own descriptor, and its `HasTyT` typing at
the equation's type, moved from the derivation scope into the environment itself (`hasTyTExt`). It
follows the `envWfT_bodyTyped` pattern. C2 alone is NOT the evidence for IA-023.

The walk exists once, BUNDLED (`RecursorCellMinorsT`): the same traversal returns the cell and the
`MinorPremisesMatch` clause IA-023 drops; IA-025 (`RcicIATypedGroupDerived`) consumes the bundle.
The bare-cell names below are one-line projections of the bundled walk.

**The substantive evidence is C4, that admission really checks.** At a real fixture the typed
checker that discharges the field (`synCheck`, through `iotaEquationTypedT_of_check`) ACCEPTS the
derived right-hand side and REFUSES three decoys. The decoys are the GM-IND-005 shapes a descriptor
would register unchecked: the wrong minor, the recursive call on the wrong field, and the missing
induction hypothesis. Each refusal is `= none`, by evaluation (`tooth_GM_IND_005_*`). C3 adds the
second instrument: the right-hand sides themselves, computed by evaluation (`pin_IA023T_listSchema`).

Pins (C3): the row consumed at `listEnvUT`'s recursor (List, ref 11: the cons RHS carries a
recursive call) and at `srcEnvG`'s K3c recursor `recValueAt` (slot 143, nine minors), through the
unconditional `envWfT_srcEnvG`. Its nine equations were discharged in-tree by the same checker run
(`iotaAllB143`, `ScmSrcGroupsEnvWfT15`).

The legacy `iotaTyping_of_admitted` (`RcicAdmit.lean`) is untouched. `closure_claim` 0; axioms within
{propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-! ## (1) the recursor cell -/

/-- a recursor member's admission cell: the environment built so far, the recursor's elimination
    admission at it, its ι descriptor clause, the typed ι equations (the `IndGroupTypedT` field), and
    the fact that the derivation scope `extendEnv E0 r m` is part of `E`. -/
structure RecursorCellT (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Type where
  E0 : ResolvedEnv
  adm : RecursorEliminationAdmitted E0 r m
  clause : IotaDescriptorClause E0 adm
  typed : ∀ i, IotaEquationTypedT adm i (clause.fuelAt i) (clause.shapesAt i)
  sub : ∀ r' m', (extendEnv E0 r m).members r' = some m' → E.members r' = some m'
  /-- the recursor reference was fresh in the derivation prefix
      (admission's own `hfresh`), so `E0 ⊆ E`. -/
  fresh : E0.members r = none

/-- a cell survives every member-preserving extension. -/
def RecursorCellT.lift {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hsub : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    (c : RecursorCellT E r m) : RecursorCellT E' r m :=
  ⟨c.E0, c.adm, c.clause, c.typed, fun r' m' h => hsub r' m' (c.sub r' m' h), c.fresh⟩

/-- the admission cell together with the minor-premises clause its `.recursor` admission
    carries. IA-023's extraction drops `MinorPremisesMatch` (it types ι right-hand sides, not
    minors); IA-025's "the group contains the exact derived objects" consumes it. One walk
    produces the bundle — the bare cell is its projection — so IA-023 and IA-025 share ONE
    traversal of `EnvWfT`/`GroupMembersT` instead of two copies of the same walk. -/
structure RecursorCellMinorsT (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Type where
  cell : RecursorCellT E r m
  minors : MinorPremisesMatch cell.adm

/-- the bundled cell survives every member-preserving extension; the admission — and with it
    the minors clause — does not move. -/
def RecursorCellMinorsT.lift {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hsub : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    (b : RecursorCellMinorsT E r m) : RecursorCellMinorsT E' r m :=
  ⟨b.cell.lift hsub, b.minors⟩

/-- an `IndGroupAdmitted` cell of a `recursorM` member is the `.recursor` cell WITH the
    minors clause kept (the family and constructor views carry their own class,
    `hasClass`). -/
def recursorCellMinors_of_admitted {E E'' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hcls : m.mclass = .recursorM)
    (hsub : ∀ r' m', (extendEnv E r m).members r' = some m' → E''.members r' = some m') :
    (hadm : IndGroupAdmitted E r m) → IndGroupTypedT hadm → RecursorCellMinorsT E'' r m
  | .family _ view _ hm _, _ =>
      absurd (show m.mclass = .inductiveM from hm ▸ view.hasClass)
        (fun h => by rw [hcls] at h; cases h)
  | .constructor _ view _ _ _ _ _, _ =>
      absurd view.hasClass (fun h => by rw [hcls] at h; cases h)
  | .recursor a hfresh _ _ _ h12 h14, ht =>
      ⟨⟨E, a, h14, ht.2.2, hsub, hfresh⟩, h12⟩

/-- an `IndGroupAdmitted` cell of a `recursorM` member is the `.recursor` cell: the family and
    constructor views carry their own class (`hasClass`). One-line corollary of the bundled
    `recursorCellMinors_of_admitted`. -/
def recursorCell_of_admitted {E E'' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hcls : m.mclass = .recursorM)
    (hsub : ∀ r' m', (extendEnv E r m).members r' = some m' → E''.members r' = some m') :
    (hadm : IndGroupAdmitted E r m) → IndGroupTypedT hadm → RecursorCellT E'' r m :=
  fun hadm ht => (recursorCellMinors_of_admitted hcls hsub hadm ht).cell

/-- the group walk, bundled: a `recursorM` member a `GroupMembersT` chain adds has its cell
    and its minors clause. -/
def groupMembersT_recursorCellMinors {S : ResolvedEnv} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → {r : Nat} → {m : CheckedMember} →
    E'.members r = some m → E.members r = none → m.mclass = .recursorM →
    RecursorCellMinorsT E' r m
  | _, _, _, .nil _, _, _, hm, hnone, _ => absurd (hnone ▸ hm) (by simp)
  | _, _, _, .cons E r₀ m₀ _ E' _ _ _ _ _ _ _ hadm _ _ _ _ htyped hrest, r, m, hm, hnone,
      hcls => by
      by_cases hr : r = r₀
      · subst hr
        have hm0 : E'.members r = some m₀ :=
          groupMembersT_mono hrest r m₀ (by simp [extendEnv])
        have heq : m₀ = m := Option.some.inj (hm0.symm.trans hm)
        subst heq
        exact recursorCellMinors_of_admitted hcls (groupMembersT_mono hrest) hadm htyped
      · exact groupMembersT_recursorCellMinors hrest hm
          (by simp only [extendEnv, if_neg hr]; exact hnone) hcls

/-- the group walk: a `recursorM` member a `GroupMembersT` chain adds has its cell.
    One-line corollary of the bundled `groupMembersT_recursorCellMinors`. -/
def groupMembersT_recursorCell {S E : ResolvedEnv} {l : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (hchain : GroupMembersT S E l E') {r : Nat} {m : CheckedMember}
    (hm : E'.members r = some m) (hnone : E.members r = none)
    (hcls : m.mclass = .recursorM) : RecursorCellT E' r m :=
  (groupMembersT_recursorCellMinors hchain hm hnone hcls).cell

/-- C1 bundled: every `recursorM` member of an `EnvWfT` environment has its admission cell
    and its minors clause. -/
def envWfT_recursorCellMinors : {E : ResolvedEnv} → EnvWfT E → {r : Nat} → {m : CheckedMember} →
    E.members r = some m → m.mclass = .recursorM → RecursorCellMinorsT E r m
  | _, .empty, _, _, hm, _ => absurd hm (by simp [emptyEnv])
  | _, .axiom E r₀ _ _ hE hfresh _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_recursorCellMinors hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .definition E r₀ _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_recursorCellMinors hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .thm E r₀ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_recursorCellMinors hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .opaque E r₀ _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_recursorCellMinors hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .group E _ _ _ _ _ _ hE _ _ _ hmem, r, m, hm, hcls => by
      cases hb : E.members r with
      | some m' =>
          have h' := groupMembersT_mono hmem r m' hb
          have heq : m' = m := Option.some.inj (h'.symm.trans hm)
          subst heq
          exact (envWfT_recursorCellMinors hE hb hcls).lift (groupMembersT_mono hmem)
      | none => exact groupMembersT_recursorCellMinors hmem hm hb hcls

/-- C1: every `recursorM` member of an `EnvWfT` environment has its admission cell.
    One-line corollary of the bundled `envWfT_recursorCellMinors`. -/
def envWfT_recursorCell {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hcls : m.mclass = .recursorM) : RecursorCellT E r m :=
  (envWfT_recursorCellMinors hW hm hcls).cell

/-! ## (2) the extraction -/

/-- every ι equation of a cell: its domains and its right-hand side are computed, and the
    right-hand side is `HasTyT` in the environment itself at the equation's type. -/
theorem RecursorCellT.iota_rhs_typed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellT E r m) (i : Fin c.adm.constructors.length) :
    ∃ doms rhs, equationDoms c.adm i = some doms ∧
      iotaSchemaAt c.adm i (c.clause.fuelAt i) (c.clause.shapesAt i) = some rhs ∧
      Nonempty (HasTyT E m.arity (assumptionCtx doms) rhs (iotaEquationType c.adm i)) := by
  have h := c.typed i
  unfold IotaEquationTypedT at h
  revert h
  cases hd : equationDoms c.adm i with
  | none => intro h; exact False.elim h
  | some doms =>
      cases hs : iotaSchemaAt c.adm i (c.clause.fuelAt i) (c.clause.shapesAt i) with
      | none => intro h; exact False.elim h
      | some rhs =>
          intro h
          obtain ⟨t⟩ := h
          exact ⟨doms, rhs, rfl, rfl, ⟨hasTyTExt c.sub t⟩⟩

/-- the row's shape at one recursor member: there is an admission cell whose every ι right-hand side
    is computed and `HasTyT` in `E` at the equation's type. -/
def IotaRhsTypedAt (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Prop :=
  ∃ (E0 : ResolvedEnv) (a : RecursorEliminationAdmitted E0 r m) (h14 : IotaDescriptorClause E0 a),
    ∀ i, ∃ doms rhs, equationDoms a i = some doms ∧
      iotaSchemaAt a i (h14.fuelAt i) (h14.shapesAt i) = some rhs ∧
      Nonempty (HasTyT E m.arity (assumptionCtx doms) rhs (iotaEquationType a i))

/-- IA-023 typed, AS AN EXTRACTION: every recursor member of an `EnvWfT` environment has an
    admission cell whose every ι right-hand side is `HasTyT` in the environment at the equation's
    type. The typing is `EnvWfT`'s own field (R-NoFunRec-1 step 0). This theorem extracts what
    admission established; the evidence that admission CHECKS it is C4
    (`tooth_GM_IND_005_listDecoys`), not this statement. -/
theorem IA023T_every_iota_rhs_typed {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM) :
    IotaRhsTypedAt E r m :=
  let c := envWfT_recursorCell hW hm hcls
  ⟨c.E0, c.adm, c.clause, c.iota_rhs_typed⟩

/-! ## (3) C3: pins at real fixtures, and the right-hand sides by evaluation -/

/-- PIN (IA-023T): List's recursor (ref 11) in the two-group environment `listEnvUT`. -/
theorem pin_IA023T_listU : IotaRhsTypedAt listEnvUT 11 listURecMember :=
  IA023T_every_iota_rhs_typed listEnvUWfT rfl rfl

/-- List's cons right-hand side, as `iotaSchemaAt` derives it in the equation's context
    `[xs, x, mc, mn, M, A]`: the cons minor applied to the fields, then the recursive call on `xs`. -/
def listConsRhsU : Expr Nat :=
  .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.app (.app (.const 11 [.param 0, .param 1]) (.bvar 5)) (.bvar 4))
      (.bvar 3)) (.bvar 2)) (.bvar 0))

/-- SECOND INSTRUMENT (C3): the two right-hand sides of List's descriptor, by evaluation — the nil
    minor, and the cons minor with its recursive call. -/
theorem pin_IA023T_listSchema :
    iotaSchemaAt listGroupU ⟨0, by decide⟩ (listIotaClauseU.fuelAt ⟨0, by decide⟩)
      (listIotaClauseU.shapesAt ⟨0, by decide⟩) = some (.bvar 1) ∧
    iotaSchemaAt listGroupU ⟨1, by decide⟩ (listIotaClauseU.fuelAt ⟨1, by decide⟩)
      (listIotaClauseU.shapesAt ⟨1, by decide⟩) = some listConsRhsU := by
  constructor <;> decide

/-! ## (4) C4: the checker accepts the derived right-hand side and refuses the GM-IND-005 decoys -/

/-- the cons equation's context, as `equationDoms` derives it. -/
def listConsDomsU : List (Expr Nat) := (equationDoms listGroupU ⟨1, by decide⟩).getD []

/-- the cons equation's type, `M (cons A x xs)`. -/
def listConsEqTyU : Expr Nat := iotaEquationType listGroupU ⟨1, by decide⟩

/-- DECOY (wrong minor): the NIL minor where the cons minor belongs. -/
def listDecoyMinorU : Expr Nat :=
  .app (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.app (.app (.const 11 [.param 0, .param 1]) (.bvar 5)) (.bvar 4))
      (.bvar 3)) (.bvar 2)) (.bvar 0))

/-- DECOY (wrong recursive field): the recursive call on the head `x` instead of the tail `xs`. -/
def listDecoyRecArgU : Expr Nat :=
  .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.app (.app (.const 11 [.param 0, .param 1]) (.bvar 5)) (.bvar 4))
      (.bvar 3)) (.bvar 2)) (.bvar 1))

/-- DECOY (missing induction hypothesis): the cons minor applied to the fields only. -/
def listDecoyNoIHU : Expr Nat := .app (.app (.bvar 2) (.bvar 1)) (.bvar 0)

/-- C4, the accepting half: the checker that discharges the cons equation (`synCheck`, the same call
    `listRecTypedU` hands `iotaEquationTypedT_of_check`) accepts the derived right-hand side. -/
theorem pin_IA023T_listChecked :
    (synCheck listEnvUT 2 (assumptionCtx listConsDomsU) listConsRhsU listConsEqTyU).isSome = true :=
  rfl

/-- TOOTH (GM-IND-005, C4): the same checker, on the same equation, REFUSES each decoy, by
    evaluation. A decoy right-hand side therefore cannot be discharged into a recursor cell through
    the checker route `iotaEquationTypedT_of_check`: admission checks the right-hand side; it does not
    merely register it. -/
theorem tooth_GM_IND_005_listDecoys :
    synCheck listEnvUT 2 (assumptionCtx listConsDomsU) listDecoyMinorU listConsEqTyU = none ∧
    synCheck listEnvUT 2 (assumptionCtx listConsDomsU) listDecoyRecArgU listConsEqTyU = none ∧
    synCheck listEnvUT 2 (assumptionCtx listConsDomsU) listDecoyNoIHU listConsEqTyU = none :=
  ⟨rfl, rfl, rfl⟩

end Rcic.Declarative

namespace Rcic.Scm.SrcG

open Rcic.Declarative

-- slot 143 of `srcEnvG` is the K3c recursor `recValueAt` (kernel-checked lookup).
kernel_rfl_theorem srcEnvG_slot143 : srcEnvG.members 143 = some recValueAt

/-- PIN (IA-023T): `srcEnvG`'s nine-minor recursor `recValueAt` (slot 143), through the unconditional
    `envWfT_srcEnvG`. In-tree, the same checker run discharged its nine equations (`iotaAllB143`). -/
theorem pin_IA023T_srcVA : IotaRhsTypedAt srcEnvG 143 recValueAt :=
  IA023T_every_iota_rhs_typed envWfT_srcEnvG srcEnvG_slot143 rfl

end Rcic.Scm.SrcG

#print axioms Rcic.Declarative.RecursorCellT.lift
#print axioms Rcic.Declarative.RecursorCellMinorsT.lift
#print axioms Rcic.Declarative.recursorCellMinors_of_admitted
#print axioms Rcic.Declarative.recursorCell_of_admitted
#print axioms Rcic.Declarative.groupMembersT_recursorCellMinors
#print axioms Rcic.Declarative.groupMembersT_recursorCell
#print axioms Rcic.Declarative.envWfT_recursorCellMinors
#print axioms Rcic.Declarative.envWfT_recursorCell
#print axioms Rcic.Declarative.RecursorCellT.iota_rhs_typed
#print axioms Rcic.Declarative.IA023T_every_iota_rhs_typed
#print axioms Rcic.Declarative.pin_IA023T_listU
#print axioms Rcic.Declarative.pin_IA023T_listSchema
#print axioms Rcic.Declarative.pin_IA023T_listChecked
#print axioms Rcic.Declarative.tooth_GM_IND_005_listDecoys
#print axioms Rcic.Scm.SrcG.srcEnvG_slot143
#print axioms Rcic.Scm.SrcG.pin_IA023T_srcVA
