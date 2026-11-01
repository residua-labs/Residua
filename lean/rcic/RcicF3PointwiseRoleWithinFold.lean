import rcic.RcicF3PointwiseRoleWithin
import rcic.RcicF3PointwiseCheckedApex

/-!
# Admission folding at one admitted completion

`LocalGroupsWithin` stores obligations only at the group occurrences of
one actual admission derivation. Its local output is family membership,
constructor membership, and the existing `RecPkgAt` at the fixed admitted
completion. The fold produces all earlier iota cases by actual inclusion
and role/plan transport, and produces ordinary declarations from their
bounded stored bodies. Coverage and both original bound predicates remain
literal inputs.

The generic fold is not an unchecked or indexed group producer. A separate
available instance below uses the already produced W/D-checked pointwise
theorem, on exactly its old bounds. It does not infer that those checks
always pass, or migrate any root to a new premise. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRole.WithinFold
open Rcic.Declarative Rcic.Model.PS
open Rcic.Declarative.Ann (EnvSub)
open Rcic.F3.StepWCheck (EnvWChecked)

/-- The local semantic production still owed at one actual group. Its
conclusion is the existing member contracts and fixed `RecPkgAt`, rather
than the whole invariant. The predecessor may be used only at the same
admitted completion. -/
def LocalGroupWithin (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm, NodeCovered hmem node) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  GInvWithin P K F hFinal hE → EnvSub E' F →
  ∀ α : Arities, AritiesAgree α E' →
  ∀ ctx : Nat → Role, (∀ r, Dom E' r → ctx r = NormRole.envCtx
    (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
  ∀ plans : EvalRole.Plans, (∀ r, Dom E' r → plans r = EvalRole.envPlan
    (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
  ∀ μ, EvalRole.Faithful (familyValue α) P μ ctx plans E' →
    let node := (EvalPlan.ofGroup hE hfam hctors hrec hmem).node
    MemberSound P μ K f fm ∧
      (∀ j : Fin node.a.constructors.length,
        MemberSound P μ K (f + 1 + j.val) node.a.constructors[j.val]) ∧
      RecPkgAt P μ K F E' rr rm

/-- A finite supply indexed by the actual admission derivation. No
universal quantifier over unrelated group declarations is introduced. -/
def LocalGroupsWithin (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F) :
    {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => LocalGroupsWithin P K F hFinal hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ =>
      LocalGroupsWithin P K F hFinal hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => LocalGroupsWithin P K F hFinal hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => LocalGroupsWithin P K F hFinal hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem =>
      LocalGroupsWithin P K F hFinal hE ∧
        LocalGroupWithin P K F hFinal hE hfam hctors hrec hmem

/-- Actual admission induction. The singleton cases are proved from their
stored bodies; a group is assembled by the exhaustive admitted member
classification and its supplied local `RecPkgAt`. -/
theorem gInvWithin_of_localGroups (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Covered hW →
      BoundG K hW → BoundDG K hW → LocalGroupsWithin P K F hFinal hW →
        GInvWithin P K F hFinal hW
  | _, .empty, _, _, _, _ => gInvWithin_empty P K F hFinal
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _, _ => hC.elim
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv,
      hC, hB, hD, hLocal =>
      gInvWithin_singleW P K F hFinal (Or.inl rfl)
        hfresh hclA hclv hlvlA hlvlv hv hB.2
        (gInvWithin_of_localGroups P K F hFinal hE hC hB.1 hD hLocal)
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp,
      hC, hB, hD, hLocal =>
      gInvWithin_singleW P K F hFinal (Or.inr (Or.inl rfl))
        hfresh hclA hclp hlvlA hlvlp hp hB.2
        (gInvWithin_of_localGroups P K F hFinal hE hC hB.1 hD hLocal)
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv,
      hC, hB, hD, hLocal =>
      gInvWithin_singleW P K F hFinal (Or.inr (Or.inr rfl))
        hfresh hclA hclv hlvlA hlvlv hv hB.2
        (gInvWithin_of_localGroups P K F hFinal hE hC hB.1 hD hLocal)
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem,
      hC, hB, hD, hLocal => by
      have IH := gInvWithin_of_localGroups P K F hFinal hE
        hC.1 hB.1 hD.1 hLocal.1
      intro hsub α hα ctx hctx plans hplans μ hFaith
      have hPrior := gInvWithin_group_prefix P K F hFinal hE hfam hctors hrec hmem
        IH hsub α hα ctx hctx plans hplans μ hFaith
      have hHere := hLocal.2 hC.2 hB hD IH hsub α hα ctx hctx plans hplans μ hFaith
      exact allSound_iota_groupWithin P K F hFinal hE hfam hctors hrec hmem
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node hsub μ hPrior
        hHere.1 hHere.2.1 hHere.2.2

/-- The final consumer composes with the finite local supply. This is a
conditional assembly theorem, not production of its group certificates. -/
theorem false_of_localGroups (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hC : Covered hW)
    (hB : BoundG K hW) (hD : BoundDG K hW)
    (hLocal : LocalGroupsWithin P K E hW hW)
    (h1 : E.members 1 = some falseRecMemberU) (n : Nat)
    (e : Expr Nat) (D : HasTyT E n [] e (.const 0 []))
    (hl : LOKt (fun _ => 0) 4 K D) : False :=
  false_of_gInvWithin P K hW
    (gInvWithin_of_localGroups P K E hW hW hC hB hD hLocal) h1 n e D hl

/-! The following is the available CHECKED instance. It uses the
already-produced checked invariant, and claims no extension of that
theorem's domain to unchecked or indexed bounds. -/

/-- Extract exactly the local package from an existing old invariant at
this actual group, with no attempt to strengthen a weak predecessor. -/
theorem localGroupWithin_of_gInv (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hOld : GInv P K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem)) :
    LocalGroupWithin P K F hFinal hE hfam hctors hrec hmem := by
  intro _hCov _hBound _hBoundD _hPred _hsub α hα ctx hctx plans hplans μ hFaith
  have h := hOld α hα ctx hctx plans hplans μ hFaith
  let node := (EvalPlan.ofGroup hE hfam hctors hrec hmem).node
  have hfm : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  exact ⟨h.1 f fm hfm, fun j => h.1 _ _ (node_ctor_member node j),
    fun hsub => ⟨h.1 rr rm hrm, h.2 F hsub rr rm hrm hrec⟩⟩

/-- The existing checked producer, read at its inductive predicates. -/
theorem gInv_of_coveredWDChecked (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hC : Covered hW)
    (hWc : EnvWChecked hW) (hDc : Rcic.F3.StepWDApex.EnvDChecked K hW)
    (hB : BoundG K hW) (hD : BoundDG K hW) : GInv P K hW :=
  gInv_of_steps P K _ _
    (PointwiseADataChecked.steps_coveredWDChecked P K
      (PointwiseLocalProducer.stepADataChecked P K))
    (fun {_} _ _ _ _ _ _ _ _ _ hCx => hCx.1)
    hW ⟨hC, hWc, hDc⟩ ⟨hB, hD⟩

/-- Actual finite certificates on the existing checked domain. Each
group uses its already-produced checked result; the new generic fold
does not receive a universal group theorem as a new root premise. -/
theorem localGroupsWithin_of_checked (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Covered hW → EnvWChecked hW →
      Rcic.F3.StepWDApex.EnvDChecked K hW → BoundG K hW → BoundDG K hW →
        LocalGroupsWithin P K F hFinal hW
  | _, .empty, _, _, _, _, _ => True.intro
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _, _, _ => hC.elim
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hWc, hDc, hB, hD =>
      localGroupsWithin_of_checked P K F hFinal hE hC hWc hDc hB.1 hD
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC, hWc, hDc, hB, hD =>
      localGroupsWithin_of_checked P K F hFinal hE hC hWc hDc hB.1 hD
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hWc, hDc, hB, hD =>
      localGroupsWithin_of_checked P K F hFinal hE hC hWc hDc hB.1 hD
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem,
      hC, hWc, hDc, hB, hD =>
      ⟨localGroupsWithin_of_checked P K F hFinal hE hC.1 hWc.1 hDc.1 hB.1 hD.1,
        localGroupWithin_of_gInv P K F hFinal hE hfam hctors hrec hmem
          (gInv_of_coveredWDChecked P K
            (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)
            hC hWc hDc hB hD)⟩

/-- The actual new fold instantiated on the unchanged checked tier. -/
theorem gInvWithin_of_checks (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    GInvWithin P K F hFinal hW := by
  have hC := EnvWfT_axiomFree_covered P hW hAx
  have hWc := Rcic.F3.StepWApex.envCheck_sound hW pw
  have hDc := Rcic.F3.StepWDApex.envCheck_sound K hW pd
  exact gInvWithin_of_localGroups P K F hFinal hW hC hB hD
    (localGroupsWithin_of_checked P K F hFinal hW hC hWc hDc hB hD)

end Rcic.F3.PSet.PointwiseRole.WithinFold

#print axioms Rcic.F3.PSet.PointwiseRole.WithinFold.gInvWithin_of_localGroups
#print axioms Rcic.F3.PSet.PointwiseRole.WithinFold.false_of_localGroups
#print axioms Rcic.F3.PSet.PointwiseRole.WithinFold.localGroupsWithin_of_checked
#print axioms Rcic.F3.PSet.PointwiseRole.WithinFold.gInvWithin_of_checks
