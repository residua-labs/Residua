import rcic.RcicF3StepWCheck
import rcic.RcicF3StepWObstr
import rcic.RcicRk01SortValley
import rcic.RcicElimPolicy
import rcic.RcicRecursorCellHT

/-!
# StepW open-arm witnesses and the exact global checked face

`OpenArm` retains every premise of `StepWHyp`, including the admitted prefix,
group and recursor node. `eqWOpenArm` inhabits this local input type and its
conclusion is true. This is LOCAL non-vacuity, not a proof of the globally
quantified `StepWHyp` or of its consistency. The global truth question remains
open here. The checked global face is equivalent to that same open question.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWOpen

open Rcic.Declarative Rcic.F3.PSet Rcic.F3.StepWMin Rcic.F3.StepWCheck
open Rcic.Syn.FamApp.StepW

/-- A single input to the literal open arm; no environment policy is added. -/
structure OpenArm where
  E : ResolvedEnv
  E' : ResolvedEnv
  f : Nat
  rr : Nat
  fm : CheckedMember
  rm : CheckedMember
  ctors : List (Nat × CheckedMember)
  hE : EnvWfT E
  hfam : fm.mclass = .inductiveM
  hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM
  hrec : rm.mclass = .recursorM
  hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'
  node : RecNode E E' f rr rm
  pend : PendW hmem node
  uniform : UniformType node.a.family.resultLevel
  outside : ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope

/-- The semantic conclusion at a single open-arm input. -/
def OpenArm.Agrees (w : OpenArm) : Prop :=
  WalkAgree (AgreeAt w.node.a.family.parameters.length) w.hmem

/-- The finite checked conclusion at the same input. -/
def OpenArm.Checked (w : OpenArm) : Prop :=
  WalkAgree (AgreeAtDec w.node.a.family.parameters.length) w.hmem

/-- The existing Eq-prefix fixture meets ALL open-arm premises. -/
def eqWOpenArm : OpenArm where
  E := eqEnvT
  E' := eqWEnv
  f := 66
  rr := 68
  fm := eqWV
  rm := eqWRec
  ctors := [(67, eqWMk)]
  hE := eqPrefixWfT
  hfam := rfl
  hctors := fun c hc => by
    simp only [List.mem_singleton] at hc
    subst hc
    rfl
  hrec := rfl
  hmem := eqWMembersT
  node := eqWNode
  pend := eqW_not_walkClass
  uniform := eqW_uniformType
  outside := eqW_not_inScope

/-- Local non-vacuity: the input conjunction does not imply False. -/
theorem openArm_nonempty : Nonempty OpenArm := ⟨eqWOpenArm⟩

/-- The inhabited input also has a true conclusion, without Premises4. -/
theorem eqWOpenArm_agrees : eqWOpenArm.Agrees := eqW_stepW

/-- A refutation at the Eq-prefix fixture is impossible. -/
theorem eqWOpenArm_not_refutation : ¬ (¬ eqWOpenArm.Agrees) :=
  fun h => h eqWOpenArm_agrees

/-- The missing direction of the global equivalence, using check soundness. -/
theorem hyp_of_stepWChecked (h : StepWChecked) : StepWHyp := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem node hPend hT hIS
  exact walkAgree_congr (fun _ _ _ _ => agreeAt_of_agreeAtDec) hmem
    (h hE hfam hctors hrec hmem node hPend hT hIS)

/-- A global check is exactly the conjecture; it does not discharge it. -/
theorem stepWChecked_iff_hyp : StepWChecked ↔ StepWHyp :=
  ⟨hyp_of_stepWChecked, stepWChecked_of_hyp⟩

/-- Packaging the local inputs neither weakens nor strengthens the conjecture. -/
theorem hyp_iff_all_openArm : StepWHyp ↔ ∀ w : OpenArm, w.Agrees := by
  constructor
  · intro h w
    exact h w.hE w.hfam w.hctors w.hrec w.hmem w.node w.pend w.uniform w.outside
  · intro h E E' f rr fm rm ctors hE hfam hctors hrec hmem node hPend hT hIS
    exact h ⟨E, E', f, rr, fm, rm, ctors, hE, hfam, hctors, hrec, hmem,
      node, hPend, hT, hIS⟩

/-- Under the tier's own decidability premise, global double-negation
non-vacuity already entails the full W conjecture. A local example cannot
satisfy this stronger requirement. -/
theorem global_nonvacuity_iff (P : Premises4) :
    (¬ (StepWHyp → False)) ↔ StepWHyp := by
  constructor
  · intro hn
    cases P.dec StepWHyp with
    | isTrue h => exact h
    | isFalse h => exact (hn h).elim
  · intro h hn
    exact hn h

/-- An actual admitted open-arm counterexample, rather than a failed supplier. -/
def Counterexample : Prop := ∃ w : OpenArm, ¬ w.Agrees

/-- A concrete counterexample suffices to refute the literal global conjecture. -/
theorem counterexample_refutes_hyp (h : Counterexample) : ¬ StepWHyp := by
  obtain ⟨w, hbad⟩ := h
  intro hW
  exact hbad (hW w.hE w.hfam w.hctors w.hrec w.hmem w.node w.pend w.uniform w.outside)

/-- The older excursion predicate includes ordinary same-sort beta steps.
Its universal absence cannot supply the open W arm. -/
theorem diagonal_sortExcursion (E : ResolvedEnv) (n : Nat) (u : Level) :
    Nonempty (Rk01SortValley.SortExcursion E n u u) := by
  let X : Expr Nat := .app (.lam (.sort (.succ u)) (.bvar 0)) (.sort u)
  let c : ConvT E n [] X (.sort u) (.sort (.succ u)) :=
    .beta [] (.sort (.succ u)) (.bvar 0) (.sort u) (.sort (.succ u))
      (.succ (.succ u)) (.sort [] (.succ u))
      (.bvar [.assumption (.sort (.succ u))] 0 (.sort (.succ u)) rfl)
      (.sort [] u)
  exact ⟨⟨[], X, X, .sort (.succ u), .sort (.succ u),
    (fun _ h => Expr.noConfusion h), (fun _ h => Expr.noConfusion h),
    ⟨c, trivial⟩, ⟨c, trivial⟩, ⟨Rk01SortValley.PrimSeq.refl [] X⟩⟩⟩

/-- Refutation of an auxiliary route, not of StepWHyp or sort uniqueness. -/
theorem noExcursion_refuted (E : ResolvedEnv) (n : Nat) :
    ¬ (∀ u v : Level, ¬ Nonempty (Rk01SortValley.SortExcursion E n u v)) :=
  fun h => h .zero .zero (diagonal_sortExcursion E n .zero)

/-- Constructor admission occurs before the current recursor: its member
lookup embeds into the recursor node's pre-installation environment. -/
theorem ctorEnvironment_before_rec {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    {Ew : ResolvedEnv} {r : Nat} {m : CheckedMember} (famO : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew famO m) (h04 : CtorBeforeRecursors Ew m)
    (hin : (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)])
    (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m') :
    ∀ r' m', Ew.members r' = some m' → node.E0.members r' = some m' := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  obtain ⟨i, _, hm, _, _, _⟩ :=
    walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO cv hin hEw
  have hmf := memberFamRef_ctorView cv
  have hmr := memberFamRef_ctorView (node.a.constructorViews i)
  rw [hm] at hmf
  have hf : famO.ref = node.a.family.ref := Option.some.inj (hmf.symm.trans hmr)
  have hno : Ew.members rr ≠ some rm := by
    intro hr
    exact CtorBeforeRecursors.no_existing h04 (memberFamRef_ctorView cv) hr hrec
      (by rw [hf]; exact memberFamRef_recAdm node.a hrec)
  obtain ⟨_, _, hfm, _, _⟩ := group_refs hmem hL hrr
  have hfmm : fm = node.a.family.member :=
    Option.some.inj (hfm.symm.trans (node_fam_member node))
  intro r' m' hm'
  rcases group_member_cases hmem hL hrr node (hEw r' m' hm') with
    hb | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · exact node.base r' m' hb
  · have hh := node.a.family.present
    rw [node.fam] at hh
    simpa only [hfmm] using hh
  · exact (hno hm').elim
  · have hj := node.a.constructorsPresent j
    rw [node.fam] at hj
    exact hj

/-- Both sortings of a gap entry and its well-formed context already live
before the current recursor is installed. Earlier recursors remain possible. -/
theorem walk_entry_double_typed_before_rec {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    {Ew : ResolvedEnv} {r : Nat} {m : CheckedMember} (famO : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew famO m) (htyped : CtorTypedT cv)
    (h04 : CtorBeforeRecursors Ew m)
    (hin : (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)])
    (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m')
    (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length)
    (hge : node.a.family.parameters.length ≤ k) :
    Nonempty (CtxWfT node.E0 famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k)) ∧
    Nonempty (HasTyT node.E0 famO.member.arity
      (policyPrefixContext (cv.parameters ++ cv.fields) k)
      ((cv.parameters ++ cv.fields)[k]'hk)
      (.sort (cv.domainsTyped.levels ⟨k, hk⟩))) ∧
    ∃ uR : Level,
      Nonempty (HasTyT node.E0 famO.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) k)
        ((cv.parameters ++ cv.fields)[k]'hk)
        (.sort uR)) ∧
      (UniformProp famO.resultLevel ∨ leN uR famO.resultLevel) := by
  obtain ⟨i, _, _, hcat, hlvO, harO⟩ :=
    walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO cv hin hEw
  have hpre := ctorEnvironment_before_rec hE hfam hctors hrec hmem hWR node famO cv h04 hin hEw
  have htelPre : TelTypedT node.E0 famO.member.arity (cv.parameters ++ cv.fields) cv.domainsTyped.levels :=
    fun idx => let ⟨d⟩ := htyped.1 idx; ⟨hasTyTExt hpre d⟩
  have hΓ : Nonempty (CtxWfT node.E0 famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k)) :=
    ctxWfT_of_telTypedT htelPre k (Nat.le_of_lt hk)
  have hdO : Nonempty (HasTyT node.E0 famO.member.arity
      (policyPrefixContext (cv.parameters ++ cv.fields) k)
      ((cv.parameters ++ cv.fields)[k]'hk)
      (.sort (cv.domainsTyped.levels ⟨k, hk⟩))) := htelPre ⟨k, hk⟩
  let cvR := node.a.constructorViews i
  have hlenN : cvR.parameters.length = node.a.family.parameters.length := cvR.parameterCount
  have hkR : k < (cvR.parameters ++ cvR.fields).length := hcat ▸ hk
  have hjlt : k - cvR.parameters.length < cvR.fields.length := by
    simp only [List.length_append] at hkR; omega
  let jR : Fin cvR.fields.length := ⟨k - cvR.parameters.length, hjlt⟩
  have hfi : (⟨k, hkR⟩ : Fin (cvR.parameters ++ cvR.fields).length) = cvR.fieldIndex jR :=
    Fin.ext (by
      show k = cvR.parameters.length + (k - cvR.parameters.length)
      omega)
  obtain ⟨⟨dR0⟩, hbdR⟩ := recView_field_bound node i jR
  have hdR : Nonempty (HasTyT node.E0 famO.member.arity
      (policyPrefixContext (cv.parameters ++ cv.fields) k)
      ((cv.parameters ++ cv.fields)[k]'hk)
      (.sort (cvR.domainsTyped.levels (cvR.fieldIndex jR)))) := by
    have hval : (cvR.fieldIndex jR).val = k := congrArg Fin.val hfi.symm
    have hΓeq : policyPrefixContext (cvR.parameters ++ cvR.fields) (cvR.fieldIndex jR).val =
        policyPrefixContext (cv.parameters ++ cv.fields) k := by
      rw [hval, hcat]
    have heeq : (cvR.parameters ++ cvR.fields)[(cvR.fieldIndex jR).val] =
        (cv.parameters ++ cv.fields)[k]'hk := by
      simp only [hval, hcat]
    exact ⟨by simpa only [harO.symm, hΓeq, heeq] using dR0⟩
  refine ⟨hΓ, hdO, cvR.domainsTyped.levels (cvR.fieldIndex jR), hdR, ?_⟩
  rw [hlvO]
  exact hbdR

/-- Every iota rule available before this recursor reads all three declarations
from the admitted base; its arguments may still mention new members. -/
theorem prefix_iota_members_old {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm) (w : IotaWitness node.E0) :
    E.members w.recRef = some w.recMember ∧
    E.members w.ctorRef = some w.ctorMember ∧
    E.members w.familyRef = some w.famMember := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  have hsub := recNode_E0_sub node
  have hr : E.members w.recRef = some w.recMember := by
    rcases group_member_cases hmem hL hrr node (hsub _ _ w.hrec) with
      hb | ⟨_, hm⟩ | ⟨hr, _⟩ | ⟨i, _, hm⟩
    · exact hb
    · have hc := w.hrecK
      rw [hm, hfam] at hc
      cases hc
    · have hp := w.hrec
      rw [hr, node.fresh] at hp
      cases hp
    · have hc := w.hrecK
      rw [hm, (node.a.constructorViews i).hasClass] at hc
      cases hc
  let c := envWfT_cellHT hE hr w.hrecK
  have hf : w.familyRef = c.cell.adm.family.ref :=
    Option.some.inj ((memberFamRef_recMember w).symm.trans
      (memberFamRef_recAdm c.cell.adm w.hrecK))
  have hfamE := c.cell.env_extends _ _ c.cell.adm.family.present
  have hfm : w.famMember = c.cell.adm.family.member := by
    have hp := node.base _ _ hfamE
    rw [← hf] at hp
    exact Option.some.inj (w.hfam.symm.trans hp)
  have hnm : w.nMinors = c.cell.adm.constructors.length := by
    have hp := c.cell.adm.recursorRef
    have hw := w.hrecIdx
    rw [hf] at hw
    omega
  let i : Fin c.cell.adm.constructors.length := ⟨w.ctorIdx, hnm ▸ w.hidx⟩
  have hctorE := c.cell.env_extends _ _ (c.cell.adm.constructorsPresent i)
  have hcr : w.ctorRef = c.cell.adm.family.ref + 1 + i.val := by
    rw [w.hctorIdx, hf]
  have hcm : w.ctorMember = c.cell.adm.constructors[i] := by
    have hp := node.base _ _ hctorE
    rw [← hcr] at hp
    exact Option.some.inj (w.hctor.symm.trans hp)
  exact ⟨hr, by simpa only [hcm, hcr] using hctorE,
    by simpa only [hfm, hf] using hfamE⟩

/-- The partial prefix and the admitted base have exactly the same raw iota
steps. This does not restrict the typing of their arguments. -/
theorem derivedIota_before_rec_iff {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm) (lhs rhs : Expr Nat) :
    Nonempty (DerivedIota node.E0 lhs rhs) ↔ Nonempty (DerivedIota E lhs rhs) := by
  constructor
  · rintro ⟨h⟩
    cases h with
    | of w =>
      have hm := prefix_iota_members_old hE hfam hctors hrec hmem hWR node w
      exact ⟨.of { w with hrec := hm.1, hctor := hm.2.1, hfam := hm.2.2 }⟩
  · rintro ⟨h⟩
    cases h with
    | of w => exact ⟨.of (extWitness node.base w)⟩

/-- Raw-rule equality does not imply direct typing restriction, even in the
admitted Eq-prefix-W fixture and a context already well formed in the base.
The fresh family application still names a member absent from that base. -/
theorem freshFamily_typing_does_not_restrict :
    Nonempty (CtxWfT eqEnvT 0 [.assumption (.sort .zero)]) ∧
    Nonempty (HasTyT eqWNode.E0 0 [.assumption (.sort .zero)]
      (.app (.const 66 []) (.bvar 0)) (.sort (.succ .zero))) ∧
    ¬ Nonempty (HasTyT eqEnvT 0 [.assumption (.sort .zero)]
      (.app (.const 66 []) (.bvar 0)) (.sort (.succ .zero))) := by
  refine ⟨⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩,
    ⟨eqWVAppTyT rfl (.bvar _ 0 _ rfl)⟩, ?_⟩
  intro ⟨h⟩
  obtain ⟨m, hm⟩ := (hasTyT_constsIn h).1
  have hf : eqEnvT.members 66 = none := by simp [eqEnvT_mem]
  rw [hf] at hm
  cases hm

end Rcic.F3.StepWOpen
