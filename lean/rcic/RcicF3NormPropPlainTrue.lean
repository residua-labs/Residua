import rcic.RcicF3NormPropPlainIota
import rcic.RcicF3NormPropCtorUniform
import rcic.RcicTypedGroupPins

/-!
# The actual admitted nullary Prop group for plain indexed iota

The canonical normalized table and plan are obtained from trueMembersT.
Every bound premise and every plain-field premise is produced from that
actual typed group. The complete new RecPkg is then invoked at this table.
An explicit legacy witness exists here, so this instance is distinct from
the positive-depth no-legacy-witness argument at AccR.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormPropPlainTrue
open Rcic.Declarative Rcic.Model.PS RawFamily

abbrev Node := RecNode emptyEnv trueEnvU 0 2 trueRecMemberU

theorem family_member (node : Node) : node.a.family.member = trueFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

theorem family (node : Node) : node.a.family.parameters = [] ∧
    node.a.family.indices = [] ∧ node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [family_member node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

theorem count (node : Node) : node.a.constructors.length = 1 :=
  node_ctors_length (ctors := [(1, trueIntroMember)]) node rfl

theorem slot_zero (node : Node) (i : Fin node.a.constructors.length) : i.val = 0 := by
  have hi : i.val < 1 := Nat.lt_of_lt_of_eq i.isLt (count node)
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)

theorem constructor_member (node : Node) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = trueIntroMember := by
  have h := node_ctor_member node i
  have hr : 0 + 1 + i.val = 1 := by rw [slot_zero node i]
  have hmem : trueEnvU.members (0 + 1 + i.val) = some trueIntroMember := by
    rw [hr]
    rfl
  exact Option.some.inj (h.symm.trans hmem)

theorem view (node : Node) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [] ∧
    (node.a.constructorViews i).fields = [] ∧
    (node.a.constructorViews i).resultIndices = [] := by
  have hp : (node.a.constructorViews i).parameters = [] := by
    have h := (node.a.constructorViews i).parameterCount
    rw [(family node).1] at h
    exact List.eq_nil_of_length_eq_zero h
  have hi : (node.a.constructorViews i).resultIndices = [] := by
    have h := (node.a.constructorViews i).indexCount
    rw [(family node).2.1] at h
    exact List.eq_nil_of_length_eq_zero h
  have hst := (node.a.constructorViews i).storedType
  have htype : (node.a.constructors[i.val]).mtype = (.const 0 [] : Expr Nat) :=
    congrArg CheckedMember.mtype (constructor_member node i)
  have hst' := htype.symm.trans hst
  rw [hp, List.nil_append] at hst'
  have hn := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals 0 (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  have hf := (policyPi_split_eq [] _ (.const 0 []) _
    (fun _ _ h => Expr.noConfusion h) hn hst').1
  exact ⟨hp, hf.symm, hi⟩

theorem policy (node : Node) : node.a.policy = .anySort := by
  cases h : node.a.policy with
  | anySort => rfl
  | propOnly =>
      have ha := node.a.recursorArity
      rw [family_member node, h] at ha
      change 1 = 0 at ha
      exact False.elim (Nat.noConfusion ha)

theorem shapes (node : Node) (i : Fin node.a.constructors.length) :
    node.h14.shapesAt i = [] := by
  have h := node.h14.analyzed i
  rw [(view node i).2.1] at h
  exact (Option.some.inj h).symm

theorem noFun (node : Node) : NoFunRec node := by
  intro i s hs
  rw [shapes node i] at hs
  exact (List.not_mem_nil _ hs).elim

theorem fields_free (node : Node) (i : Fin node.a.constructors.length) A
    (hA : A ∈ (node.a.constructorViews i).fields) : occursConst node.a.family.ref A = false := by
  rw [(view node i).2.1] at hA
  exact (List.not_mem_nil _ hA).elim

theorem bound (K : Nat → Nat) : BoundG K trueEnvUWfT := by
  refine ⟨trivial, ?_, ?_, ?_⟩
  · intro node i vs _ _
    rw [constructor_member node i]
    exact ⟨.zero, trueConstTyT rfl, fun l hl => (List.not_mem_nil l hl).elim⟩
  · exact ⟨trivial, fun _ _ _ k => k.elim0, trivial, trivial⟩
  · intro node _ _ i vs _ k
    have hk : k.val < 0 := Nat.lt_of_lt_of_eq k.isLt
      (congrArg List.length (view node i).2.1)
    exact (Nat.not_lt_zero _ hk).elim

theorem ctorClasses : ∀ c ∈ [(1, trueIntroMember)], c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 0) (fm := trueFamMember)
    (ctors := [(1, trueIntroMember)]) (rr := 2) (rm := trueRecMemberU)
    rfl ctorClasses rfl trueMembersT

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P trueEnvUWfT

theorem faithful (P : Premises4) :
    EvalRole.Faithful role P (table P) (NormRole.envCtx trueEnvUWfT)
      (EvalRole.envPlan trueEnvUWfT) trueEnvU :=
  (NormRole.table_spec P trueEnvUWfT).1

/-- The new complete producer is applied with all premises paid. -/
theorem package (P : Premises4) (K : Nat → Nat) :
    RecPkg P (table P) K trueEnvU 2 trueRecMemberU := by
  apply NormPropPlainIota.rec_pkg P (table P) K
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) EnvWfT.empty rfl ctorClasses rfl trueMembersT
    (bound K) (NormRole.gInv_empty P K)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
  · change UniformProp plan.node.a.family.resultLevel
    intro σ
    rw [(family plan.node).2.2]
    rfl
  · exact policy plan.node
  · exact noFun plan.node
  · exact fields_free plan.node

theorem constructor_sound (P : Premises4) (K : Nat → Nat) :
    MemberSound P (table P) K 1 trueIntroMember := by
  let j : Fin plan.node.a.constructors.length := ⟨0, by rw [count]; decide⟩
  have hProp : UniformProp plan.node.a.family.resultLevel := by
    intro σ
    rw [(family plan.node).2.2]
    rfl
  have h := NormPropCtorUniform.member_sound P (table P) K
    (f := 0) (fm := trueFamMember) (ctors := [(1, trueIntroMember)])
    (rr := 2) (rm := trueRecMemberU) EnvWfT.empty rfl ctorClasses rfl trueMembersT
    (bound K) (NormRole.gInv_empty P K)
    (NormRole.envCtx trueEnvUWfT) (EvalRole.envPlan trueEnvUWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) hProp j
  change MemberSound P (table P) K 1 (plan.node.a.constructors[j.val]) at h
  rw [constructor_member] at h
  exact h

theorem inhabited_family (P : Premises4) :
    table P 1 [] ∈ Ed (mkM P (table P)) (table P 0 []) :=
  (constructor_sound P (fun _ => 1) (fun _ => 0) [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1

/-- An actual legacy redex exists: the major is intro and the minor is
the second local argument. No higher-order witness is substituted. -/
noncomputable def witness : IotaWitness trueEnvU where
  recRef := 2
  ctorRef := 1
  ls := [.param 0]
  lsC := []
  recMember := trueRecMemberU
  ctorMember := trueIntroMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 1, .bvar 0]
  fields := []
  ctorParams := []
  kinds := []
  minor := .bvar 0
  hlen := rfl
  familyRef := 0
  famMember := trueFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := by simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
  ctorDoms := []
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.pi (.const 0 []) (.sort (.param 0)),
    .app (.bvar 0) (.const 1 []), .const 0 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := by
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 0 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem witness_lhs : iotaLhsOf witness =
    .app (.app (.app (.const 2 [.param 0]) (.bvar 1)) (.bvar 0)) (.const 1 []) := rfl

theorem witness_rhs : iotaRhsOf witness = .bvar 0 := rfl

def Witness (P : Premises4) (K : Nat → Nat) : Prop :=
  BoundG K trueEnvUWfT ∧ NoFunRec plan.node ∧
  (∀ j A, A ∈ (plan.node.a.constructorViews j).fields →
    occursConst plan.node.a.family.ref A = false) ∧
  RecPkg P (table P) K trueEnvU 2 trueRecMemberU ∧
  MemberSound P (table P) K 1 trueIntroMember ∧
  table P 1 [] ∈ Ed (mkM P (table P)) (table P 0 []) ∧
  witness.recRef = 2 ∧ witness.fields = [] ∧
  iotaRhsOf witness = .bvar 0

theorem component_witness (P : Premises4) (K : Nat → Nat) : Witness P K :=
  ⟨bound K, noFun plan.node, fields_free plan.node, package P K,
    constructor_sound P K, inhabited_family P, rfl, rfl, witness_rhs⟩

theorem component_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (Witness P K → (Premises4 → False)) :=
  fun h => h (component_witness P K) P

end Rcic.F3.PSet.NormPropPlainTrue
