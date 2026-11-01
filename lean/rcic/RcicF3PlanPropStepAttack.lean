import rcic.RcicF3PlanPropEndAttack
import rcic.RcicF3PendAWGroup

/-!
# Paying the StepAG antecedents at the actual AccR group

The typed singleton Prop group has a positive-depth recursive field and
large elimination. All walk and bound premises are produced, including the
Prop field typings. No Acc/W family is excluded. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PlanPropStepAttack
open Rcic.Declarative
abbrev Node := RecNode emptyEnv accEnv 0 2 accRecMember

noncomputable def pNode : Node where
  E0 := accPrefix
  a := accGroupAdmitted
  h14 := AccEnv.accIotaClause
  fam := rfl
  fresh := rfl
  sub := fun _ _ h => h
  base := fun _ _ h => nomatch h
  h04 := AccEnv.accCensus
  h07 := AccEnv.accUniverseRow
  h12 := accMinorMatch
  famTyped := AccEnv.accRecTyped.1
  ctorsTyped := AccEnv.accRecTyped.2.1
  u := AccEnv.accRecSortU
  hT := AccEnv.accRecTyT

kernel_rfl_theorem shape : (pNode.h14.shapesAt ⟨0, by decide⟩)[0]? = some (.recursive 1)
theorem pendA : PendA pNode := ⟨⟨0, by decide⟩, 0, 0, shape⟩

theorem familyMember (node : Node) : node.a.family.member = accFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

kernel_rfl_theorem recFirstDom :
  (recPreDomsOf accGroupAdmitted ++ [recMajorOf accGroupAdmitted])[0]? = some (.sort .zero)

theorem familyInfo (node : Node) :
    node.a.family.parameters = [.sort .zero] ∧ node.a.family.indices = [] ∧
    node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [familyMember node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [.sort .zero] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  injection h2 with hrl
  obtain ⟨_, hql⟩ := family_params_of_recType node _ h1
    (recPreDomsOf accGroupAdmitted ++ [recMajorOf accGroupAdmitted]) (recResultOf accGroupAdmitted)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (recType_eq accGroupAdmitted) 1
    (fun k hk hne e he => by
      cases k with
      | zero =>
        rw [recFirstDom] at he
        cases he
        exact fun _ _ h => Expr.noConfusion h
      | succ k =>
        have hz : k = 0 := by change k + 1 ≤ 1 at hk; omega
        subst hz
        exact (hne rfl).elim)
  have hq := List.eq_nil_of_length_eq_zero hql
  rw [hq, List.append_nil] at h1
  exact ⟨h1.symm, hq, hrl.symm⟩

theorem ctorInfo (node : Node) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = accIntroMember ∧ i.val = 0 := by
  have hlen : node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(1, accIntroMember)]) node rfl
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
    (by simpa only [hlen] using i.isLt))
  have h := node_ctor_member node i
  exact ⟨Option.some.inj (h.symm.trans (by rw [hi]; rfl)), hi⟩

theorem views (node : Node) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [.sort .zero] ∧
    (node.a.constructorViews i).resultIndices = [] ∧
    (node.a.constructorViews i).fields = [accField] := by
  obtain ⟨hP, hI, _⟩ := familyInfo node
  have hpl : (node.a.constructorViews i).parameters.length = 1 := by
    rw [(node.a.constructorViews i).parameterCount, hP]; rfl
  have hri : (node.a.constructorViews i).resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [(node.a.constructorViews i).indexCount, hI]; rfl
  have hst := (node.a.constructorViews i).storedType
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals
      (node.a.constructorViews i).parameters.length (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  have hm : (node.a.constructors[i.val]).mtype =
      policyPi ([.sort .zero] ++ [accField]) (accApp (.bvar 1)) := by
    rw [(ctorInfo node i).1]; rfl
  have hsp := (policyPi_split_eq _ _ _ _ (fun _ _ h => Expr.noConfusion h) hne
    (hm.symm.trans hst)).1
  obtain ⟨hp, hf⟩ := List.append_inj hsp (by rw [hpl]; rfl)
  exact ⟨hp.symm, hri, hf.symm⟩

theorem walkClass (node : Node) : WalkClass node.a.family.parameters.length AccEnv.accMembersT := by
  rw [(familyInfo node).1]
  exact ⟨True.intro, rfl, rfl, True.intro⟩

theorem walkAgree (node : Node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) AccEnv.accMembersT :=
  walkAgree_of_walkClass node AccEnv.accMembersT (walkClass node)

theorem ctorBound (node : Node) (K τ : Nat → Nat)
    (i : Fin node.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT accFamOnly node.a.family.member.arity []
      (node.a.constructors[i.val]).mtype (.sort u)), LOKt τ 4 K d := by
  rw [familyMember node, (ctorInfo node i).1]
  refine ⟨_, AccEnv.accIntroTyT accFamOnly rfl, ?_⟩
  simp [AccEnv.accIntroTyT, AccEnv.accFieldTyT, LOKt, LevelsOK, evalTotal]

theorem introBound (K : Nat → Nat) : PendAWGroup.ownBound K accIntroAdmitted := by
  apply PendAWGroup.ownBound_of_at
  intro vs k
  cases k with
  | zero =>
    change ∃ d : HasTyT accFamOnly 0 [] (.sort .zero) (.sort (.succ .zero)),
      LOKt (σOf vs) 4 K d
    exact ⟨.sort [] .zero, by change 1 ≤ 4; decide⟩
  | succ k =>
    cases k with
    | zero =>
      change ∃ d : HasTyT accFamOnly 0 [.assumption (.sort .zero)] accField
          (.sort (.imax .zero .zero)), LOKt (σOf vs) 4 K d
      refine ⟨AccEnv.accFieldTyT accFamOnly rfl, ?_⟩
      simp [AccEnv.accFieldTyT, LOKt, LevelsOK, evalTotal]
    | succ k =>
      exact PendAWGroup.ownAt_ge _ _ _ _
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))

theorem walkBound (K : Nat → Nat) : WalkB2 K AccEnv.accMembersT := by
  exact ⟨True.intro, introBound K, True.intro, True.intro⟩

theorem propFieldBound (K : Nat → Nat) (node : Node)
    (i : Fin node.a.constructors.length) (τ : Nat → Nat)
    (k : Fin (node.a.constructorViews i).fields.length) :
    ∃ l : Level, UniformProp l ∧
      ∃ d : HasTyT accFamOnly node.a.family.member.arity
        (policyPrefixContext (node.a.family.parameters ++ (node.a.constructorViews i).fields)
          (node.a.family.parameters.length + k.val))
        ((node.a.constructorViews i).fields[k]) (.sort l), LOKt τ 4 K d := by
  rcases k with ⟨k, hk⟩
  have hf := (views node i).2.2
  rw [hf] at hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  subst k
  have hd : ∃ l : Level, UniformProp l ∧
      ∃ d : HasTyT accFamOnly 0 [.assumption (.sort .zero)] accField (.sort l),
        LOKt τ 4 K d := by
    refine ⟨.imax .zero .zero, accImaxZero_prop, AccEnv.accFieldTyT accFamOnly rfl, ?_⟩
    simp [AccEnv.accFieldTyT, LOKt, LevelsOK, evalTotal]
  have hn : node.a.family.member.arity = 0 := by rw [familyMember node]; rfl
  have hΓ : policyPrefixContext
      (node.a.family.parameters ++ (node.a.constructorViews i).fields)
      node.a.family.parameters.length = [.assumption (.sort .zero)] := by
    rw [(familyInfo node).1, hf]
    rfl
  have hA : (node.a.constructorViews i).fields[0]'(by rw [hf]; decide) = accField := by
    simp only [hf, List.getElem_cons_zero]
  have hmove : ∀ (n : Nat) (Γ : LCtx) (A : Expr Nat),
      0 = n → [.assumption (.sort .zero)] = Γ → accField = A →
      ∃ l : Level, UniformProp l ∧
        ∃ d : HasTyT accFamOnly n Γ A (.sort l), LOKt τ 4 K d := by
    intro n Γ A en eΓ eA
    cases en
    cases eΓ
    cases eA
    exact hd
  exact hmove _ _ _ hn.symm hΓ.symm hA.symm

theorem boundG (K : Nat → Nat) : BoundG K AccEnv.accEnvWfT := by
  exact ⟨True.intro, fun node i vs _ _ => ctorBound node K (σOf vs) i,
    walkBound K, fun node _ _ i vs _ k => propFieldBound K node i (σOf vs) k⟩

theorem boundDG : BoundDG (fun _ => 1) AccEnv.accEnvWfT := by
  exact boundDG_of_boundG _ AccEnv.accEnvWfT
    ⟨True.intro, fun _ _ _ => Nat.le_refl 1⟩ (boundG _)

theorem empty_gInv (P : Premises4) (K : Nat → Nat) :
    PlanRole.GInv RawFamily.role P K (.empty : EnvWfT emptyEnv) := by
  intro ctx _ plans _ μ _
  constructor
  · intro r m hm; nomatch hm
  · intro Efin _ r m hm _; nomatch hm

/-- Literal refutation of the current planned raw-role StepAG. Every one of
its four group-step antecedents has been supplied at the admitted AccR group. -/
theorem stepAG_false (P : Premises4) :
    ¬ PlanRole.StepAG RawFamily.role P (fun _ => 1) := by
  intro h
  exact PlanPropEndAttack.gInv_false P
    (h (E := emptyEnv) (E' := accEnv) (f := 0) (rr := 2)
      (fm := accFamMember) (rm := accRecMember) (ctors := [(1, accIntroMember)])
      .empty rfl (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl
      AccEnv.accMembersT ⟨pNode, pendA⟩ walkAgree (boundG _) boundDG (empty_gInv P _))

/-- The universal current operational target implies the very contradiction
that A-M1's required non-refutability witness must exclude. -/
theorem universal_target_refuted :
    (∀ (P : Premises4) (K : Nat → Nat), PlanRole.StepAG RawFamily.role P K) →
      (Premises4 → False) := by
  intro h P
  exact stepAG_false P (h P (fun _ => 1))

end Rcic.F3.PSet.PlanPropStepAttack
