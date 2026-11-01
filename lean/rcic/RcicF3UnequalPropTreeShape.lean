import rcic.RcicF3UnequalPropTreeFixture
import rcic.RcicF3AndFixture

/-!
# Shared literal-view extraction for the two unequal-mirror trees

The family and leaf are fixed existing declarations. The second constructor
has one arbitrary stored field. A recursor beginning with the family Prop
parameter forces the same parameter/index cut for every RecNode.
This factors the old literal-view/bound proofs once; both old and local-beta
fixtures instantiate it. No admission or bound premise is invented.
Source draft. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.UnequalPropTreeShape
open Rcic.Declarative
open Rcic.Declarative.UnequalPropTree (ownParam fam leaf famApp eFam eLeaf)

noncomputable def nodeMember (A : Expr Nat) : CheckedMember :=
  ⟨.constructorM, 0, .pi ownParam (.pi A (famApp (.bvar 1))), none⟩
noncomputable def allEnv (A : Expr Nat) (rm : CheckedMember) : ResolvedEnv :=
  extendEnv (extendEnv eLeaf 6 (nodeMember A)) 7 rm
abbrev Node (A : Expr Nat) (rm : CheckedMember) := RecNode emptyEnv (allEnv A rm) 4 7 rm

variable {A : Expr Nat} {rm : CheckedMember}

theorem familyMember (n : Node A rm) : n.a.family.member = fam :=
  Option.some.inj ((node_fam_member n).symm.trans rfl)

theorem familyInfo (hhead : ∃ B : Expr Nat, rm.mtype = .pi (.sort .zero) B)
    (n : Node A rm) :
    n.a.family.parameters = [.sort .zero] ∧ n.a.family.indices = [] ∧
      n.a.family.resultLevel = .zero := by
  have hst := n.a.family.storedType
  rw [familyMember n] at hst
  obtain ⟨hds, hbody⟩ := policyPi_split_eq [.sort .zero] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  injection hbody with hl
  cases hp : n.a.family.parameters with
  | nil =>
      obtain ⟨B, hB⟩ := hhead
      have hr := n.a.recursorType
      unfold policyRecursorType at hr
      rw [hp] at hr
      change rm.mtype = .pi (policyMotiveType n.a.family n.a.policy) _ at hr
      have hh := hB.symm.trans hr
      injection hh with hdom _
      obtain ⟨C, D, hCD⟩ := policyMotiveType_pi n.a.family n.a.policy
      rw [hCD] at hdom
      cases hdom
  | cons B Bs =>
      rw [hp, List.cons_append] at hds
      obtain ⟨hB, htail⟩ := List.cons.inj hds
      obtain ⟨hBs, hIs⟩ := List.append_eq_nil.mp htail.symm
      refine ⟨?_, hIs, hl.symm⟩
      simp only [hp, hBs, ← hB]

theorem familyArity (n : Node A rm) : n.a.family.member.arity = 0 :=
  congrArg (fun m : CheckedMember => m.arity) (familyMember n)

theorem ctorCount (n : Node A rm) : n.a.constructors.length = 2 :=
  node_ctors_length (ctors := [(5, leaf), (6, nodeMember A)]) n rfl

theorem policyPropOnly (hhead : ∃ B : Expr Nat, rm.mtype = .pi (.sort .zero) B)
    (n : Node A rm) : n.a.policy = .propOnly :=
  (n.a.uniformProp_many (fun σ => by rw [(familyInfo hhead n).2.2]; rfl)
    (by rw [ctorCount n]; decide)).1

theorem ctorInfo (n : Node A rm) (i : Fin n.a.constructors.length) :
    (n.a.constructors[i.val] = leaf ∧ i.val = 0) ∨
      (n.a.constructors[i.val] = nodeMember A ∧ i.val = 1) := by
  obtain ⟨k, hk⟩ := i
  have hm := node_ctor_member n ⟨k, hk⟩
  have hi : k < 2 := (ctorCount n) ▸ hk
  cases k with
  | zero => exact Or.inl ⟨Option.some.inj (hm.symm.trans rfl), rfl⟩
  | succ k =>
      cases k with
      | zero => exact Or.inr ⟨Option.some.inj (hm.symm.trans rfl), rfl⟩
      | succ k => exact (by omega : False).elim

theorem views (hhead : ∃ B : Expr Nat, rm.mtype = .pi (.sort .zero) B)
    (n : Node A rm) (i : Fin n.a.constructors.length) :
    (n.a.constructorViews i).parameters = [ownParam] ∧
    (n.a.constructorViews i).resultIndices = [] ∧
    (((n.a.constructorViews i).fields = [] ∧ i.val = 0) ∨
      ((n.a.constructorViews i).fields = [A] ∧ i.val = 1)) := by
  obtain ⟨hP, hI, _⟩ := familyInfo hhead n
  have hpl : (n.a.constructorViews i).parameters.length = 1 := by
    rw [(n.a.constructorViews i).parameterCount, hP]
    rfl
  have hri : (n.a.constructorViews i).resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [(n.a.constructorViews i).indexCount, hI]
    rfl
  have hst := (n.a.constructorViews i).storedType
  have hne := foldApps_ne_pi (.const n.a.family.ref (policyFamilyLevels n.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals (n.a.constructorViews i).parameters.length
      (n.a.constructorViews i).fields.length ++ (n.a.constructorViews i).resultIndices)
  rcases ctorInfo n i with ⟨e, h0⟩ | ⟨e, h1⟩
  · have hm : (n.a.constructors[i.val]).mtype =
        policyPi [ownParam] (famApp (.bvar 0)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _
      (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨hp, hf⟩ := List.append_inj
      (show ([ownParam] : List (Expr Nat)) ++ [] = _ from hsp)
      (by rw [hpl]; rfl)
    exact ⟨hp.symm, hri, Or.inl ⟨hf.symm, h0⟩⟩
  · have hm : (n.a.constructors[i.val]).mtype =
        policyPi [ownParam, A] (famApp (.bvar 1)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _
      (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨hp, hf⟩ := List.append_inj
      (show ([ownParam] : List (Expr Nat)) ++ [A] = _ from hsp)
      (by rw [hpl]; rfl)
    exact ⟨hp.symm, hri, Or.inr ⟨hf.symm, h1⟩⟩

theorem ctorBound (n : Node A rm) (K σ : Nat → Nat)
    (hleaf : ∃ u : Level, ∃ d : HasTyT eFam 0 [] leaf.mtype (.sort u), LOKt σ 4 K d)
    (hnode : ∃ u : Level, ∃ d : HasTyT eFam 0 [] (nodeMember A).mtype (.sort u), LOKt σ 4 K d)
    (i : Fin n.a.constructors.length) :
    ∃ u : Level, ∃ d : HasTyT eFam n.a.family.member.arity []
      (n.a.constructors[i.val]).mtype (.sort u), LOKt σ 4 K d := by
  rw [familyArity n]
  rcases ctorInfo n i with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]; exact hleaf
  · rw [e]; exact hnode

theorem fieldBound (hhead : ∃ B : Expr Nat, rm.mtype = .pi (.sort .zero) B)
    (n : Node A rm) (K σ : Nat → Nat)
    (hfield : ∃ l : Level,
      ∃ d : HasTyT eFam 0 [.assumption ownParam] A (.sort l), LOKt σ 4 K d)
    (i : Fin n.a.constructors.length) (k : Fin (n.a.constructorViews i).fields.length) :
    ∃ l : Level,
      ∃ d : HasTyT eFam n.a.family.member.arity
        (policyPrefixContext ((n.a.constructorViews i).parameters ++
          (n.a.constructorViews i).fields)
          ((n.a.constructorViews i).parameters.length + k.val))
        ((n.a.constructorViews i).fields[k]) (.sort l), LOKt σ 4 K d := by
  obtain ⟨hp, _, hfields⟩ := views hhead n i
  rcases hfields with ⟨hf, _⟩ | ⟨hf, _⟩
  · have hlen : (n.a.constructorViews i).fields.length = 0 := congrArg List.length hf
    exact (Nat.not_lt_zero k.val (Nat.lt_of_lt_of_eq k.isLt hlen)).elim
  · obtain ⟨k, hk⟩ := k
    have hk0 : k = 0 := by
      rw [hf] at hk
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    have hΓ : policyPrefixContext ((n.a.constructorViews i).parameters ++
        (n.a.constructorViews i).fields)
        ((n.a.constructorViews i).parameters.length + 0) = [.assumption ownParam] := by
      rw [hp, hf]
      rfl
    have hfieldEq : (n.a.constructorViews i).fields[0]'hk = A := by
      simp only [hf, List.getElem_cons_zero]
    change ∃ l : Level,
      ∃ d : HasTyT eFam n.a.family.member.arity
        (policyPrefixContext ((n.a.constructorViews i).parameters ++
          (n.a.constructorViews i).fields)
          ((n.a.constructorViews i).parameters.length + 0))
        ((n.a.constructorViews i).fields[0]'hk) (.sort l), LOKt σ 4 K d
    rw [familyArity n, hΓ, hfieldEq]
    exact hfield

end Rcic.F3.PSet.UnequalPropTreeShape
