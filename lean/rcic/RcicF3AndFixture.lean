import rcic.RcicF3NatFixture

/-!
# F3 S6-3: the class contains a `Prop` family with large elimination and proof fields

`andEnvUWfT` (the admitted `And` block: `And : Prop → Prop → Prop` at 0,
`intro : Π A B, A → B → And A B` at 1, its recursor eliminating into any
sort at 2) is in `ClassG` and in `BoundG K` for every `K`
(`andEnvUWfT_classG`), and the induction gives a sound model of it
(`andEnvUWfT_envSound`). `intro`'s fields are proofs: the fixture exercises
the recursor's value at `∅` fields and ι read off the right-hand side's
typing.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The recursor node of the `And` block. -/
abbrev AndNode := RecNode emptyEnv andEnvU 0 2 andRecMemberU

theorem and_fam (node : AndNode) : node.a.family.member = andFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

theorem policyMotiveType_pi {E : ResolvedEnv} (family : PolicyFamilyView E) (policy : EliminationPolicy) :
    ∃ A B, policyMotiveType family policy = .pi A B := by
  unfold policyMotiveType
  cases family.indices with
  | nil => exact ⟨_, _, rfl⟩
  | cons _ _ => exact ⟨_, _, rfl⟩

/-- The recursor's stored type fixes the family view's parameter count: the
motive sits right after the parameters and is a product, so `p` is the count
when no other domain among the first ones is a product. -/
theorem family_params_of_recType {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (Ds : List (Expr Nat))
    (hD : Ds = node.a.family.parameters ++ node.a.family.indices) (L : List (Expr Nat)) (b : Expr Nat)
    (hb : ∀ A B, b ≠ .pi A B) (hrt : rm.mtype = policyPi L b) (p : Nat)
    (hpm : ∀ k, k ≤ Ds.length → k ≠ p → ∀ e, L[k]? = some e → ∀ A B, e ≠ .pi A B) :
    node.a.family.parameters.length = p ∧ node.a.family.indices.length = Ds.length - p := by
  have hsp := (policyPi_split_eq _ _ _ _ hb (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (hrt.symm.trans (recType_eq node.a))).1
  have hlen : node.a.family.parameters.length + node.a.family.indices.length = Ds.length := by
    rw [hD, List.length_append]
  have hmot : (recPreDomsOf node.a ++ [recMajorOf node.a])[node.a.family.parameters.length]? =
      some (policyMotiveType node.a.family node.a.policy) := by
    unfold recPreDomsOf
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.cons_append,
      List.getElem?_cons_zero]
  rw [← hsp] at hmot
  have hnp : node.a.family.parameters.length = p := by
    refine @Decidable.byCases (node.a.family.parameters.length = p) _ _ id fun hne => ?_
    obtain ⟨A, B, hAB⟩ := policyMotiveType_pi node.a.family node.a.policy
    exact absurd hAB (hpm _ (by omega) hne _ hmot A B)
  exact ⟨hnp, by omega⟩

/-- The family view of the `And` block: two `Prop` parameters, no index, level `0`. -/
theorem and_family (node : AndNode) :
    node.a.family.parameters = [.sort .zero, .sort .zero] ∧ node.a.family.indices = [] ∧
      node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [and_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [.sort .zero, .sort .zero] _ _ _ (expr_not_pi_of_sort _)
    (expr_not_pi_of_sort _) hst
  injection h2 with hrl
  obtain ⟨_, hql⟩ := family_params_of_recType node _ h1 [.sort .zero, .sort .zero, andMotTy, andMinorTy,
    andApp (.bvar 3) (.bvar 2)] (.app (.bvar 2) (.bvar 0)) (fun _ _ h => Expr.noConfusion h) rfl 2
    (fun k hk hne e he => match k, hk, hne, he with
      | 0, _, _, he => by cases he; exact fun _ _ h => Expr.noConfusion h
      | 1, _, _, he => by cases he; exact fun _ _ h => Expr.noConfusion h
      | 2, _, hne, _ => absurd rfl hne
      | _ + 3, hk, _, _ => absurd hk (by rw [List.length_cons, List.length_cons, List.length_nil]; omega))
  have hq := List.eq_nil_of_length_eq_zero hql
  rw [hq, List.append_nil] at h1
  exact ⟨h1.symm, hq, hrl.symm⟩

theorem and_ctor (node : AndNode) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = andIntroMember ∧ i.val = 0 := by
  have hlen : node.a.constructors.length = 1 := node_ctors_length (ctors := [(1, andIntroMember)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 1 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- The constructor view of `intro`: two `Prop` parameters, two proof fields, no result index. -/
theorem and_view (node : AndNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [.sort .zero, .sort .zero] ∧
      (node.a.constructorViews i).fields = [.bvar 1, .bvar 1] ∧ (node.a.constructorViews i).resultIndices = [] := by
  obtain ⟨hP, hI, _⟩ := and_family node
  have hst := (node.a.constructorViews i).storedType
  have hm : (node.a.constructors[i.val]).mtype = policyPi [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
      (andApp (.bvar 3) (.bvar 2)) := by rw [(and_ctor node i).1]; rfl
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals (node.a.constructorViews i).parameters.length
      (node.a.constructorViews i).fields.length ++ (node.a.constructorViews i).resultIndices)
  have hsp := (policyPi_split_eq _ _ _ _ (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
  have hpl : (node.a.constructorViews i).parameters.length = 2 := by
    rw [(node.a.constructorViews i).parameterCount, hP]; rfl
  have hri : (node.a.constructorViews i).resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [(node.a.constructorViews i).indexCount, hI]; rfl
  obtain ⟨h1, h2⟩ := List.append_inj (show ([.sort .zero, .sort .zero] : List (Expr Nat)) ++ [.bvar 1, .bvar 1] = _
    from hsp) (by rw [hpl]; rfl)
  exact ⟨h1.symm, h2.symm, hri⟩

/-- The proof fields' typings, at level `0`. -/
theorem and_fields_typed (K : Nat → Nat) (vs : List Nat) (Ps Fs : List (Expr Nat))
    (hP : Ps = [.sort .zero, .sort .zero]) (hF : Fs = [.bvar 1, .bvar 1]) (k : Fin Fs.length) :
    ∃ l : Level, UniformProp l ∧ ∃ d : HasTyT (extendEnv emptyEnv 0 andFamMember) 0
      (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val)) (Fs[k]) (.sort l), LOKt (σOf vs) 4 K d := by
  subst hP; subst hF
  match k with
  | ⟨0, _⟩ => exact ⟨.zero, fun _ => rfl, .bvar _ 1 _ rfl, trivial⟩
  | ⟨1, _⟩ => exact ⟨.zero, fun _ => rfl, .bvar _ 1 _ rfl, trivial⟩

/-- **The `And` block is in the class**, at every instance bound: a `Prop`
family with large elimination and proof fields. -/
theorem andEnvUWfT_classG : ClassG andEnvUWfT ∧ ∀ K, BoundG K andEnvUWfT := by
  refine ⟨⟨trivial, fun node => ⟨fun i => ?_,
    fun _ _ i => ?_⟩, fun node => ?_⟩,
    fun K => ⟨trivial, fun node i vs _ _ => ?_, ?_, fun node _ _ i vs _ k => ?_⟩⟩
  · obtain ⟨_, hf, _⟩ := and_view node i
    rw [hf]
    exact ⟨Or.inl rfl, Or.inl rfl, trivial⟩
  · obtain ⟨_, _, hr⟩ := and_view node i
    intro k _
    rw [hr]
    rfl
  · rw [(and_family node).1]
    exact ⟨trivial, rfl, rfl, trivial⟩
  · rw [(and_ctor node i).1, and_fam node]
    refine ⟨andIntroSortU, andIntroTyT rfl, ?_⟩
    simp [LOKt, LevelsOK, evalTotal, andIntroTyT, andOfTyT, andIntroSortU]
  · refine ⟨trivial, fun vs _ _ k => ?_, trivial, trivial⟩
    match k with
    | ⟨0, _⟩ => exact ⟨.sort _ .zero, (by decide : 1 ≤ 4)⟩
    | ⟨1, _⟩ => exact ⟨.sort _ .zero, (by decide : 1 ≤ 4)⟩
    | ⟨2, _⟩ => exact ⟨.bvar _ 1 _ rfl, trivial⟩
    | ⟨3, _⟩ => exact ⟨.bvar _ 1 _ rfl, trivial⟩
  · rw [show node.a.family.member.arity = 0 by rw [and_fam node]; rfl]
    exact and_fields_typed K vs _ _ (and_family node).1 (and_view node i).2.1 k

/-- The induction applied to the `And` block: its table is a sound model of it. -/
theorem andEnvUWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx andEnvUWfT) andEnvUWfT)) σ K andEnvU n :=
  envSound_envμR_classG P K andEnvUWfT andEnvUWfT_classG.1 (andEnvUWfT_classG.2 K) σ n

end PSet

end Rcic.F3
