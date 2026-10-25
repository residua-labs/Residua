import rcic.RcicF3MainG
import rcic.RcicG2AdmitBool

/-!
# F3 S5a-18: the class of `consistent4_G` contains groups with constructors

`boolWfT` is the admitted `Bool` block (family `Type` at 0, two constructors at 1
and 2, recursor at 3), as one `EnvWfT.group` step from the empty environment,
built from the in-tree admission chain `Rcic.G2.boolGroupChain`.
`boolWfT_classG`: it is in `ClassG` and in `BoundG K` for every `K`;
`boolWfT_envSound`: the induction of `RcicF3MainG` gives a sound model of it.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

theorem policyPi_eq_const {r : Nat} {ls : List Level} {b : Expr Nat} :
    (D : List (Expr Nat)) → policyPi D b = .const r ls → D = [] ∧ b = .const r ls
  | [], h => ⟨rfl, h⟩
  | A :: D, h => by
      have h' : Expr.pi A (policyPi D b) = .const r ls := h
      cases h'

theorem foldApps_eq_const {r : Nat} {ls : List Level} : (g : Expr Nat) → (as : List (Expr Nat)) →
    foldApps g as = .const r ls → as = [] ∧ g = .const r ls
  | _, [], h => ⟨rfl, h⟩
  | g, a :: as, h => by
      have := (foldApps_eq_const (.app g a) as h).2
      cases this

/-- The admitted `Bool` block, as one group step. -/
def boolWfT : EnvWfT Rcic.G2.boolEnv :=
  .group emptyEnv 0 natFamMember [(1, natZeroMember), (2, natZeroMember)] 3 Rcic.G2.boolRecMember Rcic.G2.boolEnv
    .empty rfl (fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      · rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact absurd hc (List.not_mem_nil _))
    rfl (groupMembersT_of_chain Rcic.G2.boolGroupChain)

theorem bool_ctor (node : RecNode emptyEnv Rcic.G2.boolEnv 0 3 Rcic.G2.boolRecMember)
    (i : Fin node.a.constructors.length) : node.a.constructors[i.val] = natZeroMember := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, natZeroMember), (2, natZeroMember)]) node rfl
  have hz : Rcic.G2.boolEnv.members (0 + 1 + i.val) = some natZeroMember := by
    have hi : i.val < 2 := by have := i.isLt; omega
    generalize i.val = k at hi ⊢
    match k, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  exact Option.some.inj ((node_ctor_member node i).symm.trans hz)

/-- A constructor view of the `Bool` block has no parameters, fields or result indices. -/
theorem bool_views (node : RecNode emptyEnv Rcic.G2.boolEnv 0 3 Rcic.G2.boolRecMember)
    (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields = [] ∧
      (node.a.constructorViews i).resultIndices = [] := by
  have e : (node.a.constructors[i.val]).mtype = .const 0 [] := by rw [bool_ctor node i]; rfl
  have hst := (node.a.constructorViews i).storedType
  rw [e] at hst
  obtain ⟨hD, hb⟩ := policyPi_eq_const _ hst.symm
  obtain ⟨has, _⟩ := foldApps_eq_const _ _ hb
  exact ⟨hD, (List.append_eq_nil.mp has).2⟩

/-! The walk of an admitted block is produced by `groupMembersT_of_chain`, whose
term destructures proofs (`And.rec`); these let the walk conditions see
through it. -/

theorem walkClass_andRec (np : Nat) {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)} {a b : Prop}
    (F : a → b → GroupMembersT S E ms E') (h : a ∧ b) :
    WalkClass np (@And.rec a b (fun _ => GroupMembersT S E ms E') F h) = WalkClass np (F h.1 h.2) := by
  cases h; rfl

theorem walkB2_andRec (K : Nat → Nat) {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)} {a b : Prop}
    (F : a → b → GroupMembersT S E ms E') (h : a ∧ b) :
    WalkB2 K (@And.rec a b (fun _ => GroupMembersT S E ms E') F h) = WalkB2 K (F h.1 h.2) := by
  cases h; rfl

/-- The `Bool` block's constructors have no fields. -/
theorem bool_fields (node : RecNode emptyEnv Rcic.G2.boolEnv 0 3 Rcic.G2.boolRecMember)
    (i : Fin node.a.constructors.length) : (node.a.constructorViews i).fields = [] :=
  (List.append_eq_nil.mp (bool_views node i).1).2

theorem bool_params (node : RecNode emptyEnv Rcic.G2.boolEnv 0 3 Rcic.G2.boolRecMember) :
    node.a.family.parameters.length = 0 := by
  have hm := node_fam_member node
  have hz : Rcic.G2.boolEnv.members 0 = some natFamMember := rfl
  have hfm : node.a.family.member = natFamMember := Option.some.inj (hm.symm.trans hz)
  have hst := node.a.family.storedType
  rw [hfm] at hst
  have := (policyPi_split_eq [] _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst).1
  rw [(List.append_eq_nil.mp this.symm).1]
  rfl

/-- **The `Bool` block is in the class**, at every instance bound. -/
theorem boolWfT_classG : ClassG boolWfT ∧ ∀ K, BoundG K boolWfT := by
  refine ⟨⟨trivial, fun node => ⟨fun i => ?_,
    fun _ _ i k hk => by rw [bool_fields node i] at hk; exact absurd hk (Nat.not_lt_zero _)⟩, fun node => ?_⟩,
    fun K => ⟨trivial, fun node i vs hvl _ => ?_, ?_, fun node _ _ i _ _ k => by
      have hl : (node.a.constructorViews i).fields.length = 0 := by rw [bool_fields node i]; rfl
      have := k.isLt
      exact (by omega : False).elim⟩⟩
  · rw [bool_fields node i]; trivial
  · rw [bool_params node]
    show WalkClass 0 (groupMembersT_of_chain Rcic.G2.boolGroupChain)
    unfold Rcic.G2.boolGroupChain
    simp only [groupMembersT_of_chain]
    repeat rw [walkClass_andRec]
    refine ⟨trivial, ?_⟩
    repeat rw [walkClass_andRec]
    refine ⟨rfl, ?_⟩
    repeat rw [walkClass_andRec]
    refine ⟨rfl, ?_⟩
    repeat rw [walkClass_andRec]
    exact ⟨rfl, trivial⟩
  · rw [bool_ctor node i]
    exact ⟨.succ .zero, .const [] 0 [] natFamMember rfl rfl rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩
  · show WalkB2 K (groupMembersT_of_chain Rcic.G2.boolGroupChain)
    unfold Rcic.G2.boolGroupChain
    simp only [groupMembersT_of_chain]
    repeat rw [walkB2_andRec]
    refine ⟨trivial, ?_⟩
    repeat rw [walkB2_andRec]
    refine ⟨fun _ _ _ k => (Nat.not_lt_zero _ k.isLt).elim, ?_⟩
    repeat rw [walkB2_andRec]
    refine ⟨fun _ _ _ k => (Nat.not_lt_zero _ k.isLt).elim, ?_⟩
    repeat rw [walkB2_andRec]
    exact ⟨trivial, trivial⟩

/-- The induction applied to the `Bool` block: its table is a sound model of it. -/
theorem boolWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx boolWfT) boolWfT)) σ K Rcic.G2.boolEnv n :=
  envSound_envμR_classG P K boolWfT boolWfT_classG.1 (boolWfT_classG.2 K) σ n

end PSet

end Rcic.F3
