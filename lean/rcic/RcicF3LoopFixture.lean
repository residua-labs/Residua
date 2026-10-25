import rcic.RcicF3NatFixture
import rcic.RcicPinLoopEraseWf

/-!
# F3 C: the class contains a recursive `Prop` family with large elimination

`loopWfT` (the admitted `Loop` block of `pinLoopGroupRecWfT`: `Loop : Prop` at 60,
`mk : Loop → Loop` at 61, the recursor into any sort at 62) is in `ClassG`
and in `BoundG K` for every `K` (`loopWfT_classG`), and the induction of
`RcicF3MainG` gives a sound model of it (`loopWfT_envSound`). `mk`'s one
field is a recursive proof, so the fixture exercises the empty-family route
(`propEmpty_of_lim`, `rec_member_sound_empty`, ι's empty case).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Scm.SrcG (sortTyAtC)

namespace PSet

/-- The recursor node of the `Loop` block. -/
abbrev LoopNode := RecNode emptyEnv pinLoopEnvT 60 62 pinLoopRecT

theorem loop_fam (node : LoopNode) : node.a.family.member = pinLoopFamT :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- The family view of the `Loop` block: no parameters, no indices, level 0. -/
theorem loop_family (node : LoopNode) :
    node.a.family.parameters = [] ∧ node.a.family.indices = [] ∧ node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [loop_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

theorem loop_ctor (node : LoopNode) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = pinLoopMkT ∧ i.val = 0 := by
  have hlen : node.a.constructors.length = 1 := node_ctors_length (ctors := [(61, pinLoopMkT)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 1 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- The constructor view of `mk`: no parameters or result indices, the one field `Loop`. -/
theorem loop_view (node : LoopNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [] ∧ (node.a.constructorViews i).resultIndices = [] ∧
      (node.a.constructorViews i).fields = [.const 60 []] := by
  obtain ⟨hP, hI, _⟩ := loop_family node
  have hp : (node.a.constructorViews i).parameters = [] := by
    have := (node.a.constructorViews i).parameterCount
    rw [hP] at this
    exact List.eq_nil_of_length_eq_zero this
  have hr : (node.a.constructorViews i).resultIndices = [] := by
    have := (node.a.constructorViews i).indexCount
    rw [hI] at this
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨hp, hr, ?_⟩
  have hst := (node.a.constructorViews i).storedType
  rw [hp, List.nil_append] at hst
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals 0 (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  have hm : (node.a.constructors[i.val]).mtype = policyPi [.const 60 []] (.const 60 []) := by
    rw [(loop_ctor node i).1]; rfl
  exact (policyPi_split_eq [.const 60 []] _ (.const 60 []) _ (fun _ _ h => Expr.noConfusion h) hne
    (hm.symm.trans hst)).1.symm

/-- `Loop : Prop`, wherever the family is present. -/
def loopConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 60 = some pinLoopFamT) :
    HasTyT E n Γ (.const 60 []) (.sort .zero) :=
  .const Γ 60 [] pinLoopFamT h rfl rfl

/-- One link of an admission chain as a `GroupMembersT` step, with the
leaf's facts read off by projections (so that the step reduces). -/
def chainLink {S : ResolvedEnv} {fuel : Nat} (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
    (rest : List (Nat × CheckedMember)) (E' : ResolvedEnv) (hadm : IndGroupAdmitted E r m)
    (hsort : (sortTyAtC E m.arity fuel [] m.mtype).isSome = true)
    (hleaf : memberAcceptB S E fuel hadm ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1 = true)
    (hrest : GroupMembersT S (extendEnv E r m) rest E') : GroupMembersT S E ((r, m) :: rest) E' :=
  let hl := (Bool.and_eq_true _ _).mp hleaf
  let h1 := (Bool.and_eq_true _ _).mp hl.1
  .cons E r m rest E' hadm.fresh (memberStructB_of h1.1).1 (memberStructB_of h1.1).2.1
    (memberStructB_of h1.1).2.2.1 (memberStructB_of h1.1).2.2.2.1 (memberStructB_of h1.1).2.2.2.2.1
    (memberStructB_of h1.1).2.2.2.2.2 hadm (memberContentB_of hadm hl.2).1
    ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1 ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).2
    (memberScopeB_of h1.2) (memberContentB_of hadm hl.2).2 hrest

/-- The `Loop` block's members, from the admission chain of `pinLoopGroupChain`. -/
def loopMembersT : GroupMembersT pinLoopFamEnvT emptyEnv
    [(60, pinLoopFamT), (61, pinLoopMkT), (62, pinLoopRecT)] pinLoopEnvT :=
  chainLink (fuel := 96) emptyEnv 60 pinLoopFamT _ _ pinLoopFamAdm pinLoopSortB0 pinLoopAccB0
    (chainLink (fuel := 96) pinLoopFamEnvT 61 pinLoopMkT _ _ pinLoopMkAdm pinLoopSortB1 pinLoopAccB1
      (chainLink (fuel := 96) pinLoopPrefixT 62 pinLoopRecT _ _ pinLoopRecAdm pinLoopSortB2 pinLoopAccB2
        (.nil _)))

/-- The admitted `Loop` block's derivation, as its `.group` clause: the
admissions and leaves of `pinLoopGroupRecWfT`, with the group's class facts
read off `groupClassB_of`. -/
def loopWfT : EnvWfT pinLoopEnvT :=
  .group emptyEnv 60 pinLoopFamT [(61, pinLoopMkT)] 62 pinLoopRecT pinLoopEnvT .empty
    (groupClassB_of pinLoopClassB).1 (groupClassB_of pinLoopClassB).2.1 (groupClassB_of pinLoopClassB).2.2
    loopMembersT

/-- The recursive proof field's typing, at level `0`. -/
theorem loop_fields_typed (K : Nat → Nat) (vs : List Nat) (Ps Fs : List (Expr Nat))
    (hP : Ps = []) (hF : Fs = [.const 60 []]) (k : Fin Fs.length) :
    ∃ l : Level, UniformProp l ∧ ∃ d : HasTyT (extendEnv emptyEnv 60 pinLoopFamT) 0
      (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val)) (Fs[k]) (.sort l), LOKt (σOf vs) 4 K d := by
  subst hP; subst hF
  match k with
  | ⟨0, _⟩ => exact ⟨.zero, fun _ => rfl, loopConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩

/-- **The `Loop` block is in the class**, at every instance bound: a `Prop`
family with large elimination whose constructor's field is a recursive proof. -/
theorem loopWfT_classG : ClassG loopWfT ∧ ∀ K, BoundG K loopWfT := by
  refine ⟨⟨trivial, fun node => ⟨fun i => ?_, fun _ _ i k _ => ?_⟩, fun node => ?_⟩,
    fun K => ⟨trivial, fun node i vs _ _ => ?_, ?_, fun node _ _ i vs _ k => ?_⟩⟩
  · rw [(loop_view node i).2.2, (loop_family node).1]
    refine ⟨Or.inr ⟨[], ?_, by rw [(loop_family node).2.1], fun e he => absurd he (List.not_mem_nil _)⟩, trivial⟩
    show Expr.const 60 [] = foldApps (.const 60 ((List.range node.a.family.member.arity).map Level.param)) ([] ++ [])
    rw [loop_fam node]
    rfl
  · rw [(loop_view node i).2.1]
    rfl
  · rw [(loop_family node).1]
    exact ⟨trivial, rfl, rfl, trivial⟩
  · rw [(loop_ctor node i).1]
    exact ⟨_, .pi [] _ _ _ _ (loopConstTyT rfl) (loopConstTyT rfl),
      Nat.zero_le _, Nat.zero_le _,
      fun l hl => absurd hl (List.not_mem_nil _), fun l hl => absurd hl (List.not_mem_nil _)⟩
  · refine ⟨trivial, fun vs _ _ k => ?_, trivial, trivial⟩
    obtain ⟨k, hk⟩ := k
    match k, hk with
    | 0, _ => exact ⟨loopConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩
  · rw [show node.a.family.member.arity = 0 by rw [loop_fam node]; rfl]
    exact loop_fields_typed K vs _ _ (loop_family node).1 (loop_view node i).2.2 k

/-- The induction applied to the `Loop` block: its table is a sound model of it. -/
theorem loopWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx loopWfT) loopWfT)) σ K pinLoopEnvT n :=
  envSound_envμR_classG P K loopWfT loopWfT_classG.1 (loopWfT_classG.2 K) σ n

end PSet

end Rcic.F3
