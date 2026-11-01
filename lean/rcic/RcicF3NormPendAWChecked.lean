import rcic.RcicF3NormPendAWInvariant
import rcic.RcicF3StepWDApex

/-!
# Both exact checks at the sound normalized PendA W environment

The W check accepts the actual Nat/W admission chain because both walks
have their original parameter cuts. The D check is characterized exactly
by its four constructor-to-recursor bound inequalities. Every constant
bound therefore passes both executable checks and the existing BoundG /
BoundDG premises at this same environment.

The composition retains the produced normalized invariant, installed-table
soundness, and actual height-omega family element. A nonconstant bound is
also exhibited for which D refuses this environment despite its repaired
invariant; acceptance is not asserted for every bound.

This is a fixture certificate. Universal StepAG, the checked apex, and its
distinguished False-prefix conditions are not produced here. The literal
legacy iota scope of the retained invariant is unchanged. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAWChecked
open Rcic.Declarative Rcic.Model.PS
open Rcic.F3.StepWCheck Rcic.F3.StepDGOrder

theorem nat_w_checked : EnvWChecked natEnvUWfT := by
  refine ⟨trivial, ?_⟩
  intro node hW _ _
  exact False.elim (hW (natEnvUWfT_classG.1.2.2 node))

theorem w_checked : EnvWChecked PendAWGroup.wft := by
  refine ⟨nat_w_checked, ?_⟩
  intro node hW _ _
  exact False.elim (hW (PendAWGroup.walkClass node))

theorem w_check : Rcic.F3.StepWApex.envCheck PendAWGroup.wft = true :=
  (Rcic.F3.StepWApex.envCheck_pass_iff PendAWGroup.wft).mpr w_checked

/-- The D conditions at every actual Nat node, including the selected one. -/
theorem nat_d_side_iff (K : Nat → Nat) (node : NatNode) :
    StepDGSide K node ↔ K 1 ≤ K 3 ∧ K 2 ≤ K 3 := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) node rfl
  constructor
  · intro h
    exact ⟨h.2.2 ⟨0, by rw [hlen]; decide⟩,
      h.2.2 ⟨1, by rw [hlen]; decide⟩⟩
  · intro h
    refine ⟨fun i => (nat_views node i).1.trans (nat_family node).1.symm, ?_, ?_⟩
    · intro hu
      rw [(nat_family node).2.2] at hu
      exact False.elim (Nat.noConfusion (hu (fun _ => 0)))
    · intro i
      rcases nat_ctor node i with ⟨_, hi⟩ | ⟨_, hi⟩
      · change K (0 + 1 + i.val) ≤ K 3
        rw [hi]
        exact h.1
      · change K (0 + 1 + i.val) ≤ K 3
        rw [hi]
        exact h.2

/-- The higher-order W field is retained; D's Prop/anySort corner is vacuous
because the actual result universe is Type, independently of its policy. -/
theorem w_d_side_iff (K : Nat → Nat) (node : PendAWGroup.Node) :
    StepDGSide K node ↔ K 5 ≤ K 7 ∧ K 6 ≤ K 7 := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) node rfl
  constructor
  · intro h
    exact ⟨h.2.2 ⟨0, by rw [hlen]; decide⟩,
      h.2.2 ⟨1, by rw [hlen]; decide⟩⟩
  · intro h
    refine ⟨fun i => (PendAWGroup.views node i).1.trans
      (PendAWGroup.familyInfo node).1.symm, ?_, ?_⟩
    · intro hu
      rw [(PendAWGroup.familyInfo node).2.2] at hu
      exact False.elim (Nat.noConfusion (hu (fun _ => 0)))
    · intro i
      rcases PendAWGroup.ctorInfo node i with ⟨_, hi⟩ | ⟨_, hi⟩
      · change K (4 + 1 + i.val) ≤ K 7
        rw [hi]
        exact h.1
      · change K (4 + 1 + i.val) ≤ K 7
        rw [hi]
        exact h.2

/-- Exact acceptance for the whole admission chain, not just its last group. -/
theorem d_check_iff (K : Nat → Nat) :
    Rcic.F3.StepWDApex.envCheck K PendAWGroup.wft = true ↔
      (K 1 ≤ K 3 ∧ K 2 ≤ K 3) ∧ (K 5 ≤ K 7 ∧ K 6 ≤ K 7) := by
  apply Iff.trans (Rcic.F3.StepWDApex.envCheck_pass_iff K PendAWGroup.wft)
  constructor
  · intro h
    exact ⟨(nat_d_side_iff K _).mp h.1.2, (w_d_side_iff K _).mp h.2⟩
  · intro h
    exact ⟨⟨trivial, (nat_d_side_iff K _).mpr h.1⟩,
      (w_d_side_iff K _).mpr h.2⟩

theorem d_check (k : Nat) :
    Rcic.F3.StepWDApex.envCheck (fun _ => k) PendAWGroup.wft = true :=
  (d_check_iff (fun _ => k)).mpr
    ⟨⟨Nat.le_refl k, Nat.le_refl k⟩, ⟨Nat.le_refl k, Nat.le_refl k⟩⟩

theorem axiom_free : AxiomFreeEnv' PendAW.eAll := by
  intro r m hm
  rcases groupMembersT_cases PendAW.membersT r m hm with hbase | hnew
  · rcases groupMembersT_cases natMembersT r m hbase with hempty | hnat
    · cases hempty
    · simp only [List.cons_append, List.nil_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hnat
      rcases hnat with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        exact fun h => MemberClass.noConfusion h
  · change (r, m) ∈ [(4, PendAW.fam), (5, PendAW.leaf),
      (6, PendAW.node), (7, PendAW.recMem)] at hnew
    simp only [List.cons_append, List.nil_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hnew
    rcases hnew with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      exact fun h => MemberClass.noConfusion h

/-- Soundness of this same installed table, at every semantic valuation. -/
theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (NormPendAW.table P)) σ K PendAW.eAll n := by
  have h := NormPendAWInvariant.actual_invariant P K
  exact envSound_of P (Efin := PendAW.eAll) (fun _ _ hm => hm) h.1
    (fun r m hm hk => h.2 PendAW.eAll (fun _ _ hm => hm) r m hm hk) σ n

/-- The check remains conservative even at this now-sound fixture. -/
def refusedBound (r : Nat) : Nat := if r = 5 then 1 else 0

theorem d_check_refuses :
    Rcic.F3.StepWDApex.envCheck refusedBound PendAWGroup.wft = false := by
  apply Bool.of_not_eq_true
  intro hp
  have h := ((d_check_iff refusedBound).mp hp).2.1
  change 1 ≤ 0 at h
  exact Nat.not_succ_le_zero 0 h

def Witness (P : Premises4) : Prop :=
  NormPendAWInvariant.Witness P ∧
  AxiomFreeEnv' PendAW.eAll ∧
  Rcic.F3.StepWApex.envCheck PendAWGroup.wft = true ∧
  (∀ k, Rcic.F3.StepWDApex.envCheck (fun _ => k) PendAWGroup.wft = true ∧
    BoundG (fun _ => k) PendAWGroup.wft ∧ BoundDG (fun _ => k) PendAWGroup.wft) ∧
  (∀ K σ n, EnvSound (mkM P (NormPendAW.table P)) σ K PendAW.eAll n) ∧
  Rcic.F3.StepWDApex.envCheck refusedBound PendAWGroup.wft = false

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPendAWInvariant.component_witness P, axiom_free, w_check,
    fun k => ⟨d_check k, PendAWGroup.boundG _, PendAWGroup.boundDG k⟩,
    env_sound P, d_check_refuses⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPendAWChecked
