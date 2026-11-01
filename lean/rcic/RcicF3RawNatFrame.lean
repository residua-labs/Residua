import rcic.RcicF3RawFamilyCtor
import rcic.RcicF3RoleNat

/-!
# The raw intersection at the actual admitted Nat descriptor

Nat's empty parameter and index telescopes let one exact stage-one least
fixed point serve as a closed candidate at every universe vector and key.
The comparison is proved at the raw intersection, then transferred to
every actual NatNode. No predecessor invariant or new closure premise is
assumed. This is the Nat component needed by the normalized W fixture;
it is not a universal small-data-frame construction. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RawNatFrame
open Rcic.Declarative PiIndex RawFamily

/-- The actual Nat constructor data, retaining its elimination policy. -/
def data (policy : EliminationPolicy) : FamData :=
  ⟨0, [], [], .succ .zero, [([], []), ([.const 0 []], [])], policy⟩

theorem descriptor (node : NatNode) : famDataOf node.a = data node.a.policy := by
  have hlen : (famDataOf node.a).ctors.length = 2 :=
    (famDataOf_ctors_length node.a).trans
      (node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) node rfl)
  have hctors : (famDataOf node.a).ctors = [([], []), ([.const 0 []], [])] := by
    apply List.ext_getElem
    · exact hlen
    · intro j hj hj'
      let i : Fin node.a.constructors.length :=
        ⟨j, (famDataOf_ctors_length node.a) ▸ hj⟩
      have hget := famDataOf_ctor node.a i
      change (famDataOf node.a).ctors[j]? =
        some ((node.a.constructorViews i).fields,
          (node.a.constructorViews i).resultIndices) at hget
      rw [List.getElem?_eq_getElem hj, (nat_views node i).2.1] at hget
      rcases (nat_views node i).2.2 with ⟨hf, hi⟩ | ⟨hf, hi⟩
      · rw [hf] at hget
        have he : j = 0 := hi
        subst j
        exact Option.some.inj hget
      · rw [hf] at hget
        have he : j = 1 := hi
        subst j
        exact Option.some.inj hget
  change ofFin node.a.constructors.length
    (fun i => ((node.a.constructorViews i).fields,
      (node.a.constructorViews i).resultIndices)) = _ at hctors
  unfold famDataOf data
  rw [node.fam, (nat_family node).1, (nat_family node).2.1,
    (nat_family node).2.2, hctors]

theorem type_read (policy : EliminationPolicy) (σ : Nat → Nat) :
    evalTotal σ (data policy).resLevel ≠ 0 := Nat.one_ne_zero

theorem bounded (policy : EliminationPolicy) : FamBounded (data policy) 0 := by
  constructor
  · intro A hA; exact (List.not_mem_nil A hA).elim
  · intro A hA; exact (List.not_mem_nil A hA).elim
  · rfl
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨fun A hA => (List.not_mem_nil A hA).elim,
        fun A hA => (List.not_mem_nil A hA).elim⟩
    · rw [List.mem_singleton.mp hc]
      exact ⟨fun A hA => by rw [List.mem_singleton.mp hA]; rfl,
        fun A hA => (List.not_mem_nil A hA).elim⟩

theorem nonIR (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) :
    ∀ σ ρ (j : Fin (data policy).ctors.length),
      NonIRSem P μ σ ρ (data policy).fref ((data policy).ctors.get j).1 := by
  intro σ ρ j
  apply nonIRSem_of_kinds
  obtain ⟨j, hj⟩ := j
  change j < 2 at hj
  cases j with
  | zero => intro a b _ hb; exact (Nat.not_lt_zero b hb).elim
  | succ j =>
      have hj0 : j = 0 := by omega
      subst j
      intro a b hab hb
      change b < 1 at hb
      exact (by omega : False).elim

theorem result_tuple (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    {z : PSet.{4}} (hz : z ∈ DStar P μ (data policy) σ ρ) :
    Equiv (resTupF P μ (data policy) σ ρ z) (ordPair pempty (tup [])) := by
  have hp := (DStar_lfp P μ (data policy) σ ρ (type_read policy σ)
    (nonIR P μ policy σ ρ)).1.2.1 z hz
  obtain ⟨i, ⟨j, c, xs, hc, he, hIn⟩, hi⟩ := mem_sep.mp hp
  have hl : xs.length = c.1.length :=
    (Sem.InPhi.length _ (kindsOf (data policy).fref c.1) xs 0 [] hIn).trans
      (List.length_map _ _)
  have hresult := resTupF_dataVal P μ (data policy) σ ρ hc hl (hi.symm.trans he)
  have hc0 : c.2 = [] := by
    have hm := List.getElem?_mem hc
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · rw [List.mem_singleton.mp hm]
  simpa only [hc0, List.map_nil] using hresult

theorem fibre_full (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (fibAt P μ (data policy) (DStar P μ (data policy)) σ ρ [])
      (DStar P μ (data policy) σ ρ) := by
  apply ext; intro z
  constructor
  · exact mem_sep_subset
  · intro hz
    obtain ⟨i, hi⟩ := hz
    exact mem_sep.mpr ⟨i, result_tuple P μ policy σ ρ ⟨i, Equiv.rfl⟩, hi⟩

/-- A constant candidate is allowed at unused keys; raw closure still
requires the exact empty key at every actual constructor conclusion. -/
noncomputable def candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) : Frame :=
  fun _ _ => DStar P μ (data policy) (σOf []) ρ0

theorem candidate_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) : Admissible (data policy) (candidate P μ policy) := by
  intro vs i
  refine ⟨DStar_mem P μ (data policy) (nonIR P μ policy) (σOf []) ρ0, ?_⟩
  rw [if_neg (type_read policy (σOf vs))]
  exact DStar_ne P μ (data policy) (nonIR P μ policy) (σOf []) ρ0

theorem field_read (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (C : Frame) (hC : Admissible (data policy) C)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (Ed (mkM P (table P μ (data policy) C))
      (den (mkM P (table P μ (data policy) C)) σ ρ (.const 0 [])))
      (C [] (key [])) := by
  change Equiv (Ed (mkM P μ) (ofFrame P μ (data policy) C [])) _
  exact apply_ofFrame_ed P μ (data policy) C hC [] [] trivial

theorem zero_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) :
    dataVal 0 [] ∈ DStar P μ (data policy) (σOf []) ρ0 := by
  apply (DStar_lfp P μ (data policy) (σOf []) ρ0 (type_read policy _)
    (nonIR P μ policy _ _)).1.1
  obtain ⟨i, hi⟩ := dataVal_mem_stage (stageW4 P 1) 0 []
    (fun x hx => (List.not_mem_nil x hx).elim)
  exact mem_sep.mpr ⟨i, ⟨0, ([], []), [], rfl, hi, trivial⟩, hi⟩

theorem successor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) {x : PSet.{4}}
    (hx : x ∈ DStar P μ (data policy) (σOf []) ρ0) :
    dataVal 1 [x] ∈ DStar P μ (data policy) (σOf []) ρ0 := by
  have hxW := (stageW4 P 1).trans
    (DStar_mem P μ (data policy) (nonIR P μ policy) (σOf []) ρ0) hx
  have hr : recTupF P μ (data policy) (σOf []) ρ0 [.const 0 []] 0 [] pempty =
      ordPair pempty (tup []) := by
    change cond P.dec (TelFits (mkM P μ) (σOf []) [] ρ0 [])
      (ordPair pempty (tup [])) (singleton pempty) = _
    exact cond_pos trivial _ _
  have hresult : Equiv (resTupF P μ (data policy) (σOf []) ρ0 x)
      (recTupF P μ (data policy) (σOf []) ρ0 [.const 0 []] 0 [] pempty) := by
    rw [hr]
    exact result_tuple P μ policy _ _ hx
  apply (DStar_lfp P μ (data policy) (σOf []) ρ0 (type_read policy _)
    (nonIR P μ policy _ _)).1.1
  obtain ⟨i, hi⟩ := dataVal_mem_stage (stageW4 P 1) 1 [x]
    (fun y hy => (List.mem_singleton.mp hy).symm ▸ hxW)
  exact mem_sep.mpr ⟨i, ⟨1, ([.const 0 []], []), [x], rfl, hi,
    ⟨⟨hx, hresult⟩, trivial⟩⟩, hi⟩

/-- Inversion retains the exact result key and actual recursive value. -/
theorem ctor_cases (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (C : Frame) (hC : Admissible (data policy) C)
    {vs : List Nat} {i : Index.{4}} {z : PSet.{4}}
    (hz : CtorAt P μ (data policy) C vs i z) :
    i = key [] ∧ (Equiv z (dataVal 0 []) ∨
      ∃ x, x ∈ C [] (key []) ∧ Equiv z (dataVal 1 [x])) := by
  obtain ⟨⟨j, hj⟩, ps, xs, hp, hx, _hs, hi, hz⟩ := hz
  have hps : ps = [] := List.eq_nil_of_length_eq_zero hp.length
  subst ps
  rw [if_neg (type_read policy (σOf vs))] at hz
  change j < 2 at hj
  cases j with
  | zero =>
      cases xs with
      | cons x xs => exact False.elim hx
      | nil => exact ⟨hi, Or.inl hz⟩
  | succ j =>
      have hj0 : j = 0 := by omega
      subst j
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
          cases xs with
          | cons y ys => exact False.elim hx.2
          | nil =>
              exact ⟨hi, Or.inr ⟨x,
                mem_congr_right (field_read P μ policy C hC (σOf vs) ρ0) hx.1, hz⟩⟩

theorem candidate_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) : Closed P μ (data policy) (candidate P μ policy) := by
  intro vs i z hz
  obtain ⟨_hi, hz | ⟨x, hx, hz⟩⟩ :=
    ctor_cases P μ policy _ (candidate_admissible P μ policy) hz
  · exact mem_congr_left hz.symm (zero_mem P μ policy)
  · exact mem_congr_left hz.symm (successor_mem P μ policy hx)

theorem raw_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) : Admissible (data policy) (frame P μ (data policy)) :=
  frame_admissible P μ (data policy)
    ⟨candidate P μ policy, candidate_admissible P μ policy, candidate_closed P μ policy⟩

/-- Raw closed frames are prefixed at the canonical child instance and
closed into every root instance, as required by the literal all-vs operator. -/
theorem closed_cross (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (C : Frame) (hC : Admissible (data policy) C)
    (hc : Closed P μ (data policy) C) (vs : List Nat) :
    Sub (PsiF P μ (data policy) (σOf []) ρ0 (C [] (key []))) (C vs (key [])) := by
  intro z hz
  obtain ⟨i, ⟨⟨j, hj⟩, xs, he, hIn⟩, hi⟩ := mem_sep.mp
    (mem_congr_right (PsiF_fin P μ (data policy) (σOf []) ρ0 (C [] (key []))) hz)
  change j < 2 at hj
  cases j with
  | zero =>
      cases xs with
      | cons x xs => exact False.elim hIn
      | nil =>
          apply hc vs (key []) z
          exact ⟨⟨0, by change 0 < 2; decide⟩, [], [], trivial, trivial,
            trivial, rfl, hi.symm.trans he⟩
  | succ j =>
      have hj0 : j = 0 := by omega
      subst j
      cases xs with
      | nil => exact False.elim hIn
      | cons x xs =>
          cases xs with
          | cons y ys => exact False.elim hIn.2
          | nil =>
              have hx : x ∈ C [] (key []) := hIn.1.1
              have hx' := mem_congr_right
                (field_read P μ policy C hC (σOf vs) ρ0).symm hx
              have hs : SmallAlong (mkM P (table P μ (data policy) C)) (σOf vs)
                  (W4 1) [.const 0 []] ρ0 [x] :=
                ⟨mem_congr_left (field_read P μ policy C hC (σOf vs) ρ0).symm
                  (hC [] (key [])).1, trivial⟩
              apply hc vs (key []) z
              exact ⟨⟨1, by change 1 < 2; decide⟩, [], [x], trivial,
                ⟨hx', trivial⟩, hs, rfl, hi.symm.trans he⟩

theorem raw_fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (vs : List Nat) :
    Equiv (frame P μ (data policy) vs (key []))
      (DStar P μ (data policy) (σOf []) ρ0) := by
  apply ext; intro z
  constructor
  · exact frame_least P μ (data policy) (candidate P μ policy)
      (candidate_admissible P μ policy) (candidate_closed P μ policy) vs (key []) z
  · intro hz
    have hall : InAll P μ (data policy) vs (key []) z := by
      intro C hC hc
      have hleast := DStar_least P μ (data policy) (nonIR P μ policy)
        (σOf []) ρ0 (type_read policy _) (closed_cross P μ policy C hC hc [])
      exact closed_cross P μ policy C hC hc vs z
        (PsiF_mono P μ (data policy) (σOf []) ρ0 hleast z
          ((DStar_lfp P μ (data policy) (σOf []) ρ0 (type_read policy _)
            (nonIR P μ policy _ _)).1.2.1 z hz))
    have hw := (stageW4 P 1).trans
      (DStar_mem P μ (data policy) (nonIR P μ policy) (σOf []) ρ0) hz
    obtain ⟨i, hi⟩ := hw
    unfold frame
    rw [if_neg (type_read policy (σOf vs))]
    exact mem_sep.mpr ⟨i, (inAll_resp P μ (data policy) vs (key []) hi.symm).mp hall, hi⟩

theorem raw_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) : Closed P μ (data policy) (frame P μ (data policy)) := by
  intro vs i z hctor
  obtain ⟨hi, hz | ⟨x, hx, hz⟩⟩ := ctor_cases P μ policy _ (raw_admissible P μ policy) hctor
  · subst i
    exact mem_congr_right (raw_fibre P μ policy vs).symm
      (mem_congr_left hz.symm (zero_mem P μ policy))
  · subst i
    exact mem_congr_right (raw_fibre P μ policy vs).symm
      (mem_congr_left hz.symm
        (successor_mem P μ policy (mem_congr_right (raw_fibre P μ policy []) hx)))

theorem of_candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (vs : List Nat) :
    Equiv (ofFrame P μ (data policy) (candidate P μ policy) vs)
      (famKT P μ (data policy) vs) := by
  unfold famKT
  rw [if_neg (type_read policy (σOf vs))]
  change Equiv (tyv (DStar P μ (data policy) (σOf []) ρ0))
    (tyv (fibAt P μ (data policy) (DStar P μ (data policy)) (σOf vs) ρ0 []))
  exact tyv_congr ((DStar_levels P μ (data policy) 0 (nonIR P μ policy)
    (bounded policy) (σ := σOf []) (σ' := σOf vs)
    (fun i hi => (Nat.not_lt_zero i hi).elim) ρ0).trans
      (fibre_full P μ policy (σOf vs) ρ0).symm)

theorem role_value (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (vs : List Nat) :
    Equiv (role P μ (data policy) vs) (famKT P μ (data policy) vs) := by
  refine Equiv.trans ?_ (of_candidate P μ policy vs)
  exact tyv_congr (raw_fibre P μ policy vs)

/-- The comparison is at the actual admitted descriptor, not a selected
alternate family role or an assumed finite-stage equality. -/
theorem role_value_at_node (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (node : NatNode) (vs : List Nat) :
    Equiv (role P μ (famDataOf node.a) vs) (famKT P μ (famDataOf node.a) vs) := by
  rw [descriptor node]
  exact role_value P μ node.a.policy vs

theorem admissible_at_node (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (node : NatNode) : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)) := by
  rw [descriptor node]
  exact raw_admissible P μ node.a.policy

theorem closed_at_node (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (node : NatNode) : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)) := by
  rw [descriptor node]
  exact raw_closed P μ node.a.policy

def numeral : Nat → PSet.{4}
  | 0 => dataVal 0 []
  | n + 1 => dataVal 1 [numeral n]

theorem numeral_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (policy : EliminationPolicy) (n : Nat) (vs : List Nat) :
    numeral n ∈ frame P μ (data policy) vs (key []) := by
  apply mem_congr_right (raw_fibre P μ policy vs).symm
  induction n with
  | zero => exact zero_mem P μ policy
  | succ n ih => exact successor_mem P μ policy ih

theorem zero_ne_one : ¬ Equiv (numeral 0) (numeral 1) := by
  intro h
  have he : 0 = 1 := ord_inj ((tagOf_dataVal 0 []).symm.trans
    ((tagOf_congr h).trans (tagOf_dataVal 1 [numeral 0])))
  exact Nat.noConfusion he

def Witness (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (node : NatNode) : Prop :=
  Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)) ∧
  Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)) ∧
  (∀ vs, Equiv (role P μ (famDataOf node.a) vs) (famKT P μ (famDataOf node.a) vs)) ∧
  (∀ n vs, numeral n ∈ frame P μ (famDataOf node.a) vs (key [])) ∧
  ¬ Equiv (numeral 0) (numeral 1)

theorem component_witness (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (node : NatNode) : Witness P μ node := by
  refine ⟨admissible_at_node P μ node, closed_at_node P μ node,
    role_value_at_node P μ node, ?_, zero_ne_one⟩
  intro n vs
  rw [descriptor node]
  exact numeral_mem P μ node.a.policy n vs

theorem component_nonrefutable (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (node : NatNode) : ¬ (Witness P μ node → (Premises4 → False)) :=
  fun h => h (component_witness P μ node) P

end Rcic.F3.PSet.RawNatFrame
