import rcic.RcicF3PiSmallKeyProducer
import rcic.RcicF3PiSmallRecursiveAttack

/-!
# Decoded-field-dependent complete keys at depth three

The second branch domain depends on the actual first branch value. The
third domain has the proof face. Child keys retain a fixed parameter and
the result of applying the actual encoded field to all three arguments.
The parent key retains the same parameter and the literal data constructor
value. Two inhabited field assignments give different child and parent
keys. No index is replaced by a placeholder.

Both seed constructors retain the exact admitted PendA height-omega value
as an ordinary payload. This is a semantic signature fixture, not an
EnvWfT certificate for the auxiliary signature or a universal data frame.
The existing dependent tuple and recursive compression witness is composed
in Witness. Branch domains are fixed before the recursive fields are
chosen; dependence on earlier recursive outputs remains an open compiler
obligation. The family bound here is W4(k+4), not W4 1, 2, or 3.
closure_claim = 0.
-/
set_option autoImplicit false
noncomputable section
namespace Rcic.F3.PSet.PiSmallKeyProducerAttack
open PiIndex PiSmallKeyProducer

noncomputable def branch0 : PSet.{3} := dataVal 0 []
noncomputable def branch1 : PSet.{3} := dataVal 1 []
noncomputable def domain0 : PSet.{3} := pair branch0 branch1
noncomputable def domain1 (q : FBr domain0) : PSet.{3} :=
  singleton (PiCompile.classValue domain0 q)
noncomputable def domain2 : PSet.{3} := tv True

noncomputable def branchTel : RecTel.{3,5} (List PSet.{4}) 3 :=
  .pi domain0 (fun a => .pi (domain1 a) (fun b => .pi domain2 (fun c =>
    .ret [lift.{3,4} (PiCompile.classValue domain0 a),
      lift.{3,4} (PiCompile.classValue (domain1 a) b),
      lift.{3,4} (PiCompile.classValue domain2 c)])))

theorem domain0_data : ¬ pempty ∈ domain0 := by
  intro h
  rcases mem_pair.mp h with h | h
  · exact dataVal_ne_pempty 0 [] h.symm
  · exact dataVal_ne_pempty 1 [] h.symm

theorem domain1_data (q : FBr domain0) : ¬ pempty ∈ domain1 q := by
  intro h
  exact domain0_data (mem_congr_left (mem_singleton.mp h).symm
    (PiCompile.classValue_mem domain0 q))

theorem branch_domains : branchTel.DomainsDich :=
  ⟨Or.inr domain0_data, fun q => ⟨Or.inr (domain1_data q),
    fun _ => ⟨dich_tv True, fun _ => True.intro⟩⟩⟩

theorem branch_path : Nonempty branchTel.tel.Path := by
  obtain ⟨i, hi⟩ : branch0 ∈ domain0 := mem_pair.mpr (Or.inl Equiv.rfl)
  let a : FBr domain0 := Quotient.mk (FSetoid domain0) i
  obtain ⟨j, hj⟩ : PiCompile.classValue domain0 a ∈ domain1 a :=
    mem_singleton.mpr Equiv.rfl
  let b : FBr (domain1 a) := Quotient.mk (FSetoid (domain1 a)) j
  obtain ⟨k, hk⟩ : pempty ∈ domain2 := mem_tv.mpr ⟨True.intro, Equiv.rfl⟩
  let c : FBr domain2 := Quotient.mk (FSetoid domain2) k
  exact ⟨⟨a, b, c, .unit⟩⟩

theorem branch_values_distinct : ¬ Equiv branch0 branch1 := by
  intro h
  have ht : 0 = 1 := (dataVal_inj rfl h).1
  cases ht

/-- The dependent second domain changes extensionally, not just syntactically. -/
theorem domain_dependency :
    ∃ a b : FBr domain0, ¬ Equiv (domain1 a) (domain1 b) := by
  obtain ⟨i, hi⟩ : branch0 ∈ domain0 := mem_pair.mpr (Or.inl Equiv.rfl)
  obtain ⟨j, hj⟩ : branch1 ∈ domain0 := mem_pair.mpr (Or.inr Equiv.rfl)
  let a : FBr domain0 := Quotient.mk (FSetoid domain0) i
  let b : FBr domain0 := Quotient.mk (FSetoid domain0) j
  have ha : Equiv (PiCompile.classValue domain0 a) branch0 :=
    (PiCompile.classValue_at domain0 i).trans hi
  have hb : Equiv (PiCompile.classValue domain0 b) branch1 :=
    (PiCompile.classValue_at domain0 j).trans hj
  refine ⟨a, b, fun h => ?_⟩
  have he : Equiv (PiCompile.classValue domain0 a)
      (PiCompile.classValue domain0 b) :=
    mem_singleton.mp (mem_congr_right h (mem_singleton.mpr Equiv.rfl))
  exact branch_values_distinct (ha.symm.trans (he.trans hb))

theorem branch_arity (p : branchTel.tel.Path) : (branchTel.result p).length = 3 := rfl

theorem read_flatten (M : Interp.{4}) (f : PSet.{4}) (p : branchTel.tel.Path) :
    branchTel.tel.flatten (PiSmallField.read M branchTel f) p =
      fapps f (branchTel.result p) := rfl

abbrev Shape := ULift.{3} (Option Bool)

@[match_pattern] def Shape.seed0 : Shape := ⟨none⟩
@[match_pattern] def Shape.seed1 : Shape := ⟨some false⟩
@[match_pattern] def Shape.node : Shape := ⟨some true⟩

/-- Three explicit cases using existing small types. -/
noncomputable def Shape.casesOn {motive : Shape → Sort _} (s : Shape)
    (seed0 : motive Shape.seed0) (seed1 : motive Shape.seed1)
    (node : motive Shape.node) : motive s := by
  rcases s with ⟨s⟩
  cases s with
  | none => exact seed0
  | some b => cases b with
    | false => exact seed1
    | true => exact node

def Field : Shape → Type 3
  | Shape.seed0 => ULift.{3} Empty
  | Shape.seed1 => ULift.{3} Empty
  | Shape.node => ULift.{3} Unit

def depth : (s : Shape) → Field s → Nat
  | Shape.seed0, _ => 0
  | Shape.seed1, _ => 0
  | Shape.node, _ => 3

noncomputable def tel : (s : Shape) → (k : Field s) →
    RecTel.{3,5} (List PSet.{4}) (depth s k) :=
  fun s => Shape.casesOn (motive := fun t => (k : Field t) →
      RecTel.{3,5} (List PSet.{4}) (depth t k)) s (fun k => Empty.elim k.down)
    (fun k => Empty.elim k.down) (fun _ => branchTel)

noncomputable def parameter : PSet.{4} := tyv pempty

noncomputable def seed (P : Premises4) (j : Nat) : PSet.{4} :=
  dataVal j [fxZW P]

noncomputable def code (P : Premises4) : (s : Shape) → (Field s → PSet.{4}) → PSet.{4}
  | Shape.seed0, _ => seed P 0
  | Shape.seed1, _ => seed P 1
  | Shape.node, f => dataVal 2 [f ⟨()⟩]

theorem code_congr (P : Premises4) (s : Shape)
    (f g : Field s → PSet.{4}) (h : ∀ k, Equiv (f k) (g k)) :
    Equiv (code P s f) (code P s g) := by
  cases s using Shape.casesOn with
  | seed0 => exact Equiv.rfl
  | seed1 => exact Equiv.rfl
  | node => exact dataVal_congr 2 ⟨h ⟨()⟩, True.intro⟩

noncomputable def signature (P : Premises4) : Sig Index.{4} (List PSet.{4}) where
  Sh := Shape
  Field := Field
  depth := depth
  tel := tel
  child := fun _ f k args => key [parameter, fapps (f k) args]
  out := fun s f => key [parameter, code P s f]
  code := code P
  child_congr := fun _ _ _ h k args =>
    (key_eq_iff _ _).mpr ⟨Equiv.rfl, fapps_congr (h k) args, True.intro⟩
  out_congr := fun s f g h =>
    (key_eq_iff _ _).mpr ⟨Equiv.rfl, code_congr P s f g h, True.intro⟩
  code_congr := code_congr P

theorem code_dich (P : Premises4) : CodeDich (signature P) := by
  apply Or.inr
  intro s f
  cases s using Shape.casesOn with
  | seed0 => exact dataVal_ne_pempty 0 [fxZW P]
  | seed1 => exact dataVal_ne_pempty 1 [fxZW P]
  | node => exact dataVal_ne_pempty 2 [f ⟨()⟩]

theorem domains (P : Premises4) : ∀ s k, ((signature P).tel s k).DomainsDich := by
  intro s k
  cases s using Shape.casesOn with
  | seed0 => exact Empty.elim k.down
  | seed1 => exact Empty.elim k.down
  | node => exact branch_domains

theorem omega_stage_four (P : Premises4) : fxZW P ∈ W4 4 :=
  W4_mono P (by decide) (by decide) (PiSmallTupleAttack.omega_stage_one P)

theorem code_small (P : Premises4) (s : Shape) (f : Field s → PSet.{4})
    (hf : ∀ k, Small.{3,4} (f k)) : Small.{3,4} (code P s f) := by
  apply mem_univIn.{3,4}.mp
  change code P s f ∈ W4 4
  have hW := stage4 P 3
  cases s using Shape.casesOn with
  | seed0 =>
      exact hW.ordPair_mem hW.empty
        (hW.ordPair_mem (ord_mem_stage hW 0)
          (hW.ordPair_mem (omega_stage_four P) hW.empty))
  | seed1 =>
      exact hW.ordPair_mem hW.empty
        (hW.ordPair_mem (ord_mem_stage hW 1)
          (hW.ordPair_mem (omega_stage_four P) hW.empty))
  | node =>
      exact hW.ordPair_mem hW.empty
        (hW.ordPair_mem (ord_mem_stage hW 2)
          (hW.ordPair_mem (mem_univIn.{3,4}.mpr (hf ⟨()⟩)) hW.empty))

noncomputable def model (P : Premises4) : Interp.{4} := PiSmallTupleAttack.model P
noncomputable def X (P : Premises4) : Index.{4} → PSet.{4} :=
  family (model P) (signature P)

theorem seed0_mem (P : Premises4) : seed P 0 ∈ X P (key [parameter, seed P 0]) := by
  let f : Field Shape.seed0 → PSet.{4} := fun k => Empty.elim k.down
  exact produce (model P) P.c3 (signature P) (code_dich P) (domains P)
    Shape.seed0 f (fun k => Empty.elim k.down)

theorem seed1_mem (P : Premises4) : seed P 1 ∈ X P (key [parameter, seed P 1]) := by
  let f : Field Shape.seed1 → PSet.{4} := fun k => Empty.elim k.down
  exact produce (model P) P.c3 (signature P) (code_dich P) (domains P)
    Shape.seed1 f (fun k => Empty.elim k.down)

noncomputable def value (P : Premises4) (z : PSet.{4}) : PSet.{4} :=
  PiSmallField.encode (model P) branchTel (branchTel.tel.unflatten (fun _ => z))

noncomputable def fieldValues (P : Premises4) (z : PSet.{4}) : Field Shape.node → PSet.{4} :=
  fun _ => value P z

noncomputable def node (P : Premises4) (z : PSet.{4}) : PSet.{4} :=
  dataVal 2 [value P z]

theorem value_apply (P : Premises4) (z : PSet.{4}) (p : branchTel.tel.Path) :
    Equiv (fapps (value P z) (branchTel.result p)) z := by
  have h := PiSmallField.read_encode (model P) branchTel branch_domains
    (branchTel.tel.unflatten (fun _ => z)) p
  rw [PiTel.flatten_unflatten] at h
  exact h

theorem child_key (P : Premises4) (z : PSet.{4}) (p : branchTel.tel.Path) :
    (signature P).child Shape.node (fieldValues P z) ⟨()⟩ (branchTel.result p) =
      key [parameter, z] :=
  (key_eq_iff _ _).mpr ⟨Equiv.rfl, value_apply P z p, True.intro⟩

theorem fields_fit (P : Premises4) (z : PSet.{4})
    (hz : z ∈ X P (key [parameter, z])) :
    FieldsFit (model P) (signature P) (X P) Shape.node (fieldValues P z) := by
  intro k
  change value P z ∈ Ed (model P)
    ((PiSmallCompile.widen branchTel).erasedType (model P)
      (fun args => X P (key [parameter, fapps (value P z) args])))
  apply PiSmallField.encode_mem (model P) branchTel branch_domains
    (fun args => X P (key [parameter, fapps (value P z) args]))
    (fun args => family_dich (model P) (signature P) (code_dich P) _)
    (branchTel.tel.unflatten (fun _ => z))
  apply (PiTel.all_iff _ _ _).mpr
  intro p
  rw [PiTel.flatten_unflatten]
  have hk : key [parameter, fapps (value P z) (branchTel.result p)] =
      key [parameter, z] := child_key P z p
  change z ∈ X P (key [parameter, fapps (value P z) (branchTel.result p)])
  rw [hk]
  exact hz

theorem node_mem (P : Premises4) (z : PSet.{4})
    (hz : z ∈ X P (key [parameter, z])) :
    node P z ∈ X P (key [parameter, node P z]) :=
  produce (model P) P.c3 (signature P) (code_dich P) (domains P)
    Shape.node (fieldValues P z) (fields_fit P z hz)

theorem seed_ne (P : Premises4) : ¬ Equiv (seed P 0) (seed P 1) := by
  intro he
  have ht : 0 = 1 := (dataVal_inj rfl he).1
  cases ht

theorem seed_keys_ne (P : Premises4) :
    key [parameter, seed P 0] ≠ key [parameter, seed P 1] := by
  intro h
  exact seed_ne P ((key_eq_iff _ _).mp h).2.1

/-- Both supplied assignments fit, and their child keys differ at every path. -/
theorem child_keys_ne (P : Premises4) (p : branchTel.tel.Path) :
    (signature P).child Shape.node (fieldValues P (seed P 0)) ⟨()⟩ (branchTel.result p) ≠
      (signature P).child Shape.node (fieldValues P (seed P 1)) ⟨()⟩ (branchTel.result p) := by
  rw [child_key P (seed P 0) p, child_key P (seed P 1) p]
  exact seed_keys_ne P

theorem keyed_node_inj {a f g : PSet.{4}}
    (h : key [a, dataVal 2 [f]] = key [a, dataVal 2 [g]]) : Equiv f g := by
  have he : Equiv (dataVal 2 [f]) (dataVal 2 [g]) :=
    ((key_eq_iff [a, dataVal 2 [f]] [a, dataVal 2 [g]]).mp h).2.1
  exact (dataVal_inj (j := 2) (j' := 2) (xs := [f]) (ys := [g]) rfl he).2.1

theorem value_ne_of_ne (P : Premises4) (z z' : PSet.{4})
    (hne : ¬ Equiv z z') : ¬ Equiv (value P z) (value P z') := by
  intro hf
  obtain ⟨p⟩ := branch_path
  exact hne ((value_apply P z p).symm.trans
    ((fapps_congr hf (branchTel.result p)).trans (value_apply P z' p)))

theorem node_keys_ne (P : Premises4) :
    key [parameter, node P (seed P 0)] ≠ key [parameter, node P (seed P 1)] := by
  intro h
  have hf : Equiv (value P (seed P 0)) (value P (seed P 1)) :=
    keyed_node_inj (a := parameter) (f := value P (seed P 0))
      (g := value P (seed P 1)) h
  exact value_ne_of_ne P (seed P 0) (seed P 1) (seed_ne P) hf

theorem seed_payload (P : Premises4) (j : Nat) :
    Equiv (pfst (payload (seed P j))) (fxZW P) :=
  (pfst_congr (payload_dataVal j [fxZW P])).trans pfst_pair

theorem family_component (P : Premises4) :
    Closed (model P) (signature P) (X P) ∧ ∀ i k, X P i ∈ W4 (k + 4) :=
  component P (model P) (signature P) (code_dich P) (domains P) (code_small P)

def Witness (P : Premises4) : Prop :=
  Nonempty branchTel.tel.Path ∧
  (∃ a b : FBr domain0, ¬ Equiv (domain1 a) (domain1 b)) ∧
  (∀ p : branchTel.tel.Path, (branchTel.result p).length = 3) ∧
  Closed (model P) (signature P) (X P) ∧
  (∀ i k, X P i ∈ W4 (k + 4)) ∧
  seed P 0 ∈ X P (key [parameter, seed P 0]) ∧
  seed P 1 ∈ X P (key [parameter, seed P 1]) ∧
  node P (seed P 0) ∈ X P (key [parameter, node P (seed P 0)]) ∧
  node P (seed P 1) ∈ X P (key [parameter, node P (seed P 1)]) ∧
  FieldsFit (model P) (signature P) (X P) Shape.node (fieldValues P (seed P 0)) ∧
  FieldsFit (model P) (signature P) (X P) Shape.node (fieldValues P (seed P 1)) ∧
  (∀ p : branchTel.tel.Path,
    (signature P).child Shape.node (fieldValues P (seed P 0)) ⟨()⟩ (branchTel.result p) =
      key [parameter, seed P 0] ∧
    (signature P).child Shape.node (fieldValues P (seed P 1)) ⟨()⟩ (branchTel.result p) =
      key [parameter, seed P 1] ∧
    (signature P).child Shape.node (fieldValues P (seed P 0)) ⟨()⟩ (branchTel.result p) ≠
      (signature P).child Shape.node (fieldValues P (seed P 1)) ⟨()⟩ (branchTel.result p)) ∧
  key [parameter, node P (seed P 0)] ≠ key [parameter, node P (seed P 1)] ∧
  (∀ j, Equiv (pfst (payload (seed P j))) (fxZW P)) ∧
  PiSmallRecursiveAttack.Witness P

theorem component_witness (P : Premises4) : Witness P :=
  ⟨branch_path, domain_dependency, branch_arity,
    (family_component P).1, (family_component P).2,
    seed0_mem P, seed1_mem P,
    node_mem P (seed P 0) (seed0_mem P), node_mem P (seed P 1) (seed1_mem P),
    fields_fit P (seed P 0) (seed0_mem P), fields_fit P (seed P 1) (seed1_mem P),
    fun p => ⟨child_key P (seed P 0) p, child_key P (seed P 1) p, child_keys_ne P p⟩,
    node_keys_ne P, seed_payload P, PiSmallRecursiveAttack.component_witness P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PiSmallKeyProducerAttack
