import rcic.RcicF3PropEvalSafeIndex

/-!
# Nonempty depth-three child domains for the proposed indexed branch fixture

The closed proposition bot is forall Q : Prop, Q. Its decoded domain is
empty in every mkM P mu. A typed map y -> bot therefore makes y empty.
The three domains [y : Prop, n : y -> bot, h : x] have an explicit fitting
tuple when x is trueCode; at every reached y the corresponding child
domain is empty. The original parameter remains in the actual full key.

These semantic facts are independent of admission and interpretation of
the forthcoming family. This file does not assert EnvWfT, BoundGIndexed,
candidate constructor membership, Eval, executable IH membership, or iota.
The companion Branch fixture and evaluator instantiate these facts.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false


namespace Rcic.F3.PSet.IndexedBranchDomain
open Rcic.Declarative PiIndex
open PropEvalSafeIndex (falseCode trueCode)

noncomputable def bot : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- After inserting g, the outer context is [g, x, motive, p]. -/
noncomputable def assignment (p x motive g : PSet.{4}) : Nat → PSet.{4} :=
  vcons g (vcons x (vcons motive (push [p] ρ0)))

noncomputable def domains : List (Expr Nat) :=
  [.sort .zero, .pi (.bvar 0) bot, .bvar 3]

/-- After the three children the context is [h, n, y, g, x, motive, p]. -/
noncomputable def arguments : List (Expr Nat) := [.bvar 6, .bvar 2]

theorem depth : domains.length = 3 := rfl

theorem false_mem_sort (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    falseCode ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (.sort .zero)) :=
  tyv_pempty_mem_sort P μ σ ρ .zero

theorem true_mem_sort (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    trueCode ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (.sort .zero)) := by
  have ht : trueCode ∈ U W4 0 :=
    mem_sImage_tyv.mpr ⟨tv True,
      mem_propSets.mpr (fun _ hz => (mem_tv.mp hz).2), Equiv.rfl⟩
  exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)).symm ht

theorem false_no_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {z : PSet.{4}} (hz : z ∈ Ed (mkM P μ) falseCode) : False :=
  not_mem_pempty (mem_congr_right (ed_tyv_empty (mkM P μ)) hz)

theorem true_proof_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    pempty ∈ Ed (mkM P μ) trueCode :=
  mem_congr_right (ed_tyv (mkM P μ) (dich_tv True)).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

/-- Typed Pi application at falseCode refutes any alleged bottom inhabitant. -/
theorem bot_no_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) {z : PSet.{4}}
    (hz : z ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ bot)) : False := by
  let M := mkM P μ
  have hf : z ∈ Ed M (piVal M (tyv (U W4 0)) (fun q => q)) := hz
  have ha : falseCode ∈ Ed M (tyv (U W4 0)) := false_mem_sort P μ σ ρ
  have hfalse : fapp z falseCode ∈ Ed M falseCode :=
    app_mem M (fun _ _ h => h) hf ha
  exact false_no_mem P μ hfalse

theorem bot_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (Ed (mkM P μ) (den (mkM P μ) σ ρ bot)) pempty :=
  ext fun z => ⟨fun hz => (bot_no_mem P μ σ ρ hz).elim,
    fun hz => (not_mem_pempty hz).elim⟩

/-- This uses the actual membership of the negative proof, not proof erasure. -/
theorem negative_code_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) (y n : PSet.{4})
    (hn : n ∈ Ed (mkM P μ)
      (piVal (mkM P μ) y (fun _ => den (mkM P μ) σ ρ bot))) :
    ∀ z, z ∈ Ed (mkM P μ) y → False := by
  intro z hz
  have hb : fapp n z ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ bot) :=
    app_mem (mkM P μ) (B := fun _ => den (mkM P μ) σ ρ bot)
      (fun _ _ _ => Equiv.rfl) hn hz
  exact bot_no_mem P μ σ ρ hb

/-- The negative proof at the selected false child is constructed vacuously. -/
theorem negative_false_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) :
    pempty ∈ Ed (mkM P μ)
      (piVal (mkM P μ) falseCode (fun _ => den (mkM P μ) σ ρ bot)) := by
  let M := mkM P μ
  have hp : PiProp M falseCode (fun _ => den M σ ρ bot) := by
    intro z hz
    exact (false_no_mem P μ hz).elim
  apply mem_congr_right (ed_piVal_of_prop M hp).symm
  exact mem_tv.mpr ⟨fun z hz => (false_no_mem P μ hz).elim, Equiv.rfl⟩

/-- A fitting, nonempty selected domain of the actual three-binder shape. -/
theorem selected_fits (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (p motive g : PSet.{4}) :
    TelFits (mkM P μ) σ domains (assignment p trueCode motive g)
      [falseCode, pempty, pempty] := by
  refine ⟨false_mem_sort P μ σ _, ?_, true_proof_mem P μ, True.intro⟩
  exact negative_false_mem P μ σ ρ0

/-- Any fitting child at any root index has an empty decoded result index. -/
theorem fitted_child_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p x motive g y n h : PSet.{4})
    (hzs : TelFits (mkM P μ) σ domains (assignment p x motive g) [y, n, h]) :
    ∀ z, z ∈ Ed (mkM P μ) y → False := by
  have hn : n ∈ Ed (mkM P μ)
      (piVal (mkM P μ) y (fun _ => den (mkM P μ) σ ρ0 bot)) := hzs.2.1
  exact negative_code_empty P μ σ ρ0 y n hn

/-- The original fixed parameter and actual recursive index are both retained. -/
theorem arguments_read (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p x motive g y n h : PSet.{4}) :
    arguments.map (den (mkM P μ) σ (push [y, n, h] (assignment p x motive g))) =
      [p, y] := rfl

theorem fitted_arguments (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p x motive g : PSet.{4}) (zs : List PSet.{4})
    (hzs : TelFits (mkM P μ) σ domains (assignment p x motive g) zs) :
    ∃ y, arguments.map (den (mkM P μ) σ (push zs (assignment p x motive g))) =
      [p, y] ∧ ∀ z, z ∈ Ed (mkM P μ) y → False := by
  cases zs with
  | nil => exact hzs.elim
  | cons y ys =>
    cases ys with
    | nil => exact hzs.2.elim
    | cons n ns =>
      cases ns with
      | nil => exact hzs.2.2.elim
      | cons h hs =>
        cases hs with
        | nil => exact ⟨y, rfl, fitted_child_empty P μ σ p x motive g y n h hzs⟩
        | cons q qs => exact hzs.2.2.2.elim

/-- At an empty root index, the third child argument cannot be supplied. -/
theorem no_children_of_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p x motive g : PSet.{4})
    (hx : ∀ z, z ∈ Ed (mkM P μ) x → False) (zs : List PSet.{4}) :
    ¬ TelFits (mkM P μ) σ domains (assignment p x motive g) zs := by
  intro hzs
  cases zs with
  | nil => exact hzs
  | cons y ys =>
    cases ys with
    | nil => exact hzs.2
    | cons n ns =>
      cases ns with
      | nil => exact hzs.2.2
      | cons h hs => exact hx h hzs.2.2.1

theorem leaf_no_children (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p motive g : PSet.{4}) (zs : List PSet.{4}) :
    ¬ TelFits (mkM P μ) σ domains (assignment p falseCode motive g) zs :=
  no_children_of_empty P μ σ p falseCode motive g
    (fun _ hz => false_no_mem P μ hz) zs

theorem child_parent_keys_ne (P : Premises4) (p : PSet.{4}) :
    key [p, falseCode] ≠ key [p, trueCode] := by
  intro he
  have h := (key_eq_iff [p, falseCode] [p, trueCode]).mp he
  exact PropEvalSafeIndex.distinct_codes P h.2.1

/-- Literal semantic component: no admission or evaluation conclusion is hidden. -/
noncomputable def Witness (P : Premises4) : Prop :=
  ∀ (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p motive g : PSet.{4}),
    domains.length = 3 ∧
    Equiv (Ed (mkM P μ) (den (mkM P μ) σ ρ0 bot)) pempty ∧
    TelFits (mkM P μ) σ domains (assignment p trueCode motive g)
      [falseCode, pempty, pempty] ∧
    (∀ zs, ¬ TelFits (mkM P μ) σ domains (assignment p falseCode motive g) zs) ∧
    (∀ zs, TelFits (mkM P μ) σ domains (assignment p trueCode motive g) zs →
      ∃ y, arguments.map
        (den (mkM P μ) σ (push zs (assignment p trueCode motive g))) = [p, y] ∧
        ∀ z, z ∈ Ed (mkM P μ) y → False) ∧
    key [p, falseCode] ≠ key [p, trueCode]

theorem component_witness (P : Premises4) : Witness P := by
  intro μ σ p motive g
  exact ⟨depth, bot_empty P μ σ ρ0, selected_fits P μ σ p motive g,
    leaf_no_children P μ σ p motive g,
    fitted_arguments P μ σ p trueCode motive g, child_parent_keys_ne P p⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

/-- The stored constructor field starts in [x, p], before either insertion. -/
noncomputable def originalAssignment (p x : PSet.{4}) : Nat → PSet.{4} :=
  vcons x (push [p] ρ0)

noncomputable def originalDomains : List (Expr Nat) :=
  [.sort .zero, .pi (.bvar 0) bot, .bvar 2]

noncomputable def originalArguments : List (Expr Nat) := [.bvar 4, .bvar 2]

theorem original_selected_fits (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p : PSet.{4}) :
    TelFits (mkM P μ) σ originalDomains (originalAssignment p trueCode)
      [falseCode, pempty, pempty] := by
  refine ⟨false_mem_sort P μ σ _, ?_, true_proof_mem P μ, True.intro⟩
  exact negative_false_mem P μ σ ρ0

theorem original_child_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p x y n h : PSet.{4})
    (hzs : TelFits (mkM P μ) σ originalDomains (originalAssignment p x) [y, n, h]) :
    ∀ z, z ∈ Ed (mkM P μ) y → False := by
  have hn : n ∈ Ed (mkM P μ)
      (piVal (mkM P μ) y (fun _ => den (mkM P μ) σ ρ0 bot)) := hzs.2.1
  exact negative_code_empty P μ σ ρ0 y n hn

theorem original_arguments_read (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p x y n h : PSet.{4}) :
    originalArguments.map
      (den (mkM P μ) σ (push [y, n, h] (originalAssignment p x))) = [p, y] := rfl

theorem original_no_children_of_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p x : PSet.{4})
    (hx : ∀ z, z ∈ Ed (mkM P μ) x → False) (zs : List PSet.{4}) :
    ¬ TelFits (mkM P μ) σ originalDomains (originalAssignment p x) zs := by
  intro hzs
  cases zs with
  | nil => exact hzs
  | cons y ys =>
    cases ys with
    | nil => exact hzs.2
    | cons n ns =>
      cases ns with
      | nil => exact hzs.2.2
      | cons h hs => exact hx h hzs.2.2.1

noncomputable def OriginalWitness (P : Premises4) : Prop :=
  ∀ (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p : PSet.{4}),
    originalDomains.length = 3 ∧
    TelFits (mkM P μ) σ originalDomains (originalAssignment p trueCode)
      [falseCode, pempty, pempty] ∧
    (∀ zs, ¬ TelFits (mkM P μ) σ originalDomains
      (originalAssignment p falseCode) zs) ∧
    (∀ x y n h, TelFits (mkM P μ) σ originalDomains
      (originalAssignment p x) [y, n, h] →
      originalArguments.map
        (den (mkM P μ) σ (push [y, n, h] (originalAssignment p x))) = [p, y] ∧
      ∀ z, z ∈ Ed (mkM P μ) y → False)

theorem original_witness (P : Premises4) : OriginalWitness P := by
  intro μ σ p
  refine ⟨rfl, original_selected_fits P μ σ p,
    original_no_children_of_empty P μ σ p falseCode
      (fun _ hz => false_no_mem P μ hz), ?_⟩
  intro x y n h hz
  exact ⟨original_arguments_read P μ σ p x y n h,
    original_child_empty P μ σ p x y n h hz⟩

theorem original_nonrefutable (P : Premises4) :
    ¬ (OriginalWitness P → (Premises4 → False)) :=
  fun h => h (original_witness P) P

noncomputable def FullWitness (P : Premises4) : Prop := Witness P ∧ OriginalWitness P

theorem full_witness (P : Premises4) : FullWitness P :=
  ⟨component_witness P, original_witness P⟩

theorem full_nonrefutable (P : Premises4) :
    ¬ (FullWitness P → (Premises4 → False)) :=
  fun h => h (full_witness P) P

end Rcic.F3.PSet.IndexedBranchDomain

#print axioms Rcic.F3.PSet.IndexedBranchDomain.bot_no_mem
#print axioms Rcic.F3.PSet.IndexedBranchDomain.negative_code_empty
#print axioms Rcic.F3.PSet.IndexedBranchDomain.selected_fits
#print axioms Rcic.F3.PSet.IndexedBranchDomain.fitted_arguments
#print axioms Rcic.F3.PSet.IndexedBranchDomain.leaf_no_children
#print axioms Rcic.F3.PSet.IndexedBranchDomain.child_parent_keys_ne
#print axioms Rcic.F3.PSet.IndexedBranchDomain.component_witness
#print axioms Rcic.F3.PSet.IndexedBranchDomain.component_nonrefutable
#print axioms Rcic.F3.PSet.IndexedBranchDomain.original_witness
#print axioms Rcic.F3.PSet.IndexedBranchDomain.original_nonrefutable
#print axioms Rcic.F3.PSet.IndexedBranchDomain.full_witness
#print axioms Rcic.F3.PSet.IndexedBranchDomain.full_nonrefutable
