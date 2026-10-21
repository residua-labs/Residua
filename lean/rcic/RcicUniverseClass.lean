import rcic.RcicSortLevelBridge
import rcic.RcicLevelCalc

namespace Rcic.Declarative

/-!
Spec05 family universe classification. The executable tests already live
in RcicLevelZero and RcicLevelDec; this module supplies their extensional
classification interface, including the genuinely separate Mixed case.
No bounded collection of probes is assumed complete: completeness is
proved from the level algebra and the existing exact zero theorem.
-/

def UniformProp (l : Level) : Prop :=
  ∀ ν : Nat → Nat, evalTotal ν l = 0

def UniformType (l : Level) : Prop :=
  ∀ ν : Nat → Nat, 0 < evalTotal ν l

def MixedUniverse (l : Level) : Prop :=
  ¬ UniformProp l ∧ ¬ UniformType l

abbrev levelUniformZero := levelIsZero
abbrev levelUniformPositive := levelNeverZero

theorem uniformProp_iff_eqN_zero (l : Level) :
    UniformProp l ↔ eqN l .zero :=
  evalTotal_eq_iff_eqN l .zero

theorem uniformProp_eqN_zero {l : Level} (h : UniformProp l) :
    eqN l .zero := (uniformProp_iff_eqN_zero l).mp h

theorem levelUniformZero_iff (l : Level) :
    levelUniformZero l = true ↔ UniformProp l :=
  (levelIsZero_iff l).trans (uniformProp_iff_eqN_zero l).symm

theorem levelUniformPositive_iff (l : Level) :
    levelUniformPositive l = true ↔ UniformType l := by
  constructor
  · intro h ν
    apply Nat.pos_of_ne_zero
    intro hz
    exact levelNeverZero_not_zero l (fun i => some (ν i)) h
      ((eval_total ν l).trans (congrArg some hz))
  · intro h
    cases hb : levelNeverZero l with
    | true => exact hb
    | false =>
        have hz := neverZero_false_evalTotal0 l hb
        have hp := h (fun _ => 0)
        rw [hz] at hp
        exact False.elim (Nat.lt_irrefl 0 hp)

theorem uniformType_iff_leN_one (l : Level) :
    UniformType l ↔ leN (.succ .zero) l := by
  constructor
  · intro h ρ x y hx hy
    have hx1 : x = 1 := (Option.some.inj hx).symm
    subst x
    have hb := (levelUniformPositive_iff l).mpr h
    apply Nat.pos_of_ne_zero
    intro hz
    exact levelNeverZero_not_zero l ρ hb (hy.trans (congrArg some hz))
  · intro h ν
    exact h (fun i => some (ν i)) 1 (evalTotal ν l) rfl (eval_total ν l)

theorem uniformProp_not_uniformType {l : Level} (h : UniformProp l) :
    ¬ UniformType l := by
  intro hp
  have hp0 := hp (fun _ => 0)
  rw [h (fun _ => 0)] at hp0
  exact Nat.lt_irrefl 0 hp0

inductive UniverseClass where
  | uniformProp
  | uniformType
  | mixed
  deriving DecidableEq, Repr

def classifyUniverse (l : Level) : UniverseClass :=
  if levelUniformZero l then .uniformProp
  else if levelUniformPositive l then .uniformType
  else .mixed

theorem classifyUniverse_uniformProp_iff (l : Level) :
    classifyUniverse l = .uniformProp ↔ UniformProp l := by
  constructor
  · intro h
    cases hz : levelUniformZero l with
    | true => exact (levelUniformZero_iff l).mp hz
    | false =>
        cases hp : levelUniformPositive l <;>
          simp only [classifyUniverse, hz, hp, Bool.false_eq_true, Bool.true_eq,
            ↓reduceIte] at h <;> cases h
  · intro h
    have hz := (levelUniformZero_iff l).mpr h
    simp only [classifyUniverse, hz, Bool.true_eq, ↓reduceIte]

theorem classifyUniverse_uniformType_iff (l : Level) :
    classifyUniverse l = .uniformType ↔ UniformType l := by
  constructor
  · intro h
    cases hz : levelUniformZero l with
    | true =>
        simp only [classifyUniverse, hz, Bool.true_eq, ↓reduceIte] at h
        cases h
    | false =>
        cases hp : levelUniformPositive l with
        | true => exact (levelUniformPositive_iff l).mp hp
        | false =>
            simp only [classifyUniverse, hz, hp, Bool.false_eq_true, ↓reduceIte] at h
            cases h
  · intro h
    have hp := (levelUniformPositive_iff l).mpr h
    have hz : levelUniformZero l = false := by
      cases hz : levelUniformZero l with
      | false => rfl
      | true =>
          exact False.elim
            (uniformProp_not_uniformType ((levelUniformZero_iff l).mp hz) h)
    simp only [classifyUniverse, hz, hp, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]

theorem classifyUniverse_mixed_iff (l : Level) :
    classifyUniverse l = .mixed ↔ MixedUniverse l := by
  constructor
  · intro h
    constructor
    · intro hp
      have he := (classifyUniverse_uniformProp_iff l).mpr hp
      rw [h] at he
      cases he
    · intro ht
      have he := (classifyUniverse_uniformType_iff l).mpr ht
      rw [h] at he
      cases he
  · intro h
    cases hc : classifyUniverse l with
    | mixed => rfl
    | uniformProp =>
        exact False.elim (h.1 ((classifyUniverse_uniformProp_iff l).mp hc))
    | uniformType =>
        exact False.elim (h.2 ((classifyUniverse_uniformType_iff l).mp hc))

/-- All-one evaluation is a complete zero test for this level algebra. -/
theorem levelUniformZero_of_evalTotal_one_zero (l : Level)
    (h : evalTotal (fun _ => 1) l = 0) : levelUniformZero l = true := by
  induction l with
  | zero => rfl
  | succ l _ => exact False.elim (Nat.succ_ne_zero _ h)
  | max a b iha ihb =>
      have ha : evalTotal (fun _ => 1) a = 0 :=
        Nat.le_zero.mp (h ▸ Nat.le_max_left _ _)
      have hb : evalTotal (fun _ => 1) b = 0 :=
        Nat.le_zero.mp (h ▸ Nat.le_max_right _ _)
      exact Bool.and_eq_true_iff.mpr ⟨iha ha, ihb hb⟩
  | imax a b _ ihb =>
      have he : eval (fun _ => some 1) (.imax a b) = some 0 :=
        (eval_total (fun _ => 1) (.imax a b)).trans (congrArg some h)
      have hb := (eval_imax_eq_zero (fun _ => some 1) a b).mp he
      exact ihb (Option.some.inj ((eval_total (fun _ => 1) b).symm.trans hb))
  | param i => exact False.elim (Nat.one_ne_zero h)

/-- Mixed has explicit separating valuations; it is not the complement
of UniformProp relabeled as UniformType. -/
theorem mixedUniverse_witnesses {l : Level} (h : MixedUniverse l) :
    evalTotal (fun _ => 0) l = 0 ∧ 0 < evalTotal (fun _ => 1) l := by
  constructor
  · have hb : levelNeverZero l = false := by
      cases hb : levelNeverZero l with
      | false => rfl
      | true => exact False.elim (h.2 ((levelUniformPositive_iff l).mp hb))
    exact neverZero_false_evalTotal0 l hb
  · apply Nat.pos_of_ne_zero
    intro hz
    exact h.1 ((levelUniformZero_iff l).mp
      (levelUniformZero_of_evalTotal_one_zero l hz))

theorem evalTotal_instLevel (ls : List Level) (ν : Nat → Nat) (l : Level) :
    evalTotal ν (instLevel ls l) =
      evalTotal (fun i => evalTotal ν ((ls[i]?).getD (.param i))) l := by
  apply Option.some.inj
  calc
    some (evalTotal ν (instLevel ls l)) =
        eval (fun i => some (ν i)) (instLevel ls l) := (eval_total ν _).symm
    _ = eval (fun i => eval (fun j => some (ν j)) ((ls[i]?).getD (.param i))) l :=
      eval_instLevel ls (fun i => some (ν i)) l
    _ = eval (fun i => some (evalTotal ν ((ls[i]?).getD (.param i)))) l :=
      eval_congr_val (fun i => eval_total ν ((ls[i]?).getD (.param i))) l
    _ = some (evalTotal (fun i => evalTotal ν ((ls[i]?).getD (.param i))) l) :=
      eval_total _ l

theorem uniformProp_instLevel {l : Level} (h : UniformProp l) (ls : List Level) :
    UniformProp (instLevel ls l) := by
  intro ν
  rw [evalTotal_instLevel]
  exact h _

theorem uniformType_instLevel {l : Level} (h : UniformType l) (ls : List Level) :
    UniformType (instLevel ls l) := by
  intro ν
  rw [evalTotal_instLevel]
  exact h _

end Rcic.Declarative
