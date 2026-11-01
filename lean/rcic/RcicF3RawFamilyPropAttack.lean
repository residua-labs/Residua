import rcic.RcicF3RawFamilyProp
import rcic.RcicF3AccEnvT
import rcic.RcicF3KTWPropFix
/-! Replay the literal, fully typed AccR : Prop → Prop descriptor. Its
field is A → AccR A; this is distinct from the semantic Nat.lt fixture.
All sizing and constructor monotonicity inputs are paid. Indexed induction
proves exact fibre truth at every fitting parameter. An independent closed
frame also excludes the inhabited self-loop. No admitted family is refused.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyPropAttack
open Rcic.Declarative PiIndex RawFamily
abbrev fd : FamData := famDataOf accGroupAdmitted

theorem field_read (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Frame) (hC : Admissible fd C) (a : PSet.{4}) (ha : a ∈ U W4 0)
    (vs : List Nat) :
    Equiv (Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) (σOf vs) (push [a] ρ0) accField))
      (tv (∀ x, x ∈ Ed (mkM P μ) a → pempty ∈ C [] (key [a]))) := by
  let M := mkM P (table P μ fd C)
  have hfit : TelFits (mkM P μ) (σOf []) (fd.params ++ fd.indices) ρ0 [a] := by
    refine ⟨?_, trivial⟩
    exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)).symm ha
  have hr : Equiv (Ed M (fapps (ofFrame P μ fd C []) [a])) (C [] (key [a])) :=
    apply_ofFrame_ed P μ fd C hC [] [a] hfit
  have hp : PiProp M a (fun _ => fapps (ofFrame P μ fd C []) [a]) := by
    intro x hx y hy
    have hf := (hC [] (key [a])).2
    change ∀ z, z ∈ C [] (key [a]) → Equiv z pempty at hf
    exact hf y (mem_congr_right hr hy)
  change Equiv (Ed M (piVal M a (fun _ => fapps (table P μ fd C 0 []) [a]))) _
  rw [show table P μ fd C 0 [] = ofFrame P μ fd C [] from upd_eq _ _ _ _]
  refine (ed_piVal_of_prop M hp).trans ?_
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨h, he⟩ := mem_tv.mp hz
    exact mem_tv.mpr ⟨fun x hx => mem_congr_right hr (h x hx), he⟩
  · intro hz
    obtain ⟨h, he⟩ := mem_tv.mp hz
    exact mem_tv.mpr ⟨fun x hx => mem_congr_right hr.symm (h x hx), he⟩

theorem acc_mono (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ConstructorMono P μ fd := by
  intro C D hC hD hsub vs i z hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  have hj : j = ⟨0, by decide⟩ := Fin.ext
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases ps with
  | nil => exact False.elim hp
  | cons a ps =>
    cases ps with
    | cons b bs => exact False.elim hp.2
    | nil =>
      have ha : a ∈ U W4 0 := mem_congr_right
        (ed_tyv (mkM P (table P μ fd C)) (U4_dich 0)) hp.1
      have hpD : TelFits (mkM P (table P μ fd D)) (σOf vs) fd.params ρ0 [a] := by
        refine ⟨?_, trivial⟩
        exact mem_congr_right (ed_tyv (mkM P (table P μ fd D)) (U4_dich 0)).symm ha
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
        cases xs with
        | cons y ys => exact False.elim hx.2
        | nil =>
          have hxC := mem_tv.mp (mem_congr_right (field_read P μ C hC a ha vs) hx.1)
          have hxD : x ∈ Ed (mkM P (table P μ fd D))
              (den (mkM P (table P μ fd D)) (σOf vs) (push [a] ρ0) accField) := by
            exact mem_congr_right (field_read P μ D hD a ha vs).symm
              (mem_tv.mpr ⟨fun y hy => hsub [] (key [a]) _ (hxC.1 y hy), hxC.2⟩)
          exact ⟨⟨0, by decide⟩, [a], [x], hpD, ⟨hxD, trivial⟩, trivial, hi, hz⟩

/-- The generic proof-family construction pays all sizing and positive
closure inputs at the actual fully typed function-recursive Acc descriptor. -/
theorem acc_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Admissible fd (frame P μ fd) ∧ Closed P μ fd (frame P μ fd) := by
  exact ⟨RawFamilyProp.admissible P μ fd (fun _ => rfl),
    RawFamilyProp.closed P μ fd (fun _ => rfl) (acc_mono P μ)⟩

theorem empty_parameter_inhabited (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) : pempty ∈ frame P μ fd vs (key [tyv pempty]) := by
  let C := frame P μ fd
  let M := mkM P (table P μ fd C)
  have hC := (acc_closed P μ).1
  have ha : tyv (pempty : PSet.{4}) ∈ U W4 0 :=
    mem_sImage_tyv.mpr ⟨pempty, mem_propSets.mpr (fun _ h => (not_mem_pempty h).elim), Equiv.rfl⟩
  have hp : TelFits M (σOf vs) fd.params ρ0 [tyv pempty] := by
    refine ⟨?_, trivial⟩
    exact mem_congr_right (ed_tyv M (U4_dich 0)).symm ha
  have hx : pempty ∈ Ed M (den M (σOf vs) (push [tyv pempty] ρ0) accField) := by
    apply mem_congr_right (field_read P μ C hC (tyv pempty) ha vs).symm
    refine mem_tv.mpr ⟨?_, Equiv.rfl⟩
    intro x hx
    exact (not_mem_pempty (mem_congr_right
      (ed_tyv (mkM P μ) (Or.inl (fun _ h => (not_mem_pempty h).elim))) hx)).elim
  apply (acc_closed P μ).2 vs (key [tyv pempty]) pempty
  exact ⟨⟨0, by decide⟩, [tyv pempty], [pempty], hp, ⟨hx, trivial⟩, trivial, rfl, Equiv.rfl⟩

def refusing : Frame := fun _ i => tv (i ≠ key [tyv (tv True)])

theorem refusing_admissible (P : Premises4) : Admissible fd refusing := by
  intro vs i
  exact ⟨(stageW4 P 0).prop_mem (fun _ hz => (mem_tv.mp hz).2),
    fun _ hz => (mem_tv.mp hz).2⟩
theorem refusing_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Closed P μ fd refusing := by
  intro vs i z hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  have hj : j = ⟨0, by decide⟩ := Fin.ext
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases ps with
  | nil => exact False.elim hp
  | cons a ps =>
    cases ps with
    | cons b bs => exact False.elim hp.2
    | nil =>
      have ha : a ∈ U W4 0 := mem_congr_right
        (ed_tyv (mkM P (table P μ fd refusing)) (U4_dich 0)) hp.1
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
        cases xs with
        | cons y ys => exact False.elim hx.2
        | nil =>
          have hxC := mem_tv.mp (mem_congr_right
            (field_read P μ refusing (refusing_admissible P) a ha vs) hx.1)
          change i = key [a] at hi
          rw [hi]
          apply mem_tv.mpr
          refine ⟨?_, hz⟩
          intro he
          have ea : Equiv a (tyv (tv True)) := ((key_eq_iff _ _).mp he).1
          have hpa : pempty ∈ Ed (mkM P μ) a :=
            mem_congr_right (ed_congr (mkM P μ) ea).symm
              (mem_congr_right (ed_tyv (mkM P μ) (dich_tv True)).symm
                (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩))
          exact (mem_tv.mp (hxC.1 pempty hpa)).1 he
theorem self_loop_refused (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) : ¬ pempty ∈ frame P μ fd vs (key [tyv (tv True)]) := by
  intro hz
  have hr := frame_least P μ fd refusing (refusing_admissible P)
    (refusing_closed P μ) vs (key [tyv (tv True)]) pempty hz
  exact (mem_tv.mp hr).1 rfl
theorem parameter_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∀ vs i z, z ∈ frame P μ fd vs i →
      ∀ a, key [a] = i → ∀ x, x ∈ Ed (mkM P μ) a → False := by
  let C := frame P μ fd
  let Q := fun (_ : List Nat) (i : Index.{4}) (_ : PSet.{4}) =>
    ∀ a, key [a] = i → ∀ x, x ∈ Ed (mkM P μ) a → False
  apply frame_induction P μ fd (acc_closed P μ).1 (acc_closed P μ).2
    (acc_mono P μ) Q (fun _ _ _ _ _ h => h)
  intro vs i z hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  have hj : j = ⟨0, by decide⟩ := Fin.ext
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases ps with
  | nil => exact False.elim hp
  | cons a ps =>
    cases ps with
    | cons b bs => exact False.elim hp.2
    | nil =>
      have ha : a ∈ U W4 0 := mem_congr_right
        (ed_tyv (mkM P (table P μ fd (restrict C Q))) (U4_dich 0)) hp.1
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
        cases xs with
        | cons y ys => exact False.elim hx.2
        | nil =>
          have hxC := mem_tv.mp (mem_congr_right
            (field_read P μ (restrict C Q)
              (restrict_admissible P fd C (acc_closed P μ).1 Q) a ha vs) hx.1)
          change i = key [a] at hi
          intro b hb y hy
          have he : Equiv b a := ((key_eq_iff _ _).mp (hb.trans hi)).1
          have hya : y ∈ Ed (mkM P μ) a := mem_congr_right (ed_congr _ he) hy
          obtain ⟨_, hQ, _⟩ := mem_sep.mp (hxC.1 y hya)
          exact hQ a rfl y hya
theorem parameter_exact (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) (a : PSet.{4}) (ha : a ∈ U W4 0) :
    pempty ∈ frame P μ fd vs (key [a]) ↔ ∀ x, x ∈ Ed (mkM P μ) a → False := by
  constructor
  · intro hz
    exact parameter_empty P μ vs (key [a]) pempty hz a rfl
  · intro hempty
    let C := frame P μ fd
    let M := mkM P (table P μ fd C)
    have hp : TelFits M (σOf vs) fd.params ρ0 [a] := by
      refine ⟨?_, trivial⟩
      exact mem_congr_right (ed_tyv M (U4_dich 0)).symm ha
    have hx : pempty ∈ Ed M (den M (σOf vs) (push [a] ρ0) accField) := by
      apply mem_congr_right (field_read P μ C (acc_closed P μ).1 a ha vs).symm
      exact mem_tv.mpr ⟨fun x hx => (hempty x hx).elim, Equiv.rfl⟩
    exact (acc_closed P μ).2 vs (key [a]) pempty
      ⟨⟨0, by decide⟩, [a], [pempty], hp, ⟨hx, trivial⟩, trivial, rfl, Equiv.rfl⟩
end Rcic.F3.PSet.RawFamilyPropAttack
