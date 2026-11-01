import rcic.RcicF3RecFieldOriginSyntax
import rcic.RcicF3PiGraphInversionAttack

/-!
# Actual W lookup and application through the origin producer

An inhabited branch argument is added to the previous actual W field
context. The stored higher-order field is looked up at its complete type,
then applied by the literal bounded application rule. Both original
contexts fit, the generic lookup produces depth-one Origin, and the generic
typed application produces depth-zero Origin at the unchanged family key.

The application result is an actual nonempty DATA member. A separate empty
domain supplies an inhabited equality/erasure case for the separator. The
earlier beta-converted Pi and height-omega components are all retained.
These remain auxiliary local judgments in the admitted W prefix; this is
not a producer of all normalized tuple masks. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldOriginAttack
open Rcic.Declarative RawFamily PiIndex RecFieldOrigin
open NormFreshHeadAttack (base C D model parameter σ admissible_C admissible_D prefix_sound)
open PendAWBridge (fd)

def Γ : LCtx := .assumption (.bvar 3) :: RecFieldConsumerAttack.Γ
noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons (ord 1) (RecFieldConsumerAttack.ρ P)
def field : Expr Nat := RecFieldConsumerAttack.fieldAt 4
def body : Expr Nat := .app (.const 4 []) (.bvar 5)
def resultType : Expr Nat := .app (.const 4 []) (.bvar 4)
def term : Expr Nat := .app (.bvar 3) (.bvar 0)

noncomputable def context_typed : CtxWfT PendAW.eFam 0 Γ :=
  .assumption RecFieldConsumerAttack.Γ (.bvar 3) (.succ .zero)
    RecFieldConsumerAttack.context_wf (.bvar _ 3 _ rfl)
noncomputable def head_typed : HasTyT PendAW.eFam 0 Γ (.bvar 3) field :=
  .bvar Γ 3 field rfl
noncomputable def argument_typed : HasTyT PendAW.eFam 0 Γ (.bvar 0) (.bvar 4) :=
  .bvar Γ 0 (.bvar 4) rfl
noncomputable def application_typed : HasTyT PendAW.eFam 0 Γ term resultType :=
  .app Γ (.bvar 3) (.bvar 0) (.bvar 4) body head_typed argument_typed

theorem application_bound (K : Nat → Nat) : LOKt σ 4 K application_typed :=
  ⟨True.intro, True.intro⟩

theorem argument_mem (P : Premises4) (X : Frame) :
    ord 1 ∈ Ed (model P X) parameter := by
  have hdom : Equiv (Ed (model P X) parameter) (fxDomBig P) := by
    rw [fx_domBig_eq P]
    exact (ed_tyv (model P X) fx_dich).trans el_tyv.symm
  exact mem_congr_right hdom.symm (PiGraphInversionAttack.argument_mem P)

theorem contexts_fit (P : Premises4) :
    Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) :=
  ⟨⟨(RecFieldConsumerAttack.contexts_fit P).1, argument_mem P (C P)⟩,
    ⟨(RecFieldConsumerAttack.contexts_fit P).2, argument_mem P (D P)⟩⟩

theorem reader : piTelescopeFuel PendAW.eFam 16 field =
    some ([.bvar 4], foldApps (.const 4 (canonL 0)) [.bvar 5]) := rfl

theorem instances (K : Nat → Nat) : InstOK PendAW.eFam σ K field := by
  intro r ls hr
  change (r, ls) ∈ ([] ++ ([(4, [])] ++ [])) at hr
  simp only [List.nil_append, List.append_nil] at hr
  cases List.mem_singleton.mp hr
  exact ⟨PendAW.fam, rfl, rfl, fun _ h => (List.not_mem_nil _ h).elim⟩

theorem lookup_origin (P : Premises4) (K : Nat → Nat) :
    Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) field))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) field))
      (RawFamilyIHBuilderAttack.x P) := by
  exact RecFieldOriginSyntax.lookup P (base P) fd (C P) (admissible_C P) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    (RecFieldConsumerAttack.bodies K) (ρ P) (contexts_fit P).1 (contexts_fit P).2
    3 field rfl 0 16 [.bvar 4] [.bvar 5] reader (instances K)
    (by intro e he; cases List.mem_singleton.mp he; rfl)
    (by intro e he; cases List.mem_singleton.mp he; rfl) rfl
    (by change 1 ≠ 0; decide)

/-- This invocation pays all application memberships from the actual
two bounded typing premises; no semantic continuation is supplied. -/
theorem application_origin (P : Premises4) (K : Nat → Nat) :
    Origin (mkM P (base P)) fd (C P) 0
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) resultType))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) resultType))
      (den (model P (C P)) σ (ρ P) term) :=
  RecFieldOriginSyntax.typed_application P (base P) fd (C P) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    (ρ P) (contexts_fit P).1 (contexts_fit P).2
    (.bvar 3) (.bvar 0) (.bvar 4) body rfl rfl
    head_typed True.intro argument_typed True.intro 1 (lookup_origin P K)

theorem result_mem (P : Premises4) (K : Nat → Nat) :
    den (model P (C P)) σ (ρ P) term ∈
      Ed (model P (C P)) (den (model P (C P)) σ (ρ P) resultType) :=
  sound_ty (P.good _ rfl) (prefix_sound P (C P) (admissible_C P) σ K 0)
    application_typed (application_bound K) (ρ P) (contexts_fit P).1

theorem result_nonempty (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (den (model P (C P)) σ (ρ P) term) pempty := by
  have he := RawFamilyEnlarge.application_read P (base P) fd (C P) (admissible_C P)
    0 σ (ρ P) [.bvar 4]
    (by intro e h; cases List.mem_singleton.mp h; rfl)
    (PendAWBridge.argsFit P (base P) pempty)
  have hx : den (model P (C P)) σ (ρ P) term ∈ C P [] (key [parameter]) :=
    mem_congr_right he (result_mem P K)
  have hd := (admissible_C P [] (key [parameter])).2
  change ∀ z, z ∈ C P [] (key [parameter]) → ¬ Equiv z pempty at hd
  exact hd _ hx

/-- An empty recursive domain gives a genuine source/target type equality.
The separator is invoked with both membership and equality inhabited. -/
theorem empty_separator (P : Premises4) :
    let M := mkM P (base P)
    let B := fun _ : PSet.{4} => tyv (C P [] (key [parameter]))
    let B' := fun _ : PSet.{4} => tyv (D P [] (key [parameter]))
    let S := Ed M (piVal M (tyv pempty) B)
    let T := Ed M (piVal M (tyv pempty) B')
    Origin M fd (C P) 1 S T pempty ∧ pempty ∈ S ∧ Equiv S T ∧
      Equiv (pempty : PSet.{4}) pempty := by
  dsimp only
  let M := mkM P (base P)
  let B := fun _ : PSet.{4} => tyv (C P [] (key [parameter]))
  let B' := fun _ : PSet.{4} => tyv (D P [] (key [parameter]))
  have hnone : ∀ a, a ∈ Ed M (tyv pempty) → False := by
    intro a ha
    exact not_mem_pempty (mem_congr_right (ed_tyv M
      (Or.inl (fun _ h => (not_mem_pempty h).elim))) ha)
  have hp : PiProp M (tyv pempty) B := fun a ha => (hnone a ha).elim
  have hp' : PiProp M (tyv pempty) B' := fun a ha => (hnone a ha).elim
  have eS := ed_piVal_of_prop M hp
  have eT := ed_piVal_of_prop M hp'
  have ht : (∀ a, a ∈ Ed M (tyv pempty) → pempty ∈ Ed M (B a)) :=
    fun a ha => (hnone a ha).elim
  have ht' : (∀ a, a ∈ Ed M (tyv pempty) → pempty ∈ Ed M (B' a)) :=
    fun a ha => (hnone a ha).elim
  have htv : Equiv (tv (∀ a, a ∈ Ed M (tyv pempty) → pempty ∈ Ed M (B a)))
      (tv (∀ a, a ∈ Ed M (tyv pempty) → pempty ∈ Ed M (B' a))) :=
    ext fun z => ⟨fun hz => mem_tv.mpr ⟨ht', (mem_tv.mp hz).2⟩,
      fun hz => mem_tv.mpr ⟨ht, (mem_tv.mp hz).2⟩⟩
  have he := eS.trans (htv.trans eT.symm)
  have hz := mem_congr_right eS.symm (mem_tv.mpr ⟨ht, Equiv.rfl⟩)
  have ho : Origin M fd (C P) 1
      (Ed M (piVal M (tyv pempty) B)) (Ed M (piVal M (tyv pempty) B')) pempty :=
    .pi (tyv pempty) B B' (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl)
      Equiv.rfl Equiv.rfl (fun a ha => (hnone a ha).elim)
  exact ⟨ho, hz, he, separator ho hz he⟩

def Witness (P : Premises4) : Prop :=
  PiGraphInversionAttack.Witness P ∧
  Nonempty (CtxWfT PendAW.eFam 0 Γ) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ term resultType) ∧
  Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) ∧
  (∀ K, LOKt σ 4 K application_typed ∧
    Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) field))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) field))
      (RawFamilyIHBuilderAttack.x P) ∧
    Origin (mkM P (base P)) fd (C P) 0
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) resultType))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) resultType))
      (den (model P (C P)) σ (ρ P) term) ∧
    den (model P (C P)) σ (ρ P) term ∈
      Ed (model P (C P)) (den (model P (C P)) σ (ρ P) resultType) ∧
    ¬ Equiv (den (model P (C P)) σ (ρ P) term) pempty) ∧
  (let M := mkM P (base P)
   let B := fun _ : PSet.{4} => tyv (C P [] (key [parameter]))
   let B' := fun _ : PSet.{4} => tyv (D P [] (key [parameter]))
   let S := Ed M (piVal M (tyv pempty) B)
   let T := Ed M (piVal M (tyv pempty) B')
   Origin M fd (C P) 1 S T pempty ∧ pempty ∈ S ∧ Equiv S T ∧
     Equiv (pempty : PSet.{4}) pempty) ∧
  σ 0 = 1

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PiGraphInversionAttack.component_witness P, ⟨context_typed⟩, ⟨application_typed⟩,
    (contexts_fit P).1, (contexts_fit P).2,
    fun K => ⟨application_bound K, lookup_origin P K, application_origin P K,
      result_mem P K, result_nonempty P K⟩, empty_separator P, rfl⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RecFieldOriginAttack
