import rcic.RcicF3RecFieldConsumer
import rcic.RcicF3DataNotPiAttack
import rcic.RcicF3CandidateBoundTuple

/-!
# An inhabited higher-order W argument and an actual proof consumer

The actual admitted W constructor prefix carries its height-omega branching
function. Two auxiliary locals then supply a true proposition and a proof-
valued consumer of that function. This is an actual well-formed local
context and application derivation over the admitted family-only environment;
the auxiliary consumer is not asserted to be a stored constructor field.

Both source and enlarged models fit the same complete local environment.
The new generic consumer-erasure theorem is invoked with the actual bounded
application premises. Separately, the real W branch has a complete path,
so the new nested-spike theorem proves that the two recursive-field element
sets differ. The extra valuation slot remains 1. All earlier witnesses are
retained, and no universal DATA domain mask or small frame is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldConsumerAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex
open NormFreshHeadAttack (base C D model parameter σ admissible_C admissible_D prefix_sound)
open PendAWBridge (fd)

def fieldAt (k : Nat) : Expr Nat :=
  .pi (.bvar k) (.app (.const 4 []) (.bvar (k + 1)))
def parameterΓ : LCtx := [.assumption (.sort (.succ .zero))]
def fieldΓ : LCtx := .assumption PendAW.field :: parameterΓ
def proofΓ : LCtx := .assumption (.sort .zero) :: fieldΓ
def consumerType : Expr Nat := .pi (fieldAt 2) (.bvar 1)
def Γ : LCtx := .assumption consumerType :: proofΓ
def lookupField : Expr Nat := fieldAt 3
def app : Expr Nat := .app (.bvar 0) (.bvar 2)
def truth : PSet.{4} := tyv (tv True)
noncomputable def start (P : Premises4) : Nat → PSet.{4} :=
  vcons (RawFamilyIHBuilderAttack.x P) (vcons parameter ρ0)
noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons pempty (vcons truth (start P))

noncomputable def parameter_wf : CtxWfT PendAW.eFam 0 parameterΓ :=
  .assumption [] (.sort (.succ .zero)) (.succ (.succ .zero)) .nil
    (.sort [] (.succ .zero))

noncomputable def field_typed : HasTyT PendAW.eFam 0 parameterΓ PendAW.field
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi parameterΓ (.bvar 0) (.succ .zero) (.app (.const 4 []) (.bvar 1)) (.succ .zero)
    (.bvar _ 0 _ rfl)
    (.app _ (.const 4 []) (.bvar 1) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 1 _ rfl))

noncomputable def field_wf : CtxWfT PendAW.eFam 0 fieldΓ :=
  .assumption parameterΓ PendAW.field (.imax (.succ .zero) (.succ .zero))
    parameter_wf field_typed

noncomputable def proof_wf : CtxWfT PendAW.eFam 0 proofΓ :=
  .assumption fieldΓ (.sort .zero) (.succ .zero) field_wf (.sort fieldΓ .zero)

noncomputable def consumer_domain_typed : HasTyT PendAW.eFam 0 proofΓ (fieldAt 2)
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi proofΓ (.bvar 2) (.succ .zero) (.app (.const 4 []) (.bvar 3)) (.succ .zero)
    (.bvar _ 2 _ rfl)
    (.app _ (.const 4 []) (.bvar 3) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 3 _ rfl))

noncomputable def consumer_type_typed : HasTyT PendAW.eFam 0 proofΓ consumerType
    (.sort (.imax (.imax (.succ .zero) (.succ .zero)) .zero)) :=
  .pi proofΓ (fieldAt 2) (.imax (.succ .zero) (.succ .zero)) (.bvar 1) .zero
    consumer_domain_typed (.bvar _ 1 _ rfl)

noncomputable def context_wf : CtxWfT PendAW.eFam 0 Γ :=
  .assumption proofΓ consumerType (.imax (.imax (.succ .zero) (.succ .zero)) .zero)
    proof_wf consumer_type_typed

noncomputable def consumer_typed : HasTyT PendAW.eFam 0 Γ (.bvar 0)
    (.pi lookupField (.bvar 2)) := .bvar Γ 0 _ rfl
noncomputable def argument_typed : HasTyT PendAW.eFam 0 Γ (.bvar 2) lookupField :=
  .bvar Γ 2 _ rfl
noncomputable def application_typed : HasTyT PendAW.eFam 0 Γ app (.bvar 1) :=
  .app Γ (.bvar 0) (.bvar 2) lookupField (.bvar 2) consumer_typed argument_typed

theorem application_bound (K : Nat → Nat) : LOKt σ 4 K application_typed :=
  ⟨True.intro, True.intro⟩

theorem truth_mem (P : Premises4) : truth ∈ U W4 0 :=
  mem_sImage_tyv.mpr ⟨tv True,
    mem_propSets.mpr (fun _ hz => (mem_tv.mp hz).2), Equiv.rfl⟩

private theorem promote_fit (P : Premises4) (X : Frame)
    (h : Fits (model P X) (σOf []) fieldΓ (start P)) :
    Fits (model P X) σ fieldΓ (start P) := by
  refine ⟨h.1, ?_⟩
  rw [den_levels_closed (model P X) σ (σOf []) PendAW.field rfl]
  exact h.2

private theorem extend_fit (P : Premises4) (X : Frame)
    (h : Fits (model P X) σ fieldΓ (start P)) :
    Fits (model P X) σ Γ (ρ P) := by
  let M := model P X
  have ht : truth ∈ Ed M (den M σ (start P) (.sort .zero)) :=
    mem_congr_right (ed_tyv M (U4_dich 0)).symm (truth_mem P)
  refine ⟨⟨h, ht⟩, ?_⟩
  change pempty ∈ Ed M (piVal M (den M σ (vcons truth (start P)) (fieldAt 2))
    (fun _ => truth))
  have he : Equiv (Ed M truth) (tv True) := ed_tyv M (dich_tv True)
  have hp : PiProp M (den M σ (vcons truth (start P)) (fieldAt 2)) (fun _ => truth) :=
    fun _ _ y hy => (mem_tv.mp (mem_congr_right he hy)).2
  apply mem_congr_right (ed_piVal_of_prop M hp).symm
  exact mem_tv.mpr ⟨fun _ _ => mem_congr_right he.symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩), Equiv.rfl⟩

theorem contexts_fit (P : Premises4) :
    Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) := by
  have h := NormFreshHeadAttack.constructor_prefixes P 1
  exact ⟨extend_fit P (C P) (promote_fit P (C P) h.1),
    extend_fit P (D P) (promote_fit P (D P) h.2)⟩

theorem reader : piTelescopeFuel PendAW.eFam 16 lookupField =
    some ([.bvar 3], foldApps (.const 4 (canonL 0)) [.bvar 4]) := by
  rfl

theorem instances (K : Nat → Nat) : InstOK PendAW.eFam σ K lookupField := by
  intro r ls hr
  change (r, ls) ∈ ([] ++ ([(4, [])] ++ [])) at hr
  simp only [List.nil_append, List.append_nil] at hr
  cases List.mem_singleton.mp hr
  exact ⟨PendAW.fam, rfl, rfl, fun _ h => (List.not_mem_nil _ h).elim⟩

theorem bodies (K : Nat → Nat) : BodiesOK PendAW.eFam σ K :=
  CandidateBoundFields.family_prefix_bodiesOK σ K natEnvUWfT
    (natEnvUWfT_classG.2 K) PendAW.membersT

/-- This uses the generic actual-consumer theorem with both direct bounded
application premises. The actual argument is the W height-omega field. -/
theorem application_erasure (P : Premises4) (K : Nat → Nat) :
    (Equiv (den (model P (C P)) σ (ρ P) (.bvar 0)) pempty ∨
      Equiv (RawFamilyIHBuilderAttack.x P) pempty) ∧
    Equiv (den (model P (C P)) σ (ρ P) app)
      (fapp (den (model P (C P)) σ (ρ P) (.bvar 0)) pempty) := by
  exact RecFieldConsumer.consumer_erasure P (base P) fd (C P) (admissible_C P) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0) (bodies K) (ρ P)
    (contexts_fit P).1 (contexts_fit P).2 2 lookupField rfl 0 16 [.bvar 3] [.bvar 4]
    reader (instances K)
    (by intro e he; cases List.mem_singleton.mp he; rfl)
    (by intro e he; cases List.mem_singleton.mp he; rfl) rfl
    (by change 1 ≠ 0; decide) (.bvar 0) lookupField (.bvar 2) rfl
    consumer_typed True.intro argument_typed True.intro

/-- The W branch is actually inhabited, so the strict-telescope argument
is exercised independently of the proof-valued consumer's empty value. -/
theorem field_types_separate (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) lookupField))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) lookupField)) := by
  intro he
  let M := mkM P (base P)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P (base P) σ [.bvar 4])
    [.bvar 3] (ρ P)
  have hclean (k : Nat) : ∀ e ∈ [.bvar k], occursConst 4 e = false := by
    intro e he
    cases List.mem_singleton.mp he
    rfl
  have hc := RecFieldConsumer.lookup_field_eq P (base P) fd (C P) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0) (bodies K) (ρ P)
    (contexts_fit P).1 2 lookupField rfl 0 16 [.bvar 3] [.bvar 4]
    reader (instances K) (hclean 3) (hclean 4)
  have hd := RecFieldConsumer.lookup_field_eq P (base P) fd (D P) σ K
    (prefix_sound P (D P) (admissible_D P) σ K 0) (bodies K) (ρ P)
    (contexts_fit P).2 2 lookupField rfl 0 16 [.bvar 3] [.bvar 4]
    reader (instances K) (hclean 3) (hclean 4)
  dsimp only at hc hd
  have hx := sound_ty (P.good (model P (C P)) rfl)
    (prefix_sound P (C P) (admissible_C P) σ K 0) argument_typed True.intro
    (ρ P) (contexts_fit P).1
  have hnt := RecFieldSeparation.no_path_of_equiv P (base P) fd (C P) (admissible_C P)
    [] (by change 1 ≠ 0; decide) t
    (PiSyntaxCompile.compile_domains M σ (PiIndependent.leafArgs P (base P) σ [.bvar 4])
      [.bvar 3] (ρ P))
    (PiPropField.compile_result_property M σ (PiIndependent.leafArgs P (base P) σ [.bvar 4])
      (fun xs => xs.length = (fd.params ++ fd.indices).length)
      (fun _ => rfl) [.bvar 3] (ρ P)) _ (mem_congr_right hc.symm hx)
    (hc.trans (he.trans hd.symm))
  have hdom : Equiv (Ed M parameter) (fxDomBig P) := by
    rw [fx_domBig_eq P]
    exact (ed_tyv M fx_dich).trans el_tyv.symm
  have ha : ord 1 ∈ Ed M parameter := mem_congr_right hdom.symm
    ((fx_domBig_mem P).mpr ⟨0, Equiv.rfl⟩)
  obtain ⟨i, _⟩ := ha
  exact hnt ⟨Quotient.mk (FSetoid (Ed M parameter)) i, PUnit.unit⟩

def Witness (P : Premises4) : Prop :=
  DataNotPiAttack.Witness P ∧
  Nonempty (CtxWfT PendAW.eFam 0 Γ) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ app (.bvar 1)) ∧
  (∀ K, LOKt σ 4 K application_typed) ∧
  Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) ∧
  piTelescopeFuel PendAW.eFam 16 lookupField =
    some ([.bvar 3], foldApps (.const 4 (canonL 0)) [.bvar 4]) ∧
  (∀ K, InstOK PendAW.eFam σ K lookupField ∧ BodiesOK PendAW.eFam σ K ∧
    (Equiv (den (model P (C P)) σ (ρ P) (.bvar 0)) pempty ∨
      Equiv (RawFamilyIHBuilderAttack.x P) pempty) ∧
    Equiv (den (model P (C P)) σ (ρ P) app)
      (fapp (den (model P (C P)) σ (ρ P) (.bvar 0)) pempty) ∧
    ¬ Equiv (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) lookupField))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) lookupField))) ∧
  σ 0 = 1 ∧ σ 0 ≠ σOf [] 0

theorem component_witness (P : Premises4) : Witness P :=
  ⟨DataNotPiAttack.component_witness P, ⟨context_wf⟩, ⟨application_typed⟩,
    application_bound, (contexts_fit P).1, (contexts_fit P).2, reader,
    (fun K => ⟨instances K, bodies K, (application_erasure P K).1,
      (application_erasure P K).2, field_types_separate P K⟩), rfl, by decide⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RecFieldConsumerAttack
