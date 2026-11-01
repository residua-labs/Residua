import rcic.RcicF3PiSmallRecursive
import rcic.RcicF3PiSmallTupleAttack
import rcic.RcicF3PiStageValue

/-!
# Stage-one compression of a dependent depth-three data field

The first argument chooses a proof or data type; the second argument is
typed in that chosen domain. The third argument and every terminal value
contain the exact admitted PendA height-omega element. The field is an
actual piLam, its original element-set is in W4 1, and Choice0 compresses
it without changing the value or the complete three-entry result reader.

The auxiliary table is a semantic compiler fixture. No EnvWfT certificate
for that table or universal data-frame producer is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallRecursiveAttack
open Rcic.Declarative PiIndex
open PiSmallTupleAttack (model σ fields result proofTuple dataTuple
  proofType dataType alternatives)

def leaf : Expr Nat := .const 7 []
def field : Expr Nat := policyPi fields leaf

noncomputable def labels (P : Premises4) : (Nat → PSet.{4}) → Index.{4} :=
  read (model P) σ result

noncomputable def fibres (P : Premises4) : Index.{4} → PSet.{4} :=
  fun _ => singleton (fxZW P)

noncomputable def originalTel (P : Premises4) : RecTel.{4,5} Index.{4} 3 :=
  PiSyntaxCompile.compile (model P) σ (labels P) fields ρ0

noncomputable def smallTel (P : Premises4) : RecTel.{0,5} Index.{4} 3 :=
  PiSmallRecursive.compile.{0,4,5} (model P) P.c0 σ (labels P) fields ρ0

noncomputable def value (P : Premises4) : PSet.{4} :=
  piLam (model P) σ (fun _ => fxZW P) ρ0 field

theorem fibres_dich (P : Premises4) : ∀ i, Dich (fibres P i) :=
  fun _ => PiSmallTupleAttack.singleton_dich (PiSmallTupleAttack.omega_not_empty P)

theorem leaf_read (P : Premises4) (ρ : Nat → PSet.{4}) :
    Equiv (fibres P (labels P ρ)) (Ed (model P) (den (model P) σ ρ leaf)) :=
  (ed_tyv (model P) (fibres_dich P (labels P ρ))).symm

theorem leaf_member (P : Premises4) (ρ : Nat → PSet.{4}) :
    fxZW P ∈ Ed (model P) (den (model P) σ ρ leaf) :=
  mem_congr_right (leaf_read P ρ) (mem_singleton.mpr Equiv.rfl)

theorem alternative_domain_stage (P : Premises4) (a : PSet.{4})
    (ha : a ∈ Ed (model P) (tyv alternatives)) : Ed (model P) a ∈ W4 1 := by
  have hm := mem_congr_right (ed_tyv (model P) PiSmallTupleAttack.alternatives_dich) ha
  rcases mem_pair.mp hm with he | he
  · exact mem_congr_left (ed_congr (model P) he).symm
      (PiSmallTupleAttack.proof_small P).2.1
  · exact mem_congr_left (ed_congr (model P) he).symm
      (PiSmallTupleAttack.data_small P).2.1

theorem original_domains_stage (P : Premises4) :
    (originalTel P).DomainsStage (W4 1) := by
  refine ⟨(PiSmallTupleAttack.proof_small P).1, ?_⟩
  intro q
  refine ⟨?_, fun _ => ⟨(PiSmallTupleAttack.proof_small P).2.2.1,
    fun _ => True.intro⟩⟩
  exact alternative_domain_stage P _ (PiCompile.classValue_mem _ q)

theorem original_equiv (P : Premises4) :
    Equiv ((originalTel P).erasedType (model P) (fibres P))
      (den (model P) σ ρ0 field) := by
  apply PiSyntaxCompile.compile_spec (model P) σ (labels P) (fibres P)
    (fibres_dich P) leaf fields ρ0
  intro a ha b hb c hc
  exact Equiv.rfl

theorem original_stage_one (P : Premises4) :
    Ed (model P) (den (model P) σ ρ0 field) ∈ W4 1 := by
  have hs := (originalTel P).erasedType_stage (model P) (W4 1) (stage4 P 0)
    (PiSyntaxCompile.compile_domains (model P) σ (labels P) fields ρ0)
    (original_domains_stage P) (fibres P) (fibres_dich P)
    (fun _ => (stage4 P 0).singleton_mem (PiSmallTupleAttack.omega_stage_one P))
  exact mem_congr_left (ed_congr (model P) (original_equiv P)) hs

theorem value_member (P : Premises4) :
    value P ∈ Ed (model P) (den (model P) σ ρ0 field) := by
  apply piLam_mem (model P) σ (envResp_const (fxZW P)) field ρ0
  intro a ha b hb c hc
  exact leaf_member P _

theorem proof_apply (P : Premises4) :
    Equiv (fapps (value P) (proofTuple P)) (fxZW P) :=
  fapps_piLam (model P) σ (envResp_const (fxZW P)) leaf fields ρ0
    (proofTuple P) (PiSmallTupleAttack.proof_fits P)

theorem data_apply (P : Premises4) :
    Equiv (fapps (value P) (dataTuple P)) (fxZW P) :=
  fapps_piLam (model P) σ (envResp_const (fxZW P)) leaf fields ρ0
    (dataTuple P) (PiSmallTupleAttack.data_fits P)

theorem empty_body_equations (P : Premises4) :
    DeltaNormalize.BodyEquations (model P) emptyEnv σ := by
  intro r ls b hb ρ
  cases hb

theorem field_read : piTelescopeFuel emptyEnv 16 field = some (fields, leaf) := by
  decide

/-- This calls the exact stage-one normalization/compression composition,
not merely its generic membership lemma with a supplied result. -/
theorem compressed_member (P : Premises4) :
    value P ∈ Ed (model P)
      ((PiSmallRecursive.widen.{0,4,5} (smallTel P)).erasedType (model P) (fibres P)) :=
  PiSmallRecursive.normalized_mem_stage_one P (model P) emptyEnv σ
    (empty_body_equations P) (labels P) (fibres P) (fibres_dich P)
    leaf (leaf_read P) 16 field fields ρ0 (value P) field_read
    (original_stage_one P) (value_member P)

theorem compressed_result (P : Premises4) (p : (smallTel P).tel.Path) :
    ∃ xs, TelFits (model P) σ fields ρ0 xs ∧
      (smallTel P).result p = key (result.map (den (model P) σ (push xs ρ0))) :=
  PiSmallRecursive.result_fits.{0,4,5} (model P) P.c0 σ (labels P) fields ρ0 p

def Witness (P : Premises4) : Prop :=
  fields.length = 3 ∧
  Ed (model P) (den (model P) σ ρ0 field) ∈ W4 1 ∧
  value P ∈ Ed (model P) (den (model P) σ ρ0 field) ∧
  value P ∈ Ed (model P)
    ((PiSmallRecursive.widen.{0,4,5} (smallTel P)).erasedType (model P) (fibres P)) ∧
  Equiv (fapps (value P) (proofTuple P)) (fxZW P) ∧
  Equiv (fapps (value P) (dataTuple P)) (fxZW P) ∧
  (∀ p : (smallTel P).tel.Path, ∃ xs, TelFits (model P) σ fields ρ0 xs ∧
    (smallTel P).result p = key (result.map (den (model P) σ (push xs ρ0)))) ∧
  PiSmallTupleAttack.Witness P

theorem component_witness (P : Premises4) : Witness P :=
  ⟨rfl, original_stage_one P, value_member P, compressed_member P,
    proof_apply P, data_apply P, compressed_result P,
    PiSmallTupleAttack.component_witness P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PiSmallRecursiveAttack
