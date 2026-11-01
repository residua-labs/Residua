import rcic.RcicF3PiSmallMaskShape
import rcic.RcicF3PiSmallRecursiveAttack
import rcic.RcicF3NormDataRecMemAttack

/-!
# An inhabited small masked signature with a dependent depth-three field

A seed contains the exact admitted W height-omega value. A second
constructor contains an actual depth-three function returning that seed,
followed by another height-omega payload. The inner telescope chooses a
proof or data domain and retains all three arguments. Its later ordinary
field is read after masking the recursive function to pempty; that domain
equality is proved directly. The output key retains the actual function.

Both constructor codes enter the newly compiled Type0 signature through
its public tuple-to-shape producer. Its closed family lies in W4 1 using
Choice0. This is an auxiliary semantic compiler fixture, with no EnvWfT
claim for its table; the actual admitted W component is retained separately.
No universal admitted mask or all-vector normalized frame is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallMaskShapeAttack
open Rcic.Declarative PiIndex PiValueRule PiSmallMaskShape
open PiSmallTupleAttack (σ fields proofTuple dataTuple)

noncomputable def seed (P : Premises4) : PSet.{4} := dataVal 0 [fxZW P]

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  fun r vs => if r = 8 then tyv (singleton (seed P)) else PiSmallTupleAttack.table P r vs

noncomputable def model (P : Premises4) : Interp.{4} := mkM P (table P)

def leaf : Expr Nat := .const 8 []
def field : Expr Nat := policyPi fields leaf
def specs : List FieldSpec := [.recursive fields [], .plain (.const 7 [])]
def constructors : List PiValueRule.Constructor :=
  [⟨[.plain (.const 7 [])], []⟩, ⟨specs, [.bvar 1, .bvar 0]⟩]

noncomputable def sig (P : Premises4) := PiSmallMaskShape.signature.{0,4} (model P) P.c0 σ constructors []
noncomputable def X (P : Premises4) : Index.{4} → PSet.{4} :=
  PiSmallKeyProducerAt.family (model P) (sig P)

theorem seed_not_empty (P : Premises4) : ¬ Equiv (seed P) pempty := dataVal_ne_pempty 0 _

theorem seed_stage (P : Premises4) : seed P ∈ W4 1 := by
  apply dataVal_mem_stage (stage4 P 0) 0
  intro x hx
  have he : x = fxZW P := List.mem_singleton.mp hx
  subst x
  exact PiSmallTupleAttack.omega_stage_one P

theorem plain_read (P : Premises4) (ρ : Nat → PSet.{4}) :
    Equiv (Ed (model P) (den (model P) σ ρ (.const 7 []))) (singleton (fxZW P)) :=
  ed_tyv (model P) (PiSmallTupleAttack.singleton_dich (PiSmallTupleAttack.omega_not_empty P))

theorem plain_mem (P : Premises4) (ρ : Nat → PSet.{4}) :
    fxZW P ∈ Ed (model P) (den (model P) σ ρ (.const 7 [])) :=
  mem_congr_right (plain_read P ρ).symm (mem_singleton.mpr Equiv.rfl)

theorem plain_stage (P : Premises4) (ρ : Nat → PSet.{4}) :
    Ed (model P) (den (model P) σ ρ (.const 7 [])) ∈ W4 1 :=
  mem_congr_left (plain_read P ρ).symm
    ((stage4 P 0).singleton_mem (PiSmallTupleAttack.omega_stage_one P))

theorem leaf_read (P : Premises4) (ρ : Nat → PSet.{4}) :
    Equiv (Ed (model P) (den (model P) σ ρ leaf)) (singleton (seed P)) :=
  ed_tyv (model P) (PiSmallTupleAttack.singleton_dich (seed_not_empty P))

theorem leaf_mem (P : Premises4) (ρ : Nat → PSet.{4}) :
    seed P ∈ Ed (model P) (den (model P) σ ρ leaf) :=
  mem_congr_right (leaf_read P ρ).symm (mem_singleton.mpr Equiv.rfl)

/-- The seed uses the new public constructor/shape producer. -/
theorem seed_mem (P : Premises4) : seed P ∈ X P (key []) := by
  apply PiSmallMaskShape.produce.{0,4} (model P) (model P) P.c0 rfl σ constructors [] 8 []
    (⟨0, by decide⟩ : Fin constructors.length) [fxZW P]
  · exact ⟨plain_mem P ρ0, True.intro⟩
  · exact ⟨plain_stage P ρ0, True.intro⟩
  · exact ⟨Equiv.rfl, fun _ _ => True.intro⟩
  · exact True.intro

noncomputable def branchTel (P : Premises4) : RecTel.{4,5} (List PSet.{4}) 3 :=
  PiSyntaxCompile.compile (model P) σ (lastVals 3) fields ρ0

theorem branch_domains_stage (P : Premises4) : (branchTel P).DomainsStage (W4 1) := by
  refine ⟨(PiSmallTupleAttack.proof_small P).1, ?_⟩
  intro q
  refine ⟨?_, fun _ => ⟨(PiSmallTupleAttack.proof_small P).2.2.1,
    fun _ => True.intro⟩⟩
  exact PiSmallRecursiveAttack.alternative_domain_stage P _ (PiCompile.classValue_mem _ q)

theorem branch_equiv (P : Premises4) :
    Equiv ((branchTel P).erasedType (model P) (fun _ => singleton (seed P)))
      (den (model P) σ ρ0 field) := by
  apply PiSyntaxCompile.compile_spec (model P) σ (lastVals 3) (fun _ => singleton (seed P))
    (fun _ => PiSmallTupleAttack.singleton_dich (seed_not_empty P)) leaf fields ρ0
  intro a ha b hb c hc
  exact Equiv.rfl

theorem branch_stage (P : Premises4) :
    Ed (model P) (den (model P) σ ρ0 field) ∈ W4 1 := by
  have hs := (branchTel P).erasedType_stage (model P) (W4 1) (stage4 P 0)
    (PiSyntaxCompile.compile_domains (model P) σ (lastVals 3) fields ρ0)
    (branch_domains_stage P) (fun _ => singleton (seed P))
    (fun _ => PiSmallTupleAttack.singleton_dich (seed_not_empty P))
    (fun _ => (stage4 P 0).singleton_mem (seed_stage P))
  exact mem_congr_left (ed_congr (model P) (branch_equiv P)) hs

noncomputable def value (P : Premises4) : PSet.{4} :=
  piLam (model P) σ (fun _ => seed P) ρ0 field

theorem value_mem (P : Premises4) :
    value P ∈ Ed (model P) (den (model P) σ ρ0 field) := by
  apply piLam_mem (model P) σ (envResp_const (seed P)) field ρ0
  intro a ha b hb c hc
  exact leaf_mem P _

theorem proof_apply (P : Premises4) :
    Equiv (fapps (value P) (proofTuple P)) (seed P) :=
  fapps_piLam (model P) σ (envResp_const (seed P)) leaf fields ρ0
    (proofTuple P) (PiSmallTupleAttack.proof_fits P)

theorem data_apply (P : Premises4) :
    Equiv (fapps (value P) (dataTuple P)) (seed P) :=
  fapps_piLam (model P) σ (envResp_const (seed P)) leaf fields ρ0
    (dataTuple P) (PiSmallTupleAttack.data_fits P)

theorem value_not_empty (P : Premises4) : ¬ Equiv (value P) pempty :=
  fun he => seed_not_empty P ((proof_apply P).symm.trans
    (fapps_equiv_pempty he (proofTuple P)))

theorem tuple_fits (P : Premises4) :
    TelFits (model P) σ (specs.map (fieldExpr 8 [])) ρ0 [value P, fxZW P] :=
  ⟨value_mem P, plain_mem P _, True.intro⟩

theorem tuple_stage (P : Premises4) :
    SmallAlong (model P) σ (W4 1) (specs.map (fieldExpr 8 [])) ρ0 [value P, fxZW P] :=
  ⟨branch_stage P, plain_stage P _, True.intro⟩

/-- The later ordinary domain is literally unchanged when the preceding
actual recursive value is masked. No Fits of the masked prefix is used. -/
theorem tuple_mask (P : Premises4) :
    TupleMask (model P) (model P) σ specs ρ0 ρ0 [value P, fxZW P] :=
  ⟨PiSmallMaskSpine.domains_self (model P) σ fields ρ0,
    Equiv.rfl, fun _ _ => True.intro⟩

theorem reached_leaves (P : Premises4) :
    Leaves (model P) (model P) σ 8 [] (X P) specs ρ0 [value P, fxZW P] := by
  refine ⟨?_, True.intro⟩
  intro zs hz z hleaf
  have he : Equiv z (seed P) := mem_singleton.mp (mem_congr_right (leaf_read P _) hleaf)
  exact mem_congr_left he.symm (seed_mem P)

/-- The recursive code uses the same actual field that was compressed,
and its two-entry output key includes that field without erasure. -/
theorem node_mem (P : Premises4) :
    dataVal 1 [value P, fxZW P] ∈ X P (key [value P, fxZW P]) :=
  PiSmallMaskShape.produce.{0,4} (model P) (model P) P.c0 rfl σ constructors [] 8 []
    (⟨1, by decide⟩ : Fin constructors.length) [value P, fxZW P]
    (tuple_fits P) (tuple_stage P) (tuple_mask P) (reached_leaves P)

theorem compiled_component (P : Premises4) :
    PiSmallKeyProducerAt.Closed (model P) (sig P) (X P) ∧
      ∀ i, X P i ∈ W4 1 ∧ ¬ pempty ∈ X P i :=
  component_stage_one P (model P) σ constructors []

theorem node_not_empty (P : Premises4) : ¬ Equiv (dataVal 1 [value P, fxZW P]) pempty :=
  dataVal_ne_pempty 1 _

def Witness (P : Premises4) : Prop :=
  NormDataRecMemAttack.Witness P ∧
  fields.length = 3 ∧
  TelFits (model P) σ fields ρ0 (proofTuple P) ∧
  TelFits (model P) σ fields ρ0 (dataTuple P) ∧
  TelFits (model P) σ (specs.map (fieldExpr 8 [])) ρ0 [value P, fxZW P] ∧
  SmallAlong (model P) σ (W4 1) (specs.map (fieldExpr 8 [])) ρ0 [value P, fxZW P] ∧
  TupleMask (model P) (model P) σ specs ρ0 ρ0 [value P, fxZW P] ∧
  seed P ∈ X P (key []) ∧
  dataVal 1 [value P, fxZW P] ∈ X P (key [value P, fxZW P]) ∧
  Equiv (fapps (value P) (proofTuple P)) (seed P) ∧
  Equiv (fapps (value P) (dataTuple P)) (seed P) ∧
  ¬ Equiv (value P) pempty ∧
  PiSmallKeyProducerAt.Closed (model P) (sig P) (X P) ∧
  (∀ i, X P i ∈ W4 1 ∧ ¬ pempty ∈ X P i) ∧
  ¬ Equiv (dataVal 1 [value P, fxZW P]) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormDataRecMemAttack.component_witness P, rfl,
    PiSmallTupleAttack.proof_fits P, PiSmallTupleAttack.data_fits P,
    tuple_fits P, tuple_stage P, tuple_mask P, seed_mem P, node_mem P,
    proof_apply P, data_apply P, value_not_empty P,
    (compiled_component P).1, (compiled_component P).2, node_not_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PiSmallMaskShapeAttack
