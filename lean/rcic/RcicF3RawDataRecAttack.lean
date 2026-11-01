import rcic.RcicF3RawDataRec
import rcic.RcicF3NormPendAWInvariant
import rcic.RcicF3RawFamilyRecAtAttack
import rcic.RcicF3RawFamilyMinorAttack

/-!
# Actual stored data minors at the original height-omega W fixture

The base is the canonical normalized installed table. The raw-frame update
is pointwise equivalent to that same table. Both actual stored minor slots
are supplied: their result is the genuine height-omega element, and their
dependent codomain is the admitted motive at its additional universe 1.
The arbitrary-depth engine's minor step is produced by RawDataRec.

All frame, ordinary-environment, constructor-code, motive and minor inputs
are proved here. This is an exact W component witness; it is not universal
small-frame production, universal StepAG or a new shape-iota theorem.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace Rcic.F3.PSet.RawDataRecAttack
open Rcic.Declarative PiIndex RawFamily PropEval
open PendAWBridge (fd)

abbrev σ : Nat → Nat := RawFamilyIHBuilderAttack.σ
def K : Nat → Nat := fun _ => 1
noncomputable abbrev base (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormPendAW.table P
noncomputable abbrev model (P : Premises4) : Interp.{4} :=
  RawFamilyRec.model P (base P) fd
def parameter : PSet.{4} := tyv fxS
noncomputable abbrev target (P : Premises4) : PSet.{4} :=
  RawFamilyIHBuilderAttack.target P (base P)
noncomputable abbrev motive (P : Premises4) : PSet.{4} :=
  RawFamilyIHBuilderAttack.motive P (base P)

theorem tables (P : Premises4) :
    ∀ r vs, Equiv (base P r vs) (table P (base P) fd (frame P (base P) fd) r vs) :=
  table_equiv P (base P) fd (frame P (base P) fd)
    (NormPendAWRecPkg.actual_values P).fam

theorem environment (P : Premises4) : EnvSound (model P) σ K PendAW.pNode.E0 0 := by
  have hGI := NormPendAWInvariant.actual_invariant P K
  have hI := hGI.2 PendAW.eAll (fun _ _ h => h)
  have he : EnvSound (mkM P (base P)) σ K PendAW.pNode.E0 0 :=
    envSound_of P (node_sub' PendAW.pNode)
      (fun r m hm => hGI.1 r m (node_sub' PendAW.pNode r m hm))
      (fun r m hm hk => hI r m (node_sub' PendAW.pNode r m hm) hk) σ 0
  exact TableSound.environment P (tables P) σ he

theorem type_facts : TypeFacts PendAW.pNode.E0 :=
  typeFacts_sub (node_sub' PendAW.pNode) (typeFacts_of_envWfT PendAWGroup.wft)

theorem parameter_fit (P : Premises4) :
    TelFits (model P) σ PendAW.pNode.a.family.parameters ρ0 [parameter] := by
  have h := PendAWBridge.argsFit P (table P (base P) fd (frame P (base P) fd)) pempty
  exact h

theorem omega_mem (P : Premises4) : fxZW P ∈ target P := by
  exact mem_congr_right (apply_ofFrame_ed P (base P) fd (frame P (base P) fd)
    (RawWFrame.raw_admissible P (base P)) [] [parameter]
    (PendAWBridge.argsFit P (base P) pempty)) (RawWFrame.heightOmega_gap P (base P)).1

theorem family_mem (P : Premises4) (z : PSet.{4}) (hz : z ∈ target P) :
    z ∈ Ed (model P) (fapps ((model P).μ 4 []) [parameter]) := by
  apply (apply_updated_mem_iff P (base P) fd (frame P (base P) fd)
    (RawWFrame.raw_admissible P (base P)) RawFamilyViewAttack.w_family_free
    [] [parameter] rfl z).mpr
  exact ⟨PendAWBridge.argsFit P (table P (base P) fd (frame P (base P) fd)) pempty, hz⟩

theorem motive_apply (P : Premises4) (z : PSet.{4})
    (hz : z ∈ Ed (model P) (fapps ((model P).μ 4 []) [parameter])) :
    Equiv (fapp (motive P) z) (tyv (target P)) :=
  fapps_piLam (model P) σ (envResp_const _) (.sort (.param 0))
    [RawFamilyIHBuilderAttack.major] (push [parameter] ρ0) [z] ⟨hz, True.intro⟩

theorem omega_in_motive (P : Premises4) (z : PSet.{4})
    (hz : z ∈ Ed (model P) (fapps ((model P).μ 4 []) [parameter])) :
    fxZW P ∈ Ed (model P) (fapp (motive P) z) := by
  exact mem_congr_right ((ed_congr (model P) (motive_apply P z hz)).trans
    (ed_tyv (model P) (admissible_dich (RawWFrame.raw_admissible P (base P)) [] _))).symm
    (omega_mem P)

theorem leaf_mem (P : Premises4) :
    fapps ((model P).μ 5 []) [parameter] ∈
      Ed (model P) (fapps ((model P).μ 4 []) [parameter]) := by
  have h := (environment P).const [] 5 [] PendAW.leaf ρ0 rfl rfl
    (fun _ h => (List.not_mem_nil _ h).elim) True.intro
  change (model P).μ 5 [] ∈ Ed (model P)
    (den (model P) σ ρ0 (policyPi [.sort (.succ .zero)]
      (.app (.const 4 []) (.bvar 0)))) at h
  exact mem_fapps (model P) σ (.app (.const 4 []) (.bvar 0))
    [.sort (.succ .zero)] ρ0 ((model P).μ 5 []) [parameter] h (parameter_fit P)

theorem node_mem (P : Premises4) (x : PSet.{4})
    (hx : x ∈ Ed (model P) (den (model P) σ (push [parameter] ρ0) PendAW.field)) :
    fapps ((model P).μ 6 []) [parameter, x] ∈
      Ed (model P) (fapps ((model P).μ 4 []) [parameter]) := by
  have h := (environment P).const [] 6 [] PendAW.node ρ0 rfl rfl
    (fun _ h => (List.not_mem_nil _ h).elim) True.intro
  change (model P).μ 6 [] ∈ Ed (model P)
    (den (model P) σ ρ0 (policyPi [.sort (.succ .zero), PendAW.field]
      (.app (.const 4 []) (.bvar 1)))) at h
  exact mem_fapps (model P) σ (.app (.const 4 []) (.bvar 1))
    [.sort (.succ .zero), PendAW.field] ρ0 ((model P).μ 6 []) [parameter, x] h
    ⟨(parameter_fit P).1, hx, True.intro⟩

def leafMinor : Expr Nat := .app (.bvar 0) (.app (.const 5 []) (.bvar 1))
def nodeField : Expr Nat := Rcic.Declarative.lift 0 2 PendAW.field
def nodeIH : Expr Nat := .pi (.bvar 3) (.app (.bvar 3) (.app (.bvar 1) (.bvar 0)))
def nodeEnd : Expr Nat := .app (.bvar 3)
  (.app (.app (.const 6 []) (.bvar 4)) (.bvar 1))
def nodeMinor : Expr Nat := .pi nodeField (.pi nodeIH nodeEnd)

/- These are the literal stored minor types, including the inserted IH. -/
kernel_rfl_theorem minor_types : PendAW.recA.minorTypes = [leafMinor, nodeMinor]

noncomputable def second (P : Premises4) : PSet.{4} :=
  piLam (model P) σ (fun _ => fxZW P)
    (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0))) nodeMinor
noncomputable def minors (P : Premises4) : List PSet.{4} := [fxZW P, second P]

theorem first_typed (P : Premises4) : fxZW P ∈ Ed (model P)
    (den (model P) σ (vcons (motive P) (push [parameter] ρ0)) leafMinor) :=
  omega_in_motive P _ (leaf_mem P)

theorem second_typed (P : Premises4) : second P ∈ Ed (model P)
    (den (model P) σ (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0))) nodeMinor) := by
  apply piLam_mem (model P) σ (envResp_const (fxZW P))
  change ∀ x, x ∈ Ed (model P) (den (model P) σ
      (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0))) nodeField) →
    ∀ ih, ih ∈ Ed (model P) (den (model P) σ
      (vcons x (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))) nodeIH) → _
  intro x hx ih _
  have hd := den_lift0_push (model P) σ [motive P, fxZW P]
    (push [parameter] ρ0) PendAW.field
  change den (model P) σ (vcons (fxZW P) (vcons (motive P) (push [parameter] ρ0)))
    nodeField = den (model P) σ (push [parameter] ρ0) PendAW.field at hd
  rw [hd] at hx
  change fxZW P ∈ Ed (model P)
    (fapp (motive P) (fapps ((model P).μ 6 []) [parameter, x]))
  exact omega_in_motive P _ (node_mem P x hx)

/-- The complete actual stored telescope is inhabited by data-valued minors. -/
theorem minors_typed (P : Premises4) :
    TelFits (model P) σ PendAW.pNode.a.minorTypes
      (vcons (motive P) (push [parameter] ρ0)) (minors P) := by
  change TelFits (model P) σ PendAW.recA.minorTypes _ _
  rw [minor_types]
  exact ⟨first_typed P, second_typed P, True.intro⟩

noncomputable def context (P : Premises4) : Context where
  E := natEnvU
  E' := PendAW.eAll
  f := 4
  rr := 7
  rm := PendAW.recMem
  node := PendAW.pNode
  M := model P
  σ := σ
  parameters := [parameter]
  motive := motive P
  minors := minors P
  minor_length := rfl

/-- Transport the actual installed constructor equations to the raw-frame
model and the unchanged valuation containing the extra motive level. -/
theorem ctor_value (P : Premises4) (j : Fin PendAW.pNode.a.constructors.length) :
    Equiv ((model P).μ (PendAW.pNode.a.family.ref + 1 + j.val)
      ((policyFamilyLevels PendAW.pNode.a.family).map (evalTotal σ)))
      (piLam (model P) σ (ctorEnd (model P) σ fd j.val
        (PendAW.pNode.a.constructorViews j).fields.length) ρ0
        (PendAW.pNode.a.constructors[j.val]).mtype) := by
  have hV := NormPendAWRecPkg.actual_values P
  have hC := hV.ctor j []
  rw [nfOf_famDataOf] at hC
  have hT := piLam_tables P (tables P) (σOf [])
    (ctorEnd_resp (mkM P (base P)) (σOf []) fd j.val
      (PendAW.pNode.a.constructorViews j).fields.length)
    (g₂ := ctorEnd (model P) (σOf []) fd j.val
      (PendAW.pNode.a.constructorViews j).fields.length)
    (fun _ => Equiv.rfl) (PendAW.pNode.a.constructors[j.val]).mtype ρ0
  have he : Equiv ((model P).μ (4 + 1 + j.val) [])
      (piLam (model P) (σOf []) (ctorEnd (model P) (σOf []) fd j.val
        (PendAW.pNode.a.constructorViews j).fields.length) ρ0
        (PendAW.pNode.a.constructors[j.val]).mtype) :=
    (tables P _ []).symm.trans (hC.trans hT)
  change Equiv ((model P).μ (4 + 1 + j.val) []) _
  refine he.trans ?_
  have hst := (PendAW.pNode.a.constructorViews j).storedType
  rw [hst]
  have hb := hV.ctorBounded j
  rw [hst] at hb
  obtain ⟨hD, _⟩ := levelsBounded_policyPi _ _ _ hb
  have hσ : ∀ k, k < PendAW.pNode.a.family.member.arity → σOf [] k = σ k :=
    fun k hk => (Nat.not_lt_zero k hk).elim
  refine piLam_levels (model P) hσ (ctorEnd_resp _ _ _ _ _)
    (fun _ => Equiv.rfl) _ (fun _ => ?_) _ hD ρ0
  rw [piLam_foldApps_const, piLam_foldApps_const]
  exact Equiv.rfl

theorem constructor_data (P : Premises4)
    (j : Fin (context P).node.a.constructors.length) (xs : List PSet.{4})
    (hxs : TelFits (context P).M (context P).σ
      ((context P).node.a.constructorViews j).fields
      (push (context P).parameters ρ0) xs) :
    Equiv ((context P).constructorAt j (context P).parameters xs) (dataVal j.val xs) := by
  have hp : (PendAW.pNode.a.constructorViews j).parameters =
      PendAW.pNode.a.family.parameters := by
    exact (PendAWGroup.views PendAW.pNode j).1.trans (PendAWGroup.familyInfo PendAW.pNode).1.symm
  exact RawDataMinor.constructor_data (model P) σ PendAW.pNode j [parameter] xs
    (by change 1 ≠ 0; decide) hp (parameter_fit P) hxs (ctor_value P j)

/-- The public DATA recursion bridge is actually instantiated with both
typed stored minors; its local closing step is not supplied by this fixture. -/
theorem produced (P : Premises4) :
    ∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
      z ∈ frame P (base P) fd [] i →
      RecPlan.nodeCore (model P) PendAW.pNode (minors P) z ∈
        PiRawMotiveAny.guarded (model P) σ 1 ((model P).μ 4 [])
          (motive P) [parameter] [] (push [parameter] ρ0) i z := by
  exact RawDataRec.nodeCore_guarded P (base P) (context P) rfl K
    PendAWLim.Typed.bounded RawFamilyViewAttack.w_family_free (by change 1 ≠ 0; decide)
    type_facts (environment P) RawFamilyRecAtAttack.bodies RawFamilyRecAtAttack.instances
    (RawWFrame.raw_admissible P (base P)) (RawFamilyInductionAttack.w_closed P (base P))
    (RawFamilyInductionAttack.w_mono P (base P)) (.param 0) rfl
    (RawFamilyIHBuilderAttack.motive_mem P (base P)) (minors_typed P) (constructor_data P)

def Witness (P : Premises4) : Prop :=
  NormPendAWInvariant.Witness P ∧
  Admissible fd (frame P (base P) fd) ∧
  Closed P (base P) fd (frame P (base P) fd) ∧
  ConstructorMono P (base P) fd ∧
  EnvSound (model P) σ K PendAW.pNode.E0 0 ∧
  TelFits (model P) σ PendAW.pNode.a.minorTypes
    (vcons (motive P) (push [parameter] ρ0)) (minors P) ∧
  fxZW P ∈ target P ∧
  fxZW P ∉ El (fapps (famLim P (base P) fd []) [parameter]) ∧
  σ 0 = 1 ∧ σ 0 ≠ σOf [] 0 ∧
  (∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
    z ∈ frame P (base P) fd [] i →
    RecPlan.nodeCore (model P) PendAW.pNode (minors P) z ∈
      PiRawMotiveAny.guarded (model P) σ 1 ((model P).μ 4 [])
        (motive P) [parameter] [] (push [parameter] ρ0) i z) ∧
  RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P) ∈ target P ∧
  ¬ Equiv (RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P)) pempty

theorem component_witness (P : Premises4) : Witness P := by
  have hResult : RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P) ∈ target P := by
    have h := produced P (key [parameter]) (fxZW P) rfl (omega_mem P)
    have hz := family_mem P (fxZW P) (omega_mem P)
    have hm := motive_apply P (fxZW P) hz
    have hT : fapps (motive P) [fxZW P] ∈ (model P).U 1 :=
      mem_congr_left hm.symm (RawFamilyIHBuilderAttack.target_type P (base P))
    have hg := PiRawMotiveAny.guarded_key (model P) σ 1 ((model P).μ 4 [])
      (motive P) [parameter] [] (push [parameter] ρ0) [] (fxZW P) True.intro hz hT
    exact mem_congr_right (hg.trans ((ed_congr (model P) hm).trans
      (ed_tyv (model P) (admissible_dich (RawWFrame.raw_admissible P (base P)) [] _)))) h
  have hNonempty :
      ¬ Equiv (RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P)) pempty := by
    have h := (RawWFrame.raw_admissible P (base P) [] (key [parameter])).2
    change (if (1 : Nat) = 0 then _ else _) at h
    rw [if_neg (by decide : (1 : Nat) ≠ 0)] at h
    exact h _ hResult
  exact ⟨NormPendAWInvariant.component_witness P, RawWFrame.raw_admissible P (base P),
    RawFamilyInductionAttack.w_closed P (base P), RawFamilyInductionAttack.w_mono P (base P),
    environment P, minors_typed P, omega_mem P, (RawWFrame.heightOmega_gap P (base P)).2,
    rfl, by decide, produced P, hResult, hNonempty⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RawDataRecAttack
