import rcic.RcicF3NormFreshHead
import rcic.RcicF3NormPendAWInvariant
import rcic.RcicF3RawFamilyMinorAttack

/-!
# Strict enlargement and bounded separation at the admitted W fixture

The starting frame is the actual W frame over the canonical normalized
installed table. Its height-omega member remains in the strict admissible
enlargement. Both sound family prefixes are produced from the real Nat
predecessor, and the actual height-omega constructor tuple supplies both
original constructor-context fits through the generic checked producer.

A separate well-formed local context in that same family-only environment
contains the height-omega value as a DATA family local. The bounded variable
separation theorem rules out typing that local at any family-free type.
This auxiliary local declaration is not claimed to be a stored W field.
Its full valuation retains the extra universe slot 1. No general converted
Pi separation, domain mask, common small signature or universal A is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormFreshHeadAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex
open PendAWBridge (fd)
open NormPendAW (plan)

noncomputable abbrev base (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormPendAW.table P
noncomputable abbrev C (P : Premises4) : Frame := frame P (base P) fd
noncomputable abbrev D (P : Premises4) : Frame := RawFamilyEnlarge.enlarge fd (C P)
noncomputable abbrev model (P : Premises4) (X : Frame) : Interp.{4} :=
  mkM P (table P (base P) fd X)

def parameter : PSet.{4} := tyv fxS
abbrev σ : Nat → Nat := RawFamilyIHBuilderAttack.σ

theorem admissible_C (P : Premises4) : Admissible fd (C P) :=
  RawWFrame.raw_admissible P (base P)

theorem admissible_D (P : Premises4) : Admissible fd (D P) :=
  RawFamilyEnlarge.admissible P fd (C P) (admissible_C P)

theorem strict_all (P : Premises4) : ∀ vs i, ¬ Equiv (C P vs i) (D P vs i) :=
  fun vs i => RawFamilyEnlarge.strict fd (C P) vs i (by change 1 ≠ 0; decide)

theorem omega_C (P : Premises4) : fxZW P ∈ C P [] (key [parameter]) :=
  mem_congr_right (apply_ofFrame_ed P (base P) fd (C P) (admissible_C P)
    [] [parameter] (PendAWBridge.argsFit P (base P) pempty))
    (RawWFrame.heightOmega_gap P (base P)).1

theorem omega_D (P : Premises4) : fxZW P ∈ D P [] (key [parameter]) :=
  RawFamilyEnlarge.frame_sub fd (C P) [] (key [parameter]) _ (omega_C P)

private theorem predecessor_context (r : Nat) (hr : Dom natEnvU r) :
    NormRole.envCtx PendAWGroup.wft r = NormRole.envCtx natEnvUWfT r :=
  NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT r hr

private theorem predecessor_plan (r : Nat) (hr : Dom natEnvU r) :
    EvalRole.envPlan PendAWGroup.wft r = EvalRole.envPlan natEnvUWfT r :=
  EvalRole.envPlan_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT r hr

private theorem predecessor_faithful (P : Premises4) :
    EvalRole.Faithful role P (base P) (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) natEnvU :=
  fun r m hm => NormPendAW.faithful P r m (groupMembersT_preserve PendAW.membersT r m hm)

/-- Every supplied admissible W frame gives an actually sound family-only
prefix, including the freshly constructed strict enlargement. -/
theorem prefix_sound (P : Premises4) (X : Frame) (hX : Admissible fd X)
    (τ K : Nat → Nat) (n : Nat) : EnvSound (model P X) τ K PendAW.eFam n := by
  have hX' : Admissible (famDataOf plan.node.a) X := by
    rw [NormPendAW.raw_descriptor]
    exact hX
  have hp := NormCandidatePrefix.target_facts P (base P) K plan PendAW.fam
    [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl PendAW.membersT
    (NormNatInvariant.gInv P K) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) predecessor_context predecessor_plan
    (predecessor_faithful P) X hX'
  rw [NormPendAW.raw_descriptor] at hp
  exact hp.2.2 τ n

noncomputable def nodeIndex : Fin plan.node.a.constructors.length :=
  ⟨1, by
    rw [node_ctors_length (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) plan.node rfl]
    decide⟩

theorem node_parameters : (plan.node.a.constructorViews nodeIndex).parameters =
    [.sort (.succ .zero)] := (PendAWGroup.views plan.node nodeIndex).1

theorem node_fields : (plan.node.a.constructorViews nodeIndex).fields = [PendAW.field] := by
  rcases (PendAWGroup.views plan.node nodeIndex).2.2 with ⟨_, hn⟩ | ⟨hf, _⟩
  · change (1 : Nat) = 0 at hn
    cases hn
  · exact hf

theorem arity : plan.node.a.family.member.arity = 0 :=
  congrArg CheckedMember.arity (PendAWGroup.familyMember plan.node)

private theorem field_tuple (P : Premises4) :
    TelFits (model P (C P)) (σOf []) (EvalPlanNormal.fields plan nodeIndex)
      (push [parameter] ρ0) [RawFamilyIHBuilderAttack.x P] := by
  rw [NormPendAW.fields_eq, node_fields]
  refine ⟨?_, True.intro⟩
  have h := RawFamilyMinorAttack.raw_field_mem P (base P)
  change RawFamilyIHBuilderAttack.x P ∈ Ed (model P (C P))
    (den (model P (C P)) σ (push [parameter] ρ0) PendAW.field) at h
  rw [den_levels_closed (model P (C P)) σ (σOf []) PendAW.field rfl] at h
  exact h

/-- This invocation retains the real recursive field and its height-omega
branching function in both original constructor prefixes. -/
theorem constructor_prefixes (P : Premises4) (bound : Nat) :
    Fits (model P (C P)) (σOf [])
      [.assumption PendAW.field, .assumption (.sort (.succ .zero))]
      (vcons (RawFamilyIHBuilderAttack.x P) (vcons parameter ρ0)) ∧
    Fits (model P (D P)) (σOf [])
      [.assumption PendAW.field, .assumption (.sort (.succ .zero))]
      (vcons (RawFamilyIHBuilderAttack.x P) (vcons parameter ρ0)) := by
  have hC' : Admissible (famDataOf plan.node.a) (C P) := by
    rw [NormPendAW.raw_descriptor]
    exact admissible_C P
  have hps : TelFits (mkM P (base P)) (σOf []) plan.node.a.family.parameters
      ρ0 [parameter] := by
    rw [(PendAWGroup.familyInfo plan.node).1]
    exact PendAWBridge.argsFit P (base P) pempty
  have hxs : TelFits (mkM P (table P (base P) (famDataOf plan.node.a) (C P)))
      (σOf []) (EvalPlanNormal.fields plan nodeIndex) (push [parameter] ρ0)
      [RawFamilyIHBuilderAttack.x P] := by
    rw [NormPendAW.raw_descriptor]
    exact field_tuple P
  have hp := NormFreshHead.constructor_prefixes P (base P) (fun _ => bound) plan
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT (PendAWGroup.boundG _)
    (PendAWGroup.boundDG bound)
    (fun j => (PendAWGroup.views plan.node j).1.trans
      (PendAWGroup.familyInfo plan.node).1.symm)
    (NormNatInvariant.gInv P _) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) predecessor_context predecessor_plan
    (predecessor_faithful P) (C P) hC' [] arity.symm
    (fun _ h => (List.not_mem_nil _ h).elim) nodeIndex [parameter]
    [RawFamilyIHBuilderAttack.x P] hps hxs 1
    (by rw [node_fields]; exact Nat.le_refl 1)
  dsimp only at hp
  rw [NormPendAW.raw_descriptor, node_parameters, node_fields] at hp
  exact hp.2.2

/-- An auxiliary local DATA value, in the actual admitted family prefix.
This is deliberately separate from the stored higher-order W field. -/
def Γ : LCtx :=
  [.assumption (.app (.const 4 []) (.bvar 0)), .assumption (.sort (.succ .zero))]

noncomputable def local_wf : CtxWfT PendAW.eFam 0 Γ :=
  .assumption [.assumption (.sort (.succ .zero))]
    (.app (.const 4 []) (.bvar 0)) (.succ .zero)
    (.assumption [] (.sort (.succ .zero)) (.succ (.succ .zero)) .nil
      (.sort [] (.succ .zero)))
    (.app _ (.const 4 []) (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 0 _ rfl))

noncomputable def family_local : HasTyT PendAW.eFam 0 Γ (.bvar 0)
    (.app (.const 4 []) (.bvar 1)) := .bvar Γ 0 _ rfl

noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons (fxZW P) (vcons parameter ρ0)

theorem local_fits (P : Premises4) (X : Frame) (hX : Admissible fd X)
    (hω : fxZW P ∈ X [] (key [parameter])) : Fits (model P X) σ Γ (ρ P) := by
  have hps := PendAWBridge.argsFit P (table P (base P) fd X) pempty
  refine ⟨⟨True.intro, hps.1⟩, ?_⟩
  apply (apply_updated_mem_iff P (base P) fd X hX
    RawFamilyViewAttack.w_family_free [] [parameter] rfl (fxZW P)).mpr
  exact ⟨hps, hω⟩

/-- Actual bounded variable typing at a family-free type is excluded.
The auxiliary context itself is well formed and contains height omega. -/
theorem no_clean_local (P : Premises4) (K : Nat → Nat) (A : Expr Nat)
    (hA : occursConst 4 A = false)
    (d : HasTyT PendAW.eFam 0 Γ (.bvar 0) A) (hd : LOKt σ 4 K d) : False := by
  apply RawFamilyEnlarge.no_clean_variable_type P (base P) fd (C P) (admissible_C P)
    0 σ K (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0) (ρ P)
    (local_fits P (C P) (admissible_C P) (omega_C P))
    (local_fits P (D P) (admissible_D P) (omega_D P))
    [.bvar 1] A (by intro e he; cases List.mem_singleton.mp he; rfl) hA
    (by change 1 ≠ 0; decide) ?_ 0 rfl d hd
  exact PendAWBridge.argsFit P (base P) pempty

def Witness (P : Premises4) : Prop :=
  NormPendAWInvariant.Witness P ∧
  Admissible fd (C P) ∧ Admissible fd (D P) ∧ FrameSub (C P) (D P) ∧
  (∀ vs i, ¬ Equiv (C P vs i) (D P vs i)) ∧
  fxZW P ∈ C P [] (key [parameter]) ∧ fxZW P ∈ D P [] (key [parameter]) ∧
  (Fits (model P (C P)) (σOf [])
      [.assumption PendAW.field, .assumption (.sort (.succ .zero))]
      (vcons (RawFamilyIHBuilderAttack.x P) (vcons parameter ρ0)) ∧
    Fits (model P (D P)) (σOf [])
      [.assumption PendAW.field, .assumption (.sort (.succ .zero))]
      (vcons (RawFamilyIHBuilderAttack.x P) (vcons parameter ρ0))) ∧
  (∀ K, EnvSound (model P (C P)) σ K PendAW.eFam 0 ∧
    EnvSound (model P (D P)) σ K PendAW.eFam 0) ∧
  Nonempty (CtxWfT PendAW.eFam 0 Γ) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ (.bvar 0) (.app (.const 4 []) (.bvar 1))) ∧
  Fits (model P (C P)) σ Γ (ρ P) ∧ Fits (model P (D P)) σ Γ (ρ P) ∧
  (∀ K A, occursConst 4 A = false →
    ∀ d : HasTyT PendAW.eFam 0 Γ (.bvar 0) A, LOKt σ 4 K d → False) ∧
  σ 0 = 1 ∧ σ 0 ≠ σOf [] 0

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPendAWInvariant.component_witness P, admissible_C P, admissible_D P,
    RawFamilyEnlarge.frame_sub fd (C P), strict_all P, omega_C P, omega_D P,
    constructor_prefixes P 1,
    (fun K => ⟨prefix_sound P (C P) (admissible_C P) σ K 0,
      prefix_sound P (D P) (admissible_D P) σ K 0⟩),
    ⟨local_wf⟩, ⟨family_local⟩,
    local_fits P (C P) (admissible_C P) (omega_C P),
    local_fits P (D P) (admissible_D P) (omega_D P), no_clean_local P,
    rfl, by decide⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormFreshHeadAttack
