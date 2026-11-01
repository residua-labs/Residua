import rcic.RcicF3RoleNat
import rcic.RcicF3RoleGroup
import rcic.RcicF3RoleIota
import rcic.RcicF3PendAFamily
import rcic.RcicF3KTWRecA

/-!
# Full role-model obligations at the admitted PendA W group

This file checks the group that refutes the old finite-stage target.
No witness-shape condition is assumed at the fixture.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace Rcic.F3.PSet.PendARoleW
open Rcic.Declarative

/-- The leaf's direct row and the higher-order constructor's rejected
legacy analysis cover every possible iota witness at this group. -/
theorem witnessRow (j : Fin PendAW.recA.constructors.length) (ks : List RecKind)
    (hk : analyzeFields PendAW.recA.family.ref (PendAW.recA.constructorViews j).fields = some ks) :
    RecFieldsDirect PendAW.recA.family.ref (policyFamilyLevels PendAW.recA.family)
      PendAW.recA.family.parameters.length PendAW.recA.family.indices.length
      (PendAW.recA.constructorViews j).fields 0 := by
  rcases (PendAWGroup.views PendAW.pNode j).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
  · change (PendAW.recA.constructorViews j).fields = [] at hf
    rw [hf]; trivial
  · change (PendAW.recA.constructorViews j).fields = [PendAW.field] at hf
    rw [hf] at hk
    change (none : Option (List RecKind)) = some ks at hk
    cases hk

kernel_rfl_theorem minor0 :
  derivedMinor PendAW.recA ⟨0, by decide⟩ admitFuel
    (shapesOf PendAW.recA.family.ref (PendAW.recA.constructorViews ⟨0, by decide⟩).fields) =
    PendAW.recA.minorTypes[0]?
kernel_rfl_theorem minor1 :
  derivedMinor PendAW.recA ⟨1, by decide⟩ admitFuel
    (shapesOf PendAW.recA.family.ref (PendAW.recA.constructorViews ⟨1, by decide⟩).fields) =
    PendAW.recA.minorTypes[1]?

/-- The class-A structure is constructed at the exact W node. -/
theorem groupA : RecGroupA PendAW.recA where
  bounded := PendAWLim.Typed.bounded
  famFree := PendAWLim.Typed.paramsFree
  fields := fun i => PendAWLim.Typed.classes _
    (List.getElem?_mem (famDataOf_ctor PendAW.recA i))
  riFree := fun i e he => PendAWLim.Typed.indicesFree _
    (List.getElem?_mem (famDataOf_ctor PendAW.recA i)) e he
  opq := fun _ => rfl
  shapes := fun i => by
    obtain ⟨i, hi⟩ := i
    change i < 2 at hi
    match i, hi with
    | 0, _ => exact ⟨admitFuel, minor0⟩
    | 1, _ => exact ⟨admitFuel, minor1⟩


/-- Recursor membership at the literal W node, using the replacement
family entry rather than a finite-stage bridge. -/
theorem memberSound (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    (X : RoleModel.RecStepCtx famKT P K PendAW.fam PendAW.pNode μ) :
    MemberSound P μ K 7 PendAW.recMem := by
  have hcl := (X.facts _ _ X.rmem).1
  have hlvl := (X.facts _ _ X.rmem).2.1
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [X.rbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ PendAW.recMem.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (X.faith.recur _).symm ?_
  exact recVal_mem_rec_KTA P μ PendAW.recA groupA (ls.map (evalTotal σ))
    (PendAWLim.Typed.nonIR P μ) PendAWLim.Typed.fresh X.lim
    (groupFaith_ctorAt P X.faith _) (PendAWLim.Typed.typeRead _)


/-- The old higher-order witness cannot occur; every actual legacy witness
still satisfies semantic iota in every final environment. -/
theorem package (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv)
    (μ : Nat → List Nat → PSet.{4})
    (X : RoleModel.RecStepCtx famKT P K PendAW.fam PendAW.pNode μ) :
    RecPkgAt P μ K Efin PendAW.eAll 7 PendAW.recMem := by
  intro hsub
  exact ⟨memberSound P K μ X,
    RoleModel.iota_type_of_witness_row P X.faith hsub X.rmem witnessRow
      PendAWLim.Typed.typeRead X.lvC⟩

/-- Fixed-point transport at a faithful replacement table. -/
theorem fixed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hKT : ∀ vs, Equiv (μ PendAW.recA.family.ref vs)
      (famKT P μ (famDataOf PendAW.recA) vs)) (vs : List Nat) :
    Equiv (famKT P μ (famDataOf PendAW.recA) vs)
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf PendAW.recA)) :=
  (PendAFamily.fixed P μ vs).symm.trans
    (famVal_tables P (tabKT_equiv P μ PendAW.recA hKT) _ _)

/-- Full group-step instance at the very group refuting the old target.
This is elementary composition of the fixed-point and recursor consumers. -/
theorem groupStep (P : Premises4) (K : Nat → Nat) :
    RoleModel.GroupStepAt famKT P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT := by
  exact RoleModel.stepAt_node famKT P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT PendAW.pNode PendAWGroup.scanHit
    (fixed P) (package P K)

/-- The repaired full group step at this fixture cannot reproduce the
landed contradiction, for the supplied model data. -/
theorem groupStep_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (RoleModel.GroupStepAt famKT P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT → (Premises4 → False)) := by
  intro h
  exact h (groupStep P K) P


/-- Full repaired invariant at the same W group and bounds used in
`PendAWGroup.stepAG_false`; the predecessor invariant is produced. -/
theorem gInv (P : Premises4) (k : Nat) :
    RoleModel.GInv famKT P (fun _ => k) PendAWGroup.wft :=
  groupStep P (fun _ => k) PendAWGroup.walkAgree (PendAWGroup.boundG _)
    (PendAWGroup.boundDG k) (RoleNat.gInv P _)

/-- The full invariant, not merely family closure, is non-refutable here.
This is a fixture certificate, not the universal PendA producer. -/
theorem gInv_nonrefutable (P : Premises4) (k : Nat) :
    ¬ (RoleModel.GInv famKT P (fun _ => k) PendAWGroup.wft → (Premises4 → False)) := by
  intro h
  exact h (gInv P k) P

theorem reads (P : Premises4) :
    RoleModel.FamilyReads famKT P PendAWBridge.fd := by
  intro μ₁ μ₂ S h hpi hfam vs
  exact famKT_agreeOn (ar := 0) P
    (fun r hr ls => by rw [h r hr ls]; exact Equiv.rfl)
    (PendAWLim.Typed.nonIR P μ₁) (PendAWLim.Typed.nonIR P μ₂)
    hpi PendAWLim.Typed.indicesFree hfam PendAWLim.Typed.classes vs

theorem readsCtx (P : Premises4) :
    RoleModel.FamilyReadsCtx famKT P (envCtx PendAWGroup.wft) := by
  have hc : envCtx PendAWGroup.wft =
      groupRoles PendAWBridge.fd 4 7 (envCtx natEnvUWfT) :=
    envCtx_group_some (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
      natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT _ PendAWGroup.scanHit
  rw [hc]
  exact RoleModel.familyReadsCtx_groupRoles (RoleNat.readsCtx P) (reads P)

/-- An actual table for the exact admitted W environment, independent of
any A-axis step hypothesis. -/
noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  RoleModel.envTable famKT P (envCtx PendAWGroup.wft) PendAWGroup.wft

theorem faithful (P : Premises4) :
    RoleModel.Faithful famKT P (table P) (envCtx PendAWGroup.wft) PendAW.eAll :=
  (RoleModel.faithful_envTable famKT P _ (readsCtx P) PendAWGroup.wft
    (readsOKAlong_envCtxW PendAWGroup.wft PendAWGroup.walkG _ (fun _ _ => rfl))).1

/-- Soundness at a concrete faithful replacement table, rather than an
implication whose faithfulness antecedent has no witness. -/
theorem canonicalSound (P : Premises4) (k : Nat) :
    AllSound P (table P) (fun _ => k) PendAW.eAll :=
  ((gInv P k) _ (fun _ _ => rfl) (table P) (faithful P)).1

theorem familyValue (P : Premises4) :
    Equiv (table P 4 []) (famKT P (table P) PendAWBridge.fd []) := by
  have h := faithful P 4 PendAW.fam (by rfl) []
  rw [PendAWGroup.familyRole] at h
  exact h

/-- The canonical faithful table itself contains the exact height-omega
value excluded by the landed finite-stage interpretation. -/
theorem canonicalHeightOmega (P : Premises4) :
    fxZW P ∈ El (fapps (table P 4 []) [tyv fxS]) :=
  mem_congr_right (el_congr (fapps_congr (familyValue P) [tyv fxS])).symm
    (PendAFamily.heightOmega P (table P))

/-- The recursor consumer's context is inhabited at the canonical W table,
with all its scope, fixed-point, freshness and typing fields paid. -/
theorem context (P : Premises4) (k : Nat) :
    RoleModel.RecStepCtx famKT P (fun _ => k) PendAW.fam PendAW.pNode (table P) := by
  have hTF : TypeFacts PendAW.eAll := typeFacts_of_envWfT PendAWGroup.wft
  have hlim : ∀ vs, Equiv (table P 4 vs) (famKT P (table P) PendAWBridge.fd vs) := by
    intro vs
    have h := faithful P 4 PendAW.fam rfl vs
    rw [PendAWGroup.familyRole] at h
    exact h
  have hctx : ∀ r, Dom PendAW.eAll r → envCtx PendAWGroup.wft r =
      groupRoles PendAWBridge.fd 4 7 (envCtx natEnvUWfT) r := by
    intro r _
    exact congrFun (envCtx_group_some (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
      natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT _ PendAWGroup.scanHit) r
  have hG := RoleModel.groupFaith_of famKT P PendAW.membersT rfl rfl
    PendAW.pNode (faithful P) hctx hTF (fixed P (table P) hlim)
  have hsub : ∀ r m, PendAW.eFam.members r = some m → PendAW.eAll.members r = some m := by
    intro r m hr
    change (extendEnv natEnvU 4 PendAW.fam).members r = some m at hr
    by_cases he : r = 4
    · subst he; rw [members_extend_eq] at hr; cases hr; rfl
    · rw [members_extend_ne natEnvU 4 PendAW.fam r he] at hr
      exact Rcic.Model.PS.groupMembersT_preserve PendAW.membersT r m hr
  have hI := ((gInv P k) _ (fun _ _ => rfl) (table P) (faithful P)).2
    PendAW.eAll (fun _ _ h => h)
  refine ⟨hG, hlim, ?_, hTF, PendAWLim.Typed.paramsFree, rfl, rfl, ?_⟩
  · intro σ n
    exact envSound_of P hsub (fun r m h => canonicalSound P k r m (hsub r m h))
      (fun r m h hk => hI r m (hsub r m h) hk) σ n
  · intro i
    have h := (hTF _ _ (node_ctor_member PendAW.pNode i)).2.1
    rw [(PendAW.pNode.a.constructorViews i).arity] at h
    exact h

end Rcic.F3.PSet.PendARoleW
