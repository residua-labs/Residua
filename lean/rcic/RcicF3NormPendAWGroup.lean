import rcic.RcicF3NormPendAWRecPkg
import rcic.RcicF3NormCandidatePrefix

/-!
# Full normalized-role group step at the exact admitted PendA W fixture

The small closed data frame and the recursor package are produced at this
fixture. The stored constructors are checked along their actual bounded
walk, including their own parameter cuts, with the new predecessor
invariant supplying earlier environment soundness. No old invariant is
assumed, and there is no comparison between constructor and recursor bounds.

The public GroupStepAt retains its literal walk, BoundG, BoundDG and new
predecessor inputs. It is a fixture instance, not universal StepAG or an
unconditional GInv of the predecessor. Its stable IotaAt conjunct has the
unchanged legacy witness scope explained in NormPendAWRecPkg.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAWGroup
open Rcic.Declarative Rcic.Model.PS RawFamilyGroup

/-- Compose the paid W frame and package at one actual table. Every
constructor-field soundness input comes from the literal bounded walk. -/
theorem at_table (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    (hAg : ∀ node : PendAWGroup.Node,
      WalkAgree (AgreeAt node.a.family.parameters.length) PendAW.membersT)
    (hB : BoundG K PendAWGroup.wft)
    (hV : GroupValues P μ PendAW.fam PendAW.pNode)
    (hPrior : AllSound P μ K natEnvU)
    (hPriorIota : ∀ Efin,
      (∀ r m, PendAW.eAll.members r = some m → Efin.members r = some m) →
      ∀ r m, natEnvU.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r) :
    AllSound P μ K PendAW.eAll ∧
      ∀ Efin, (∀ r m, PendAW.eAll.members r = some m → Efin.members r = some m) →
        ∀ r m, PendAW.eAll.members r = some m → m.mclass = .recursorM →
          IotaAt P μ K Efin r := by
  have hTF := typeFacts_of_envWfT PendAWGroup.wft
  have hL : ([(5, PendAW.leaf), (6, PendAW.node)].map Prod.fst) =
      (List.range ([(5, PendAW.leaf), (6, PendAW.node)].length)).map
        (fun i => 4 + 1 + i) := rfl
  have hrr : 7 = 4 + 1 + [(5, PendAW.leaf), (6, PendAW.node)].length := rfl
  have hf : PendAW.eAll.members 4 = some PendAW.fam := rfl
  have hlim : ∀ vs, Equiv (μ PendAW.recA.family.ref vs)
      (RawFamily.role P μ (famDataOf PendAW.recA) vs) := hV.fam
  have hG : GroupFaith P μ PendAW.fam PendAW.pNode :=
    hV.toLegacy P (RawWGeneral.fixed P μ hlim)
  have hfmS : MemberSound P μ K 4 PendAW.fam :=
    fam_member_sound P PendAWBridge.fd hG.fam hG.famTy
      (hTF 4 PendAW.fam hf).1 (hTF 4 PendAW.fam hf).2.1 rfl
  have hPkg := NormPendAWRecPkg.rec_pkg_of_values P K μ hV
  have hIall : ∀ Efin,
      (∀ r m, PendAW.eAll.members r = some m → Efin.members r = some m) →
      ∀ r m, PendAW.eAll.members r = some m → m.mclass = .recursorM →
        IotaAt P μ K Efin r := by
    intro Efin hsub r m hm hk
    rcases group_member_cases PendAW.membersT hL hrr PendAW.pNode hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact hPriorIota Efin hsub r m hold hk
    · cases hk
    · exact hPkg.2 Efin hsub
    · rw [(PendAW.pNode.a.constructorViews i).hasClass] at hk
      cases hk
  have hScope : ∀ σ n, EnvSound (mkM P μ) σ K PendAW.eFam n :=
    NormCandidatePrefix.frame_prefix_envSound P K μ natEnvUWfT rfl
      PendAW.membersT PendAW.pNode hPrior (hPriorIota PendAW.eAll (fun _ _ h => h))
      (RawFamily.frame P μ PendAWBridge.fd) (RawWFrame.raw_admissible P μ) hlim
  have hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (famO : PolicyFamilyView Ew) (cv : PolicyConstructorView Ew famO m),
      (r, m) ∈ PendAW.slots → Ew.members r = none →
      FieldUniverseAdmitted cv →
      AgreeAt PendAW.pNode.a.family.parameters.length Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity →
        (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity
            (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)),
            LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' →
        PendAW.eAll.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m := by
    intro Ew r m famO cv hin hfresh h07 hagc hB2w hsubw hAw
    have hEw : ∀ r' m', Ew.members r' = some m' →
        PendAW.eAll.members r' = some m' := fun r' m' h =>
      hsubw r' m' (members_extend_preserved hfresh r' m' h)
    have hkC : m.mclass = .constructorM := cv.hasClass
    have hctor : ∃ i : Fin PendAW.pNode.a.constructors.length,
        r = 4 + 1 + i.val ∧ m = PendAW.pNode.a.constructors[i.val] := by
      change (r, m) ∈ [(4, PendAW.fam), (5, PendAW.leaf),
        (6, PendAW.node), (7, PendAW.recMem)] at hin
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hin
      rcases hin with h | h | h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        cases hkC
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨⟨0, by change 0 < 2; decide⟩, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨⟨1, by change 1 < 2; decide⟩, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        cases hkC
    obtain ⟨i, rfl, rfl⟩ := hctor
    have hESw : ∀ σ n, EnvSound (mkM P μ) σ K Ew n := by
      intro σ n
      exact envSound_of P (Efin := PendAW.eAll) hEw hAw
        (fun r m hm hk => hIall PendAW.eAll (fun _ _ h => h)
          r m (hEw r m hm) hk) σ n
    exact RawFamilyWalk.constructor_at_walk P μ K PendAW.pNode i famO cv hEw
      (RawFamily.frame P μ PendAWBridge.fd) (RawWFrame.raw_admissible P μ)
      (RawFamilyInductionAttack.w_closed P μ) hlim (hV.ctor i) hTF
      (PSet.groupMembersT_body_none PendAW.membersT _ _
        (node_ctor_mem PendAW.membersT hL hrr PendAW.pNode i))
      h07 hagc hScope hESw (hB.2.1 PendAW.pNode i) hB2w
  have hAll : AllSound P μ K PendAW.eAll := by
    refine walk_sound P μ K PendAW.slots
      (AgreeAt PendAW.pNode.a.family.parameters.length) ?_ ?_ hfmS hPkg.1 hcS
      PendAW.membersT (fun _ h => h) (fun _ _ h => h)
      (walkRec_of_group PendAW.membersT) (hAg PendAW.pNode) hB.2.2.1 hPrior
    · intro c hc hk
      change c ∈ [(4, PendAW.fam), (5, PendAW.leaf),
        (6, PendAW.node), (7, PendAW.recMem)] at hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · rfl
      · cases hk
      · cases hk
      · cases hk
    · intro c hc hk
      change c ∈ [(4, PendAW.fam), (5, PendAW.leaf),
        (6, PendAW.node), (7, PendAW.recMem)] at hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · cases hk
      · cases hk
      · cases hk
      · rfl
  exact ⟨hAll, hIall⟩

/-- Full fixture instance of the new canonical group-step target. All
semantic W components are produced; the predecessor is the new invariant. -/
theorem group_step (P : Premises4) (K : Nat → Nat) :
    NormRole.GroupStepAt P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT := by
  intro hAg hB _hBD hPred
  intro ctx hctx plans hplans μ hF
  have hsubE : ∀ r m, natEnvU.members r = some m → PendAW.eAll.members r = some m :=
    groupMembersT_preserve PendAW.membersT
  have hctxE : ∀ r, Dom natEnvU r → ctx r = NormRole.envCtx natEnvUWfT r := by
    intro r hr
    exact (hctx r (dom_groupMembersT PendAW.membersT hr)).trans
      (NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
        PendAW.membersT r hr)
  have hplansE : ∀ r, Dom natEnvU r → plans r = EvalRole.envPlan natEnvUWfT r := by
    intro r hr
    exact (hplans r (dom_groupMembersT PendAW.membersT hr)).trans
      (EvalRole.envPlan_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
        PendAW.membersT r hr)
  have hFE : EvalRole.Faithful RawFamily.role P μ ctx plans natEnvU :=
    fun r m hm => hF r m (hsubE r m hm)
  have hPrior := hPred ctx hctxE plans hplansE μ hFE
  have hV := NormPendAWRecPkg.values P μ ctx plans hctx hplans hF
  exact at_table P K μ hAg hB hV hPrior.1 (fun Efin hsub =>
    hPrior.2 Efin (fun r m hm => hsub r m (hsubE r m hm)))

def Witness (P : Premises4) : Prop :=
  NormPendAWRecPkg.Witness P ∧
  (∀ K, NormRole.GroupStepAt P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPendAWRecPkg.component_witness P, group_step P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPendAWGroup
