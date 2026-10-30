import rcic.RcicF3PendAWLim
import rcic.RcicF3DBoundBridge
import rcic.RcicF3AndFixture
import rcic.RcicF3TierGroup

/-!
# Admitted W group refutes the literal finite-stage StepAG

`wft` is the same admitted, inhabited PendA W group as `PendAW.envWfT`.
The walk, constructor/domain bounds and base invariant required by StepAG
are proved below, for every constant bound. Its canonical faithful table
interprets the family by `famLim`. The valid infinitely branching argument
maps to the height-omega tree, which is absent from that finite-stage fibre.
Thus `gInv_false` and `stepAG_false` refute the existing semantic contract,
conditional on the explicit `Premises4` model data. They do not refute the
object theory or construct its requested soundness producer.

No constructor shape, admission rule or semantic role is changed here.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace Rcic.F3.PSet.PendAWGroup
open Rcic.Declarative
abbrev Node := RecNode natEnvU PendAW.eAll 4 7 PendAW.recMem
theorem familyMember (node : Node) : node.a.family.member = PendAW.fam :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)
kernel_rfl_theorem recFirstDom :
  (recPreDomsOf PendAW.recA ++ [recMajorOf PendAW.recA])[0]? = some (.sort (.succ .zero))
theorem familyInfo (node : Node) :
    node.a.family.parameters = [.sort (.succ .zero)] ∧ node.a.family.indices = [] ∧
    node.a.family.resultLevel = .succ .zero := by
  have hst := node.a.family.storedType
  rw [familyMember node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [.sort (.succ .zero)] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  injection h2 with hrl
  obtain ⟨_, hql⟩ := family_params_of_recType node _ h1
    (recPreDomsOf PendAW.recA ++ [recMajorOf PendAW.recA]) (recResultOf PendAW.recA)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (recType_eq PendAW.recA) 1
    (fun k hk hne e he => by
      cases k with
      | zero =>
        rw [recFirstDom] at he
        cases he
        exact fun _ _ h => Expr.noConfusion h
      | succ k =>
        have hz : k = 0 := by change k + 1 ≤ 1 at hk; omega
        subst hz
        exact (hne rfl).elim)
  have hq := List.eq_nil_of_length_eq_zero hql
  rw [hq, List.append_nil] at h1
  exact ⟨h1.symm, hq, hrl.symm⟩
theorem ctorInfo (node : Node) (i : Fin node.a.constructors.length) :
    (node.a.constructors[i.val] = PendAW.leaf ∧ i.val = 0) ∨
    (node.a.constructors[i.val] = PendAW.node ∧ i.val = 1) := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 2 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Or.inl ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
theorem views (node : Node) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [.sort (.succ .zero)] ∧
    (node.a.constructorViews i).resultIndices = [] ∧
    (((node.a.constructorViews i).fields = [] ∧ i.val = 0) ∨
     ((node.a.constructorViews i).fields = [PendAW.field] ∧ i.val = 1)) := by
  obtain ⟨hP, hI, _⟩ := familyInfo node
  have hpl : (node.a.constructorViews i).parameters.length = 1 := by
    rw [(node.a.constructorViews i).parameterCount, hP]; rfl
  have hri : (node.a.constructorViews i).resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [(node.a.constructorViews i).indexCount, hI]; rfl
  have hst := (node.a.constructorViews i).storedType
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals
      (node.a.constructorViews i).parameters.length (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  rcases ctorInfo node i with ⟨e, h0⟩ | ⟨e, h1⟩
  · have hm : (node.a.constructors[i.val]).mtype =
        policyPi ([.sort (.succ .zero)] ++ []) (.app (.const 4 []) (.bvar 0)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _ (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨hp, hf⟩ := List.append_inj hsp (by rw [hpl]; rfl)
    exact ⟨hp.symm, hri, Or.inl ⟨hf.symm, h0⟩⟩
  · have hm : (node.a.constructors[i.val]).mtype =
        policyPi ([.sort (.succ .zero)] ++ [PendAW.field]) (.app (.const 4 []) (.bvar 1)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _ (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨hp, hf⟩ := List.append_inj hsp (by rw [hpl]; rfl)
    exact ⟨hp.symm, hri, Or.inr ⟨hf.symm, h1⟩⟩
theorem walkClass (node : Node) : WalkClass node.a.family.parameters.length PendAW.membersT := by
  rw [(familyInfo node).1]
  unfold PendAW.membersT PendAW.chain
  simp only [groupMembersT_of_chain]
  repeat rw [walkClass_andRec]
  refine ⟨trivial, ?_⟩
  repeat rw [walkClass_andRec]
  refine ⟨rfl, ?_⟩
  repeat rw [walkClass_andRec]
  refine ⟨rfl, ?_⟩
  repeat rw [walkClass_andRec]
  exact ⟨rfl, trivial⟩
theorem walkAgree (node : Node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) PendAW.membersT :=
  walkAgree_of_walkClass node PendAW.membersT (walkClass node)
theorem ctorClasses : ∀ c ∈ [(5, PendAW.leaf), (6, PendAW.node)], c.2.mclass = .constructorM := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · cases h; rfl
  · have h' := List.mem_singleton.mp h
    cases h'; rfl
def wft : EnvWfT PendAW.eAll :=
  .group natEnvU 4 PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)]
    7 PendAW.recMem PendAW.eAll natEnvUWfT rfl ctorClasses rfl PendAW.membersT
theorem walkG : WalkG wft := by
  exact ⟨walkG_of_classG natEnvUWfT natEnvUWfT_classG.1,
    walkRec_of_walkClass _ PendAW.membersT (walkClass PendAW.pNode), walkAgree⟩
noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  envμR P (envCtx wft) wft
theorem faithful (P : Premises4) : FaithfulR P (table P) (envCtx wft) PendAW.eAll :=
  (faithfulR_envμR P _ wft
    (readsOKAlong_envCtxW wft walkG _ (fun _ _ => rfl))).1
theorem ctorBound (node : Node) (K : Nat → Nat) (σ : Nat → Nat)
    (i : Fin node.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT PendAW.eFam node.a.family.member.arity []
      (node.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 K d := by
  rw [familyMember node]
  rcases ctorInfo node i with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]
    refine ⟨_, .pi [] _ _ _ _ (.sort [] (.succ .zero))
      (.app _ (.const 4 []) (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
        (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 0 _ rfl)), ?_⟩
    simp [LOKt, LevelsOK, evalTotal]
  · rw [e]
    refine ⟨_, .pi [] _ _ _ _ (.sort [] (.succ .zero))
      (.pi _ _ _ _ _
        (.pi _ _ _ _ _ (.bvar _ 0 _ rfl)
          (.app _ (.const 4 []) (.bvar 1) (.sort (.succ .zero)) (.sort (.succ .zero))
            (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 1 _ rfl)))
        (.app _ (.const 4 []) (.bvar 1) (.sort (.succ .zero)) (.sort (.succ .zero))
          (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 1 _ rfl))), ?_⟩
    simp [LOKt, LevelsOK, evalTotal]
def ownBound (K : Nat → Nat) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (adm : IndGroupAdmitted E r m) : Prop :=
  match adm with
  | .constructor family view _ _ _ _ _ => ∀ vs : List Nat, vs.length = family.member.arity →
      (∀ v, v ∈ vs → v ≤ K r) → ∀ k : Fin (view.parameters ++ view.fields).length,
        ∃ d : HasTyT E family.member.arity (policyPrefixContext (view.parameters ++ view.fields) k.val)
          ((view.parameters ++ view.fields)[k.val]) (.sort (view.domainsTyped.levels k)), LOKt (σOf vs) 4 K d
  | _ => True

def ownAt (K σ : Nat → Nat) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (adm : IndGroupAdmitted E r m) (k : Nat) : Prop :=
  match adm with
  | .constructor family view _ _ _ _ _ =>
      if hk : k < (view.parameters ++ view.fields).length then
        ∃ d : HasTyT E family.member.arity (policyPrefixContext (view.parameters ++ view.fields) k)
          ((view.parameters ++ view.fields)[k]) (.sort (view.domainsTyped.levels ⟨k, hk⟩)), LOKt σ 4 K d
      else True
  | _ => True
def ownLength {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (adm : IndGroupAdmitted E r m) : Nat :=
  match adm with
  | .constructor _ view _ _ _ _ _ => (view.parameters ++ view.fields).length
  | _ => 0
kernel_rfl_theorem leafLength : ownLength PendAW.leafAdm = 1
kernel_rfl_theorem nodeLength : ownLength PendAW.nodeAdm = 2
kernel_rfl_theorem leafAt0Eq : (fun K σ : Nat → Nat => ownAt K σ PendAW.leafAdm 0) =
  (fun K σ => ∃ d : HasTyT PendAW.eFam 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))), LOKt σ 4 K d)
kernel_rfl_theorem nodeAt0Eq : (fun K σ : Nat → Nat => ownAt K σ PendAW.nodeAdm 0) =
  (fun K σ => ∃ d : HasTyT PendAW.eLeaf 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))), LOKt σ 4 K d)
kernel_rfl_theorem nodeAt1Eq : (fun K σ : Nat → Nat => ownAt K σ PendAW.nodeAdm 1) =
  (fun K σ => ∃ d : HasTyT PendAW.eLeaf 0 [.assumption (.sort (.succ .zero))]
    PendAW.field (.sort (.imax (.succ .zero) (.succ .zero))), LOKt σ 4 K d)
theorem ownBound_of_at (K : Nat → Nat) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (adm : IndGroupAdmitted E r m) (h : ∀ vs k, ownAt K (σOf vs) adm k) : ownBound K adm := by
  cases adm <;> try trivial
  intro vs _ _ k
  exact (dif_pos k.isLt).mp (h vs k.val)
theorem ownAt_ge (K σ : Nat → Nat) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (adm : IndGroupAdmitted E r m) (k : Nat) (h : ownLength adm ≤ k) : ownAt K σ adm k := by
  cases adm <;> try trivial
  exact (dif_neg (Nat.not_lt.mpr h)).mpr trivial
theorem leafBound (K : Nat → Nat) : ownBound K PendAW.leafAdm := by
  apply ownBound_of_at
  intro vs k
  cases k with
  | zero =>
    rw [congrFun (congrFun leafAt0Eq K) (σOf vs)]
    exact ⟨.sort [] (.succ .zero), (by decide : 2 ≤ 4)⟩
  | succ k => exact ownAt_ge _ _ _ _ (leafLength ▸ Nat.succ_le_succ (Nat.zero_le k))
theorem nodeBound (K : Nat → Nat) : ownBound K PendAW.nodeAdm := by
  apply ownBound_of_at
  intro vs k
  cases k with
  | zero =>
    rw [congrFun (congrFun nodeAt0Eq K) (σOf vs)]
    exact ⟨.sort [] (.succ .zero), (by decide : 2 ≤ 4)⟩
  | succ k =>
    cases k with
    | zero =>
      rw [congrFun (congrFun nodeAt1Eq K) (σOf vs)]
      refine ⟨.pi _ _ _ _ _ (.bvar _ 0 _ rfl)
        (.app _ (.const 4 []) (.bvar 1) (.sort (.succ .zero)) (.sort (.succ .zero))
          (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 1 _ rfl)), ?_⟩
      simp [LOKt, LevelsOK, evalTotal]
    | succ k => exact ownAt_ge _ _ _ _ (nodeLength ▸ Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))
theorem walkBound (K : Nat → Nat) : WalkB2 K PendAW.membersT := by
  unfold PendAW.membersT PendAW.chain
  simp only [groupMembersT_of_chain]
  repeat rw [walkB2_andRec]
  refine ⟨trivial, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨leafBound K, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨nodeBound K, ?_⟩
  repeat rw [walkB2_andRec]
  exact ⟨trivial, trivial⟩
theorem boundG (K : Nat → Nat) : BoundG K wft := by
  refine ⟨natEnvUWfT_classG.2 K, fun node i vs _ _ => ctorBound node K (σOf vs) i,
    walkBound K, fun node hu _ _ _ _ _ => ?_⟩
  rw [(familyInfo node).2.2] at hu
  exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)
theorem recBelow (k : Nat) : RecBelowCtors (fun _ => k) wft := by
  exact ⟨⟨trivial, fun _ _ _ => Nat.le_refl k⟩, fun _ _ _ => Nat.le_refl k⟩
theorem boundDG (k : Nat) : BoundDG (fun _ => k) wft :=
  boundDG_of_boundG _ wft (recBelow k) (boundG _)
theorem groupInv_of_step (P : Premises4) (k : Nat) (h : TierGroup.StepAG P (fun _ => k)) :
    GInv P (fun _ => k) wft :=
  h natEnvUWfT rfl ctorClasses rfl PendAW.membersT ⟨PendAW.pNode, PendAW.pendA⟩
    walkAgree (boundG _) (boundDG k) (TierGroup.gInv_natEnvU P _)
kernel_rfl_theorem scanHit : scanRec PendAW.membersT = some PendAWBridge.fd
theorem familyRole : envCtx wft 4 = .fam PendAWBridge.fd := by
  unfold wft
  rw [envCtx_group_some natEnvUWfT rfl ctorClasses rfl PendAW.membersT _ scanHit]; rfl
theorem nodeRole : envCtx wft 6 = .ctor PendAWBridge.fd 1 := by
  unfold wft
  rw [envCtx_group_some natEnvUWfT rfl ctorClasses rfl PendAW.membersT _ scanHit]; rfl
theorem familyValue (P : Premises4) :
    Equiv (table P 4 []) (famLim P (table P) PendAWBridge.fd []) := by
  have h := faithful P 4 PendAW.fam rfl []
  rw [familyRole] at h
  exact h
theorem nodeValue (P : Premises4) :
    Equiv (table P 6 []) (piLam (mkM P (table P)) fxσ
      (ctorEnd (mkM P (table P)) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1)) ρ0 PendAW.node.mtype) := by
  have h := faithful P 6 PendAW.node rfl []
  rw [nodeRole] at h
  exact h
noncomputable abbrev fibre (P : Premises4) : PSet.{4} := El (fapps (table P 4 []) [tyv fxS])
theorem fibreEq (P : Premises4) : Equiv (fibre P)
    (iterPhiUnion P (table P) PendAWBridge.fd fxσ PendAWBridge.rp) :=
  (el_congr (fapps_congr (familyValue P) [tyv fxS])).trans
    (PendAWLim.Typed.famFiberEq P (table P))
theorem fibreNoEmpty (P : Premises4) : pempty ∉ fibre P := by
  intro h
  obtain ⟨n, hn⟩ := mem_iUnionN.mp (mem_congr_right (fibreEq P) h)
  exact iterPhi_ne (n+1) fxσ PendAWBridge.rp pempty hn Equiv.rfl
theorem fibreEd (P : Premises4) :
    Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) = fibre P :=
  ed_of_dich _ (Or.inr (fibreNoEmpty P))
theorem graphFit (P : Premises4) : graphOf (fxDomBig P) (fxhW P) ∈
    Ed (mkM P (table P)) (den (mkM P (table P)) fxσ PendAWBridge.rp PendAW.field) := by
  have hg : graphOf (fxDomBig P) (fxhW P) ∈ piSet (fxDomBig P) (fun _ => fibre P) := by
    refine graph_mem_piSet (B := fun _ => fibre P) (fun _ _ _ => Equiv.rfl) _ ?_
    intro i
    rw [fx_hW_beta P i]
    exact mem_congr_right (fibreEq P).symm
      (mem_congr_right (PendAWBridge.unionEq P (table P)).symm (fxT_mem_iUnionN P _))
  change graphOf (fxDomBig P) (fxhW P) ∈ Ed (mkM P (table P))
    (piVal (mkM P (table P)) (tyv fxS) (fun _ => fapps (table P 4 []) [tyv fxS]))
  apply mem_congr_right (ed_piVal_of_noEmpty (mkM P (table P))
    (A := tyv fxS) (B := fun _ => fapps (table P 4 []) [tyv fxS]) (fun _ _ _ => Equiv.rfl) (fun _ _ => by rw [fibreEd]; exact fibreNoEmpty P)).symm
  have hd : Equiv (fxDomBig P) (Ed (mkM P (table P)) (tyv fxS)) := by
    rw [fx_domBig_eq P]
    exact el_tyv.trans (ed_tyv (mkM P (table P)) fx_dich).symm
  exact mem_congr_right (piSet_congr hd (fun _ _ _ => by rw [fibreEd]; exact Equiv.rfl)) hg
theorem ctorArgsFit (P : Premises4) : TelFits (mkM P (table P)) fxσ
    [.sort (.succ .zero), PendAW.field] ρ0 [tyv fxS, graphOf (fxDomBig P) (fxhW P)] :=
  ⟨(PendAWBridge.argsFit P (table P) pempty).1, graphFit P, trivial⟩
theorem nodeApplied (P : Premises4) :
    Equiv (fapps (table P 6 []) [tyv fxS, graphOf (fxDomBig P) (fxhW P)]) (fxZW P) := by
  have hp := fapps_piLam (mkM P (table P)) fxσ
    (ctorEnd_resp (mkM P (table P)) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1))
    (.app (.const 4 []) (.bvar 1)) [.sort (.succ .zero), PendAW.field]
    ρ0 [tyv fxS, graphOf (fxDomBig P) (fxhW P)] (ctorArgsFit P)
  change Equiv (fapps (piLam (mkM P (table P)) fxσ
      (ctorEnd (mkM P (table P)) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1))
      ρ0 PendAW.node.mtype) [tyv fxS, graphOf (fxDomBig P) (fxhW P)])
    (ctorEnd (mkM P (table P)) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1)
      (push [tyv fxS, graphOf (fxDomBig P) (fxhW P)] ρ0)) at hp
  have he : ctorEnd (mkM P (table P)) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1)
      (push [tyv fxS, graphOf (fxDomBig P) (fxhW P)] ρ0) = fxZW P := by
    unfold ctorEnd
    rw [PendAWBridge.fdExact, cond_neg (by decide : evalTotal fxσ (.succ .zero) ≠ 0)]
    rfl
  rw [he] at hp
  exact (fapps_congr (nodeValue P) _).trans hp
theorem gInv_false (P : Premises4) (k : Nat) : ¬ GInv P (fun _ => k) wft := by
  intro hi
  have hs := (hi (envCtx wft) (fun _ _ => rfl) (table P) (faithful P)).1
  have hc := (hs 6 PendAW.node rfl fxσ [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1
  rw [instantiateLevels_nil] at hc
  have hm := mem_fapps (mkM P (table P)) fxσ (.app (.const 4 []) (.bvar 1))
    [.sort (.succ .zero), PendAW.field] ρ0 (table P 6 [])
    [tyv fxS, graphOf (fxDomBig P) (fxhW P)] hc (ctorArgsFit P)
  change fapps (table P 6 []) [tyv fxS, graphOf (fxDomBig P) (fxhW P)] ∈
    Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) at hm
  rw [fibreEd] at hm
  have hz : fxZW P ∈ fibre P := mem_congr_left (nodeApplied P) hm
  exact (PendAWBridge.heightOmega P (table P)).2 (mem_congr_right (fibreEq P) hz)
/-- The literal finite-stage-role StepAG is false, even with all its group inputs paid. -/
theorem stepAG_false (P : Premises4) (k : Nat) : ¬ TierGroup.StepAG P (fun _ => k) :=
  fun h => gInv_false P k (groupInv_of_step P k h)
end Rcic.F3.PSet.PendAWGroup
