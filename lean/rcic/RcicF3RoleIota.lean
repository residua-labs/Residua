import rcic.RcicF3StepAObstr
import rcic.RcicF3PendAWGroup

/-!
# Type-level iota from the witness's own analyzable row

The row is demanded only for constructors accepted by `analyzeFields`.
This is not the refuted global `WitDirect` premise: the admitted PendA W
node discharges it, since its higher-order constructor has no such legacy
witness while its leaf constructor has an empty row. The actual semantic
iota equality and its sound-typing antecedents are retained.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RoleModel
open Rcic.Declarative

theorem iota_type_of_witness_row (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E E' Efin : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember}
    {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m)
    (hrm : E'.members rr = some rm)
    (hrow : ∀ (j : Fin node.a.constructors.length) (ks : List RecKind),
      analyzeFields node.a.family.ref (node.a.constructorViews j).fields = some ks →
      RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
        node.a.family.parameters.length node.a.family.indices.length
        (node.a.constructorViews j).fields 0)
    (hType : ∀ σ, evalTotal σ node.a.family.resultLevel ≠ 0)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true) :
    IotaAt P μ K Efin rr := by
  intro E'' hsub w hwr σ n Γ T ρ hl il hN hr hrs hls hfit ml mr
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨hnp, hnM, _, hfr⟩ := iota_align node.a w hwr hm
  have hjk : w.ctorIdx < node.a.constructors.length := by have := w.hidx; omega
  let j : Fin node.a.constructors.length := ⟨w.ctorIdx, hjk⟩
  have hcref : w.ctorRef = node.a.family.ref + 1 + j.val := by rw [w.hctorIdx, hfr]
  have hcm : w.ctorMember = node.a.constructors[j.val] := by
    have h1 := hsub _ _ w.hctor
    have h2 := node.a.constructorsPresent j
    have h3 := hsubF _ _ (node.sub _ _ (members_extend_preserved node.fresh _ _ h2))
    rw [hcref] at h1
    rw [h1] at h3
    exact Option.some.inj h3
  -- the direct-fields row at the witness's own constructor
  have hrf : RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length
      (node.a.constructorViews j).fields 0 := by
    have hst := (node.a.constructorViews j).storedType
    have hcpl := (node.a.constructorViews j).parameterCount
    have hctm : w.ctorMember.mtype = policyPi ((node.a.constructorViews j).parameters ++
        (node.a.constructorViews j).fields)
        (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
          (policyParameterLocals (node.a.constructorViews j).parameters.length
            (node.a.constructorViews j).fields.length ++
            (node.a.constructorViews j).resultIndices)) := by rw [hcm]; exact hst
    have hnpar := w.hnpar
    rw [hctm, PSet.piCount_policyPi, PSet.piCount_foldApps _ (fun _ _ h => Expr.noConfusion h),
      List.length_append] at hnpar
    have hpeel := w.hpeel
    rw [hctm, show w.nparams + w.fields.length = ((node.a.constructorViews j).parameters ++
      (node.a.constructorViews j).fields).length by rw [List.length_append]; omega,
      PSet.peelPis_policyPi] at hpeel
    have hdoms : w.ctorDoms = (node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields :=
      (congrArg Prod.fst (Option.some.inj hpeel)).symm
    have hkinds := w.hkinds
    rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
    exact hrow j w.kinds hkinds
  have huni : evalTotal (σOf (w.ls.map (evalTotal σ))) node.a.family.resultLevel = 0 ↔
      evalTotal (σOf (w.lsC.map (evalTotal σ))) node.a.family.resultLevel = 0 := by
    rcases selection_uniform node.a with hp | ht
    · exact ⟨fun _ => hp _, fun _ => hp _⟩
    · exact ⟨fun h => absurd h (Nat.pos_iff_ne_zero.mp (ht _)),
        fun h => absurd h (Nat.pos_iff_ne_zero.mp (ht _))⟩
  have hctor0 := hG.ctor j (w.lsC.map (evalTotal σ))
  rw [nfOf_famDataOf] at hctor0
  have e : w.ctorRef = f + 1 + j.val := by rw [hcref, node.fam]
  have hctor : Equiv (μ w.ctorRef (w.lsC.map (evalTotal σ)))
      (piLam (mkM P μ) (σOf (w.lsC.map (evalTotal σ))) (ctorEnd (mkM P μ) (σOf (w.lsC.map (evalTotal σ)))
        (famDataOf node.a) j.val (node.a.constructorViews j).fields.length) (fun _ => pempty)
        (node.a.constructors[j.val]).mtype) := by rw [e]; exact hctor0
  exact iota_group W4 node.a w hwr hm σ ρ (hG.recur _) (groupFaith_famAt P hG _) j rfl hcm hctor huni
    hrf (hlvC j)
    (fun h0 _ => (hType _ h0).elim)
    (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) ml mr


end Rcic.F3.PSet.RoleModel
