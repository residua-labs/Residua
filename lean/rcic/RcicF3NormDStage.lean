import rcic.RcicF3NormRoleTransfer
import rcic.RcicF3StepDGRec

/-!
# Bounded D stages from the normalized predecessor invariant

This adapts the factored D-stage kernel in #8459 (head 74e586d9), retaining
its original raw stage tables and bounded normalization derivations. The
actual table's family soundness is received directly; no all-instance raw
famLim comparison is required. The normalized predecessor is reapplied at
each fresh family update using its produced role and indexed-plan reads.

The family member premise is explicit here. The normalized finite-frame
producer discharges it in the group adapter; this kernel alone is not a
checked group step or universal A producer. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDStage
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder

def TableSound (P : Premises4) (K : Nat → Nat) (E : ResolvedEnv)
    (μ : Nat → List Nat → PSet.{4}) : Prop :=
  AllSound P μ K E ∧ ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
    ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

section
variable {P : Premises4} {K : Nat → Nat} {E E' : ResolvedEnv} {f rr : Nat}
  {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}

theorem stage_of_tables (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hsh : NoFunRec node)
    (hpar : ∀ i : Fin node.a.constructors.length, (node.a.constructorViews i).parameters = node.a.family.parameters)
    (hBG : BoundG K hE)
    (hDG : ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
        ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level,
          ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
            (policyPrefixContext ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)
              ((node.a.constructorViews i).parameters.length + k.val))
            ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d)
    (BaseOK : (Nat → List Nat → PSet.{4}) → Prop)
    (hBase : ∀ T, BaseOK T → TableSound P K E T)
    (μ : Nat → List Nat → PSet.{4}) (hμ : BaseOK μ)
    (hStage : ∀ n, BaseOK (tabIter P μ (famDataOf node.a) n))
    (hfmμ : MemberSound P μ K f fm) :
    DStage P K node μ := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  obtain ⟨hf0, _, hf', _, _⟩ := group_refs hmem hL hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := PSet.groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  have hfr : (famDataOf node.a).fref = f := node.fam
  have hFF : FamFreeBodies node.E0 node.a.family.ref := by
    rw [node.fam]; exact famFreeBodies_node hE hf0 hmem node
  have hpfF : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false := by
    intro e he
    refine occurs_false_of_refs e fun r hr hrf => ?_
    have := groupMembersT_head_refs hmem r (by rw [hty]; exact refs_policyPi_dom _ _ e he hr)
    have hrf' : r = f := hrf.trans node.fam
    rw [hrf'] at this
    unfold Dom at this
    rw [hf0] at this
    exact absurd this (by decide)
  have RG : RecGroupD node.a node.h14.fuelAt node.h14.shapesAt := by
    refine ⟨nodeFam_bounded node hTF (node_bodies_levelsBounded0 hE hmem node K hBG), hpfF,
      nodeFam_recApp node hFF hsh, fun i => fieldsClass_of_direct _ 0 (nodeFam_fields_direct node hFF hsh i),
      fun i e he => (node.a.constructorViews i).noFamilyInIndices e he, envClosed_node node hTF, fun i => ?_⟩
    obtain ⟨shapes', fuel', hfs', hdm'⟩ := node.h12 i
    have heq : shapes' = node.h14.shapesAt i := fieldShapesFuel_unique hfs' (node.h14.analyzed i)
    subst heq
    refine ⟨fuel', ?_, hdm'⟩
    have h0 := shapesNorm_of_fieldShapesFuel hFF _ _ _ hfs' (hsh i)
    rwa [normFields_fuel_eq hFF _ _ _ _ hfs' (node.h14.analyzed i) (hsh i) (hsh i)] at h0
  have hcl := (hTF f fm hf').1
  have hlvl := (hTF f fm hf').2.1
  -- the constructor scope is sound at every table faithful on the base where the family member is sound
  have hES : ∀ T : Nat → List Nat → PSet.{4}, BaseOK T → MemberSound P T K f fm →
      ∀ σ n, EnvSound (mkM P T) σ K (extendEnv E f fm) n := by
    intro T hFT hfmS σ n
    have IHT := hBase T hFT
    refine envSound_of P hSsub ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHT.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHT.2 E' hsubE r m h hk
  have hbodies : ∀ σ, BodiesOK (extendEnv E f fm) σ K := fun σ =>
    bodiesOK_of_envWfT K hE hBG (fun r m h => members_extend_preserved hf0 r m h) (fun r m hm h0 => by
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at hm; cases hm; exact hbf
      · rw [members_extend_ne E f fm r hr] at hm; rw [hm] at h0; cases h0) σ
  have hwhnf : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel (extendEnv E f fm) fuel e :=
    whnfFuel_eq_along hmem node.base (node_sub' node) (fun r m h => members_extend_preserved hf0 r m h) hSsub
  have hag : ∀ T : Nat → List Nat → PSet.{4}, BaseOK T → MemberSound P T K f fm →
      ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → vs.length = node.a.family.member.arity →
      AgreeAtD P T node.a (fuelAt := node.h14.fuelAt) vs := fun T hFT hfmS vs hvs hlen =>
    agreeAt_of_typings P T K node vs (hES T hFT hfmS (σOf vs) _) (hbodies (σOf vs)) hwhnf hpar
      (fun i k => hDG i vs hlen hvs k)
  -- the stage tables: faithful on the base, the family member sound by membership
  have hfmT : ∀ n, MemberSound P (tabIter P μ (famDataOf node.a) n) K f fm := by
    intro n
    refine fam_member_sound_of_mem P (fun vs => ?_) hcl hlvl hbf
    have hent : tabIter P μ (famDataOf node.a) n f vs = famIter P μ (famDataOf node.a) n vs := by
      exact if_pos hfr.symm
    rw [hent, hty, show tabIter P μ (famDataOf node.a) n = upd μ (famDataOf node.a).fref
      (famIter P μ (famDataOf node.a) n) from rfl, den_famType_upd P μ _ hpfF, ed_mkM P _ μ]
    exact famIter_mem P μ _ hpfF n vs
  exact ⟨fun n => hag _ (hStage n) (hfmT n), hag μ hμ hfmμ, RG⟩

/-- The same stage kernel at the new predecessor interpretation. Its
read support is produced, including every indexed recursor endpoint. -/
theorem stage_of_invariant (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hsh : NoFunRec node)
    (hpar : ∀ i : Fin node.a.constructors.length, (node.a.constructorViews i).parameters = node.a.family.parameters)
    (hBG : BoundG K hE)
    (hDG : ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
        ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level,
          ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
            (policyPrefixContext ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)
              ((node.a.constructorViews i).parameters.length + k.val))
            ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d)
    (IH : NormRole.GInv P K hE) (ctx : Nat → Role)
    (hc : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (plans : EvalRole.Plans) (hp : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (μ : Nat → List Nat → PSet.{4})
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E)
    (hfmμ : MemberSound P μ K f fm) : DStage P K node μ := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  obtain ⟨hf0, _, _, _, _⟩ := group_refs hmem hL hrr
  have hf0' : E.members (famDataOf node.a).fref = none := by
    change E.members node.a.family.ref = none
    rw [node.fam]
    exact hf0
  exact stage_of_tables hE hfam hctors hrec hmem node hsh hpar hBG hDG
    (fun T => EvalRole.Faithful RawFamily.role P T ctx plans E)
    (fun T hFT => IH ctx hc plans hp T hFT) μ hF
    (fun _ => NormRole.faithful_upd_fresh P hE hc hp hF hf0' _) hfmμ

end
end Rcic.F3.PSet.NormDStage
