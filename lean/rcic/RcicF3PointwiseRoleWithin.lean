import rcic.RcicF3PointwiseRoleConsumer
import rcic.RcicAnnEnvBridgeGroup

/-!
# Pointwise soundness inside one admitted completion

This module leaves `PointwiseRole.GInv`, `IotaAt`, `RecPkgAt`, every old
bound, and every root theorem unchanged. `GInvWithin` fixes the ambient
environment before an admission induction, requires its `EnvWfT` evidence,
and asks for exactly the original `AllSound` and original `IotaAt` at that
environment. The singleton proof and the final fundamental consumer use
these obligations directly; neither uses an old/new invariant equality.

The group lemmas transport the actual predecessor metadata and assemble
the actual member cases from a fixed-completion recursor package. They do
not produce an unrestricted group package or indexed semantic coherence.
No universal A producer or root theorem is asserted. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRole
open Rcic.Declarative Rcic.Model.PS
open Rcic.Declarative.Ann (EnvSub)

/-- The original pointwise obligations, with one admitted completion
fixed for the whole construction. The inclusion premise is consumed at
each prefix and transported backwards along actual admission steps. -/
def GInvWithin (P : Premises4) (K : Nat → Nat) (F : ResolvedEnv)
    (_hF : EnvWfT F) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  EnvSub E F →
  ∀ α : Arities, AritiesAgree α E →
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = NormRole.envCtx hW r) →
  ∀ plans : EvalRole.Plans, (∀ r, Dom E r → plans r = EvalRole.envPlan hW r) →
  ∀ μ, EvalRole.Faithful (familyValue α) P μ ctx plans E →
    AllSound P μ K E ∧
      ∀ r m, E.members r = some m → m.mclass = .recursorM →
        IotaAt P μ K F r

/-- Restriction of the old, stronger arbitrary-extension invariant. -/
theorem gInvWithin_of_gInv (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hF : EnvWfT F) {E : ResolvedEnv}
    (hW : EnvWfT E) (hI : GInv P K hW) :
    GInvWithin P K F hF hW := by
  intro hsub α hα ctx hctx plans hplans μ hFaith
  have h := hI α hα ctx hctx plans hplans μ hFaith
  exact ⟨h.1, h.2 F hsub⟩

theorem gInvWithin_empty (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hF : EnvWfT F) :
    GInvWithin P K F hF (.empty : EnvWfT emptyEnv) :=
  gInvWithin_of_gInv P K F hF .empty (gInv_empty P K)

/-- The fixed-completion invariant supplies the original semantic
environment contract at every valuation, using the same installed table. -/
theorem envSound_of_gInvWithin (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hF : EnvWfT F) {E : ResolvedEnv}
    (hW : EnvWfT E) (hsub : EnvSub E F)
    (hI : GInvWithin P K F hF hW) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P hW)) σ K E n := by
  have hIv := hI hsub (arities E) (arities_agree E)
    (NormRole.envCtx hW) (fun _ _ => rfl)
    (EvalRole.envPlan hW) (fun _ _ => rfl) _ (table_spec P hW).2.1
  exact envSound_of P hsub hIv.1 hIv.2 σ n

/-- The original False finalizer needs only the fixed admitted completion
`E` itself. No extra premise is added to the underlying typing judgment,
the level bound, or the distinguished stored False recursor. -/
theorem false_of_gInvWithin (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hI : GInvWithin P K E hW hW)
    (h1 : E.members 1 = some falseRecMemberU) (n : Nat)
    (e : Expr Nat) (D : HasTyT E n [] e (.const 0 []))
    (hl : LOKt (fun _ => 0) 4 K D) : False := by
  have hsub : EnvSub E E := fun _ _ h => h
  have hIv := hI hsub (arities E) (arities_agree E)
    (NormRole.envCtx hW) (fun _ _ => rfl)
    (EvalRole.envPlan hW) (fun _ _ => rfl) _ (table_spec P hW).2.1
  exact empty_of_falseRec P (hIv.1 1 _ h1)
    (sound_ty (P.good _ rfl)
      (envSound_of_gInvWithin P K E hW hW hsub hI (fun _ => 0) n)
      D hl ρ0 trivial)

/-- A definition, theorem, or opaque declaration is sound from the
predecessor invariant at the same fixed completion. This proves the
stored body using the original `sound_ty` consumer via `envSound_of`. -/
theorem gInvWithin_singleW (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F)
    {E : ResolvedEnv} {hE : EnvWfT E} {r : Nat}
    {k : MemberClass} {A v : Expr Nat}
    (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM)
    (hfresh : E.members r = none)
    (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A)
    (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true)
    (hlvlv : exprLevelsBounded 0 v = true)
    (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (IH : GInvWithin P K F hFinal hE)
    (hsubF : EnvSub (extendEnv E r ⟨k, 0, A, some v⟩) F)
    (α : Arities) (hα : AritiesAgree α (extendEnv E r ⟨k, 0, A, some v⟩))
    (ctx : Nat → Role)
    (hctx : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' →
      ctx r' = NormRole.envCtx hE r') (plans : EvalRole.Plans)
    (hplans : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' →
      plans r' = EvalRole.envPlan hE r')
    (μ : Nat → List Nat → PSet.{4})
    (hFaith : EvalRole.Faithful (familyValue α) P μ ctx plans
      (extendEnv E r ⟨k, 0, A, some v⟩)) :
    AllSound P μ K (extendEnv E r ⟨k, 0, A, some v⟩) ∧
      ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' →
        m'.mclass = .recursorM → IotaAt P μ K F r' := by
  have hsub := members_extend_preserved (m := ⟨k, 0, A, some v⟩) hfresh
  have hEF : EnvSub E F := fun r' m' h => hsubF r' m' (hsub r' m' h)
  have IHμ := IH hEF α (hα.mono hsub)
    ctx (fun r' h => hctx r' (dom_extend hfresh r' h))
    plans (fun r' h => hplans r' (dom_extend hfresh r' h)) μ
    (fun r' m' h => hFaith r' m' (hsub r' m' h))
  have hES : EnvSound (mkM P μ) (fun _ => 0) K E 0 :=
    envSound_of P hEF IHμ.1 IHμ.2 _ 0
  have hr : ctx r = .plain :=
    (hctx r dom_self).trans (NormRole.envCtx_fresh hE r hfresh)
  have hval : Equiv (μ r []) (den (mkM P μ) (fun _ => 0) ρ0 v) := by
    have h := hFaith r _ (members_extend_eq E r _) []
    rw [hr] at h
    change Equiv (μ r []) (RoleModel.memberVal (familyValue α) P μ
      .plain ⟨k, 0, A, some v⟩ []) at h
    have he : RoleModel.memberVal (familyValue α) P μ
        .plain ⟨k, 0, A, some v⟩ [] = den (mkM P μ) (fun _ => 0) ρ0 v :=
      mem_memberVal_def hk A v []
    rw [he] at h
    exact h
  refine ⟨fun r' m' h => ?_, fun r' m' h hk' => ?_⟩
  · by_cases hr' : r' = r
    · subst r'; rw [members_extend_eq] at h; cases h
      exact memberSound_singleton' hval hclA hclv hlvlA hlvlv hv hl hES
    · rw [members_extend_ne E r _ r' hr'] at h
      exact IHμ.1 r' m' h
  · by_cases hr' : r' = r
    · subst r'; rw [members_extend_eq] at h; cases h
      rcases hk with rfl | rfl | rfl <;> cases hk'
    · rw [members_extend_ne E r _ r' hr'] at h
      exact IHμ.2 r' m' h hk'

/-- Actual group-prefix transport of arities, role map, plans, and
faithfulness, preserving the same admitted completion and iota contract. -/
theorem gInvWithin_group_prefix (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (hFinal : EnvWfT F)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (IH : GInvWithin P K F hFinal hE) (hsubF : EnvSub E' F)
    (α : Arities) (hα : AritiesAgree α E')
    (ctx : Nat → Role)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (plans : EvalRole.Plans)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (μ : Nat → List Nat → PSet.{4})
    (hFaith : EvalRole.Faithful (familyValue α) P μ ctx plans E') :
    AllSound P μ K E ∧
      ∀ r m, E.members r = some m → m.mclass = .recursorM →
        IotaAt P μ K F r := by
  have hsubE : EnvSub E E' := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  exact IH (fun r m hm => hsubF r m (hsubE r m hm))
    α (hα.mono hsubE) ctx hctxE plans hplansE μ
    (fun r m hm => hFaith r m (hsubE r m hm))

/-- Assemble a group's actual membership cases and iota cases. The local
recursor obligation is precisely the existing `RecPkgAt` at the fixed
completion; old recursors retain their predecessor obligations. -/
theorem allSound_iota_groupWithin (P : Premises4) (K : Nat → Nat)
    (F : ResolvedEnv) (_hFinal : EnvWfT F)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hsubF : EnvSub E' F)
    (μ : Nat → List Nat → PSet.{4})
    (hPrior : AllSound P μ K E ∧
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K F r)
    (hFam : MemberSound P μ K f fm)
    (hCtor : ∀ j : Fin node.a.constructors.length,
      MemberSound P μ K (f + 1 + j.val) node.a.constructors[j.val])
    (hPkg : RecPkgAt P μ K F E' rr rm) :
    AllSound P μ K E' ∧
      ∀ r m, E'.members r = some m → m.mclass = .recursorM →
        IotaAt P μ K F r := by
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hRec := hPkg hsubF
  constructor
  · intro r m hm
    rcases group_member_cases hmem hL hrr node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hPrior.1 r m hold
    · exact hFam
    · exact hRec.1
    · exact hCtor j
  · intro r m hm hk
    rcases group_member_cases hmem hL hrr node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hPrior.2 r m hold hk
    · rw [hfam] at hk; cases hk
    · exact hRec.2
    · rw [(node.a.constructorViews j).hasClass] at hk; cases hk

end Rcic.F3.PSet.PointwiseRole

#print axioms Rcic.F3.PSet.PointwiseRole.gInvWithin_of_gInv
#print axioms Rcic.F3.PSet.PointwiseRole.envSound_of_gInvWithin
#print axioms Rcic.F3.PSet.PointwiseRole.false_of_gInvWithin
#print axioms Rcic.F3.PSet.PointwiseRole.gInvWithin_singleW
#print axioms Rcic.F3.PSet.PointwiseRole.gInvWithin_group_prefix
#print axioms Rcic.F3.PSet.PointwiseRole.allSound_iota_groupWithin
