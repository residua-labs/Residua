import rcic.RcicF3ReaderFieldMasks
import rcic.RcicF3ReaderGroupWorld
import rcic.RcicF3PointwisePrefix
import rcic.RcicF3NormSmallFrameLocal
import rcic.RcicF3NormPropParamFields
import rcic.RcicF3CandidateBoundTuple

/-!
# Admitted bounded DATA constructors produce their reached-domain masks

The separate pointwise predecessor is reapplied at an arbitrary admissible
frame and its strict enlargement. The existing D-bound field derivations
and checked parameter equality reconstruct both original tuples. Their
actual cache, bounded field typings and produced reader world then invoke
the complete field-mask induction, including every ordinary representative.

The final theorem instantiates the globally admissible signature candidate
and constructs its closure only at the original bounded canonical world.
No local candidate, constructor closure, domain mask, normalization callback,
or conversion between the old and new invariants is assumed. The original
unbounded raw-family target is unchanged. All child and result keys remain
evaluated at the actual preceding recursive fields. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseFieldMasks
open Rcic.Declarative Rcic.Model.PS RawFamily RecFieldMask

/-- At the supplied arity-correct universe vector whose entries are bounded
by K rr and whose DATA result universe is nonzero, the actual admitted group
and pointwise predecessor produce the mask for the supplied constructor and
fitting parameter/field tuples. Both reconstructed original tuples retain
exactly those supplied values. -/
theorem constructor_mask (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (C : Frame) (hC : Admissible (famDataOf p.node.a) C)
    (vs : List Nat) (hvl : vs.length = p.node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (h0 : evalTotal (σOf vs) p.node.a.family.resultLevel ≠ 0)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) C)) (σOf vs)
      p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) C)) (σOf vs)
      (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    PiSmallMaskShape.TupleMask (mkM P (table P μ (famDataOf p.node.a) C))
      (mkM P μ) (σOf vs) (EvalPlanNormal.specs (p.constructors j).fields)
      (push ps ρ0) (push ps ρ0) xs := by
  let fd := famDataOf p.node.a
  let D := RawFamilyEnlarge.enlarge fd C
  let cv := p.node.a.constructorViews j
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd D)
  let Γ := policyPrefixContext cv.parameters cv.parameters.length
  have hAd : Admissible fd D := RawFamilyEnlarge.admissible P fd C hC
  have hPC := PointwiseRole.target_facts P μ K p fm ctors hE hfam hmem
    hPred α hα ctx plans hctx hplans hFaith C hC
  have hPD := PointwiseRole.target_facts P μ K p fm ctors hE hfam hmem
    hPred α hα ctx plans hctx hplans hFaith D hAd
  obtain ⟨_, _, hfree, _, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hrefs : RefsIn (fun r => r ≠ fd.fref) fd.params := by
    intro A hA r hr
    exact denRefs_ne_of_occurs A (hfree A (List.mem_append_left _ hA)) r hr
  have hpBase : TelFits (mkM P μ) (σOf vs) fd.params ρ0 ps :=
    (TelFits_agreeOn P (agreeOn_upd_off μ fd.fref (ofFrame P μ fd C))
      (σOf vs) fd.params hrefs ρ0 ps).mp hps
  have hparams (X : Frame) : TelFits (mkM P (table P μ fd X)) (σOf vs)
      p.node.a.family.parameters ρ0 ps :=
    (TelFits_agreeOn P (agreeOn_upd_off μ fd.fref (ofFrame P μ fd X))
      (σOf vs) fd.params hrefs ρ0 ps).mpr hpBase
  have hraw (X : Frame) (hX : Admissible fd X) (hCX : FrameSub C X)
      (hPX : AllSound P (table P μ fd X) K p.E ∧
        (∀ r m, p.E.members r = some m → m.mclass = .recursorM →
          IotaAt P (table P μ fd X) K p.E' r) ∧
        (∀ σ n, EnvSound (mkM P (table P μ fd X)) σ K
          (extendEnv p.E p.f fm) n)) :
      TelFits (mkM P (table P μ fd X)) (σOf vs) cv.fields (push ps ρ0) xs := by
    apply NormPropParamFields.fields_to_raw_of_guarded P μ (σOf vs) K p fm ctors
      hE hfam hctors hrec hmem hB hD hpar C X hC hX hPX.1 hPX.2.1
      (hPX.2.2 (σOf vs) p.node.a.family.member.arity) vs rfl hvl hvs j ps xs
      (hparams X) ?_ hxs
    intro ws i z hz _ _
    exact hCX ws i z hz
  have hxC := hraw C hC (fun _ _ _ h => h) hPC
  have hxD := hraw D hAd (RawFamilyEnlarge.frame_sub fd C) hPD
  have hown (X : Frame) : TelFits (mkM P (table P μ fd X)) (σOf vs)
      cv.parameters ρ0 ps := by
    rw [hpar j]
    exact hparams X
  have hfits (X : Frame) : Fits (mkM P (table P μ fd X)) (σOf vs) Γ (push ps ρ0) := by
    have hp := hown X
    have ht : ps.take cv.parameters.length = ps := by
      rw [← hp.length, List.take_length]
    have hf := fits_prefixContext (mkM P (table P μ fd X)) (σOf vs)
      cv.parameters ρ0 ps hp cv.parameters.length (Nat.le_refl _)
    simpa only [ht] using hf
  have htypes : ∀ k : Fin cv.fields.length, ∃ u : Level,
      ∃ d : HasTyT (extendEnv p.E p.f fm) p.node.a.family.member.arity
        (BoundedPiSpine.context Γ (cv.fields.take k.val)) (cv.fields[k]) (.sort u),
        LOKt (σOf vs) 4 K d := by
    intro k
    obtain ⟨u, d, hd⟩ := hD.2 p.node j vs hvl hvs k
    have hfold : ∀ (Δ : LCtx) (Fs : List (Expr Nat)),
        BoundedPiSpine.context Δ Fs = Fs.reverse.map LocalDecl.assumption ++ Δ := by
      intro Δ Fs
      induction Fs generalizing Δ with
      | nil => rfl
      | cons A Fs ih =>
          simp only [BoundedPiSpine.context, ih, List.reverse_cons, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
    have hΓ : BoundedPiSpine.context Γ (cv.fields.take k.val) =
        policyPrefixContext (cv.parameters ++ cv.fields) (cv.parameters.length + k.val) := by
      rw [hfold]
      simp only [Γ, policyPrefixContext, List.take_length,
        List.take_append_eq_append_take, List.take_of_length_le (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.reverse_append, List.map_append]
    obtain ⟨d', hd'⟩ := lokt_cast_ctx (σOf vs) 4 K hΓ.symm d hd
    exact ⟨u, d', hd'⟩
  have hb := CandidateBoundFields.family_prefix_bodiesOK (σOf vs) K hE hB.1 hmem
  have hI := NormPropParamFields.original_fields_instOK (σOf vs) K hE hfam hctors
    hrec hmem hD p.node vs rfl hvl hvs j
  have hcan : (canonL p.node.a.family.member.arity).map (evalTotal (σOf vs)) = vs := by
    rw [← hvl]
    exact map_param_σOf vs
  have hzero : evalTotal (σOf ((canonL p.node.a.family.member.arity).map
      (evalTotal (σOf vs)))) fd.resLevel ≠ 0 := by
    rw [hcan]
    exact h0
  let W := ReaderPacket.World.of_pointwise_predecessor P μ fd C (σOf vs) K
    hE hB.1 hmem p.node p.node.fam hPred α hα ctx plans hctx hplans hFaith
  exact ReaderFieldMasks.fields_mask P μ fd C hC (σOf vs) K W
    (hPC.2.2 (σOf vs) p.node.a.family.member.arity)
    (hPD.2.2 (σOf vs) p.node.a.family.member.arity) hb
    (CandidateScope.recNode_transparentBody_prefix hmem p.node) hzero
    (p.constructors j).fields hI Γ htypes (fun _ => none)
    (push ps ρ0) (push ps ρ0) (fun _ _ _ => Equiv.rfl)
    (hfits C) (hfits D) xs hxC hxD

/-- The globally admissible signature candidate is used only as a typing
model here. Its reached masks are produced before any closure is invoked. -/
theorem bounded_masks (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hType : UniformType p.node.a.family.resultLevel) :
    NormSmallFrameLocal.BoundedReachedMasks P μ p K := by
  intro vs hvl hvs j ps xs hps hxs _hsmall
  exact constructor_mask P μ K p fm ctors hE hfam hctors hrec hmem hB hD hpar
    hPred α hα ctx plans hctx hplans hFaith (NormSmallFrame.candidate P μ p)
    (NormSmallFrame.admissible P μ p fm ctors hE hmem) vs hvl hvs
    (Nat.ne_of_gt (hType _)) j ps xs hps hxs

/-- Local candidate existence is now constructed from the original group,
bounds and predecessor. This theorem assumes neither a mask nor a candidate
existence predicate, and requires no facts at unbounded universe vectors. -/
theorem local_candidates (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hType : UniformType p.node.a.family.resultLevel) :
    PointwiseDataLocal.LocalCandidates P μ p K :=
  NormSmallFrameLocal.local_candidates P μ p fm ctors hE hmem hType K
    (bounded_masks P μ K p fm ctors hE hfam hctors hrec hmem hB hD hpar
      hPred α hα ctx plans hctx hplans hFaith hType)

end Rcic.F3.PSet.PointwiseFieldMasks
