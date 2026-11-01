import rcic.RcicF3RawFamilyEnlarge
import rcic.RcicF3NormCandidatePrefix
import rcic.RcicF3NormPropParamFields

/-!
# Bounded fresh-head separation at an actual constructor prefix

The original fitting contexts in the two admissible models are produced
from one fitting normalized constructor tuple. The supplied D bound and
the existing checked equality of parameter telescopes reconstruct the
original fields; the actual predecessor invariant supplies both sound
family prefixes. No raw-frame closure or local-context erasure is used.

The conclusion excludes a bounded typing of a local at a family-free type
when its literal lookup type is a complete fitting DATA family head.
Higher-order field values, dependent arguments and complete result keys
remain present in the preceding tuple. This does not yet separate an
arbitrary converted Pi head or prove recursive-local domain independence.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormFreshHead
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex

/-- Both original contexts are produced from the SAME normalized tuple.
The second frame is a literal strict admissible enlargement, not a closed
candidate or a replacement for the canonical family role. -/
theorem constructor_prefixes (P : Premises4)
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans p.E)
    (C : Frame) (hC : Admissible (famDataOf p.node.a) C)
    (vs : List Nat) (hvl : vs.length = p.node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) C)) (σOf vs)
      (EvalPlanNormal.fields p j) (push ps ρ0) xs)
    (k : Nat) (hk : k ≤ (p.node.a.constructorViews j).fields.length) :
    let fd := famDataOf p.node.a
    let D := RawFamilyEnlarge.enlarge fd C
    let c := p.node.a.constructorViews j
    let Γ := policyPrefixContext (c.parameters ++ c.fields) (c.parameters.length + k)
    let ρ := push ((ps ++ xs).take (c.parameters.length + k)) ρ0
    EnvSound (mkM P (table P μ fd C)) (σOf vs) K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity ∧
    EnvSound (mkM P (table P μ fd D)) (σOf vs) K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity ∧
    Fits (mkM P (table P μ fd C)) (σOf vs) Γ ρ ∧
    Fits (mkM P (table P μ fd D)) (σOf vs) Γ ρ := by
  dsimp only
  let fd := famDataOf p.node.a
  let D := RawFamilyEnlarge.enlarge fd C
  let c := p.node.a.constructorViews j
  have hAd : Admissible fd D := RawFamilyEnlarge.admissible P fd C hC
  have hPC := NormCandidatePrefix.target_facts P μ K p fm ctors hE hfam hmem
    hPred ctx plans hctx hplans hFaith C hC
  have hPD := NormCandidatePrefix.target_facts P μ K p fm ctors hE hfam hmem
    hPred ctx plans hctx hplans hFaith D hAd
  obtain ⟨_, _, hfree, _, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hparams (X : Frame) : TelFits (mkM P (table P μ fd X)) (σOf vs)
      p.node.a.family.parameters ρ0 ps := by
    apply (TelFits_agreeOn P (agreeOn_upd_off μ fd.fref (ofFrame P μ fd X))
      (σOf vs) fd.params (fun A hA r hr =>
        denRefs_ne_of_occurs A (hfree A (List.mem_append_left _ hA)) r hr) ρ0 ps).mpr
    exact hps
  have hraw (X : Frame) (hX : Admissible fd X) (hCX : FrameSub C X)
      (hPX : AllSound P (table P μ fd X) K p.E ∧
        (∀ r m, p.E.members r = some m → m.mclass = .recursorM →
          IotaAt P (table P μ fd X) K p.E' r) ∧
        (∀ σ n, EnvSound (mkM P (table P μ fd X)) σ K
          (extendEnv p.E p.f fm) n)) :
      TelFits (mkM P (table P μ fd X)) (σOf vs) c.fields (push ps ρ0) xs := by
    apply NormPropParamFields.fields_to_raw_of_guarded P μ (σOf vs) K p fm ctors
      hE hfam hctors hrec hmem hB hD hpar C X hC hX hPX.1 hPX.2.1
      (hPX.2.2 (σOf vs) p.node.a.family.member.arity) vs rfl hvl hvs j ps xs
      (hparams X) ?_ hxs
    intro ws i z hz _ _
    exact hCX ws i z hz
  have hown (X : Frame) : TelFits (mkM P (table P μ fd X)) (σOf vs)
      c.parameters ρ0 ps := by
    rw [hpar j]
    exact hparams X
  have hxc := hraw C hC (fun _ _ _ h => h) hPC
  have hxd := hraw D hAd (RawFamilyEnlarge.frame_sub fd C) hPD
  have hlen : c.parameters.length + k ≤ (c.parameters ++ c.fields).length := by
    rw [List.length_append]
    exact Nat.add_le_add_left hk c.parameters.length
  exact ⟨hPC.2.2 (σOf vs) p.node.a.family.member.arity,
    hPD.2.2 (σOf vs) p.node.a.family.member.arity,
    fits_prefixContext (mkM P (table P μ fd C)) (σOf vs) _ ρ0 _
      (TelFits.append (hown C) hxc) _ hlen,
    fits_prefixContext (mkM P (table P μ fd D)) (σOf vs) _ ρ0 _
      (TelFits.append (hown D) hxd) _ hlen⟩

/-- Bounded variable inversion and both semantic soundness calls are
composed with actual admitted-prefix reconstruction. The supplied typing
is the proposition being ruled out, not a semantic conversion callback. -/
theorem no_clean_variable_type (P : Premises4)
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans p.E)
    (C : Frame) (hC : Admissible (famDataOf p.node.a) C)
    (vs : List Nat) (hvl : vs.length = p.node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) C)) (σOf vs)
      (EvalPlanNormal.fields p j) (push ps ρ0) xs)
    (k : Nat) (hk : k ≤ (p.node.a.constructorViews j).fields.length)
    (args : List (Expr Nat)) (A : Expr Nat)
    (ha : ∀ e ∈ args, occursConst p.node.a.family.ref e = false)
    (hA : occursConst p.node.a.family.ref A = false)
    (h0 : evalTotal (σOf vs) p.node.a.family.resultLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf vs)
      (p.node.a.family.parameters ++ p.node.a.family.indices) ρ0
      (args.map (den (mkM P μ) (σOf vs)
        (push ((ps ++ xs).take ((p.node.a.constructorViews j).parameters.length + k)) ρ0))))
    (b : Nat)
    (hlook : lookupType
      (policyPrefixContext ((p.node.a.constructorViews j).parameters ++
        (p.node.a.constructorViews j).fields)
        ((p.node.a.constructorViews j).parameters.length + k)) b =
      some (foldApps (.const p.node.a.family.ref (canonL p.node.a.family.member.arity)) args))
    (d : HasTyT (extendEnv p.E p.f fm) p.node.a.family.member.arity
      (policyPrefixContext ((p.node.a.constructorViews j).parameters ++
        (p.node.a.constructorViews j).fields)
        ((p.node.a.constructorViews j).parameters.length + k)) (.bvar b) A)
    (hd : LOKt (σOf vs) 4 K d) : False := by
  have hp := constructor_prefixes P μ K p fm ctors hE hfam hctors hrec hmem hB hD
    hpar hPred ctx plans hctx hplans hFaith C hC vs hvl hvs j ps xs hps hxs k hk
  dsimp only at hp
  have hcan : (canonL p.node.a.family.member.arity).map (evalTotal (σOf vs)) = vs := by
    rw [← hvl]
    exact map_param_σOf vs
  apply RawFamilyEnlarge.no_clean_variable_type P μ (famDataOf p.node.a) C hC
    p.node.a.family.member.arity (σOf vs) K hp.1 hp.2.1 _ hp.2.2.1 hp.2.2.2
    args A ha hA ?_ ?_ b hlook d hd
  · rw [hcan]
    exact h0
  · rw [hcan]
    exact hfit

end Rcic.F3.PSet.NormFreshHead
