import rcic.RcicF3RecFieldMaskFields
import rcic.RcicF3NormFreshHead
import rcic.RcicF3CandidateBoundTuple

/-!
# Actual admitted constructor prefixes supply the bounded mask Context

The existing checked equality of parameter telescopes, BoundG/BoundDG,
and predecessor invariant produce the source and enlarged original fits.
The actual admitted cache and bounded transparent bodies then produce
every recursive lookup Origin. No Context, normalization, or family-read
callback is added to the public group hypotheses.

This establishes the local-context input of the bounded masking theorem
at every ordinary field prefix. It does not claim typed provenance for
every normalized reader domain or an all-universe-vector mask.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormFieldMaskContext
open Rcic.Declarative Rcic.Model.PS RawFamily RecFieldMask

private theorem context_eq (Γ : LCtx) (Fs : List (Expr Nat)) :
    BoundedPiSpine.context Γ Fs = Fs.reverse.map LocalDecl.assumption ++ Γ := by
  induction Fs generalizing Γ with
  | nil => rfl
  | cons A Fs ih =>
      simp only [BoundedPiSpine.context, ih, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]

private theorem context_inv (M : Interp.{4}) (σ : Nat → Nat) :
    (Γ : LCtx) → (Fs : List (Expr Nat)) → (ρ : Nat → PSet.{4}) →
    (xs : List PSet.{4}) → xs.length = Fs.length →
    Fits M σ (BoundedPiSpine.context Γ Fs) (push xs ρ) →
      Fits M σ Γ ρ ∧ TelFits M σ Fs ρ xs
  | _, [], _, [], _, hf => ⟨hf, True.intro⟩
  | _, [], _, _ :: _, h, _ => (Nat.noConfusion h)
  | _, _ :: _, _, [], h, _ => (Nat.noConfusion h)
  | Γ, A :: Fs, ρ, x :: xs, hlen, hf => by
      have h := context_inv M σ (.assumption A :: Γ) Fs (vcons x ρ) xs
        (Nat.succ.inj hlen) hf
      exact ⟨h.1.1, h.1.2, h.2⟩

private theorem split_tuple (M : Interp.{4}) (σ : Nat → Nat) :
    (Ps Fs : List (Expr Nat)) → (ρ : Nat → PSet.{4}) →
    (ps xs : List PSet.{4}) → ps.length = Ps.length →
    TelFits M σ (Ps ++ Fs) ρ (ps ++ xs) →
      TelFits M σ Fs (push ps ρ) xs
  | [], _, _, [], _, _, h => h
  | [], _, _, _ :: _, _, h, _ => (Nat.noConfusion h)
  | _ :: _, _, _, [], _, h, _ => (Nat.noConfusion h)
  | _ :: Ps, Fs, ρ, p :: ps, xs, hl, h =>
      split_tuple M σ Ps Fs (vcons p ρ) ps xs (Nat.succ.inj hl) h.2

private theorem original_tuple (M : Interp.{4}) (σ : Nat → Nat)
    (Ps Fs : List (Expr Nat)) (ps xs : List PSet.{4})
    (hp : ps.length = Ps.length) (hx : xs.length = Fs.length)
    (hf : Fits M σ (policyPrefixContext (Ps ++ Fs) (Ps.length + Fs.length))
      (push ((ps ++ xs).take (Ps.length + Fs.length)) ρ0)) :
    TelFits M σ Fs (push ps ρ0) xs := by
  have hz : (ps ++ xs).length = (Ps ++ Fs).length := by
    simp only [List.length_append, hp, hx]
  have ht : (ps ++ xs).take (Ps.length + Fs.length) = ps ++ xs := by
    rw [← List.length_append, ← hz, List.take_length]
  rw [ht] at hf
  have hf' : Fits M σ (BoundedPiSpine.context [] (Ps ++ Fs)) (push (ps ++ xs) ρ0) := by
    simpa only [context_eq, policyPrefixContext, ← List.length_append,
      List.take_length, List.append_nil] using hf
  exact split_tuple M σ Ps Fs ρ0 ps xs hp (context_inv M σ [] (Ps ++ Fs) ρ0
    (ps ++ xs) hz hf').2

private theorem context_prefix (Ps Fs : List (Expr Nat)) (k : Nat) :
    BoundedPiSpine.context (policyPrefixContext Ps Ps.length) (Fs.take k) =
      policyPrefixContext (Ps ++ Fs) (Ps.length + k) := by
  rw [context_eq]
  simp only [policyPrefixContext, List.take_length, List.take_append_eq_append_take,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.reverse_append, List.map_append]

/-- At the supplied positive DATA stage and bounded family valuation, the
actual group supplies context, reader and instance facts. Recursive field
VALUES are masked; parameters, ordinary values and recursive keys remain actual. -/
theorem constructor_contexts (P : Premises4)
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
    (h0 : evalTotal (σOf vs) p.node.a.family.resultLevel ≠ 0)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) C)) (σOf vs)
      (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    ∀ k, k ≤ (p.node.a.constructorViews j).fields.length →
      Context P μ (famDataOf p.node.a) C (σOf vs)
        (extendMarks ((p.constructors j).shapes.take k) (fun _ => none))
        (policyPrefixContext ((p.node.a.constructorViews j).parameters ++
          (p.node.a.constructorViews j).fields)
          ((p.node.a.constructorViews j).parameters.length + k))
        (push (xs.take k) (push ps ρ0))
        (maskedPush ((p.constructors j).shapes.take k) (xs.take k) (push ps ρ0)) := by
  let fd := famDataOf p.node.a
  let c := p.node.a.constructorViews j
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  have hp := NormFreshHead.constructor_prefixes P μ K p fm ctors hE hfam hctors hrec hmem
    hB hD hpar hPred ctx plans hctx hplans hFaith C hC vs hvl hvs j ps xs hps hxs
    c.fields.length (Nat.le_refl _)
  dsimp only at hp
  have hpl : ps.length = c.parameters.length := by
    rw [hpar j]
    exact hps.length
  have hxl : xs.length = c.fields.length := hxs.length.trans
    ((List.length_map _ _).trans (EvalPlanNormal.specs_length (p.constructors j).fields))
  have hxC := original_tuple MC (σOf vs) c.parameters c.fields ps xs hpl hxl hp.2.2.1
  have hxD := original_tuple MD (σOf vs) c.parameters c.fields ps xs hpl hxl hp.2.2.2
  have hb := CandidateBoundFields.family_prefix_bodiesOK (σOf vs) K hE hB.1 hmem
  have hi := NormPropParamFields.original_fields_instOK (σOf vs) K hE hfam hctors hrec
    hmem hD p.node vs rfl hvl hvs j
  have hcan : (canonL p.node.a.family.member.arity).map (evalTotal (σOf vs)) = vs := by
    rw [← hvl]
    exact map_param_σOf vs
  have hzero : evalTotal (σOf ((canonL p.node.a.family.member.arity).map
      (evalTotal (σOf vs)))) fd.resLevel ≠ 0 := by
    rw [hcan]
    exact h0
  have hr : Context P μ fd C (σOf vs) (fun _ => none)
      (policyPrefixContext c.parameters c.parameters.length) (push ps ρ0) (push ps ρ0) :=
    fun _ _ _ => Equiv.rfl
  have hc := fields_contexts P μ fd C hC (σOf vs) K hp.1 hp.2.1 hb
    (CandidateScope.recNode_transparentBody_prefix hmem p.node) hzero
    (p.constructors j).fields hi (fun _ => none)
    (policyPrefixContext c.parameters c.parameters.length) (push ps ρ0) (push ps ρ0)
    hr xs hxC hxD
  intro k hk
  simpa only [context_prefix] using hc k hk

end Rcic.F3.PSet.NormFieldMaskContext
