import rcic.RcicF3EvalPlanNormal

/-!
# Canonical roles carrying the admitted normalized family descriptor

This is a distinct interpretation. A group stores the actual normalized
descriptor in its family and constructor roles; its recursor keeps the
original admitted plan, normalized domains and complete argument data.
The generic EvalRole value rule and faithful installer are reused literally.

The original raw-role invariant and both published literal refutations are
unchanged. No equivalence of the invariants is asserted. The targets below
are declarations of the remaining composition obligation, not producers.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormRole
open Rcic.Declarative Rcic.Model.PS

/-- The family descriptor is obtained from this group's actual admitted
plan. Ordinary declarations retain their existing plain interpretation. -/
noncomputable def envCtx : {E : ResolvedEnv} → EnvWfT E → Nat → Role
  | _, .empty => fun _ => .plain
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCtx hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCtx hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCtx hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCtx hE
  | _, .group _ f _ _ rr _ _ hE hfam hctors hrec hmem =>
      groupRoles (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem))
        f rr (envCtx hE)

/-- The descriptor equation does not identify this context with the raw one. -/
theorem envCtx_group {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    envCtx (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) =
      groupRoles (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem))
        f rr (envCtx hE) := rfl

/-- A canonical role outside the admitted environment is plain. -/
theorem envCtx_fresh : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ∀ r, E.members r = none → envCtx hW r = .plain
  | _, .empty, _, _ => rfl
  | _, .axiom _ _ _ _ hE _ _ _ _, r, h =>
      envCtx_fresh hE r (extendEnv_ne_none h).2
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, r, h =>
      envCtx_fresh hE r (extendEnv_ne_none h).2
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, r, h =>
      envCtx_fresh hE r (extendEnv_ne_none h).2
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, r, h =>
      envCtx_fresh hE r (extendEnv_ne_none h).2
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, r, h => by
      obtain ⟨hL, hrr⟩ :=
        group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
      obtain ⟨_, _, hf', hr', hbet⟩ := group_refs hmem hL hrr
      have h1 : r ≠ f := by
        intro he
        rw [he, hf'] at h
        cases h
      have h2 : r ≠ rr := by
        intro he
        rw [he, hr'] at h
        cases h
      have h3 : ¬ (f < r ∧ r < rr) := by
        intro ⟨a, b⟩
        obtain ⟨_, _, _, _, hm⟩ := hbet r a b
        rw [hm] at h
        cases h
      rw [envCtx_group, groupRoles, if_neg h1, if_neg h2, if_neg h3]
      exact envCtx_fresh hE r (groupMembersT_none hmem h)

/-- Installing this group preserves all preceding canonical roles. -/
theorem envCtx_group_stable {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') (r : Nat) (hr : Dom E r) :
    envCtx (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r =
      envCtx hE r := by
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  obtain ⟨hf0, hr0, _, _, hbet⟩ := group_refs hmem hL hrr
  have h1 : r ≠ f := by
    intro he
    unfold Dom at hr
    rw [he, hf0] at hr
    cases hr
  have h2 : r ≠ rr := by
    intro he
    unfold Dom at hr
    rw [he, hr0] at hr
    cases hr
  have h3 : ¬ (f < r ∧ r < rr) := by
    intro ⟨a, b⟩
    unfold Dom at hr
    rw [(hbet r a b).1] at hr
    cases hr
  rw [envCtx_group, groupRoles, if_neg h1, if_neg h2, if_neg h3]

/-- The new invariant quantifies over tables faithful to the normalized
canonical roles and the unchanged actual indexed-evaluation plans. -/
def GInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) →
  ∀ plans : EvalRole.Plans, (∀ r, Dom E r → plans r = EvalRole.envPlan hW r) →
  ∀ μ, EvalRole.Faithful RawFamily.role P μ ctx plans E →
    AllSound P μ K E ∧
    ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

/-- The empty predecessor supplies the new invariant without a semantic
table premise. Nontrivial group witnesses are constructed separately. -/
theorem gInv_empty (P : Premises4) (K : Nat → Nat) :
    GInv P K (.empty : EnvWfT emptyEnv) := by
  intro ctx hc plans hp μ hF
  constructor
  · intro r m hm
    nomatch hm
  · intro Efin hsub r m hm
    nomatch hm

def GroupStepAt (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm,
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  GInv P K hE →
    GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- The full PendA domain is retained. This declaration supplies no producer. -/
def StepAG (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    (∃ node : RecNode E E' f rr rm, PendA node) →
      GroupStepAt P K hE hfam hctors hrec hmem

end Rcic.F3.PSet.NormRole
