import rcic.RcicF3PointwiseDataReads
import rcic.RcicF3PointwiseDataNormal
import rcic.RcicF3NormRoleTable
import rcic.RcicF3NormPropCtorUniform

/-!
# Explicit arity metadata and a separate pointwise DATA family role

The arity map is actual declaration metadata. Capturing it supplies the
existing generic FamilyValue/installer interface without changing Role or
the retained plans. Uniformly Prop families keep the existing raw-role
interpretation literally. Uniformly Type families use PointwiseData.

The new read law and faithful installation are unconditional. Family-kind
membership follows from actual admitted metadata and the new unconditional
size theorem. A separate invariant is declared; it is not identified with
NormRole.GInv and no group-step or universal A producer is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseRole
open Rcic.Declarative PiIndex RawFamily

abbrev Arities := Nat → Nat

def AritiesAgree (α : Arities) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → α r = m.arity

noncomputable def arities (E : ResolvedEnv) : Arities := fun r =>
  match E.members r with
  | none => 0
  | some m => m.arity

theorem arities_agree (E : ResolvedEnv) : AritiesAgree (arities E) E := by
  intro r m hm
  simp only [arities, hm]

theorem AritiesAgree.mono {α : Arities} {E E' : ResolvedEnv}
    (h : AritiesAgree α E')
    (hsub : ∀ r m, E.members r = some m → E'.members r = some m) :
    AritiesAgree α E := fun r m hm => h r m (hsub r m hm)

/-- The branch is the original proof/data distinction, independent of K. -/
noncomputable def familyValue (α : Arities) : RoleModel.FamilyValue :=
  fun P μ fd vs => if evalTotal (σOf vs) fd.resLevel = 0 then
    RawFamily.role P μ fd vs
  else PointwiseData.role P μ fd (α fd.fref) vs

theorem familyValue_prop (α : Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hProp : UniformProp fd.resLevel) (vs : List Nat) :
    familyValue α P μ fd vs = RawFamily.role P μ fd vs := by
  simp only [familyValue, if_pos (hProp (σOf vs))]

theorem familyValue_data (α : Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hType : UniformType fd.resLevel) (vs : List Nat) :
    familyValue α P μ fd vs = PointwiseData.role P μ fd (α fd.fref) vs := by
  simp only [familyValue, if_neg (Nat.ne_of_gt (hType (σOf vs)))]

theorem familyReads (α : Arities) (P : Premises4) (fd : FamData) :
    RoleModel.FamilyReads (familyValue α) P fd := by
  intro μ ν S h hp hc vs
  unfold familyValue
  split
  · rw [RawFamily.role_agreeOn P h fd hp hc vs]
    exact Equiv.rfl
  · rw [PointwiseData.role_agreeOn P h fd hp hc (α fd.fref) vs]
    exact Equiv.rfl

theorem familyReadsCtx (α : Arities) (P : Premises4) (ctx : Nat → Role) :
    RoleModel.FamilyReadsCtx (familyValue α) P ctx :=
  fun _ fd _ => familyReads α P fd

/-- Read the exact stored family arity from the actual final environment. -/
theorem arity_at_node {α : Arities} {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (hα : AritiesAgree α E') (node : RecNode E E' f rr rm) :
    α node.a.family.ref = node.a.family.member.arity := by
  have hm := node_fam_member node
  exact (congrArg α node.fam).trans (hα _ _ hm)

/-- All family vectors are covered. The Prop branch uses its old produced
admissibility; the DATA branch uses unconditional pointwise admissibility. -/
theorem family_mem_of_group (α : Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hα : AritiesAgree α p.E') (vs : List Nat) :
    familyValue α P μ (EvalPlanNormal.fd p) vs ∈ Ed (mkM P μ)
      (den (mkM P μ) (σOf vs) ρ0 (famType (EvalPlanNormal.fd p))) := by
  rcases selection_uniform p.node.a with hProp | hType
  · rw [familyValue_prop α P μ _ hProp vs]
    exact ofFrame_mem P μ (EvalPlanNormal.fd p) _
      (RawFamilyProp.admissible P μ (EvalPlanNormal.fd p) (fun ws => hProp (σOf ws))) vs
  · rw [familyValue_data α P μ _ hType vs]
    have har : α (EvalPlanNormal.fd p).fref = p.node.a.family.member.arity :=
      arity_at_node hα p.node
    rw [har]
    exact PointwiseData.role_mem P μ _ _
      (EvalPlanNormal.bounded_of_group p fm ctors hE hmem) vs

noncomputable def table (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    Nat → List Nat → PSet.{4} :=
  EvalRole.envTable (familyValue (arities E)) P (NormRole.envCtx hW)
    (EvalRole.envPlan hW) hW

theorem table_spec (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    AritiesAgree (arities E) E ∧
    EvalRole.Faithful (familyValue (arities E)) P (table P hW)
      (NormRole.envCtx hW) (EvalRole.envPlan hW) E ∧
    EvalRole.ReadsClosed (NormRole.envCtx hW) (EvalRole.envPlan hW) E :=
  ⟨arities_agree E,
    EvalRole.faithful_envTable (familyValue (arities E)) P (NormRole.envCtx hW)
      (EvalRole.envPlan hW) (familyReadsCtx _ P _) hW
      (NormRole.planReadsOKAlong hW _ _ (fun _ _ => rfl) (fun _ _ => rfl))⟩

/-- This is a new target. Arity agreement is literal declaration metadata;
the old normalized invariant is neither an input nor a conclusion. -/
def GInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ α : Arities, AritiesAgree α E →
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = NormRole.envCtx hW r) →
  ∀ plans : EvalRole.Plans, (∀ r, Dom E r → plans r = EvalRole.envPlan hW r) →
  ∀ μ, EvalRole.Faithful (familyValue α) P μ ctx plans E →
    AllSound P μ K E ∧
    ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

theorem gInv_empty (P : Premises4) (K : Nat → Nat) :
    GInv P K (.empty : EnvWfT emptyEnv) := by
  intro α hα ctx hc plans hp μ hF
  constructor
  · intro r m hm
    nomatch hm
  · intro Efin hsub r m hm
    nomatch hm

end Rcic.F3.PSet.PointwiseRole
