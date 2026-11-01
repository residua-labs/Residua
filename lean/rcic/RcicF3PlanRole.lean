import rcic.RcicF3PiRecValue
import rcic.RcicF3RoleTable
/-! Plan-aware group interpretation. The family role is explicit and every
recursor consumes the normalized plan from its typed admission descriptor.
The repaired target retains the entire original typed PendA domain,
AllSound and final-environment IotaAt. Canonical table installation is proved
from the existing family-read law; it does not prove soundness of the
family or recursor value. This target supersedes the family-only operational
proposal for higher-order hidden fields. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PlanRole
open Rcic.Declarative

abbrev Plans := Nat → List (List FieldShape)

def admittedPlan {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a) :
    List (List FieldShape) :=
  (List.range a.constructors.length).map (fun j =>
    if hj : j < a.constructors.length then h.shapesAt ⟨j, hj⟩ else [])

def scanPlan {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' →
    Option (List (List FieldShape))
  | _, _, _, .nil _ => none
  | _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      match hadm with
      | .recursor a _ _ _ _ _ h14 =>
          if m.mclass = .recursorM then some (admittedPlan a h14) else scanPlan hrest
      | _ => scanPlan hrest

def envPlan : {E : ResolvedEnv} → EnvWfT E → Plans
  | _, .empty => fun _ => []
  | _, .axiom _ _ _ _ hE _ _ _ _ => envPlan hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envPlan hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envPlan hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envPlan hE
  | _, .group _ _ _ _ rr _ _ hE _ _ _ hmem =>
      match scanPlan hmem with
      | some plan => fun r => if r = rr then plan else envPlan hE r
      | none => envPlan hE

noncomputable def memberVal (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (plan : List (List FieldShape)) :
    Role → CheckedMember → List Nat → PSet.{4}
  | .recursor fd, m, vs => RecPlanValue.memberValue (mkM P μ) (σOf vs) fd plan m
  | ro, m, vs => RoleModel.memberVal F P μ ro m vs

def Faithful (F : RoleModel.FamilyValue) (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : Plans) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ∀ vs,
    Equiv (μ r vs) (memberVal F P μ (plans r) (ctx r) m vs)

def GInv (F : RoleModel.FamilyValue) (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) →
  ∀ plans : Plans, (∀ r, Dom E r → plans r = envPlan hW r) →
  ∀ μ, Faithful F P μ ctx plans E →
    AllSound P μ K E ∧ ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

def GroupStepAt (F : RoleModel.FamilyValue) (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  GInv F P K hE → GInv F P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

def StepAG (F : RoleModel.FamilyValue) (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    (∃ node : RecNode E E' f rr rm, PendA node) → GroupStepAt F P K hE hfam hctors hrec hmem

theorem scanPlan_present {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E') :
    (scanPlan hmem).isSome = (scanRec hmem).isSome := by
  induction hmem with
  | nil => rfl
  | cons E r m rest E' hfresh hnobody hcl harity hlvl hcanon harities hadm hidx u hT hTc htyped hrest ih =>
    cases hadm <;> simp only [scanPlan, scanRec]
    · exact ih
    · exact ih
    · split
      · rfl
      · exact ih
theorem endpoint_of_dec {M M' : Interp.{4}} (h : M.dec = M'.dec)
    (σ : Nat → Nat) (fd : FamData) (plan : List (List FieldShape)) (ρ : Nat → PSet.{4}) :
    RecPlanValue.endValue M σ fd plan ρ = RecPlanValue.endValue M' σ fd plan ρ := by
  unfold RecPlanValue.endValue RecPlan.core
  rw [recCore_of_dec h, recEnd_of_dec h]
  unfold cond
  rw [h]
theorem member_agree {F : RoleModel.FamilyValue} {P : Premises4} {ctx : Nat → Role}
    (hC : RoleModel.FamilyReadsCtx F P ctx) {μ₁ μ₂ : Nat → List Nat → PSet.{4}}
    {S : Nat → Prop} (h : AgreeOn μ₁ μ₂ S) (r : Nat) (m : CheckedMember)
    (hr : ReadsIn S (ctx r) m) (plan : List (List FieldShape)) (vs : List Nat) :
    Equiv (memberVal F P μ₁ plan (ctx r) m vs)
      (memberVal F P μ₂ plan (ctx r) m vs) := by
  cases he : ctx r with
  | recursor fd =>
    rw [he] at hr
    exact piLam_agreeOn P h (σOf vs)
      (RecPlanValue.laws (mkM P μ₁) (σOf vs) fd plan).1
      (fun ρ => by rw [endpoint_of_dec (M := mkM P μ₁) (M' := mkM P μ₂) rfl]; exact Equiv.rfl)
      m.mtype hr ρ0
  | plain => simpa only [he, memberVal] using RoleModel.member_agree hC h r m hr vs
  | fam fd => simpa only [he, memberVal] using RoleModel.member_agree hC h r m hr vs
  | ctor fd j => simpa only [he, memberVal] using RoleModel.member_agree hC h r m hr vs
/-- Install the members of a group at the roles `ctx`. -/
noncomputable def groupTable (F : RoleModel.FamilyValue) (P : Premises4) (ctx : Nat → Role) (plans : Plans) {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' →
    (Nat → List Nat → PSet.{4}) → Nat → List Nat → PSet.{4}
  | _, _, _, .nil _, μ => μ
  | _, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, μ =>
      groupTable F P ctx plans hrest (upd μ r (memberVal F P μ (plans r) (ctx r) m))

/-- The table of an admitted environment, at the roles `ctx`. -/
noncomputable def envTable (F : RoleModel.FamilyValue) (P : Premises4) (ctx : Nat → Role) (plans : Plans) : {E : ResolvedEnv} → EnvWfT E → Nat → List Nat → PSet.{4}
  | _, .empty => fun _ _ => pempty
  | _, .axiom (arity := arity) _ r A _ hE _ _ _ _ =>
      upd (envTable F P ctx plans hE) r (memberVal F P (envTable F P ctx plans hE) (plans r) (ctx r) ⟨.axiomM, arity, A, none⟩)
  | _, .definition _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envTable F P ctx plans hE) r (memberVal F P (envTable F P ctx plans hE) (plans r) (ctx r) ⟨.definitionM, 0, A, some v⟩)
  | _, .thm _ r A p hE _ _ _ _ _ _ _ =>
      upd (envTable F P ctx plans hE) r (memberVal F P (envTable F P ctx plans hE) (plans r) (ctx r) ⟨.theoremM, 0, A, some p⟩)
  | _, .opaque _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envTable F P ctx plans hE) r (memberVal F P (envTable F P ctx plans hE) (plans r) (ctx r) ⟨.opaqueM, 0, A, some v⟩)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem => groupTable F P ctx plans hmem (envTable F P ctx plans hE)

theorem faithful_step (F : RoleModel.FamilyValue) (P : Premises4)
    (ctx : Nat → Role) (plans : Plans) (hC : RoleModel.FamilyReadsCtx F P ctx)
    {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hF : Faithful F P μ ctx plans E) (hR : ReadsClosed ctx E)
    (hfresh : E.members r = none) (hm : ReadsIn (Dom E) (ctx r) m) :
    Faithful F P (upd μ r (memberVal F P μ (plans r) (ctx r) m)) ctx plans (extendEnv E r m) ∧
      ReadsClosed ctx (extendEnv E r m) := by
  have hag := agreeOn_upd hfresh μ (memberVal F P μ (plans r) (ctx r) m)
  refine ⟨fun r' m' h vs => ?_, fun r' m' h => ?_⟩
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      rw [upd_eq]
      exact member_agree hC hag r' m hm (plans r') vs
    · rw [members_extend_ne E r m r' hr] at h
      rw [upd_ne μ r _ hr]
      exact (hF r' m' h vs).trans (member_agree hC hag r' m' (hR r' m' h) (plans r') vs)
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      exact hm.mono (dom_extend hfresh)
    · rw [members_extend_ne E r m r' hr] at h
      exact (hR r' m' h).mono (dom_extend hfresh)
theorem faithful_groupTable (F : RoleModel.FamilyValue) (P : Premises4) (ctx : Nat → Role) (plans : Plans) (hC : RoleModel.FamilyReadsCtx F P ctx) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    GroupReadsOK ctx hmem → ∀ (μ : Nat → List Nat → PSet.{4}), Faithful F P μ ctx plans E → ReadsClosed ctx E →
      Faithful F P (groupTable F P ctx plans hmem μ) ctx plans E' ∧ ReadsClosed ctx E'
  | _, _, _, .nil _, _, μ, hF, hR => ⟨hF, hR⟩
  | _, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, hg, μ, hF, hR => by
      obtain ⟨hm, hrestR⟩ := hg
      obtain ⟨hF', hR'⟩ := faithful_step F P ctx plans hC hF hR hfresh hm
      exact faithful_groupTable F P ctx plans hC hrest hrestR _ hF' hR'

theorem faithful_envTable (F : RoleModel.FamilyValue) (P : Premises4) (ctx : Nat → Role) (plans : Plans) (hC : RoleModel.FamilyReadsCtx F P ctx) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ReadsOKAlong ctx hW → Faithful F P (envTable F P ctx plans hW) ctx plans E ∧ ReadsClosed ctx E
  | _, .empty, _ => ⟨fun _ _ h => (Option.noConfusion h), fun _ _ h => (Option.noConfusion h)⟩
  | _, .axiom E r A u hE hfresh _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx plans hC hE hR0
      exact faithful_step F P ctx plans hC hF hR hfresh hm
  | _, .definition E r A v u hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx plans hC hE hR0
      exact faithful_step F P ctx plans hC hF hR hfresh hm
  | _, .thm E r A p hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx plans hC hE hR0
      exact faithful_step F P ctx plans hC hF hR hfresh hm
  | _, .opaque E r A v u hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx plans hC hE hR0
      exact faithful_step F P ctx plans hC hF hR hfresh hm
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem, hRA => by
      obtain ⟨hR0, hg⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx plans hC hE hR0
      exact faithful_groupTable F P ctx plans hC hmem hg _ hF hR

/-- Transport from a family-only invariant when its actual recursors already
use the raw plan. This is a compatibility lemma, not a universal producer. -/
theorem gInv_of_raw (F : RoleModel.FamilyValue) (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hraw : ∀ r, Dom E r → ∀ fd, envCtx hW r = .recursor fd →
      envPlan hW r = RecPlan.rawPlan fd)
    (hI : RoleModel.GInv F P K hW) : GInv F P K hW := by
  intro ctx hc plans hp μ hF
  apply hI ctx hc μ
  intro r m hr vs
  have h := hF r m hr vs
  cases he : ctx r with
  | recursor fd =>
    have hg : plans r = RecPlan.rawPlan fd :=
      (hp r (dom_of_members hr)).trans
        (hraw r (dom_of_members hr) fd ((hc r (dom_of_members hr)).symm.trans he))
    rw [he, hg] at h
    change Equiv (μ r vs) (RecPlanValue.memberValue (mkM P μ) (σOf vs) fd
      (RecPlan.rawPlan fd) m) at h
    unfold RecPlanValue.memberValue at h
    rw [funext (RecPlanValue.laws (mkM P μ) (σOf vs) fd (RecPlan.rawPlan fd)).2] at h
    exact h
  | plain => simpa only [he, memberVal] using h
  | fam fd => simpa only [he, memberVal] using h
  | ctor fd j => simpa only [he, memberVal] using h

end Rcic.F3.PSet.PlanRole
