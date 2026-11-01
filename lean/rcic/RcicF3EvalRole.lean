import rcic.RcicF3EvalPlanValue

/-!
# Environment roles using the actual indexed evaluation endpoint

The canonical plan stores the admitted node, normalized recursive domains,
complete argument expressions and stored minor data. Recursor installation
uses EvalPlanValue.memberValue. The old PlanRole interpretation remains a
separate literal target, including its published refutation.

Plan support is a syntactic read obligation, discharged from admitted
syntax by EvalRoleReads. Faithfulness asserts the installed equations; it
asserts neither universal soundness nor the repaired StepAG producer.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalRole
open Rcic.Declarative

abbrev Plans := Nat → Option EvalPlan.Plan

noncomputable def envPlan : {E : ResolvedEnv} → EnvWfT E → Plans
  | _, .empty => fun _ => none
  | _, .axiom _ _ _ _ hE _ _ _ _ => envPlan hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envPlan hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envPlan hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envPlan hE
  | _, .group _ _ _ _ rr _ _ hE hfam hctors hrec hmem =>
      fun r => if r = rr then some (EvalPlan.ofGroup hE hfam hctors hrec hmem)
        else envPlan hE r

/-- Support of the actual plan is produced for every semantic interpretation. -/
def PlanReady (p : EvalPlan.Plan) : Prop :=
  ∀ (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat),
    PropEval.EndpointReads (Dom p.node.E0)
      (EvalPlanValue.context p (mkM P μ) σ ρ0)

def PlanReadsIn (S : Nat → Prop) : Option EvalPlan.Plan → Prop
  | none => True
  | some p => PlanReady p ∧ ∀ r, Dom p.node.E0 r → S r

theorem PlanReadsIn.mono {S S' : Nat → Prop} (h : ∀ r, S r → S' r)
    {plan : Option EvalPlan.Plan} (hp : PlanReadsIn S plan) : PlanReadsIn S' plan := by
  cases plan with
  | none => exact True.intro
  | some p => exact ⟨hp.1, fun r hr => h r (hp.2 r hr)⟩

/-- Stored type reads and the actual normalized plan reads travel together. -/
def ReadsIn (S : Nat → Prop) (plan : Option EvalPlan.Plan)
    (ro : Role) (m : CheckedMember) : Prop :=
  PSet.ReadsIn S ro m ∧ PlanReadsIn S plan

theorem ReadsIn.mono {S S' : Nat → Prop} (h : ∀ r, S r → S' r)
    {plan : Option EvalPlan.Plan} {ro : Role} {m : CheckedMember}
    (hr : ReadsIn S plan ro m) : ReadsIn S' plan ro m :=
  ⟨PSet.ReadsIn.mono h hr.1, PlanReadsIn.mono h hr.2⟩

def ReadsClosed (ctx : Nat → Role) (plans : Plans) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ReadsIn (Dom E) (plans r) (ctx r) m

noncomputable def memberVal (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (plan : Option EvalPlan.Plan) :
    Role → CheckedMember → List Nat → PSet.{4}
  | .recursor fd, m, vs =>
      match plan with
      | some p => EvalPlanValue.memberValue (mkM P μ) (σOf vs) p m
      | none => RoleModel.memberVal F P μ (.recursor fd) m vs
  | .plain, m, vs => RoleModel.memberVal F P μ .plain m vs
  | .fam fd, m, vs => RoleModel.memberVal F P μ (.fam fd) m vs
  | .ctor fd j, m, vs => RoleModel.memberVal F P μ (.ctor fd j) m vs

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

/-- Table agreement on the actual plan support transports the new endpoint. -/
theorem member_agree {F : RoleModel.FamilyValue} {P : Premises4} {ctx : Nat → Role}
    (hC : RoleModel.FamilyReadsCtx F P ctx) {μ₁ μ₂ : Nat → List Nat → PSet.{4}}
    {S : Nat → Prop} (h : AgreeOn μ₁ μ₂ S) (r : Nat) (m : CheckedMember)
    (plan : Option EvalPlan.Plan) (hr : ReadsIn S plan (ctx r) m) (vs : List Nat) :
    Equiv (memberVal F P μ₁ plan (ctx r) m vs)
      (memberVal F P μ₂ plan (ctx r) m vs) := by
  cases he : ctx r with
  | recursor fd =>
    rw [he] at hr
    cases plan with
    | none =>
      exact memberValR_agree P h (.recursor fd) m hr.1 vs
    | some p =>
      have hag : AgreeOn μ₁ μ₂ (Dom p.node.E0) :=
        fun q hq ls => h q (hr.2.2 q hq) ls
      exact piLam_agreeOn P h (σOf vs)
        (EvalPlanValue.endValue_resp (mkM P μ₁) (σOf vs) p)
        (EvalPlanValue.endValue_agreeOn P μ₁ μ₂ (Dom p.node.E0) hag p (σOf vs)
          (hr.2.1 P μ₁ (σOf vs))) m.mtype hr.1 ρ0
  | plain => simpa only [he, memberVal] using RoleModel.member_agree hC h r m hr.1 vs
  | fam fd => simpa only [he, memberVal] using RoleModel.member_agree hC h r m hr.1 vs
  | ctor fd j => simpa only [he, memberVal] using RoleModel.member_agree hC h r m hr.1 vs

/-- Each original stored member and every plan reads only its preceding prefix. -/
def GroupReadsOK (ctx : Nat → Role) (plans : Plans) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → Prop
  | _, _, _, .nil _ => True
  | E, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest =>
      ReadsIn (Dom E) (plans r) (ctx r) m ∧ GroupReadsOK ctx plans hrest

def ReadsOKAlong (ctx : Nat → Role) (plans : Plans) :
    {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom (arity := arity) E r A _ hE _ _ _ _ =>
      ReadsOKAlong ctx plans hE ∧ ReadsIn (Dom E) (plans r) (ctx r) ⟨.axiomM, arity, A, none⟩
  | _, .definition E r A v _ hE _ _ _ _ _ _ _ =>
      ReadsOKAlong ctx plans hE ∧ ReadsIn (Dom E) (plans r) (ctx r) ⟨.definitionM, 0, A, some v⟩
  | _, .thm E r A p hE _ _ _ _ _ _ _ =>
      ReadsOKAlong ctx plans hE ∧ ReadsIn (Dom E) (plans r) (ctx r) ⟨.theoremM, 0, A, some p⟩
  | _, .opaque E r A v _ hE _ _ _ _ _ _ _ =>
      ReadsOKAlong ctx plans hE ∧ ReadsIn (Dom E) (plans r) (ctx r) ⟨.opaqueM, 0, A, some v⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      ReadsOKAlong ctx plans hE ∧ GroupReadsOK ctx plans hmem

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
    (hF : Faithful F P μ ctx plans E) (hR : ReadsClosed ctx plans E)
    (hfresh : E.members r = none) (hm : ReadsIn (Dom E) (plans r) (ctx r) m) :
    Faithful F P (upd μ r (memberVal F P μ (plans r) (ctx r) m)) ctx plans (extendEnv E r m) ∧
      ReadsClosed ctx plans (extendEnv E r m) := by
  have hag := agreeOn_upd hfresh μ (memberVal F P μ (plans r) (ctx r) m)
  refine ⟨fun r' m' h vs => ?_, fun r' m' h => ?_⟩
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      rw [upd_eq]
      exact member_agree hC hag r' m (plans r') hm vs
    · rw [members_extend_ne E r m r' hr] at h
      rw [upd_ne μ r _ hr]
      exact (hF r' m' h vs).trans (member_agree hC hag r' m' (plans r') (hR r' m' h) vs)
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      exact hm.mono (dom_extend hfresh)
    · rw [members_extend_ne E r m r' hr] at h
      exact (hR r' m' h).mono (dom_extend hfresh)
theorem faithful_groupTable (F : RoleModel.FamilyValue) (P : Premises4) (ctx : Nat → Role) (plans : Plans) (hC : RoleModel.FamilyReadsCtx F P ctx) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    GroupReadsOK ctx plans hmem → ∀ (μ : Nat → List Nat → PSet.{4}), Faithful F P μ ctx plans E → ReadsClosed ctx plans E →
      Faithful F P (groupTable F P ctx plans hmem μ) ctx plans E' ∧ ReadsClosed ctx plans E'
  | _, _, _, .nil _, _, μ, hF, hR => ⟨hF, hR⟩
  | _, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, hg, μ, hF, hR => by
      obtain ⟨hm, hrestR⟩ := hg
      obtain ⟨hF', hR'⟩ := faithful_step F P ctx plans hC hF hR hfresh hm
      exact faithful_groupTable F P ctx plans hC hrest hrestR _ hF' hR'

theorem faithful_envTable (F : RoleModel.FamilyValue) (P : Premises4) (ctx : Nat → Role) (plans : Plans) (hC : RoleModel.FamilyReadsCtx F P ctx) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ReadsOKAlong ctx plans hW → Faithful F P (envTable F P ctx plans hW) ctx plans E ∧ ReadsClosed ctx plans E
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

end Rcic.F3.PSet.EvalRole
