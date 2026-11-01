import rcic.RcicF3RoleModel

/-!
# Canonical tables for the parameterized family role

The installation and faithfulness proof are the landed EnvG construction
with the family interpretation parameter exposed. `FamilyReadsCtx` is the
precise table-congruence interface needed by installation. It is discharged
at the M1 fixtures, not asserted for arbitrary family interpreters.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RoleModel
open Rcic.Declarative

/-- The same allowed read set as the landed family role. -/
def FamilyReads (F : FamilyValue) (P : Premises4) (fd : FamData) : Prop :=
  ∀ (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop),
    AgreeOn μ₁ μ₂ S → RefsIn S (fd.params ++ fd.indices) →
    FamRefsIn (fun r => S r ∨ r = fd.fref) fd → ∀ vs,
      Equiv (F P μ₁ fd vs) (F P μ₂ fd vs)

def FamilyReadsCtx (F : FamilyValue) (P : Premises4) (ctx : Nat → Role) : Prop :=
  ∀ r fd, ctx r = .fam fd → FamilyReads F P fd

theorem familyReadsCtx_plain (F : FamilyValue) (P : Premises4) :
    FamilyReadsCtx F P (fun _ => .plain) := by
  intro _ _ h
  cases h

theorem familyReadsCtx_groupRoles {F : FamilyValue} {P : Premises4}
    {ctx : Nat → Role} {fd : FamData} {f rr : Nat}
    (hC : FamilyReadsCtx F P ctx) (hf : FamilyReads F P fd) :
    FamilyReadsCtx F P (groupRoles fd f rr ctx) := by
  intro r fd' h
  unfold groupRoles at h
  split at h
  · cases h; exact hf
  · split at h
    · cases h
    · split at h
      · cases h
      · exact hC r fd' h

/-- Elementary reuse of the three unchanged roles and the explicit
family congruence law. -/
theorem member_agree {F : FamilyValue} {P : Premises4} {ctx : Nat → Role}
    (hC : FamilyReadsCtx F P ctx) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ₁ μ₂ S) (r : Nat) (m : CheckedMember)
    (hr : ReadsIn S (ctx r) m) (vs : List Nat) :
    Equiv (memberVal F P μ₁ (ctx r) m vs) (memberVal F P μ₂ (ctx r) m vs) := by
  cases he : ctx r with
  | fam fd =>
    rw [he] at hr
    exact hC r fd he μ₁ μ₂ S h hr.2.1 hr.2.2 vs
  | plain =>
    rw [he] at hr
    exact memberValR_agree P h .plain m hr vs
  | ctor fd j =>
    rw [he] at hr
    exact memberValR_agree P h (.ctor fd j) m hr vs
  | recursor fd =>
    rw [he] at hr
    exact memberValR_agree P h (.recursor fd) m hr vs

/-- Install the members of a group at the roles `ctx`. -/
noncomputable def groupTable (F : FamilyValue) (P : Premises4) (ctx : Nat → Role) {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' →
    (Nat → List Nat → PSet.{4}) → Nat → List Nat → PSet.{4}
  | _, _, _, .nil _, μ => μ
  | _, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, μ =>
      groupTable F P ctx hrest (upd μ r (memberVal F P μ (ctx r) m))

/-- The table of an admitted environment, at the roles `ctx`. -/
noncomputable def envTable (F : FamilyValue) (P : Premises4) (ctx : Nat → Role) : {E : ResolvedEnv} → EnvWfT E → Nat → List Nat → PSet.{4}
  | _, .empty => fun _ _ => pempty
  | _, .axiom (arity := arity) _ r A _ hE _ _ _ _ =>
      upd (envTable F P ctx hE) r (memberVal F P (envTable F P ctx hE) (ctx r) ⟨.axiomM, arity, A, none⟩)
  | _, .definition _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envTable F P ctx hE) r (memberVal F P (envTable F P ctx hE) (ctx r) ⟨.definitionM, 0, A, some v⟩)
  | _, .thm _ r A p hE _ _ _ _ _ _ _ =>
      upd (envTable F P ctx hE) r (memberVal F P (envTable F P ctx hE) (ctx r) ⟨.theoremM, 0, A, some p⟩)
  | _, .opaque _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envTable F P ctx hE) r (memberVal F P (envTable F P ctx hE) (ctx r) ⟨.opaqueM, 0, A, some v⟩)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem => groupTable F P ctx hmem (envTable F P ctx hE)

theorem faithful_step (F : FamilyValue) (P : Premises4) (ctx : Nat → Role) (hC : FamilyReadsCtx F P ctx) {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv}
    {r : Nat} {m : CheckedMember} (hF : Faithful F P μ ctx E) (hR : ReadsClosed ctx E)
    (hfresh : E.members r = none) (hm : ReadsIn (Dom E) (ctx r) m) :
    Faithful F P (upd μ r (memberVal F P μ (ctx r) m)) ctx (extendEnv E r m) ∧ ReadsClosed ctx (extendEnv E r m) := by
  have hag := agreeOn_upd hfresh μ (memberVal F P μ (ctx r) m)
  refine ⟨fun r' m' h vs => ?_, fun r' m' h => ?_⟩
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      rw [upd_eq]
      exact member_agree hC hag r' m hm vs
    · rw [members_extend_ne E r m r' hr] at h
      rw [upd_ne μ r _ hr]
      exact (hF r' m' h vs).trans (member_agree hC hag r' m' (hR r' m' h) vs)
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      exact hm.mono (dom_extend hfresh)
    · rw [members_extend_ne E r m r' hr] at h
      exact (hR r' m' h).mono (dom_extend hfresh)

theorem faithful_groupTable (F : FamilyValue) (P : Premises4) (ctx : Nat → Role) (hC : FamilyReadsCtx F P ctx) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    GroupReadsOK ctx hmem → ∀ (μ : Nat → List Nat → PSet.{4}), Faithful F P μ ctx E → ReadsClosed ctx E →
      Faithful F P (groupTable F P ctx hmem μ) ctx E' ∧ ReadsClosed ctx E'
  | _, _, _, .nil _, _, μ, hF, hR => ⟨hF, hR⟩
  | _, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, hg, μ, hF, hR => by
      obtain ⟨hm, hrestR⟩ := hg
      obtain ⟨hF', hR'⟩ := faithful_step F P ctx hC hF hR hfresh hm
      exact faithful_groupTable F P ctx hC hrest hrestR _ hF' hR'

theorem faithful_envTable (F : FamilyValue) (P : Premises4) (ctx : Nat → Role) (hC : FamilyReadsCtx F P ctx) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ReadsOKAlong ctx hW → Faithful F P (envTable F P ctx hW) ctx E ∧ ReadsClosed ctx E
  | _, .empty, _ => ⟨fun _ _ h => (Option.noConfusion h), fun _ _ h => (Option.noConfusion h)⟩
  | _, .axiom E r A u hE hfresh _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx hC hE hR0
      exact faithful_step F P ctx hC hF hR hfresh hm
  | _, .definition E r A v u hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx hC hE hR0
      exact faithful_step F P ctx hC hF hR hfresh hm
  | _, .thm E r A p hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx hC hE hR0
      exact faithful_step F P ctx hC hF hR hfresh hm
  | _, .opaque E r A v u hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx hC hE hR0
      exact faithful_step F P ctx hC hF hR hfresh hm
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem, hRA => by
      obtain ⟨hR0, hg⟩ := hRA
      obtain ⟨hF, hR⟩ := faithful_envTable F P ctx hC hE hR0
      exact faithful_groupTable F P ctx hC hmem hg _ hF hR

end Rcic.F3.PSet.RoleModel
