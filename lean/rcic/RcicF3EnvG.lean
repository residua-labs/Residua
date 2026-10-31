import rcic.RcicF3RecValRec

/-!
# F3 S5a-11: the table of an environment with inductive groups

Each member is given a `Role`: a plain member (singleton) keeps
`memberVal`; a group's family, constructors and recursor get the group's
values (`famEnd`, `ctorEnd`, `recEnd` over their stored types), read off the
group's recursor admission (`scanRec`). `envCtx` assigns the roles of a
whole `EnvWfT` derivation; `envμR` installs the members, one at a time, at
the roles of the final environment; `faithfulR_envμR`: the final table
satisfies every member's equation read at itself, up to `≈`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs hasTyT_denRefs groupMembersT_preserve)

namespace PSet

/-- A member's role in its group. -/
inductive Role : Type
  | plain
  | fam (fd : FamData)
  | ctor (fd : FamData) (j : Nat)
  | recursor (fd : FamData)

/-- The value of a member at its role, read at the table `μ`. -/
noncomputable def memberValR (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Role → CheckedMember → List Nat → PSet.{4}
  | .plain, m, vs => memberVal P μ m vs
  | .fam fd, _, vs => famLim P μ fd vs
  | .ctor fd j, m, vs => piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) fd j (nfOf fd j)) ρ0 m.mtype
  | .recursor fd, m, vs => piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) fd) ρ0 m.mtype

/-- The group's data, read off the admission of its recursor (the member of class
`recursorM`). -/
def scanRec {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → Option FamData
  | _, _, _, .nil _ => none
  | _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      match hadm with
      | .recursor a _ _ _ _ _ _ => if m.mclass = .recursorM then some (famDataOf a) else scanRec hrest
      | _ => scanRec hrest

/-- The roles of one group: family `f`, recursor `rr`, constructors in between. -/
def groupRoles (fd : FamData) (f rr : Nat) (ctx : Nat → Role) : Nat → Role := fun r =>
  if r = f then .fam fd else if r = rr then .recursor fd else if f < r ∧ r < rr then .ctor fd (r - f - 1) else ctx r

/-- The roles of an admitted environment. -/
def envCtx : {E : ResolvedEnv} → EnvWfT E → Nat → Role
  | _, .empty => fun _ => .plain
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCtx hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCtx hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCtx hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCtx hE
  | _, .group _ f _ _ rr _ _ hE _ _ _ hmem =>
      match scanRec hmem with
      | some fd => groupRoles fd f rr (envCtx hE)
      | none => envCtx hE

/-- A reference-aware value rule. The legacy role interpretation is its default. -/
abbrev MemberValue := Nat → (Nat → List Nat → PSet.{4}) → Role → CheckedMember → List Nat → PSet.{4}

noncomputable abbrev roleValue (P : Premises4) : MemberValue :=
  fun _ μ ro m vs => memberValR P μ ro m vs

/-- Install the members of a group at the roles `ctx`. -/
noncomputable def groupμBy (value : MemberValue) (ctx : Nat → Role) {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' →
    (Nat → List Nat → PSet.{4}) → Nat → List Nat → PSet.{4}
  | _, _, _, .nil _, μ => μ
  | _, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, μ =>
      groupμBy value ctx hrest (upd μ r (value r μ (ctx r) m))

/-- The table of an admitted environment, at the roles `ctx`. -/
noncomputable def envμBy (value : MemberValue) (ctx : Nat → Role) : {E : ResolvedEnv} → EnvWfT E → Nat → List Nat → PSet.{4}
  | _, .empty => fun _ _ => pempty
  | _, .axiom (arity := arity) _ r A _ hE _ _ _ _ =>
      upd (envμBy value ctx hE) r (value r (envμBy value ctx hE) (ctx r) ⟨.axiomM, arity, A, none⟩)
  | _, .definition _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envμBy value ctx hE) r (value r (envμBy value ctx hE) (ctx r) ⟨.definitionM, 0, A, some v⟩)
  | _, .thm _ r A p hE _ _ _ _ _ _ _ =>
      upd (envμBy value ctx hE) r (value r (envμBy value ctx hE) (ctx r) ⟨.theoremM, 0, A, some p⟩)
  | _, .opaque _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envμBy value ctx hE) r (value r (envμBy value ctx hE) (ctx r) ⟨.opaqueM, 0, A, some v⟩)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem => groupμBy value ctx hmem (envμBy value ctx hE)

/-- Legacy group installation, using the shared value-rule fold. -/
noncomputable def groupμR (P : Premises4) (ctx : Nat → Role) {S E E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E ms E')
    (μ : Nat → List Nat → PSet.{4}) : Nat → List Nat → PSet.{4} :=
  groupμBy (roleValue P) ctx hmem μ

/-- Legacy environment installation, using the shared value-rule fold. -/
noncomputable def envμR (P : Premises4) (ctx : Nat → Role) {E : ResolvedEnv}
    (hW : EnvWfT E) : Nat → List Nat → PSet.{4} :=
  envμBy (roleValue P) ctx hW

/-- The references a member's value reads at its role lie in `S`. -/
def ReadsIn (S : Nat → Prop) : Role → CheckedMember → Prop
  | .plain, m => (∀ r, r ∈ denRefs m.mtype → S r) ∧ (∀ b, m.body = some b → ∀ r, r ∈ denRefs b → S r)
  | .fam fd, m => (∀ r, r ∈ denRefs m.mtype → S r) ∧ RefsIn S (fd.params ++ fd.indices) ∧
      FamRefsIn (fun r => S r ∨ r = fd.fref) fd
  | .ctor _ _, m => ∀ r, r ∈ denRefs m.mtype → S r
  | .recursor _, m => ∀ r, r ∈ denRefs m.mtype → S r

theorem ReadsIn.mono {S S' : Nat → Prop} (hS : ∀ r, S r → S' r) : {ro : Role} → {m : CheckedMember} →
    ReadsIn S ro m → ReadsIn S' ro m
  | .plain, _, ⟨h1, h2⟩ => ⟨fun r hr => hS r (h1 r hr), fun b hb r hr => hS r (h2 b hb r hr)⟩
  | .fam _, _, ⟨h1, h2, h3⟩ => ⟨fun r hr => hS r (h1 r hr), fun e he r hr => hS r (h2 e he r hr),
      fun c hc => ⟨fun e he r hr => ((h3 c hc).1 e he r hr).imp (hS r) id,
        fun e he r hr => ((h3 c hc).2 e he r hr).imp (hS r) id⟩⟩
  | .ctor _ _, _, h1 => fun r hr => hS r (h1 r hr)
  | .recursor _, _, h1 => fun r hr => hS r (h1 r hr)

theorem recEnd_of_dec {M M' : Interp.{4}} (h : M.dec = M'.dec) (σ : Nat → Nat) (fd : FamData)
    (ρ : Nat → PSet.{4}) : recEnd M σ fd ρ = recEnd M' σ fd ρ := by
  unfold recEnd
  rw [recCore_of_dec h]
  unfold cond
  rw [h]

/-- Agreeing tables give `≈`-equal values. -/
theorem memberValR_agree (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ₁ μ₂ S) : (ro : Role) → (m : CheckedMember) → ReadsIn S ro m → (vs : List Nat) →
    Equiv (memberValR P μ₁ ro m vs) (memberValR P μ₂ ro m vs)
  | .plain, m, ⟨h1, h2⟩, vs => by
      show Equiv (memberVal P μ₁ m vs) (memberVal P μ₂ m vs)
      rw [memberVal_agree P m (fun r hr ls => h r (h1 r hr) ls) (fun b hb r hr ls => h r (h2 b hb r hr) ls) vs]
      exact Equiv.rfl
  | .fam fd, _, ⟨_, h2, h3⟩, vs =>
      famLim_agreeOn P (fun r hr ls => by rw [h r hr ls]; exact Equiv.rfl) fd h2 h3 vs
  | .ctor fd j, m, h1, vs =>
      piLam_agreeOn P h (σOf vs) (ctorEnd_resp _ _ fd j _) (fun _ => Equiv.rfl) m.mtype h1 ρ0
  | .recursor fd, m, h1, vs =>
      piLam_agreeOn P h (σOf vs) (recEnd_resp _ _ fd) (fun ρ => by
        rw [recEnd_of_dec (M := mkM P μ₁) (M' := mkM P μ₂) rfl]; exact Equiv.rfl) m.mtype h1 ρ0

/-- A value rule respects the existing semantic read relation. -/
def ValueAgrees (value : MemberValue) : Prop :=
  ∀ {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}, AgreeOn μ₁ μ₂ S →
    ∀ r ro m, ReadsIn S ro m → ∀ vs, Equiv (value r μ₁ ro m vs) (value r μ₂ ro m vs)

theorem roleValue_agrees (P : Premises4) : ValueAgrees (roleValue P) :=
  fun h _ ro m hm vs => memberValR_agree P h ro m hm vs

/-- The table satisfies the selected member value equations. -/
def FaithfulBy (value : MemberValue) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ∀ vs, Equiv (μ r vs) (value r μ (ctx r) m vs)

/-- The legacy table equation is the default value-rule specialization. -/
def FaithfulR (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ∀ vs, Equiv (μ r vs) (memberValR P μ (ctx r) m vs)

/-- The members of `E`. -/
def Dom (E : ResolvedEnv) (r : Nat) : Prop := (E.members r).isSome

/-- Every member's reads lie in the environment. -/
def ReadsClosed (ctx : Nat → Role) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ReadsIn (Dom E) (ctx r) m

theorem dom_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (hfresh : E.members r = none) :
    ∀ r', Dom E r' → Dom (extendEnv E r m) r' := fun _ h => isSome_extend hfresh h

theorem agreeOn_upd {E : ResolvedEnv} {r : Nat} (hfresh : E.members r = none)
    (μ : Nat → List Nat → PSet.{4}) (d : List Nat → PSet.{4}) : AgreeOn μ (upd μ r d) (Dom E) :=
  fun r' hr' ls => agree_of_upd hfresh μ d hr' ls

theorem faithfulBy_step (value : MemberValue) (hAgree : ValueAgrees value) (ctx : Nat → Role) {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv}
    {r : Nat} {m : CheckedMember} (hF : FaithfulBy value μ ctx E) (hR : ReadsClosed ctx E)
    (hfresh : E.members r = none) (hm : ReadsIn (Dom E) (ctx r) m) :
    FaithfulBy value (upd μ r (value r μ (ctx r) m)) ctx (extendEnv E r m) ∧ ReadsClosed ctx (extendEnv E r m) := by
  have hag := agreeOn_upd hfresh μ (value r μ (ctx r) m)
  refine ⟨fun r' m' h vs => ?_, fun r' m' h => ?_⟩
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      rw [upd_eq]
      exact hAgree hag r' (ctx r') m hm vs
    · rw [members_extend_ne E r m r' hr] at h
      rw [upd_ne μ r _ hr]
      exact (hF r' m' h vs).trans (hAgree hag r' (ctx r') m' (hR r' m' h) vs)
  · by_cases hr : r' = r
    · subst hr
      rw [members_extend_eq] at h
      cases h
      exact hm.mono (dom_extend hfresh)
    · rw [members_extend_ne E r m r' hr] at h
      exact (hR r' m' h).mono (dom_extend hfresh)

theorem faithfulR_step (P : Premises4) (ctx : Nat → Role) {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv}
    {r : Nat} {m : CheckedMember} (hF : FaithfulR P μ ctx E) (hR : ReadsClosed ctx E)
    (hfresh : E.members r = none) (hm : ReadsIn (Dom E) (ctx r) m) :
    FaithfulR P (upd μ r (memberValR P μ (ctx r) m)) ctx (extendEnv E r m) ∧ ReadsClosed ctx (extendEnv E r m) :=
  faithfulBy_step (roleValue P) (roleValue_agrees P) ctx hF hR hfresh hm

/-- Each group member's reads lie in the group built before it. -/
def GroupReadsOK (ctx : Nat → Role) {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' → Prop
  | _, _, _, .nil _ => True
  | E, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest => ReadsIn (Dom E) (ctx r) m ∧ GroupReadsOK ctx hrest

/-- Each member's reads lie in the environment before it. -/
def ReadsOKAlong (ctx : Nat → Role) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom (arity := arity) E r A _ hE _ _ _ _ => ReadsOKAlong ctx hE ∧ ReadsIn (Dom E) (ctx r) ⟨.axiomM, arity, A, none⟩
  | _, .definition E r A v _ hE _ _ _ _ _ _ _ =>
      ReadsOKAlong ctx hE ∧ ReadsIn (Dom E) (ctx r) ⟨.definitionM, 0, A, some v⟩
  | _, .thm E r A p hE _ _ _ _ _ _ _ => ReadsOKAlong ctx hE ∧ ReadsIn (Dom E) (ctx r) ⟨.theoremM, 0, A, some p⟩
  | _, .opaque E r A v _ hE _ _ _ _ _ _ _ =>
      ReadsOKAlong ctx hE ∧ ReadsIn (Dom E) (ctx r) ⟨.opaqueM, 0, A, some v⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem => ReadsOKAlong ctx hE ∧ GroupReadsOK ctx hmem

theorem faithfulBy_groupμBy (value : MemberValue) (hAgree : ValueAgrees value) (ctx : Nat → Role) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    GroupReadsOK ctx hmem → ∀ (μ : Nat → List Nat → PSet.{4}), FaithfulBy value μ ctx E → ReadsClosed ctx E →
      FaithfulBy value (groupμBy value ctx hmem μ) ctx E' ∧ ReadsClosed ctx E'
  | _, _, _, .nil _, _, μ, hF, hR => ⟨hF, hR⟩
  | _, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, hg, μ, hF, hR => by
      obtain ⟨hm, hrestR⟩ := hg
      obtain ⟨hF', hR'⟩ := faithfulBy_step value hAgree ctx hF hR hfresh hm
      exact faithfulBy_groupμBy value hAgree ctx hrest hrestR _ hF' hR'

theorem faithfulBy_envμBy (value : MemberValue) (hAgree : ValueAgrees value) (ctx : Nat → Role) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ReadsOKAlong ctx hW → FaithfulBy value (envμBy value ctx hW) ctx E ∧ ReadsClosed ctx E
  | _, .empty, _ => ⟨fun _ _ h => (Option.noConfusion h), fun _ _ h => (Option.noConfusion h)⟩
  | _, .axiom E r A u hE hfresh _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithfulBy_envμBy value hAgree ctx hE hR0
      exact faithfulBy_step value hAgree ctx hF hR hfresh hm
  | _, .definition E r A v u hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithfulBy_envμBy value hAgree ctx hE hR0
      exact faithfulBy_step value hAgree ctx hF hR hfresh hm
  | _, .thm E r A p hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithfulBy_envμBy value hAgree ctx hE hR0
      exact faithfulBy_step value hAgree ctx hF hR hfresh hm
  | _, .opaque E r A v u hE hfresh _ _ _ _ _ _, hRA => by
      obtain ⟨hR0, hm⟩ := hRA
      obtain ⟨hF, hR⟩ := faithfulBy_envμBy value hAgree ctx hE hR0
      exact faithfulBy_step value hAgree ctx hF hR hfresh hm
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem, hRA => by
      obtain ⟨hR0, hg⟩ := hRA
      obtain ⟨hF, hR⟩ := faithfulBy_envμBy value hAgree ctx hE hR0
      exact faithfulBy_groupμBy value hAgree ctx hmem hg _ hF hR

theorem faithfulR_groupμR (P : Premises4) (ctx : Nat → Role) {S : ResolvedEnv}
    {E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E ms E')
    (hg : GroupReadsOK ctx hmem) (μ : Nat → List Nat → PSet.{4})
    (hF : FaithfulR P μ ctx E) (hR : ReadsClosed ctx E) :
    FaithfulR P (groupμR P ctx hmem μ) ctx E' ∧ ReadsClosed ctx E' :=
  faithfulBy_groupμBy (roleValue P) (roleValue_agrees P) ctx hmem hg μ hF hR

theorem faithfulR_envμR (P : Premises4) (ctx : Nat → Role) {E : ResolvedEnv} (hW : EnvWfT E)
    (hR : ReadsOKAlong ctx hW) :
    FaithfulR P (envμR P ctx hW) ctx E ∧ ReadsClosed ctx E :=
  faithfulBy_envμBy (roleValue P) (roleValue_agrees P) ctx hW hR

end PSet

end Rcic.F3
