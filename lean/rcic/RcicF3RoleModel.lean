import rcic.RcicF3TierGroup

/-!
# The family interpretation parameter in the group invariant

`GInv` below changes precisely the family-entry equation in `FaithfulR`.
It retains the landed `AllSound` and every final-environment `IotaAt`
obligation. `StepAG` retains the entire typed PendA domain and all four
antecedents of the landed group step. No field-shape check is added.

This is an interface, not a producer. In particular neither an arbitrary
`FamilyValue` nor the legacy finite-stage interpretation is asserted sound.
The legacy equalities pin the old contract for consumer migration.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet.RoleModel
open Rcic.Declarative

abbrev FamilyValue := Premises4 → (Nat → List Nat → PSet.{4}) →
  FamData → List Nat → PSet.{4}

/-- Family semantics is the only parameter; all other member roles retain
their literal landed denotations. -/
noncomputable def memberVal (F : FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) : Role → CheckedMember → List Nat → PSet.{4}
  | .plain, m, vs => PSet.memberVal P μ m vs
  | .fam fd, _, vs => F P μ fd vs
  | .ctor fd j, m, vs => piLam (mkM P μ) (σOf vs)
      (ctorEnd (mkM P μ) (σOf vs) fd j (nfOf fd j)) ρ0 m.mtype
  | .recursor fd, m, vs => piLam (mkM P μ) (σOf vs)
      (recEnd (mkM P μ) (σOf vs) fd) ρ0 m.mtype

def Faithful (F : FamilyValue) (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ∀ vs, Equiv (μ r vs) (memberVal F P μ (ctx r) m vs)

/-- The full invariant with the family-role parameter exposed. -/
def GInv (F : FamilyValue) (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) → ∀ μ, Faithful F P μ ctx E →
    AllSound P μ K E ∧ ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

def GInvAt (F : FamilyValue) (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv)
    {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  (∀ r m, E.members r = some m → Efin.members r = some m) →
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) → ∀ μ, Faithful F P μ ctx E →
    AllSound P μ K E ∧ ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

def GroupStepAt (F : FamilyValue) (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  GInv F P K hE → GInv F P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- The repaired A target interface: the same PendA domain, with an explicit
family interpretation. Supplying this argument is part of the repair. -/
def StepAG (F : FamilyValue) (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    (∃ node : RecNode E E' f rr rm, PendA node) → GroupStepAt F P K hE hfam hctors hrec hmem

/-- Elementary logical boundary: with the supplied decidability data,
non-refutability of the universal target is equivalent to producing it.
A single fixture instance cannot establish the left side. -/
theorem stepAG_nonrefutable_iff (F : FamilyValue) (P : Premises4) (K : Nat → Nat) :
    (¬ (StepAG F P K → (Premises4 → False))) ↔ StepAG F P K := by
  constructor
  · intro h
    cases P.dec (StepAG F P K) with
    | isTrue ht => exact ht
    | isFalse hn => exact False.elim (h (fun ht _ => hn ht))
  · intro ht h
    exact h ht P

/-- The old interpretation, retained solely to pin contract fidelity. -/
noncomputable def legacy : FamilyValue := famLim

/-- Elementary definitional fidelity, not a new soundness theorem. -/
theorem memberVal_legacy (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (ro : Role) (m : CheckedMember) (vs : List Nat) :
    memberVal legacy P μ ro m vs = memberValR P μ ro m vs := by cases ro <;> rfl

theorem faithful_legacy (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (E : ResolvedEnv) :
    Faithful legacy P μ ctx E ↔ FaithfulR P μ ctx E := Iff.rfl

theorem gInv_legacy (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) :
    GInv legacy P K hW ↔ PSet.GInv P K hW := Iff.rfl

theorem stepAG_legacy (P : Premises4) (K : Nat → Nat) :
    StepAG legacy P K ↔ TierGroup.StepAG P K := Iff.rfl

end Rcic.F3.PSet.RoleModel
