import rcic.RcicF3Tel
import rcic.RcicF3FalseEnv
import rcic.RcicF3BoundDefs

/-!
# F3 S4b: the interpretation of an admitted environment

`envμ P hW` interprets every member of an `EnvWfT` environment, one member
at a time (`upd`), each by `memberVal` read at the table built so far:

- a definition, theorem or opaque member denotes its body;
- an inductive family denotes the abstraction over its telescope whose end
  value is the empty type value (`tyv ∅`) — exact for constructor-free
  families;
- any other member (axiom, constructor, recursor) denotes the abstraction
  over its telescope with end value `∅`.

`faithful_envμ`: the final table satisfies every member's equation read at
the final table itself (`Faithful`), because each member's type and body
mention only earlier members (`RefsClosed`). Soundness obligations are
then stated about one table only (`RcicF3EnvSound`). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs hasTyT_denRefs groupMembersT_preserve)

namespace PSet

/-- The height-4 interpretation with constant table `μ`. -/
def mkM (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Interp.{4} := ⟨P.dec, U W4, μ⟩

theorem mkM_eq_withμ (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    mkM P μ = withμ (falseM P.dec) μ := rfl

/-- The empty environment of values. -/
def ρ0 : Nat → PSet.{4} := fun _ => pempty

/-- The value of one member, read at the table `μ`. -/
def memberVal (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (m : CheckedMember)
    (vs : List Nat) : PSet.{4} :=
  match m.mclass with
  | .inductiveM => piLam (mkM P μ) (σOf vs) (fun _ => tyv pempty) ρ0 m.mtype
  | .axiomM => piLam (mkM P μ) (σOf vs) (fun _ => pempty) ρ0 m.mtype
  | .constructorM => piLam (mkM P μ) (σOf vs) (fun _ => pempty) ρ0 m.mtype
  | .recursorM => piLam (mkM P μ) (σOf vs) (fun _ => pempty) ρ0 m.mtype
  | _ =>
      match m.body with
      | some b => den (mkM P μ) (fun _ => 0) ρ0 b
      | none => pempty

/-- Override the table at one reference. -/
def upd (μ : Nat → List Nat → PSet.{4}) (r : Nat) (d : List Nat → PSet.{4}) :
    Nat → List Nat → PSet.{4} :=
  fun r' vs => if r' = r then d vs else μ r' vs

theorem upd_eq (μ : Nat → List Nat → PSet.{4}) (r : Nat) (d : List Nat → PSet.{4}) (vs : List Nat) :
    upd μ r d r vs = d vs := if_pos rfl

theorem upd_ne (μ : Nat → List Nat → PSet.{4}) (r : Nat) (d : List Nat → PSet.{4}) {r' : Nat}
    (h : r' ≠ r) (vs : List Nat) : upd μ r d r' vs = μ r' vs := if_neg h

/-- Install the members of a group, in order. -/
def groupμ (P : Premises4) {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' →
    (Nat → List Nat → PSet.{4}) → Nat → List Nat → PSet.{4}
  | _, _, _, .nil _, μ => μ
  | _, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, μ =>
      groupμ P hrest (upd μ r (memberVal P μ m))

/-- The table of an admitted environment. -/
def envμ (P : Premises4) : {E : ResolvedEnv} → EnvWfT E → Nat → List Nat → PSet.{4}
  | _, .empty => fun _ _ => pempty
  | _, .axiom _ r A _ hE _ _ _ _ =>
      upd (envμ P hE) r (memberVal P (envμ P hE) ⟨.axiomM, 0, A, none⟩)
  | _, .definition _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envμ P hE) r (memberVal P (envμ P hE) ⟨.definitionM, 0, A, some v⟩)
  | _, .thm _ r A p hE _ _ _ _ _ _ _ =>
      upd (envμ P hE) r (memberVal P (envμ P hE) ⟨.theoremM, 0, A, some p⟩)
  | _, .opaque _ r A v _ hE _ _ _ _ _ _ _ =>
      upd (envμ P hE) r (memberVal P (envμ P hE) ⟨.opaqueM, 0, A, some v⟩)
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem => groupμ P hmem (envμ P hE)

/-- The references a member's type and body mention are members of `E`. -/
def RefsOK (E : ResolvedEnv) (m : CheckedMember) : Prop :=
  (∀ r, r ∈ denRefs m.mtype → (E.members r).isSome) ∧
    (∀ b, m.body = some b → ∀ r, r ∈ denRefs b → (E.members r).isSome)

/-- Every member's references are members. -/
def RefsClosed (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → RefsOK E m

/-- The table satisfies every member's equation, read at the table itself. -/
def Faithful (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → ∀ vs, μ r vs = memberVal P μ m vs

theorem isSome_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (hfresh : E.members r = none)
    {r' : Nat} (h : (E.members r').isSome) : ((extendEnv E r m).members r').isSome := by
  cases hm : E.members r' with
  | none => rw [hm] at h; exact absurd h (by decide)
  | some m' => rw [members_extend_preserved hfresh r' m' hm]; rfl

theorem refsOK_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (hfresh : E.members r = none)
    {m' : CheckedMember} (h : RefsOK E m') : RefsOK (extendEnv E r m) m' :=
  ⟨fun r' hr' => isSome_extend hfresh (h.1 r' hr'),
    fun b hb r' hr' => isSome_extend hfresh (h.2 b hb r' hr')⟩

theorem refsClosed_step {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hR : RefsClosed E) (hfresh : E.members r = none) (hm : RefsOK E m) :
    RefsClosed (extendEnv E r m) := by
  intro r' m' h
  by_cases hr : r' = r
  · subst hr
    rw [members_extend_eq] at h
    cases h
    exact refsOK_extend hfresh hm
  · rw [members_extend_ne E r m r' hr] at h
    exact refsOK_extend hfresh (hR r' m' h)

theorem memberVal_agree (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} (m : CheckedMember)
    (h1 : ∀ r, r ∈ denRefs m.mtype → ∀ ls, μ₁ r ls = μ₂ r ls)
    (h2 : ∀ b, m.body = some b → ∀ r, r ∈ denRefs b → ∀ ls, μ₁ r ls = μ₂ r ls) (vs : List Nat) :
    memberVal P μ₁ m vs = memberVal P μ₂ m vs := by
  unfold memberVal
  simp only [mkM_eq_withμ]
  cases m.mclass <;> (try exact piLam_agree _ _ _ m.mtype h1 ρ0) <;>
  · cases hb : m.body with
    | some b => exact den_agree _ _ b (h2 b hb) ρ0
    | none => rfl

/-- Tables agree at every reference that is a member. -/
theorem agree_of_upd {E : ResolvedEnv} {r : Nat} (hfresh : E.members r = none)
    (μ : Nat → List Nat → PSet.{4}) (d : List Nat → PSet.{4}) {r' : Nat}
    (h : (E.members r').isSome) (ls : List Nat) : μ r' ls = upd μ r d r' ls := by
  have hne : r' ≠ r := by
    intro he; subst he; rw [hfresh] at h; exact absurd h (by decide)
  rw [upd_ne μ r d hne]

theorem faithful_step (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hF : Faithful P μ E) (hR : RefsClosed E) (hfresh : E.members r = none)
    (hm : RefsOK E m) :
    Faithful P (upd μ r (memberVal P μ m)) (extendEnv E r m) := by
  intro r' m' h vs
  have agreeOf : ∀ {m'' : CheckedMember}, RefsOK E m'' → ∀ vs',
      memberVal P μ m'' vs' = memberVal P (upd μ r (memberVal P μ m)) m'' vs' := fun hm'' vs' =>
    memberVal_agree P _ (fun r'' hr'' ls => agree_of_upd hfresh μ _ (hm''.1 r'' hr'') ls)
      (fun b hb r'' hr'' ls => agree_of_upd hfresh μ _ (hm''.2 b hb r'' hr'') ls) vs'
  by_cases hr : r' = r
  · subst hr
    rw [members_extend_eq] at h
    cases h
    rw [upd_eq]
    exact agreeOf hm vs
  · rw [members_extend_ne E r m r' hr] at h
    rw [upd_ne μ r _ hr, hF r' m' h vs]
    exact agreeOf (hR r' m' h) vs

/-- The group walk keeps both invariants. -/
theorem faithful_groupμ (P : Premises4) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    ∀ (μ : Nat → List Nat → PSet.{4}), Faithful P μ E → RefsClosed E →
      Faithful P (groupμ P hmem μ) E' ∧ RefsClosed E'
  | _, _, _, .nil _, μ, hF, hR => ⟨hF, hR⟩
  | E, _, _, .cons _ r m _ _ hfresh hnobody _ _ _ _ _ _ _ _ hT _ _ hrest, μ, hF, hR => by
      have hm : RefsOK E m :=
        ⟨fun r' hr' => hasTyT_denRefs hT r' hr', fun b hb => by rw [hnobody] at hb; cases hb⟩
      exact faithful_groupμ P hrest _ (faithful_step P hF hR hfresh hm) (refsClosed_step hR hfresh hm)

theorem refsOK_singleton {E : ResolvedEnv} {n : Nat} {A b T : Expr Nat} {k : MemberClass} {ar : Nat}
    {u : Level} (hA : HasTyT E n [] A (.sort u)) (hb : HasTyT E n [] b T) :
    RefsOK E ⟨k, ar, A, some b⟩ :=
  ⟨fun r hr => hasTyT_denRefs hA r hr, fun b' hb' r hr => by
    cases hb'; exact hasTyT_denRefs hb r hr⟩

theorem faithful_envμ (P : Premises4) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    Faithful P (envμ P hW) E ∧ RefsClosed E
  | _, .empty => ⟨fun _ _ h => (Option.noConfusion h), fun _ _ h => (Option.noConfusion h)⟩
  | _, .axiom E r A u hE hfresh hA _ _ => by
      obtain ⟨hF, hR⟩ := faithful_envμ P hE
      have hm : RefsOK E ⟨.axiomM, 0, A, none⟩ :=
        ⟨fun r' hr' => hasTyT_denRefs hA r' hr', fun b hb => by cases hb⟩
      exact ⟨faithful_step P hF hR hfresh hm, refsClosed_step hR hfresh hm⟩
  | _, .definition E r A v u hE hfresh hA hv _ _ _ _ => by
      obtain ⟨hF, hR⟩ := faithful_envμ P hE
      have hm := refsOK_singleton (k := .definitionM) (ar := 0) hA hv
      exact ⟨faithful_step P hF hR hfresh hm, refsClosed_step hR hfresh hm⟩
  | _, .thm E r A p hE hfresh hA hp _ _ _ _ => by
      obtain ⟨hF, hR⟩ := faithful_envμ P hE
      have hm := refsOK_singleton (k := .theoremM) (ar := 0) hA hp
      exact ⟨faithful_step P hF hR hfresh hm, refsClosed_step hR hfresh hm⟩
  | _, .opaque E r A v u hE hfresh hA hv _ _ _ _ => by
      obtain ⟨hF, hR⟩ := faithful_envμ P hE
      have hm := refsOK_singleton (k := .opaqueM) (ar := 0) hA hv
      exact ⟨faithful_step P hF hR hfresh hm, refsClosed_step hR hfresh hm⟩
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem => by
      obtain ⟨hF, hR⟩ := faithful_envμ P hE
      exact faithful_groupμ P hmem _ hF hR

end PSet

end Rcic.F3
