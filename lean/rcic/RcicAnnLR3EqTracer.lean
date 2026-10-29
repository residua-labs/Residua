import rcic.RcicAnnLR3IotaRecursorArms
import rcic.RcicAnnEqLargeFixture
import rcic.RcicAnnLR3KindCandidateProbe
import rcic.RcicAnnLR3NeutralExtraction
import rcic.RcicAnnLR3GuardedNeutralBoundary

/-!
# Early Eq tracer: J's recursor arms in the candidate design

The AnySort Eq group is the admitted `EqLargeFixture` (family 63, field-free
refl 64, recursor 65 with a motive in any `Sort u`).

**(1) Conv ι at refl, actual.** The refl constructor has no fields, so every
ι walk in this environment is first-order (`eq_firstOrderArity`). The landed
recursor law then supplies the `Conv_iota` and `Conv_structIota` arms for
every code system in the plain recursor semantics (`eq_conv_iota`,
`eq_conv_structIota`).

**(2) Ty of Eq.rec at a non-Prop motive: J's retyping (b ≡ a).** In the
candidate design a proof of `Eq a b` is the refl value `r`, with the indices
related by the domain relation (`eqRel`). That relation is saturated and
proof-irrelevant. The motive is an invariant candidate of kind
`A → Eq → Sort` (R8, `KindCandidateProbe`). The call is any operation of the
major that computes to the minor at `r` (the ι law). `j_retype`: the call at
a proof of `Eq a b` is related in the motive at `(b, h)`, because it equals
the minor, which lives at `(a, refl)`, and invariance moves it. The motive's
codomain need not be Prop.
Mutant `index_free_mutant`: without the index relation, an invariant motive
sends the minor to an empty relation at `b`.

In an environment that realizes the context, a proof variable is bound to a
member of `eqRel`, i.e. to `r`, so a variable-major call computes. A stuck
call arises only from reflection:

**(3) Boundary `stuck_j_boundary` (all premises constructed).** The recursor
hook applies the major to its case selector. Suppose a proof variable is
reflected as a neutral atom and proofs are irrelevant (the atom is related
to the refl value). Then any realizer of the call relates the minor with a
stuck application. No exact relation, such as one for a relevant inductive
type, relates them. `stuck_j_boundary_congr` strengthens this to every
head-separating relation. That includes NbE-style neutral congruence
(`stuckCongr` relates any two stuck calls at the neutral major), because
irrelevance pairs a computing call with a stuck one, not two stuck ones. The
landed `GuardedNeutralBoundary.atom_application_not_sort` is the type-valued
case: such a stuck call is not a sort member at any level.

**(4) Boundary `girard_no_neutralSupport`.** Reflecting a proof variable as
the refl value instead requires the indices to be related. `NeutralSupport`
puts a reflected value in every code's relation, so a model with an empty
code (`Eq` at apart indices, or `∀ X : Prop, X`) has none
(`no_neutralSupport_of_empty`). The closed Girard code system (plain
saturated candidates, `codeSystemS`) has the empty code `∀ X : Prop, X`.
The repair is open realizers: in the open system candidates contain the
reflections (CR3), and `CandidateReflection.neutralSupport` supplies a
`NeutralSupport`; consistency is then a statement about closed realizers.

**Consequence for the design.** J is sound in realizing environments,
including its retyping. Generic environments for open contexts cannot come
from `NeutralSupport` on a content model whose relations hold only closed
values, when the context has an Eq hypothesis at apart indices. They need
open realizers (CR3, as in `CandidateReflection`), with a guarded K
completion at Eq (`EqKRepair`).

Not claimed: the paired `Ty` arm for the recursor constant of the actual
environment, a reader of source motives into kind candidates, and the
generic-environment construction. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EqTracer

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open IotaRecursor

/-! ## (1) ι at refl for the actual AnySort Eq environment -/

theorem eq_members {r : Nat} {m : CheckedMemberA} (h : EqLargeFixture.env.members r = some m) :
    (r = 63 ∧ m = EqLargeFixture.fam) ∨ (r = 64 ∧ m = EqLargeFixture.reflMember) ∨
      (r = 65 ∧ m = EqLargeFixture.recMember) := by
  simp only [EqLargeFixture.env, EqLargeFixture.prefixEnv, EqLargeFixture.famEnv, extendEnvA,
    emptyEnvA] at h
  by_cases h65 : r = 65
  · rw [if_pos h65] at h; injection h with h; exact .inr (.inr ⟨h65, h.symm⟩)
  · rw [if_neg h65] at h
    by_cases h64 : r = 64
    · rw [if_pos h64] at h; injection h with h; exact .inr (.inl ⟨h64, h.symm⟩)
    · rw [if_neg h64] at h
      by_cases h63 : r = 63
      · rw [if_pos h63] at h; injection h with h; exact .inl ⟨h63, h.symm⟩
      · rw [if_neg h63] at h; exact Option.noConfusion h

theorem eq_group_data :
    (iotaGroupA EqLargeFixture.env 65 64).map
      (fun g => (g.nparams, g.familyRef, ctorTypeOf g)) =
      some (2, 63, EqLargeFixture.reflTy) := by decide

theorem eq_shapes : ctorShapesA 63 2 EqLargeFixture.reflTy = some [] := by decide

/-- The refl constructor has no fields, so every ι walk is first-order. -/
theorem eq_firstOrderArity : FirstOrderArity EqLargeFixture.env := by
  intro recRef c g shapes pre ls args ctorAfter hg hsh _ _
  obtain ⟨hrecM, hrecC, hctorM, hctorC, _⟩ := iotaGroupA_some hg
  rcases eq_members hrecM with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨hr, _⟩ <;>
    try (rw [hm] at hrecC; exact absurd hrecC (by decide))
  subst hr
  rcases eq_members hctorM with ⟨_, hm⟩ | ⟨hc, _⟩ | ⟨_, hm⟩ <;>
    try (rw [hm] at hctorC; exact absurd hctorC (by decide))
  subst hc
  have hd := eq_group_data
  rw [hg] at hd
  injection hd with hd
  injection hd with hnp hd
  injection hd with hfam hty
  rw [hnp, hfam, hty, eq_shapes] at hsh
  injection hsh with hsh
  subst hsh
  cases args.drop g.nparams <;> trivial

/-- Conv ι (in particular at refl) for the AnySort Eq environment, over every
code system. -/
theorem eq_conv_iota (C : CodeSystem) (n : Nat) :
    PairedArms.Conv_iota
      (EnvironmentEval.annSemantics C EqLargeFixture.env (iotaHook EqLargeFixture.env))
      EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) n :=
  conv_iota_plain C EqLargeFixture.env eq_firstOrderArity n

theorem eq_conv_structIota (C : CodeSystem) (n : Nat) :
    PairedArms.Conv_structIota
      (EnvironmentEval.annSemantics C EqLargeFixture.env (iotaHook EqLargeFixture.env))
      EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) n :=
  conv_structIota_plain C EqLargeFixture.env eq_firstOrderArity n

/-! ## (2) J retyping in the candidate design

A proof of `Eq a b` over a domain relation `D` is the refl value `r` (the
constructor is field free), and the indices are related. The motive is an
invariant candidate of the dependent kind `A → Eq → Sort`, with the proof
domain read irrelevantly. The recursor call is any operation `j` of the
major that computes to the minor at `r` (the source ι law). -/

open KindCandidateProbe
open CandidateTowerProbe

def reflRel (r : Value) : Relation := fun h h' => ValueEq h r ∧ ValueEq h' r

def eqRel (D : Relation) (r a b : Value) : Relation := fun h h' => D a b ∧ reflRel r h h'

theorem eqRel_sat {D : Relation} {r a b : Value} (hr : r .bot) : Sat (eqRel D r a b) :=
  ⟨⟨fun ⟨hab, h, h'⟩ => ⟨hab, h', h⟩, fun ⟨hab, h, _⟩ ⟨_, _, h'⟩ => ⟨hab, h, h'⟩⟩,
    fun _ _ ⟨_, h, _⟩ => (h .bot).mpr hr⟩

/-- Proof irrelevance: any two members are related. -/
theorem eqRel_irrelevant {D : Relation} {r a b h h' : Value} (hh : eqRel D r a b h h)
    (hh' : eqRel D r a b h' h') : eqRel D r a b h h' :=
  ⟨hh.1, hh.2.1, hh'.2.1⟩

/-- **J retyping.** The call at a proof of `Eq a b` computes to the minor,
which lives in the motive at `(a, refl)`; invariance of the motive moves it
to `(b, h)`. -/
theorem j_retype {D : Relation} {r a b h h' m m' : Value} {j j' : Value → Value}
    {C : CR (.arrT (.arrT .star))}
    (hC : Inv (.arrT (.arrT .star)) (D, (reflRel r, ())) C C)
    (hab : eqRel D r a b h h') (hm : C a r m m')
    (hι : ValueEq (j r) m) (hι' : ValueEq (j' r) m') :
    C b h (j h) (j' h') := by
  have hs : Same (C a r) (C b h) :=
    (hC a b hab.1 r h ⟨ValueEq.refl r, hab.2.1⟩).2.2
  rw [NeutralCodes.valueEq_eq hab.2.1, NeutralCodes.valueEq_eq hab.2.2,
    NeutralCodes.valueEq_eq hι, NeutralCodes.valueEq_eq hι']
  rw [NeutralCodes.valueEq_eq hab.2.1] at hs
  exact (hs m m').mp hm

/-- The exact relation on bottom-carrying values. -/
def exactRel : Relation := fun x y => ValueEq x y ∧ x .bot

theorem exactRel_laws : Laws exactRel :=
  ⟨fun ⟨h, hx⟩ => ⟨h.symm, (h .bot).mp hx⟩, fun ⟨h, hx⟩ ⟨g, _⟩ => ⟨h.trans g, hx⟩⟩

def badMotive : CR (.arrT (.arrT .star)) := fun x _ => badFamily x

theorem badMotive_inv (r : Value) :
    Inv (.arrT (.arrT .star)) (exactRel, (reflRel r, ())) badMotive badMotive := by
  intro x y hxy _ _ _
  rw [NeutralCodes.valueEq_eq hxy.1]
  exact ⟨badFamily_sat y, badFamily_sat y, fun _ _ => Iff.rfl⟩

/-- **Mutant: the index relation is load-bearing.** With an index-free proof
relation, `bottom` would prove `Eq mark bottom`, the motive is invariant,
the minor lives at `mark`, and the retyped call does not live at `bottom`.
The indices are not related by the exact relation. -/
theorem index_free_mutant :
    reflRel bottom bottom bottom ∧
    Inv (.arrT (.arrT .star)) (exactRel, (reflRel bottom, ())) badMotive badMotive ∧
    badMotive mark bottom bottom bottom ∧ ¬ badMotive bottom bottom bottom bottom ∧
    ¬ exactRel mark bottom := by
  refine ⟨⟨ValueEq.refl _, ValueEq.refl _⟩, badMotive_inv bottom, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, Or.inr rfl⟩
  · rintro ⟨_, _, h⟩
    cases h
  · rintro ⟨h, _⟩
    have hb := (h _).mp (Or.inr rfl : mark (.spine 0 []))
    cases hb

/-! ## (3) Boundary: a stuck variable-major J with proof irrelevance

The recursor hook applies the major to the case selector. If a proof
variable is reflected as a neutral atom, then its call is a stuck
application. Proof irrelevance relates that atom to the refl value, so any
realizer of the call must relate the minor with the stuck application. No
exact relation (as for a relevant inductive type) can do so. -/

def minorV : Value := NeutralPER.neutralAtom 1

def reflV : Value := UnifiedPi.legalGraph (fun _ _ => True) (fun _ => minorV)

def stuckMajor : Value := NeutralPER.neutralAtom 7

def call (S h : Value) : Value := NeutralPi.applyValue h S

theorem reflV_call (S : Value) : ValueEq (call S reflV) minorV :=
  UnifiedPi.applyValue_legalGraph (fun _ _ => .bot EnvI.bot (.const 1 []))
    (fun _ _ c hc => ⟨[], by simp, fun _ _ _ => hc⟩) True.intro

theorem minorV_not_stuck (c : CptI) (h : minorV c) (hc : c = .spine 7 [.bot]) : False := by
  subst hc
  rcases approxI_const_inv h with h | h
  · cases h
  · exact absurd (CptI.spine.inj h).1 (by decide)

/-- The proof-irrelevant relation on the two proofs. -/
def proofs : Relation := fun h h' =>
  (ValueEq h reflV ∨ ValueEq h stuckMajor) ∧ (ValueEq h' reflV ∨ ValueEq h' stuckMajor)

theorem stuck_j_boundary (S : Value) (hS : S .bot) :
    Laws proofs ∧ proofs reflV stuckMajor ∧ ValueEq (call S reflV) minorV ∧
    ¬ ∃ N : Relation, (∀ x y, N x y → ValueEq x y) ∧
      ∀ h h', proofs h h' → N (call S h) (call S h') := by
  refine ⟨⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, _⟩ ⟨_, b⟩ => ⟨a, b⟩⟩,
    ⟨.inl (ValueEq.refl _), .inr (ValueEq.refl _)⟩, reflV_call S, ?_⟩
  rintro ⟨N, hN, hJ⟩
  have he := (reflV_call S).symm.trans
    (hN _ _ (hJ _ _ ⟨.inl (ValueEq.refl _), .inr (ValueEq.refl _)⟩))
  have hobs := GuardedNeutralBoundary.atom_application_observed 7 S hS
  exact minorV_not_stuck _ ((he _).mpr hobs) rfl

/-- A relation separates the stuck head when it never relates a value
carrying the stuck observation to one without it. Exact relations do, and
so does a neutral congruence that relates stuck calls only to stuck calls
(`stuckCongr`). -/
def HeadSeparating (N : Relation) : Prop :=
  ∀ x y, N x y → (x (.spine 7 [.bot]) ↔ y (.spine 7 [.bot]))

/-- The coarsest congruence on the stuck calls at the neutral major (any
two selectors), exact elsewhere. -/
def stuckCongr : Relation := fun x y =>
  ValueEq x y ∨ ∃ S S' : Value, S .bot ∧ S' .bot ∧
    ValueEq x (call S stuckMajor) ∧ ValueEq y (call S' stuckMajor)

theorem stuckCongr_headSeparating : HeadSeparating stuckCongr := by
  rintro x y (h | ⟨S, S', hS, hS', hx, hy⟩)
  · exact h _
  · exact ⟨fun _ => (hy _).mpr (GuardedNeutralBoundary.atom_application_observed 7 S' hS'),
      fun _ => (hx _).mpr (GuardedNeutralBoundary.atom_application_observed 7 S hS)⟩

theorem stuckCongr_relates_stuck {S S' : Value} (hS : S .bot) (hS' : S' .bot) :
    stuckCongr (call S stuckMajor) (call S' stuckMajor) :=
  .inr ⟨S, S', hS, hS', ValueEq.refl _, ValueEq.refl _⟩

/-- **The boundary survives neutral congruence.** No head-separating relation
realizes the call over the proof-irrelevant proofs: irrelevance pairs the
refl value (whose call computes to the minor) with the neutral proof (whose
call is stuck), and that pair is not a pair of stuck calls. -/
theorem stuck_j_boundary_congr (S : Value) (hS : S .bot) (N : Relation)
    (hN : HeadSeparating N) : ¬ ∀ h h', proofs h h' → N (call S h) (call S h') := by
  intro hJ
  have h := hJ _ _ ⟨.inl (ValueEq.refl _), .inr (ValueEq.refl _)⟩
  have hobs := (hN _ _ h).mpr (GuardedNeutralBoundary.atom_application_observed 7 S hS)
  exact minorV_not_stuck _ ((reflV_call S _).mp hobs) rfl

/-! ## (4) Boundary: NeutralSupport needs every type inhabited

`NeutralSupport.reflect_member` puts a reflected value in the relation of
every code. A model whose relations are on closed values only and that has
an empty code (an Eq at apart indices, or `∀ X : Prop, X`) admits no
`NeutralSupport`. The closed Girard system (plain saturated candidates,
`codeSystemS`) is such a model. The open system, whose candidates contain
the reflections (CR3), has one: `CandidateReflection.neutralSupport`. -/

theorem no_neutralSupport_of_empty {M : AnnSemantics} {k : Option Nat} {V : Value}
    {R : Relation} (hc : M.Code k V R) (hempty : ∀ x, ¬ Member R x)
    (S : NeutralExtraction.NeutralSupport M) : False :=
  hempty _ (S.reflect_member hc 0)

open CandidateCodeSystem in
/-- `∀ X : Prop, X`. -/
def falseCode : GCode 0 := .pi (.univ 0) (.var 0 0)

open CandidateCodeSystem in
theorem falseCode_kinded : Kinded [] falseCode := ⟨trivial, rfl⟩

open CandidateCodeSystem in
theorem falseCode_empty (x : Value) : ¬ Member (ElS σ0 ρ0 falseCode) x := by
  rintro ⟨_, _, h⟩
  have hu : ElS σ0 ρ0 (GCode.univ 0) (image σ0 (GCode.neutral 0 0))
      (image σ0 (GCode.neutral 0 0)) :=
    ⟨GCode.neutral 0 0, (by decide : (0 : Nat) ≠ 11), ValueEq.refl _, ValueEq.refl _⟩
  have hR : Sat (fun _ _ => False) := ⟨⟨fun h => h.elim, fun h _ => h.elim⟩, fun _ _ h => h.elim⟩
  exact (h _ _ hu _ hR).1.1

open CandidateCodeSystem in
/-- The closed Girard code system admits no `NeutralSupport`. -/
theorem girard_no_neutralSupport (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (S : NeutralExtraction.NeutralSupport (EnvironmentEval.annSemantics codeSystemS E H)) :
    False :=
  no_neutralSupport_of_empty (M := EnvironmentEval.annSemantics codeSystemS E H)
    (familyS.ok_code (c := falseCode) falseCode_kinded (ValueEq.refl _)) falseCode_empty S

end Rcic.Declarative.Ann.LR3.EqTracer
