import rcic.RcicAnnLR3RCodeSoundKripke
import rcic.RcicAnnLR3ImpredicativePiProbe

/-!
# Pi closure of the sound interface at a Prop codomain

**Construction.** Take a sound domain `A` at any level, possibly impredicative
over a large carrier, and a contextual family `D` of level-zero sound fibres
with a Kripke uniform index. `piPropSound` is then an actual `RCodeSound`
instance for the source product `Π A B`. The pieces are:
- its code is the impredicative product code of the fibres' memberships,
  evaluated at the actual type image;
- its fragments are the uniform sections, whose sources are their actual
  lambdas, together with the typed neutrals of the product type;
- each section evaluates to the actual evaluation of its lambda. Membership
  of that value comes from `lambda_member`, using the fibres' own fragment
  erasures (a section is the body IH).

Realization needs one section. The generic fibre's realization supplies it
through the Kripke index, with one existential elimination. Coherence and
realization of members are level-zero irrelevance; reflection is exact.

`application_sound` reads applications back into the fibres.
`piPropSound_botClosed` shows that the resulting code lies in the bot-closed
Prop universe of the impredicative probe. The PiControl family inhabits every
premise.

**Scope.** Products at positive codomain levels need a code former for
dependent action carriers. `GuardedTaggedCode.Producer` has no such
constructor; it belongs to the recursive tower and is not claimed here.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeSoundPiProp

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER RCodeSoundInterface RCodeSoundPi RCodeSoundKripke
open ImpredicativePiProbe (ImpMember impCode impCode_member_iff lambda_member BotClosed
  impCode_botClosed)

universe u v w z q

section Construction

variable {W : World} {a : Nat} {A : RCodeSound.{u,v} W a} {B : ExprA} {lB : Level}

/-- Fibre membership of a raw value. -/
def FibreGood (D : Family.{u,v,w,z} A 0 B lB) (x : Member A.code) (val : Value) : Prop :=
  GuardedTaggedCode.Good (D.fibre x).code.kernel val

def PiMember (D : Family.{u,v,w,z} A 0 B lB) : Value → Prop :=
  ImpMember (α := Member A.code) (fun x => A.code.erase x.val) (fun _ => True) (FibreGood D)

theorem piType_level (D : Family.{u,v,w,z} A 0 B lB) :
    eval W.valuation (.imax A.sourceLevel lB) = some 0 := by
  have h0 : eval W.valuation lB = some 0 := by
    have h := (D.fibre (anchor A)).level
    rw [D.source_level] at h
    exact h
  change (eval W.valuation lB).bind (fun y => if y = 0 then some 0
    else (eval W.valuation A.sourceLevel).map (fun x => max x y)) = some 0
  rw [h0]
  rfl

theorem piType_sortMember (D : Family.{u,v,w,z} A 0 B lB) :
    SortMember (some 0) (W.evaluate (.pi A.sourceType A.sourceLevel B lB)) := by
  have h := CandidateActionProducts.source_pi_level W.env W.family W.valuation
    W.rawEnvironment A.sourceType B A.sourceLevel lB
  rw [piType_level D] at h
  exact h

def piCode (D : Family.{u,v,w,z} A 0 B lB) : GuardedTaggedCode.Code.{0} 0 :=
  impCode.{0} (α := Member A.code) (fun x => A.code.erase x.val) (fun _ => True)
    (FibreGood D) (W.evaluate (.pi A.sourceType A.sourceLevel B lB))
    (piType_sortMember D)
    (CandidateActionProducts.source_pi_defined W.env W.family W.valuation
      W.rawEnvironment A.sourceType B A.sourceLevel lB)

/-- A section is the body IH: its lambda's actual evaluation is a member. -/
theorem section_member {D : Family.{u,v,w,z} A 0 B lB} (σ : Section D) :
    PiMember D (W.evaluate (.lam A.sourceType A.sourceLevel σ.body)) :=
  lambda_member W.env W.family W.valuation W.rawEnvironment A.sourceType σ.body
    A.sourceLevel (fun x _ => ⟨((D.fibre x).evalSem (σ.fragment x)).val,
      ((D.fibre x).evalSem (σ.fragment x)).property, by
        have h := (D.fibre x).erasure (σ.fragment x)
        rw [σ.source_eq x] at h
        exact h⟩)

/-- Fragments: uniform sections and typed product neutrals. -/
inductive PiFragment (D : Family.{u,v,w,z} A 0 B lB) : Type (max u v w z)
  | lam (σ : Section D)
  | neutral (n : Neutral W (.pi A.sourceType A.sourceLevel B lB))

def piSource {D : Family.{u,v,w,z} A 0 B lB} :
    PiFragment D → Source W (.pi A.sourceType A.sourceLevel B lB)
  | .lam σ => ⟨_, σ.lambdaTyped⟩
  | .neutral n => n.toSource

def piEval {D : Family.{u,v,w,z} A 0 B lB} :
    PiFragment D → Member (piCode D)
  | .lam σ => ⟨⟨W.evaluate (.lam A.sourceType A.sourceLevel σ.body)⟩,
      (impCode_member_iff _ _ _ _ _ _ _).mpr (section_member σ)⟩
  | .neutral n => ⟨⟨n.value⟩, (impCode_member_iff _ _ _ _ _ _ _).mpr (Or.inr n.neutral)⟩

theorem piEval_erasure {D : Family.{u,v,w,z} A 0 B lB} (s : PiFragment D) :
    ValueEq ((piCode D).erase (piEval s).val) (W.evaluate (piSource s).term) := by
  cases s with
  | lam σ => exact ValueEq.refl _
  | neutral n => exact n.image.symm

/-- The Pi instance at a Prop codomain over any sound domain. -/
def piPropSound (D : Family.{u,v,w,z} A 0 B lB) (K : KripkeFamily.{u,v,w,z,q} D) :
    RCodeSound.{0, max u v w z} W 0 where
  code := piCode D
  sourceType := .pi A.sourceType A.sourceLevel B lB
  sourceLevel := .imax A.sourceLevel lB
  typeTyped := .pi _ _ _ _ _ A.typeTyped D.codomainTyped
  level := piType_level D
  typeImage := ValueEq.refl _
  Fragment := PiFragment D
  source := piSource
  evalSem := piEval
  erasure := piEval_erasure
  source_coherence := fun s t _ => (piCode D).view.irrelevant rfl _ _
    (piEval s).property (piEval t).property
  realization := fun x => by
    obtain ⟨i, _⟩ := K.generic_realization ((D.fibre K.generic).point 0)
    exact ⟨.lam (K.sectionAt i), (piCode D).view.irrelevant rfl _ _ x.property
      (piEval (.lam (K.sectionAt i))).property⟩
  reflect := fun n => piEval (.neutral n)
  reflection_source := fun n => ⟨.neutral n, related_refl _,
    ⟨.refl _ n.term _ n.typed⟩⟩

theorem piPropSound_botClosed (D : Family.{u,v,w,z} A 0 B lB)
    (K : KripkeFamily.{u,v,w,z,q} D) : BotClosed (piPropSound D K).code :=
  impCode_botClosed _ _ _ _ _ _

/-- Every section is read back by its actual lambda. -/
theorem piPropSound_section_readback (D : Family.{u,v,w,z} A 0 B lB)
    (K : KripkeFamily.{u,v,w,z,q} D) (σ : Section D) :
    (piPropSound D K).ReadsBack (.lam σ) (piEval (.lam σ)) ⟨_, σ.lambdaTyped⟩ :=
  (piPropSound D K).readback_total (.lam σ)

/-- Applications of members to realized domain arguments lie in the fibres.
Neutral members need neutral reflection in the fibres and nonempty argument
images. -/
theorem application_sound (D : Family.{u,v,w,z} A 0 B lB) (K : KripkeFamily.{u,v,w,z,q} D)
    (hneu : ∀ x val, CandidatePi.Neutral val → FibreGood D x val)
    (hne : ∀ x : Member A.code, CandidatePi.NonemptyValue (A.code.erase x.val))
    (f : (piPropSound D K).Element) (x : Member A.code) :
    FibreGood D x (NeutralPi.applyValue ((piPropSound D K).erase f) (A.code.erase x.val)) :=
  ImpredicativePiProbe.application_member (fun x _ => hneu x) (fun x _ => hne x)
    ((impCode_member_iff _ _ _ _ _ _ _).mp f.property) True.intro

end Construction

/-! ## The PiControl family supplies every premise -/

section Control

open RCodeSoundPiControl

def controlPi (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    RCodeSound.{0,0} (RCodeSoundZeroInstances.world F ν
      (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name))) 0 :=
  piPropSound (family F ν name) (controlKripke F ν name)

theorem controlPi_packet (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    BotClosed (controlPi F ν name).code ∧
    (controlPi F ν name).sourceType =
      .pi RCodeProofReadback.proofType .zero codomain .zero ∧
    (∀ x : (controlPi F ν name).Element,
      ∃ s, (controlPi F ν name).ReadsBack s x ((controlPi F ν name).source s)) ∧
    (∀ (f : (controlPi F ν name).Element) (x : (domain F ν name).Element),
      FibreGood (family F ν name) x
        (NeutralPi.applyValue ((controlPi F ν name).erase f) ((domain F ν name).code.erase x.val))) :=
  ⟨piPropSound_botClosed _ _, rfl, (controlPi F ν name).member_readback,
    fun f x => application_sound _ _
      (fun _ v hv => ⟨(GuardedKernel.nativeNeutralReflector.{0} 0 name).reflect v hv,
        (GuardedKernel.nativeNeutralReflector.{0} 0 name).member v hv,
        (GuardedKernel.nativeNeutralReflector.{0} 0 name).image v hv⟩)
      (fun (x : (domain F ν name).Element) =>
        CandidatePi.nonempty_of_bot (neutral_bot x.val.down.neutral)) f x⟩

end Control

end Rcic.Declarative.Ann.LR3.RCodeSoundPiProp
