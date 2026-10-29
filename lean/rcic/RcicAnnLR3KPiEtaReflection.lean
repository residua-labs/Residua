import rcic.RcicAnnLR3GuardedEtaGluing
import rcic.RcicAnnLR3GuardedTypeImage
import rcic.RcicAnnLR3FunctionEval

/-!
# Type-directed semantic eta reflection for the actual large-K minor

The actual minor has type `Pi P : Prop, Prop`. Its reflected action returns
a retained proposition code whose native tagged payload is the neutral
application, rather than a fixed designated point. Its value is the actual
native lambda `lambda a. tag_0 (n a)`. All carrier, application, respect and
membership fields are constructed below.

Reification here targets the existing semantic `Value` language. The laws
are exact native application, preservation of the tagged neutral payload,
and eta roundtrip in the action PER. This does not assert syntactic normal
forms or a quotient readback of every certified code's PER.

The guarded instance uses the existing conditional type image and glues the
Pi eta action with native-neutral fallback, retaining both branch reification
equations and the conjunctive PER without deciding the guard.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.KPiEtaReflection

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily StratifiedCandidates
open CandidateActionProducts TaggedSaturatedTower

universe u v

theorem neutral_bot {n : Value} (hn : CandidatePi.Neutral n) : n .bot := by
  cases hn with
  | atom name => exact ApproxI.bot _ _
  | app hf a ha => exact Or.inl rfl

theorem tagged_level (k : Option Nat) (n : Value) :
    SortMember k (InductiveCodes.taggedValue k n) := by
  rintro c (rfl | ⟨a, p, rfl, ha, _⟩)
  · exact .bot
  · exact .tagged a p ha

theorem tagged_defined (k : Option Nat) {n : Value} (hn : n .bot) :
    TypeDefined (InductiveCodes.taggedValue k n) :=
  ⟨k, .bot, (InductiveCodes.taggedValue_full k n .bot).mpr hn⟩

theorem tagged_congr (k : Option Nat) {n m : Value} (h : ValueEq n m) :
    ValueEq (InductiveCodes.taggedValue k n) (InductiveCodes.taggedValue k m) := by
  rw [NeutralCodes.valueEq_eq h]
  exact ValueEq.refl _

/-- The universe representation retains the entire neutral payload. -/
theorem tagged_injective (k : Option Nat) {n m : Value}
    (h : ValueEq (InductiveCodes.taggedValue k n) (InductiveCodes.taggedValue k m)) :
    ValueEq n m := by
  intro c
  exact (InductiveCodes.taggedValue_full k n c).symm.trans
    ((h (NeutralCodes.fullTag k c)).trans (InductiveCodes.taggedValue_full k m c))

/-- A genuine retained proposition code for any application-closed neutral. -/
def propReflect (n : Value) (hn : CandidatePi.Neutral n) : CandidateAction.ClosedCode 0 where
  code := {
    value := InductiveCodes.taggedValue (some 0) n
    candidate := CandidateUniverse.predicateCandidate (fun _ => False)
    level := tagged_level (some 0) n
    defined := tagged_defined (some 0) (neutral_bot hn) }
  bot := Or.inl rfl

def universeReflect (n : Value) (hn : CandidatePi.Neutral n) :
    StratifiedCandidates.Carrier 1 :=
  StratifiedCandidates.encode 0 (propReflect n hn).code

theorem prop_reify_reflect (n : Value) (hn : CandidatePi.Neutral n) :
    CandidateAction.eraseCode (propReflect n hn) = InductiveCodes.taggedValue (some 0) n := rfl

theorem universe_reify_reflect (n : Value) (hn : CandidatePi.Neutral n) :
    StratifiedCandidates.erase 1 (universeReflect n hn) =
      InductiveCodes.taggedValue (some 0) n := rfl

theorem universe_reflect_related (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) :
    SaturatedTower.UniverseRel 0 (universeReflect n hn) (universeReflect m hm) := by
  refine ⟨?_, SaturatedTower.zero_closed _, SaturatedTower.zero_closed _⟩
  exact ⟨fun _ _ => Iff.rfl, fun name => CandidatePi.decode_reflection _ (.atom name)⟩

theorem universe_reflect_member (n : Value) (hn : CandidatePi.Neutral n) :
    SaturatedTower.UniverseRel 0 (universeReflect n hn) (universeReflect n hn) :=
  universe_reflect_related n n hn hn

theorem universe_reification_injective (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m)
    (h : ValueEq (StratifiedCandidates.erase 1 (universeReflect n hn))
      (StratifiedCandidates.erase 1 (universeReflect m hm))) : ValueEq n m :=
  tagged_injective (some 0) h

private theorem native_bound_image (ρ : EnvI) (i : Nat) (n : Value)
    (he : ρ i = n) (hb : n .bot) : ValueEq (denI ρ (.bvar i)) n := by
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with rfl | hc
    · exact hb
    · rw [he] at hc
      exact hc
  · intro hc
    apply ApproxI.bvar
    rw [he]
    exact hc

def etaBody : Expr Nat := taggedTerm (some 0) (.app (.bvar 1) (.bvar 0))

/-- This is a native lambda with the incoming neutral captured in its environment. -/
def etaValue (n : Value) : Value :=
  denI (EnvI.cons n EnvI.bot) (.lam (sortTerm (some 0)) etaBody)

theorem etaValue_application (n a : Value) (hn : n .bot) (ha : a .bot) :
    ValueEq (NeutralPi.applyValue (etaValue n) a)
      (InductiveCodes.taggedValue (some 0) (NeutralPi.applyValue n a)) := by
  let σ := EnvI.cons a (EnvI.cons n EnvI.bot)
  apply (FunctionEval.native_lambda_application (EnvI.cons n EnvI.bot)
    (sortTerm (some 0)) etaBody a).trans
  apply (InductiveCodes.taggedValue_denI σ (some 0) (.app (.bvar 1) (.bvar 0))).symm.trans
  apply tagged_congr
  exact (NeutralPi.applyValue_denI σ (.bvar 1) (.bvar 0)).symm.trans
    (NeutralPi.applyValue_congr (native_bound_image σ 1 n rfl hn)
      (native_bound_image σ 0 a rfl ha))

/-- Standard type-directed reflection on the actual retained Pi carrier:
the semantic run reflects `n (reify a)` at its Prop-universe codomain. -/
def reflectPi (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n) :
    (TaggedKPiFixture.code E F ν ρ).Element where
  value := etaValue n
  run := fun a => universeReflect (NeutralPi.applyValue n (CandidateAction.eraseCode a))
    (.app hn _ (CandidatePi.nonempty_of_bot a.bot))
  erased := fun a => etaValue_application n (CandidateAction.eraseCode a) (neutral_bot hn) a.bot
  respect := fun a b _ => universe_reflect_related _ _
    (.app hn _ (CandidatePi.nonempty_of_bot a.bot))
    (.app hn _ (CandidatePi.nonempty_of_bot b.bot))

theorem reflectPi_run (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n)
    (a : CandidateAction.ClosedCode 0) :
    (reflectPi E F ν ρ n hn).run a =
      universeReflect (NeutralPi.applyValue n (CandidateAction.eraseCode a))
        (.app hn _ (CandidatePi.nonempty_of_bot a.bot)) := rfl

theorem reflectPi_member (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n) :
    (TaggedKPiFixture.code E F ν ρ).view.relation
      (reflectPi E F ν ρ n hn) (reflectPi E F ν ρ n hn) :=
  SaturatedPiElements.elementRel_refl _

/-- The inherited universe relation compares decoded candidate PERs. These
neutral-only result candidates therefore inhabit the same semantic class. -/
theorem reflectPi_related (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) :
    (TaggedKPiFixture.code E F ν ρ).view.relation
      (reflectPi E F ν ρ n hn) (reflectPi E F ν ρ m hm) := by
  intro a _
  exact universe_reflect_related _ _
    (.app hn _ (CandidatePi.nonempty_of_bot a.bot))
    (.app hm _ (CandidatePi.nonempty_of_bot a.bot))

theorem reflectPi_reify (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n) :
    (TaggedKPiFixture.code E F ν ρ).erase (reflectPi E F ν ρ n hn) = etaValue n := rfl

theorem reflectPi_application (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Value) (hn : CandidatePi.Neutral n)
    (a : CandidateAction.ClosedCode 0) :
    ValueEq (NeutralPi.applyValue
      ((TaggedKPiFixture.code E F ν ρ).erase (reflectPi E F ν ρ n hn))
      (CandidateAction.eraseCode a))
      (StratifiedCandidates.erase 1
        (universeReflect (NeutralPi.applyValue n (CandidateAction.eraseCode a))
          (.app hn _ (CandidatePi.nonempty_of_bot a.bot)))) :=
  (reflectPi E F ν ρ n hn).erased a

/-- A probe recovers the input neutral head after applying the reflected Pi. -/
theorem etaValue_atom_name_injective (r s : Nat)
    (h : ValueEq (etaValue (NeutralPER.neutralAtom r))
      (etaValue (NeutralPER.neutralAtom s))) : r = s := by
  let a := CandidateAction.eraseCode TaggedKPiFixture.argument
  have ha : a .bot := TaggedKPiFixture.argument_bot
  have htag := (etaValue_application (NeutralPER.neutralAtom r) a (neutral_bot (.atom r)) ha).symm.trans
    ((NeutralPi.applyValue_congr h (ValueEq.refl a)).trans
      (etaValue_application (NeutralPER.neutralAtom s) a (neutral_bot (.atom s)) ha))
  have happ := tagged_injective (some 0) htag
  have hr : NeutralPi.applyValue (NeutralPER.neutralAtom r) a (.spine r [.bot]) :=
    Or.inr (Or.inr ⟨r, [], .bot, rfl, NeutralPER.neutralAtom_observed r, ha⟩)
  have hs := (NeutralPi.applyValue_atom s a (.spine r [.bot])).mp ((happ _).mp hr)
  rcases hs with hbot | ⟨z, hz, he⟩
  · cases hbot
  · exact (CptI.spine.inj he).1

/-- Raw reification retains more information than the inherited action PER.
Consequently these semantic eta laws are not a PER-quotient normal-form
readback theorem. Both elements here are constructed above. -/
theorem related_reflections_distinct_reification
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (r s : Nat) (hrs : r ≠ s) :
    (TaggedKPiFixture.code E F ν ρ).view.relation
      (reflectPi E F ν ρ (NeutralPER.neutralAtom r) (.atom r))
      (reflectPi E F ν ρ (NeutralPER.neutralAtom s) (.atom s)) ∧
    ¬ ValueEq
      ((TaggedKPiFixture.code E F ν ρ).erase
        (reflectPi E F ν ρ (NeutralPER.neutralAtom r) (.atom r)))
      ((TaggedKPiFixture.code E F ν ρ).erase
        (reflectPi E F ν ρ (NeutralPER.neutralAtom s) (.atom s))) :=
  ⟨reflectPi_related E F ν ρ _ _ (.atom r) (.atom s),
    fun h => hrs (etaValue_atom_name_injective r s h)⟩

/-- Eta expansion works for every existing action without a new result-fibre
membership assumption; it keeps the already represented run exactly. -/
def etaAction {α : Type u} {β : Type v} {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {R : α → β → β → Prop}
    (f : SaturatedPiElements.ElementAction eraseA eraseB D R) :
    SaturatedPiElements.ElementAction eraseA eraseB D R where
  value := UnifiedPi.etaGraph (fun _ _ => True) f.value
  run := f.run
  erased := fun a => (UnifiedPi.etaGraph_application (fun _ _ => True) f.value
    (x := eraseA a) True.intro).trans (f.erased a)
  respect := f.respect

theorem etaAction_run {α : Type u} {β : Type v} {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {R : α → β → β → Prop}
    (f : SaturatedPiElements.ElementAction eraseA eraseB D R) (a : α) :
    (etaAction f).run a = f.run a := rfl

theorem etaAction_related {α : Type u} {β : Type v}
    {eraseA : α → Value} {eraseB : β → Value} {D : α → α → Prop}
    {R : α → β → β → Prop}
    (f : SaturatedPiElements.ElementAction eraseA eraseB D R) :
    SaturatedPiElements.ElementRel (etaAction f) f :=
  SaturatedPiElements.elementRel_refl f

/-- Concrete unconditional guarded reflection: both branch elements are supplied
by definitions above and the existing native-neutral constructor. -/
def guardedReflect (G : Prop) (ν : Valuation) (a : GuardedReaderSource.IndexAssignment)
    (fallbackName : Nat) (n : Value) (hn : CandidatePi.Neutral n) :
    (GuardedKernel.kernel G (GuardedOpenEqCall.minorCode ν a).kernel
      (Code.neutral.{0} 1 fallbackName).kernel
      (GuardedTypeImage.piNeutral G ν a fallbackName)).Element :=
  GuardedEtaGluing.glue G
    (reflectPi EqLargeFixture.env TaggedKEvaluation.eqSyntax ν
      (GuardedReaderSource.rawEnvironment a) n hn)
    (neutralReflect 1 fallbackName n hn)

theorem guardedReflect_member (G : Prop) (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) :
    GuardedKernel.Relation (guardedReflect G ν a fallbackName n hn)
      (guardedReflect G ν a fallbackName n hn) :=
  GuardedEtaGluing.glue_member _ _
    (reflectPi_member EqLargeFixture.env TaggedKEvaluation.eqSyntax ν
      (GuardedReaderSource.rawEnvironment a) n hn)
    (neutral_cr3 1 fallbackName n hn)

theorem guardedReflect_yes {G : Prop} (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) (hG : G) :
    (guardedReflect G ν a fallbackName n hn).yes hG =
      reflectPi EqLargeFixture.env TaggedKEvaluation.eqSyntax ν
        (GuardedReaderSource.rawEnvironment a) n hn := rfl

theorem guardedReflect_no {G : Prop} (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) (hG : ¬ G) :
    (guardedReflect G ν a fallbackName n hn).no hG =
      neutralReflect 1 fallbackName n hn := rfl

theorem guardedReflect_reify (G : Prop) (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) :
    (guardedReflect G ν a fallbackName n hn).value =
      GuardedKernel.conditionalValue G (etaValue n) n := rfl

theorem guardedReflect_reify_true {G : Prop} (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) (hG : G) :
    ValueEq (guardedReflect G ν a fallbackName n hn).value (etaValue n) :=
  GuardedKernel.conditionalValue_true G _ _ hG

theorem guardedReflect_reify_false {G : Prop} (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) (hG : ¬ G) :
    ValueEq (guardedReflect G ν a fallbackName n hn).value n :=
  GuardedKernel.conditionalValue_false G _ _ hG

theorem guardedReflect_application_true {G : Prop} (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (fallbackName : Nat)
    (n : Value) (hn : CandidatePi.Neutral n) (hG : G)
    (x : CandidateAction.ClosedCode 0) :
    ValueEq (NeutralPi.applyValue (guardedReflect G ν a fallbackName n hn).value
      (CandidateAction.eraseCode x))
      (InductiveCodes.taggedValue (some 0)
        (NeutralPi.applyValue n (CandidateAction.eraseCode x))) :=
  (NeutralPi.applyValue_congr
    (guardedReflect_reify_true ν a fallbackName n hn hG)
    (ValueEq.refl (CandidateAction.eraseCode x))).trans
      (etaValue_application n (CandidateAction.eraseCode x) (neutral_bot hn) x.bot)

end Rcic.Declarative.Ann.LR3.KPiEtaReflection
