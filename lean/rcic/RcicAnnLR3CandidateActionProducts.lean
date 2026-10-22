import rcic.RcicAnnLR3CandidateActionSource
import rcic.RcicAnnLR3EnvironmentPi
import rcic.RcicAnnLR3NativeMemberValues

/-!
# Product constructors using retained semantic actions

Proof-valued products are actual stage-zero codes whose fibres are the
retained outputs of their body. Their neutral reflection, element laws,
application and paired code transport are supplied. The source product
forall P : Prop, P has a complete instance, quantifying over every
original candidate through the relation-preserving code completion.

Universe-valued endomorphisms have an actual PointedPER on the explicit
action carrier, with source identity and neutral constant actions as
members. That carrier is not the old Value + CodeData k carrier. Embedding
all such function carriers coherently in one source code hierarchy is
still open; neither full Ty_pi nor Conv_pi is claimed here.
closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.CandidateActionProducts

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateAction

universe u

/-- The body IH for this constructor retains its output code as data.
This interface alone is not asserted as a source producer. -/
structure Body (α : Type u) (erase : α → Value) (D : α → α → Prop)
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (B : ExprA) (k : Nat) where
  run : α → ClosedCode k
  image : ∀ x, ValueEq (EnvironmentEval.denote E F ν (EnvI.cons (erase x) ρ) B)
    (eraseCode (run x))
  respect : ∀ x y, D x y → CodeRel (run x) (run y)

/-- A retained body gives an actual source lambda action using the
already proved unrestricted lambda application equation. -/
def bodyAction {α : Type u} {erase : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k : Nat} (A : ExprA) (v : Level)
    (b : Body α erase D E F ν ρ B k) : Action α erase D k where
  value := EnvironmentEval.denote E F ν ρ (.lam A v B)
  run := b.run
  erased := fun x => (EnvironmentEval.denote_lambda_application E F ν ρ A B v
    (erase x)).trans (b.image x)
  respect := b.respect

def proofCandidate {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (b : Body α erase D E F ν ρ B 0) :
    CandidatePi.ClosedCandidate :=
  CandidatePi.functionCandidate erase D hD
    (fun x => CandidatePi.complete (b.run x).code.candidate)
    (fun x y h => (b.respect x y h).transport) hne

theorem source_pi_level (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A B : ExprA) (v w : Level) :
    SortMember (eval ν (.imax v w)) (EnvironmentEval.denote E F ν ρ (.pi A v B w)) := by
  have h := EnvironmentEval.denote_pi_value E F ν ρ A B v w
  have hl := InductiveCodes.piValue_level
    (InductiveCodes.imaxLevel (eval ν v) (eval ν w))
    (EnvironmentEval.denote E F ν ρ A) (EnvironmentEval.denote E F ν ρ (.lam A v B))
  rw [InductiveCodes.imaxLevel_eval] at hl
  exact sortMember_congr h.symm hl

theorem source_pi_defined (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A B : ExprA) (v w : Level) :
    TypeDefined (EnvironmentEval.denote E F ν ρ (.pi A v B w)) :=
  typeDefined_congr (EnvironmentEval.denote_pi_value E F ν ρ A B v w).symm
    (InductiveCodes.piValue_defined _ _ _)

/-- Actual stage-zero product construction from the retained body IH.
The element PER is constructed, rather than required as a premise. -/
def propositionPi {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0) : ClosedCode 0 where
  code :=
    { value := EnvironmentEval.denote E F ν ρ (.pi A v B w)
      candidate := (proofCandidate hD hne b).toCandidate
      level := by
        have himax : eval ν (.imax v w) = some 0 := by
          change (eval ν w).bind (fun y => if y = 0 then some 0
            else (eval ν v).map (fun x => max x y)) = some 0
          rw [hw]
          rfl
        exact himax ▸ source_pi_level E F ν ρ A B v w
      defined := source_pi_defined E F ν ρ A B v w }
  bot := EnvironmentEval.denote_bot E F ν ρ _

theorem propositionPi_el {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0) :
    Same (view 0 (propositionPi hD hne A v w hw b).code).relation
      (proofCandidate hD hne b).relation :=
  CandidatePi.complete_fixed (proofCandidate hD hne b)

theorem propositionPi_reflect {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0)
    {f : Value} (hf : CandidatePi.Neutral f) :
    Member (view 0 (propositionPi hD hne A v w hw b).code).relation f :=
  (propositionPi_el hD hne A v w hw b f f).mpr ((proofCandidate hD hne b).reflect hf)

theorem propositionPi_apply {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0)
    {f g : Value} {x y : α}
    (hfg : (view 0 (propositionPi hD hne A v w hw b).code).relation f g)
    (hxy : D x y) :
    (view 0 (b.run x).code).relation (NeutralPi.applyValue f (erase x))
      (NeutralPi.applyValue g (erase y)) :=
  ((propositionPi_el hD hne A v w hw b f g).mp hfg) x y hxy

/-- Paired product transport uses only forward body-code transport.
There is no converse from completed element relations to source guards. -/
theorem propositionPi_transport {α : Type u} {erase : α → Value}
    {D : α → α → Prop} (hD : RelLaws D)
    (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F G : EnvironmentEval.FamilySyntax} {ν μ : Valuation}
    {ρ σ : EnvI} {B B' : ExprA} (A A' : ExprA) (v w v' w' : Level)
    (hw : eval ν w = some 0) (hw' : eval μ w' = some 0)
    (b : Body α erase D E F ν ρ B 0) (c : Body α erase D E G μ σ B' 0)
    (hbc : ∀ x, D x x → CodeRel (b.run x) (c.run x)) :
    CodeRel (propositionPi hD hne A v w hw b) (propositionPi hD hne A' v' w' hw' c) := by
  apply (zero_related_iff _ _).mpr
  have hfun := CandidatePi.functionPER_same erase hD (fun _ _ => Iff.rfl)
    (fun x hx => (hbc x hx).transport)
  intro f g
  exact (propositionPi_el hD hne A v w hw b f g).trans
    ((hfun f g).trans (propositionPi_el hD hne A' v' w' hw' c f g).symm)

/-- Here the body producer itself is supplied for every retained code. -/
def forallBody (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    Body (ClosedCode 0) eraseCode CodeRel E F ν ρ (.bvar 0) 0 where
  run := id
  image := fun C => bound_image E F ν (EnvI.cons (eraseCode C) ρ) 0 (eraseCode C) rfl C.bot
  respect := fun _ _ h => h

def forallCode (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : ClosedCode 0 :=
  propositionPi (codeRel_laws 0) (fun C _ => CandidatePi.nonempty_of_bot C.bot)
    (.sort .zero) (.succ .zero) .zero rfl (forallBody E F ν ρ)

theorem forall_source_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] EqLargeFixture.parameter (.sort .zero)) ∧
    ValueEq (EnvironmentEval.denote emptyEnvA F ν EnvI.bot EqLargeFixture.parameter)
      (eraseCode (forallCode emptyEnvA F ν EnvI.bot)) ∧
    (universeCode 0).relation (encode 0 (forallCode emptyEnvA F ν EnvI.bot).code)
      (encode 0 (forallCode emptyEnvA F ν EnvI.bot).code) ∧
    Member (view 0 (forallCode emptyEnvA F ν EnvI.bot).code).relation
      (NeutralPER.neutralAtom name) ∧
    (∀ C : Code 0, Member (view 0 (close 0 C).code).relation
      (NeutralPi.applyValue (NeutralPER.neutralAtom name) (eraseCode (close 0 C)))) := by
  have hn := propositionPi_reflect (codeRel_laws 0)
    (fun C _ => CandidatePi.nonempty_of_bot C.bot)
    (.sort .zero) (.succ .zero) .zero rfl (forallBody emptyEnvA F ν EnvI.bot)
    (CandidatePi.Neutral.atom name)
  refine ⟨⟨.empty⟩, ⟨.nil⟩, ⟨EqLargeFixture.parameterTyped⟩, ValueEq.refl _,
    universe_member 0 _, hn, ?_⟩
  intro C
  exact propositionPi_apply (codeRel_laws 0) (fun C _ => CandidatePi.nonempty_of_bot C.bot)
    (.sort .zero) (.succ .zero) .zero rfl (forallBody emptyEnvA F ν EnvI.bot)
    hn (codeRel_refl (close 0 C))

abbrev UniverseFunction (k : Nat) := Action (ClosedCode k) eraseCode CodeRel k

def neutralResult (k name : Nat) : ClosedCode k :=
  ⟨NativeMemberValues.neutralCode k name, NativeMemberValues.neutralCode_bot k name⟩

/-- A genuine product PER on its explicit retained-action carrier.
It is deliberately not coerced into the old fixed raw/sum carrier. -/
def universeFunctionPER (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (k : Nat) : PointedPER (k + 1) (UniverseFunction k) where
  value := EnvironmentEval.denote E F ν ρ (CandidateActionSource.identityType k)
  level := by
    have hl := source_pi_level E F ν ρ (.sort (CandidateActionSource.level k))
      (.sort (CandidateActionSource.level k)) (.succ (CandidateActionSource.level k))
      (.succ (CandidateActionSource.level k))
    have he : eval ν (.imax (.succ (CandidateActionSource.level k))
        (.succ (CandidateActionSource.level k))) = some (k + 1) := by
      simp [eval, CandidateActionSource.level_eval]
    exact he ▸ hl
  defined := source_pi_defined E F ν ρ _ _ _ _
  relation := ActionRel
  lawful := actionRel_laws (codeRel_laws k) k
  point := fun name => constant eraseCode CodeRel E F ν ρ
    (.sort (CandidateActionSource.level k)) (.succ (CandidateActionSource.level k))
    (neutralResult k name)
  point_member := fun _ => actionRel_refl _
  irrelevant := fun h => False.elim (Nat.noConfusion h)

theorem universeFunction_identity (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (k : Nat) :
    (universeFunctionPER E F ν ρ k).relation
      (identity E F ν ρ (.sort (CandidateActionSource.level k)) (.succ (CandidateActionSource.level k)) k)
      (identity E F ν ρ (.sort (CandidateActionSource.level k)) (.succ (CandidateActionSource.level k)) k) :=
  actionRel_refl _

theorem universeFunction_transport (E : ResolvedEnvA) (F G : EnvironmentEval.FamilySyntax)
    (ν μ : Valuation) (ρ σ : EnvI) (k : Nat) :
    Related (universeFunctionPER E F ν ρ k) (universeFunctionPER E G μ σ k) :=
  ⟨fun _ _ => Iff.rfl, fun name _ _ _ => codeRel_refl (neutralResult k name)⟩

end Rcic.Declarative.Ann.LR3.CandidateActionProducts
