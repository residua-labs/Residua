import rcic.RcicAnnLR3StratifiedCandidates
import rcic.RcicAnnLR3EnvironmentEvalComposition

/-!
# Retained universe-valued semantic actions

An action carries its code-valued application as data. Erasing that data
commutes with actual native application; application never asks a raw
value to select a candidate. The constructors below supply identity at
every finite universe stage, arbitrary retained constants and composition.
The raw functions are actual EnvironmentEval images, including composition.

Adding the evaluator's bottom observation to a code value changes no
element relation, designated member or candidate. Every existing code has
such a completion. This is not a restriction to originally inhabited
propositions and does not put bottom in their element PERs.

The action carrier is explicit and differs from the old raw function
carrier. These constructions are not a complete source interpretation of
all function types or a Fundamental theorem. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateAction

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates

universe u

def addBottom (V : Value) : Value := fun c => c = .bot ∨ V c

theorem addBottom_bot (V : Value) : addBottom V .bot := Or.inl rfl

theorem addBottom_level {V : Value} {k : Option Nat}
    (h : SortMember k V) : SortMember k (addBottom V) := by
  intro c hc
  rcases hc with rfl | hc
  · exact .bot
  · exact h c hc

theorem addBottom_defined {V : Value} (h : TypeDefined V) :
    TypeDefined (addBottom V) := by
  obtain ⟨k, p, h⟩ := h
  exact ⟨k, p, Or.inr h⟩

theorem addBottom_fixed {V : Value} (h : V .bot) : ValueEq (addBottom V) V := by
  intro c
  constructor
  · rintro (rfl | hc)
    · exact h
    · exact hc
  · exact Or.inr

/-- Only the erased type value is completed. The retained element PER
and its actual reflection data are unchanged. -/
def completeCode : (k : Nat) → Code k → Code k
  | 0, C =>
      { C with
        value := addBottom C.value
        level := addBottom_level C.level
        defined := addBottom_defined C.defined }
  | _ + 1, C =>
      { C with
        value := addBottom C.value
        level := addBottom_level C.level
        defined := addBottom_defined C.defined }

theorem completeCode_value (k : Nat) (C : Code k) :
    (view k (completeCode k C)).value = addBottom (view k C).value := by
  cases k <;> rfl

theorem completeCode_relation (k : Nat) (C : Code k) :
    (view k (completeCode k C)).relation = (view k C).relation := by
  cases k <;> rfl

theorem completeCode_related (k : Nat) (C : Code k) :
    CodeRelated k C (completeCode k C) := by
  cases k with
  | zero => exact ⟨fun _ _ => Iff.rfl, (candidateView C).point_member⟩
  | succ k => exact ⟨fun _ _ => Iff.rfl, C.point_member⟩

structure ClosedCode (k : Nat) where
  code : Code k
  bot : (view k code).value .bot

def close (k : Nat) (C : Code k) : ClosedCode k :=
  ⟨completeCode k C, by rw [completeCode_value]; exact addBottom_bot _⟩

def eraseCode {k : Nat} (C : ClosedCode k) : Value := (view k C.code).value

def CodeRel {k : Nat} (C D : ClosedCode k) : Prop := CodeRelated k C.code D.code

theorem codeRel_refl {k : Nat} (C : ClosedCode k) : CodeRel C C :=
  related_refl (view k C.code)

theorem codeRel_symm {k : Nat} {C D : ClosedCode k} (h : CodeRel C D) :
    CodeRel D C := related_symm h

theorem codeRel_trans {k : Nat} {C D E : ClosedCode k}
    (h : CodeRel C D) (g : CodeRel D E) : CodeRel C E := related_trans h g

theorem codeRel_laws (k : Nat) : RelLaws (@CodeRel k) :=
  ⟨codeRel_symm, codeRel_trans⟩

theorem close_transport {k : Nat} {C D : Code k} (h : CodeRelated k C D) :
    CodeRel (close k C) (close k D) :=
  related_trans (related_symm (completeCode_related k C))
    (related_trans h (completeCode_related k D))

theorem close_preserves_fibre (k : Nat) (C : Code k) :
    (view k (close k C).code).relation = (view k C).relation :=
  completeCode_relation k C

theorem close_value_fixed {k : Nat} (C : Code k) (h : (view k C).value .bot) :
    ValueEq (eraseCode (close k C)) (view k C).value := by
  change ValueEq (view k (completeCode k C)).value _
  rw [completeCode_value]
  exact addBottom_fixed h

/-- Both the output code and its raw application equation are retained.
The equation is an interface obligation; the constructors below supply
it for actual native identity, constant and composition functions. -/
structure Action (α : Type u) (erase : α → Value) (D : α → α → Prop) (k : Nat) where
  value : Value
  run : α → ClosedCode k
  erased : ∀ x, ValueEq (NeutralPi.applyValue value (erase x)) (eraseCode (run x))
  respect : ∀ x y, D x y → CodeRel (run x) (run y)

def ActionRel {α : Type u} {erase : α → Value} {D : α → α → Prop} {k : Nat}
    (f g : Action α erase D k) : Prop :=
  ∀ x y, D x y → CodeRel (f.run x) (g.run y)

theorem actionRel_refl {α : Type u} {erase : α → Value}
    {D : α → α → Prop} {k : Nat} (f : Action α erase D k) : ActionRel f f := f.respect

theorem actionRel_symm {α : Type u} {erase : α → Value}
    {D : α → α → Prop} {k : Nat} (hD : RelLaws D)
    {f g : Action α erase D k} (h : ActionRel f g) : ActionRel g f :=
  fun x y hxy => codeRel_symm (h y x (hD.symm hxy))

theorem actionRel_trans {α : Type u} {erase : α → Value}
    {D : α → α → Prop} {k : Nat} (hD : RelLaws D)
    {f g h : Action α erase D k} (hfg : ActionRel f g) (hgh : ActionRel g h) :
    ActionRel f h := fun x y hxy =>
  codeRel_trans (hfg x y hxy) (hgh y y (hD.trans (hD.symm hxy) hxy))

theorem actionRel_laws {α : Type u} {erase : α → Value}
    {D : α → α → Prop} (hD : RelLaws D) (k : Nat) :
    RelLaws (@ActionRel α erase D k) :=
  ⟨actionRel_symm hD, actionRel_trans hD⟩

/-- Erasure does not participate in selecting either result code. -/
theorem apply_related {α : Type u} {erase : α → Value}
    {D : α → α → Prop} {k : Nat} {f g : Action α erase D k}
    (hfg : ActionRel f g) {x y : α} (hxy : D x y) :
    CodeRel (f.run x) (g.run y) := hfg x y hxy

theorem apply_transport {α : Type u} {erase : α → Value}
    {D : α → α → Prop} {k : Nat} {f g : Action α erase D k}
    (hfg : ActionRel f g) {x y : α} (hxy : D x y)
    (a b : Carrier k) :
    (view k (f.run x).code).relation a b ↔ (view k (g.run y).code).relation a b :=
  (apply_related hfg hxy).transport a b

/-- A local native variable calculation used only by the actual action
constructors. This does not implement the external source variable arm. -/
theorem bound_image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (i : Nat) (V : Value)
    (h : ρ i = V) (hb : V .bot) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.bvar i)) V := by
  apply (EnvironmentEval.denote_core E F ν ρ (e := .bvar i) True.intro).trans
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with rfl | hc
    · exact hb
    · rw [h] at hc
      exact hc
  · intro hc
    apply ApproxI.bvar
    rw [h]
    exact hc

def identityTerm (A : ExprA) (u : Level) : ExprA := .lam A u (.bvar 0)

def identity (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A : ExprA) (u : Level) (k : Nat) :
    Action (ClosedCode k) eraseCode CodeRel k where
  value := EnvironmentEval.denote E F ν ρ (identityTerm A u)
  run := id
  erased := fun C =>
    (EnvironmentEval.denote_lambda_application E F ν ρ A (.bvar 0) u (eraseCode C)).trans
      (bound_image E F ν (EnvI.cons (eraseCode C) ρ) 0 (eraseCode C) rfl C.bot)
  respect := fun _ _ h => h

theorem identity_apply (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A : ExprA) (u : Level) (k : Nat) (C : ClosedCode k) :
    (identity E F ν ρ A u k).run C = C := rfl

/-- A captured retained constant has an actual native constant function;
it need not have a closed source expression representing its candidate. -/
def constant {α : Type u} (erase : α → Value) (D : α → α → Prop)
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A : ExprA) (u : Level) {k : Nat} (C : ClosedCode k) :
    Action α erase D k where
  value := EnvironmentEval.denote E F ν (EnvI.cons (eraseCode C) ρ) (.lam A u (.bvar 1))
  run := fun _ => C
  erased := fun x =>
    (EnvironmentEval.denote_lambda_application E F ν (EnvI.cons (eraseCode C) ρ)
      A (.bvar 1) u (erase x)).trans
      (bound_image E F ν (EnvI.cons (erase x) (EnvI.cons (eraseCode C) ρ))
        1 (eraseCode C) rfl C.bot)
  respect := fun _ _ _ => codeRel_refl C

def composeTerm (A : ExprA) (u : Level) : ExprA :=
  .lam A u (.app (.bvar 2) (.app (.bvar 1) (.bvar 0)))

/-- Composition is supplied by a native lambda whose two captured
functions are the raw actions, with code composition retained separately. -/
def compose {α : Type u} {erase : α → Value} {D : α → α → Prop}
    {j k : Nat} (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A : ExprA) (u : Level)
    (g : Action (ClosedCode j) eraseCode CodeRel k) (f : Action α erase D j)
    (hf : f.value .bot) (hg : g.value .bot) (hx : ∀ x, (erase x) .bot) :
    Action α erase D k where
  value := EnvironmentEval.denote E F ν (EnvI.cons f.value (EnvI.cons g.value ρ))
    (composeTerm A u)
  run := fun x => g.run (f.run x)
  erased := by
    intro x
    let σ := EnvI.cons (erase x) (EnvI.cons f.value (EnvI.cons g.value ρ))
    apply (EnvironmentEval.denote_lambda_application E F ν
      (EnvI.cons f.value (EnvI.cons g.value ρ)) A
        (.app (.bvar 2) (.app (.bvar 1) (.bvar 0))) u (erase x)).trans
    apply (EnvironmentEval.denote_application E F ν σ
      (.bvar 2) (.app (.bvar 1) (.bvar 0))).trans
    have hinner : ValueEq (EnvironmentEval.denote E F ν σ (.app (.bvar 1) (.bvar 0)))
        (eraseCode (f.run x)) :=
      (EnvironmentEval.denote_application E F ν σ (.bvar 1) (.bvar 0)).trans
        ((NeutralPi.applyValue_congr (bound_image E F ν σ 1 f.value rfl hf)
          (bound_image E F ν σ 0 (erase x) rfl (hx x))).trans (f.erased x))
    exact (NeutralPi.applyValue_congr (bound_image E F ν σ 2 g.value rfl hg)
      hinner).trans (g.erased (f.run x))
  respect := fun x y hxy => g.respect _ _ (f.respect x y hxy)

theorem compose_apply {α : Type u} {erase : α → Value} {D : α → α → Prop}
    {j k : Nat} (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A : ExprA) (u : Level)
    (g : Action (ClosedCode j) eraseCode CodeRel k) (f : Action α erase D j)
    (hf : f.value .bot) (hg : g.value .bot) (hx : ∀ x, (erase x) .bot) (x : α) :
    (compose E F ν ρ A u g f hf hg hx).run x = g.run (f.run x) := rfl

end Rcic.Declarative.Ann.LR3.CandidateAction
