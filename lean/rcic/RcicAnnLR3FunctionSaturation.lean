import rcic.RcicAnnLR3FunctionEval

/-!
# Bottom saturation of legal function arguments

Adding bottom to a function value does not change native application.
Consequently every native FunctionPER admits that operation at function
positions, including function members whose raw observations omit bottom.
The domain condition used for general native eta is therefore relatedness
of `withBottom x` and `x`, rather than literal bottom containment.

Native eta application is proved exactly at every raw argument: it
applies the original function to `withBottom x`. Domain saturation and
dependent-fibre coherence then supply eta in the original function PER.
The saturation condition is constructed for the current NeutralCodes
PERs and for all native FunctionPERs. No admitted member is removed.

These are semantic function operations and laws. A source eta arm still
needs identification of its selected Pi code with the corresponding
function PER and evaluator. No source-arm supply is claimed here.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.FunctionSaturation

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements

def withBottom (x : Value) : Value := fun c => c = .bot ∨ x c

theorem withBottom_bot (x : Value) : withBottom x .bot := Or.inl rfl

theorem withBottom_eq_of_bot {x : Value} (hx : x .bot) : ValueEq (withBottom x) x := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | hc
    · subst c
      exact hx
    · exact hc
  · exact fun hc => Or.inr hc

/-- Function application observes only lambda graphs and neutral spines
of its function argument; it generates bottom independently of that value. -/
theorem applyValue_withBottom_function (f x : Value) :
    ValueEq (NeutralPi.applyValue (withBottom f) x) (NeutralPi.applyValue f x) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ |
        ⟨head, args, u, hc, hf, ha⟩
    · exact Or.inl hc
    · rcases hf with hf | hf
      · cases hf
      · exact Or.inr (Or.inl ⟨g, s, hc, hf, hs, ha⟩)
    · rcases hf with hf | hf
      · cases hf
      · exact Or.inr (Or.inr ⟨head, args, u, hc, hf, ha⟩)
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ |
        ⟨head, args, u, hc, hf, ha⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl ⟨g, s, hc, Or.inr hf, hs, ha⟩)
    · exact Or.inr (Or.inr ⟨head, args, u, hc, Or.inr hf, ha⟩)

theorem functionPER_withBottom_left (D : Relation) (C : Value → Relation) (f g : Value) :
    FunctionPER NeutralPi.applyValue D C (withBottom f) g ↔
      FunctionPER NeutralPi.applyValue D C f g := by
  constructor
  · intro h x y hxy
    have hr := h x y hxy
    rw [NeutralCodes.valueEq_eq (applyValue_withBottom_function f x)] at hr
    exact hr
  · intro h x y hxy
    rw [NeutralCodes.valueEq_eq (applyValue_withBottom_function f x)]
    exact h x y hxy

theorem functionPER_withBottom_right (D : Relation) (C : Value → Relation) (f g : Value) :
    FunctionPER NeutralPi.applyValue D C f (withBottom g) ↔
      FunctionPER NeutralPi.applyValue D C f g := by
  constructor
  · intro h x y hxy
    have hr := h x y hxy
    rw [NeutralCodes.valueEq_eq (applyValue_withBottom_function g y)] at hr
    exact hr
  · intro h x y hxy
    rw [NeutralCodes.valueEq_eq (applyValue_withBottom_function g y)]
    exact h x y hxy

theorem functionPER_withBottom_both (D : Relation) (C : Value → Relation) (f g : Value) :
    FunctionPER NeutralPi.applyValue D C (withBottom f) (withBottom g) ↔
      FunctionPER NeutralPi.applyValue D C f g :=
  (functionPER_withBottom_left D C f (withBottom g)).trans
    (functionPER_withBottom_right D C f g)

theorem functionPER_withBottom_member (D : Relation) (C : Value → Relation) (f : Value) :
    Member (FunctionPER NeutralPi.applyValue D C) (withBottom f) ↔
      Member (FunctionPER NeutralPi.applyValue D C) f :=
  functionPER_withBottom_both D C f f

/-- The correct legal-domain condition permits raw members without a
bottom observation. It asks only for relatedness after bottom is added. -/
def Saturated (D : Relation) : Prop :=
  ∀ x : Value, Member D x → D (withBottom x) x

theorem saturated_of_same {D E : Relation} (hDE : Same D E) (hD : Saturated D) :
    Saturated E := by
  intro x hx
  exact (hDE _ _).mp (hD x ((hDE x x).mpr hx))

theorem saturated_related {D : Relation} (hD : Laws D) (hs : Saturated D)
    {x y : Value} (hxy : D x y) : D (withBottom x) (withBottom y) :=
  hD.trans (hs x (left_member hD hxy))
    (hD.trans hxy (hD.symm (hs y (right_member hD hxy))))

/-- Saturation is supplied for every presentation in the current code
fragment. Literal bottom containment is used only to prove this instance. -/
theorem code_saturated {k : Option Nat} {V : Value} {D : Relation}
    (hcode : NeutralCodes.Code k V D) : Saturated D := by
  intro x hx
  rw [NeutralCodes.valueEq_eq (withBottom_eq_of_bot (FunctionEval.code_member_bot hcode hx))]
  exact hx

/-- Every native function PER is saturated, without an additional
assumption on its function values, domain, or codomain fibres. -/
theorem functionPER_saturated (D : Relation) (C : Value → Relation) :
    Saturated (FunctionPER NeutralPi.applyValue D C) := by
  intro f hf
  exact (functionPER_withBottom_left D C f f).mpr hf

/-- Exact native eta computation on arbitrary raw arguments. A variable
under the extended environment observes precisely `withBottom x`. -/
theorem native_eta_withBottom_application (ρ : EnvI) (A f : Expr Nat) (x : Value) :
    ValueEq
      (NeutralPi.applyValue (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0)))) x)
      (NeutralPi.applyValue (denI ρ f) (withBottom x)) := by
  apply (FunctionEval.native_lambda_application ρ A
    (.app (lift 0 1 f) (.bvar 0)) x).trans
  apply (NeutralPi.applyValue_denI (EnvI.cons x ρ) (lift 0 1 f) (.bvar 0)).symm.trans
  apply NeutralPi.applyValue_congr
  · exact fun c => approxI_cons_lift0_iff ρ x f c
  · intro c
    constructor
    · exact approxI_bvar_inv
    · intro hc
      rcases hc with hc | hc
      · subst c
        exact ApproxI.bot (EnvI.cons x ρ) (.bvar 0)
      · exact ApproxI.bvar hc

/-- The saturated argument is related to the original one. Coherence
transports the result from its saturated dependent fibre to the original
fibre, so eta retains the original legal-domain function relation. -/
theorem native_eta_related {D : Relation} (hD : Laws D) (hs : Saturated D)
    {C : Value → Relation} (hC : FamilyCoherent D C)
    {ρ σ : EnvI} {A f g : Expr Nat}
    (hfg : FunctionPER NeutralPi.applyValue D C (denI ρ f) (denI σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0)))) (denI σ g) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (native_eta_withBottom_application ρ A f x)]
  have hsx := hs x (left_member hD hxy)
  have hr := hfg (withBottom x) y (hD.trans hsx hxy)
  exact (hC (withBottom x) x hsx _ _).mp hr

theorem native_etas_related {D : Relation} (hD : Laws D) (hs : Saturated D)
    {C : Value → Relation} (hC : FamilyCoherent D C)
    {ρ σ : EnvI} {A A' f g : Expr Nat}
    (hfg : FunctionPER NeutralPi.applyValue D C (denI ρ f) (denI σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0))))
      (denI σ (.lam A' (.app (lift 0 1 g) (.bvar 0)))) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (native_eta_withBottom_application ρ A f x),
    NeutralCodes.valueEq_eq (native_eta_withBottom_application σ A' g y)]
  have hsx := hs x (left_member hD hxy)
  have hr := hfg (withBottom x) (withBottom y) (saturated_related hD hs hxy)
  exact (hC (withBottom x) x hsx _ _).mp hr

theorem native_eta_member {D : Relation} (hD : Laws D) (hs : Saturated D)
    {C : Value → Relation} (hC : FamilyCoherent D C)
    {ρ : EnvI} {A f : Expr Nat}
    (hf : Member (FunctionPER NeutralPi.applyValue D C) (denI ρ f)) :
    Member (FunctionPER NeutralPi.applyValue D C)
      (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0)))) :=
  native_etas_related hD hs hC hf

theorem denote_eta_withBottom_application (ν : Valuation) (ρ : EnvI)
    (A f : ExprA) (u : Level) (x : Value) :
    ValueEq
      (NeutralPi.applyValue
        (UnitModel.denote ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0)))) x)
      (NeutralPi.applyValue (UnitModel.denote ν ρ f) (withBottom x)) := by
  simpa only [UnitModel.denote, translate, translate_lift] using
    native_eta_withBottom_application ρ (translate ν A) (translate ν f) x

theorem denote_eta_related {D : Relation} (hD : Laws D) (hs : Saturated D)
    {C : Value → Relation} (hC : FamilyCoherent D C)
    {ν μ : Valuation} {ρ σ : EnvI} {A f g : ExprA} {u : Level}
    (hfg : FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ f) (UnitModel.denote μ σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0))))
      (UnitModel.denote μ σ g) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (denote_eta_withBottom_application ν ρ A f u x)]
  have hsx := hs x (left_member hD hxy)
  have hr := hfg (withBottom x) y (hD.trans hsx hxy)
  exact (hC (withBottom x) x hsx _ _).mp hr

theorem denote_eta_at_code {k : Option Nat} {V : Value} {D : Relation}
    (hcode : NeutralCodes.Code k V D)
    {C : Value → Relation} (hC : FamilyCoherent D C)
    {ν μ : Valuation} {ρ σ : EnvI} {A f g : ExprA} {u : Level}
    (hfg : FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ f) (UnitModel.denote μ σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0))))
      (UnitModel.denote μ σ g) :=
  denote_eta_related (NeutralCodes.code_lawful hcode) (code_saturated hcode) hC hfg

end Rcic.Declarative.Ann.LR3.FunctionSaturation
