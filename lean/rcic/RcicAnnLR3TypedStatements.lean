import rcic.RcicAnnLR3TypedPER
import rcic.RcicAnnLR3UnitSortExtraction

/-!
# Exact realised-context fundamental statements and guarded extraction

These are statement schemas, not a global typed model. The code relation
is an explicit parameter with its algebraic laws; a concrete non-IR
instance is supplied by the separate empty-family boundary. No source
soundness, complete universe decoder, or all-context realisation is hidden
in this record. Global term/conversion soundness is stated as a Prop.

The extraction theorem names its representative-realisation input. The
truth-valued Eq and Loop counterinstances show why that input must not be
claimed from CtxWfA. Native images are raw-subject images, not selected
annotations. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedStatements
open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

def universeValue (k : Option Nat) : Value := denI EnvI.bot (sortTerm k)

/-- Pure semantic algebra. Existence of such data is not source soundness.
The complete Code/El construction and its source member interpretation
must still be built for any proposed full model. -/
structure CodeSystem where
  Code : Option Nat → Value → Relation → Prop
  universePER : Option Nat → Relation
  lawful : ∀ {k V R}, Code k V R → Laws R
  defined : ∀ {k V R}, Code k V R → TypeDefined V
  level : ∀ {k V R}, Code k V R → SortMember k V
  coherent : ∀ {k l V R S}, Code k V R → Code l V S → Same R S
  universe_code : ∀ k, Code (k.map Nat.succ) (universeValue k) (universePER k)
  universe_member : ∀ k, Member (universePER (k.map Nat.succ)) (universeValue k)
  universe_elim : ∀ {k l R x}, Code l (universeValue k) R →
    Member R x → SortMember k x ∧ TypeDefined x

structure AnnSemantics extends CodeSystem where
  image : Valuation → LCtxA → EnvI → ExprA → Value
  sort_image : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l)

/-- Entries are interpreted in their outer/tail environment. Let-bindings
agree with their stored value in the actual type PER. -/
inductive Realises (M : AnnSemantics) (ν : Valuation) : LCtxA → EnvI → Prop
  | nil (ρ : EnvI) : Realises M ν [] ρ
  | assumption {Γ : LCtxA} {ρ : EnvI} {A : ExprA} {x : Value} {k : Option Nat} {R : Relation}
      (tail : Realises M ν Γ ρ) (code : M.Code k (M.image ν Γ ρ A) R)
      (member : Member R x) : Realises M ν (.assumption A :: Γ) (EnvI.cons x ρ)
  | letBinding {Γ : LCtxA} {ρ : EnvI} {A v : ExprA} {x : Value} {k : Option Nat} {R : Relation}
      (tail : Realises M ν Γ ρ) (code : M.Code k (M.image ν Γ ρ A) R)
      (member : Member R x) (value : R x (M.image ν Γ ρ v)) :
      Realises M ν (.letBinding A v :: Γ) (EnvI.cons x ρ)

def Judgment (M : AnnSemantics) (ν : Valuation) (Γ : LCtxA) (ρ : EnvI)
    (a b A : ExprA) : Prop :=
  ∃ k R, M.Code k (M.image ν Γ ρ A) R ∧ TypeDefined (M.image ν Γ ρ A) ∧
    R (M.image ν Γ ρ a) (M.image ν Γ ρ b)

def TyGoal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (e A : ExprA) : Prop :=
  CtxWfA E I n Γ → ∀ ν ρ, Realises M ν Γ ρ → Judgment M ν Γ ρ e e A

def ConvGoal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (a b A : ExprA) : Prop :=
  CtxWfA E I n Γ → ∀ ν ρ, Realises M ν Γ ρ → Judgment M ν Γ ρ a b A

/-- The requested mutual statement, NOT an asserted theorem. Environment
admission must be supplied by any producer of this statement. -/
def Fundamental (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  (∀ {Γ e A}, HasTyA E I n Γ e A → TyGoal M E I n Γ e A) ∧
  (∀ {Γ a b A}, ConvA E I n Γ a b A → ConvGoal M E I n Γ a b A)

/-- The requested admission-wide supply, stated separately from the
per-environment theorem. The interface is the actual concrete iota of E. -/
def AllAdmittedFundamental (models : ResolvedEnvA → AnnSemantics) : Prop :=
  ∀ E, EnvWfA (iotaIfaceA E) E → ∀ n, Fundamental (models E) E (iotaIfaceA E) n

theorem sort_judgment_membership {M : AnnSemantics} {ν : Valuation} {Γ : LCtxA}
    {ρ : EnvI} {A : ExprA} {u : Level}
    (h : Judgment M ν Γ ρ A A (.sort u)) :
    SortMember (eval ν u) (M.image ν Γ ρ A) ∧ TypeDefined (M.image ν Γ ρ A) := by
  obtain ⟨k, R, hc, _, hm⟩ := h
  rw [M.sort_image] at hc
  exact M.universe_elim hc hm

/-- The sort arm uses only concrete universe algebra, not source rows. -/
theorem sort_goal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA)
    (n : Nat) (Γ : LCtxA) (l : Level) : TyGoal M E I n Γ (.sort l) (.sort (.succ l)) := by
  intro _ ν ρ _
  refine ⟨(eval ν (.succ l)).map Nat.succ, M.universePER (eval ν (.succ l)), ?_, ?_, ?_⟩
  · rw [M.sort_image]; exact M.universe_code _
  · rw [M.sort_image]; exact sort_defined _ _
  · rw [M.sort_image]; exact M.universe_member _

theorem judgment_symm {M : AnnSemantics} {ν : Valuation} {Γ : LCtxA}
    {ρ : EnvI} {a b A : ExprA} (h : Judgment M ν Γ ρ a b A) :
    Judgment M ν Γ ρ b a A := by
  obtain ⟨k, R, hc, hd, hr⟩ := h
  exact ⟨k, R, hc, hd, (M.lawful hc).symm hr⟩

theorem judgment_trans {M : AnnSemantics} {ν : Valuation} {Γ : LCtxA}
    {ρ : EnvI} {a b c A : ExprA} (h : Judgment M ν Γ ρ a b A)
    (g : Judgment M ν Γ ρ b c A) : Judgment M ν Γ ρ a c A := by
  obtain ⟨k, R, hc, hd, hr⟩ := h
  obtain ⟨l, S, hcs, _, hs⟩ := g
  exact ⟨k, R, hc, hd, (M.lawful hc).trans hr ((M.coherent hcs hc _ _).mp hs)⟩

/-- The additional coverage needed to instantiate the unconditional image
port. It is NOT implied by the realised-context fundamental theorem. -/
def Representative (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (choose : Valuation → LCtxA → EnvI) : Prop :=
  ∀ ν Γ, CtxWfA E I n Γ → Realises M ν Γ (choose ν Γ)

theorem ann_membership_of_fundamental {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (hF : Fundamental M E I n)
    (choose : Valuation → LCtxA → EnvI) (hc : Representative M E I n choose) :
    AnnSortMembershipSound E I n (fun ν Γ e => M.image ν Γ (choose ν Γ) e) := by
  intro ν Γ A u hΓ hA
  exact sort_judgment_membership (hF.1 hA hΓ ν (choose ν Γ) (hc ν Γ hΓ))

/-- No choice is required for the weaker pair conclusion: select an
existential realisation only inside the proof of the valuation equality. -/
theorem ann_sortUniq_at_realisable_context {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (hF : Fundamental M E I n) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) (cover : ∀ ν, ∃ ρ, Realises M ν Γ ρ)
    {A : ExprA} {u v : Level} (hu : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ A (.sort v)) : eqN u v := by
  intro ν
  obtain ⟨ρ, hρ⟩ := cover ν
  have su := sort_judgment_membership (hF.1 hu hΓ ν ρ hρ)
  have sv := sort_judgment_membership (hF.1 hv hΓ ν ρ hρ)
  exact sortMember_unique su.1 sv.1 su.2

structure NativeSemantics extends CodeSystem where
  image : Valuation → LCtx → EnvI → Expr Nat → Value
  sort_image : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l)

inductive NativeRealises (M : NativeSemantics) (ν : Valuation) : LCtx → EnvI → Prop
  | nil (ρ : EnvI) : NativeRealises M ν [] ρ
  | assumption {Γ : LCtx} {ρ : EnvI} {A : Expr Nat} {x : Value} {k : Option Nat} {R : Relation}
      (tail : NativeRealises M ν Γ ρ) (code : M.Code k (M.image ν Γ ρ A) R)
      (member : Member R x) : NativeRealises M ν (.assumption A :: Γ) (EnvI.cons x ρ)
  | letBinding {Γ : LCtx} {ρ : EnvI} {A v : Expr Nat} {x : Value} {k : Option Nat} {R : Relation}
      (tail : NativeRealises M ν Γ ρ) (code : M.Code k (M.image ν Γ ρ A) R)
      (member : Member R x) (value : R x (M.image ν Γ ρ v)) :
      NativeRealises M ν (.letBinding A v :: Γ) (EnvI.cons x ρ)

def NativeJudgment (M : NativeSemantics) (ν : Valuation) (Γ : LCtx) (ρ : EnvI)
    (a b A : Expr Nat) : Prop :=
  ∃ k R, M.Code k (M.image ν Γ ρ A) R ∧ TypeDefined (M.image ν Γ ρ A) ∧
    R (M.image ν Γ ρ a) (M.image ν Γ ρ b)

def NativeFundamental (M : NativeSemantics) (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E →
  (∀ {Γ e A}, CtxWfT E n Γ → HasTyT E n Γ e A →
    ∀ ν ρ, NativeRealises M ν Γ ρ → NativeJudgment M ν Γ ρ e e A) ∧
  (∀ {Γ a b A}, CtxWfT E n Γ → ConvT E n Γ a b A →
    ∀ ν ρ, NativeRealises M ν Γ ρ → NativeJudgment M ν Γ ρ a b A)

def NativeRepresentative (M : NativeSemantics) (E : ResolvedEnv) (n : Nat)
    (choose : Valuation → LCtx → EnvI) : Prop :=
  EnvWfT E → ∀ ν Γ, CtxWfT E n Γ → NativeRealises M ν Γ (choose ν Γ)

theorem native_membership_of_fundamental {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (hF : NativeFundamental M E n)
    (choose : Valuation → LCtx → EnvI) (hc : NativeRepresentative M E n choose) :
    NativeSortMembershipSound E n (fun ν Γ e => M.image ν Γ (choose ν Γ) e) := by
  intro hW ν Γ A u hΓ hA
  obtain ⟨k, R, hcode, _, hm⟩ := (hF hW).1 hΓ hA ν (choose ν Γ) (hc hW ν Γ hΓ)
  rw [M.sort_image] at hcode
  exact M.universe_elim hcode hm

end Rcic.Declarative.Ann.LR3.TypedStatements
