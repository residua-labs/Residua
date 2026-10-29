import rcic.RcicAnnLR3TypeZeroTowerProbe
import rcic.RcicAnnLR3ImpredicativePiProbe
import rcic.RcicAnnLR3ObservationReflection

/-!
# Probe: open codes in candidate environments (Girard-style tower)

The closed tower needs each Pi code's fibres as a function from raw
arguments to codes. A Prop-level `∀ x ∃ code` hypothesis yields that only by
choice, and a raw type variable cannot be decoded back to code data. This
probe tests the standard alternative.

**Design.** Codes are open: de Bruijn variables `var i` may occur, and every
Pi binds one. A code is interpreted relative to a raw environment `σ` (for
images) and a candidate environment `ρ` (for relations). A product's codomain
is interpreted at every pair of related raw arguments and every admissible
candidate for its bound variable. Admissibility is a parameter (`ElA adm`).
The closed system `ElS` admits every saturated candidate, where saturation
is bot-closure, the condition the evaluator forces on variables
(impredicative probe). The open system `El` (`SatFor`) also requires the
candidate to contain the observation-directed reflections of its two raw
arguments (CR3 relative to the raw type). A source type is read to a code
syntactically, so no choice and no decoding is needed. Neutral types relate
all neutrals, and named neutral types do not use the sort head 11.

**(1)** `GCode : Nat → Type`; the image and the interpretation are structural
into `Value`/`Prop` and unfold by `rfl` on closed examples.
**(2)** The evaluator's image of the typed closed identity `λ (X : Prop) (x : X). x`
is related to itself at the Girard reading of `∀ X : Prop, X → X`, for every
lawful admissibility (`identity_realized`).
**(3)** In saturated environments every relation is bot-closed
(`el_saturated`), including universe, neutral, product and variable codes.

Coherence of raw images with interpretations for open codes is not proved
here. The stated plan is to quantify images over all raw environments, so that
variables are separated by varying them. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateTowerProbe

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN)

/-- Open codes. Every product binds one variable. -/
inductive GCode : Nat → Type
  | var (k i : Nat) : GCode k
  | univ (k : Nat) : GCode (k + 1)
  | neutral (k name : Nat) : GCode k
  | pi {a b : Nat} (A : GCode a) (B : GCode b) : GCode (imaxN a b)

abbrev REnv := Nat → Value
abbrev CEnv := Nat → Relation

def rcons (x : Value) (σ : REnv) : REnv
  | 0 => x
  | i + 1 => σ i

def ccons (R : Relation) (ρ : CEnv) : CEnv
  | 0 => R
  | i + 1 => ρ i

/-- Raw images in a raw environment. A variable's image is its entry with
the bottom observation, exactly the evaluator's variable denotation. -/
def image : {k : Nat} → REnv → GCode k → Value
  | _, σ, .var _ i => TypeZeroTowerProbe.withBot (σ i)
  | _, _, .univ k => universeValue (some k)
  | _, _, .neutral k name => NativeMemberValues.value (some k) name
  | _, σ, @GCode.pi a b A B => InductiveCodes.piValue (some (imaxN a b)) (image σ A)
      (UnifiedPi.legalGraph (fun _ _ => True) (fun x => image (rcons x σ) B))

/-- Saturated candidates: PERs whose related values carry the bottom
observation. -/
def Sat (R : Relation) : Prop := Laws R ∧ ∀ x y, R x y → x .bot

/-- Reflectable neutrals: neutral values whose head is not the sort payload
head 11. -/
def Ntr (n : Value) : Prop := CandidatePi.Neutral n ∧ TypeZeroTowerProbe.Head11Free n

/-- Admissibility of a candidate for a bound variable at two related raw
arguments. -/
abbrev Adm := Value → Value → Relation → Prop

/-- Plain saturation (the closed system). -/
def satAdm : Adm := fun _ _ R => Sat R

/-- Saturation containing the reflections of the two raw arguments (the open
system, CR3 relative to the raw type). -/
def SatFor : Adm := fun x y R =>
  Sat R ∧ ∀ n m, Ntr n → Ntr m →
    R (ObservationReflection.reflV x n) (ObservationReflection.reflV y m)

structure AdmLaws (adm : Adm) : Prop where
  sat : ∀ {x y : Value} {R : Relation}, adm x y R → Sat R
  symm : ∀ {x y : Value} {R : Relation}, adm x y R → adm y x R
  left : ∀ {x y : Value} {R : Relation}, adm x y R → adm x x R

/-- Scope: every variable is bound within `n` enclosing binders. -/
def ClosedAt : {k : Nat} → Nat → GCode k → Prop
  | _, n, .var _ i => i < n
  | _, _, .univ _ => True
  | _, _, .neutral _ _ => True
  | _, n, .pi A B => ClosedAt n A ∧ ClosedAt (n + 1) B

/-- The kind a product binder gives its variable: the level of a universe
domain, or none for any other domain. -/
def kindOfCode : {k : Nat} → GCode k → Option Nat
  | _, .univ j => some j
  | _, .var _ _ => none
  | _, .neutral _ _ => none
  | _, .pi _ _ => none

/-- Kinding: every variable is bound by a universe binder of its own level.
Named neutral types do not use the sort head 11. -/
def Kinded : {k : Nat} → List (Option Nat) → GCode k → Prop
  | _, κ, .var k i => κ[i]? = some (some k)
  | _, _, .univ _ => True
  | _, _, .neutral _ name => name ≠ 11
  | _, κ, .pi A B => Kinded κ A ∧ Kinded (kindOfCode A :: κ) B

/-- The Girard reading, parametric in candidate admissibility: products
quantify over every admissible candidate for their bound variable, and relate
applications in the codomain at both related arguments. Universes relate
images of closed, kinded codes. Neutral types relate all neutrals. A
level-zero type variable is read through the irrelevant closure of its
candidate (proof irrelevance). -/
def ElA (adm : Adm) : {k : Nat} → REnv → CEnv → GCode k → Relation
  | _, _, ρ, .var 0 i => fun x y => ρ i x x ∧ ρ i y y
  | _, _, ρ, .var (_ + 1) i => ρ i
  | _, σ, _, .univ k => fun V W =>
      ∃ c : GCode k, Kinded [] c ∧ ValueEq V (image σ c) ∧ ValueEq W (image σ c)
  | _, _, _, .neutral _ _ => fun x y => CandidatePi.Neutral x ∧ CandidatePi.Neutral y
  | _, σ, ρ, .pi A B => fun f g => f .bot ∧ g .bot ∧ ∀ x y, ElA adm σ ρ A x y →
      ∀ R : Relation, adm x y R →
        ElA adm (rcons x σ) (ccons R ρ) B (NeutralPi.applyValue f x)
          (NeutralPi.applyValue g y) ∧
        ElA adm (rcons y σ) (ccons R ρ) B (NeutralPi.applyValue f x)
          (NeutralPi.applyValue g y)

/-- The open system: candidates contain the reflections of their raw type. -/
abbrev El : {k : Nat} → REnv → CEnv → GCode k → Relation := ElA SatFor

/-- The closed system: plain saturated candidates. -/
abbrev ElS : {k : Nat} → REnv → CEnv → GCode k → Relation := ElA satAdm

/-! ## (1) Unfolding -/

/-- `∀ X : Prop, X → X`, with `X` as variable 1 under the inner binder. -/
def identityCode : GCode 0 := .pi (.univ 0) (.pi (.var 0 0) (.var 0 1))

theorem identityCode_level : imaxN 1 (imaxN 0 0) = 0 := rfl

theorem el_identity_unfold (σ : REnv) (ρ : CEnv) (f g : Value) :
    El σ ρ identityCode f g =
      (f .bot ∧ g .bot ∧ ∀ X Y, El σ ρ (GCode.univ 0) X Y → ∀ R : Relation, SatFor X Y R →
        El (rcons X σ) (ccons R ρ) (GCode.pi (.var 0 0) (.var 0 1))
          (NeutralPi.applyValue f X) (NeutralPi.applyValue g Y) ∧
        El (rcons Y σ) (ccons R ρ) (GCode.pi (.var 0 0) (.var 0 1))
          (NeutralPi.applyValue f X) (NeutralPi.applyValue g Y)) := rfl

theorem el_var_unfold (σ : REnv) (ρ : CEnv) (i : Nat) : El σ ρ (GCode.var 3 i) = ρ i := rfl

theorem image_var_unfold (σ : REnv) (i : Nat) :
    image σ (GCode.var 0 i) = TypeZeroTowerProbe.withBot (σ i) := rfl

/-! ## (2) The evaluator realizes the impredicative identity -/

theorem sat_bot_closed {F : EnvironmentEval.FamilySyntax} {ν : Valuation} {ρ₀ ρ₁ : EnvI}
    {R : Relation} (hR : Sat R) {x y : Value} (h : R x y) :
    R (EnvironmentEval.denote emptyEnvA F ν (EnvI.cons x ρ₀) (.bvar 0))
      (EnvironmentEval.denote emptyEnvA F ν (EnvI.cons y ρ₁) (.bvar 0)) := by
  have hx : x .bot := hR.2 x y h
  have hy : y .bot := hR.2 y x (hR.1.symm h)
  rw [NeutralCodes.valueEq_eq (RCodeProofReadback.environment_variable_image emptyEnvA F ν
      (EnvI.cons x ρ₀) 0 hx),
    NeutralCodes.valueEq_eq (RCodeProofReadback.environment_variable_image emptyEnvA F ν
      (EnvI.cons y ρ₁) 0 hy)]
  exact h

/-- The inner layer `X → X` of the identity, at either raw environment. -/
theorem identity_inner {adm : Adm} (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (σ : REnv) (ρ : CEnv) (R : Relation) (hR : Sat R) (Z X Y : Value) :
    ElA adm (rcons Z σ) (ccons R ρ) (GCode.pi (.var 0 0) (.var 0 1))
      (EnvironmentEval.denote emptyEnvA F ν (EnvI.cons X EnvI.bot) ImpredicativePiProbe.innerLambda)
      (EnvironmentEval.denote emptyEnvA F ν (EnvI.cons Y EnvI.bot) ImpredicativePiProbe.innerLambda) := by
  refine ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _, ?_⟩
  intro x y hxy R' _
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      _ (.bvar 0) (.bvar 0) .zero x),
    NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      _ (.bvar 0) (.bvar 0) .zero y)]
  exact ⟨⟨sat_bot_closed hR hxy.1, sat_bot_closed hR hxy.2⟩,
    ⟨sat_bot_closed hR hxy.1, sat_bot_closed hR hxy.2⟩⟩

/-- The evaluator's image of the typed closed identity is related to itself
at the Girard reading of `∀ X : Prop, X → X`, in every environment. -/
theorem identity_realized {adm : Adm} (ha : AdmLaws adm) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (σ : REnv) (ρ : CEnv) :
    ElA adm σ ρ identityCode
      (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm)
      (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm) := by
  refine ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _, ?_⟩
  intro X Y _ R hR
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      EnvI.bot (.sort .zero) ImpredicativePiProbe.innerLambda (.succ .zero) X),
    NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      EnvI.bot (.sort .zero) ImpredicativePiProbe.innerLambda (.succ .zero) Y)]
  exact ⟨identity_inner F ν σ ρ R (ha.sat hR) X X Y, identity_inner F ν σ ρ R (ha.sat hR) Y X Y⟩

/-! ## (3) Saturation in saturated environments -/

def SatEnv (σ : REnv) (ρ : CEnv) : Prop := (∀ i, Sat (ρ i)) ∧ ∀ i, σ i .bot

theorem image_bot {k : Nat} (σ : REnv) (_hσ : ∀ i, σ i .bot) : (c : GCode k) → image σ c .bot
  | .var _ _ => Or.inl rfl
  | .univ _ => .bot _ _
  | .neutral _ _ => NativeMemberValues.value_bot _ _
  | .pi _ _ => Or.inl rfl

/-- Every relation is bot-closed in a saturated environment. -/
theorem el_saturated {adm : Adm} {k : Nat} (σ : REnv) (ρ : CEnv) (h : SatEnv σ ρ) :
    (c : GCode k) → ∀ x y, ElA adm σ ρ c x y → x .bot
  | .var 0 i => fun _ _ hxy => (h.1 i).2 _ _ hxy.1
  | .var (_ + 1) i => fun _ _ hxy => (h.1 i).2 _ _ hxy
  | .univ _ => fun _ _ ⟨c, _, hx, _⟩ => (hx .bot).mpr (image_bot σ h.2 c)
  | .neutral _ _ => fun _ _ hxy => RCodeSoundPiControl.neutral_bot hxy.1
  | .pi _ _ => fun _ _ hxy => hxy.1

theorem satEnv_rcons {σ : REnv} {ρ : CEnv} (h : SatEnv σ ρ) {x : Value} (hx : x .bot)
    {R : Relation} (hR : Sat R) : SatEnv (rcons x σ) (ccons R ρ) :=
  ⟨fun i => by cases i; exact hR; exact h.1 _, fun i => by cases i; exact hx; exact h.2 _⟩

/-- Every interpretation is a PER in a saturated environment. -/
theorem neutral_laws : Laws (fun x y => CandidatePi.Neutral x ∧ CandidatePi.Neutral y) :=
  ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, _⟩ ⟨_, c⟩ => ⟨a, c⟩⟩

theorem el_laws_open {adm : Adm} (ha : AdmLaws adm) :
    {k : Nat} → (c : GCode k) → ∀ σ ρ, SatEnv σ ρ → Laws (ElA adm σ ρ c)
  | _, .var 0 _, _, _, _ => ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, _⟩ ⟨_, c⟩ => ⟨a, c⟩⟩
  | _, .var (_ + 1) i, _, _, h => (h.1 i).1
  | _, .univ _, _, _, _ =>
      ⟨fun ⟨c, hc, hv, hw⟩ => ⟨c, hc, hw, hv⟩,
        fun ⟨c, hc, hv, hw⟩ ⟨_, _, hw', hz⟩ => ⟨c, hc, hv, hz.trans (hw'.symm.trans hw)⟩⟩
  | _, .neutral _ _, _, _, _ => neutral_laws
  | _, .pi A B, σ, ρ, h => by
      have lA := el_laws_open ha A σ ρ h
      have bot : ∀ x y, ElA adm σ ρ A x y → x .bot := el_saturated σ ρ h A
      refine ⟨?_, ?_⟩
      · rintro f g ⟨hf, hg, hfg⟩
        refine ⟨hg, hf, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := hfg y x (lA.symm hxy) R (ha.symm hR)
        exact ⟨(el_laws_open ha B _ _ (satEnv_rcons h (bot x y hxy) (ha.sat hR))).symm h2,
          (el_laws_open ha B _ _
            (satEnv_rcons h (bot y x (lA.symm hxy)) (ha.sat hR))).symm h1⟩
      · rintro f g k ⟨hf, _, hfg⟩ ⟨_, hk, hgk⟩
        refine ⟨hf, hk, fun x y hxy R hR => ?_⟩
        have hxx := lA.trans hxy (lA.symm hxy)
        have hyy := lA.trans (lA.symm hxy) hxy
        have hRx := ha.left hR
        have hRy := ha.left (ha.symm hR)
        exact ⟨(el_laws_open ha B _ _ (satEnv_rcons h (bot x y hxy) (ha.sat hR))).trans
            (hfg x x hxx R hRx).1 (hgk x y hxy R hR).1,
          (el_laws_open ha B _ _ (satEnv_rcons h (bot y x (lA.symm hxy)) (ha.sat hR))).trans
            (hfg x y hxy R hR).2 (hgk y y hyy R hRy).1⟩

/-! ## The two admissibilities -/

theorem satAdm_laws : AdmLaws satAdm := ⟨id, id, id⟩

theorem satFor_laws : AdmLaws SatFor := by
  refine ⟨fun h => h.1, fun ⟨hs, h⟩ => ⟨hs, fun n m hn hm => hs.1.symm (h m n hm hn)⟩,
    fun ⟨hs, h⟩ => ⟨hs, fun n m hn hm => ?_⟩⟩
  exact hs.1.trans (h n n hn hn) (hs.1.symm (h m n hm hn))

end Rcic.Declarative.Ann.LR3.CandidateTowerProbe
