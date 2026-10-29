import rcic.RcicAnnLR3CandidateTowerCoherence
import rcic.RcicAnnLR3ImageKeyedCodeSystem
import rcic.RcicAnnLR3EnvironmentPi
import rcic.RcicAnnLR3IotaLiftLaw

/-!
# Closed Girard codes as an image-keyed code system (R7 link)

Closed, kinded open-codes are interpreted in one fixed saturated
environment. Their
raw images do not depend on the raw environment, so equal images in one
environment give equal images in all bot-containing environments. Open
coherence then makes them an image-keyed family. Well-formed means kinded,
and kinded implies closed. The relation is the Girard reading, and the
universe relates images of kinded codes. The generic builder produces an
Option-indexed `CodeSystem` with universe transport, Prop irrelevance
(level-zero type variables are read through the irrelevant closure of their
candidates) and the original `Ty_sort`.

**End-to-end check** (`identity_judgment`). In the model
`EnvironmentEval.annSemantics codeSystem emptyEnvA F`, the closed typed
identity `λ (X : Prop) (x : X). x : ∀ X : Prop, X → X` has an actual
`Judgment`: the evaluator's image of the type is the image of the closed
Girard code of `∀ X : Prop, X → X`, so the system decodes it. The
evaluator's image of the term is related to itself by that code's Girard
relation, which quantifies over every admissible candidate.

The builder `familyA` works for any lawful admissibility. `family` (and
`codeSystem`) is the open system (`SatFor`); `familyS` (and `codeSystemS`)
is the closed system with plain saturated candidates.

This links the impredicative Girard reading to the image-keyed `Target`
shape on a closed instance. It is not a Fundamental theorem: there is no
reader for all source types and no context arms. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateCodeSystem

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe CandidateTowerCoherence

/-! ## Closed images do not depend on the raw environment -/

theorem image_closed : {k : Nat} → (c : GCode k) → ∀ (n : Nat) (σ σ' : REnv),
    ClosedAt n c → (∀ i, i < n → σ i = σ' i) → image σ c = image σ' c
  | _, .var _ i, _, σ, σ', hc, h => by
      show withBot (σ i) = withBot (σ' i)
      rw [h i hc]
  | _, .univ _, _, _, _, _, _ => rfl
  | _, .neutral _ _, _, _, _, _, _ => rfl
  | _, .pi A B, n, σ, σ', hc, h => by
      have hA := image_closed A n σ σ' hc.1 h
      have hB : (fun x => image (rcons x σ) B) = (fun x => image (rcons x σ') B) := by
        funext x
        exact image_closed B (n + 1) _ _ hc.2 (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (Nat.lt_of_succ_lt_succ hi))
      show InductiveCodes.piValue _ (image σ A) _ = InductiveCodes.piValue _ (image σ' A) _
      rw [hA, hB]

/-! ## The fixed saturated environment -/

def σ0 : REnv := fun _ => bottom

def botRel : Relation := fun x y => x .bot ∧ y .bot

theorem botRel_sat : Sat botRel := ⟨⟨fun h => ⟨h.2, h.1⟩, fun h g => ⟨h.1, g.2⟩⟩, fun _ _ h => h.1⟩

def ρ0 : CEnv := fun _ => botRel

theorem sat0 : SatEnv σ0 ρ0 := ⟨fun _ => botRel_sat, fun _ => rfl⟩

/-- `botRel` is admissible in the open system at any two arguments. -/
theorem botRel_satFor (x y : Value) : SatFor x y botRel :=
  ⟨botRel_sat, fun _ _ _ _ => ⟨.bot _ _, .bot _ _⟩⟩

theorem lt_of_getElem? {α : Type} : (l : List α) → (i : Nat) → (a : α) → l[i]? = some a →
    i < l.length
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: l, i + 1, a, h => Nat.succ_lt_succ (lt_of_getElem? l i a (by simpa using h))

/-- Kinded codes are closed below their kind context. -/
theorem kinded_closed : {k : Nat} → (c : GCode k) → ∀ κ : List (Option Nat), Kinded κ c →
    ClosedAt κ.length c
  | _, .var _ i, κ, h => lt_of_getElem? κ i _ h
  | _, .univ _, _, _ => trivial
  | _, .neutral _ _, _, _ => trivial
  | _, .pi A B, κ, h => ⟨kinded_closed A κ h.1, kinded_closed B _ h.2⟩

theorem closed_imageEq {k l : Nat} {c : GCode k} {d : GCode l} (hc : ClosedAt 0 c)
    (hd : ClosedAt 0 d) (h : ValueEq (image σ0 c) (image σ0 d)) : ImageEq c d := by
  intro σ _
  rw [image_closed c 0 σ σ0 hc (fun _ hi => absurd hi (Nat.not_lt_zero _)),
    image_closed d 0 σ σ0 hd (fun _ hi => absurd hi (Nat.not_lt_zero _))]
  exact h

theorem closed_level : {k : Nat} → (c : GCode k) → ClosedAt 0 c →
    SortMember (some k) (image σ0 c) ∧ TypeDefined (image σ0 c)
  | _, .var _ _, hc => absurd hc (Nat.not_lt_zero _)
  | _, .univ k, _ => ⟨sort_member _ (some k), sort_defined _ (some k)⟩
  | _, .neutral k name, _ =>
      ⟨NativeMemberValues.value_level (some k) name, NativeMemberValues.value_defined (some k) name⟩
  | _, .pi _ _, _ => ⟨InductiveCodes.piValue_level _ _ _, InductiveCodes.piValue_defined _ _ _⟩

/-! ## The image-keyed family -/

/-- The image-keyed family of closed kinded codes, for any admissibility. -/
def familyA (adm : Adm) (ha : AdmLaws adm) : ImageKeyedCodeSystem.Family where
  Cd := GCode
  ok := fun c => Kinded [] c
  img := fun c => image σ0 c
  rel := fun c => ElA adm σ0 ρ0 c
  laws := fun c _ => el_laws_open ha c σ0 ρ0 sat0
  level := fun c hc => (closed_level c (kinded_closed c [] hc)).1
  defined := fun c hc => (closed_level c (kinded_closed c [] hc)).2
  coherent := fun c d hc hd h => open_coherent ha c d [] hc hd
    (closed_imageEq (kinded_closed c [] hc) (kinded_closed d [] hd) h) σ0 ρ0 sat0
  univ := GCode.univ
  univ_ok := fun _ => trivial
  univ_img := fun _ => ValueEq.refl _
  univ_member := fun k => ⟨GCode.univ k, trivial, ValueEq.refl _, ValueEq.refl _⟩
  univ_decode := by
    rintro k V W ⟨c, hc, hV, hW⟩
    exact ⟨c, c, hc, hc, hV, hW, fun _ _ => Iff.rfl⟩

/-- The open system: candidates contain the reflections of their raw type. -/
def family : ImageKeyedCodeSystem.Family := familyA SatFor satFor_laws

/-- The closed system, with plain saturated candidates. -/
def familyS : ImageKeyedCodeSystem.Family := familyA satAdm satAdm_laws

def codeSystem : CodeSystem := family.codeSystem

def codeSystemS : CodeSystem := familyS.codeSystem

theorem universeTransport : PairedStatements.UniverseTransport codeSystem :=
  family.universeTransport

/-- Level-zero codes are proof-irrelevant. -/
theorem propIrrelevance : PairedStatements.PropIrrelevance codeSystem :=
  family.propIrrelevance (fun c _ x y hx hy => el_irrelevant satFor_laws c rfl σ0 ρ0 sat0 x y hx hy)

/-! ## The closed identity, end to end -/

theorem identityCode_kinded : Kinded [] identityCode := ⟨trivial, rfl, rfl⟩

theorem identityCode_closed : ClosedAt 0 identityCode := kinded_closed _ [] identityCode_kinded

theorem bvar_image (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (i : Nat) : ValueEq (EnvironmentEval.denote E H ν ρ (.bvar i)) (withBot (ρ i)) := by
  rw [IotaRecursor.denote_bvar]
  intro c
  constructor
  · intro h
    exact approxI_bvar_inv h
  · rintro (h | h)
    · rw [h]
      exact .bot _ _
    · exact .bvar h

theorem legalGraph_congr {F G : Value → Value} (h : ∀ x, ValueEq (F x) (G x)) :
    UnifiedPi.legalGraph (fun _ _ => True) F = UnifiedPi.legalGraph (fun _ _ => True) G := by
  have : F = G := funext fun x => NeutralCodes.valueEq_eq (h x)
  rw [this]

theorem inner_image (H : EnvironmentEval.FamilySyntax) (ν : Valuation) (X : Value) :
    ValueEq (EnvironmentEval.denote emptyEnvA H ν (EnvI.cons X EnvI.bot)
        ImpredicativePiProbe.innerType)
      (image (rcons X σ0) (GCode.pi (.var 0 0) (.var 0 1))) := by
  have h := EnvironmentEval.denote_pi_value emptyEnvA H ν (EnvI.cons X EnvI.bot)
    (.bvar 0) (.bvar 1) .zero .zero
  have hl := NeutralCodes.valueEq_eq
    (EnvironmentEval.denote_lambda_graph emptyEnvA H ν (EnvI.cons X EnvI.bot) (.bvar 0) (.bvar 1) .zero)
  rw [hl, NeutralCodes.valueEq_eq (bvar_image emptyEnvA H ν _ 0),
    legalGraph_congr (fun x => bvar_image emptyEnvA H ν (EnvI.cons x (EnvI.cons X EnvI.bot)) 1)] at h
  exact h

theorem identity_type_image (H : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    ValueEq (EnvironmentEval.denote emptyEnvA H ν EnvI.bot ImpredicativePiProbe.identityType)
      (image σ0 identityCode) := by
  have h := EnvironmentEval.denote_pi_value emptyEnvA H ν EnvI.bot
    (.sort .zero) ImpredicativePiProbe.innerType (.succ .zero) (.imax .zero .zero)
  have hl := NeutralCodes.valueEq_eq
    (EnvironmentEval.denote_lambda_graph emptyEnvA H ν EnvI.bot (.sort .zero)
      ImpredicativePiProbe.innerType (.succ .zero))
  have hs : EnvironmentEval.denote emptyEnvA H ν EnvI.bot (.sort .zero) = universeValue (some 0) :=
    (EnvironmentEval.annSemantics codeSystem emptyEnvA H).sort_image ν [] EnvI.bot .zero
  rw [hl, hs, legalGraph_congr (fun X => inner_image H ν X)] at h
  exact h

/-- An actual model judgment for the closed impredicative identity. -/
theorem identity_judgment (H : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    Judgment (EnvironmentEval.annSemantics codeSystem emptyEnvA H) ν [] EnvI.bot
      ImpredicativePiProbe.identityTerm ImpredicativePiProbe.identityTerm
      ImpredicativePiProbe.identityType := by
  refine ⟨some 0, El σ0 ρ0 identityCode,
    family.ok_code (c := identityCode) identityCode_kinded (identity_type_image H ν),
    typeDefined_congr (identity_type_image H ν).symm (closed_level _ identityCode_closed).2, ?_⟩
  exact identity_realized satFor_laws H ν σ0 ρ0

end Rcic.Declarative.Ann.LR3.CandidateCodeSystem
