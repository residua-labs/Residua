import rcic.RcicAnnLR3CandidateSubstitution
import rcic.RcicAnnLR3CandidateReflection
import rcic.RcicAnnLR3CandidateReader

/-!
# A Girard Fundamental for the λ2 fragment, and its Target judgments

`Typed ν Γ e c` is a Church-style λ2 typing of a source expression `e`
with an open Girard code `c` as its type. Contexts hold type variables
(`ty k`, ranging over `Sort k`) and term variables (`tm c`). Rules: term
variables, term and type abstraction, and term and type application. Domain
annotations are read by `CandidateReader.Reads`. A type application
substitutes the read argument code (`subst (sub0 cT) cB`).

**Fundamental** (`fundamental`). The theorem is about the open system
(`El = ElA SatFor`). It is proved by induction on the derivation, for every
candidate environment of saturated relations and every pair of raw
environments that realize the context (`GR`). The evaluator's images of the
term in the two environments are related by the Girard reading of its type.
The candidate for a type variable is any relation containing the reflections
of its two raw entries; it is otherwise not tied to the raw type image
(Girard's decoupling). That is what the impredicative products quantify
over. At a type application the instantiating relation is admissible by
CR3 (`CandidateReflection.el_reflect`).

**Target judgments** (`closed_judgment`). For a closed typed term whose source
type reads to its code, the theorem gives an actual `Judgment` in
`EnvironmentEval.annSemantics codeSystem E H`, for every environment `E`,
family syntax `H` and raw environment. Examples: the identity
(`identity_judgment'`), and the impredicative self-instantiation
`id (∀ X : Prop, X → X) id` (`selfApp_judgment`).

This is why the paired arm format is not enough on its own: an arm's
semantic hypotheses cover only decoded candidates, whereas the Girard
products need every admissible candidate. A Fundamental by induction on
derivations, over arbitrary candidate environments, supplies the arms as
wrappers.

Not claimed: conversion rules, constants, inductive types, type-level
computation, term-dependent types, or a reading of `HasTyA` derivations into
`Typed`. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateFundamental

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe CandidateTowerCoherence CandidateCodeSystem CandidateReader
open CandidateSubstitution

inductive Entry where
  | ty (k : Nat)
  | tm {a : Nat} (c : GCode a)

def Entry.kind : Entry → Option Nat
  | .ty k => some k
  | .tm _ => none

def kinds (Γ : List Entry) : List (Option Nat) := Γ.map Entry.kind

def shiftBy (n : Nat) : Nat → Nat := fun j => j + n

inductive Typed (ν : Valuation) : List Entry → ExprA → {k : Nat} → GCode k → Prop
  | var {Γ : List Entry} {i a : Nat} {c : GCode a} (h : Γ[i]? = some (.tm c))
      (hc : Kinded (kinds (Γ.drop (i + 1))) c) :
      Typed ν Γ (.bvar i) (ren (shiftBy (i + 1)) c)
  | lamTm {Γ : List Entry} {A body : ExprA} {u : Level} {a b : Nat} {cA : GCode a}
      {cB : GCode b} (hA : Reads ν (kinds Γ) A cA) (hk : kindOfCode cA = none)
      (hbody : Typed ν (.tm cA :: Γ) body cB) :
      Typed ν Γ (.lam A u body) (.pi cA cB)
  | lamTy {Γ : List Entry} {l u : Level} {body : ExprA} {k b : Nat} {cB : GCode b}
      (hl : eval ν l = some k) (hbody : Typed ν (.ty k :: Γ) body cB) :
      Typed ν Γ (.lam (.sort l) u body) (.pi (.univ k) cB)
  | appTm {Γ : List Entry} {f e : ExprA} {a b : Nat} {cA : GCode a} {cB : GCode b}
      (hf : Typed ν Γ f (.pi cA (ren Nat.succ cB))) (he : Typed ν Γ e cA) :
      Typed ν Γ (.app f e) cB
  | appTy {Γ : List Entry} {f T : ExprA} {k b : Nat} {cB : GCode b} {cT : GCode k}
      (hf : Typed ν Γ f (.pi (.univ k) cB)) (hT : Reads ν (kinds Γ) T cT) :
      Typed ν Γ (.app f T) (subst (sub0 cT) cB)

theorem kinds_drop (Γ : List Entry) (n j : Nat) :
    (kinds Γ)[j + n]? = (kinds (Γ.drop n))[j]? := by
  simp [kinds, List.getElem?_drop, Nat.add_comm]

/-- Types of derivations are kinded by the context. -/
theorem typed_kinded {ν : Valuation} {Γ : List Entry} {e : ExprA} {k : Nat} {c : GCode k}
    (h : Typed ν Γ e c) : Kinded (kinds Γ) c := by
  induction h with
  | @var Γ i a c _ hc =>
      exact kinded_ren c (shiftBy (i + 1)) _ _ (fun j => kinds_drop Γ (i + 1) j) hc
  | lamTm hA hk _ ih =>
      refine ⟨reads_kinded hA, ?_⟩
      rw [hk]
      exact ih
  | lamTy _ _ ih => exact ⟨trivial, ih⟩
  | appTm _ _ ihf _ =>
      exact kinded_ren_inv _ Nat.succ _ _ (fun _ => by simp) ihf.2
  | appTy _ hT ihf => exact kinded_subst0 (reads_kinded hT) ihf.2

/-! ## Realizing environments -/

def tailV (s : EnvI) : EnvI := fun i => s (i + 1)

def tailC (ρ : CEnv) : CEnv := fun i => ρ (i + 1)

/-- Two raw environments realize a context in a candidate environment.
Type variables are bound to universe-related type images at their level,
with a candidate containing their reflections; term variables to related
values of their type. -/
def GR : List Entry → EnvI → EnvI → CEnv → Prop
  | [], _, _, _ => True
  | .ty k :: Γ, s, s', ρ => El σ0 ρ (.univ k) (s 0) (s' 0) ∧ SatFor (s 0) (s' 0) (ρ 0) ∧
      GR Γ (tailV s) (tailV s') (tailC ρ)
  | .tm c :: Γ, s, s', ρ => El σ0 (tailC ρ) c (s 0) (s' 0) ∧ GR Γ (tailV s) (tailV s') (tailC ρ)

theorem gr_var : (Γ : List Entry) → (i : Nat) → ∀ {a : Nat} {c : GCode a} {s s' : EnvI}
    {ρ : CEnv}, Γ[i]? = some (.tm c) → GR Γ s s' ρ →
    El σ0 (fun j => ρ (j + (i + 1))) c (s i) (s' i)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | .ty _ :: _, 0, _, _, _, _, _, h, _ => by simp at h
  | .tm c' :: _, 0, _, _, _, _, _, h, hG => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      cases h
      exact hG.1
  | .ty _ :: Γ, i + 1, _, _, _, _, _, h, hG => gr_var Γ i (by simpa using h) hG.2.2
  | .tm _ :: Γ, i + 1, _, _, _, _, _, h, hG => gr_var Γ i (by simpa using h) hG.2

def consS {k : Nat} (d : GCode k) (τ : Subst) : Subst
  | j, 0 => if h : k = j then h ▸ d else .var j 0
  | j, i + 1 => τ j i

def skipS (τ : Subst) : Subst
  | j, 0 => .var j 0
  | j, i + 1 => τ j i

theorem image_bot0 {k : Nat} (d : GCode k) : (image σ0 d) .bot := image_bot σ0 (fun _ => rfl) d

/-- The type variables of a realized context have closed codes, uniformly
in both raw environments. -/
theorem gr_codes : (Γ : List Entry) → ∀ {s s' : EnvI} {ρ : CEnv}, GR Γ s s' ρ →
    ∃ τ : Subst, ∀ j i, (kinds Γ)[i]? = some (some j) →
      Kinded [] (τ j i) ∧ image σ0 (τ j i) = withBot (s i) ∧ image σ0 (τ j i) = withBot (s' i)
  | [], _, _, _, _ => ⟨fun j i => .var j i, fun _ _ h => by simp [kinds] at h⟩
  | .ty k :: Γ, s, s', _, hG => by
      obtain ⟨⟨d, hd, hV, hW⟩, _, hT⟩ := hG
      obtain ⟨τ, hτ⟩ := gr_codes Γ hT
      refine ⟨consS d τ, fun j i hi => ?_⟩
      cases i with
      | zero =>
          have hj : k = j := by simpa [kinds, Entry.kind] using hi
          subst hj
          have e0 : consS d τ k 0 = d := by simp [consS]
          rw [e0, NeutralCodes.valueEq_eq hV, NeutralCodes.valueEq_eq hW,
            withBot_eq (image_bot0 d)]
          exact ⟨hd, rfl, rfl⟩
      | succ i => exact hτ j i (by simpa [kinds] using hi)
  | .tm _ :: Γ, _, _, _, hG => by
      obtain ⟨τ, hτ⟩ := gr_codes Γ hG.2
      refine ⟨skipS τ, fun j i hi => ?_⟩
      cases i with
      | zero => simp [kinds, Entry.kind] at hi
      | succ i => exact hτ j i (by simpa [kinds] using hi)

/-- Realized entries carry the bottom observation, and type-variable
candidates are coupled to their raw entries. -/
theorem gr_facts : (Γ : List Entry) → ∀ {s s' : EnvI} {ρ : CEnv}, (∀ i, Sat (ρ i)) →
    GR Γ s s' ρ →
    (∀ i, i < Γ.length → s i .bot ∧ s' i .bot) ∧
    (∀ i j, (kinds Γ)[i]? = some (some j) → SatFor (s i) (s' i) (ρ i))
  | [], _, _, _, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => by simp [kinds] at h⟩
  | .ty k :: Γ, s, s', ρ, hρ, hG => by
      obtain ⟨hU, hR, hT⟩ := hG
      obtain ⟨h1, h2⟩ := gr_facts Γ (fun i => hρ (i + 1)) hT
      have hs : SatEnv σ0 ρ := ⟨hρ, fun _ => rfl⟩
      refine ⟨fun i hi => ?_, fun i j hi => ?_⟩
      · cases i with
        | zero =>
            exact ⟨el_saturated σ0 ρ hs (GCode.univ k) _ _ hU,
              el_saturated σ0 ρ hs (GCode.univ k) _ _ ((el_laws_open satFor_laws _ σ0 ρ hs).symm hU)⟩
        | succ i => exact h1 i (Nat.lt_of_succ_lt_succ hi)
      · cases i with
        | zero => exact hR
        | succ i => exact h2 i j (by simpa [kinds] using hi)
  | .tm c :: Γ, s, s', ρ, hρ, hG => by
      obtain ⟨hc, hT⟩ := hG
      obtain ⟨h1, h2⟩ := gr_facts Γ (fun i => hρ (i + 1)) hT
      have hs : SatEnv σ0 (tailC ρ) := ⟨fun i => hρ (i + 1), fun _ => rfl⟩
      refine ⟨fun i hi => ?_, fun i j hi => ?_⟩
      · cases i with
        | zero =>
            exact ⟨el_saturated σ0 _ hs c _ _ hc,
              el_saturated σ0 _ hs c _ _ ((el_laws_open satFor_laws c σ0 _ hs).symm hc)⟩
        | succ i => exact h1 i (Nat.lt_of_succ_lt_succ hi)
      · cases i with
        | zero => simp [kinds, Entry.kind] at hi
        | succ i => exact h2 i j (by simpa [kinds] using hi)

/-! ## The Fundamental -/

theorem satEnv0 {ρ : CEnv} (h : ∀ i, Sat (ρ i)) : SatEnv σ0 ρ := ⟨h, fun _ => rfl⟩

theorem ccons_sat {ρ : CEnv} (h : ∀ i, Sat (ρ i)) {R : Relation} (hR : Sat R) :
    ∀ i, Sat (ccons R ρ i)
  | 0 => hR
  | i + 1 => h i

theorem fundamental (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) {ν : Valuation}
    {Γ : List Entry} {e : ExprA} {k : Nat} {c : GCode k} (h : Typed ν Γ e c) :
    ∀ (s s' : EnvI) (ρ : CEnv), (∀ i, Sat (ρ i)) → GR Γ s s' ρ →
      El σ0 ρ c (EnvironmentEval.denote E H ν s e) (EnvironmentEval.denote E H ν s' e) := by
  induction h with
  | @var Γ i a c hi _ =>
      intro s s' ρ hρ hG
      have hv := gr_var Γ i hi hG
      have hs : SatEnv σ0 (fun j => ρ (j + (i + 1))) := satEnv0 (fun j => hρ _)
      have hx := el_saturated σ0 _ hs c _ _ hv
      have hy := el_saturated σ0 _ hs c _ _ ((el_laws_open satFor_laws c σ0 _ hs).symm hv)
      rw [NeutralCodes.valueEq_eq (bvar_image E H ν s i),
        NeutralCodes.valueEq_eq (bvar_image E H ν s' i), withBot_eq hx, withBot_eq hy]
      exact (el_ren c (shiftBy (i + 1)) σ0 ρ _ _).mpr hv
  | @lamTm Γ A body u a b cA cB _ _ _ ih =>
      intro s s' ρ hρ hG
      refine ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _,
        fun x y hxy R hR => ?_⟩
      have hb := ih (EnvI.cons x s) (EnvI.cons y s') (ccons R ρ) (ccons_sat hρ hR.1) ⟨hxy, hG⟩
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application E H ν s A body u x),
        NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application E H ν s' A body u y)]
      exact ⟨(el_raw cB σ0 _ _ _ _).mp hb, (el_raw cB σ0 _ _ _ _).mp hb⟩
  | @lamTy Γ l u body k b cB _ _ ih =>
      intro s s' ρ hρ hG
      refine ⟨EnvironmentEval.denote_bot _ _ _ _ _, EnvironmentEval.denote_bot _ _ _ _ _,
        fun x y hxy R hR => ?_⟩
      have hb := ih (EnvI.cons x s) (EnvI.cons y s') (ccons R ρ) (ccons_sat hρ hR.1)
        ⟨hxy, hR, hG⟩
      rw [NeutralCodes.valueEq_eq
          (EnvironmentEval.denote_lambda_application E H ν s (.sort l) body u x),
        NeutralCodes.valueEq_eq
          (EnvironmentEval.denote_lambda_application E H ν s' (.sort l) body u y)]
      exact ⟨(el_raw cB σ0 _ _ _ _).mp hb, (el_raw cB σ0 _ _ _ _).mp hb⟩
  | @appTm Γ f e a b cA cB _ _ ihf ihe =>
      intro s s' ρ hρ hG
      have hF := ihf s s' ρ hρ hG
      have hX := ihe s s' ρ hρ hG
      have h1 := (hF.2.2 _ _ hX botRel (botRel_satFor _ _)).1
      have h2 := (el_ren cB Nat.succ _ _ _ _).mp h1
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s f e),
        NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s' f e)]
      exact (el_raw cB _ σ0 ρ _ _).mp h2
  | @appTy Γ f T k b cB cT hf hT ihf =>
      intro s s' ρ hρ hG
      have hs := satEnv0 hρ
      have hF := ihf s s' ρ hρ hG
      obtain ⟨τ, hτ⟩ := gr_codes Γ hG
      have hκ := reads_kinded hT
      have hd : Kinded [] (subst τ cT) :=
        kinded_subst cT τ _ [] (fun j i hi => (hτ j i hi).1) hκ
      have e1 : image σ0 (subst τ cT) = image s cT :=
        image_subst cT τ _ σ0 s (fun j i hi => (hτ j i hi).2.1) hκ
      have e2 : image σ0 (subst τ cT) = image s' cT :=
        image_subst cT τ _ σ0 s' (fun j i hi => (hτ j i hi).2.2) hκ
      have hU : El σ0 ρ (GCode.univ k) (EnvironmentEval.denote E H ν s T)
          (EnvironmentEval.denote E H ν s' T) :=
        ⟨subst τ cT, hd, e1 ▸ reads_image E H hT s, e2 ▸ reads_image E H hT s'⟩
      obtain ⟨hbots, hcoup⟩ := gr_facts Γ hρ hG
      have hlen : (kinds Γ).length = Γ.length := List.length_map _ _
      let s₁ : REnv := fun i => if i < Γ.length then s i else bottom
      let s₂ : REnv := fun i => if i < Γ.length then s' i else bottom
      have hcl : ClosedAt Γ.length cT := hlen ▸ kinded_closed cT (kinds Γ) hκ
      have e3 : image s₁ cT = image s cT :=
        image_closed cT _ s₁ s hcl (fun i hi => by simp [s₁, hi])
      have e4 : image s₂ cT = image s' cT :=
        image_closed cT _ s₂ s' hcl (fun i hi => by simp [s₂, hi])
      have hs₁ : SatEnv s₁ ρ := ⟨hρ, fun i => by
        by_cases hi : i < Γ.length
        · simp only [s₁, if_pos hi]
          exact (hbots i hi).1
        · simp only [s₁, if_neg hi]
          rfl⟩
      have hs₂ : ∀ i, s₂ i .bot := fun i => by
        by_cases hi : i < Γ.length
        · simp only [s₂, if_pos hi]
          exact (hbots i hi).2
        · simp only [s₂, if_neg hi]
          rfl
      have hcp : ∀ i j, (kinds Γ)[i]? = some (some j) → SatFor (s₁ i) (s₂ i) (ρ i) := by
        intro i j hi
        have hlt : i < Γ.length := hlen ▸ lt_of_getElem? _ i _ hi
        simp only [s₁, s₂, if_pos hlt]
        exact hcoup i j hi
      have hR : SatFor (EnvironmentEval.denote E H ν s T) (EnvironmentEval.denote E H ν s' T)
          (El σ0 ρ cT) := by
        refine ⟨⟨el_laws_open satFor_laws cT σ0 ρ hs, el_saturated σ0 ρ hs cT⟩,
          fun n m hn hm => ?_⟩
        rw [NeutralCodes.valueEq_eq (reads_image E H hT s),
          NeutralCodes.valueEq_eq (reads_image E H hT s'), ← e3, ← e4]
        exact (el_raw cT s₁ σ0 ρ _ _).mp
          (CandidateReflection.el_reflect cT (kinds Γ) s₁ s₂ ρ hκ hs₁ hs₂ hcp n m hn hm)
      have h1 := (hF.2.2 _ _ hU _ hR).1
      have h2 := (el_raw cB _ σ0 _ _ _).mp h1
      have hB : Kinded (some k :: kinds Γ) cB := (typed_kinded hf).2
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s f T),
        NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν s' f T)]
      exact (el_subst0 satFor_laws hB σ0 ρ hs _ _).mpr h2

/-! ## Target judgments for closed terms -/

theorem closed_judgment (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) {ν : Valuation}
    {e T : ExprA} {k : Nat} {c : GCode k} (he : Typed ν [] e c) (hT : Reads ν [] T c)
    (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics codeSystem E H) ν [] ρ e e T := by
  have hc := reads_code E H hT ρ
  exact ⟨some k, El σ0 ρ0 c, hc, codeSystem.defined hc,
    fundamental E H he ρ ρ ρ0 (fun _ => botRel_sat) trivial⟩

theorem identity_typed (ν : Valuation) :
    Typed ν [] ImpredicativePiProbe.identityTerm identityCode :=
  .lamTy rfl (.lamTm (.bvar rfl) rfl
    (.var (Γ := [.tm (GCode.var 0 0), .ty 0]) (i := 0) (c := GCode.var 0 0) rfl
      (show ([some 0] : List (Option Nat))[0]? = some (some 0) from rfl)))

theorem identity_judgment' (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics codeSystem E H) ν [] ρ
      ImpredicativePiProbe.identityTerm ImpredicativePiProbe.identityTerm
      ImpredicativePiProbe.identityType :=
  closed_judgment E H (identity_typed ν) (reads_identityType ν) ρ

/-- `id (∀ X : Prop, X → X) id`: the identity instantiated at its own type. -/
def selfApp : ExprA :=
  .app (.app ImpredicativePiProbe.identityTerm ImpredicativePiProbe.identityType)
    ImpredicativePiProbe.identityTerm

theorem selfApp_typed (ν : Valuation) : Typed ν [] selfApp identityCode :=
  .appTm (cA := identityCode) (cB := identityCode)
    (.appTy (identity_typed ν) (reads_identityType ν)) (identity_typed ν)

theorem selfApp_judgment (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics codeSystem E H) ν [] ρ selfApp selfApp
      ImpredicativePiProbe.identityType :=
  closed_judgment E H (selfApp_typed ν) (reads_identityType ν) ρ

end Rcic.Declarative.Ann.LR3.CandidateFundamental
