import rcic.RcicAnnLR3CandidateCodeSystem
import rcic.RcicAnnLR3TowerSourcePi

/-!
# An image-exact reader for the type fragment into open Girard codes

`Reads ν κ e c` reads a source type `e` (sorts, products and type
variables) to an open Girard code `c`. The kind context `κ` records, for
each bound variable, the evaluated level of the sort it ranges over, or
`none` for a variable of a non-sort domain, which is never read as a type.
A product is read only when both evaluated annotation levels are finite,
and its code index is their `imax`.

Reading is a relation, so a proof that needs a code eliminates one
existential. No reader function is extracted and no choice is used.
Fibres are open codes, so no function from raw arguments to codes is
needed.

`reads_image` shows reading is image-exact: in every raw environment, the
actual evaluator image of the source type IS the image of its code.
`reads_closed` shows a type read in the empty kind context is a closed
code. Hence `reads_code`: every closed source type of the fragment is a code
of the Girard code system at its level, with the Girard relation of its
code. The impredicative identity type is an instance. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateReader

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe CandidateCodeSystem

/-- The kind a product binder gives its variable. -/
def kindOf (ν : Valuation) : ExprA → Option Nat
  | .sort l => eval ν l
  | _ => none

inductive Reads (ν : Valuation) : List (Option Nat) → ExprA → {k : Nat} → GCode k → Prop
  | sort {κ : List (Option Nat)} {l : Level} {k : Nat} (h : eval ν l = some k) :
      Reads ν κ (.sort l) (.univ k)
  | bvar {κ : List (Option Nat)} {i k : Nat} (h : κ[i]? = some (some k)) :
      Reads ν κ (.bvar i) (.var k i)
  | pi {κ : List (Option Nat)} {A B : ExprA} {u v : Level} {a b : Nat}
      {cA : GCode a} {cB : GCode b} (hu : eval ν u = some a) (hv : eval ν v = some b)
      (hA : Reads ν κ A cA) (hB : Reads ν (kindOf ν A :: κ) B cB) :
      Reads ν κ (.pi A u B v) (.pi cA cB)

theorem rcons_eq_cons (x : Value) (ρ : EnvI) : rcons x ρ = EnvI.cons x ρ := by
  funext i
  cases i <;> rfl

/-- Reading is image-exact in every raw environment. -/
theorem reads_image {ν : Valuation} (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    {κ : List (Option Nat)} {e : ExprA} {k : Nat} {c : GCode k} (h : Reads ν κ e c) :
    ∀ ρ : EnvI, ValueEq (EnvironmentEval.denote E H ν ρ e) (image ρ c) := by
  induction h with
  | @sort κ l k hl =>
      intro ρ
      have hs : EnvironmentEval.denote E H ν ρ (.sort l) = universeValue (eval ν l) :=
        (EnvironmentEval.annSemantics codeSystem E H).sort_image ν [] ρ l
      rw [hs, hl]
      exact ValueEq.refl _
  | @bvar κ i k _ =>
      intro ρ
      exact bvar_image E H ν ρ i
  | @pi κ A B u v a b cA cB hu hv _ _ ihA ihB =>
      intro ρ
      have h := EnvironmentEval.denote_pi_value E H ν ρ A B u v
      have hl := NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_graph E H ν ρ A B u)
      rw [hl, hu, hv, TowerSourcePi.imaxLevel_some, NeutralCodes.valueEq_eq (ihA ρ),
        legalGraph_congr (G := fun x => image (rcons x ρ) cB)
          (fun x => by
            show ValueEq _ (image (rcons x ρ) cB)
            rw [rcons_eq_cons]
            exact ihB (EnvI.cons x ρ))] at h
      exact h

theorem reads_kind {ν : Valuation} {κ : List (Option Nat)} {A : ExprA} {k : Nat}
    {c : GCode k} (h : Reads ν κ A c) : kindOf ν A = kindOfCode c := by
  cases h with
  | sort hl => exact hl
  | bvar _ => rfl
  | pi _ _ _ _ => rfl

/-- A read type is kinded by its kind context. -/
theorem reads_kinded {ν : Valuation} {κ : List (Option Nat)} {e : ExprA} {k : Nat}
    {c : GCode k} (h : Reads ν κ e c) : Kinded κ c := by
  induction h with
  | sort _ => trivial
  | bvar hk => exact hk
  | pi _ _ hA _ ihA ihB =>
      refine ⟨ihA, ?_⟩
      rw [← reads_kind hA]
      exact ihB

/-- A read type is closed below its kind context. -/
theorem reads_closed {ν : Valuation} {κ : List (Option Nat)} {e : ExprA} {k : Nat}
    {c : GCode k} (h : Reads ν κ e c) : ClosedAt κ.length c :=
  kinded_closed c κ (reads_kinded h)

/-- Every closed source type of the fragment is a code of the Girard code
system, at its level, with the Girard relation of its code. -/
theorem reads_code (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) {ν : Valuation}
    {e : ExprA} {k : Nat} {c : GCode k} (h : Reads ν [] e c) (ρ : EnvI) :
    codeSystem.Code (some k) (EnvironmentEval.denote E H ν ρ e) (El σ0 ρ0 c) := by
  have hc : ClosedAt 0 c := reads_closed h
  have himg : ValueEq (EnvironmentEval.denote E H ν ρ e) (image σ0 c) := by
    rw [image_closed c 0 σ0 ρ hc (fun _ hi => absurd hi (Nat.not_lt_zero _))]
    exact reads_image E H h ρ
  exact family.ok_code (c := c) (reads_kinded h) himg

/-- The impredicative identity type is read to its Girard code. -/
theorem reads_identityType (ν : Valuation) :
    Reads ν [] ImpredicativePiProbe.identityType identityCode :=
  .pi rfl rfl (.sort rfl) (.pi rfl rfl (.bvar rfl) (.bvar rfl))

end Rcic.Declarative.Ann.LR3.CandidateReader
