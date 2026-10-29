import rcic.RcicAnnLR3LevelSubstitution
import rcic.RcicAnnLR3CandidateReader

/-!
# Reading source types into level codes

`ReadsL E H ν κ e c` reads a source type `e` into a level code `c`, for the
evaluator `EnvironmentEval.denote E H ν`. Sorts read to universes, bound
variables to variable codes of their kind, and products to `pi0` (codomain
of level zero) or `pi c` (positive codomain, with `imax a (b + 1) = c + 1`).
Any other proposition reads opaquely as `prop (denote · e)`, given that its
image function is well formed and depends only on the context's slots.

`reads_image`: reading is image-exact in every raw environment.
`reads_kinded`, `reads_closed`: read types are kinded and closed below the
kind context. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelReader

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe (REnv CEnv rcons ccons)
open LevelGirard LevelSubstitution

/-- The kind a product binder gives its variable. -/
def kindOfS (ν : Valuation) : ExprA → Option Nat
  | .sort l => eval ν l
  | _ => none

inductive ReadsL (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    List (Option Nat) → ExprA → {k : Nat} → LCode k → Prop
  | sort {κ : List (Option Nat)} {l : Level} {k : Nat} (h : eval ν l = some k) :
      ReadsL E H ν κ (.sort l) (.univ k)
  | bvar {κ : List (Option Nat)} {i k : Nat} (h : κ[i]? = some (some k)) :
      ReadsL E H ν κ (.bvar i) (varCode k i)
  | pi0 {κ : List (Option Nat)} {A B : ExprA} {u v : Level} {a : Nat} {cA : LCode a}
      {cB : LCode 0} (hu : eval ν u = some a) (hv : eval ν v = some 0)
      (hA : ReadsL E H ν κ A cA) (hB : ReadsL E H ν (kindOfS ν A :: κ) B cB) :
      ReadsL E H ν κ (.pi A u B v) (.pi0 cA cB)
  | pi {κ : List (Option Nat)} {A B : ExprA} {u v : Level} {a b c : Nat} {cA : LCode a}
      {cB : LCode (b + 1)} (hu : eval ν u = some a) (hv : eval ν v = some (b + 1))
      (hc : imaxN a (b + 1) = c + 1)
      (hA : ReadsL E H ν κ A cA) (hB : ReadsL E H ν (kindOfS ν A :: κ) B cB) :
      ReadsL E H ν κ (.pi A u B v) (.pi c cA cB)
  | prop {κ : List (Option Nat)} {e : ExprA}
      (h : PropImg (fun σ => EnvironmentEval.denote E H ν σ e))
      (hcl : ∀ σ σ' : REnv, (∀ i, i < κ.length → σ i = σ' i) →
        EnvironmentEval.denote E H ν σ e = EnvironmentEval.denote E H ν σ' e) :
      ReadsL E H ν κ e (.prop (fun σ => EnvironmentEval.denote E H ν σ e))

variable {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} {ν : Valuation}

theorem sort_not_prop {l : Level}
    (h : PropImg (fun σ => EnvironmentEval.denote E H ν σ (.sort l))) : False := by
  have hs : EnvironmentEval.denote E H ν (fun _ => bottom) (.sort l) = universeValue (eval ν l) :=
    (EnvironmentEval.annSemantics LevelGirardSystem.codeSystem E H).sort_image ν [] _ l
  have hl := h.level (fun _ => bottom)
  have hd := h.defined (fun _ => bottom)
  rw [hs] at hl hd
  have := sortMember_unique hl (sort_member _ (eval ν l)) hd
  cases he : eval ν l with
  | none => rw [he] at this; exact Option.noConfusion this
  | some k => rw [he] at this; exact Nat.succ_ne_zero k (Option.some.inj this).symm

theorem reads_kind {κ : List (Option Nat)} {A : ExprA} {k : Nat} {c : LCode k}
    (h : ReadsL E H ν κ A c) : kindOfS ν A = kindOf c := by
  cases h with
  | sort hl => exact hl
  | bvar _ => cases k <;> rfl
  | pi0 _ _ _ _ => rfl
  | pi _ _ _ _ _ => rfl
  | prop hp _ =>
      cases A with
      | sort l => exact (sort_not_prop hp).elim
      | _ => rfl

theorem reads_kinded {κ : List (Option Nat)} {e : ExprA} {k : Nat} {c : LCode k}
    (h : ReadsL E H ν κ e c) : Kinded κ c := by
  induction h with
  | sort _ => trivial
  | bvar hk => exact kinded_varCode _ _ hk
  | pi0 _ _ hA _ ihA ihB =>
      refine ⟨ihA, ?_⟩
      rw [← reads_kind hA]
      exact ihB
  | pi _ _ _ hA _ ihA ihB =>
      refine ⟨ihA, ?_⟩
      rw [← reads_kind hA]
      exact ihB
  | prop hp _ => exact hp

theorem reads_closed {κ : List (Option Nat)} {e : ExprA} {k : Nat} {c : LCode k}
    (h : ReadsL E H ν κ e c) : ClosedAt κ.length c := by
  induction h with
  | sort _ => trivial
  | @bvar κ i k hk =>
      have hi := CandidateCodeSystem.lt_of_getElem? κ i _ hk
      cases k <;> exact hi
  | pi0 _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | pi _ _ _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | prop _ hcl => exact hcl

/-- Reading is image-exact in every raw environment. -/
theorem reads_image {κ : List (Option Nat)} {e : ExprA} {k : Nat} {c : LCode k}
    (h : ReadsL E H ν κ e c) :
    ∀ ρ : EnvI, ValueEq (EnvironmentEval.denote E H ν ρ e) (image ρ c) := by
  induction h with
  | @sort κ l k hl =>
      intro ρ
      have hs : EnvironmentEval.denote E H ν ρ (.sort l) = universeValue (eval ν l) :=
        (EnvironmentEval.annSemantics LevelGirardSystem.codeSystem E H).sort_image ν [] ρ l
      rw [hs, hl]
      exact ValueEq.refl _
  | @bvar κ i k _ =>
      intro ρ
      rw [image_varCode]
      exact CandidateCodeSystem.bvar_image E H ν ρ i
  | @pi0 κ A B u v a cA cB hu hv _ _ ihA ihB =>
      intro ρ
      have h := EnvironmentEval.denote_pi_value E H ν ρ A B u v
      have hl := NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_graph E H ν ρ A B u)
      rw [hl, hu, hv, TowerSourcePi.imaxLevel_some, NeutralCodes.valueEq_eq (ihA ρ),
        CandidateCodeSystem.legalGraph_congr (G := fun x => image (rcons x ρ) cB)
          (fun x => by
            show ValueEq _ (image (rcons x ρ) cB)
            rw [CandidateReader.rcons_eq_cons]
            exact ihB (EnvI.cons x ρ))] at h
      exact h
  | @pi κ A B u v a b c cA cB hu hv hc _ _ ihA ihB =>
      intro ρ
      have h := EnvironmentEval.denote_pi_value E H ν ρ A B u v
      have hl := NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_graph E H ν ρ A B u)
      rw [hl, hu, hv, TowerSourcePi.imaxLevel_some, hc, NeutralCodes.valueEq_eq (ihA ρ),
        CandidateCodeSystem.legalGraph_congr (G := fun x => image (rcons x ρ) cB)
          (fun x => by
            show ValueEq _ (image (rcons x ρ) cB)
            rw [CandidateReader.rcons_eq_cons]
            exact ihB (EnvI.cons x ρ))] at h
      exact h
  | prop _ _ => intro ρ; exact ValueEq.refl _

end Rcic.Declarative.Ann.LR3.LevelReader
