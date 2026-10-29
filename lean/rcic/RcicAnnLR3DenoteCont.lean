import rcic.RcicAnnLR3LevelGirard

/-!
# Joint continuity of the evaluator

`approxI_cont`: every observation of the raw evaluator is determined by
finitely many (slot, observation) pairs of the environment. Hence
`denote_cont`: the denotation of every annotated expression, for every
environment, family syntax and valuation, is jointly continuous in the raw
environment (`LevelGirard.JointCont`). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.DenoteCont

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel
open CandidateTowerProbe (REnv rcons)
open LevelGirard (JointCont combine_reqs shiftReqs shiftReqs_sound shiftReqs_back)

theorem cons_eq_rcons (S : CptI → Prop) (ρ : EnvI) : EnvI.cons S ρ = rcons S ρ := by
  funext i
  cases i <;> rfl

/-- A derivation under one binder, with the bound slot fixed. -/
theorem binder_reqs {ρ : EnvI} {B : Expr Nat} {s : List CptI × CptI}
    (h : ∃ S : List (Nat × CptI), (∀ p ∈ S, EnvI.cons (demand s.1) ρ p.1 p.2) ∧
      ∀ ρ' : EnvI, (∀ p ∈ S, ρ' p.1 p.2) → ApproxI ρ' B s.2) :
    ∃ S : List (Nat × CptI), (∀ p ∈ S, ρ p.1 p.2) ∧
      ∀ ρ' : EnvI, (∀ p ∈ S, ρ' p.1 p.2) → ApproxI (EnvI.cons (demand s.1) ρ') B s.2 := by
  obtain ⟨S, hS, kS⟩ := h
  rw [cons_eq_rcons] at hS
  refine ⟨shiftReqs S, shiftReqs_sound hS, fun ρ' h' => kS _ ?_⟩
  rw [cons_eq_rcons]
  exact shiftReqs_back (fun u hu => hS _ hu) h'

/-- Every observation of the raw evaluator depends on finitely many
observations of the environment. -/
theorem approxI_cont {ρ : EnvI} {e : Expr Nat} {c : CptI} (h : ApproxI ρ e c) :
    ∃ S : List (Nat × CptI), (∀ p ∈ S, ρ p.1 p.2) ∧
      ∀ ρ' : EnvI, (∀ p ∈ S, ρ' p.1 p.2) → ApproxI ρ' e c := by
  induction h with
  | bot => exact ⟨[], by simp, fun _ _ => .bot _ _⟩
  | @bvar ρ i c hi => exact ⟨[(i, c)], by simpa using hi, fun ρ' h => .bvar (h (i, c) (by simp))⟩
  | sort => exact ⟨[], by simp, fun _ _ => .sort _ _⟩
  | @pi ρ A B a f _ _ ihA ihB =>
      obtain ⟨SA, hSA, kA⟩ := ihA
      obtain ⟨SB, hSB, kB⟩ := combine_reqs ρ
        (fun ρ' (s : List CptI × CptI) => ApproxI (EnvI.cons (demand s.1) ρ') B s.2) f
        (fun s hs => binder_reqs (ihB s hs))
      refine ⟨SA ++ SB, fun p hp => ?_, fun ρ' h' => .pi (kA ρ' (fun p hp => h' p
        (List.mem_append_left _ hp))) (kB ρ' (fun p hp => h' p (List.mem_append_right _ hp)))⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact hSA p hp
      · exact hSB p hp
  | @lam ρ A b f _ ihb =>
      obtain ⟨SB, hSB, kB⟩ := combine_reqs ρ
        (fun ρ' (s : List CptI × CptI) => ApproxI (EnvI.cons (demand s.1) ρ') b s.2) f
        (fun s hs => binder_reqs (ihb s hs))
      exact ⟨SB, hSB, fun ρ' h' => .lam (kB ρ' h')⟩
  | @app ρ f a g s _ hs _ ihf iha =>
      obtain ⟨Sf, hSf, kf⟩ := ihf
      obtain ⟨Sa, hSa, ka⟩ := combine_reqs ρ (fun ρ' (u : CptI) => ApproxI ρ' a u) s.1
        (fun u hu => iha u hu)
      refine ⟨Sf ++ Sa, fun p hp => ?_, fun ρ' h' => .app (kf ρ' (fun p hp => h' p
        (List.mem_append_left _ hp))) hs (ka ρ' (fun p hp => h' p (List.mem_append_right _ hp)))⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact hSf p hp
      · exact hSa p hp
  | const => exact ⟨[], by simp, fun _ _ => .const _ _ _⟩
  | appSpine _ _ ihf iha =>
      obtain ⟨Sf, hSf, kf⟩ := ihf
      obtain ⟨Sa, hSa, ka⟩ := iha
      refine ⟨Sf ++ Sa, fun p hp => ?_, fun ρ' h' => .appSpine (kf ρ' (fun p hp => h' p
        (List.mem_append_left _ hp))) (ka ρ' (fun p hp => h' p (List.mem_append_right _ hp)))⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact hSf p hp
      · exact hSa p hp
  | letE _ ih =>
      obtain ⟨S, hS, k⟩ := ih
      exact ⟨S, hS, fun ρ' h' => .letE (k ρ' h')⟩
  | lit h _ => exact ⟨[], by simp, fun ρ' _ => .lit (approxI_natExpand_env _ ρ' _ h)⟩

/-- The raw evaluator's denotation is jointly continuous. -/
theorem denI_cont (t : Expr Nat) : JointCont (fun σ => denI σ t) := fun σ _ hd =>
  approxI_cont hd

/-- The environment evaluator's denotation is jointly continuous. -/
theorem denote_cont (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (e : ExprA) : JointCont (fun σ => EnvironmentEval.denote E F ν σ e) := by
  rintro σ d ⟨t, ht, hd⟩
  obtain ⟨S, hS, k⟩ := approxI_cont hd
  exact ⟨S, hS, fun σ' h' => ⟨t, ht, k σ' h'⟩⟩

end Rcic.Declarative.Ann.LR3.DenoteCont
