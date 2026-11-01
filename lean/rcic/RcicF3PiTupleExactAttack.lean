import rcic.RcicF3PiTupleExact
import rcic.RcicF3PiSizedAttack
/-! Inhabited whole-constructor normalization attacks. Raw, beta and let
presentations retain a dependent family parameter and work at every label.
These are constructor components, not a universal group proof. `closure_claim = 0`. -/
set_option autoImplicit false
universe u
namespace Rcic.F3.PSet.PiTupleExactAttack
open Rcic.Declarative PiValueRule PiValueExtract PiRawCtorAttack PiSizedAttack

/-- Elementary typing-rule assembly for the original constructor, retaining
its original possibly-hidden recursive field. -/
def ctor_typed (f : Nat) (T : Expr Nat)
    (d : HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] T (.sort (.imax .zero .zero))) :
    HasTyT (paramEnv f) 0 [] (policyPi (params ++ [T]) (.app (.const f []) (.bvar 1)))
      (.sort (.imax (.succ .zero) (.imax (.imax .zero .zero) .zero))) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ (.imax .zero .zero) _ .zero d
      (.app _ _ _ (.sort .zero) (.sort .zero)
        (.const _ f [] paramMember (members_extend_eq _ _ _) rfl rfl)
        (.bvar _ 1 (.sort .zero) rfl)))

/-- Elementary body-less lookup: this fixture has no transparent-body debt. -/
theorem param_regular (P : Premises4) (f : Nat) (σ K : Nat → Nat) :
    PiHereditary.BodiesRegular (mkM P (paramTable P f)) σ K (paramEnv f) := by
  intro r m b ls hm hb
  by_cases hr : r = f
  · subst r
    rw [show (paramEnv f).members f = some paramMember from members_extend_eq _ _ _] at hm
    cases hm
    cases hb
  · rw [show (paramEnv f).members r = none from members_extend_ne emptyEnv f paramMember r hr] at hm
    cases hm

/-- Executable reads at the actual extraction fuel; this is an elementary scan pin. -/
theorem param_views (f : Nat) :
    ∀ T ∈ [paramField f, param_beta f, param_zeta f],
      Views (paramEnv f) 8 f 0 1 (params ++ [T]) paramCtor.fields := by
  intro T hT
  apply PiRawCtor.prefix_views params
    (by intro A hA; have he := List.mem_singleton.mp hA; subst A; rfl)
  refine .cons ?_ .nil
  change piTelescopeFuel (paramEnv f) 7 T =
      some ([.bvar 0], foldApps (.const f []) [.bvar 1]) ∧ _
  refine ⟨?_, by simp [occursConst]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  all_goals simp [piTelescopeFuel, whnfFuel, appsSpine, transparentBody,
    paramEnv, members_extend_eq, paramMember, transparent, paramField,
    param_beta, param_zeta, foldApps, instantiate0, instantiate, lift]

/-- Both tuple directions, actual tuple inhabitation, and the raw constructor
predicate equation all hold together; no normalized typing premise is supplied.
The result reads the original parameter after the recursive field. -/
theorem param_exact (P : Premises4) (f : Nat) :
    let M := mkM P (paramTable P f)
    ∀ T ∈ [paramField f, param_beta f, param_zeta f],
      (∀ xs, TelFits M (σOf [])
        (paramCtor.fields.map (fieldExpr f [])) ρ0 xs ↔
          TelFits M (σOf []) (params ++ [T]) ρ0 xs) ∧
      TelFits M (σOf []) (params ++ [T]) ρ0 [tyv pempty, pempty] ∧
      (∀ i, paramPred P [] i ↔ ∃ xs, TelFits M (σOf []) (params ++ [T]) ρ0 xs ∧
        PiIndex.read (mkM P PiValueRuleAttack.emptyBase) (σOf []) [.bvar 1] (push xs ρ0) = i) := by
  let M := mkM P (paramTable P f)
  obtain ⟨_, _, _, hb, _⟩ := param_checks f
  have hE := paramSound P f (σOf []) (fun _ => 0)
  have hR := param_regular P f (σOf []) (fun _ => 0)
  have hn : TelFits M (σOf []) (paramCtor.fields.map (fieldExpr f [])) ρ0
      [tyv pempty, pempty] := (param_inhabited P f).1
  have go : ∀ T, T ∈ [paramField f, param_beta f, param_zeta f] →
      ∀ (d : HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] T (.sort (.imax .zero .zero))),
      LOKt (σOf []) 4 (fun _ => 0) d →
      (∀ xs, TelFits M (σOf []) (paramCtor.fields.map (fieldExpr f [])) ρ0 xs ↔
        TelFits M (σOf []) (params ++ [T]) ρ0 xs) ∧
      TelFits M (σOf []) (params ++ [T]) ρ0 [tyv pempty, pempty] ∧
      (∀ i, paramPred P [] i ↔ ∃ xs, TelFits M (σOf []) (params ++ [T]) ρ0 xs ∧
        PiIndex.read (mkM P PiValueRuleAttack.emptyBase) (σOf []) [.bvar 1] (push xs ρ0) = i) := by
    intro T hT d hd
    let dc := ctor_typed f T d
    have hdc : LOKt (σOf []) 4 (fun _ => 0) dc := by
      simpa [dc, ctor_typed, LOKt, evalTotal, LevelsOK] using hd
    have hv := param_views f T hT
    have ht := fun xs => PiTupleExact.fits_iff P (paramTable P f) (σOf []) (fun _ => 0)
      hE hb hR hv dc hdc ρ0 xs True.intro
    refine ⟨ht, (ht _).mp hn, ?_⟩
    have hc : ∀ c : Fin ([paramCtor].length), c = ⟨0, Nat.zero_lt_succ 0⟩ :=
      fun c => Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ c.isLt))
    intro i
    have he := PiTupleExact.predicate_equation P PiValueRuleAttack.emptyBase f params [paramCtor] []
      (fun _ => params ++ [T]) (by intro c; rw [hc c]; exact hv) (fun _ => 0) hE hb hR
      (fun _ => .imax (.succ .zero) (.imax (.imax .zero .zero) .zero))
      (by intro c; rw [hc c]; exact dc) (by intro c; rw [hc c]; exact hdc) i
    constructor
    · intro hi
      obtain ⟨c, xs, hx, hr⟩ := he.mp hi
      rw [hc c] at hr
      exact ⟨xs, hx, hr⟩
    · rintro ⟨xs, hx, hr⟩
      exact he.mpr ⟨⟨0, Nat.zero_lt_succ 0⟩, xs, hx, hr⟩
  dsimp only
  intro T hT
  have ht := hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact go _ hT (param_field_typed f) (by simp [param_field_typed, LOKt, LevelsOK, evalTotal])
  · exact go _ hT (param_beta_typed f) (by
      simp [param_beta_typed, param_field_typed, LOKt, LevelsOK, evalTotal])
  · exact go _ hT (param_zeta_typed f) (by
      simp [param_zeta_typed, param_field_typed, LOKt, LevelsOK, evalTotal])
/-- Without original typing the reverse tuple implication is false, even
though the malformed raw field has a nonempty root. -/
theorem untyped_tuple_refused (M : Interp.{u}) (σ : Nat → Nat) :
    ∃ xs, TelFits M σ [policyPi [.bvar 0] (.bvar 3)] PiHereditaryAttack.badAssignment xs ∧
      ¬ TelFits M σ [PiHereditaryAttack.badType] PiHereditaryAttack.badAssignment xs := by
  obtain ⟨x, hx, hn⟩ := PiHereditaryAttack.bad_normalization_changes_members M σ
  exact ⟨[x], ⟨hx, True.intro⟩, fun h => hn h.1⟩
end Rcic.F3.PSet.PiTupleExactAttack
