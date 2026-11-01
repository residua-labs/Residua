import rcic.RcicF3PiCanonicalParams
import rcic.RcicF3PiGroupSyntaxAttack
/-! Original-type constructor membership with a family-containing parameter
mirror, actual tuple inhabitation and raw/beta/let recursive fields. All
ordinary environment and bound premises are paid at every numeric family
label. This is a constructor component, not a new whole group admission.
Its recursive domain is empty; nonempty W fixtures remain separate.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiCanonicalParamsAttack
open Rcic.Declarative PiValueRule PiValueExtract PiRawCtorAttack PiGroupSyntaxAttack

/-- Elementary explicit conversion at a local variable. -/
def hiddenBvarTy (f i : Nat) (Γ : LCtx)
    (h : lookupType Γ i = some (hiddenParam f)) :
    HasTyT (paramEnv f) 0 Γ (.bvar i) (.sort .zero) :=
  .conv Γ _ _ _ _ (.bvar Γ i (hiddenParam f) h) (hiddenParamConv f Γ)

/-- Actual field typing under the original hidden parameter domain. -/
def hiddenFieldTy (f : Nat) :
    HasTyT (paramEnv f) 0 [.assumption (hiddenParam f)] (paramField f)
      (.sort (.imax .zero .zero)) :=
  .pi _ _ .zero _ .zero (hiddenBvarTy f 0 _ rfl)
    (.app _ _ _ (.sort .zero) (.sort .zero)
      (.const _ f [] paramMember (members_extend_eq _ _ _) rfl rfl)
      (hiddenBvarTy f 1 _ rfl))

/-- Elementary typed beta wrapper in that same original context. -/
def hiddenBetaTy (f : Nat) :
    HasTyT (paramEnv f) 0 [.assumption (hiddenParam f)] (PiSizedAttack.param_beta f)
      (.sort (.imax .zero .zero)) :=
  .app _ _ _ (.sort (.imax .zero .zero)) (.sort (.imax .zero .zero))
    (.lam _ _ _ _ _ (.sort _ (.imax .zero .zero)) (.bvar _ 0 _ rfl)) (hiddenFieldTy f)

/-- Elementary typed let wrapper in that same original context. -/
def hiddenZetaTy (f : Nat) :
    HasTyT (paramEnv f) 0 [.assumption (hiddenParam f)] (PiSizedAttack.param_zeta f)
      (.sort (.imax .zero .zero)) :=
  .letE _ _ _ _ _ _ (.sort _ (.imax .zero .zero)) (hiddenFieldTy f) (.bvar _ 0 _ rfl)

/-- Whole stored constructor typing retains the hidden parameter syntax. -/
def hiddenCtorTy (f : Nat) (T : Expr Nat)
    (d : HasTyT (paramEnv f) 0 [.assumption (hiddenParam f)] T (.sort (.imax .zero .zero))) :
    HasTyT (paramEnv f) 0 [] (policyPi ([hiddenParam f] ++ [T])
      (.app (.const f []) (.bvar 1)))
      (.sort (.imax (.succ .zero) (.imax (.imax .zero .zero) .zero))) :=
  .pi [] _ _ _ _ (hiddenParamTy f [])
    (.pi _ _ (.imax .zero .zero) _ .zero d
      (.app _ _ _ (.sort .zero) (.sort .zero)
        (.const _ f [] paramMember (members_extend_eq _ _ _) rfl rfl)
        (hiddenBvarTy f 1 _ rfl)))

/-- A family-containing own parameter is permitted and inhabited. Every
premise of the new canonical transport and original-type membership is paid
for all three field presentations and every numeric family label. -/
theorem hidden_actual (P : Premises4) (f : Nat) :
    let M := mkM P (paramTable P f)
    occursConst f (hiddenParam f) = true ∧
    ∀ T ∈ [paramField f, PiSizedAttack.param_beta f, PiSizedAttack.param_zeta f],
      TelFits M (σOf []) ([hiddenParam f] ++ [T]) ρ0 [tyv pempty, pempty] ∧
      TelFits M (σOf []) (params ++ [paramField f]) ρ0 [tyv pempty, pempty] ∧
      let C := policyPi ([hiddenParam f] ++ [T]) (.app (.const f []) (.bvar 1))
      piLam M (σOf []) (fun _ => pempty) ρ0 C ∈ Ed M (den M (σOf []) ρ0 C) := by
  let M := mkM P (paramTable P f)
  obtain ⟨_, _, _, hb, _⟩ := param_checks f
  have hE := paramSound P f (σOf []) (fun _ => 0)
  have hR := PiTupleExactAttack.param_regular P f (σOf []) (fun _ => 0)
  have hn : TelFits M (σOf []) ([hiddenParam f] ++ [paramField f]) ρ0
      [tyv pempty, pempty] :=
    ⟨(hidden_inhabited P f).1.1, (param_inhabited P f).1.2⟩
  have hfree : ∀ A ∈ params, occursConst f A = false := by
    intro A hA
    have he := List.mem_singleton.mp hA
    subst A
    rfl
  have hresult : ∀ A ∈ (policyParameterLocals 1 1 ++ [] : List (Expr Nat)),
      occursConst f A = false := by
    intro A hA
    have he := List.mem_singleton.mp hA
    subst A
    rfl
  have go : ∀ T, T ∈ [paramField f, PiSizedAttack.param_beta f, PiSizedAttack.param_zeta f] →
      ∀ (d : HasTyT (paramEnv f) 0 [.assumption (hiddenParam f)] T
        (.sort (.imax .zero .zero))), LOKt (σOf []) 4 (fun _ => 0) d →
      TelFits M (σOf []) ([hiddenParam f] ++ [T]) ρ0 [tyv pempty, pempty] ∧
      TelFits M (σOf []) (params ++ [paramField f]) ρ0 [tyv pempty, pempty] ∧
      let C := policyPi ([hiddenParam f] ++ [T]) (.app (.const f []) (.bvar 1))
      piLam M (σOf []) (fun _ => pempty) ρ0 C ∈ Ed M (den M (σOf []) ρ0 C) := by
    intro T hT d hd
    let dc := hiddenCtorTy f T d
    have hdc : LOKt (σOf []) 4 (fun _ => 0) dc := by
      simpa [dc, hiddenCtorTy, hiddenBvarTy, hiddenParamTy, hiddenParamConv,
        LOKt, LOKc, LevelsOK, evalTotal] using hd
    have hv : Views (paramEnv f) 8 f 0 1 [T] [.recursive [.bvar 0] [.bvar 1]] := by
      have hv := PiTupleExactAttack.param_views f T hT
      cases hv with
      | cons _ hv => exact hv
    have ht := (PiGroupSyntax.prefix_fits_iff P (paramTable P f) (σOf []) (fun _ => 0)
      hE hb hR hv [hiddenParam f] dc hdc ρ0 [tyv pempty, pempty] True.intro).mp hn
    refine ⟨ht, ?_, ?_⟩
    · exact PiCanonicalParams.canonical_tuple P PiValueRuleAttack.emptyBase f (paramPred P)
        params [] [hiddenParam f] [T] [] [] rfl rfl hfree (fun _ => 0)
        hE hb hR hv dc hdc [tyv pempty, pempty] ht
    · exact PiCanonicalParams.constructor_mem P PiValueRuleAttack.emptyBase f params [] [paramCtor] []
        ⟨0, Nat.zero_lt_succ 0⟩ [hiddenParam f] [T] [] [.recursive [.bvar 0] [.bvar 1]]
        rfl rfl hfree hv rfl rfl hresult (fun _ => 0) hE hb hR dc hdc
  refine ⟨(hidden_checks f []).2.2.1, ?_⟩
  intro T hT
  have ht := hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact go _ hT (hiddenFieldTy f) (by
      simp [hiddenFieldTy, hiddenBvarTy, hiddenParamConv, LOKt, LOKc, LevelsOK, evalTotal])
  · exact go _ hT (hiddenBetaTy f) (by
      simp [hiddenBetaTy, hiddenFieldTy, hiddenBvarTy, hiddenParamConv, LOKt, LOKc, LevelsOK, evalTotal])
  · exact go _ hT (hiddenZetaTy f) (by
      simp [hiddenZetaTy, hiddenFieldTy, hiddenBvarTy, hiddenParamConv, LOKt, LOKc, LevelsOK, evalTotal])

end Rcic.F3.PSet.PiCanonicalParamsAttack
