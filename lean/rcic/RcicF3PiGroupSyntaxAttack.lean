import rcic.RcicF3PiGroupSyntax
import rcic.RcicF3PiTupleExactAttack
import rcic.RcicF3RoleAttacks
/-! Whole-admission list pins and inhabited parameter-prefix normalization.
The W and Acc pins use actual typed admission descriptors. Hidden parameter
checks below concern a typed expression and its semantic parameter value,
not an entire new admission derivation. `closure_claim = 0`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Rcic.F3.PSet.PiGroupSyntaxAttack
open Rcic.Declarative PiValueRule PiValueExtract PiGroupSyntax PiRawCtorAttack

kernel_rfl_theorem w_slots :
  constructors PendAW.recA PendAW.recIota.fuelAt =
    [⟨[.plain (.sort (.succ .zero))], [.bvar 0]⟩,
     ⟨[.plain (.sort (.succ .zero)), .recursive [.bvar 0] [.bvar 1]], [.bvar 1]⟩]

kernel_rfl_theorem acc_slots :
  constructors Rcic.Declarative.Ann.accPGroupAdm Rcic.Declarative.Ann.accPIotaClause.fuelAt =
    [⟨[.plain (.sort .zero), .recursive RoleAttacks.accDomains [.bvar 1]], [.bvar 1]⟩]

/-- The parameter prefix is a genuinely typed beta expression containing the
family constant in a discarded argument; its free scan cannot be assumed away. -/
def hiddenParam (f : Nat) : Expr Nat :=
  .app (.lam paramMember.mtype (.sort .zero)) (.const f [])

def hiddenParamTy (f : Nat) (Γ : LCtx) :
    HasTyT (paramEnv f) 0 Γ (hiddenParam f) (.sort (.succ .zero)) :=
  .app Γ _ _ _ _
    (.lam Γ _ _ _ _
      (.pi Γ _ _ _ _ (.sort Γ .zero) (.sort _ .zero)) (.sort _ .zero))
    (.const Γ f [] paramMember (members_extend_eq _ _ _) rfl rfl)

def hiddenParamConv (f : Nat) (Γ : LCtx) :
    ConvT (paramEnv f) 0 Γ (hiddenParam f) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ _ _ _ _ _
    (.pi Γ _ _ _ _ (.sort Γ .zero) (.sort _ .zero)) (.sort _ .zero)
    (.const Γ f [] paramMember (members_extend_eq _ _ _) rfl rfl)

/-- Elementary bound and scan computation, universally over numeric labels. -/
theorem hidden_checks (f : Nat) (Γ : LCtx) :
    LOKt (σOf []) 4 (fun _ => 0) (hiddenParamTy f Γ) ∧
      LOKc (σOf []) 4 (fun _ => 0) (hiddenParamConv f Γ) ∧
      occursConst f (hiddenParam f) = true ∧ hiddenParam f ≠ .sort .zero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hiddenParamTy, LOKt, LevelsOK, evalTotal]
  · simp [hiddenParamConv, LOKc, LOKt, LevelsOK, evalTotal]
  · simp [hiddenParam, occursConst]
  · exact Expr.noConfusion

/-- Typed hidden parameters retain an actual semantic inhabitant. This probe
prevents promoting raw parameter scans to an additional universal wall. -/
theorem hidden_inhabited (P : Premises4) (f : Nat) :
    let M := mkM P (paramTable P f)
    TelFits M (σOf []) [hiddenParam f] ρ0 [tyv pempty] ∧
      occursConst f (hiddenParam f) = true := by
  let M := mkM P (paramTable P f)
  have hE := paramSound P f (σOf []) (fun _ => 0)
  have hc := sound_conv (P.good _ rfl) hE (hiddenParamConv f [])
    (hidden_checks f []).2.1 ρ0 True.intro
  have hx := tyv_pempty_mem_sort P (paramTable P f) (σOf []) ρ0 .zero
  exact ⟨⟨mem_congr_right (ed_congr M hc.1.symm) hx, True.intro⟩,
    (hidden_checks f []).2.2.1⟩

/-- The new prefix bridge is exercised on original, beta and let fields,
with original typing and an actual fitting tuple paid internally at every label. -/
theorem parameter_prefix (P : Premises4) (f : Nat) :
    let M := mkM P (paramTable P f)
    ∀ T ∈ [paramField f, PiSizedAttack.param_beta f, PiSizedAttack.param_zeta f],
      (∀ xs, TelFits M (σOf [])
        (params ++ [fieldExpr f [] (.recursive [.bvar 0] [.bvar 1])]) ρ0 xs ↔
          TelFits M (σOf []) (params ++ [T]) ρ0 xs) ∧
      TelFits M (σOf []) (params ++ [T]) ρ0 [tyv pempty, pempty] := by
  let M := mkM P (paramTable P f)
  obtain ⟨_, _, _, hb, _⟩ := param_checks f
  have hE := paramSound P f (σOf []) (fun _ => 0)
  have hR := PiTupleExactAttack.param_regular P f (σOf []) (fun _ => 0)
  have go : ∀ T,
      T ∈ [paramField f, PiSizedAttack.param_beta f, PiSizedAttack.param_zeta f] →
      ∀ (d : HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] T (.sort (.imax .zero .zero))),
      LOKt (σOf []) 4 (fun _ => 0) d →
      ∀ xs, TelFits M (σOf [])
        (params ++ [fieldExpr f [] (.recursive [.bvar 0] [.bvar 1])]) ρ0 xs ↔
          TelFits M (σOf []) (params ++ [T]) ρ0 xs := by
    intro T hT d hd xs
    have hv : Views (paramEnv f) 8 f 0 1 [T] [.recursive [.bvar 0] [.bvar 1]] := by
      have hf := PiTupleExactAttack.param_views f T hT
      cases hf with
      | cons _ ht => exact ht
    have hdc : LOKt (σOf []) 4 (fun _ => 0) (PiTupleExactAttack.ctor_typed f T d) := by
      simpa [PiTupleExactAttack.ctor_typed, LOKt, evalTotal, LevelsOK] using hd
    exact prefix_fits_iff P (paramTable P f) (σOf []) (fun _ => 0) hE hb hR hv
      params (PiTupleExactAttack.ctor_typed f T d) hdc ρ0 xs True.intro
  dsimp only
  intro T hT
  refine ⟨?_, (PiTupleExactAttack.param_exact P f T hT).2.1⟩
  have ht := hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact go _ hT (PiSizedAttack.param_field_typed f) (by
      simp [PiSizedAttack.param_field_typed, LOKt, LevelsOK, evalTotal])
  · exact go _ hT (PiSizedAttack.param_beta_typed f) (by
      simp [PiSizedAttack.param_beta_typed, PiSizedAttack.param_field_typed, LOKt, LevelsOK, evalTotal])
  · exact go _ hT (PiSizedAttack.param_zeta_typed f) (by
      simp [PiSizedAttack.param_zeta_typed, PiSizedAttack.param_field_typed, LOKt, LevelsOK, evalTotal])

end Rcic.F3.PSet.PiGroupSyntaxAttack
