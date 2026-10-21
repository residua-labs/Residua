import rcic.RcicNativeTypedModelCovXExpansion
import rcic.RcicNativeTypedModelCovXEtaControl

/-!
# The remaining general eta input is compact-action factorization

An eta lambda may have a compact which its unexpanded head never observes.
The required model input therefore factors each action through an actually
observed head compact, which may differ from action to action. It contains no recursive relation or Fundamental
conclusion. The full input is supplied for native successor, including an
actual non-bottom lambda observation with an empty-demand non-bottom row.

The general eta adapter below consumes the function child's relation. Its
use at a different compact is still the same genuine function subderivation;
there is no induction on a newly constructed application derivation.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovXAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Every finite application action of `c` is also an action of `d`.
This compares only the already landed compact application relation. -/
def CovXCompactActionCovers (E : ResolvedEnv) (d c : CptT) : Prop :=
  ∀ ds out, CovXCompactAction E c ds out → CovXCompactAction E d ds out

/-- The model-only general eta residual: an actual eta observation has a
Pi gate and each action is covered by an actually observed head compact.
No relatedness, readback, typing derivation or Fundamental motive occurs. -/
def CovXEtaActionFactorAt (C : CovTyping E) (M : CtxModelT E)
    (D f : Expr Nat) : Prop :=
  ∀ ρ c, M.Ap ρ (.lam D (.app (lift 0 1 f) (.bvar 0))) c →
    CovXPiGate C c ∧ ∀ ds out, CovXCompactAction E c ds out →
      ∃ d, M.Ap ρ f d ∧ CovXCompactAction E d ds out

/-- A genuine Pi relation transports along inclusion of compact actions.
The target's compact typing gate is supplied separately and explicitly. -/
theorem lrSCoreCovXAt_pi_of_action_covers (C : CovTyping E)
    {Γ : LCtx} {A D B : Expr Nat} (read : RedR R Γ A (.pi D B))
    (dom : CovXTypeView E R n Γ D)
    (body : CovXTypeView E R n (.assumption D :: Γ) B)
    (cod : ∀ N, HasTyT E n Γ N D → CovXTypeView E R n Γ (instantiate0 N B))
    {x y : Expr Nat} {d c : CptT}
    (hgate : CovXPiGate C c) (hcover : CovXCompactActionCovers E d c)
    (h : LRSCoreCovXAt C (.pi D B read dom body cod) x y d) :
    LRSCoreCovXAt C (.pi D B read dom body cod) x y c := by
  refine ⟨hgate, ?_⟩
  intro ds out action N N' hN hN' hc hd
  exact h.2 ds out (hcover ds out action) N N' hN hN' hc hd

/-- The left-only observational eta branch factors through the genuine
function child, then uses the proved beta/application eta relation theorem.
The relation-side Pi view is explicit; no model eta equality is assumed. -/
theorem covX_eta_left_of_action_factor (C : CovTyping E) (M : CtxModelT E)
    (hL : ReadbackLaws E R) {Γ : LCtx} {A D B sourceD f : Expr Nat}
    (read : RedR R Γ A (.pi D B))
    (dom : CovXTypeView E R n Γ D)
    (body : CovXTypeView E R n (.assumption D :: Γ) B)
    (cod : ∀ N, HasTyT E n Γ N D → CovXTypeView E R n Γ (instantiate0 N B))
    (hfactor : CovXEtaActionFactorAt C M sourceD f)
    {ρ : EnvT} {x y : Expr Nat} {c : CptT}
    (hchild : ∀ d, M.Ap ρ f d →
      LRSCoreCovXAt C (.pi D B read dom body cod) x y d)
    (hobs : M.Ap ρ (.lam sourceD (.app (lift 0 1 f) (.bvar 0))) c) :
    LRSCoreCovXAt C (.pi D B read dom body cod)
      (.lam D (.app (lift 0 1 x) (.bvar 0))) y c := by
  obtain ⟨hgate, hcover⟩ := hfactor ρ c hobs
  apply lrSCoreCovXAt_eta_left C hL read dom body cod
  refine ⟨hgate, ?_⟩
  intro ds out action N N' hN hN' hc hd
  obtain ⟨d, hobsd, haction⟩ := hcover ds out action
  exact (hchild d hobsd).2 ds out haction N N' hN hN' hc hd

private theorem covX_succ_row_argument {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {a : Expr Nat} {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ (.app (.const 2 []) a) c) :
    c = .bot ∨ ∃ u, c = .spine 2 [u] ∧ ApproxT natEnvU ρ a u := by
  rcases approxT_app_inv (approxTK_forget h) with hb | ⟨g, s, _, hf, _⟩ |
      ⟨r, args, u, hc, hf, hu⟩
  · exact Or.inl hb
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ hf with hb | hs
    · exact CptT.noConfusion hb
    · exact CptT.noConfusion hs
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ hf with hb | hs
    · exact CptT.noConfusion hb
    · cases hs
      exact Or.inr ⟨u, hc, hu⟩

/-- Every actual successor eta observation is covered by the actual rigid
successor compact. The proof retains the argument observation in each row. -/
theorem covX_natSucc_eta_action_covers {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c) :
    CovXCompactActionCovers natEnvU (.spine 2 []) c := by
  rcases approxTK_lam_inv h with rfl | ⟨a, g, rfl, _, _, hrows⟩
  · intro ds out action
    cases action with
    | bot => exact .bot _ _
  · intro ds out action
    cases action with
    | bot => exact .bot _ _
    | @app g' s arg hs hx =>
      rcases covX_succ_row_argument (hrows s hs).2 with hb | ⟨u, he, hu⟩
      · rw [hb]
        exact .bot _ _
      · rw [he]
        apply AppCptT.appSpine
        rcases approxT_bvar_inv hu with rfl | hmem
        · exact .bot _ _
        · exact hx u hmem

/-- The complete general eta factor input is inhabited on `natEnvUWfT`.
Its head witness is non-bottom for every observed lambda compact. -/
theorem covX_natSucc_eta_action_factor (n : Nat) (Γ : LCtx) :
    CovXEtaActionFactorAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n Γ)
      (.const 0 []) (.const 2 []) := by
  intro ρ c hc
  refine ⟨covX_natSucc_eta_pi_gate hc, ?_⟩
  intro ds out action
  exact ⟨.spine 2 [], ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ),
    covX_natSucc_eta_action_covers hc ds out action⟩

/-- On the imported K-free fragment, the action part is supplied generally.
Each selected eta row factors through the landed application inversion, then
the landed lift equivalence recovers an actual observation of the head.
Different rows are allowed to choose different observed head compacts. -/
theorem covX_eta_actions_of_kFree {Γ : LCtx} {ρ : EnvT}
    {D f : Expr Nat} {c : CptT} (hfree : KFreeT E f)
    (hobs : ApproxTK E n Γ ρ (.lam D (.app (lift 0 1 f) (.bvar 0))) c) :
    ∀ ds out, CovXCompactAction E c ds out →
      ∃ d, ApproxTK E n Γ ρ f d ∧ CovXCompactAction E d ds out := by
  rcases approxT_lam_inv (approxTK_forget hobs) with rfl |
    ⟨a, g, rfl, _, _, hrows⟩
  · intro ds out action
    cases action with
    | bot => exact ⟨.bot, .bot _ _ _, .bot _ _⟩
  · intro ds out action
    cases action with
    | bot => exact ⟨.bot, .bot _ _ _, .bot _ _⟩
    | @app g' s arg hs hx =>
      obtain ⟨d, hhead, hstep⟩ :=
        (approxT_app_iff_appCpt E (EnvT.cons (demandT s.1) ρ)
          (lift 0 1 f) (.bvar 0) s.2).mp (hrows s hs).2
      have hmove : ∀ {v o},
          AppCptT E (EnvT.cons (demandT s.1) ρ) v (.bvar 0) o →
            CovXCompactAction E v ds o := by
        intro v o step
        cases step with
        | bot => exact .bot _ _
        | app ht hu =>
          refine AppCptT.app ht ?_
          intro u humem
          rcases approxT_bvar_inv (hu u humem) with rfl | hmem
          · exact .bot _ _
          · exact hx u hmem
        | appSpine hu =>
          apply AppCptT.appSpine
          rcases approxT_bvar_inv hu with rfl | hmem
          · exact .bot _ _
          · exact hx _ hmem
      exact ⟨d, ApproxTK.free hfree
        ((approxT_cons_lift0_iff E ρ (demandT s.1) f d).mp hhead), hmove hstep⟩

/-- Thus the K-free eta residual is precisely the compact Pi gate. This
conditional adapter is not asserted as a general gate supplier. -/
theorem covX_eta_action_factor_of_kFree (C : CovTyping E) (Γ : LCtx)
    {D f : Expr Nat} (hfree : KFreeT E f)
    (hgate : ∀ ρ c,
      ApproxTK E n Γ ρ (.lam D (.app (lift 0 1 f) (.bvar 0))) c →
      CovXPiGate C c) :
    CovXEtaActionFactorAt C (ctxModelT_approxTK E n Γ) D f := by
  intro ρ c hc
  exact ⟨hgate ρ c hc, covX_eta_actions_of_kFree hfree hc⟩

/-- An actual left-only eta compact with an empty demand and a non-bottom
successor output. This row is why a fixed Nat-arrow type table was inadequate. -/
def covXNatEtaEmptyRow : CptT := .lam [([], .spine 2 [.bot])]

theorem covX_natSucc_eta_empty_row_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      covXNatEtaEmptyRow := by
  apply ApproxTK.lam
      (ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat))
  · intro s hs u hu
    have he : s = ([], .spine 2 [.bot]) := List.mem_singleton.mp hs
    subst s
    exact nomatch hu
  · exact ⟨([], .spine 2 [.bot]), List.mem_singleton.mpr rfl,
      fun h => CptT.noConfusion h⟩
  · intro s hs
    have he : s = ([], .spine 2 [.bot]) := List.mem_singleton.mp hs
    subst s
    exact ApproxTK.appSpine
      (ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ))
      (ApproxTK.bot _ _ _)

/-- This factorization control has an inhabited native context, actual
native endpoint typings and eta conversion, and a non-bottom left compact. -/
theorem covX_natSucc_eta_factor_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    CovXEtaActionFactorAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (.const 0 []) (.const 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      covXNatEtaEmptyRow ∧ covXNatEtaEmptyRow ≠ .bot := by
  obtain ⟨hW, hΓ, hl, hr, hc, _⟩ := covX_natSucc_eta_control n
  exact ⟨hW, hΓ, hl, hr, hc, covX_natSucc_eta_action_factor n [],
    covX_natSucc_eta_empty_row_observed n [] EnvT.bot,
    fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_FACTOR_ROOTS
#print axioms CovXCompactActionCovers
#print axioms CovXEtaActionFactorAt
#print axioms lrSCoreCovXAt_pi_of_action_covers
#print axioms covX_eta_left_of_action_factor
#print axioms covX_natSucc_eta_action_covers
#print axioms covX_natSucc_eta_action_factor
#print axioms covX_eta_actions_of_kFree
#print axioms covX_eta_action_factor_of_kFree
#print axioms covXNatEtaEmptyRow
#print axioms covX_natSucc_eta_empty_row_observed
#print axioms covX_natSucc_eta_factor_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_FACTOR_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit
