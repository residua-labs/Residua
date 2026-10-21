import rcic.RcicNativeTypedModelCovWNativeCore
import rcic.RcicNativeTypedModelCovWEtaAliasControl

/-!
# Local typed eta supply for an application alias

The supplier below uses the actual native Pi type of the function, an
observation of its actual codomain, and an observation of its fresh-variable
application. The latter is a genuine new-model premise, so native K sources
must discharge the exact native guards when they supply it.

The resulting beta-alias observation consumes a strictly typed function
graph. This is a local constructor-level result, with no interpretation,
general beta invariance, or raw observation transport claimed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelKFragmentAudit TypedModelCovWIrrelAudit

theorem covWNative_empty_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {f x : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWNative E n Γ ρ f (.lam [([], c)])) :
    ApproxTKWNative E n Γ ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

theorem covWNative_empty_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {A b : Expr Nat} {c : CptWIrrel} (hc : c ≠ .bot)
    (h : ApproxTKWNative E n (.assumption A :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ) b c) :
    ApproxTKWNative E n Γ ρ (.lam A b) (.lam [([], c)]) := by
  refine .lam (.bot _ _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

/-- Even an empty-demand graph carries native Pi typing and an actual
fresh-variable application observation. -/
theorem covWNative_eta_empty_row {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e D B : Expr Nat} {c : CptWIrrel}
    (he : HasTyT E n Γ e (.pi D B)) (hc : c ≠ .bot)
    (hb : ApproxTKWNative E n (.assumption D :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ)
      (.app (lift 0 1 e) (.bvar 0)) c) :
    ApproxTKWNative E n Γ ρ e (.lam [([], c)]) := by
  refine .eta he (.bot _ _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact hb

/-- The domain is actually observed at bottom and the codomain at sort;
therefore the graph's strict typing is checked against an actual Pi code. -/
theorem covWNative_type_sort_row {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {D B : Expr Nat}
    (hB : ApproxTKWNative E n (.assumption D :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ) B .sort) :
    ApproxTKWNative E n Γ ρ (.pi D B) (.pi .bot [([], .sort)]) := by
  refine .pi (.bot _ _ _) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact hB

theorem covWNative_empty_graph_typed_sort_pi {E : ResolvedEnv} {c : CptWIrrel}
    (hcode : TyCodeCT (covWIrrelErase c)) :
    CTyS E (covWIrrelErase (.lam [([], c)]))
      (covWIrrelErase (.pi .bot [([], .sort)])) := by
  simpa only [covWIrrelErase, covWIrrelEraseRows, covWIrrelEraseArgs] using
    TypedModelCovWEtaAudit.covWEta_empty_graph_typed_sort_pi hcode

/-- A concrete beta alias can use the supplied typed eta graph. Every
observation premise concerns the actual native function or native codomain. -/
theorem covWNative_beta_apply_alias {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e D B x : Expr Nat} {c : CptWIrrel}
    (he : HasTyT E n Γ e (.pi D B)) (hc : c ≠ .bot) (hcode : TyCodeCT (covWIrrelErase c))
    (hB : ApproxTKWNative E n (.assumption D :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ) B .sort)
    (hb : ApproxTKWNative E n (.assumption D :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ)
      (.app (lift 0 1 e) (.bvar 0)) c) :
    ApproxTKWNative E n Γ ρ
      (.app (.lam (.pi D B) (.app (.bvar 0) (lift 0 1 x))) e) c := by
  refine .app (g := [([.lam [([], c)]], c)])
    (s := ([.lam [([], c)]], c)) ?_ (List.mem_singleton.mpr rfl) ?_
  · refine .lam (covWNative_type_sort_row hB) ?_
      ⟨([.lam [([], c)]], c), List.mem_singleton.mpr rfl, hc⟩ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      obtain rfl := List.mem_singleton.mp hu
      exact covWNative_empty_graph_typed_sort_pi hcode
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      apply covWNative_empty_app
      exact .bvar (List.mem_singleton.mpr rfl)
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact covWNative_eta_empty_row he hc hb

theorem covWNative_beta_apply_alias_not_only_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e D B x : Expr Nat} {c : CptWIrrel}
    (he : HasTyT E n Γ e (.pi D B)) (hc : c ≠ .bot) (hcode : TyCodeCT (covWIrrelErase c))
    (hB : ApproxTKWNative E n (.assumption D :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ) B .sort)
    (hb : ApproxTKWNative E n (.assumption D :: Γ) (EnvWIrrel.cons (demandWIrrel []) ρ)
      (.app (lift 0 1 e) (.bvar 0)) c) :
    ¬ (∀ d, ApproxTKWNative E n Γ ρ
      (.app (.lam (.pi D B) (.app (.bvar 0) (lift 0 1 x))) e) d → d = .bot) := by
  intro h
  exact hc (h c (covWNative_beta_apply_alias he hc hcode hB hb))

theorem covWNative_sort_observed (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (l : Level) :
    ApproxTKWNative E n Γ ρ (.sort l) (sortCodeWIrrel l) :=
  .sort Γ ρ l

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_ALIAS_CONTROL_ROOTS
#print axioms covWNative_empty_app
#print axioms covWNative_empty_lam
#print axioms covWNative_eta_empty_row
#print axioms covWNative_type_sort_row
#print axioms covWNative_empty_graph_typed_sort_pi
#print axioms covWNative_beta_apply_alias
#print axioms covWNative_beta_apply_alias_not_only_bot
#print axioms covWNative_sort_observed
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_ALIAS_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
