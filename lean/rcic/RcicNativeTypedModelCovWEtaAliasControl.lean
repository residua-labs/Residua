import rcic.RcicNativeTypedModelCovWEtaAligned

/-!
# Local typed eta supply for an application alias

The supplier below uses the actual native Pi type of the function, an
observation of its actual codomain, and an observation of its fresh-variable
application. The latter is a genuine new-model premise, so native K sources
must still discharge the unchanged guards when they supply it.

The resulting beta-alias observation consumes a strictly typed function
graph. This is a local constructor-level result, with no interpretation,
general beta invariance, or raw observation transport claimed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelKFragmentAudit

theorem covWEta_empty_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {f x : Expr Nat} {c : CptT}
    (h : ApproxTKWEta E n Γ ρ f (.lam [([], c)])) :
    ApproxTKWEta E n Γ ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

theorem covWEta_empty_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {A b : Expr Nat} {c : CptT} (hc : c ≠ .bot)
    (h : ApproxTKWEta E n (.assumption A :: Γ) (EnvT.cons (demandT []) ρ) b c) :
    ApproxTKWEta E n Γ ρ (.lam A b) (.lam [([], c)]) := by
  refine .lam (.bot _ _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

/-- Even an empty-demand graph carries native Pi typing and an actual
fresh-variable application observation. -/
theorem covWEta_eta_empty_row {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e D B : Expr Nat} {c : CptT}
    (he : HasTyT E n Γ e (.pi D B)) (hc : c ≠ .bot)
    (hb : ApproxTKWEta E n (.assumption D :: Γ) (EnvT.cons (demandT []) ρ)
      (.app (lift 0 1 e) (.bvar 0)) c) :
    ApproxTKWEta E n Γ ρ e (.lam [([], c)]) := by
  refine .eta he (.bot _ _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact hb

/-- The domain is actually observed at bottom and the codomain at sort;
therefore the graph's strict typing is checked against an actual Pi code. -/
theorem covWEta_type_sort_row {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {D B : Expr Nat}
    (hB : ApproxTKWEta E n (.assumption D :: Γ) (EnvT.cons (demandT []) ρ) B .sort) :
    ApproxTKWEta E n Γ ρ (.pi D B) (.pi .bot [([], .sort)]) := by
  refine .pi (.bot _ _ _) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact hB

theorem covWEta_empty_graph_typed_sort_pi {E : ResolvedEnv} {c : CptT}
    (hcode : TyCodeCT c) : CTyS E (.lam [([], c)]) (.pi .bot [([], .sort)]) := by
  rw [CTyS]
  refine Or.inr ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    cases h with
    | pi _ hg => exact not_isPropCT_sort E (hg ([], .sort) (List.mem_singleton.mpr rfl))
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs t ht _
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp ht
    rw [CTyS]
    exact Or.inr hcode
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact Or.inr ⟨([], .sort), List.mem_singleton.mpr rfl, fun _ hu => hu⟩

/-- A concrete beta alias can use the supplied typed eta graph. Every
observation premise concerns the actual native function or native codomain. -/
theorem covWEta_beta_apply_alias {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e D B x : Expr Nat} {c : CptT}
    (he : HasTyT E n Γ e (.pi D B)) (hc : c ≠ .bot) (hcode : TyCodeCT c)
    (hB : ApproxTKWEta E n (.assumption D :: Γ) (EnvT.cons (demandT []) ρ) B .sort)
    (hb : ApproxTKWEta E n (.assumption D :: Γ) (EnvT.cons (demandT []) ρ)
      (.app (lift 0 1 e) (.bvar 0)) c) :
    ApproxTKWEta E n Γ ρ
      (.app (.lam (.pi D B) (.app (.bvar 0) (lift 0 1 x))) e) c := by
  refine .app (g := [([.lam [([], c)]], c)])
    (s := ([.lam [([], c)]], c)) ?_ (List.mem_singleton.mpr rfl) ?_
  · refine .lam (covWEta_type_sort_row hB) ?_
      ⟨([.lam [([], c)]], c), List.mem_singleton.mpr rfl, hc⟩ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      obtain rfl := List.mem_singleton.mp hu
      exact covWEta_empty_graph_typed_sort_pi hcode
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      apply covWEta_empty_app
      exact .free (kFreeT_bvar E 0) (.bvar (List.mem_singleton.mpr rfl))
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact covWEta_eta_empty_row he hc hb

theorem covWEta_beta_apply_alias_not_only_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {e D B x : Expr Nat} {c : CptT}
    (he : HasTyT E n Γ e (.pi D B)) (hc : c ≠ .bot) (hcode : TyCodeCT c)
    (hB : ApproxTKWEta E n (.assumption D :: Γ) (EnvT.cons (demandT []) ρ) B .sort)
    (hb : ApproxTKWEta E n (.assumption D :: Γ) (EnvT.cons (demandT []) ρ)
      (.app (lift 0 1 e) (.bvar 0)) c) :
    ¬ (∀ d, ApproxTKWEta E n Γ ρ
      (.app (.lam (.pi D B) (.app (.bvar 0) (lift 0 1 x))) e) d → d = .bot) := by
  intro h
  exact hc (h c (covWEta_beta_apply_alias he hc hcode hB hb))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_ALIAS_CONTROL_ROOTS
#print axioms covWEta_empty_app
#print axioms covWEta_empty_lam
#print axioms covWEta_eta_empty_row
#print axioms covWEta_type_sort_row
#print axioms covWEta_empty_graph_typed_sort_pi
#print axioms covWEta_beta_apply_alias
#print axioms covWEta_beta_apply_alias_not_only_bot
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_ALIAS_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
