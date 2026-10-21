import rcic.RcicNativeTypedModelProbe
import rcic.RcicNativePiProbeCongruence
import rcic.RcicNativePiProbeModelBoundary
import rcic.RcicNativePiProbeRelBridge
import rcic.RcicNativeReadbackCK

/-!
# Application actions from the typed relation

Composition-only adapters from `LRSCoreS` and the existing
`FundTyAt`/`FundConvAt` statements to the application action ports.
The function clause consumes a native-convertible, typed argument pair
and its relations at the selected graph step's demands. Model inversion
selects that graph step from a realized application compact.

No Fundamental case is proved here. Every model realization and related
substitution supplied to the adapters is an explicit hypothesis.
`closure_claim = 0`. No new axiom, no `sorry`, no `Classical.choice`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeRelAppAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit
open Rcic.Declarative.NativeValleys.PiProbeRelBridgeAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- Apply exactly one step of the typed relation's function clause.
The index is a syntactic Pi, so its normality aligns the clause's domain
and codomain. No Pi injectivity or normal-form uniqueness is used here. -/
theorem lrSCoreS_app_of_lambda_demand (hL : ReadbackLaws E R)
    {Γ : LCtx} {f g a b A B : Expr Nat}
    {graph : List (List CptT × CptT)} {s : List CptT × CptT}
    (hfg : LRSCoreS R E n Γ f g (.pi A B) (.lam graph)) (hs : s ∈ graph)
    (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A)
    (hab : ConvT E n Γ a b A)
    (hdemand : ∀ c ∈ s.1, LRSCoreS R E n Γ a b A c) :
    LRSCoreS R E n Γ (.app f a) (.app g b) (instantiate0 a B) s.2 := by
  rw [LRSCoreS.eq_def] at hfg
  obtain ⟨A₁, B₁, hread, _, hgraph⟩ := hfg
  obtain ⟨hA, hB⟩ := Expr.pi.inj (redR_pi_eq hL hread)
  subst A₁
  subst B₁
  exact hgraph s hs a b ha hb ⟨hab⟩ hdemand

/-- Model application inversion at a non-spine compact, followed by the
function clause. `hfun` relates the function at the graph selected by
either endpoint; `harg` relates each demand supplied by that endpoint.
These localized suppliers are separate from their Fundamental wrappers. -/
theorem lrSCoreS_app_of_model_demand (hL : ReadbackLaws E R)
    {M : CtxModelT E} (hM : CtxModelTLaws M)
    {Γ : LCtx} {ρ ρ' : EnvT} {f g a b A B : Expr Nat}
    (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A)
    (hab : ConvT E n Γ a b A)
    (hfun : ∀ graph, M.Ap ρ f (.lam graph) ∨ M.Ap ρ' g (.lam graph) →
      LRSCoreS R E n Γ f g (.pi A B) (.lam graph))
    (harg : ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c → LRSCoreS R E n Γ a b A c)
    (c : CptT) (hns : ∀ r args, c ≠ .spine r args)
    (hc : M.Ap ρ (.app f a) c ∨ M.Ap ρ' (.app g b) c) :
    LRSCoreS R E n Γ (.app f a) (.app g b) (instantiate0 a B) c := by
  rcases hc with hc | hc
  · rcases hM.app_inv hc with rfl | ⟨graph, s, rfl, hf, hs, hd⟩ |
        ⟨r, args, u, rfl, _, _⟩
    · exact lrSCoreS_bot _ _ _ _
    · exact lrSCoreS_app_of_lambda_demand hL (hfun graph (Or.inl hf)) hs ha hb hab
        (fun d hd' => harg d (Or.inl (hd d hd')))
    · exact (hns r (args ++ [u]) rfl).elim
  · rcases hM.app_inv hc with rfl | ⟨graph, s, rfl, hg, hs, hd⟩ |
        ⟨r, args, u, rfl, _, _⟩
    · exact lrSCoreS_bot _ _ _ _
    · exact lrSCoreS_app_of_lambda_demand hL (hfun graph (Or.inr hg)) hs ha hb hab
        (fun d hd' => harg d (Or.inr (hd d hd')))
    · exact (hns r (args ++ [u]) rfl).elim

/-- Compose the model inversion with the two observation bridges. The
realization hypotheses are at the actual two application endpoints and
the existing context environment; they are not raw backward transport.
The lambda graph and every consumed argument demand remain exposed by
the two localized relation suppliers. -/
theorem probeEquiv_app_of_approx_relationsT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f g a b A B : Expr Nat}
    (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A)
    (hab : ConvT E n Γ a b A)
    (hfun : ∀ graph,
      ApproxT E (ctxEnvT E Γ) f (.lam graph) ∨
        ApproxT E (ctxEnvT E Γ) g (.lam graph) →
      LRSCoreS R E n Γ f g (.pi A B) (.lam graph))
    (harg : ∀ c, ApproxT E (ctxEnvT E Γ) a c ∨
        ApproxT E (ctxEnvT E Γ) b c → LRSCoreS R E n Γ a b A c)
    (hreal : ProbeRealizedAtT R E n Γ (.app f a))
    (hreal' : ProbeRealizedAtT R E n Γ (.app g b)) :
    ProbeEquivT R E n Γ (.app f a) (.app g b) := by
  apply probeEquiv_of_lrSCoreS_probesT hL hNU hW hΓ
    (I := instantiate0 a B)
  · intro u hread
    apply lrSCoreS_app_of_model_demand hL (ctxModelTLaws_approxT E)
      ha hb hab hfun harg (sortCode u)
    · intro r args heq
      rcases sortCode_prop_or_sort u with hu | hu <;> rw [hu] at heq <;> cases heq
    · rcases hread with hread | hread
      · exact Or.inl (hreal.1 u hread)
      · exact Or.inr (hreal'.1 u hread)
  · intro C D hread hΓC
    apply lrSCoreS_app_of_model_demand hL (ctxModelTLaws_approxT E)
      ha hb hab hfun harg (.pi .bot [])
    · intro r args heq
      cases heq
    · rcases hread with hread | hread
      · exact Or.inl (hreal.2 C D hread hΓC)
      · exact Or.inr (hreal'.2 C D hread hΓC)

/-- Head action consumes the conversion motive for the head, and the
typing motive for each fixed argument. The identity package instantiates
those existing motives; realization is requested at both observed apps.
Neither motive nor the quantified realization input is proved here. -/
theorem appHeadAction_of_fundAtT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f g A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B))
    (hId : RelSubstIdT (ctxModelT_approxT E) R n Γ (ctxEnvT E Γ))
    (hfun : FundConvAt (ctxModelT_approxT E) R n Γ f g (.pi A B))
    (harg : ∀ {a : Expr Nat}, HasTyT E n Γ a A →
      FundTyAt (ctxModelT_approxT E) R n Γ a A)
    (hreal : ∀ {a : Expr Nat}, HasTyT E n Γ a A →
      ProbeRealizedAtT R E n Γ (.app f a) ∧
        ProbeRealizedAtT R E n Γ (.app g a)) :
    AppHeadActionT R hf := by
  intro a ha
  exact probeEquiv_app_of_approx_relationsT hL hNU hW hΓ
    ha ha (.refl Γ a A ha)
    (fun graph hc => fundConvAt_ctx_of_id hΓ hId hfun (.lam graph) hc)
    (fun c hc => fundTyAt_ctx_of_id hΓ hId (harg ha) c (hc.elim id id))
    (hreal ha).1 (hreal ha).2

/-- Argument action consumes the typing motive for the fixed function,
and the conversion motive for the argument pair. Typing of both argument
endpoints comes from their native conversion. Realization is only asked
of this fixed function applied to typed arguments. -/
theorem appArgAction_of_fundAtT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {g A B : Expr Nat}
    (hg : HasTyT E n Γ g (.pi A B))
    (hId : RelSubstIdT (ctxModelT_approxT E) R n Γ (ctxEnvT E Γ))
    (hfun : FundTyAt (ctxModelT_approxT E) R n Γ g (.pi A B))
    (harg : ∀ {a b : Expr Nat}, ConvT E n Γ a b A →
      FundConvAt (ctxModelT_approxT E) R n Γ a b A)
    (hreal : ∀ {a : Expr Nat}, HasTyT E n Γ a A →
      ProbeRealizedAtT R E n Γ (.app g a)) :
    AppArgActionT R hg := by
  intro a b hab
  have ha := (convEnds hW hΓ hab).1
  have hb := (convEnds hW hΓ hab).2.1
  exact probeEquiv_app_of_approx_relationsT hL hNU hW hΓ ha hb hab
    (fun graph hc => fundTyAt_ctx_of_id hΓ hId hfun (.lam graph) (hc.elim id id))
    (fun c hc => fundConvAt_ctx_of_id hΓ hId (harg hab) c hc)
    (hreal ha) (hreal hb)

/-- Deterministic-readback specialization. The supplied Fundamental
conjunction is consumed as `FundConvAt` on the head and `FundTyAt` on each
argument. The identity package and both application realizations remain
separate hypotheses. -/
theorem appHeadAction_of_fundamentalSAtT_whStepCK (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f g A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B))
    (hId : RelSubstIdT (ctxModelT_approxT E) (WhStepCK E) n Γ (ctxEnvT E Γ))
    (hF : FundamentalSAtT (ctxModelT_approxT E) (WhStepCK E) n)
    (hreal : ∀ {a : Expr Nat}, HasTyT E n Γ a A →
      ProbeRealizedAtT (WhStepCK E) E n Γ (.app f a) ∧
        ProbeRealizedAtT (WhStepCK E) E n Γ (.app g a)) :
    AppHeadActionT (WhStepCK E) hf :=
  appHeadAction_of_fundAtT (readbackLaws_whStepCK E)
    (normalUniqueR_whStepCK hW) hW hΓ hf hId
    (hF.2 hΓ hf) (fun ha => hF.1 hΓ ha) hreal

/-- Deterministic-readback specialization. Here the supplied Fundamental
conjunction is consumed as `FundTyAt` on the function and `FundConvAt` on
the arguments. This constructs no Fundamental witness. -/
theorem appArgAction_of_fundamentalSAtT_whStepCK (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {g A B : Expr Nat}
    (hg : HasTyT E n Γ g (.pi A B))
    (hId : RelSubstIdT (ctxModelT_approxT E) (WhStepCK E) n Γ (ctxEnvT E Γ))
    (hF : FundamentalSAtT (ctxModelT_approxT E) (WhStepCK E) n)
    (hreal : ∀ {a : Expr Nat}, HasTyT E n Γ a A →
      ProbeRealizedAtT (WhStepCK E) E n Γ (.app g a)) :
    AppArgActionT (WhStepCK E) hg :=
  appArgAction_of_fundAtT (readbackLaws_whStepCK E)
    (normalUniqueR_whStepCK hW) hW hΓ hg hId
    (hF.1 hΓ hg) (fun hab => hF.2 hΓ hab) hreal

/-! ## Typed local satisfiability checks

The following checks distinguish three facts: the identity package has
an empty-context instance; constant-body applications realize their
observed compacts; and an actual typed application can select a lambda
step with a nonempty, nonbottom `.prop` demand. They do not supply
`FundamentalSAtT` or any realization package for arbitrary functions.
-/

/-- An actual identity package at the empty native context. This makes
no assertion about identity packages at arbitrary contexts. -/
theorem relSubstIdT_nil_probe (M : CtxModelT E) (ρ : EnvT) :
    RelSubstIdT M R n [] ρ := by
  simp [RelSubstIdT, RelSubstAtT, TypedSubstT, ConvSubstT, lookupType, lookupValue]

/-- A selected empty demand is constructively realizable when its
nonbottom body compact is given. This is a constructor fact, not a model
substitution or expansion law. -/
theorem approxT_app_empty_demand {ρ : EnvT} {D body a : Expr Nat} {c : CptT}
    (hc : c ≠ .bot) (hbody : ApproxT E (EnvT.cons (demandT []) ρ) body c) :
    ApproxT E ρ (.app (.lam D body) a) c := by
  have hlam : ApproxT E ρ (.lam D body) (.lam [([], c)]) := by
    refine .lam (.bot ρ D) ?_ ?_ ?_
    · intro s hs u hu
      have heq := List.mem_singleton.mp hs
      subst s
      exact (List.not_mem_nil u hu).elim
    · exact ⟨([], c), List.mem_singleton.mpr rfl, hc⟩
    · intro s hs
      have heq := List.mem_singleton.mp hs
      subst s
      exact hbody
  exact .app hlam (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

/-- This whole local realization input is inhabited for every constant
sort application, including every typed argument to such a function. -/
theorem probeRealizedAt_constantSortAppT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (Γ : LCtx) (D a : Expr Nat) (u : Level) :
    ProbeRealizedAtT R E n Γ (.app (.lam D (.sort u)) a) := by
  have hread : RedR R Γ (.app (.lam D (.sort u)) a) (.sort u) :=
    redR_single (hL.beta Γ D (.sort u) a)
  have hn : NormalR R Γ (.sort u) := fun e hs => hL.sort_normal Γ u e hs
  constructor
  · intro v hv
    have heq := Expr.sort.inj
      (hNU Γ hv (fun e hs => hL.sort_normal Γ v e hs) hread hn)
    subst v
    exact approxT_app_empty_demand (sortCode_ne_bot u) (.sort _ u)
  · intro A B hpi _
    have heq := hNU Γ hread hn hpi (fun e hs => hL.pi_normal Γ A B e hs)
    exact (Expr.noConfusion heq : False).elim

/-- Pi-body applications also inhabit their entire local realization
input. The observation compact needs no model information about the
Pi's components, even when substitution changes them. -/
theorem probeRealizedAt_piBodyAppT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (Γ : LCtx) (D A B a : Expr Nat) :
    ProbeRealizedAtT R E n Γ (.app (.lam D (.pi A B)) a) := by
  have hread : RedR R Γ (.app (.lam D (.pi A B)) a) (instantiate0 a (.pi A B)) :=
    redR_single (hL.beta Γ D (.pi A B) a)
  have hn : NormalR R Γ (instantiate0 a (.pi A B)) :=
    fun e hs => hL.pi_normal Γ _ _ e hs
  constructor
  · intro u hu
    have heq := hNU Γ hu (fun e hs => hL.sort_normal Γ u e hs) hread hn
    exact (Expr.noConfusion heq : False).elim
  · intro C F _ _
    exact approxT_app_empty_demand (fun h => CptT.noConfusion h)
      (approxT_pi_bot_nil _ _ _ _)

def appSortDemandGraph : List (List CptT × CptT) := [([.prop], .prop)]
def appPiDemandGraph : List (List CptT × CptT) := [([.prop], .pi .bot [])]

/-- The chosen nonempty argument demand is realized by the native typed
`Sort 0 : Sort 1`, and is strictly typed at the domain's actual code. -/
theorem app_argument_demand_witness :
    ApproxT emptyEnv (ctxEnvT emptyEnv []) appCounterArgument .prop ∧
    CTyS emptyEnv .prop .sort := by
  constructor
  · simpa only [appCounterArgument, sortCode_zero] using
      (ApproxT.sort (E := emptyEnv) (ctxEnvT emptyEnv []) .zero)
  · rw [CTyS]
    exact Or.inr TyCodeCT.prop

theorem app_sort_function_demand_witness :
    ApproxT emptyEnv (ctxEnvT emptyEnv []) appCounterLeft (.lam appSortDemandGraph) := by
  refine ApproxT.lam (a := .sort) ?_ ?_ ?_ ?_
  · have hcode : sortCode (.succ .zero) = .sort :=
      (sortCode_eq_sort_iff _).mpr (Rcic.Declarative.Ann.not_eqN_succ_zero .zero)
    simpa only [appCounterDomain, hcode] using
      (ApproxT.sort (E := emptyEnv) (ctxEnvT emptyEnv []) (.succ .zero))
  · intro s hs c hc
    have heq := List.mem_singleton.mp hs
    subst s
    have heq := List.mem_singleton.mp hc
    subst c
    rw [CTyS]
    exact Or.inr TyCodeCT.prop
  · exact ⟨([.prop], .prop), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩
  · intro s hs
    have heq := List.mem_singleton.mp hs
    subst s
    simpa only [appCounterArgument, sortCode_zero] using
      (ApproxT.sort (E := emptyEnv) (EnvT.cons (demandT [.prop]) (ctxEnvT emptyEnv [])) .zero)

theorem app_pi_function_demand_witness :
    ApproxT emptyEnv (ctxEnvT emptyEnv []) appCounterRight (.lam appPiDemandGraph) := by
  refine ApproxT.lam (a := .sort) ?_ ?_ ?_ ?_
  · have hcode : sortCode (.succ .zero) = .sort :=
      (sortCode_eq_sort_iff _).mpr (Rcic.Declarative.Ann.not_eqN_succ_zero .zero)
    simpa only [appCounterDomain, hcode] using
      (ApproxT.sort (E := emptyEnv) (ctxEnvT emptyEnv []) (.succ .zero))
  · intro s hs c hc
    have heq := List.mem_singleton.mp hs
    subst s
    have heq := List.mem_singleton.mp hc
    subst c
    rw [CTyS]
    exact Or.inr TyCodeCT.prop
  · exact ⟨([.prop], .pi .bot []), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩
  · intro s hs
    have heq := List.mem_singleton.mp hs
    subst s
    exact approxT_pi_bot_nil _ _ _ _

/-- The selected argument's actual `.prop` relation is a sort clause. -/
theorem app_argument_relation_witness :
    LRSCoreS R emptyEnv 0 [] appCounterArgument appCounterArgument appCounterDomain .prop := by
  rw [lrSCoreS_prop_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, .refl _, .refl _⟩

/-- The selected lambda step is related at all native typed argument
pairs. The body's sort is constant, so the supplied demand relation is
accepted without any additional substitution fact. -/
theorem app_sort_function_relation_witness (hL : ReadbackLaws emptyEnv R) :
    LRSCoreS R emptyEnv 0 [] appCounterLeft appCounterLeft
      (.pi appCounterDomain appCounterDomain) (.lam appSortDemandGraph) := by
  rw [LRSCoreS.eq_def]
  refine ⟨appCounterDomain, appCounterDomain, .refl _,
    ⟨.assumption [] appCounterDomain (.succ (.succ .zero)) .nil (.sort [] (.succ .zero))⟩, ?_⟩
  intro s hs a b _ _ _ _
  have heq := List.mem_singleton.mp hs
  subst s
  rw [lrSCoreS_prop_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero,
    redR_single (hL.beta [] appCounterDomain appCounterArgument a),
    redR_single (hL.beta [] appCounterDomain appCounterArgument b)⟩

theorem app_pi_function_relation_witness (hL : ReadbackLaws emptyEnv R) :
    LRSCoreS R emptyEnv 0 [] appCounterRight appCounterRight
      (.pi appCounterDomain appCounterDomain) (.lam appPiDemandGraph) := by
  rw [LRSCoreS.eq_def]
  refine ⟨appCounterDomain, appCounterDomain, .refl _,
    ⟨.assumption [] appCounterDomain (.succ (.succ .zero)) .nil (.sort [] (.succ .zero))⟩, ?_⟩
  intro s hs a b _ _ _ _
  have heq := List.mem_singleton.mp hs
  subst s
  rw [LRSCoreS.eq_def]
  exact ⟨⟨.succ .zero, .refl _⟩,
    .sort .zero, .sort .zero, .sort .zero, .sort .zero,
    redR_single (hL.beta [] appCounterDomain appCounterPi a),
    redR_single (hL.beta [] appCounterDomain appCounterPi b),
    ⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.zero, lrSCoreS_bot _ _ _ _⟩,
    fun t ht _ => (List.not_mem_nil t ht).elim⟩

/-- An actual native typed beta redex realizes the sort observation and
applies the relation's selected step at the nonbottom `.prop` demand. -/
theorem app_sort_typed_demand_control :
    Nonempty (HasTyT emptyEnv 0 [] (.app appCounterLeft appCounterArgument) appCounterDomain) ∧
    ProbeRealizedAtT (WhStepCK emptyEnv) emptyEnv 0 [] (.app appCounterLeft appCounterArgument) ∧
    RedR (WhStepCK emptyEnv) [] (.app appCounterLeft appCounterArgument) (.sort .zero) ∧
    LRSCoreS (WhStepCK emptyEnv) emptyEnv 0 []
      (.app appCounterLeft appCounterArgument) (.app appCounterLeft appCounterArgument)
      appCounterDomain .prop := by
  refine ⟨⟨appCounterLeftAppTyping⟩,
    probeRealizedAt_constantSortAppT (readbackLaws_whStepCK emptyEnv)
      (normalUniqueR_whStepCK .empty) [] appCounterDomain appCounterArgument .zero,
    redR_single ((readbackLaws_whStepCK emptyEnv).beta []
      appCounterDomain appCounterArgument appCounterArgument), ?_⟩
  apply lrSCoreS_app_of_lambda_demand (readbackLaws_whStepCK emptyEnv)
    (app_sort_function_relation_witness (readbackLaws_whStepCK emptyEnv))
    (List.mem_singleton.mpr rfl) appCounterArgumentTyping appCounterArgumentTyping
    (.refl [] appCounterArgument appCounterDomain appCounterArgumentTyping)
  intro c hc
  have heq := List.mem_singleton.mp hc
  subst c
  exact app_argument_relation_witness

/-- The Pi observation has a separate native typed beta-redex control
using the same inhabited, nonbottom argument demand. -/
theorem app_pi_typed_demand_control :
    Nonempty (HasTyT emptyEnv 0 [] (.app appCounterRight appCounterArgument) appCounterDomain) ∧
    ProbeRealizedAtT (WhStepCK emptyEnv) emptyEnv 0 [] (.app appCounterRight appCounterArgument) ∧
    RedR (WhStepCK emptyEnv) [] (.app appCounterRight appCounterArgument) appCounterPi ∧
    LRSCoreS (WhStepCK emptyEnv) emptyEnv 0 []
      (.app appCounterRight appCounterArgument) (.app appCounterRight appCounterArgument)
      appCounterDomain (.pi .bot []) := by
  refine ⟨⟨appCounterRightAppTyping⟩,
    probeRealizedAt_piBodyAppT (readbackLaws_whStepCK emptyEnv)
      (normalUniqueR_whStepCK .empty) [] appCounterDomain (.sort .zero) (.sort .zero)
      appCounterArgument,
    redR_single ((readbackLaws_whStepCK emptyEnv).beta []
      appCounterDomain appCounterPi appCounterArgument), ?_⟩
  apply lrSCoreS_app_of_lambda_demand (readbackLaws_whStepCK emptyEnv)
    (app_pi_function_relation_witness (readbackLaws_whStepCK emptyEnv))
    (List.mem_singleton.mpr rfl) appCounterArgumentTyping appCounterArgumentTyping
    (.refl [] appCounterArgument appCounterDomain appCounterArgumentTyping)
  intro c hc
  have heq := List.mem_singleton.mp hc
  subst c
  exact app_argument_relation_witness

-- BEGIN RCIC_PI_PROBE_REL_APP_ROOTS
#print axioms lrSCoreS_app_of_lambda_demand
#print axioms lrSCoreS_app_of_model_demand
#print axioms probeEquiv_app_of_approx_relationsT
#print axioms appHeadAction_of_fundAtT
#print axioms appArgAction_of_fundAtT
#print axioms appHeadAction_of_fundamentalSAtT_whStepCK
#print axioms appArgAction_of_fundamentalSAtT_whStepCK
#print axioms relSubstIdT_nil_probe
#print axioms approxT_app_empty_demand
#print axioms probeRealizedAt_constantSortAppT
#print axioms probeRealizedAt_piBodyAppT
#print axioms appSortDemandGraph
#print axioms appPiDemandGraph
#print axioms app_argument_demand_witness
#print axioms app_sort_function_demand_witness
#print axioms app_pi_function_demand_witness
#print axioms app_argument_relation_witness
#print axioms app_sort_function_relation_witness
#print axioms app_pi_function_relation_witness
#print axioms app_sort_typed_demand_control
#print axioms app_pi_typed_demand_control
-- END RCIC_PI_PROBE_REL_APP_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeRelAppAudit
