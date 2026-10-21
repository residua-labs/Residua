import rcic.RcicNativeTypedModelRel

/-!
# Pi-cycle audit: the exact typed probe and its single-link input

The Pi read-off needs only `pi bot []`.  At this compact the landed typed and
untyped relations coincide.  Compose the already proved `BotPiCpt` PER instead
of instantiating the all-compact `typedPER` with circular `ConvArgsT` witnesses.

`PiProbeLinkT` is the remaining input, not a proved fundamental lemma.  The
chain consumer below transports a middle diagonal using the relation itself;
it does not assume approximation invariance of a readback or a model.  Its
single-link premise still ranges over every native `ConvT` constructor,
including conversions built from proof irrelevance followed by iota.

This does not prove all cases of `FundamentalS`, generic declared-domain
alignment, or the Pi row.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiCycleAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- The Pi probe is the same observation in the landed typed and untyped
relations.  No family-spine or nonempty demand clause is inspected. -/
theorem piProbe_typed_iff {Γ : LCtx} {M N A : Expr Nat} :
    LRSCoreT R E n Γ M N A (.pi .bot []) ↔
      LRSCore R E n Γ M N A (.pi .bot []) := by
  rw [LRSCoreT.eq_def, LRSCore.eq_def]
  constructor
  · rintro ⟨hindex, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB, ⟨u, _⟩, _⟩
    exact ⟨hindex, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB,
      ⟨u, lrSCore_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩
  · rintro ⟨hindex, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB, ⟨u, _⟩, _⟩
    exact ⟨hindex, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB,
      ⟨u, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- The typed Pi probe has symmetry without either `ConvArgsT` PER premise. -/
theorem piProbe_symmT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N A : Expr Nat} (h : LRSCoreT R E n Γ M N A (.pi .bot [])) :
    LRSCoreT R E n Γ N M A (.pi .bot []) :=
  piProbe_typed_iff.mpr
    (lrSCore_symm_botPiCpt hW hΓ botPiCpt_pi_bot_nil (piProbe_typed_iff.mp h))

/-- The typed Pi probe has transitivity without the full typed PER. -/
theorem piProbe_transT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N P A : Expr Nat}
    (hMN : LRSCoreT R E n Γ M N A (.pi .bot []))
    (hNP : LRSCoreT R E n Γ N P A (.pi .bot [])) :
    LRSCoreT R E n Γ M P A (.pi .bot []) :=
  piProbe_typed_iff.mpr
    (lrSCore_trans_botPiCpt hL hNU hW hΓ botPiCpt_pi_bot_nil
      (piProbe_typed_iff.mp hMN) (piProbe_typed_iff.mp hNP))

/-- A successful link supplies the next diagonal.  This is the only transport
needed at the middle of a `TyConvT` chain. -/
theorem piProbe_right_diagonalT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N A : Expr Nat}
    (h : LRSCoreT R E n Γ M N A (.pi .bot [])) :
    LRSCoreT R E n Γ N N A (.pi .bot []) :=
  piProbe_transT hL hNU hW hΓ (piProbe_symmT hW hΓ h) h

/-- Minimal single-link input for this consumer: preserve a self-related Pi
probe along a native conversion at a sort.  It is not assumed to be true. -/
def PiProbeLinkT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
    ConvT E n Γ A B (.sort u) →
    LRSCoreT R E n Γ A A (.sort u) (.pi .bot []) →
    LRSCoreT R E n Γ A B (.sort u) (.pi .bot [])

/-- Close the native type-conversion chain from `PiProbeLinkT`.  The proof
uses neither a declared family telescope nor compact transport in `ApproxT`. -/
theorem piProbe_chainT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : PiProbeLinkT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (hc : TyConvT E n Γ A B) :
    ∀ {u : Level}, LRSCoreT R E n Γ A A (.sort u) (.pi .bot []) →
      LRSCoreT R E n Γ A B (.sort u) (.pi .bot []) := by
  induction hc with
  | refl => exact fun h => h
  | of A B v hc =>
      intro u hAA
      have hAA' : LRSCore R E n Γ A A (.sort v) (.pi .bot []) :=
        lrSCore_sort_index_irrel hL (.pi .bot []) (piProbe_typed_iff.mp hAA)
      have hAB := hlink hΓ hc (piProbe_typed_iff.mpr hAA')
      exact piProbe_typed_iff.mpr
        (lrSCore_sort_index_irrel hL (.pi .bot []) (piProbe_typed_iff.mp hAB))
  | trans A B C _ _ ih₁ ih₂ =>
      intro u hAA
      have hAB := ih₁ hAA
      exact piProbe_transT hL hNU hW hΓ hAB
        (ih₂ (piProbe_right_diagonalT hL hNU hW hΓ hAB))

/-- A typed syntactic Pi seeds the probe through the landed diagonal lemma. -/
theorem piProbe_diagT_of_typing {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u : Level} (hPi : HasTyT E n Γ (.pi A B) (.sort u)) :
    LRSCoreT R E n Γ (.pi A B) (.pi A B) (.sort u) (.pi .bot []) := by
  obtain ⟨v, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
  exact piProbe_typed_iff.mpr (diag_pi_probe (.assumption Γ A v hΓ hA) u)

/-- Pi injectivity from the named single-link input.  The first-of split is
the landed native chain interface; all relational work is composed above. -/
theorem piRowField_of_piProbeLinkT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : PiProbeLinkT R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  cases tyConvT_firstOf_data hc with
  | inl heq =>
      rcases Expr.pi.inj heq with ⟨rfl, rfl⟩
      exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  | inr first =>
      obtain ⟨_, u, hfirst, _⟩ := first
      have hPi := (convEnds hW hΓ hfirst).1
      exact lrSCore_pi_components hL (piProbe_typed_iff.mp
        (piProbe_chainT hL hNU hW hlink hΓ hc (piProbe_diagT_of_typing hΓ hPi)))

/-- At the outer Pi probe, an approximated application necessarily uses a
function compact.  This excludes `appSpine` at this observation only; the
function compact may still contain family demands in its arguments. -/
theorem approxT_app_piProbe_inv {ρ : EnvT} {f x : Expr Nat}
    (h : ApproxT E ρ (.app f x) (.pi .bot [])) :
    ∃ (g : List (List CptT × CptT)) (s : List CptT × CptT),
      s.2 = CptT.pi .bot [] ∧ ApproxT E ρ f (.lam g) ∧
      s ∈ g ∧ ∀ u ∈ s.1, ApproxT E ρ x u := by
  rcases approxT_app_inv h with hbot | ⟨g, s, heq, hf, hs, hx⟩ | ⟨r, xs, u, heq, _, _⟩
  · exact CptT.noConfusion hbot
  · exact ⟨g, s, heq.symm, hf, hs, hx⟩
  · exact CptT.noConfusion heq

-- BEGIN RCIC_PI_CYCLE_PROBE_ROOTS
#print axioms piProbe_typed_iff
#print axioms piProbe_symmT
#print axioms piProbe_transT
#print axioms piProbe_right_diagonalT
#print axioms PiProbeLinkT
#print axioms piProbe_chainT
#print axioms piProbe_diagT_of_typing
#print axioms piRowField_of_piProbeLinkT
#print axioms approxT_app_piProbe_inv
-- END RCIC_PI_CYCLE_PROBE_ROOTS

end Rcic.Declarative.NativeValleys.PiCycleAudit
