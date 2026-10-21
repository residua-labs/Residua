import rcic.RcicNativeTypedModelCovVControls
import rcic.RcicNativeTypedModelCovVHeadActions

/-!
# The actual scope of the eligible-Eq call boundary

Recursor eligibility leaves the old raw Eq observation intact, but the
guarded relation already excludes every indexed proposition recursor from
its transitive `.free` fragment. In particular a closed major cannot make
that branch admit an Eq call. The apart-index raw observation and the
independent index-guard failure are supplied separately below.

The native CK2 index certificate uses native conversion. The independent
index guard's rejection is not a proof that this native certificate fails.
The precise native normality characterization is recorded without asserting
either side. Consequently this module does not claim a fully inhabited
counterexample to the aligned matching-head theorem.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKGuardAudit TypedModelKFailureAudit
open TypedModelKTransportAudit TypedModelKControlAudit TypedModelKObstructionAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2ModelObstructionAudit
open TypedModelCovTAudit TypedModelCovVAudit PiProbeModelBoundaryAudit

/-- A normal source has only its reflexive finite reduct. This is independent
of determinism and leaves the source itself available as a normal head. -/
theorem covW_normal_redR_eq {R : Readback} {Γ : LCtx} {a b : Expr Nat}
    (hn : NormalR R Γ a) (hr : RedR R Γ a b) : b = a :=
  redR_of_normal hn hr

/-- Any literal occurrence of an indexed proposition recursor contradicts
the old fragment's actual support certificate. -/
theorem covW_indexed_occurrence_not_free {E : ResolvedEnv} {r : Nat}
    {e : Expr Nat} (hi : IndexedPropRecT E r)
    (ho : occursConst r e = true) : ¬ KFreeT E e := by
  rintro ⟨S, hS, hs⟩
  exact hS.noIndexed r (hs r ho) hi

/-- The transitive old `.free` fragment excludes every spine headed by an
indexed proposition recursor, independently of its arguments or major. -/
theorem covW_indexed_rec_spine_not_free {E : ResolvedEnv} {r : Nat}
    (hi : IndexedPropRecT E r) (ls : List Level) (args : List (Expr Nat)) :
    ¬ KFreeT E (foldApps (.const r ls) args) :=
  fun hf => kFreeT_const_not_indexed (kFreeT_foldApps_head hf) hi

/-- Hiding the indexed reference in a transparent body cannot evade the
same exclusion: the existing fragment follows every inspected delta body. -/
theorem covW_indexed_delta_not_free {E : ResolvedEnv} {r k : Nat}
    {m : CheckedMember} {b : Expr Nat} (hd : DeltaConst E r m b)
    (hi : IndexedPropRecT E k) (ls ls' : List Level)
    (ho : occursConst k (instantiateLevels ls' b) = true) :
    ¬ KFreeT E (.const r ls) :=
  fun hf => covW_indexed_occurrence_not_free hi ho (kFreeT_delta hf hd)

/-- The fragment also follows all structured recursor schemas; eligibility
at an outer reference cannot hide a restricted inner recursor. -/
theorem covW_indexed_schema_not_free {E : ResolvedEnv} {k : Nat}
    (w : IotaWitnessS E) (hi : IndexedPropRecT E k) (ls ls' : List Level)
    (ho : occursConst k (instantiateLevels ls' w.schema) = true) :
    ¬ KFreeT E (.const w.recRef ls) :=
  fun hf => covW_indexed_occurrence_not_free hi ho (kFreeT_schema w hf)

/-- In particular native K eligibility cannot discharge the incompatible
`.free` premise of an indexed recursor. Both eligibility predicates retain
their actual native existential witnesses. -/
theorem covW_indexed_eligible_spine_not_free {E : ResolvedEnv} {r : Nat}
    (hi : IndexedPropRecT E r) (_hn : KFreeRec E r ∨ KProjRec E r)
    (ls : List Level) (args : List (Expr Nat)) :
    ¬ KFreeT E (foldApps (.const r ls) args) :=
  covW_indexed_rec_spine_not_free hi ls args

/-- The actual Eq recursor inhabits both metadata predicates. Thus the
preceding exclusion is nonvacuous at the admitted eligible recursor. -/
theorem covW_eq_eligible_indexed :
    Nonempty (EnvWfT eqEnvT) ∧ KFreeRec eqEnvT 65 ∧
    IndexedPropRecT eqEnvT 65 ∧
    ∀ (ls : List Level) (args : List (Expr Nat)),
      ¬ KFreeT eqEnvT (foldApps (.const 65 ls) args) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨eqGapW, rfl, ⟨rfl, rfl, rfl⟩⟩,
    indexedPropRecT_eqRec,
    covW_indexed_rec_spine_not_free indexedPropRecT_eqRec⟩

/-- The old full-grammar inversion survives CovV forgetting. No Eq proper
prefix can carry a nonbottom compact, including any curried lambda table. -/
theorem covW_eq_prefix_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {ls : List Level} {args : List (Expr Nat)} {c : CptT}
    (hlen : args.length < 6)
    (ho : ApproxTKN eqEnvT n Γ ρ (foldApps (.const 65 ls) args) c) :
    c = .bot :=
  approxTK_eqRec_fold_prefix_bot hlen (approxTKN_forget ho)

/-- This excludes every lambda table, not only a selected empty-demand row. -/
theorem covW_eq_prefix_no_lambda (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (ls : List Level) (args : List (Expr Nat)) (hlen : args.length < 6)
    (rows : List (List CptT × CptT)) :
    ¬ ApproxTKN eqEnvT n Γ ρ (foldApps (.const 65 ls) args) (.lam rows) :=
  fun ho => CptT.noConfusion (covW_eq_prefix_only_bot hlen ho)

/-- The bottom-only prefix measurement includes its actual observation. -/
theorem covW_eq_prefix_observation_iff (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (ls : List Level) (args : List (Expr Nat)) (hlen : args.length < 6)
    (c : CptT) :
    ApproxTKN eqEnvT n Γ ρ (foldApps (.const 65 ls) args) c ↔ c = .bot := by
  constructor
  · exact covW_eq_prefix_only_bot hlen
  · intro hc
    subst c
    exact .bot _ _ _

/-- The old eligible raw relation still observes the exact apart call. This
is deliberately an ApproxTN statement, not an ApproxTKN `.free` witness. -/
theorem covW_eq_apart_raw_observed (ρ : EnvT) :
    ApproxTN eqEnvT ρ apartRec .prop :=
  covV_approxT_of_native_heads covV_eq_native_heads (apartRec_model ρ)

/-- Its old empty-major-demand prefix row also remains in the raw relation. -/
theorem covW_eq_apart_prefix_raw_observed (ρ : EnvT) :
    ApproxTN eqEnvT ρ apartPrefix (.lam [([], .prop)]) :=
  covV_approxT_of_native_heads covV_eq_native_heads (apartPrefix_model ρ)

/-- This is the actual field-free witness at the apart source, with all
five recursor arguments fixed. -/
def covWEqApartWitness : IotaWitness eqEnvT :=
  eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight apartMot (.sort .zero)

/-- The independent guard fails at this actual call. This does not identify
failure of the separate native KIndexConvAt conjunct. -/
theorem covW_eq_apart_guard_rejected (n : Nat) :
    ¬ KIndexGuardAt eqEnvT n apartCtx covWEqApartWitness :=
  not_kIndexGuardAt_apart (x := .bvar 0) rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)

/-- All native premises of the raw/guarded comparison are supplied. The
raw nonbottom output and prefix row coexist with exact guarded exclusion. -/
theorem covW_eq_apart_raw_guarded_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    KFreeRec eqEnvT 65 ∧
    ApproxTN eqEnvT EnvT.bot apartPrefix (.lam [([], .prop)]) ∧
    ApproxTN eqEnvT EnvT.bot apartRec .prop ∧
    (¬ KFreeT eqEnvT apartRec) ∧
    (¬ KIndexGuardAt eqEnvT n apartCtx covWEqApartWitness) ∧
    ApproxTKN eqEnvT n apartCtx EnvT.bot apartRec .bot ∧
    (∀ ρ c, ApproxTKN eqEnvT n apartCtx ρ apartRec c → c = .bot) ∧
    ¬ ApproxTKN eqEnvT n apartCtx EnvT.bot apartRec .prop := by
  obtain ⟨hW, hΓ, ht, _, hb, honly, hnot⟩ := covV_K_apart_control n
  exact ⟨hW, hΓ, ht, ⟨covWEqApartWitness, rfl, ⟨rfl, rfl, rfl⟩⟩,
    covW_eq_apart_prefix_raw_observed EnvT.bot,
    covW_eq_apart_raw_observed EnvT.bot,
    covW_indexed_rec_spine_not_free indexedPropRecT_eqRec _ _,
    covW_eq_apart_guard_rejected n, hb, honly, hnot⟩

/-- The exact native normality obligation still depends on the native gate.
Rejecting only the independent model guard cannot establish this premise. -/
theorem covW_eq_apart_normal_iff_no_native (n : Nat) :
    NormalR (WhStepCK2 eqEnvT n) apartCtx apartRec ↔
      ∀ e, ¬ KNativeHead eqEnvT n apartCtx apartRec e := by
  constructor
  · intro hn e hs
    exact hn e (.native hs)
  · intro hn
    exact normalR_kRec_of_no_native pinEqGroupWfT
      (w := covWEqApartWitness) (Or.inl ⟨rfl, rfl, rfl⟩)
      not_isCtorSpine_bvar hn

/-- If the separate native obstruction were supplied, its conclusion would
be a normal stuck spine and no matching sort readback. It would still have
an actual normal reduct, namely itself. This implication is not a claim
that its native-obstruction premise has been proved. -/
theorem covW_eq_apart_normal_consequences (n : Nat)
    (hnative : ∀ e, ¬ KNativeHead eqEnvT n apartCtx apartRec e) :
    CovVNativeHead eqEnvT n apartCtx apartRec ∧
    ∀ l, ¬ RedR (WhStepCK2 eqEnvT n) apartCtx apartRec (.sort l) := by
  have hn := (covW_eq_apart_normal_iff_no_native n).mpr hnative
  refine ⟨⟨apartRec, .refl _, hn⟩, ?_⟩
  intro l hr
  exact Expr.noConfusion (covW_normal_redR_eq hn hr)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CALL_BOUNDARY_ROOTS
#print axioms covW_normal_redR_eq
#print axioms covW_indexed_occurrence_not_free
#print axioms covW_indexed_rec_spine_not_free
#print axioms covW_indexed_delta_not_free
#print axioms covW_indexed_schema_not_free
#print axioms covW_indexed_eligible_spine_not_free
#print axioms covW_eq_eligible_indexed
#print axioms covW_eq_prefix_only_bot
#print axioms covW_eq_prefix_no_lambda
#print axioms covW_eq_prefix_observation_iff
#print axioms covW_eq_apart_raw_observed
#print axioms covW_eq_apart_prefix_raw_observed
#print axioms covWEqApartWitness
#print axioms covW_eq_apart_guard_rejected
#print axioms covW_eq_apart_raw_guarded_control
#print axioms covW_eq_apart_normal_iff_no_native
#print axioms covW_eq_apart_normal_consequences
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CALL_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
