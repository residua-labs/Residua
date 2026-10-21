import rcic.RcicNativeTypedModelCovNormCov2
import rcic.RcicNativeTypedModelCovNormConstCases
import rcic.RcicNativeTypedModelCovRelFundApp

/-!
# The exact native remainder of rigid-spine application

`convArgsT_snoc` already extends the declared telescope. Its inputs are an
actual residual Pi of `instTelescope` and argument conversion at that domain.
The native substitution package supplies conversion at the application's
derivation domain instead. The remaining alignment, extended normality and
new family saturation gate are recorded below without assuming a relation
or model-typing conclusion.

The assembly theorem is conditional on that explicit native port. It does
not derive the port from `C2` or from the child motives. An actual `C2` Pi
typing does supply rigidity and hence extended CK2 normality, but its
semantic `peelPi` data concerns compact arguments, whereas `SpineClauseS`
only gives a lower bound on the number of native arguments. No alignment
between those two telescopes is asserted here.

The final Nat control inhabits both genuine child motives, all native
typings, the model environment guard, the actual observations, and the
extended non-bottom spine. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormAppAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelAudit.TypingFin
open ReadbackCKAudit ReadbackCK2Audit
open TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelBoundaryAudit TypedModelCovRelRealizationAudit
open TypedModelCovNormCov2Audit
open TypedModelCovNormTyCasesAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- The remaining native data at a chosen pair of head readbacks. The
right saturation length is supplied by imported `ConvArgsT` length equality
after extension; it is not a separate hypothesis. -/
structure CovSpineAppNativeAt (E : ResolvedEnv) (R : Readback) (n : Nat)
    (Δ : LCtx) (r : Nat) (m : CheckedMember) (ls ls' : List Level)
    (xs xs' : List (Expr Nat)) (A T x y : Expr Nat) : Prop where
  domain : ∃ D B, instTelescope (instantiateLevels ls m.mtype) xs = .pi D B ∧
    Nonempty (TyConvT E n Δ A D)
  normalL : NormalR R Δ (foldApps (.const r ls) (xs ++ [x]))
  normalR : NormalR R Δ (foldApps (.const r ls') (xs' ++ [y]))
  family : (∃ l, RedR R Δ T (.sort l)) → m.mclass = .inductiveM →
    (xs ++ [x]).length = (piDomsOf m.mtype).length ∧
      (∃ w, Nonempty (HasTyT E n Δ (foldApps (.const r ls) (xs ++ [x])) (.sort w))) ∧
      (∃ w', Nonempty (HasTyT E n Δ (foldApps (.const r ls') (xs' ++ [y])) (.sort w')))

/-- An actual rigid head, together with environment admission, rules out
both ordinary context steps and every extra CK2 saturated-rec source. -/
theorem normalR_rigidSpineCK2 (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : RigidConst E r)
    (Δ : LCtx) (ls : List Level) (xs : List (Expr Nat)) :
    NormalR (WhStepCK2 E n) Δ (foldApps (.const r ls) xs) := by
  obtain ⟨hb, hnrec⟩ := hr m hm
  have hbody : m.body = none :=
    hb.elim id (ctorNoBody_of_envWfT hW r m hm)
  intro e hs
  rcases whStepCK2_ctx_or_saturated hs with hs | hs
  · exact whStepRecCtx_rigidNonRec_false hm hbody hnrec ls xs
      (whStepCtx_to_whStepRecCtx hs)
  · exact hnrec (saturatedRecSource_spine hm hs).1

/-- This discharges only normality, and requires an actual compact Pi
typing. Such a typing is not manufactured from a child relation motive. -/
theorem normalR_spine_of_C2_pi (hW : EnvWfT E)
    {r : Nat} {args : List CptT} {a : CptT} {g : List (List CptT × CptT)}
    (hc : (C2 E).ty (.spine r args) (.pi a g))
    (Δ : LCtx) (ls : List Level) (xs : List (Expr Nat)) :
    NormalR (WhStepCK2 E n) Δ (foldApps (.const r ls) xs) := by
  change CTyCov2 E (.spine r args) (.pi a g) at hc
  rw [CTyCov2] at hc
  obtain ⟨_, m, _, hm, hr, _⟩ := hc
  exact normalR_rigidSpineCK2 hW hm hr Δ ls xs

/-- Assemble one extended spine using the landed telescope-extension and
native conversion-transport lemmas. No type realization is an input. -/
theorem lrSCoreCov_spine_snoc_of_native (C : CovTyping E) (hL : ReadbackLaws E R)
    {Δ : LCtx} {r : Nat} {m : CheckedMember} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {args : List CptT} {u : CptT}
    {f f' A T x y : Expr Nat}
    (hm : E.members r = some m)
    (hf : RedR R Δ f (foldApps (.const r ls) xs))
    (hf' : RedR R Δ f' (foldApps (.const r ls') xs'))
    (hls : eqNList ls ls') (hlen : args.length ≤ xs.length)
    (hlen' : args.length ≤ xs'.length)
    (hargs : ConvArgsT E n Δ (instantiateLevels ls m.mtype) xs xs')
    (hxy : ConvT E n Δ x y A)
    (hN : CovSpineAppNativeAt E R n Δ r m ls ls' xs xs' A T x y) :
    LRSCoreCov C R n Δ (.app f x) (.app f' y) T (.spine r (args ++ [u])) := by
  obtain ⟨D, B, hpi, ⟨hAD⟩⟩ := hN.domain
  have hext := convArgsT_snoc hargs hpi (convT_of_tyConv hxy hAD)
  rw [lrSCoreCov_spine_iff]
  refine ⟨m, ls, ls', xs ++ [x], xs' ++ [y], hm, ?_, ?_,
    hN.normalL, hN.normalR, hls, ?_, ?_, hext, ?_⟩
  · simpa only [foldApps_snoc] using redR_appHead hL hf
  · simpa only [foldApps_snoc] using redR_appHead hL hf'
  · simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hlen 1
  · simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hlen' 1
  · intro hsort hind
    obtain ⟨hlen, hty, hty'⟩ := hN.family hsort hind
    exact ⟨hlen, (convArgsT_length_eq hext).symm.trans hlen, hty, hty'⟩

/-- The exact pointwise shape of `CovAppResiduals.spine`, conditional on the
native port at the head witnesses furnished by the genuine function child.
The argument's native derivation and related substitution supply its common
native conversion. Its recursive relation motive supplies no declared-domain
alignment, and is not an unused premise of this theorem. -/
theorem covAppSpine_of_native_port (C : CovTyping E) (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Ξ Γ Δ : LCtx} {f a A B : Expr Nat}
    (hΓ : CtxWfT E n Γ) (ha : HasTyT E n Γ a A)
    (ihf : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ f (.pi A B))
    {ρ ρ' : EnvT} {σ σ' : SubstT} (hΔ : CtxWfT E n Δ)
    (hS : RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ)
    (r : Nat) (args : List CptT) (u : CptT)
    (ho : (ApproxTK E n Ξ ρ f (.spine r args) ∧ ApproxTK E n Ξ ρ a u) ∨
      (ApproxTK E n Ξ ρ' f (.spine r args) ∧ ApproxTK E n Ξ ρ' a u))
    (hN : ∀ (m : CheckedMember) (ls ls' : List Level) (xs xs' : List (Expr Nat)),
      E.members r = some m →
      RedR R Δ (substT σ f) (foldApps (.const r ls) xs) →
      RedR R Δ (substT σ' f) (foldApps (.const r ls') xs') →
      NormalR R Δ (foldApps (.const r ls) xs) →
      NormalR R Δ (foldApps (.const r ls') xs') → eqNList ls ls' →
      args.length ≤ xs.length → args.length ≤ xs'.length →
      ConvArgsT E n Δ (instantiateLevels ls m.mtype) xs xs' →
      CovSpineAppNativeAt E R n Δ r m ls ls' xs xs'
        (substT σ A) (substT σ (instantiate0 a B)) (substT σ a) (substT σ' a)) :
    LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a))
      (substT σ (instantiate0 a B)) (.spine r (args ++ [u])) := by
  have hf := ihf hΔ hS (.spine r args)
    (ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  rw [lrSCoreCov_spine_iff] at hf
  obtain ⟨m, ls, ls', xs, xs', hm, hf, hf', hn, hn', hls, hl, hl', hs, _⟩ := hf
  obtain ⟨_, _, ⟨hxy⟩⟩ := hS.nativeInstances hW hcl hst hι hΓ hΔ ha
  exact lrSCoreCov_spine_snoc_of_native C hL hm hf hf' hls hl hl' hs hxy
    (hN m ls ls' xs xs' hm hf hf' hn hn' hls hl hl' hs)

/-- The missing port is concrete for the successor's empty prefix and the
native zero argument. Both normality proofs are imported constructor facts. -/
theorem covSpineAppNativeAt_natSucc_zero (n : Nat) (Δ : LCtx) :
    CovSpineAppNativeAt natEnvU (WhStepCK2 natEnvU n) n Δ 2 natSuccMember
      [] [] [] [] (.const 0 []) (.const 0 []) (.const 1 []) (.const 1 []) := by
  have hn := normalR_ctorSpineCK2 (n := n) natEnvUWfT
    (rfl : natEnvU.members 2 = some natSuccMember) rfl Δ [] [.const 1 []]
  refine ⟨⟨.const 0 [], .const 0 [], rfl, ⟨.refl Δ (.const 0 [])⟩⟩, hn, hn, ?_⟩
  intro _ hind
  exact MemberClass.noConfusion hind

/-- The zero child has a genuine spine relation in every target context. -/
theorem lrSCoreCov_natZero_spine (C : CovTyping natEnvU) (n : Nat) (Δ : LCtx) :
    LRSCoreCov C (WhStepCK2 natEnvU n) n Δ (.const 1 []) (.const 1 [])
      (.const 0 []) (.spine 1 []) := by
  rw [lrSCoreCov_spine_iff]
  have hn := normalR_ctorSpineCK2 (n := n) natEnvUWfT
    (rfl : natEnvU.members 1 = some natZeroMember) rfl Δ [] []
  refine ⟨natZeroMember, [], [], [], [], rfl, .refl _, .refl _,
    hn, hn, ?_, by decide, by decide, .nil _, ?_⟩
  · trivial
  · intro _ hind
    exact MemberClass.noConfusion hind

/-- The successor child motive is proved for every actual observation and
every related substitution, rather than supplied as a hypothesis. -/
theorem fundTyAtCov_natSucc (C : CovTyping natEnvU) (n : Nat) (Ξ Γ : LCtx) :
    FundTyAtCov C (ctxModelT_approxTK natEnvU n Ξ) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) := by
  exact fundCov_const_of_spineInput (C := C) (Γ := Γ)
    (rfl : natEnvU.members 2 = some natSuccMember)
    (covConstSpineInput_ctor (n := n) (Ξ := Ξ) natEnvUWfT
      (ls := []) (rfl : natEnvU.members 2 = some natSuccMember)
      rfl rigidConst_natEnvU_succ)

/-- The zero child motive is also inhabited, including both valuation sides. -/
theorem fundTyAtCov_natZero (C : CovTyping natEnvU) (n : Nat) (Ξ Γ : LCtx) :
    FundTyAtCov C (ctxModelT_approxTK natEnvU n Ξ) (WhStepCK2 natEnvU n) n Γ
      (.const 1 []) (.const 0 []) := by
  exact fundCov_const_of_spineInput (C := C) (Γ := Γ)
    (rfl : natEnvU.members 1 = some natZeroMember)
    (covConstSpineInput_ctor (n := n) (Ξ := Ξ) natEnvUWfT
      (ls := []) (rfl : natEnvU.members 1 = some natZeroMember)
      rfl rigidConst_natEnvU_zero)

/-- The declared telescope is actually extended at the positive call. The
compact argument contributes its length; native conversion comes from zero's
actual typing derivation. -/
theorem lrSCoreCov_natSucc_zero_spine (C : CovTyping natEnvU) (n : Nat)
    (Δ : LCtx) (u : CptT) :
    LRSCoreCov C (WhStepCK2 natEnvU n) n Δ
      (.app (.const 2 []) (.const 1 [])) (.app (.const 2 []) (.const 1 []))
      (.const 0 []) (.spine 2 [u]) := by
  exact lrSCoreCov_spine_snoc_of_native C (readbackLaws_whStepCK2 natEnvU n)
    (args := []) (u := u) (xs := []) (xs' := [])
    (rfl : natEnvU.members 2 = some natSuccMember) (.refl _) (.refl _)
    (by trivial) (by decide) (by decide) (.nil _)
    (.refl Δ (.const 1 []) (.const 0 []) (hasTyT_natEnvU_zero n Δ))
    (covSpineAppNativeAt_natSucc_zero n Δ)

/-- A full non-bottom Nat application control at the actual `C2` and
`ApproxTK`, with both genuine native children and their proved motives. -/
theorem natSucc_zero_C2_spine_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] (.app (.const 2 []) (.const 1 [])) (.const 0 [])) ∧
    FundTyAtCov (C2 natEnvU) (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n)
      n [] (.const 2 []) (.pi (.const 0 []) (.const 0 [])) ∧
    FundTyAtCov (C2 natEnvU) (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n)
      n [] (.const 1 []) (.const 0 []) ∧
    EnvTypedCovAtP (C2 natEnvU) (ctxModelT_approxTK natEnvU n []) [] ρ ∧
    ApproxTK natEnvU n [] ρ (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] ρ (.const 1 []) (.spine 1 []) ∧
    ApproxTK natEnvU n [] ρ (.app (.const 2 []) (.const 1 [])) (.spine 2 [.spine 1 []]) ∧
    ApproxTK natEnvU n [] ρ (.const 0 []) (.spine 0 []) ∧
    (C2 natEnvU).ty (.spine 2 [.spine 1 []]) (.spine 0 []) ∧
    LRSCoreCov (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.app (.const 2 []) (.const 1 [])) (.app (.const 2 []) (.const 1 []))
      (.const 0 []) (.spine 2 [.spine 1 []]) ∧
    (.spine 2 [.spine 1 []] : CptT) ≠ .bot ∧ (.spine 0 [] : CptT) ≠ .bot := by
  have hf : ApproxTK natEnvU n [] ρ (.const 2 []) (.spine 2 []) :=
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine ρ)
  have hz : ApproxTK natEnvU n [] ρ (.const 1 []) (.spine 1 []) :=
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero)
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨hasTyT_natEnvU_succ n []⟩,
    ⟨hasTyT_natEnvU_zero n []⟩, ⟨?native⟩,
    fundTyAtCov_natSucc (C2 natEnvU) n [] [], fundTyAtCov_natZero (C2 natEnvU) n [] [],
    envTypedCovAtP_nil (C2 natEnvU) _ ρ, hf, hz, .appSpine hf hz,
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat), ?typing,
    lrSCoreCov_natSucc_zero_spine (C2 natEnvU) n [] (.spine 1 []),
    (fun h => CptT.noConfusion h), (fun h => CptT.noConfusion h)⟩
  case native =>
    exact .app [] (.const 2 []) (.const 1 []) (.const 0 []) (.const 0 [])
      (hasTyT_natEnvU_succ n []) (hasTyT_natEnvU_zero n [])
  case typing =>
    change CTyCov2 natEnvU (.spine 2 [.spine 1 []]) (.spine 0 [])
    rw [CTyCov2]
    exact Or.inr ⟨⟨2, [.spine 1 []], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_APP_ROOTS
#print axioms CovSpineAppNativeAt
#print axioms normalR_rigidSpineCK2
#print axioms normalR_spine_of_C2_pi
#print axioms lrSCoreCov_spine_snoc_of_native
#print axioms covAppSpine_of_native_port
#print axioms covSpineAppNativeAt_natSucc_zero
#print axioms lrSCoreCov_natZero_spine
#print axioms fundTyAtCov_natSucc
#print axioms fundTyAtCov_natZero
#print axioms lrSCoreCov_natSucc_zero_spine
#print axioms natSucc_zero_C2_spine_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_APP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormAppAudit
