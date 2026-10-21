import rcic.RcicNativePiCycleKOrder
import rcic.RcicNativePiProbeAlgebra
import rcic.RcicNativePiProbeComputation
import rcic.RcicNativePiModelDeltaIotaTerm

/-!
# The K readback: exact normal uniqueness fails, compatible Pi probes survive

The landed `WhStepRecK` counterexample embeds in `WhStepK`.  Its source is
typed below by composing the existing mixed-And minor typing with typed
inversion, beta, Pi congruence and endpoint validity.  Thus the failure of
`NormalUniqueR (WhStepK andEnvU 0)` is present on an admitted typed example.

The two unequal Pi normal forms have natively convertible components and
inhabit the exact typed probe.  Their inequality therefore refutes the
strong uniqueness premise, not `PiProbeLinkT` or Pi injectivity.  Ordinary
native iota has a K readback step; direct sort-indexed irrelevance needs
the separately named exclusion of `HasTyT (Sort u) (Sort 0)`.

No arbitrary K-step subject reduction, raw Pi-readback coherence, or
single-link fundamental lemma is claimed.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeKObstructionAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiCycleAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ## Inclusion of the landed reduction witness -/

/-- `recArg` includes the saturated recursor-major context step. -/
theorem whStepK_of_whStepRecCtx {Γ : LCtx} {a b : Expr Nat}
    (h : WhStepRecCtx E Γ a b) : WhStepK E n Γ a b := by
  induction h with
  | beta A body arg => exact .ctx (.beta A body arg)
  | zeta A value body => exact .ctx (.zeta A value body)
  | zetaLocal hv => exact .ctx (.zetaLocal hv)
  | delta hm hb => exact .ctx (.delta hm hb)
  | iota hI => exact .ctx (.iota hI)
  | lit t => exact .ctx (.lit t)
  | appHead _ ih => exact .appHead ih
  | recMajor hm hrec _ _ ih =>
      simpa only [foldApps_snoc] using WhStepK.recArg hm hrec ih

/-- All constructors of the landed K witness embed in the current K readback.
The reverse inclusion is not asserted: `recArg` has no saturation premise. -/
theorem whStepK_of_whStepRecK {Γ : LCtx} {a b : Expr Nat}
    (h : WhStepRecK E n Γ a b) : WhStepK E n Γ a b := by
  induction h with
  | recCtx hs => exact whStepK_of_whStepRecCtx hs
  | pmajor hI hP hc hx => exact .pmajor hI hP hc hx
  | appHead _ ih => exact .appHead ih
  | recMajor hm hrec _ _ ih =>
      simpa only [foldApps_snoc] using WhStepK.recArg hm hrec ih

theorem redR_whStepK_of_whRedRecK {Γ : LCtx} {a b : Expr Nat}
    (h : WhRedRecK E n Γ a b) : RedR (WhStepK E n) Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (whStepK_of_whStepRecK hs) ih

theorem andPiNF1_readback :
    RedR (WhStepK andEnvU 0) mixAndCtx andNonUniquePiRedex andPiNF1 :=
  redR_whStepK_of_whRedRecK whRedRecK_andNonUniquePi_nf1

theorem andPiNF2_readback :
    RedR (WhStepK andEnvU 0) mixAndCtx andNonUniquePiRedex andPiNF2 :=
  redR_whStepK_of_whRedRecK whRedRecK_andNonUniquePi_nf2

theorem andPiNF1_normal : NormalR (WhStepK andEnvU 0) mixAndCtx andPiNF1 :=
  fun _ hs => whStepK_pi_false hs

theorem andPiNF2_normal : NormalR (WhStepK andEnvU 0) mixAndCtx andPiNF2 :=
  fun _ hs => whStepK_pi_false hs

theorem not_normalUniqueR_whStepK_andEnvU :
    ¬ NormalUniqueR (WhStepK andEnvU 0) :=
  fun h => andPiNF1_ne_andPiNF2
    (h mixAndCtx andPiNF1_readback andPiNF1_normal andPiNF2_readback andPiNF2_normal)

/-! ## Actual native typing of the existing source -/

private abbrev andMinorType : Expr Nat :=
  .pi (.bvar 4) (.pi (.bvar 4) (.app (lift 0 2 mixAndMot) mixAndMkTel))

/-- Replace the original minor's Pi domain by its typed beta expansion.
The original minor's annotation conversions come from typed inversion;
none of its private typing proof is copied. -/
noncomputable def andDepPiMinTy :
    HasTyT andEnvU 0 mixAndCtx andDepPiMin andMinorType := by
  obtain ⟨u, B, hA, hInner, hcOuter⟩ := hasTyTInv_lam mixAndMinTy rfl
  obtain ⟨v, C, hA', hPi, hcInner⟩ := hasTyTInv_lam hInner rfl
  obtain ⟨w, z, hDom, hCod, hcPi⟩ := hasTyTInv_pi hPi rfl
  let ΓX : LCtx := .assumption (.bvar 4) :: mixAndCtx
  let ΓXY : LCtx := .assumption (.bvar 4) :: ΓX
  have hΓX : CtxWfT andEnvU 0 ΓX :=
    .assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf hA
  have hΓXY : CtxWfT andEnvU 0 ΓXY := .assumption _ _ _ hΓX hA'
  have hProp : HasTyT andEnvU 0 ΓXY (.bvar 5) (.sort .zero) := .bvar _ 5 _ rfl
  have hArg : HasTyT andEnvU 0 ΓXY (.bvar 0) (.bvar 5) := .bvar _ 0 _ rfl
  have hBody : HasTyT andEnvU 0 (.assumption (.bvar 5) :: ΓXY)
      (.sort .zero) (.sort w) := by
    simpa only [insertAt, lift] using
      hasTyTWeaken (.assumption (.bvar 5)) (envClosed_of_envWfT andEnvUWfT)
        (c := 0) hDom
  have hBeta : ConvT andEnvU 0 ΓXY
      (.app (.lam (.bvar 5) (.sort .zero)) (.bvar 0)) (.sort .zero) (.sort w) :=
    .beta _ _ _ _ _ .zero hProp hBody hArg
  have hPiConv : ConvT andEnvU 0 ΓXY mixPi andDepPiBody (.sort (.imax w z)) :=
    .pi _ _ _ _ _ w z (.symm _ _ _ _ hBeta) (.refl _ _ _ hCod)
  have hNewPi : HasTyT andEnvU 0 ΓXY andDepPiBody C :=
    hasTyT_of_tyConvT (convEnds andEnvUWfT hΓXY hPiConv).2.1 hcPi
  have hNewInner : HasTyT andEnvU 0 ΓX (.lam (.bvar 4) andDepPiBody) B :=
    hasTyT_of_tyConvT (.lam _ _ v _ _ hA' hNewPi) hcInner
  exact hasTyT_of_tyConvT (.lam _ _ u _ _ hA hNewInner) hcOuter

/-- The source really is a type in the admitted mixed-And context. -/
noncomputable def andNonUniquePiRedexTy :
    HasTyT andEnvU 0 mixAndCtx andNonUniquePiRedex (.sort (.succ .zero)) := by
  have hpre : HasTyT andEnvU 0 mixAndCtx
      (foldApps (.const 2 [.succ (.succ .zero)])
        [.bvar 4, .bvar 3, mixAndMot, andDepPiMin])
      (.pi mixAndFamApp (.app (lift 0 1 mixAndMot) (.bvar 0))) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.const _ 2 [.succ (.succ .zero)] andRecMemberU rfl rfl rfl)
            mixTyA)
          mixTyB)
        mixAndMotTy)
      andDepPiMinTy
  have hsource : HasTyT andEnvU 0 mixAndCtx andNonUniquePiRedex
      (.app mixAndMot (.bvar 0)) := .app _ _ _ _ _ hpre mixTyH
  exact .conv _ _ _ _ _ hsource
    (.beta _ _ _ _ _ .zero mixAndFamTy (.sort _ (.succ .zero)) mixTyH)

noncomputable def andPiNF1Ty : HasTyT andEnvU 0 mixAndCtx andPiNF1
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ _ _ _ _ (.app _ _ _ _ _ hasTyT_andConstSortLam mixTyY) (.sort _ .zero)

noncomputable def andPiNF2Ty : HasTyT andEnvU 0 mixAndCtx andPiNF2
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ _ _ _ _ (.app _ _ _ _ _ hasTyT_andConstSortLam mixTyY2) (.sort _ .zero)

/-- The counterexample includes admitted environment, context, source typing,
both typed Pi endpoints, both normal readbacks and their strict inequality. -/
theorem typed_normalUniqueR_counterexample :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
    Nonempty (HasTyT andEnvU 0 mixAndCtx andNonUniquePiRedex (.sort (.succ .zero))) ∧
    Nonempty (HasTyT andEnvU 0 mixAndCtx andPiNF1
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    Nonempty (HasTyT andEnvU 0 mixAndCtx andPiNF2
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    RedR (WhStepK andEnvU 0) mixAndCtx andNonUniquePiRedex andPiNF1 ∧
    NormalR (WhStepK andEnvU 0) mixAndCtx andPiNF1 ∧
    RedR (WhStepK andEnvU 0) mixAndCtx andNonUniquePiRedex andPiNF2 ∧
    NormalR (WhStepK andEnvU 0) mixAndCtx andPiNF2 ∧ andPiNF1 ≠ andPiNF2 :=
  ⟨⟨andEnvUWfT⟩, ⟨Rcic.Domain.Model.PiInversion.mixAndCtx_wf⟩,
    ⟨andNonUniquePiRedexTy⟩, ⟨andPiNF1Ty⟩, ⟨andPiNF2Ty⟩,
    andPiNF1_readback, andPiNF1_normal, andPiNF2_readback, andPiNF2_normal,
    andPiNF1_ne_andPiNF2⟩

/-! ## The same unequal normals are compatible at the actual typed probe -/

/-- Native Pi congruence lifts the landed proof-irrelevance conversion of
the domains.  The sort-indexed derivation contains an `irr` subtree. -/
noncomputable def andPiNormalsConv : ConvT andEnvU 0 mixAndCtx andPiNF1 andPiNF2
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ _ _ _ _ _ _ convT_andPiNF1_dom_andPiNF2 (.refl _ _ _ (.sort _ .zero))

theorem andPiNormals_components :
    Nonempty (TyConvT andEnvU 0 mixAndCtx
      (.app andConstSortLam (.bvar 1)) (.app andConstSortLam mixProofY2)) ∧
    Nonempty (TyConvT andEnvU 0
      (.assumption (.app andConstSortLam (.bvar 1)) :: mixAndCtx)
      (.sort .zero) (.sort .zero)) :=
  ⟨⟨tyConvT_andPiNF1_dom_andPiNF2⟩, ⟨.refl _ _⟩⟩

/-- The concrete nonunique pair passes the exact `pi bot []` typed probe.
This statement uses no `NormalUniqueR` premise. -/
theorem andPiNormals_probe {u : Level} :
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx andPiNF1 andPiNF2
      (.sort u) (.pi .bot []) := by
  rw [LRSCoreT.eq_def]
  exact ⟨⟨u, .refl _⟩,
    .app andConstSortLam (.bvar 1), .sort .zero,
    .app andConstSortLam mixProofY2, .sort .zero, .refl _, .refl _,
    ⟨.assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf
      (.app _ _ _ _ _ hasTyT_andConstSortLam mixTyY)⟩,
    andPiNormals_components.1, andPiNormals_components.2,
    ⟨.zero, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- Readback expansion gives a self-related typed source using the two
different compatible Pi witnesses. -/
theorem andNonUniquePiRedex_probe {u : Level} :
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx
      andNonUniquePiRedex andNonUniquePiRedex (.sort u) (.pi .bot []) :=
  piProbe_typed_iff.mpr
    (lrSCore_expand (readbackLaws_whStepK andEnvU 0)
      andPiNF1_readback andPiNF2_readback (.pi .bot [])
      (piProbe_typed_iff.mp andPiNormals_probe))

/-! ## The native iota and irrelevance boundaries at a sort index -/

/-- Legacy native iota is directly included in the union-iota K readback. -/
theorem whStepK_of_native_iota {Γ : LCtx} {lhs rhs : Expr Nat}
    (hI : DerivedIota E lhs rhs) : WhStepK E n Γ lhs rhs :=
  .ctx (.iota (derivedIotaU_ofDerivedIota hI))

/-- A probe already realized by the iota contractum expands to the source.
Forward preservation from an arbitrary source witness is a distinct claim. -/
theorem piProbe_native_iota_expand {Γ : LCtx} {lhs rhs : Expr Nat} {u : Level}
    (hI : DerivedIota E lhs rhs)
    (h : LRSCoreT (WhStepK E n) E n Γ rhs rhs (.sort u) (.pi .bot [])) :
    LRSCoreT (WhStepK E n) E n Γ lhs rhs (.sort u) (.pi .bot []) :=
  piProbe_typed_iff.mpr
    (lrSCore_expand (readbackLaws_whStepK E n)
      (.step (whStepK_of_native_iota hI) (.refl _)) (.refl _) (.pi .bot [])
      (piProbe_typed_iff.mp h))

/-- The exact one-sided link for the symmetric native iota conversion.
It is supplied by readback expansion and landed probe symmetry. -/
theorem piProbe_native_iota_symm_link (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs : Expr Nat} {u : Level}
    (hI : DerivedIota E lhs rhs)
    (h : LRSCoreT (WhStepK E n) E n Γ rhs rhs (.sort u) (.pi .bot [])) :
    LRSCoreT (WhStepK E n) E n Γ rhs lhs (.sort u) (.pi .bot []) :=
  piProbe_symmT hW hΓ (piProbe_native_iota_expand hI h)

/-- Expansion transports both observations from the contractum to the
source, retaining the specified Pi components literally. -/
theorem native_iota_reverse_transport {Γ : LCtx} {lhs rhs : Expr Nat}
    (hI : DerivedIota E lhs rhs) :
    ProbeTransportT (WhStepK E n) E n Γ rhs lhs := by
  constructor
  · rintro ⟨u, hr⟩
    exact ⟨u, .step (whStepK_of_native_iota hI) hr⟩
  · intro A B hr _
    exact ⟨A, B, .step (whStepK_of_native_iota hI) hr,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩⟩

/-- Unresolved local obligation for the selected, actually typed native
iota node.  Every source sort observation and every specified source Pi
observation must survive this chosen contraction.  This definition is
not a supplied model-invariance or K-soundness fact. -/
def NativeIotaForwardAtT {Γ : LCtx} {lhs rhs T : Expr Nat}
    (_hI : DerivedIota E lhs rhs) (_hlhs : HasTyT E n Γ lhs T)
    (_hrhs : HasTyT E n Γ rhs T) : Prop :=
  ProbeTransportT (WhStepK E n) E n Γ lhs rhs

/-- Bidirection adds no unproved iota obligation: its reverse half is
the expansion theorem above.  Only the selected forward half remains. -/
theorem native_iota_motive_iff_forward {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hI : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T)
    (hrhs : HasTyT E n Γ rhs T) :
    ConvProbeMotiveT (WhStepK E n) (.iota Γ lhs rhs T hI hlhs hrhs) ↔
      NativeIotaForwardAtT hI hlhs hrhs :=
  ⟨fun h => h.1, fun h => ⟨h, native_iota_reverse_transport hI⟩⟩

/-- The strengthened iota residual includes forward sort transport in
addition to specified-Pi transport.  It is not merely the Pi clause. -/
theorem native_iota_forward_iff_sort_and_pi {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hI : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T)
    (hrhs : HasTyT E n Γ rhs T) :
    NativeIotaForwardAtT hI hlhs hrhs ↔
      SortReadTransportT (WhStepK E n) Γ lhs rhs ∧
      PiReadTransportT (WhStepK E n) E n Γ lhs rhs :=
  ⟨fun h => ⟨h.sorts, h.pis⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ### An active typed iota control, with its precise limited scope -/

private def mixAndMotiveAtCtorSort : ConvT andEnvU 0 mixAndCtx
    (.app mixAndMot mixAndMkApp) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  .beta _ _ _ _ _ .zero mixAndFamTy (.sort _ (.succ .zero)) mixAndMkTy

def mixAndIotaLhsSortTy :
    HasTyT andEnvU 0 mixAndCtx mixAndLhs (.sort (.succ .zero)) :=
  .conv _ _ _ _ _ mixAndLhsTy mixAndMotiveAtCtorSort

def mixAndIotaRhsSortTy :
    HasTyT andEnvU 0 mixAndCtx mixAndRhs (.sort (.succ .zero)) :=
  .conv _ _ _ _ _ mixAndRhsTy mixAndMotiveAtCtorSort

/-- A literal native iota node, with both endpoints typed at a sort. -/
def mixAndIotaAtSort : ConvT andEnvU 0 mixAndCtx mixAndLhs mixAndRhs
    (.sort (.succ .zero)) :=
  .iota _ _ _ _ (.of mixAndW) mixAndIotaLhsSortTy mixAndIotaRhsSortTy

theorem mixAnd_iota_rhs_readback :
    RedR (WhStepK andEnvU 0) mixAndCtx mixAndRhs mixPi :=
  .step (.ctx (.appHead (.beta _ _ _)))
    (.step (.ctx (.beta _ _ _)) (.refl _))

theorem mixAnd_iota_rhs_probe {u : Level} :
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndRhs mixAndRhs
      (.sort u) (.pi .bot []) :=
  piProbe_typed_iff.mpr
    (lrSCore_expand (readbackLaws_whStepK andEnvU 0)
      mixAnd_iota_rhs_readback mixAnd_iota_rhs_readback (.pi .bot [])
      (diag_pi_probe (.assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf
        (.sort _ .zero)) u))

theorem mixAnd_iota_probe {u : Level} :
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndLhs mixAndRhs
      (.sort u) (.pi .bot []) :=
  piProbe_native_iota_expand (.of mixAndW) mixAnd_iota_rhs_probe

/-- The original existential Pi-link condition is inhabited on this
selected native iota node.  This does not assert transport of every
specified source Pi witness, nor exclude every source sort observation. -/
theorem mixAnd_iota_pi_link {u : Level} :
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndLhs mixAndLhs
      (.sort u) (.pi .bot []) →
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndLhs mixAndRhs
      (.sort u) (.pi .bot []) :=
  fun _ => mixAnd_iota_probe

/-- The successful local link has an actual typed iota derivation and
an inhabited input diagonal.  The stronger `NativeIotaForwardAtT` port
is not claimed here: all K paths from the source have not been classified. -/
theorem mixAnd_iota_pi_link_nonvacuity :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
    Nonempty (ConvT andEnvU 0 mixAndCtx mixAndLhs mixAndRhs (.sort (.succ .zero))) ∧
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndLhs mixAndLhs
      (.sort (.succ .zero)) (.pi .bot []) ∧
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndLhs mixAndRhs
      (.sort (.succ .zero)) (.pi .bot []) :=
  ⟨⟨andEnvUWfT⟩, ⟨Rcic.Domain.Model.PiInversion.mixAndCtx_wf⟩,
    ⟨mixAndIotaAtSort⟩, piProbe_left_diagonalT mixAnd_iota_probe,
    mixAnd_iota_pi_link (piProbe_left_diagonalT mixAnd_iota_probe)⟩

/-! ### A canonical True iota source inhabits the whole local port -/

private theorem true_constructor_pin {c : Nat} {m : CheckedMember}
    (hm : trueEnvU.members c = some m) (hk : m.mclass = .constructorM) :
    c = 1 ∧ m = trueIntroMember := by
  rcases trueEnvU_mem hm with ⟨hr, hmem⟩ | ⟨hr, hmem⟩ | ⟨hr, hmem⟩
  · rw [hmem] at hk
    cases hk
  · exact ⟨hr, hmem⟩
  · rw [hmem] at hk
    cases hk

/-- The canonical constructor is field-free.  Replacing a witness's
constructor universe list leaves its right side unchanged, so the landed
union-iota determinism theorem identifies every selected minor. -/
private theorem true_iota_rhs_eq {u : Level} {motive minor canon rhs : Expr Nat}
    (hI : DerivedIotaU trueEnvU
      (recCall (.const 2 [u]) [motive, minor] canon) rhs) : rhs = minor := by
  generalize hsource : recCall (.const 2 [u]) [motive, minor] canon = source at hI
  cases hI with
  | ofU w =>
      obtain ⟨hctorR, hctorM⟩ := true_constructor_pin w.hctor w.hctorK
      have hsum := w.hnpar
      rw [hctorM] at hsum
      change w.nparams + w.fields.length = 0 at hsum
      have hfields : w.fields = [] := List.length_eq_zero.mp (by omega)
      have hparams : w.ctorParams = [] := List.length_eq_zero.mp (by
        have h := w.hctorParams
        omega)
      have hprefix : foldApps (.const 2 [u]) [motive, minor] =
          foldApps (.const w.recRef w.ls) w.preMajor := by
        simp only [iotaLhsOf, recCall, foldApps_snoc] at hsource
        exact (Expr.app.inj hsource).1
      let w' : IotaWitness trueEnvU := { w with lsC := [] }
      have hcanonical : iotaLhsOf w' =
          iotaLhsOf (trueRecWitness u motive minor) := by
        calc
          iotaLhsOf w' =
              .app (foldApps (.const w.recRef w.ls) w.preMajor) (.const 1 []) := by
            simp only [iotaLhsOf, w', ctorMajor, ctorSpine, recCall,
              foldApps_snoc, hctorR, hparams, hfields, List.nil_append, foldApps]
          _ = .app (foldApps (.const 2 [u]) [motive, minor]) (.const 1 []) :=
            congrArg (fun f => Expr.app f (.const 1 [])) hprefix.symm
          _ = iotaLhsOf (trueRecWitness u motive minor) := rfl
      have hI' : DerivedIotaU trueEnvU
          (iotaLhsOf (trueRecWitness u motive minor)) (iotaRhsOf w) := by
        rw [← hcanonical]
        exact .ofU w'
      exact iotaDetU_of_envWfT trueEnvUWfT hI' (.ofU (trueRecWitness u motive minor))
  | ofUS w =>
      obtain ⟨hctorR, hctorM⟩ := true_constructor_pin w.hctor w.hctorK
      have hsum := w.hnpar
      rw [hctorM] at hsum
      change w.nparams + w.fields.length = 0 at hsum
      have hfields : w.fields = [] := List.length_eq_zero.mp (by omega)
      have hparams : w.ctorParams = [] := List.length_eq_zero.mp (by
        have h := w.hctorParams
        omega)
      have hprefix : foldApps (.const 2 [u]) [motive, minor] =
          foldApps (.const w.recRef w.ls) w.preMajor := by
        simp only [iotaLhsOfS, recCall, foldApps_snoc] at hsource
        exact (Expr.app.inj hsource).1
      let w' : IotaWitnessS trueEnvU := { w with lsC := [] }
      have hcanonical : iotaLhsOfS w' =
          iotaLhsOf (trueRecWitness u motive minor) := by
        calc
          iotaLhsOfS w' =
              .app (foldApps (.const w.recRef w.ls) w.preMajor) (.const 1 []) := by
            simp only [iotaLhsOfS, w', recCall, foldApps_snoc,
              hctorR, hparams, hfields, List.nil_append, foldApps]
          _ = .app (foldApps (.const 2 [u]) [motive, minor]) (.const 1 []) :=
            congrArg (fun f => Expr.app f (.const 1 [])) hprefix.symm
          _ = iotaLhsOf (trueRecWitness u motive minor) := rfl
      have hI' : DerivedIotaU trueEnvU
          (iotaLhsOf (trueRecWitness u motive minor)) (iotaRhsOfS w) := by
        rw [← hcanonical]
        exact .ofUS w'
      exact iotaDetU_of_envWfT trueEnvUWfT hI' (.ofU (trueRecWitness u motive minor))

private theorem trueIntro_normal {Γ : LCtx} :
    NormalR (WhStepK trueEnvU n) Γ (.const 1 []) := by
  intro X hs
  apply whStepRecCtx_ctorApp_false trueEnvUWfT (c := 1) (m := trueIntroMember)
    (ls := []) (xs := []) rfl rfl
  apply whStepCtx_to_whStepRecCtx
  apply whStepK_to_ctx_of_notConstApplication hs
  intro r ls pre x heq
  exact Expr.noConfusion heq

private theorem true_prefix_step_false {Γ : LCtx} {u : Level} {a b : Expr Nat}
    (hs : WhStepK trueEnvU n Γ a b) :
    ∀ xs : List (Expr Nat), xs.length ≤ 2 →
      (∀ x ∈ xs, NormalR (WhStepK trueEnvU n) Γ x) →
      a = foldApps (.const 2 [u]) xs → False := by
  induction hs with
  | ctx hs =>
      intro xs hlen _ heq
      apply whStepRecCtx_recursor_prefix_false trueEnvUWfT
        (r := 2) (m := trueRecMemberU) rfl rfl [u] xs
        (by change xs.length + 1 ≤ 3; omega)
      exact whStepCtx_to_whStepRecCtx (heq ▸ hs)
  | @pmajor r ls pre canon x rhs P hI _ _ _ =>
      intro xs hlen _ heq
      have hargs : pre ++ [x] = xs := (foldApps_const_inj heq).2
      have hbound := derivedIotaU_args_length_ge_three hI
      simp only [recCall, appsSpine_foldApps_const, List.length_append,
        List.length_singleton] at hbound
      have hlength := congrArg List.length hargs
      simp only [List.length_append, List.length_singleton] at hlength
      omega
  | @recArg r ls m pre x x' _ _ hs _ =>
      intro xs _ hnormal heq
      have hargs : pre ++ [x] = xs := (foldApps_const_inj heq).2
      have hx : x ∈ xs := hargs ▸ List.mem_append_right pre (List.mem_singleton_self x)
      exact hnormal x hx x' hs
  | @appHead f f' x hs ih =>
      intro xs hlen hnormal heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, y, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact ih pre (by simp only [List.length_append, List.length_singleton] at hlen; omega)
          (fun z hz => hnormal z (List.mem_append_left _ hz)) (Expr.app.inj heq).1

private theorem true_rec_step_unique {Γ : LCtx} (u : Level) (motive minor : Expr Nat)
    (hmotive : NormalR (WhStepK trueEnvU n) Γ motive)
    (hminor : NormalR (WhStepK trueEnvU n) Γ minor)
    {a b : Expr Nat} (hs : WhStepK trueEnvU n Γ a b) :
    a = recCall (.const 2 [u]) [motive, minor] (.const 1 []) → b = minor := by
  have hnormal : ∀ x ∈ [motive, minor, Expr.const 1 []],
      NormalR (WhStepK trueEnvU n) Γ x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmotive
    · exact hminor
    · exact trueIntro_normal
  cases hs with
  | ctx hs =>
      intro heq
      have hstep : WhStepCtx trueEnvU Γ
          (recCall (.const 2 [u]) [motive, minor] (.const 1 [])) minor :=
        .iota (.ofU (trueRecWitness u motive minor))
      exact (whDetCtx_of_envWfT trueEnvUWfT Γ hstep (heq ▸ hs)).symm
  | @pmajor r ls pre canon x rhs P hI _ _ _ =>
      intro heq
      simp only [recCall, foldApps_snoc] at heq
      have hprefix := (Expr.app.inj heq).1
      have hI' : DerivedIotaU trueEnvU
          (recCall (.const 2 [u]) [motive, minor] canon) b := by
        simpa only [recCall, foldApps_snoc, hprefix] using hI
      exact true_iota_rhs_eq hI'
  | @recArg r ls m pre x x' _ _ hs =>
      intro heq
      have hargs : pre ++ [x] = [motive, minor, .const 1 []] :=
        (foldApps_const_inj heq).2
      have hx : x ∈ [motive, minor, Expr.const 1 []] :=
        hargs ▸ List.mem_append_right pre (List.mem_singleton_self x)
      exact (hnormal x hx x' hs).elim
  | @appHead f f' x hs =>
      intro heq
      simp only [recCall, foldApps_snoc] at heq
      exact (true_prefix_step_false hs [motive, minor] (by simp)
        (fun z hz => hnormal z
          (show z ∈ [motive, minor, Expr.const 1 []] from
            List.mem_append_left [Expr.const 1 []] hz))
        (Expr.app.inj heq).1).elim

def truePiIotaLevel : Level := .imax (.succ .zero) (.succ .zero)

/-- A closed recursor source with a literal Pi minor. -/
def truePiIotaLhs : Expr Nat :=
  recCall (.const 2 [.succ truePiIotaLevel])
    [trueSortMotive truePiIotaLevel, mixPi] (.const 1 [])

noncomputable def truePiIotaNative : DerivedIota trueEnvU truePiIotaLhs mixPi :=
  .of (trueRecWitness (.succ truePiIotaLevel) (trueSortMotive truePiIotaLevel) mixPi)

def truePiIotaRhsTy : HasTyT trueEnvU 0 [] mixPi (.sort truePiIotaLevel) :=
  pinPiT trueEnvU 0

noncomputable def truePiIotaLhsTy :
    HasTyT trueEnvU 0 [] truePiIotaLhs (.sort truePiIotaLevel) := by
  have hminor : HasTyT trueEnvU 0 [] mixPi
      (.app (trueSortMotive truePiIotaLevel) (.const 1 [])) :=
    .conv _ _ _ _ _ truePiIotaRhsTy
      (.symm _ _ _ _ (convT_trueSortMotive_beta truePiIotaLevel))
  have hprefix : HasTyT trueEnvU 0 []
      (foldApps (.const 2 [.succ truePiIotaLevel])
        [trueSortMotive truePiIotaLevel, mixPi])
      (.pi (.const 0 []) (.app (trueSortMotive truePiIotaLevel) (.bvar 0))) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _ (.const _ 2 [.succ truePiIotaLevel] trueRecMemberU rfl rfl rfl)
        (hasTyT_trueSortMotive truePiIotaLevel)) hminor
  exact .conv _ _ _ _ _ (.app _ _ _ _ _ hprefix hasTyT_trueIntro)
    (convT_trueSortMotive_beta truePiIotaLevel)

noncomputable def truePiIotaAtSort :
    ConvT trueEnvU 0 [] truePiIotaLhs mixPi (.sort truePiIotaLevel) :=
  .iota _ _ _ _ truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy

private theorem truePiIota_contract_normal {X : Expr Nat}
    (hX : NormalR (WhStepK trueEnvU 0) [] X)
    (hr : RedR (WhStepK trueEnvU 0) [] truePiIotaLhs X) :
    RedR (WhStepK trueEnvU 0) [] mixPi X :=
  redR_contract_of_source_unique (whStepK_of_native_iota truePiIotaNative)
    (fun _ hs => true_rec_step_unique (.succ truePiIotaLevel)
      (trueSortMotive truePiIotaLevel) mixPi
      (normalR_lam _ _) (fun _ hp => whStepK_pi_false hp) hs rfl) hX hr

/-- The entire local forward port is inhabited on this canonical typed
iota node.  Both observation clauses follow for every source reading;
no global K uniqueness or coherence premise is supplied or assumed. -/
theorem truePiIotaForward :
    NativeIotaForwardAtT truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy :=
  probeTransport_of_readback_impT (readbackLaws_whStepK trueEnvU 0)
    (fun _ hX => truePiIota_contract_normal hX)

theorem truePiIota_motive : ConvProbeMotiveT (WhStepK trueEnvU 0) truePiIotaAtSort :=
  (native_iota_motive_iff_forward truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy).mpr
    truePiIotaForward

theorem truePiIota_readback : RedR (WhStepK trueEnvU 0) [] truePiIotaLhs mixPi :=
  .step (whStepK_of_native_iota truePiIotaNative) (.refl _)

/-- The complete sort arm is absent at the chosen source. -/
theorem truePiIota_no_sort_readback (u : Level) :
    ¬ RedR (WhStepK trueEnvU 0) [] truePiIotaLhs (.sort u) := by
  intro hr
  have hread := truePiIota_contract_normal (fun _ hs => whStepK_sort_false hs) hr
  exact Expr.noConfusion (redR_of_normal (fun _ hs => whStepK_pi_false hs) hread)

/-- Whole-port satisfiability, with a typed source and target, an active
well-formed Pi reading, and its actual forward image.  The sort clause
was proved universally above; it is not an omitted side condition. -/
theorem truePiIota_forward_nonvacuity :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU 0 []) ∧
    Nonempty (HasTyT trueEnvU 0 [] truePiIotaLhs (.sort truePiIotaLevel)) ∧
    Nonempty (HasTyT trueEnvU 0 [] mixPi (.sort truePiIotaLevel)) ∧
    Nonempty (ConvT trueEnvU 0 [] truePiIotaLhs mixPi (.sort truePiIotaLevel)) ∧
    NativeIotaForwardAtT truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy ∧
    RedR (WhStepK trueEnvU 0) [] truePiIotaLhs mixPi ∧
    Nonempty (CtxWfT trueEnvU 0 [.assumption (.sort .zero)]) ∧
    ∃ A B, RedR (WhStepK trueEnvU 0) [] mixPi (.pi A B) ∧
      Nonempty (TyConvT trueEnvU 0 [] (.sort .zero) A) ∧
      Nonempty (TyConvT trueEnvU 0 [.assumption (.sort .zero)] (.sort .zero) B) :=
  ⟨⟨trueEnvUWfT⟩, ⟨.nil⟩, ⟨truePiIotaLhsTy⟩, ⟨truePiIotaRhsTy⟩,
    ⟨truePiIotaAtSort⟩, truePiIotaForward, truePiIota_readback,
    ⟨.assumption _ _ _ .nil (.sort _ .zero)⟩,
    truePiIotaForward.pis truePiIota_readback (.assumption _ _ _ .nil (.sort _ .zero))⟩

/-- The exact additional fact which excludes a direct native `irr` node
whose written result index is a literal sort.  This is local universe
consistency, stated separately from any Pi or family row. -/
theorem native_irr_at_sort_false_of_sortRow {Γ : LCtx}
    (hSort : ∀ {l₁ l₂ : Level}, TyConvT E n Γ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {P : Expr Nat} {u : Level} (hP : HasTyT E n Γ P (.sort .zero))
    (hindex : P = .sort u) : False := by
  subst P
  exact not_hasTyT_sort_zero_of_sortRow hSort u hP

-- BEGIN RCIC_PI_PROBE_K_OBSTRUCTION_ROOTS
#print axioms whStepK_of_whStepRecCtx
#print axioms whStepK_of_whStepRecK
#print axioms redR_whStepK_of_whRedRecK
#print axioms andPiNF1_readback
#print axioms andPiNF2_readback
#print axioms andPiNF1_normal
#print axioms andPiNF2_normal
#print axioms not_normalUniqueR_whStepK_andEnvU
#print axioms andDepPiMinTy
#print axioms andNonUniquePiRedexTy
#print axioms andPiNF1Ty
#print axioms andPiNF2Ty
#print axioms typed_normalUniqueR_counterexample
#print axioms andPiNormalsConv
#print axioms andPiNormals_components
#print axioms andPiNormals_probe
#print axioms andNonUniquePiRedex_probe
#print axioms whStepK_of_native_iota
#print axioms piProbe_native_iota_expand
#print axioms piProbe_native_iota_symm_link
#print axioms native_iota_reverse_transport
#print axioms NativeIotaForwardAtT
#print axioms native_iota_motive_iff_forward
#print axioms native_iota_forward_iff_sort_and_pi
#print axioms mixAndIotaLhsSortTy
#print axioms mixAndIotaRhsSortTy
#print axioms mixAndIotaAtSort
#print axioms mixAnd_iota_rhs_readback
#print axioms mixAnd_iota_rhs_probe
#print axioms mixAnd_iota_probe
#print axioms mixAnd_iota_pi_link
#print axioms mixAnd_iota_pi_link_nonvacuity
#print axioms truePiIotaLevel
#print axioms truePiIotaLhs
#print axioms truePiIotaNative
#print axioms truePiIotaRhsTy
#print axioms truePiIotaLhsTy
#print axioms truePiIotaAtSort
#print axioms truePiIotaForward
#print axioms truePiIota_motive
#print axioms truePiIota_readback
#print axioms truePiIota_no_sort_readback
#print axioms truePiIota_forward_nonvacuity
#print axioms native_irr_at_sort_false_of_sortRow
-- END RCIC_PI_PROBE_K_OBSTRUCTION_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeKObstructionAudit
