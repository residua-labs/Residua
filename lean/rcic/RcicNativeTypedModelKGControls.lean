import rcic.RcicNativeTypedModelKG

/-!
# RcicNativeTypedModelKGControls — the gate at the fixtures, both acceptance sides

The reduction-witnessed gate `KGateAt` is measured at every #7749 fixture:

* **Positive** (acceptance 2): the β gap `eqGapRedex`, the η control
  `etaIndexRedex`, and δ at the index head (`deltaRedex (.const 66 [])` in the
  checked δ extension) all observe `.prop` through the guarded clause.
* **Negative** (acceptance 1): at the apart fixture the gate is refuted
  (`not_kGateAt_apart`), so `apartRec` has only the bottom compact — the exact
  premise `not_fundamentalSAtT_of_normal_prop_compact` consumed is gone.
* **Residual divergences** (acceptance 4 inputs): the under-binder β control and
  δ under a binder natively fire `KNativeHead` (#7749) while the guarded model
  observes only bottom there — stated as kernel facts, not prose.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKAudit.KG

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit

variable {n : Nat}

/-! ## §1 — master case analysis of the gate -/

/-- Every way two indices can be reduction-witnessed to agree, stated over
variable indices so each constructor of `KIdxAgree` is reachable by `cases`. -/
theorem kIdxAgree_cases {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} (h : KIdxAgree E R n Γ a b) :
    (∃ N, RedR R Γ a N ∧ RedR R Γ b N) ∨
    (∃ (r : Nat) (ls : List Level) (m : CheckedMember) (bb b' : Expr Nat),
      DeltaConst E r m bb ∧ a = .const r ls ∧ b = b' ∧
        KIdxAgree E R n Γ (instantiateLevels ls bb) b') ∨
    (∃ (r : Nat) (ls : List Level) (m : CheckedMember) (bb a' : Expr Nat),
      DeltaConst E r m bb ∧ b = .const r ls ∧ a = a' ∧
        KIdxAgree E R n Γ a' (instantiateLevels ls bb)) ∨
    (∃ (A f : Expr Nat), a = f ∧
      b = .lam A (.app (lift 0 1 f) (.bvar 0))) ∨
    (∃ (A f : Expr Nat),
      a = .lam A (.app (lift 0 1 f) (.bvar 0)) ∧ b = f) := by
  cases h with
  | red h => exact Or.inl h
  | deltaL hd h =>
      refine Or.inr (Or.inl ?_)
      exact ⟨_, _, _, _, _, hd, rfl, rfl, h⟩
  | deltaR hd h =>
      refine Or.inr (Or.inr (Or.inl ?_))
      exact ⟨_, _, _, _, _, hd, rfl, rfl, h⟩
  | etaL _ =>
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      exact ⟨_, _, rfl, rfl⟩
  | etaR _ =>
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      exact ⟨_, _, rfl, rfl⟩

/-! ## §2 — the apart prefix and its data -/

/-- The apart fixture's pre-major spine. -/
def apartPre : List (Expr Nat) :=
  [.sort .zero, idPiProp, apartMot, .sort .zero, apartRight]

/-- The recursor constant of the Eq block. -/
def eqRecConst : Expr Nat := .const 65 [.succ (.succ .zero)]

/-- The apart fixture's actual index is a rigid family application. -/
theorem apartRight_eq : apartRight =
    foldApps (.const 63 []) [.sort .zero, idPiProp, idPiProp] := rfl

/-- Every structured witness at reference `65` in the admitted Eq environment
has the five-argument spine, one index, and an empty field list. -/
theorem eqS65_data (w : IotaWitnessS eqEnvT) (hw : w.recRef = 65) :
    PropFamilyS w ∧ w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 ∧
      w.fields = [] ∧ w.preMajor.length = 5 := by
  obtain ⟨hP, _, hfl, _⟩ := eqRec_model_schema w hw
  have hd := NativeMovingMinorUnion76.schemaData w hw
  have hlen5 : w.preMajor.length = 5 := by
    have h1 := w.hpre
    omega
  exact ⟨hP, hd.1, hd.2.1, hd.2.2.1, hfl, hlen5⟩

/-- Every legacy witness at reference `65` computes its sole result index to
the left Eq parameter and reads its sole actual index off the spine. -/
theorem eqW65_indices (w : IotaWitness eqEnvT) (hr : w.recRef = 65)
    {A a mot minor b : Expr Nat}
    (hp : w.preMajor = [A, a, mot, minor, b]) :
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 ∧ w.fields = [] ∧
      w.preMajor.take w.nparams = [A, a] ∧
      resultIdxAt w (w.preMajor.take w.nparams) w.fields = [a] ∧
      redexIdx w = [b] := by
  obtain ⟨hnp, hni, hnm⟩ := eqWitnessIndexCut w hr
  obtain ⟨hcm, hfl⟩ := eqWitnessCtorData w hr
  have htake : w.preMajor.take w.nparams = [A, a] := by
    rw [hnp, hp]; rfl
  refine ⟨hnp, hni, hnm, hfl, htake, ?_, ?_⟩
  · rw [htake, hfl]
    have hcalc : applyTel [A, a] (instantiateLevels w.ls eqReflT.mtype) =
        some (foldApps (.const 63 []) [A, a, a]) := eqRefl_applyTel A a
    unfold resultIdxAt applyTelOr
    rw [hnp, hcm, List.append_nil, hcalc]
    rfl
  · unfold redexIdx
    rw [hnp, hnm, hp]
    rfl

/-! ## §3 — the gate at every fixture -/

/-- The β gap: the actual index weak-head reduces to the computed one, so the
gate fires by the readback's own reduction. -/
theorem kIdxAgree_eqGap (R : Readback) (n : Nat) (hL : ReadbackLaws eqEnvT R) :
    KIdxAgree eqEnvT R n eqGapCtx (.bvar 1)
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) :=
  .red ⟨.bvar 1, .refl _,
    .step (hL.beta eqGapCtx (.bvar 2) (.bvar 0) (.bvar 1)) (.refl _)⟩

/-- The apart fixture: the two proposition indices are weak-head normal and
syntactically distinct (a Π versus a rigid family application), and no δ or η
pattern applies, so the reduction-witnessed gate is refuted. -/
theorem not_kIdxAgree_apart (n : Nat) :
    ¬ KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n apartCtx idPiProp apartRight := by
  intro h
  rcases kIdxAgree_cases h with ⟨N, hN₁, hN₂⟩
    | ⟨r, ls, m, bb, b', hd, ha, _, _⟩ | ⟨r, ls, m, bb, a', hd, hb, _, _⟩
    | ⟨A, f, ha, hb⟩ | ⟨A, f, ha, hb⟩
  · have h₁ : N = idPiProp :=
      redR_of_normal (normalR_piCK2 (E := eqEnvT) (n := n) apartCtx
        (.sort .zero) (.bvar 0)) hN₁
    have h₂ : N = apartRight :=
      redR_of_normal (normalR_famAppCK2 (E := eqEnvT) pinEqGroupWfT (r := 63)
        (m := eqFamT) rfl rfl apartCtx [] [.sort .zero, idPiProp, idPiProp]) hN₂
    exact foldApps_const_ne_pi [.sort .zero, idPiProp, idPiProp]
      (.sort .zero) (.bvar 0)
      (apartRight_eq.symm.trans (h₂.symm.trans h₁))
  · exact Expr.noConfusion ((rfl : idPiProp = .pi (.sort .zero) (.bvar 0)).symm.trans ha)
  · simp only [apartRight_eq, foldApps] at hb
    exact Expr.noConfusion hb
  · simp only [apartRight_eq, foldApps] at hb
    exact Expr.noConfusion hb
  · exact Expr.noConfusion ((rfl : idPiProp = .pi (.sort .zero) (.bvar 0)).symm.trans ha)

/-- At the apart fixture the gate is refuted: any matching legacy witness
computes the apart index pair, which does not agree. -/
theorem not_kGateAt_apart (n : Nat) {w : IotaWitnessS eqEnvT}
    (hw : w.recRef = 65) (hp : w.preMajor = apartPre) :
    ¬ KGateAt eqEnvT (WhStepCK2 eqEnvT n) n apartCtx w := by
  rintro ⟨w', hr, hls, hpre, hj⟩
  have hp65 : w'.recRef = 65 := hr.trans hw
  have hip : w'.preMajor = [.sort .zero, idPiProp, apartMot, .sort .zero, apartRight] :=
    hpre.trans hp
  obtain ⟨_, _, _, _, _, hc, ha⟩ :=
    @eqW65_indices w' hp65 (.sort .zero) idPiProp apartMot (.sort .zero) apartRight hip
  rw [hc, ha] at hj
  rcases hj with ⟨h, _⟩
  exact not_kIdxAgree_apart n h

/-- The η control: the actual index is the η expansion of the computed one. -/
theorem kIdxAgree_etaIndex (R : Readback) (n : Nat) :
    KIdxAgree eqEnvT R n etaEqCtx (.bvar 1) etaIndex :=
  .etaL (.bvar etaEqCtx 1 (.pi (.sort .zero) (.sort .zero)) rfl)

/-- δ at the index head: the transparent definition unfolds to the computed
index. -/
theorem kIdxAgree_deltaHead (R : Readback) (n : Nat) (Γ : LCtx) :
    KIdxAgree deltaEqEnv R n Γ indexId (.const 66 []) :=
  .deltaR ⟨rfl, rfl, by decide, by decide⟩ (kIdxAgree_refl deltaEqEnv R n Γ indexId)

/-- The under-binder β control: `indexBinderBeta` is exactly the η expansion
of `indexId` (the lift fixes `indexId` in place: its body is `#0` below the
fresh binder), so the gate fires by η. -/
theorem kIdxAgree_binder (R : Readback) (n : Nat) :
    KIdxAgree eqEnvT R n binderEqCtx indexId indexBinderBeta :=
  .etaL (A := .sort .zero) (B := .sort .zero) (f := indexId)
    (indexIdTy eqEnvT n binderEqCtx)

/-- δ under a binder: the transparent definition sits in the function position
under the λ, which no gate rule reaches. -/
theorem not_kIdxAgree_deltaBinder (n : Nat) (Γ : LCtx) :
    ¬ KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n Γ indexId deltaBinderIndex := by
  intro h
  rcases kIdxAgree_cases h with ⟨N, hN₁, hN₂⟩
    | ⟨r, ls, m, bb, b', hd, ha, _, _⟩ | ⟨r, ls, m, bb, a', hd, hb, _, _⟩
    | ⟨A, f, ha, hb⟩ | ⟨A, f, ha, hb⟩
  · have h₁ : N = indexId :=
      redR_of_normal (normalR_lamCK2 (E := deltaEqEnv) (n := n) Γ
        (.sort .zero) (.bvar 0)) hN₁
    have h₂ : N = deltaBinderIndex :=
      redR_of_normal (normalR_lamCK2 (E := deltaEqEnv) (n := n) Γ
        (.sort .zero) (.app (.const 66 []) (.bvar 0))) hN₂
    exact absurd (h₂.symm.trans h₁) (by decide)
  · exact Expr.noConfusion ((rfl : indexId = .lam (.sort .zero) (.bvar 0)).symm.trans ha)
  · exact Expr.noConfusion ((rfl : deltaBinderIndex =
      .lam (.sort .zero) (.app (.const 66 []) (.bvar 0))).symm.trans hb)
  · unfold deltaBinderIndex at hb
    injection hb with _ hbody
    injection hbody with hfun _
    rw [← ha] at hfun
    exact Expr.noConfusion ((rfl : lift 0 1 indexId = indexId).symm.trans hfun.symm)
  · have hidx : @Expr.lam Nat (.sort .zero) (.bvar 0) = indexId := rfl
    exact Expr.noConfusion (hidx.trans ha) (fun _ hbody => Expr.noConfusion hbody)

/-! ## §4 — structured witnesses at arbitrary Eq spines -/

/-- Appending a single element is injective at equal list lengths. -/
theorem append_single_inj {α : Type} {l₁ l₂ : List α} {x y : α}
    (he : l₁ ++ [x] = l₂ ++ [y]) (hlen : l₁.length = l₂.length) :
    l₁ = l₂ ∧ x = y :=
  ⟨List.append_inj_left he hlen, by
    injection List.append_inj_right he hlen with h⟩

/-- A structured witness at any saturated Eq spine with the fixed minor `Sort 0`,
in any environment that preserves the Eq block. -/
theorem eqIndexWS_exists {E : ResolvedEnv}
    (hext : ∀ r m, eqEnvT.members r = some m → E.members r = some m)
    (A a b mot : Expr Nat) :
    ∃ w₀ : IotaWitnessS E, w₀.recRef = 65 ∧ w₀.ls = [.succ (.succ .zero)] ∧
      w₀.preMajor = [A, a, mot, .sort .zero, b] ∧ w₀.fields = [] ∧
      w₀.schema = .bvar 1 ∧ PropFamilyS w₀ ∧ w₀.nindices = 1 := by
  obtain ⟨hi⟩ :=
    derivedIotaT_of_iotaWitness_envWfT pinEqGroupWfT (eqIndexW A a mot b)
  obtain ⟨w₀, hl, _⟩ := derivedIotaT_inv hi
  have hh := congrArg (fun e => (appsSpine e).1) hl
  simp only [iotaLhsOfS, iotaLhsOf, recCall, appsSpine_foldApps, appsSpine] at hh
  obtain ⟨hr, hls⟩ := Expr.const.inj hh
  have ha := congrArg (fun e => (appsSpine e).2) hl
  simp only [iotaLhsOfS, iotaLhsOf, recCall, appsSpine_foldApps, appsSpine] at ha
  obtain ⟨hP0, hlen5, hfl0, hsch0⟩ := eqRec_model_schema w₀ hr
  have hd := NativeMovingMinorUnion76.schemaData w₀ hr
  have hlen5' : w₀.preMajor.length = 5 := hlen5
  obtain ⟨hpre, _⟩ := append_single_inj (l₁ := w₀.preMajor)
    (l₂ := [A, a, mot, .sort .zero, b])
    (x := foldApps (.const w₀.ctorRef w₀.lsC) (w₀.ctorParams ++ w₀.fields))
    (y := foldApps (.const 64 []) ([A, a] ++ [])) ha (by
      simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨extWitnessS hext w₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [extWitnessS] using hr
  · simpa only [extWitnessS] using hls
  · simpa only [extWitnessS] using hpre
  · simpa only [extWitnessS] using hfl0
  · simpa only [extWitnessS] using hsch0
  · simpa only [extWitnessS] using hP0
  · simpa only [extWitnessS] using hd.2.1

/-! ## §5 — the positive controls (acceptance 2) -/

/-- The guarded clause's shared `.prop` construction: any saturated Eq spine
whose gate fires reads back its minor's sort code through the clause's demand
realisation. -/
theorem approxTK_eqRec_prop {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {A a b mot : Expr Nat}
    (w₀ : IotaWitnessS E) (hP : PropFamilyS w₀) (hr : w₀.recRef = 65)
    (hpre₀ : w₀.preMajor = [A, a, mot, .sort .zero, b])
    (hls₀ : w₀.ls = [.succ (.succ .zero)])
    (hfl : w₀.fields = []) (hsch : w₀.schema = .bvar 1)
    (hgate : KGateAt E R n Γ w₀) (x : Expr Nat) :
    ApproxTK E R n Γ ρ (recCall (.const 65 [.succ (.succ .zero)])
      [A, a, mot, .sort .zero, b] x) CptT.prop := by
  have hminor : ApproxT E ρ (.sort .zero) CptT.prop := by
    have h := approxT_sort_code E ρ Level.zero
    rwa [sortCode_zero] at h
  have hargs : ApproxArgsDemandT E ρ [A, a, mot, .sort .zero, b]
      [[], [], [], [CptT.prop], []] := by
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    refine .cons (fun u hu => ?_) ?_
    · obtain rfl := List.mem_singleton.mp hu
      exact hminor
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    exact .nil
  have hinner : ApproxTK E R n Γ
      (EnvT.pushArgs
        (([[], [], [], [CptT.prop], []] ++ w₀.fields.map (fun _ => ([] : List CptT))).map
          demandT) EnvT.bot)
      (instantiateLevels w₀.ls w₀.schema) CptT.prop := by
    rw [hfl]
    simp only [List.map_nil, List.append_nil]
    rw [hsch]
    refine .bvar ?_
    show (EnvT.cons (demandT ([] : List CptT)) (EnvT.cons (demandT [CptT.prop])
      (EnvT.cons (demandT []) (EnvT.cons (demandT [])
      (EnvT.cons (demandT []) EnvT.bot))))) 1 CptT.prop
    simp [EnvT.cons, demandT]
  have hprefix : ApproxTK E R n Γ ρ
      (foldApps (.const w₀.recRef w₀.ls) w₀.preMajor) (.lam [([], CptT.prop)]) :=
    .recursorPropK hP hgate (by rw [hpre₀]; rfl) (by rw [hpre₀]; exact hargs) hinner
  rw [recCall_eq_app, ← hpre₀, ← hls₀, ← hr]
  exact .app hprefix (List.mem_singleton.mpr rfl)
    (fun u hu => absurd hu (List.not_mem_nil _))

/-! ## §5b — Eq-block data in the checked δ extension -/

/-- Every legacy witness at reference `65` in the δ extension computes its
sole result index to the left parameter and reads its sole actual index off
the spine. -/
theorem eqW65_delta_indices (w : IotaWitness deltaEqEnv)
    (hr : w.recRef = 65) {A a mot minor b : Expr Nat}
    (hp : w.preMajor = [A, a, mot, minor, b]) :
    w.preMajor.take w.nparams = [A, a] ∧
      resultIdxAt w (w.preMajor.take w.nparams) w.fields = [a] ∧
      redexIdx w = [b] := by
  have h65 : deltaEqEnv.members 65 = some eqRecT :=
    members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl (by rw [eqEnvT_mem]; simp)
  have hrw : deltaEqEnv.members 65 = some w.recMember := by rw [← hr]; exact w.hrec
  have hm : w.recMember = eqRecT := Option.some.inj (hrw.symm.trans h65)
  have hd := IotaWitness.recData_admitted eqGroupAdm
    (fun r' m' h => members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl h)
    w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  obtain ⟨hfr, hfm, hnp, hni, hnm⟩ := hd
  have htake : w.preMajor.take w.nparams = [A, a] := by
    rw [hnp, hp]; rfl
  have hcm : w.ctorMember = eqReflT := by
    have hci : w.ctorIdx = 0 := by
      have h := w.hidx
      rw [hnm] at h
      omega
    have hcr : w.ctorRef = 64 := by rw [w.hctorIdx, hfr, hci]
    have hmem : deltaEqEnv.members 64 = some w.ctorMember := by rw [← hcr]; exact w.hctor
    have h64 : deltaEqEnv.members 64 = some eqReflT :=
      members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl (by rw [eqEnvT_mem]; simp)
    exact Option.some.inj (hmem.symm.trans h64)
  have hfl : w.fields = [] := by
    have h := w.hnpar
    rw [hnp, hcm] at h
    have hpc : piCount eqReflT.mtype = 2 := rfl
    have hzero : w.fields.length = 0 := by omega
    exact List.length_eq_zero.mp hzero
  refine ⟨htake, ?_, ?_⟩
  · unfold resultIdxAt applyTelOr
    rw [htake, hfl, hcm, hnp, List.append_nil]
    have hcalc : applyTel [A, a] (instantiateLevels w.ls eqReflT.mtype) =
        some (foldApps (.const 63 []) [A, a, a]) := eqRefl_applyTel A a
    rw [hcalc]
    rfl
  · unfold redexIdx
    rw [hnp, hnm, hp]
    rfl

/-- Every structured witness at reference `65` in the δ extension keeps the
Eq block's shape. -/
theorem eqS65_data_delta (w : IotaWitnessS deltaEqEnv) (hw : w.recRef = 65) :
    PropFamilyS w ∧ w.nindices = 1 ∧ w.preMajor.length = 5 := by
  have h65 : deltaEqEnv.members 65 = some eqRecT :=
    members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl (by rw [eqEnvT_mem]; simp)
  have hrw : deltaEqEnv.members 65 = some w.recMember := by rw [← hw]; exact w.hrec
  have hm : w.recMember = eqRecT := Option.some.inj (hrw.symm.trans h65)
  have hd := IotaWitnessS.recData_admitted eqGroupAdm
    (fun r' m' h => members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl h)
    w hw hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  refine ⟨by unfold PropFamilyS; rw [hd.2.1]; rfl, hd.2.2.2.1, ?_⟩
  have h1 := w.hpre
  omega

/-! ## §6 — acceptance 1: the apart fixture reads only bottom -/

/-- The recursor constant of the Eq block admits only bottom compacts. -/
theorem approxTK_eqRecConst65_bot {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {ls : List Level} {d : CptT}
    (h65cl : ∀ w : IotaWitnessS E, w.recRef = 65 → w.nindices = 1 ∧ PropFamilyS w)
    (hm65 : E.members 65 = some eqRecT)
    (h : ApproxTK E R n Γ ρ (.const 65 ls) d) : d = .bot := by
  rcases approxTK_cases h with h0 | ⟨i, he, _⟩ | ⟨l, he, _⟩
    | ⟨A, B, _, _, he, _, _, _⟩ | ⟨A, b, _, _, he, _, _, _⟩
    | ⟨f, a, _, _, he, _, _, _⟩ | ⟨r, ls', he, hrigid, _, _⟩ | ⟨r, ls', m, b, he, hd, _⟩
    | ⟨w, ls'', us_pre, us_fields, c₀, he, hnp, _, _, _, _, _⟩
    | ⟨w, c₀, hP, hgate, he, _⟩
    | ⟨w, ls'', us_pre, c₀, hP, hnidx, he, _, _, _, _⟩
    | ⟨f, a, r, args, u, he, _, _, _⟩ | ⟨A, v, b, he, _⟩ | ⟨t, he, _⟩
  · exact h0
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨hr, _⟩ := Expr.const.inj he
    exact ((hrigid eqRecT (by rw [← hr]; exact hm65)).2 rfl).elim
  · obtain ⟨hr, _⟩ := Expr.const.inj he
    rw [← hr] at hd
    have hm : m = eqRecT := Option.some.inj (hd.1.symm.trans hm65)
    rw [hm] at hd
    exact (hd.2.2.1 rfl).elim
  · obtain ⟨hr, _⟩ := Expr.const.inj he
    exact absurd (h65cl w hr.symm).2 hnp
  · obtain ⟨f, x, hx⟩ := foldApps_preMajor_is_app w
    rw [hx] at he
    exact Expr.noConfusion he
  · obtain ⟨hr, _⟩ := Expr.const.inj he
    have h1 := (h65cl w hr.symm).1
    rw [h1] at hnidx
    exact absurd hnidx (by decide)
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he


/-- Every Eq-spine prefix shorter than the full pre-major admits only bottom:
no clause of the guarded model fires at a `65`-spine below saturation. -/
theorem approxTK_eqSpine65_short_bot {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} : ∀ (k : Nat) (xs : List (Expr Nat)), xs.length = k → k ≤ 4 →
    (∀ w : IotaWitnessS E, w.recRef = 65 → w.preMajor.length = 5) →
    (∀ w : IotaWitnessS E, w.recRef = 65 → w.nindices = 1 ∧ PropFamilyS w) →
    E.members 65 = some eqRecT →
    ∀ {d : CptT}, ApproxTK E R n Γ ρ (foldApps (.const 65 [.succ (.succ .zero)]) xs) d →
    d = .bot := by
  intro k
  induction k with
  | zero =>
      intro xs hlen _ hno h65cl hm65 d h
      rw [List.length_eq_zero.mp hlen] at h
      exact approxTK_eqRecConst65_bot h65cl hm65 h
  | succ k ih =>
      intro xs hlen hle hno h65cl hm65 d h
      rcases list_eq_nil_or_snoc xs with rfl | ⟨ys, y, rfl⟩
      · simp only [List.length_nil] at hlen
        exact (by omega : False).elim
      · rw [foldApps_snoc] at h
        rcases approxTK_app_inv h with h0
          | ⟨g, s, hc, hf, _, _⟩ | ⟨r, args, u, hc, hf, _⟩
          | ⟨w, c₀, hP, hgate, heq, hc₀⟩
        · exact h0
        · have hy : ys.length = k := by
            simp only [List.length_append, List.length_singleton] at hlen
            omega
          exact CptT.noConfusion (ih ys hy (by omega) hno h65cl hm65 hf)
        · have hy : ys.length = k := by
            simp only [List.length_append, List.length_singleton] at hlen
            omega
          exact CptT.noConfusion (ih ys hy (by omega) hno h65cl hm65 hf)
        · rw [← foldApps_snoc] at heq
          obtain ⟨hcst, hp⟩ := foldApps_const_inj heq
          obtain ⟨hr, _⟩ := Expr.const.inj hcst
          have h5 : w.preMajor.length = 5 := hno w hr.symm
          have hplen := congrArg List.length hp
          simp only [List.length_append, List.length_singleton] at hplen
          simp only [List.length_append, List.length_singleton] at hlen
          exact (by omega : False).elim

/-- The full apart prefix admits only bottom: the sub-saturated prefixes by
length, the saturated one by the refuted gate. -/
theorem approxTK_eqSpine65_apart_bot (n : Nat) (ρ : EnvT) {d : CptT}
    (h : ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n apartCtx ρ
      (foldApps eqRecConst apartPre) d) : d = .bot := by
  rcases list_eq_nil_or_snoc apartPre with he | ⟨init, last, hs⟩
  · exact absurd he (by simp [apartPre])
  · rw [hs, foldApps_snoc] at h
    rcases approxTK_app_inv h with h0
      | ⟨g, s, hc, hf, _, _⟩ | ⟨r, args, u, hc, hf, _⟩
      | ⟨w, c₀, hP, hgate, heq, hc₀⟩
    · exact h0
    · have hlen : init.length = 4 := by
        have h6 := congrArg List.length hs
        simp only [apartPre, List.length_cons, List.length_nil, List.length_append,
          List.length_singleton] at h6
        omega
      exact CptT.noConfusion
        (approxTK_eqSpine65_short_bot 4 init hlen (by omega)
          (fun w hw => (eqS65_data w hw).2.2.2.2.2)
          (fun w hw => ⟨(eqS65_data w hw).2.2.1, (eqS65_data w hw).1⟩)
          (by rw [eqEnvT_mem]; simp) hf)
    · have hlen : init.length = 4 := by
        have h6 := congrArg List.length hs
        simp only [apartPre, List.length_cons, List.length_nil, List.length_append,
          List.length_singleton] at h6
        omega
      exact CptT.noConfusion
        (approxTK_eqSpine65_short_bot 4 init hlen (by omega)
          (fun w hw => (eqS65_data w hw).2.2.2.2.2)
          (fun w hw => ⟨(eqS65_data w hw).2.2.1, (eqS65_data w hw).1⟩)
          (by rw [eqEnvT_mem]; simp) hf)
    · rw [← foldApps_snoc] at heq
      obtain ⟨hcst, hp⟩ := foldApps_const_inj heq
      obtain ⟨hr, _⟩ := Expr.const.inj hcst
      exact (not_kGateAt_apart n hr.symm (hp.symm.trans hs.symm) hgate).elim

/-- Acceptance 1: at the apart fixture the guarded model observes only bottom,
so the exact premise of #7749's global refutation is gone. -/
theorem approxTK_apartRec_bot (n : Nat) (ρ : EnvT) {c : CptT}
    (h : ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n apartCtx ρ apartRec c) : c = .bot := by
  have hap : apartRec = .app (foldApps eqRecConst apartPre) (.bvar 0) := by
    rw [apartRec, recCall_eq_app]
    rfl
  rw [hap] at h
  rcases approxTK_app_inv h with h0
    | ⟨g, s, hc, hf, _, _⟩ | ⟨r, args, u, hc, hf, _⟩
    | ⟨w, c₀, hP, hgate, heq, hc₀⟩
  · exact h0
  · exact CptT.noConfusion (approxTK_eqSpine65_apart_bot n ρ hf)
  · exact CptT.noConfusion (approxTK_eqSpine65_apart_bot n ρ hf)
  · rw [← foldApps_snoc] at heq
    obtain ⟨hcst, hp⟩ := foldApps_const_inj heq
    obtain ⟨hr, _⟩ := Expr.const.inj hcst
    have h5 : w.preMajor.length = 5 := (eqS65_data w hr.symm).2.2.2.2.2
    have hplen := congrArg List.length hp
    simp only [apartPre, List.length_cons, List.length_nil, List.length_append,
      List.length_singleton] at hplen
    exact (by omega : False).elim

/-- In particular the old model's `.prop` observation is unreachable in the
guarded model at the apart fixture. -/
theorem not_apartRec_model_approxTK (n : Nat) (ρ : EnvT) :
    ¬ ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n apartCtx ρ apartRec CptT.prop := by
  intro h
  have := approxTK_apartRec_bot n ρ h
  exact CptT.noConfusion this

/-! ## §7 — the positive witnesses and the residual divergence -/

/-- Acceptance 2 at the β gap: the guarded model still observes `.prop`. -/
theorem approxTK_eqGapRedex_prop (n : Nat) (ρ : EnvT) :
    ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx ρ eqGapRedex CptT.prop := by
  obtain ⟨w₀, hr, hls, hpre, hfl, hsch, hP, _⟩ :=
    eqIndexWS_exists (fun _ _ h => h) (.bvar 2) (.bvar 1)
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) eqGapMot
  have hgate : KGateAt eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx w₀ := by
    have hw' : (eqIndexW (.bvar 2) (.bvar 1) eqGapMot
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))).preMajor = w₀.preMajor := hpre.symm
    refine ⟨eqIndexW (.bvar 2) (.bvar 1) eqGapMot
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)), hr.symm, hls.symm, hw', ?_⟩
    obtain ⟨_, _, _, _, _, hc, ha⟩ :=
      @eqW65_indices (eqIndexW (.bvar 2) (.bvar 1) eqGapMot
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))) rfl
        (.bvar 2) (.bvar 1) eqGapMot (.sort .zero)
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) rfl
    rw [hc, ha]
    exact ⟨kIdxAgree_eqGap (WhStepCK2 eqEnvT n) n (readbackLaws_whStepCK2 eqEnvT n), trivial⟩
  exact approxTK_eqRec_prop w₀ hP hr hpre hls hfl hsch hgate (.bvar 0)

/-- Acceptance 2 at the η control. -/
theorem approxTK_etaIndexRedex_prop (n : Nat) (ρ : EnvT) :
    ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n etaEqCtx ρ etaIndexRedex CptT.prop := by
  obtain ⟨w₀, hr, hls, hpre, hfl, hsch, hP, _⟩ :=
    eqIndexWS_exists (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot
  have hgate : KGateAt eqEnvT (WhStepCK2 eqEnvT n) n etaEqCtx w₀ := by
    have hw' : (eqIndexW indexFn (.bvar 1) etaIndexMot etaIndex).preMajor =
        w₀.preMajor := hpre.symm
    refine ⟨eqIndexW indexFn (.bvar 1) etaIndexMot etaIndex, hr.symm, hls.symm, hw', ?_⟩
    obtain ⟨_, _, _, _, _, hc, ha⟩ :=
      @eqW65_indices (eqIndexW indexFn (.bvar 1) etaIndexMot etaIndex) rfl
        indexFn (.bvar 1) etaIndexMot (.sort .zero) etaIndex rfl
    rw [hc, ha]
    exact ⟨kIdxAgree_etaIndex (WhStepCK2 eqEnvT n) n, trivial⟩
  exact approxTK_eqRec_prop w₀ hP hr hpre hls hfl hsch hgate (.bvar 0)

/-- Acceptance 2 at δ in the index head: the checked definition unfolds through
the gate. -/
theorem approxTK_deltaRedex_prop (n : Nat) (ρ : EnvT) :
    ApproxTK deltaEqEnv (WhStepCK2 deltaEqEnv n) n deltaHeadEqCtx ρ
      (deltaRedex (.const 66 [])) CptT.prop := by
  obtain ⟨w₀, hr, hls, hpre, hfl, hsch, hP, _⟩ :=
    eqIndexWS_exists (fun r m h => members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl h)
      indexFn indexId (.const 66 []) binderIndexMot
  have hgate : KGateAt deltaEqEnv (WhStepCK2 deltaEqEnv n) n deltaHeadEqCtx w₀ := by
    have hw' : (eqConvW deltaEqExtends indexFn indexId (.const 66 []) binderIndexMot
        (.sort .zero)).preMajor = w₀.preMajor := hpre.symm
    refine ⟨eqConvW deltaEqExtends indexFn indexId (.const 66 []) binderIndexMot
      (.sort .zero), hr.symm, hls.symm, hw', ?_⟩
    obtain ⟨_, hc, ha⟩ :=
      eqW65_delta_indices (eqConvW deltaEqExtends indexFn indexId (.const 66 [])
        binderIndexMot (.sort .zero)) rfl rfl
    rw [hc, ha]
    exact ⟨kIdxAgree_deltaHead (WhStepCK2 deltaEqEnv n) n deltaHeadEqCtx, trivial⟩
  exact approxTK_eqRec_prop w₀ hP hr hpre hls hfl hsch hgate (.bvar 0)

/-- The under-binder β control: the gate fires by η, so the model observes
`.prop` there as well. -/
theorem approxTK_binderIndexRedex_prop (n : Nat) (ρ : EnvT) :
    ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n binderEqCtx ρ binderIndexRedex CptT.prop := by
  obtain ⟨w₀, hr, hls, hpre, hfl, hsch, hP, _⟩ :=
    eqIndexWS_exists (fun _ _ h => h) indexFn indexId indexBinderBeta binderIndexMot
  have hgate : KGateAt eqEnvT (WhStepCK2 eqEnvT n) n binderEqCtx w₀ := by
    have hw' : (eqIndexW indexFn indexId binderIndexMot indexBinderBeta).preMajor =
        w₀.preMajor := hpre.symm
    refine ⟨eqIndexW indexFn indexId binderIndexMot indexBinderBeta, hr.symm, hls.symm,
      hw', ?_⟩
    obtain ⟨_, _, _, _, _, hc, ha⟩ :=
      @eqW65_indices (eqIndexW indexFn indexId binderIndexMot indexBinderBeta) rfl
        indexFn indexId binderIndexMot (.sort .zero) indexBinderBeta rfl
    rw [hc, ha]
    exact ⟨kIdxAgree_binder (WhStepCK2 eqEnvT n) n, trivial⟩
  exact approxTK_eqRec_prop w₀ hP hr hpre hls hfl hsch hgate (.bvar 0)

/-- At the δ-under-binder fixture the gate is refuted. -/
theorem not_kGateAt_deltaBinder (n : Nat) {w : IotaWitnessS deltaEqEnv}
    (hw : w.recRef = 65)
    (hp : w.preMajor = [indexFn, indexId, binderIndexMot, .sort .zero, deltaBinderIndex]) :
    ¬ KGateAt deltaEqEnv (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx w := by
  rintro ⟨w', hr, hls, hpre, hj⟩
  have hp65 : w'.recRef = 65 := hr.trans hw
  obtain ⟨_, hc, ha⟩ :=
    eqW65_delta_indices w' hp65 (hpre.trans hp)
  rw [hc, ha] at hj
  rcases hj with ⟨h, _⟩
  exact not_kIdxAgree_deltaBinder n _ h

/-- The full δ-under-binder prefix admits only bottom: sub-saturated prefixes
by length, the saturated one by the refuted gate. -/
theorem approxTK_deltaSpine5_bot (n : Nat) (ρ : EnvT) {d : CptT}
    (h : ApproxTK deltaEqEnv (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx ρ
      (foldApps eqRecConst [indexFn, indexId, binderIndexMot, .sort .zero,
        deltaBinderIndex]) d) : d = .bot := by
  have hmem : deltaEqEnv.members 65 = some eqRecT :=
    members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl (by rw [eqEnvT_mem]; simp)
  rcases list_eq_nil_or_snoc [indexFn, indexId, binderIndexMot, .sort .zero,
    deltaBinderIndex] with he | ⟨init, last, hs⟩
  · exact absurd he (by simp)
  · rw [hs, foldApps_snoc] at h
    rcases approxTK_app_inv h with h0
      | ⟨g, s, hc, hf, _, _⟩ | ⟨r, args, u, hc, hf, _⟩
      | ⟨w, c₀, hP, hgate, heq, hc₀⟩
    · exact h0
    · have hlen : init.length = 4 := by
        have h6 := congrArg List.length hs
        simp only [List.length_cons, List.length_nil, List.length_append,
          List.length_singleton] at h6
        omega
      exact CptT.noConfusion
        (approxTK_eqSpine65_short_bot 4 init hlen (by omega)
          (fun w hw => by
            have := (eqS65_data_delta w hw).2.2
            have h1 := w.hpre
            omega)
          (fun w hw => ⟨(eqS65_data_delta w hw).2.1, (eqS65_data_delta w hw).1⟩)
          hmem hf)
    · have hlen : init.length = 4 := by
        have h6 := congrArg List.length hs
        simp only [List.length_cons, List.length_nil, List.length_append,
          List.length_singleton] at h6
        omega
      exact CptT.noConfusion
        (approxTK_eqSpine65_short_bot 4 init hlen (by omega)
          (fun w hw => by
            have := (eqS65_data_delta w hw).2.2
            have h1 := w.hpre
            omega)
          (fun w hw => ⟨(eqS65_data_delta w hw).2.1, (eqS65_data_delta w hw).1⟩)
          hmem hf)
    · rw [← foldApps_snoc] at heq
      obtain ⟨hcst, hp⟩ := foldApps_const_inj heq
      obtain ⟨hr, _⟩ := Expr.const.inj hcst
      exact (not_kGateAt_deltaBinder n hr.symm (hp.symm.trans hs.symm) hgate).elim

/-- The one residual divergence: δ under a binder natively fires the K gate
(#7749's `kNativeHead_delta_under_binder`) while the guarded model observes
only bottom there — the gate's δ rule is head-only, by design. -/
theorem modelK_deltaBinder_divergence (n : Nat) :
    KNativeHead deltaEqEnv n deltaUnderBinderEqCtx (deltaRedex deltaBinderIndex)
        (.sort .zero) ∧
      ∀ (ρ : EnvT) (c : CptT), ApproxTK deltaEqEnv (WhStepCK2 deltaEqEnv n) n
          deltaUnderBinderEqCtx ρ (deltaRedex deltaBinderIndex) c → c = .bot := by
  refine ⟨kNativeHead_delta_under_binder n, ?_⟩
  intro ρ c h
  have hap : deltaRedex deltaBinderIndex =
      .app (foldApps eqRecConst [indexFn, indexId, binderIndexMot, .sort .zero,
        deltaBinderIndex]) (.bvar 0) := by
    rw [deltaRedex, recCall_eq_app]
    rfl
  rw [hap] at h
  rcases approxTK_app_inv h with h0
    | ⟨g, s, hc, hf, _, _⟩ | ⟨r, args, u, hc, hf, _⟩
    | ⟨w, c₀, hP, hgate, heq, hc₀⟩
  · exact h0
  · exact CptT.noConfusion (approxTK_deltaSpine5_bot n ρ hf)
  · exact CptT.noConfusion (approxTK_deltaSpine5_bot n ρ hf)
  · rw [← foldApps_snoc] at heq
    obtain ⟨hcst, hp⟩ := foldApps_const_inj heq
    obtain ⟨hr, _⟩ := Expr.const.inj hcst
    have h5 : w.preMajor.length = 5 := (eqS65_data_delta w hr.symm).2.2
    have h6 := congrArg List.length hp
    simp only [List.length_append, List.length_singleton, List.length_cons,
      List.length_nil] at h6
    exact (by omega : False).elim


-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_ROOTS
#print axioms kIdxAgree_cases
#print axioms apartPre
#print axioms eqRecConst
#print axioms apartRight_eq
#print axioms eqS65_data
#print axioms eqW65_indices
#print axioms kIdxAgree_eqGap
#print axioms not_kIdxAgree_apart
#print axioms not_kGateAt_apart
#print axioms kIdxAgree_etaIndex
#print axioms kIdxAgree_deltaHead
#print axioms kIdxAgree_binder
#print axioms not_kIdxAgree_deltaBinder
#print axioms eqW65_delta_indices
#print axioms eqS65_data_delta
#print axioms append_single_inj
#print axioms eqIndexWS_exists
#print axioms approxTK_eqRec_prop
#print axioms approxTK_eqRecConst65_bot
#print axioms approxTK_eqSpine65_short_bot
#print axioms approxTK_eqSpine65_apart_bot
#print axioms approxTK_apartRec_bot
#print axioms not_apartRec_model_approxTK
#print axioms approxTK_eqGapRedex_prop
#print axioms approxTK_etaIndexRedex_prop
#print axioms approxTK_deltaRedex_prop
#print axioms approxTK_binderIndexRedex_prop
#print axioms not_kGateAt_deltaBinder
#print axioms approxTK_deltaSpine5_bot
#print axioms modelK_deltaBinder_divergence
-- END RCIC_NATIVE_TYPED_MODEL_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKAudit.KG
