import rcic.RcicNativeTypedModelFundDelta

/-!
# RcicNativeTypedModelRecDiagCounter — the recursor-member diagonal is REFUTED

Sealed record module for the audit-lane-6 finding on #7737.

`MemberRecDiagT` is the recursor/$\iota$ admission clause that a `FundCases.consts` field
would need for `.recursorM` members: related substitutions should relate level-congruent
constant spines at every curried-step compact the recursor approximation supplies.
It is **false** at the concrete model `ctxModelT_approxT`: `ApproxT.recursor` carries no
`CTyS` typing side-condition on `us_pre`/`us_fields`, and `SpineClauseS` bounds only the
*length* of the argument-compact list, never its elements — so a bad compact (`badSpine`,
a spine of a nonexistent member) can be smuggled through the `Nat.rec` approximation and
then demanded by the relation.

`not_memberRecDiagT_natEnvU` is the kernel-checked counterexample (audit lane 6,
verbatim): at `natEnvU` (which contains a real recursor `Nat.rec`), `MemberRecDiagT`
fails under `WhStepCtx` — and also under `WhStepRecK`
(`not_memberRecDiagT_natEnvU_whStepRecK`).

This is a **model-level finding**: the gap lives in `ApproxT.recursor` / `SpineClauseS`
(relation shape), not in the `FundCases` proof script.  It is routed to the relation
re-foundation; nothing here is claimed dischargeable.  Accordingly `fundT_const` /
`fundT_consts` (`RcicNativeTypedModelFundDelta`) cover non-recursor members only
(`hnrec : m.mclass ≠ .recursorM`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- **The recursor-member diagonal** — the ι admission: at a member resolved by an
    ι-witness, related substitutions relate the level-congruent constant spines at every
    curried-step compact the recursor clauses supply.  **Refuted** on `natEnvU` at
    `ctxModelT_approxT` (`not_memberRecDiagT_natEnvU` below); kept here as the sealed
    statement of the model-level finding, not as a usable premise. -/
def MemberRecDiagT (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember},
    E.members r = some m → m.mclass = .recursorM →
    ls.length = m.arity → levelsBounded n ls = true → levelsBounded n ls' = true →
    eqNList ls ls' →
    CtxWfT E n Γ → CtxValidAt M R n Γ → CtxWfT E n Δ →
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ → ∀ c : CptT,
    M.Ap ρ (.const r ls) c ∨ M.Ap ρ' (.const r ls') c →
    LRSCoreS R E n Δ (substT σ (.const r ls)) (substT σ' (.const r ls'))
      (substT σ (instantiateLevels ls m.mtype)) c

/-- The `Nat.succ` $\iota$-schema (audit reproducer). -/
def natSuccSchema : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0))
    (.app (.app (.app (.app (.const 3 [.param 0]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

/-- The canonical `Nat.succ` structured $\iota$-witness (audit reproducer). -/
def wNatSucc : IotaWitnessS natEnvU where
  recRef := 3
  ctorRef := 2
  ls := [.param 0]
  lsC := []
  recMember := natRecMemberU
  ctorMember := natSuccMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 3, .bvar 2, .bvar 1]
  fields := [.bvar 0]
  ctorParams := []
  familyRef := 0
  famMember := natFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.const 0 []]
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  recDoms := [
    .pi (.const 0 []) (.sort (.param 0)),
    .app (.bvar 0) (.const 1 []),
    .pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))),
    .const 0 []
  ]
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 4
  shapes := [.recursive 0]
  hshapes := rfl
  schema := natSuccSchema
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : natEnvU.members 0 = some natFamMember := rfl
    have hmem1 : natEnvU.members 1 = some natZeroMember := rfl
    have hmem2 : natEnvU.members 2 = some natSuccMember := rfl
    have hmem3 : natEnvU.members 3 = some natRecMemberU := rfl
    show iotaWitnessStableB natEnvU 4 [.const 0 []] (fieldBvars 1)
      (lift 0 4 (ctorFieldTelRaw 0 [.const 0 []] (.const 0 []))) = true
    simp [iotaWitnessStableB, fieldBvars, ctorFieldTelRaw, lift,
      constsMemberFuel, hmem0, hmem1, hmem2, hmem3,
      natFamMember, natZeroMember, natSuccMember, natRecMemberU,
      transparent, instantiateLevels])
  hschemaScope := rfl

/-- A spine compact of a nonexistent member — unrelated to everything. -/
def badSpine : CptT := .spine 99 []

/-- The bad `hs`-branch compact: its first binder demands `badSpine`. -/
def badHsCpt : CptT := .lam [([badSpine], .lam [([], badSpine)])]

/-- The bad recursor compact: `badSpine` smuggled through `us_fields`/curry. -/
def badRecCpt : CptT :=
  curryStepT [[], [], [badHsCpt], ctorDemandT 2 0 [[badSpine]]] badSpine

theorem not_lrSCoreS_badSpine {R : Readback} {n : Nat} {Γ : LCtx} {M M' A : Expr Nat} :
    ¬ LRSCoreS R natEnvU n Γ M M' A badSpine := by
  rw [badSpine, lrSCoreS_spine_iff]
  rintro ⟨m, _, _, _, _, hm, _⟩
  exact Option.noConfusion hm

theorem approxT_natRec_badRecCpt (ρ : EnvT) (ls : List Level) :
    ApproxT natEnvU ρ (.const 3 ls) badRecCpt := by
  refine ApproxT.recursor (w := wNatSucc) (us_pre := [[], [], [badHsCpt]])
    (us_fields := [[badSpine]]) ls (fun h => nomatch h) rfl rfl ?_
  simp only [wNatSucc, natSuccSchema, instantiateLevels]
  refine ApproxT.app
    (ApproxT.app
      (ApproxT.bvar (c := badHsCpt) (by simp [EnvT.pushArgs, EnvT.cons, demandT]))
      (List.mem_singleton.mpr rfl)
      (fun u hu => by
        rcases List.mem_singleton.mp hu with rfl
        exact ApproxT.bvar (by simp [EnvT.pushArgs, EnvT.cons, demandT])))
    (List.mem_singleton.mpr rfl)
    (fun _ hu => nomatch hu)

theorem ctxValidAt_nil {M : CtxModelT E} {R : Readback} {n : Nat} :
    CtxValidAt M R n [] :=
  fun _ _ h => Option.noConfusion h

theorem relSubstAtT_nil {M : CtxModelT E} {R : Readback} {n : Nat}
    {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} :
    RelSubstAtT M R n Δ ρ ρ' σ σ' [] :=
  ⟨⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩,
   ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩,
   fun _ _ h => Option.noConfusion h,
   fun _ _ h => Option.noConfusion h,
   fun _ _ _ h => Option.noConfusion h⟩

/-- Peeling one `.lam` compact step of `LRSCoreS` through a typed `N`. -/
theorem lrSCoreS_lam_singleton_elim {R : Readback} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hL : ReadbackLaws E R) {M M' A₀ B₀ : Expr Nat} {us : List CptT} {c : CptT}
    (h : LRSCoreS R E n Γ M M' (.pi A₀ B₀) (.lam [(us, c)]))
    {N : Expr Nat} (hN : HasTyT E n Γ N A₀)
    (hus : ∀ u ∈ us, LRSCoreS R E n Γ N N A₀ u) :
    LRSCoreS R E n Γ (.app M N) (.app M' N) (instantiate0 N B₀) c := by
  rw [LRSCoreS.eq_def] at h
  obtain ⟨A₁, B₁, hred, _, hstep⟩ := h
  have heq := redR_pi_eq hL hred
  injection heq with hA hB; subst hA; subst hB
  exact hstep (us, c) (List.mem_singleton.mpr rfl) N N hN hN ⟨.refl _ _ _ hN⟩ hus

/-- The generic refutation: under any readback with `ReadbackLaws` keeping
    `succ zero` normal, `MemberRecDiagT` fails at `natEnvU` (audit reproducer). -/
theorem not_memberRecDiagT_natEnvU_of_normal {R : Readback} (n : Nat)
    (hL : ReadbackLaws natEnvU R)
    (hN : NormalR R [] (.app (.const 2 []) (.const 1 []))) :
    ¬ MemberRecDiagT (ctxModelT_approxT natEnvU) R n := by
  intro hMR
  have h0 := hMR (Γ := []) (Δ := []) (ρ := EnvT.bot) (ρ' := EnvT.bot)
    (σ := SubstT.id) (σ' := SubstT.id) (r := 3) (ls := [.succ .zero]) (ls' := [.succ .zero])
    (m := natRecMemberU) rfl rfl rfl rfl rfl (eqNList_refl _)
    .nil ctxValidAt_nil .nil relSubstAtT_nil badRecCpt
    (Or.inl (approxT_natRec_badRecCpt EnvT.bot [.succ .zero]))
  simp only [substT_id] at h0
  let natTy : Expr Nat := .const 0 []
  let zeroTm : Expr Nat := .const 1 []
  let succTm : Expr Nat := .const 2 []
  let succZeroTm : Expr Nat := .app succTm zeroTm
  let motTm : Expr Nat := .lam natTy natTy
  have hNat : HasTyT natEnvU n [] natTy (.sort (.succ .zero)) :=
    .const [] 0 [] natFamMember rfl rfl rfl
  have hZero : HasTyT natEnvU n [] zeroTm natTy :=
    .const [] 1 [] natZeroMember rfl rfl rfl
  have hSucc : HasTyT natEnvU n [] succTm (.pi natTy natTy) :=
    .const [] 2 [] natSuccMember rfl rfl rfl
  have hSuccZero : HasTyT natEnvU n [] succZeroTm natTy :=
    .app [] succTm zeroTm natTy natTy hSucc hZero
  have hMot : HasTyT natEnvU n [] motTm (.pi natTy (.sort (.succ .zero))) :=
    .lam [] natTy (.succ .zero) natTy (.sort (.succ .zero)) hNat
      (.const [.assumption natTy] 0 [] natFamMember rfl rfl rfl)
  have h1 := lrSCoreS_lam_singleton_elim hL h0 hMot (fun _ hu => nomatch hu)
  have hZeroMot : HasTyT natEnvU n [] zeroTm (.app motTm zeroTm) :=
    .conv [] zeroTm natTy (.app motTm zeroTm) (.succ .zero) hZero
      (.symm [] _ _ _ (.beta [] natTy natTy zeroTm (.sort (.succ .zero)) (.succ .zero)
        hNat (.const [.assumption natTy] 0 [] natFamMember rfl rfl rfl) hZero))
  have h2 := lrSCoreS_lam_singleton_elim hL h1 hZeroMot (fun _ hu => nomatch hu)
  let Γ₁ : LCtx := [.assumption natTy]
  let ihDom : Expr Nat := .app motTm (.bvar 0)
  let Γ₂ : LCtx := .assumption ihDom :: Γ₁
  let hsCod : Expr Nat := .app motTm (.app succTm (.bvar 1))
  let hsTm : Expr Nat := .lam natTy (.lam ihDom zeroTm)
  have hNat₁ : HasTyT natEnvU n Γ₁ natTy (.sort (.succ .zero)) :=
    .const Γ₁ 0 [] natFamMember rfl rfl rfl
  have hBvar0₁ : HasTyT natEnvU n Γ₁ (.bvar 0) natTy :=
    .bvar Γ₁ 0 natTy rfl
  have hIhDom : HasTyT natEnvU n Γ₁ ihDom (.sort (.succ .zero)) :=
    .app Γ₁ motTm (.bvar 0) natTy (.sort (.succ .zero))
      (.lam Γ₁ natTy (.succ .zero) natTy (.sort (.succ .zero)) hNat₁
        (.const (.assumption natTy :: Γ₁) 0 [] natFamMember rfl rfl rfl))
      hBvar0₁
  have hNat₂ : HasTyT natEnvU n Γ₂ natTy (.sort (.succ .zero)) :=
    .const Γ₂ 0 [] natFamMember rfl rfl rfl
  have hZero₂ : HasTyT natEnvU n Γ₂ zeroTm natTy :=
    .const Γ₂ 1 [] natZeroMember rfl rfl rfl
  have hSuccBvar1₂ : HasTyT natEnvU n Γ₂ (.app succTm (.bvar 1)) natTy :=
    .app Γ₂ succTm (.bvar 1) natTy natTy
      (.const Γ₂ 2 [] natSuccMember rfl rfl rfl)
      (.bvar Γ₂ 1 natTy rfl)
  have hZeroHsCod : HasTyT natEnvU n Γ₂ zeroTm hsCod :=
    .conv Γ₂ zeroTm natTy hsCod (.succ .zero) hZero₂
      (.symm Γ₂ _ _ _ (.beta Γ₂ natTy natTy (.app succTm (.bvar 1))
        (.sort (.succ .zero)) (.succ .zero) hNat₂
        (.const (.assumption natTy :: Γ₂) 0 [] natFamMember rfl rfl rfl)
        hSuccBvar1₂))
  have hHs : HasTyT natEnvU n [] hsTm (.pi natTy (.pi ihDom hsCod)) :=
    .lam [] natTy (.succ .zero) (.lam ihDom zeroTm) (.pi ihDom hsCod) hNat
      (.lam Γ₁ ihDom (.succ .zero) zeroTm hsCod hIhDom hZeroHsCod)
  have hHsRel : LRSCoreS R natEnvU n [] hsTm hsTm (.pi natTy (.pi ihDom hsCod)) badHsCpt := by
    rw [badHsCpt, LRSCoreS.eq_def]
    refine ⟨natTy, .pi ihDom hsCod, .refl _, ⟨.assumption [] natTy (.succ .zero) .nil hNat⟩, ?_⟩
    intro s hs N N' _ _ _ hus
    rcases List.mem_singleton.mp hs with rfl
    exact (not_lrSCoreS_badSpine (hus badSpine (List.mem_singleton.mpr rfl))).elim
  have h3 := lrSCoreS_lam_singleton_elim hL h2 hHs (fun u hu => by
    rcases List.mem_singleton.mp hu with rfl
    exact hHsRel)
  have hSuccZeroSpine : ∀ u : CptT,
      LRSCoreS R natEnvU n [] succZeroTm succZeroTm natTy (.spine 2 [u]) := by
    intro u
    rw [lrSCoreS_spine_iff]
    refine ⟨natSuccMember, [], [], [zeroTm], [zeroTm], rfl, .refl _, .refl _,
      hN, hN, eqNList_refl [], Nat.le_refl 1, Nat.le_refl 1,
      .cons natTy natTy zeroTm zeroTm [] [] ⟨.refl [] zeroTm natTy hZero⟩ (.nil _), ?_⟩
    intro _ hind
    exact MemberClass.noConfusion hind
  have h4 := lrSCoreS_lam_singleton_elim hL h3 hSuccZero (fun u hu => by
    simp only [ctorDemandT, fieldDemandVectorsT, List.replicate, List.map, List.nil_append,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact hSuccZeroSpine .bot
    · exact hSuccZeroSpine badSpine)
  exact not_lrSCoreS_badSpine h4

/-- `MemberRecDiagT` is false at `ctxModelT_approxT natEnvU` under `WhStepCtx`. -/
theorem not_memberRecDiagT_natEnvU (n : Nat) :
    ¬ MemberRecDiagT (ctxModelT_approxT natEnvU) (WhStepCtx natEnvU) n :=
  not_memberRecDiagT_natEnvU_of_normal n
    (readbackLaws_whStepCtx natEnvU)
    (whNormalCtx_ctorApp natEnvUWfT (c := 2) (m := natSuccMember) rfl rfl [] [.const 1 []])

/-- `MemberRecDiagT` is false at `ctxModelT_approxT natEnvU` under `WhStepRecK` too. -/
theorem not_memberRecDiagT_natEnvU_whStepRecK (n : Nat) :
    ¬ MemberRecDiagT (ctxModelT_approxT natEnvU) (WhStepRecK natEnvU n) n :=
  not_memberRecDiagT_natEnvU_of_normal n
    { sort_normal := fun _ _ _ h => whStepRecK_sort_false h
      pi_normal := fun _ _ _ _ h => whStepRecK_pi_false h
      famApp_normal := fun hW _ _ _ hm hind _ _ _ h => whStepRecK_famApp_false hW hm hind h
      appHead := fun _ _ _ _ h => .appHead h
      beta := fun _ A b a => .recCtx (.beta A b a) }
    (whNormalRecK_ctorApp natEnvUWfT (c := 2) (m := natSuccMember) rfl rfl [] [.const 1 []])

end Rcic.Declarative.NativeValleys.TypedModelAudit
