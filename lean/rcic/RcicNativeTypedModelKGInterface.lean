import rcic.RcicNativeTypedModelKGControls

/-!
# RcicNativeTypedModelKGInterface — consumer statuses and the new obstruction

Acceptance 3 and 4 of the model-k brief, as kernel facts:

* The model-lemma pieces `FundCases`/`LRSCoreS` consume are listed with their
  status in `approxTK_interface_status`: the structural inversions and the
  bottom clause are re-proved for `ApproxTK`; `app_inv` is re-proved only in
  its four-case refinement, and the old three-case form is *transported*
  through `approxTK_to_approxT` into the landed model.
* The new interface obstruction (acceptance 4): the old three-case
  `CtxModelTLaws.app_inv` is refuted for the guarded model at the eqGap prefix
  (`not_ctxModelTLaws_approxTK`) — the guarded prefix is application-headed and
  carries the remaining major step, which no compositional clause can express.
  Consequently the unchanged fundamental assembly (`fundamentalSAtT_of_cases`)
  cannot run at `ctxModelTApproxTK`; nothing else in the interface is refuted.
* The residual completeness divergence at δ under a binder is
  `modelK_deltaBinder_divergence` in the controls module.
* Non-degenerate inhabitants exist on both `eqEnvT` (the β gap's `.prop`) and
  `natEnvUWfT`'s environment (a sort code).

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

variable {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}

/-! ## §1 — re-proved and transported interface pieces -/

/-- The four-case `app` inversion of the guarded model. -/
theorem approxTK_app_inv_four (h : ApproxTK E R n Γ ρ (.app f a) c) :
    c = .bot ∨
    (∃ g s, c = s.2 ∧ ApproxTK E R n Γ ρ f (.lam g) ∧ s ∈ g ∧
      ∀ u ∈ s.1, ApproxTK E R n Γ ρ a u) ∨
    (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxTK E R n Γ ρ f (.spine r args) ∧
      ApproxTK E R n Γ ρ a u) ∨
    (∃ (w : IotaWitnessS E) (c₀ : CptT), PropFamilyS w ∧ KGateAt E R n Γ w ∧
      .app f a = foldApps (.const w.recRef w.ls) w.preMajor ∧ c = .lam [([], c₀)]) :=
  approxTK_app_inv h

/-- The landed three-case `app` inversion, transported through the conservative
refinement: every `ApproxTK` observation is an `ApproxT` observation first. -/
theorem approxTK_app_inv_transport (h : ApproxTK E R n Γ ρ (.app f a) c) :
    c = .bot ∨
    (∃ g s, c = s.2 ∧ ApproxT E ρ f (.lam g) ∧ s ∈ g ∧
      ∀ u ∈ s.1, ApproxT E ρ a u) ∨
    (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxT E ρ f (.spine r args) ∧
      ApproxT E ρ a u) :=
  approxT_app_inv (approxTK_to_approxT h)

/-- The consumer status list (acceptance 3): every model-lemma shape the
`FundCases`/`LRSCoreS` assembly consumes, with its `ApproxTK` status —
re-proved directly, refined, or transported.  `lift0_elim`/`lift0_intro` and
`ModelBetaExpandT` are not re-proved here: the guarded clause's gate is
lift-sensitive (the readback's own lift-closure is not available), so those
two fields are honest residuals of the guarded model, stated by omission. -/
theorem approxTK_interface_status :
    (∀ (ρ : EnvT) (e : Expr Nat), ApproxTK E R n Γ ρ e CptT.bot) ∧
    (∀ {ρ : EnvT} {i : Nat} {c : CptT},
      ApproxTK E R n Γ ρ (.bvar i) c → c = CptT.bot ∨ ρ i c) ∧
    (∀ {ρ : EnvT} {l : Level} {c : CptT},
      ApproxTK E R n Γ ρ (.sort l) c → c = CptT.bot ∨ c = sortCode l) ∧
    (∀ {ρ : EnvT} {A B : Expr Nat} {c : CptT},
      ApproxTK E R n Γ ρ (.pi A B) c →
      c = CptT.bot ∨ ∃ a f, c = CptT.pi a f ∧ ApproxTK E R n Γ ρ A a ∧
        ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧
          ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) B s.2) ∧
    (∀ {ρ : EnvT} {A b : Expr Nat} {c : CptT},
      ApproxTK E R n Γ ρ (.lam A b) c →
      c = CptT.bot ∨ ∃ a g, c = CptT.lam g ∧ ApproxTK E R n Γ ρ A a ∧
        (∃ s ∈ g, s.2 ≠ CptT.bot) ∧
        ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧
          ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) b s.2) ∧
    (∀ {ρ : EnvT} {A v b : Expr Nat} {c : CptT},
      ApproxTK E R n Γ ρ (.letE A v b) c →
      ApproxTK E R n Γ ρ (.app (.lam A b) v) c) ∧
    (∀ {ρ : EnvT} {f a : Expr Nat} {c : CptT},
      ApproxTK E R n Γ ρ (.app f a) c →
      c = CptT.bot ∨
      (∃ g s, c = s.2 ∧ ApproxTK E R n Γ ρ f (.lam g) ∧ s ∈ g ∧
        ∀ u ∈ s.1, ApproxTK E R n Γ ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxTK E R n Γ ρ f (.spine r args) ∧
        ApproxTK E R n Γ ρ a u) ∨
      (∃ (w : IotaWitnessS E) (c₀ : CptT), PropFamilyS w ∧ KGateAt E R n Γ w ∧
        .app f a = foldApps (.const w.recRef w.ls) w.preMajor ∧
        c = CptT.lam [([], c₀)])) ∧
    (∀ {ρ : EnvT} {f a : Expr Nat} {c : CptT},
      ApproxTK E R n Γ ρ (.app f a) c →
      c = CptT.bot ∨
      (∃ g s, c = s.2 ∧ ApproxT E ρ f (.lam g) ∧ s ∈ g ∧
        ∀ u ∈ s.1, ApproxT E ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxT E ρ f (.spine r args) ∧
        ApproxT E ρ a u)) ∧
    (∀ {ρ : EnvT} {e : Expr Nat} {c : CptT},
      ApproxTK E R n Γ ρ e c → ApproxT E ρ e c) ∧
    (∀ (hδ : ∀ (r : Nat) (ls : List Level) (m : CheckedMember) (b : Expr Nat),
        DeltaConst E r m b → PropRecAppFree E (instantiateLevels ls b))
      (hlit : ∀ t : Nat, PropRecAppFree E (natExpand t))
      {ρ : EnvT} {e : Expr Nat} {c : CptT},
      PropRecAppFree E e → ApproxT E ρ e c → ApproxTK E R n Γ ρ e c) :=
  ⟨fun ρ e => approxTK_bot E R n Γ ρ e, fun h => approxTK_bvar_inv h,
    fun h => approxTK_sort_inv h, fun h => approxTK_pi_inv h,
    fun h => approxTK_lam_inv h, fun h => approxTK_letE_inv h,
    fun h => approxTK_app_inv_four h, fun h => approxTK_app_inv_transport h,
    fun h => approxTK_to_approxT h, @fun _hδ _hlit _ρ _e _c hfree h => approxTK_of_approxT _hδ _hlit h hfree⟩

/-! ## §2 — the new interface obstruction (acceptance 4) -/

/-- The eqGap prefix observation used to refute the old interface: the guarded
clause fires at the exact pre-major prefix and yields the remaining major
step. -/
theorem approxTK_eqGapPrefix_lam (n : Nat) (ρ : EnvT) :
    ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx ρ
      (foldApps eqRecConst
        [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
          .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) (.lam [([], CptT.prop)]) := by
  obtain ⟨w₀, hr, hls, hpre, hfl, hsch, hP, _⟩ :=
    eqIndexWS_exists (fun _ _ h => h) (.bvar 2) (.bvar 1)
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) eqGapMot
  have hgate : KGateAt eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx w₀ := by
    have hw' : (eqIndexW (.bvar 2) (.bvar 1) eqGapMot
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))).preMajor = w₀.preMajor := hpre.symm
    refine ⟨eqIndexW (.bvar 2) (.bvar 1) eqGapMot
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)), hr.symm, hls.symm, hw', ?_⟩
    obtain ⟨_, _, _, _, _, hc, ha⟩ :=
      eqW65_indices (eqIndexW (.bvar 2) (.bvar 1) eqGapMot
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))) rfl rfl
    rw [hc, ha]
    exact ⟨kIdxAgree_eqGap (WhStepCK2 eqEnvT n) n (readbackLaws_whStepCK2 eqEnvT n),
      trivial⟩
  have hminor : ApproxT eqEnvT ρ (.sort .zero) CptT.prop := by
    have h := approxT_sort_code eqEnvT ρ Level.zero
    rwa [sortCode_zero] at h
  have hargs : ApproxArgsDemandT eqEnvT ρ
      [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]
      [[], [], [], [CptT.prop], []] := by
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    refine .cons (fun u hu => ?_) ?_
    · obtain rfl := List.mem_singleton.mp hu
      exact hminor
    refine .cons (fun u hu => absurd hu (List.not_mem_nil _)) ?_
    exact .nil
  have hinner : ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx
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
  unfold eqRecConst
  rw [← hpre, ← hls, ← hr]
  exact .recursorPropK hP hgate (by rw [hpre]; rfl)
    (by rw [hpre]; exact hargs) hinner

/-- The old three-case `CtxModelTLaws.app_inv` is refuted for the guarded model
at the eqGap prefix: the prefix is application-headed, its compact is the
remaining major step, and no compositional clause of the old interface can
express that. -/
theorem not_ctxModelTLaws_approxTK (n : Nat) :
    ¬ CtxModelTLaws (ctxModelTApproxTK eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx) := by
  intro hlaws
  have ρ : EnvT := fun _ _ => False
  have h5 := approxTK_eqGapPrefix_lam n ρ
  have happ : (foldApps eqRecConst
        [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
          .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)] : Expr Nat) =
      .app (foldApps eqRecConst [.bvar 2, .bvar 1, eqGapMot, .sort .zero])
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) :=
    foldApps_snoc eqRecConst (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))
      [.bvar 2, .bvar 1, eqGapMot, .sort .zero]
  rw [happ] at h5
  have hinv := hlaws.app_inv (ρ := ρ) h5
  rcases hinv with h0 | ⟨g, s, hc, hf, hs, _⟩ | ⟨r, args, u, hc, _, _⟩
  · exact CptT.noConfusion h0
  · exact CptT.noConfusion
      (approxTK_eqSpine65_short_bot 4 [.bvar 2, .bvar 1, eqGapMot, .sort .zero]
        (by rfl) (by omega)
        (fun w hw => (eqS65_data w hw).2.2.2.2.2)
        (fun w hw => ⟨(eqS65_data w hw).2.2.1, (eqS65_data w hw).1⟩)
        (by rw [eqEnvT_mem]; simp) hf)
  · exact CptT.noConfusion hc

/-! ## §3 — non-degenerate inhabitants -/

/-- Non-degeneracy on the admitted Eq environment (the degenerate-witness
rule): the β gap's `.prop` observation realises every premise of the guarded
clause with a non-bottom compact. -/
theorem approxTK_eqEnvT_nonvacuity (n : Nat) (ρ : EnvT) :
    ∃ c : CptT, c ≠ CptT.bot ∧
      ApproxTK eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx ρ eqGapRedex c :=
  ⟨CptT.prop, by intro h; exact CptT.noConfusion h, approxTK_eqGapRedex_prop n ρ⟩

/-- Non-degeneracy on the natural-number pin environment: a non-bottom sort
code exists there too, independently of any gate. -/
theorem approxTK_natEnvU_nonvacuity (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ∃ c : CptT, c ≠ CptT.bot ∧ ApproxTK natEnvU R n Γ ρ (.sort .zero) c :=
  ⟨CptT.prop, by intro h; exact CptT.noConfusion h,
    approxTK_sort_code natEnvU R n Γ ρ Level.zero⟩


-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_ROOTS
#print axioms approxTK_app_inv_four
#print axioms approxTK_app_inv_transport
#print axioms approxTK_interface_status
#print axioms approxTK_eqGapPrefix_lam
#print axioms not_ctxModelTLaws_approxTK
#print axioms approxTK_eqEnvT_nonvacuity
#print axioms approxTK_natEnvU_nonvacuity
-- END RCIC_NATIVE_TYPED_MODEL_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKAudit.KG
