import rcic.RcicNativeTypedModelCovPTyping
import rcic.RcicNativeTypedModelCovNormConvCases
import rcic.RcicAbelCoquandPin

/-!
# Positive proposition codes, actual proof collapse, and the Abel--Coquand pin

The unchanged model still uses CTyS in its binder demands. The positive
compact-typing guard is a different assertion from collapse of all actual
proof observations. A body-free declaration of the already inhabited True
has a non-bottom rigid proof observation; this refutes the unrestricted
proof-collapse port despite native proof irrelevance.

The Abel--Coquand delta pin does collapse. Its domain observations are old
IsPropCT codes, so all demands on z are bottom and neither application can
produce the non-bottom row required by the unchanged lambda rule. No
positive code is claimed for this empty-environment proposition.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovRelAudit
open TypedModelCovNormConvCasesAudit

variable {E : ResolvedEnv}

/-- This is the exact imported port: both endpoints collapse at every
valuation, without a typed-environment premise or a compact-typing input. -/
theorem covP_proofCollapse_iff (M : CtxModelT E) (p q : Expr Nat) :
    CovProofCollapseFor M p q ↔
      (∀ ρ c, M.Ap ρ p c → c = .bot) ∧
      (∀ ρ c, M.Ap ρ q c → c = .bot) := by
  constructor
  · intro h
    exact ⟨fun ρ c hc => h ρ ρ c (Or.inl hc),
      fun ρ c hc => h ρ ρ c (Or.inr hc)⟩
  · rintro ⟨hp, hq⟩ ρ ρ' c hc
    exact hc.elim (hp ρ c) (hq ρ' c)

/-- The positive typing guard supplies actual collapse only after each
actual proof observation has a positively proposition-typed code. -/
theorem covP_proofCollapse_of_positive_typing (C : CovTypingP E)
    (M : CtxModelT E) (p q : Expr Nat)
    (ht : ∀ ρ ρ' c, M.Ap ρ p c ∨ M.Ap ρ' q c →
      ∃ a, IsPropCTP E a ∧ C.ty c a) :
    CovProofCollapseFor M p q := by
  intro ρ ρ' c hc
  obtain ⟨a, ha, ht⟩ := ht ρ ρ' c hc
  exact C.prop_bot ha ht

theorem covP_true_positive : IsPropCTP trueEnvU (.spine 0 []) :=
  .spine (m := trueFamMember) rfl rfl

theorem covP_true_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK trueEnvU n Γ ρ (.const 0 []) (.spine 0 []) := by
  have hr : RigidConst trueEnvU 0 := by
    intro m hm
    have he : m = trueFamMember := Option.some.inj hm.symm
    subst m
    exact ⟨Or.inl rfl, by decide⟩
  have hn : ¬ PropCtorT trueEnvU 0 := by
    rintro ⟨m, fam, fm, hm, hctor, _⟩
    have he : m = trueFamMember := Option.some.inj hm.symm
    subst m
    exact MemberClass.noConfusion hctor
  exact .free (kFreeT_rigid_const hr []) (.const ρ 0 [] hr hn)

/-- Instantiating the generic universe-seed obstruction at True uses an
actual non-bottom proposition code typed in the Prop universe. -/
theorem covP_prop_universe_seed_no (reflect : Bool) (P : CptT → Prop)
    (hp : P .prop)
    (hc : ∀ {a u}, P a → CTyCovP2 reflect trueEnvU u a → u = .bot) : False :=
  prop_universe_seed_incompatible (CTyCovP2 reflect trueEnvU) P hp hc
    (show CTyCovP2 reflect trueEnvU (.spine 0 []) .prop from
      .univProp (isPropCT_of_isPropCTP covP_true_positive))

theorem covP_prop_universe_seed_control (reflect : Bool) (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    ApproxTK trueEnvU n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    IsPropCTP trueEnvU (.spine 0 []) ∧
    CTyCovP2 reflect trueEnvU (.spine 0 []) .prop ∧
    (.spine 0 [] : CptT) ≠ .bot ∧
    ∀ P : CptT → Prop, P .prop →
      ¬ (∀ {a u}, P a → CTyCovP2 reflect trueEnvU u a → u = .bot) := by
  exact ⟨⟨trueEnvUWfT⟩, ⟨.nil⟩, ⟨trueConstTyT rfl⟩,
    covP_true_observed n [] EnvT.bot, covP_true_positive,
    .univProp (isPropCT_of_isPropCTP covP_true_positive),
    (fun h => CptT.noConfusion h),
    fun P hp hc => covP_prop_universe_seed_no reflect P hp hc⟩

theorem covP_trueIntro_collapse (n : Nat) (Γ : LCtx) :
    CovProofCollapseFor (ctxModelT_approxTK trueEnvU n Γ)
      (.const 1 []) (.const 1 []) := by
  intro ρ ρ' c hc
  exact hc.elim (fun h => approxT_trueIntro_bot ρ (approxTK_forget h))
    (fun h => approxT_trueIntro_bot ρ' (approxTK_forget h))

/-- A real positive proposition and a proof whose observations collapse.
The native irr derivation and the model's bottom observation are inhabited. -/
theorem covP_trueIntro_control (reflect : Bool) (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT trueEnvU n [] (.const 1 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP trueEnvU (.spine 0 []) ∧
    CTyCovP2 reflect trueEnvU .bot (.spine 0 []) ∧
    ApproxTK trueEnvU n [] EnvT.bot (.const 1 []) .bot ∧
    CovProofCollapseFor (ctxModelT_approxTK trueEnvU n [])
      (.const 1 []) (.const 1 []) := by
  have hp : HasTyT trueEnvU n [] (.const 1 []) (.const 0 []) :=
    .const [] 1 [] trueIntroMember rfl rfl rfl
  exact ⟨⟨trueEnvUWfT⟩, ⟨.nil⟩, ⟨trueConstTyT rfl⟩, ⟨hp⟩,
    ⟨.irr [] (.const 0 []) (.const 1 []) (.const 1 []) (trueConstTyT rfl) hp hp⟩,
    covP_true_positive, .bot _, .bot _ _ _, covP_trueIntro_collapse n []⟩

/-- This adds an object-language declaration of an already inhabited type;
it is an ordinary native EnvWfT constructor, not a Lean axiom. -/
def covPProofMember : CheckedMember := ⟨.axiomM, 0, .const 0 [], none⟩

def covPProofEnv : ResolvedEnv := extendEnv trueEnvU 3 covPProofMember

def covPProofEnvWfT : EnvWfT covPProofEnv :=
  .axiom trueEnvU 3 (.const 0 []) .zero trueEnvUWfT rfl
    (trueConstTyT rfl) (fun _ => rfl) rfl

theorem covPProof_true_positive : IsPropCTP covPProofEnv (.spine 0 []) :=
  .spine (m := trueFamMember) rfl rfl

theorem covPProof_head_rigid : RigidConst covPProofEnv 3 := by
  intro m hm
  have he : m = covPProofMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covPProof_head_not_propCtor : ¬ PropCtorT covPProofEnv 3 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = covPProofMember := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

theorem covPProof_true_rigid : RigidConst covPProofEnv 0 := by
  intro m hm
  have he : m = trueFamMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covPProof_true_not_propCtor : ¬ PropCtorT covPProofEnv 0 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = trueFamMember := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

theorem covPProof_head_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covPProofEnv n Γ ρ (.const 3 []) (.spine 3 []) :=
  .free (kFreeT_rigid_const covPProof_head_rigid [])
    (.const ρ 3 [] covPProof_head_rigid covPProof_head_not_propCtor)

theorem covPProof_true_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covPProofEnv n Γ ρ (.const 0 []) (.spine 0 []) :=
  .free (kFreeT_rigid_const covPProof_true_rigid [])
    (.const ρ 0 [] covPProof_true_rigid covPProof_true_not_propCtor)

/-- The imported constant inversion excludes every non-bottom constructor
observation when both rigidness and proposition-constructor status hold. -/
theorem covP_approxT_rigid_propCtor_bot {r : Nat} {ls : List Level}
    (hr : RigidConst E r) (hp : PropCtorT E r) {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ (.const r ls) c) : c = .bot := by
  rcases approxT_const_inv h with hb | ⟨_, hnp, _⟩ | ⟨m, b, hd, _⟩ |
      ⟨w, _, _, _, hw, _⟩ | ⟨w, _, _, hw, _⟩
  · exact hb
  · exact (hnp hp).elim
  · exact (not_rigidConst_of_deltaConst hd hr).elim
  · have hm := w.hrec
    rw [hw] at hm
    exact ((hr w.recMember hm).2 w.hrecK).elim
  · have hm := w.hrec
    rw [hw] at hm
    exact ((hr w.recMember hm).2 w.hrecK).elim

theorem covPProof_intro_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT covPProofEnv ρ (.const 1 []) c) : c = .bot := by
  have hr : RigidConst covPProofEnv 1 := by
    intro m hm
    have he : m = trueIntroMember := Option.some.inj hm.symm
    subst m
    exact ⟨Or.inl rfl, by decide⟩
  have hp : PropCtorT covPProofEnv 1 :=
    ⟨trueIntroMember, 0, trueFamMember, rfl, rfl, rfl, rfl, rfl⟩
  exact covP_approxT_rigid_propCtor_bot hr hp h

/-- Native irr identifies the terms, while actual observation transport
fails. This is stronger than rejecting the all-valuations collapse port. -/
theorem covPProof_irr_contract_no (n : Nat) (Γ : LCtx) :
    ¬ CovModelContractAt (ctxModelT_approxTK covPProofEnv n Γ)
      (.const 3 []) (.const 1 []) := by
  intro h
  exact CptT.noConfusion (covPProof_intro_bot (approxTK_forget
    (h EnvT.bot (.spine 3 []) (covPProof_head_observed n Γ EnvT.bot))))

/-- Every actual code of True excludes this actual non-bottom proof
observation under both proposed compact typings. No code choice repairs it. -/
theorem covPProof_no_observed_type_code (reflect : Bool) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ¬ ∃ a, ApproxTK covPProofEnv n Γ ρ (.const 0 []) a ∧
      CTyCovP2 reflect covPProofEnv (.spine 3 []) a := by
  rintro ⟨a, ha, ht⟩
  rcases approxT_rigid_const_inv covPProof_true_rigid (approxTK_forget ha) with rfl | rfl
  · exact CptT.noConfusion (ctyCovP2_bot_inv ht)
  · exact CptT.noConfusion (ctyCovP2_prop_bot covPProof_true_positive ht)

theorem covPProof_collapse_no (n : Nat) (Γ : LCtx) :
    ¬ CovProofCollapseFor (ctxModelT_approxTK covPProofEnv n Γ)
      (.const 3 []) (.const 1 []) := by
  intro h
  exact CptT.noConfusion
    (h EnvT.bot EnvT.bot (.spine 3 []) (Or.inl (covPProof_head_observed n Γ EnvT.bot)))

/-- Native proof irrelevance and all source certificates coexist with the
counterobservation at a genuine positive proposition code. The old port is
therefore a separate semantic obligation, not a consequence of native irr. -/
theorem covPProof_native_irr_counterexample (reflect : Bool) (n : Nat) :
    Nonempty (EnvWfT covPProofEnv) ∧ Nonempty (CtxWfT covPProofEnv n []) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covPProofEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP covPProofEnv (.spine 0 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 1 []) .bot ∧
    (.spine 3 [] : CptT) ≠ .bot ∧
    (¬ ∃ a, ApproxTK covPProofEnv n [] EnvT.bot (.const 0 []) a ∧
      CTyCovP2 reflect covPProofEnv (.spine 3 []) a) ∧
    (¬ CovProofCollapseFor (ctxModelT_approxTK covPProofEnv n [])
      (.const 3 []) (.const 1 [])) ∧
    ¬ CovModelContractAt (ctxModelT_approxTK covPProofEnv n [])
      (.const 3 []) (.const 1 []) := by
  have hp : HasTyT covPProofEnv n [] (.const 3 []) (.const 0 []) :=
    .const [] 3 [] covPProofMember rfl rfl rfl
  have hq : HasTyT covPProofEnv n [] (.const 1 []) (.const 0 []) :=
    .const [] 1 [] trueIntroMember rfl rfl rfl
  exact ⟨⟨covPProofEnvWfT⟩, ⟨.nil⟩, ⟨trueConstTyT rfl⟩, ⟨hp⟩, ⟨hq⟩,
    ⟨.irr [] (.const 0 []) (.const 3 []) (.const 1 []) (trueConstTyT rfl) hp hq⟩,
    covPProof_true_positive, covPProof_true_observed n [] EnvT.bot,
    covPProof_head_observed n [] EnvT.bot, .bot _ _ _,
    (fun h => CptT.noConfusion h), covPProof_no_observed_type_code reflect n [] EnvT.bot,
    covPProof_collapse_no n [], covPProof_irr_contract_no n []⟩

/-- An application whose function has only bottom observations has only
bottom observations. Both application alternatives are checked explicitly. -/
theorem covP_approxT_app_bot_of_head {ρ : EnvT} {f x : Expr Nat}
    (hf : ∀ c, ApproxT E ρ f c → c = .bot) {c : CptT}
    (h : ApproxT E ρ (.app f x) c) : c = .bot := by
  rcases approxT_app_inv h with hb | ⟨g, s, _, hfun, _⟩ | ⟨r, args, u, _, hfun, _⟩
  · exact hb
  · exact CptT.noConfusion (hf (.lam g) hfun)
  · exact CptT.noConfusion (hf (.spine r args) hfun)

theorem covP_abelCoquand_bot_code {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ AbelCoquand.bot c) : IsPropCT E c := by
  rcases approxT_pi_inv h with rfl | ⟨a, g, rfl, hA, hg⟩
  · exact .bot
  · have ha : a = .bot ∨ a = .prop := by
      simpa only [sortCode_zero] using approxT_sort_inv hA
    have hta : TyCodeCT a := by rcases ha with rfl | rfl <;> constructor
    apply IsPropCT.pi hta
    intro row hr
    have ho := approxT_bvar_propDemand_bot ha (hg row hr).1 (hg row hr).2
    rcases ho with hb | hp
    · rw [hb]
      exact .bot
    · exact hp

theorem covP_abelCoquand_top_code {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ AbelCoquand.top c) : IsPropCT E c := by
  rcases approxT_pi_inv h with rfl | ⟨a, g, rfl, hA, hg⟩
  · exact .bot
  · exact .pi (tyCodeCT_of_isPropCT (covP_abelCoquand_bot_code hA))
      (fun row hr => covP_abelCoquand_bot_code (hg row hr).2)

/-- The proof uses the actual unchanged domain-demand typing and the actual
lambda non-bottom-output premise; no new positive-code hypothesis is used. -/
theorem covP_abelCoquand_delta_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ AbelCoquand.delta c) : c = .bot := by
  rcases approxT_lam_inv h with hb | ⟨a, g, _, hA, ⟨row, hr, hnb⟩, hg⟩
  · exact hb
  · have hp := covP_abelCoquand_bot_code hA
    have hz : ∀ v, ApproxT E (EnvT.cons (demandT row.1) ρ) (.bvar 0) v → v = .bot := by
      intro v hv
      rcases approxT_bvar_inv hv with hb | hv
      · exact hb
      · exact ctyS_prop_bot hp ((hg row hr).1 v hv)
    have hzTop : ∀ v, ApproxT E (EnvT.cons (demandT row.1) ρ)
        (.app (.bvar 0) AbelCoquand.top) v → v = .bot :=
      fun _ hv => covP_approxT_app_bot_of_head hz hv
    exact (hnb (covP_approxT_app_bot_of_head hzTop (hg row hr).2)).elim

theorem covP_abelCoquand_delta_collapse (n : Nat) (Γ : LCtx) :
    CovProofCollapseFor (ctxModelT_approxTK E n Γ)
      AbelCoquand.delta AbelCoquand.delta := by
  intro ρ ρ' c hc
  exact hc.elim (fun h => covP_abelCoquand_delta_bot (approxTK_forget h))
    (fun h => covP_abelCoquand_delta_bot (approxTK_forget h))

def covPAbelCoquandId : Expr Nat := .lam AbelCoquand.bot (.bvar 0)

def covPAbelCoquandId_hasTy (n : Nat) :
    HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top :=
  .lam [] AbelCoquand.bot AbelCoquand.uBot (.bvar 0) AbelCoquand.bot
    (AbelCoquand.botHasTyAt n []) (AbelCoquand.zTy n)

theorem covP_abelCoquand_id_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ covPAbelCoquandId c) : c = .bot := by
  rcases approxT_lam_inv h with hb | ⟨a, g, _, hA, ⟨row, hr, hnb⟩, hg⟩
  · exact hb
  · have hp := covP_abelCoquand_bot_code hA
    rcases approxT_bvar_inv (hg row hr).2 with hb | hv
    · exact (hnb hb).elim
    · exact (hnb (ctyS_prop_bot hp ((hg row hr).1 row.2 hv))).elim

/-- The successful AC irrelevance control compares distinct proof terms,
delta and the ordinary identity, at the same actual native proposition. -/
theorem covP_abelCoquand_distinct_proofs_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta covPAbelCoquandId AbelCoquand.top) ∧
    ApproxTK emptyEnv n [] EnvT.bot AbelCoquand.delta .bot ∧
    ApproxTK emptyEnv n [] EnvT.bot covPAbelCoquandId .bot ∧
    CovProofCollapseFor (ctxModelT_approxTK emptyEnv n [])
      AbelCoquand.delta covPAbelCoquandId := by
  refine ⟨⟨.empty⟩, ⟨.nil⟩, ⟨AbelCoquand.topIsPropAt n []⟩,
    ⟨AbelCoquand.deltaHasTy n⟩, ⟨covPAbelCoquandId_hasTy n⟩,
    ⟨.irr [] AbelCoquand.top AbelCoquand.delta covPAbelCoquandId
      (AbelCoquand.topIsPropAt n []) (AbelCoquand.deltaHasTy n)
      (covPAbelCoquandId_hasTy n)⟩, .bot _ _ _, .bot _ _ _, ?_⟩
  intro ρ ρ' c hc
  exact hc.elim (fun h => covP_abelCoquand_delta_bot (approxTK_forget h))
    (fun h => covP_abelCoquand_id_bot (approxTK_forget h))

theorem covP_abelCoquand_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta AbelCoquand.delta AbelCoquand.top) ∧
    ApproxTK emptyEnv n [] EnvT.bot AbelCoquand.delta .bot ∧
    ApproxTK emptyEnv n [] EnvT.bot AbelCoquand.top (.pi .bot []) ∧
    IsPropCT emptyEnv (.pi .bot []) ∧
    (¬ IsPropCTP emptyEnv (.pi .bot [])) ∧
    (∀ a, ¬ IsPropCTP emptyEnv a) ∧
    CovProofCollapseFor (ctxModelT_approxTK emptyEnv n [])
      AbelCoquand.delta AbelCoquand.delta := by
  exact ⟨⟨.empty⟩, ⟨.nil⟩, ⟨AbelCoquand.topIsPropAt n []⟩,
    ⟨AbelCoquand.deltaHasTy n⟩,
    ⟨.irr [] AbelCoquand.top AbelCoquand.delta AbelCoquand.delta
      (AbelCoquand.topIsPropAt n []) (AbelCoquand.deltaHasTy n) (AbelCoquand.deltaHasTy n)⟩,
    .bot _ _ _, approxTK_pi_bot_nil emptyEnv n [] EnvT.bot _ _,
    .pi .bot (by simp), not_isPropCTP_pi_nil emptyEnv .bot,
    fun _ => not_isPropCTP_emptyEnv, covP_abelCoquand_delta_collapse n []⟩

/-- The landed irr-step theorem consumes the concrete AC collapse port.
This does not convert C2P into the frozen old CovTyping structure. -/
theorem covP_abelCoquand_irr_step (C : CovTyping emptyEnv)
    (R : Readback) (n : Nat) :
    FundConvCovStep C (ctxModelT_approxTK emptyEnv n []) R n
      (ConvT.irr [] AbelCoquand.top AbelCoquand.delta AbelCoquand.delta
        (AbelCoquand.topIsPropAt n []) (AbelCoquand.deltaHasTy n)
        (AbelCoquand.deltaHasTy n)) :=
  fundCov_irr_step_of_collapse (AbelCoquand.topIsPropAt n [])
    (AbelCoquand.deltaHasTy n) (AbelCoquand.deltaHasTy n)
    (covP_abelCoquand_delta_collapse n [])

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_PROOF_COLLAPSE_ROOTS
#print axioms covP_proofCollapse_iff
#print axioms covP_proofCollapse_of_positive_typing
#print axioms covP_true_positive
#print axioms covP_true_observed
#print axioms covP_prop_universe_seed_no
#print axioms covP_prop_universe_seed_control
#print axioms covP_trueIntro_collapse
#print axioms covP_trueIntro_control
#print axioms covPProofMember
#print axioms covPProofEnv
#print axioms covPProofEnvWfT
#print axioms covPProof_true_positive
#print axioms covPProof_head_rigid
#print axioms covPProof_head_not_propCtor
#print axioms covPProof_true_rigid
#print axioms covPProof_true_not_propCtor
#print axioms covPProof_head_observed
#print axioms covPProof_true_observed
#print axioms covP_approxT_rigid_propCtor_bot
#print axioms covPProof_intro_bot
#print axioms covPProof_irr_contract_no
#print axioms covPProof_no_observed_type_code
#print axioms covPProof_collapse_no
#print axioms covPProof_native_irr_counterexample
#print axioms covP_approxT_app_bot_of_head
#print axioms covP_abelCoquand_bot_code
#print axioms covP_abelCoquand_top_code
#print axioms covP_abelCoquand_delta_bot
#print axioms covP_abelCoquand_delta_collapse
#print axioms covPAbelCoquandId
#print axioms covPAbelCoquandId_hasTy
#print axioms covP_abelCoquand_id_bot
#print axioms covP_abelCoquand_distinct_proofs_control
#print axioms covP_abelCoquand_control
#print axioms covP_abelCoquand_irr_step
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_PROOF_COLLAPSE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
