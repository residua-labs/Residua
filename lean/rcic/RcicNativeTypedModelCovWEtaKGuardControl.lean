import rcic.RcicNativeTypedModelCovWEtaControls

/-!
# Independent Eq guard exclusions after finite eta saturation

Every nonbottom Eq-headed observation in the complete new grammar has one
of two necessary syntactic/semantic properties: its actual two index slots
agree uniformly in the independent DI model, or its sixth argument has a
constant head. The second alternative deliberately over-approximates iota;
it is enough to exclude the actual neutral-major controls.

Application preserves this prerequisite. In the eta case, two-way DI
lifting transports agreement back to the source. If eta just introduced
the right index, a fresh variable cannot agree uniformly with an expression
lifted from the previous context. This is proved constructively using two
valuations and the landed lifting equivalence.

The apart-index and native-eta-index sources therefore remain bottom-only
in `ApproxTKWEta`. The final controls retain actual native typings and
conversions, while their negative observation claims are proved anew over
the extended grammar. No new-to-old forgetting map or native index
nonconvertibility premise is used. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelIdealAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKGuardAudit TypedModelKControlAudit TypedModelKObstructionAudit
open TypedModelKTransportAudit TypedModelCovWAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2IndexAudit ReadbackCK2ModelObstructionAudit ReadbackCK2InputsAudit
open PiProbeModelBoundaryAudit

/-- The fresh variable has independent DI observations; a lifted source
cannot depend on its valuation. No decidability or excluded middle is used. -/
theorem covWEtaGuard_fresh_not_uniform (E : ResolvedEnv) (a : Expr Nat) :
    ¬ (∀ ρ : EnvI, SemEqDI E ρ (lift 0 1 a) (.bvar 0)) := by
  intro h
  let S : CptI → Prop := fun c => c = .sort
  have hv : ApproxDI E (EnvI.cons S EnvI.bot) (.bvar 0) .sort := .bvar rfl
  have ha : ApproxDI E EnvI.bot a .sort :=
    (approxDI_lift0_one_iff E EnvI.bot S a .sort).mp
      ((h (EnvI.cons S EnvI.bot) .sort).mpr hv)
  have ha' : ApproxDI E (EnvI.cons (fun _ => False) EnvI.bot) (lift 0 1 a) .sort :=
    (approxDI_lift0_one_iff E EnvI.bot (fun _ => False) a .sort).mpr ha
  have hv' := (h (EnvI.cons (fun _ => False) EnvI.bot) .sort).mp ha'
  rcases approxDI_bvar_inv hv' with hb | hf
  · exact CptI.noConfusion hb
  · exact hf

private theorem covWEtaGuard_uniform_unlift {a b : Expr Nat}
    (h : ∀ ρ : EnvI, SemEqDI eqEnvT ρ (lift 0 1 a) (lift 0 1 b)) :
    ∀ ρ : EnvI, SemEqDI eqEnvT ρ a b := by
  intro ρ
  exact (semEqDI_lift0_one_iff eqEnvT ρ (fun _ => False) a b).mp
    (h (EnvI.cons (fun _ => False) ρ))

private theorem covWEtaGuard_headConst_lift (e : Expr Nat) (cutoff amount : Nat) :
    headConst (lift cutoff amount e) = headConst e := by
  induction e with
  | bvar i =>
      by_cases hi : cutoff ≤ i <;> simp [lift, hi, headConst]
  | sort => rfl
  | const => rfl
  | app f x ihf _ => exact ihf
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit => rfl

private theorem covWEtaGuard_headConst_apps (f : Expr Nat) (xs : List (Expr Nat)) :
    headConst (foldApps f xs) = headConst f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

private theorem covWEtaGuard_appsSpine_lift (e : Expr Nat) (cutoff amount : Nat) :
    appsSpine (lift cutoff amount e) =
      (lift cutoff amount (appsSpine e).1,
        (appsSpine e).2.map (lift cutoff amount)) := by
  induction e with
  | bvar i =>
      by_cases hi : cutoff ≤ i <;> simp [lift, hi, appsSpine]
  | sort => rfl
  | const => rfl
  | app f x ihf _ =>
      simp only [lift, appsSpine, ihf, List.map_append, List.map_singleton]
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit => rfl

/-- A necessary gate for an observable Eq spine: agreement of its actual
index slots, or a constant-headed sixth argument. This is not a native K gate. -/
def CovWEtaEqObservationGate (args : List (Expr Nat)) : Prop :=
  match args with
  | _ :: a :: _ :: _ :: b :: rest =>
      (∀ ρ : EnvI, SemEqDI eqEnvT ρ a b) ∨
        match rest with
        | [] => False
        | x :: _ => headConst x ≠ none
  | _ => False

private theorem covWEtaGuard_gate_append {args : List (Expr Nat)}
    (h : CovWEtaEqObservationGate args) (xs : List (Expr Nat)) :
    CovWEtaEqObservationGate (args ++ xs) := by
  rcases args with _ | ⟨A, args⟩
  · cases h
  rcases args with _ | ⟨a, args⟩
  · cases h
  rcases args with _ | ⟨mot, args⟩
  · cases h
  rcases args with _ | ⟨minor, args⟩
  · cases h
  rcases args with _ | ⟨b, args⟩
  · cases h
  cases args with
  | nil =>
      rcases h with h | h
      · exact Or.inl h
      · exact h.elim
  | cons x args => exact h

private theorem covWEtaGuard_gate_eta_elim {args : List (Expr Nat)}
    (h : CovWEtaEqObservationGate (args.map (lift 0 1) ++ [.bvar 0])) :
    CovWEtaEqObservationGate args := by
  rcases args with _ | ⟨A, args⟩
  · cases h
  rcases args with _ | ⟨a, args⟩
  · cases h
  rcases args with _ | ⟨mot, args⟩
  · cases h
  rcases args with _ | ⟨minor, args⟩
  · cases h
  cases args with
  | nil =>
      change (∀ ρ : EnvI, SemEqDI eqEnvT ρ (lift 0 1 a) (.bvar 0)) ∨ False at h
      rcases h with h | h
      · exact (covWEtaGuard_fresh_not_uniform eqEnvT a h).elim
      · exact h.elim
  | cons b args =>
      cases args with
      | nil =>
          change (∀ ρ : EnvI, SemEqDI eqEnvT ρ (lift 0 1 a) (lift 0 1 b)) ∨
            headConst (.bvar 0) ≠ none at h
          rcases h with hi | hm
          · exact Or.inl (covWEtaGuard_uniform_unlift hi)
          · exact (hm rfl).elim
      | cons x args =>
          change (∀ ρ : EnvI, SemEqDI eqEnvT ρ (lift 0 1 a) (lift 0 1 b)) ∨
            headConst (lift 0 1 x) ≠ none at h
          rcases h with hi | hm
          · exact Or.inl (covWEtaGuard_uniform_unlift hi)
          · exact Or.inr (by simpa only [covWEtaGuard_headConst_lift] using hm)

private theorem covWEtaGuard_five_list (xs : List (Expr Nat)) (h : xs.length = 5) :
    ∃ A a mot minor b, xs = [A, a, mot, minor, b] := by
  rcases xs with _ | ⟨A, xs⟩
  · cases h
  rcases xs with _ | ⟨a, xs⟩
  · cases h
  rcases xs with _ | ⟨mot, xs⟩
  · cases h
  rcases xs with _ | ⟨minor, xs⟩
  · cases h
  rcases xs with _ | ⟨b, xs⟩
  · cases h
  have hn : xs.length = 0 := by simp only [List.length_cons] at h; omega
  have he : xs = [] := List.length_eq_zero.mp hn
  subst xs
  exact ⟨A, a, mot, minor, b, rfl⟩

private theorem covWEtaGuard_pre_length (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    w.preMajor.length = 5 := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  have hp := w.hpre
  omega

/-- A finite induction over every constructor of the eta-extended grammar.
Its eta case includes every possible alternate eta derivation. -/
theorem covWEta_eq_observation_gate {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTKWEta eqEnvT n Γ ρ e c) :
    ∀ {ls : List Level} {args : List (Expr Nat)},
      appsSpine e = (.const 65 ls, args) → c ≠ .bot →
      CovWEtaEqObservationGate args := by
  induction h with
  | bot => intro ls args he hn; exact (hn rfl).elim
  | free hf _ =>
      intro ls args he _
      obtain ⟨S, hS, hs⟩ := hf
      exact (hS.noIndexed 65 (hs 65 (occursConst_true_of_head he))
        indexedPropRecT_eqRec).elim
  | pi => intro ls args he _; cases (Prod.mk.inj he).1
  | lam => intro ls args he _; cases (Prod.mk.inj he).1
  | @app Γ ρ f x g s hf hs hx ihf ihx =>
      intro ls args he _
      have hh : (appsSpine f).1 = .const 65 ls := (Prod.mk.inj he).1
      have hg := ihf (Prod.ext hh rfl) (fun hb => CptT.noConfusion hb)
      have ha : (appsSpine f).2 ++ [x] = args := (Prod.mk.inj he).2
      rw [← ha]
      exact covWEtaGuard_gate_append hg [x]
  | @appSpine Γ ρ f x r us u hf hx ihf ihx =>
      intro ls args he _
      have hh : (appsSpine f).1 = .const 65 ls := (Prod.mk.inj he).1
      have hg := ihf (Prod.ext hh rfl) (fun hb => CptT.noConfusion hb)
      have ha : (appsSpine f).2 ++ [x] = args := (Prod.mk.inj he).2
      rw [← ha]
      exact covWEtaGuard_gate_append hg [x]
  | @delta Γ ρ r ls m b c hd h ih =>
      intro ls' args he _
      have hr : r = 65 := (Expr.const.inj (Prod.mk.inj he).1).1
      subst r
      obtain ⟨hm, _, hnrec, _⟩ := hd
      have hem : m = eqRecT := (Option.some.inj hm).symm
      subst m
      exact (hnrec rfl).elim
  | letE => intro ls args he _; cases (Prod.mk.inj he).1
  | lit => intro ls args he _; cases (Prod.mk.inj he).1
  | @iota Γ ρ c w hs hr ih =>
      intro ls args he _
      have hh := congrArg Prod.fst he
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at hh
      have hw : w.recRef = 65 := (Expr.const.inj hh).1
      have hp := (eqRec_model_schema w hw).2.1
      obtain ⟨A, a, mot, minor, b, hpre⟩ := covWEtaGuard_five_list w.preMajor hp
      have ha := congrArg Prod.snd he
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at ha
      rw [← ha, hpre]
      apply Or.inr
      change headConst (foldApps (.const w.ctorRef w.lsC)
        (w.ctorParams ++ w.fields)) ≠ none
      rw [covWEtaGuard_headConst_apps]
      exact fun hnone => Option.noConfusion hnone
  | @recursorPropK Γ ρ c w x hk hn hi hc hs hr ih =>
      intro ls args he _
      have hh := congrArg Prod.fst he
      simp only [recCall, appsSpine_foldApps_const] at hh
      have hw : w.recRef = 65 := (Expr.const.inj hh).1
      obtain ⟨A, a, mot, minor, b, hpre⟩ :=
        covWEtaGuard_five_list w.preMajor (covWEtaGuard_pre_length w hw)
      have ha := congrArg Prod.snd he
      simp only [recCall, appsSpine_foldApps_const] at ha
      rw [← ha, hpre]
      apply Or.inl
      intro ρI
      have hfamily := hi.2 ρI
      obtain ⟨hcomputed, hmajor⟩ := eqKCanon_families hw hpre hk
      rw [hcomputed, hmajor] at hfamily
      have hrigid : RigidConst eqEnvT 63 :=
        rigidConst_of_inductiveM pinEqGroupWfT (m := eqFamT) rfl rfl
      exact semEqDI_famApp_slot hrigid hrigid hfamily (i := 2) (by simp)
  | @eta Γ ρ e D B a g ht hD hct hne hb ihD ihb =>
      intro ls args he _
      obtain ⟨s, hs, hnonbottom⟩ := hne
      have hspine : appsSpine (.app (lift 0 1 e) (.bvar 0)) =
          (.const 65 ls, args.map (lift 0 1) ++ [.bvar 0]) := by
        simp only [appsSpine, covWEtaGuard_appsSpine_lift, he, lift]
      exact covWEtaGuard_gate_eta_elim (ihb s hs hspine hnonbottom)

private theorem covWEtaGuard_eq_bot (c : CptT) (h : c ≠ .bot → False) : c = .bot := by
  cases c <;> first | rfl | exact (h (fun he => CptT.noConfusion he)).elim

/-- The actual apart indices violate the necessary gate, while the major
is a variable. This applies to every new-grammar observation derivation. -/
theorem covWEta_apart_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta eqEnvT n Γ ρ apartRec c) : c = .bot := by
  apply covWEtaGuard_eq_bot c
  intro hc
  have hg := covWEta_eq_observation_gate h (ls := [.succ (.succ .zero)])
    (args := [.sort .zero, idPiProp, apartMot, .sort .zero, apartRight, .bvar 0]) rfl hc
  change (∀ ρI : EnvI, SemEqDI eqEnvT ρI idPiProp apartRight) ∨
    headConst (.bvar 0) ≠ none at hg
  rcases hg with hi | hm
  · have hrigid : RigidConst eqEnvT 63 :=
      rigidConst_of_inductiveM pinEqGroupWfT (m := eqFamT) rfl rfl
    exact semEqDI_pi_famApp_disjoint hrigid (hi EnvI.bot)
  · exact hm rfl

/-- Native eta equality of the indices still does not supply their separate
uniform DI agreement. The full new observation grammar remains excluded. -/
theorem covWEta_etaIndex_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta eqEnvT n Γ ρ etaIndexRedex c) : c = .bot := by
  apply covWEtaGuard_eq_bot c
  intro hc
  have hg := covWEta_eq_observation_gate h
    (args := [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex, .bvar 0]) rfl hc
  change (∀ ρI : EnvI, SemEqDI eqEnvT ρI (.bvar 1) etaIndex) ∨
    headConst (.bvar 0) ≠ none at hg
  rcases hg with hi | hm
  · exact not_agreementDI_etaIndex (hi EnvI.bot)
  · exact hm rfl

theorem covWEta_apart_observation_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT) :
    ApproxTKWEta eqEnvT n Γ ρ apartRec c ↔ c = .bot := by
  constructor
  · exact covWEta_apart_only_bot
  · intro hc
    subst c
    exact .bot _ _ _

theorem covWEta_etaIndex_observation_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT) :
    ApproxTKWEta eqEnvT n Γ ρ etaIndexRedex c ↔ c = .bot := by
  constructor
  · exact covWEta_etaIndex_only_bot
  · intro hc
    subst c
    exact .bot _ _ _

/-- Admission, native typing and the new exact negative control coexist. -/
theorem covWEta_K_apart_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n apartCtx apartRec apartRec (.sort (.succ .zero))) ∧
    ApproxTKWEta eqEnvT n apartCtx EnvT.bot apartRec .bot ∧
    (∀ ρ c, ApproxTKWEta eqEnvT n apartCtx ρ apartRec c → c = .bot) ∧
    ¬ ApproxTKWEta eqEnvT n apartCtx EnvT.bot apartRec .prop := by
  obtain ⟨hW, hΓ, ht, hc, _, _, _⟩ := covW_K_apart_control n
  exact ⟨hW, hΓ, ht, hc, .bot _ _ _, fun _ _ h => covWEta_apart_only_bot h,
    fun h => CptT.noConfusion (covWEta_apart_only_bot h)⟩

/-- The native eta-index K head remains inhabited, but its separate guard
fails and its source still has only bottom observations after eta saturation. -/
theorem covWEta_K_eta_guard_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    ApproxTKWEta eqEnvT n etaEqCtx EnvT.bot etaIndexRedex .bot ∧
    ApproxTKWEta eqEnvT n etaEqCtx EnvT.bot (.sort .zero) .prop ∧
    (∀ ρ c, ApproxTKWEta eqEnvT n etaEqCtx ρ etaIndexRedex c → c = .bot) ∧
    ¬ KIndexGuardAt eqEnvT n etaEqCtx
      (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot (.sort .zero)) := by
  obtain ⟨hW, hΓ, ht, hc, hk, _, hs, _, hg⟩ := covW_K_eta_guard_control n
  exact ⟨hW, hΓ, ht, hc, hk, .bot _ _ _, covWEta_of_old hs,
    fun _ _ h => covWEta_etaIndex_only_bot h, hg⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_K_GUARD_CONTROL_ROOTS
#print axioms covWEtaGuard_fresh_not_uniform
#print axioms CovWEtaEqObservationGate
#print axioms covWEta_eq_observation_gate
#print axioms covWEta_apart_only_bot
#print axioms covWEta_etaIndex_only_bot
#print axioms covWEta_apart_observation_iff
#print axioms covWEta_etaIndex_observation_iff
#print axioms covWEta_K_apart_control
#print axioms covWEta_K_eta_guard_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_K_GUARD_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
