import rcic.RcicNativeTypedModelCovWIrrelCompact
import rcic.RcicNativeTypedModelCovWEtaActions

/-!
# Proof-erasing rigid observations at the actual universe instance

The raw and guarded grammars retain the actual universe vector in every
spine. At a declared native proof position only a bottom field is emitted.
An argument is always allowed at bottom, without reading it. A nonbottom
field requires native evidence that this exact position is not a proof.
The side condition refers only to landed native typing, never negatively
to the observation relation. Native eta remains in the guarded grammar;
raw remains strict. The per-call K certificates are unchanged.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2ConvAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelKAudit TypedModelCovVAudit TypedModelKIndexFreeAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovWEtaAudit

inductive ApproxTWIrrel (E : ResolvedEnv) (n : Nat) : EnvWIrrel → Expr Nat → CptWIrrel → Prop
  | bot (ρ : EnvWIrrel) (e : Expr Nat) : ApproxTWIrrel E n ρ e .bot
  | bvar {ρ : EnvWIrrel} {i : Nat} {c : CptWIrrel} (h : ρ i c) : ApproxTWIrrel E n ρ (.bvar i) c
  | sort (ρ : EnvWIrrel) (l : Level) : ApproxTWIrrel E n ρ (.sort l) (sortCodeWIrrel l)
  | pi {ρ : EnvWIrrel} {A B : Expr Nat} {a : CptWIrrel} {f : List (List CptWIrrel × CptWIrrel)}
      (hA : ApproxTWIrrel E n ρ A a)
      (hT : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hf : ∀ s ∈ f, ApproxTWIrrel E n (EnvWIrrel.cons (demandWIrrel s.1) ρ) B s.2) :
      ApproxTWIrrel E n ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvWIrrel} {A b : Expr Nat} {a : CptWIrrel} {g : List (List CptWIrrel × CptWIrrel)}
      (hA : ApproxTWIrrel E n ρ A a)
      (hT : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hnt : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTWIrrel E n (EnvWIrrel.cons (demandWIrrel s.1) ρ) b s.2) :
      ApproxTWIrrel E n ρ (.lam A b) (.lam g)
  | app {ρ : EnvWIrrel} {f a : Expr Nat} {g : List (List CptWIrrel × CptWIrrel)} {s : List CptWIrrel × CptWIrrel}
      (hf : ApproxTWIrrel E n ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxTWIrrel E n ρ a u) :
      ApproxTWIrrel E n ρ (.app f a) s.2
  | const (ρ : EnvWIrrel) (r : Nat) (ls : List Level) (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxTWIrrel E n ρ (.const r ls) (.spine r ls [])
  | delta {ρ : EnvWIrrel} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat} {c : CptWIrrel}
      (hdelta : DeltaConst E r m b)
      (h : ApproxTWIrrel E n EnvWIrrel.bot (instantiateLevels ls b) c) :
      ApproxTWIrrel E n ρ (.const r ls) c
  | recursor {ρ : EnvWIrrel} {w : IotaWitnessS E} (ls : List Level) (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptWIrrel)} {us_fields : List (List CptWIrrel)} {c : CptWIrrel}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTWIrrel E n (EnvWIrrel.pushArgs ((us_pre ++ us_fields).map demandWIrrel) EnvWIrrel.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTWIrrel E n ρ (.const w.recRef ls)
        (curryStepWIrrel (us_pre ++ [ctorDemandWIrrel w.ctorRef w.lsC w.nparams us_fields]) c)
  | appSpine {ρ : EnvWIrrel} {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWIrrel} {u : CptWIrrel}
      (hf : ApproxTWIrrel E n ρ f (.spine r ls args)) (ha : ApproxTWIrrel E n ρ a u)
      (hslot : CovWIrrelProofPosition E n r ls args.length → u = .bot) :
      ApproxTWIrrel E n ρ (.app f a) (.spine r ls (args ++ [u]))
  | letE {ρ : EnvWIrrel} {A v b : Expr Nat} {c : CptWIrrel}
      (h : ApproxTWIrrel E n ρ (.app (.lam A b) v) c) :
      ApproxTWIrrel E n ρ (.letE A v b) c
  | lit {ρ : EnvWIrrel} {t : Nat} {c : CptWIrrel}
      (h : ApproxTWIrrel E n ρ (natExpand t) c) :
      ApproxTWIrrel E n ρ (.lit t) c

inductive ApproxTKWIrrel (E : ResolvedEnv) (n : Nat) : LCtx → EnvWIrrel → Expr Nat → CptWIrrel → Prop
  | bot (Γ : LCtx) (ρ : EnvWIrrel) (e : Expr Nat) : ApproxTKWIrrel E n Γ ρ e .bot
  | free {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
      (hfree : KFreeT E e) (h : ApproxTWIrrel E n ρ e c) : ApproxTKWIrrel E n Γ ρ e c
  | pi {Γ : LCtx} {ρ : EnvWIrrel} {A B : Expr Nat} {a : CptWIrrel}
      {f : List (List CptWIrrel × CptWIrrel)}
      (hA : ApproxTKWIrrel E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hb : ∀ s ∈ f, ApproxTKWIrrel E n (.assumption A :: Γ)
        (EnvWIrrel.cons (demandWIrrel s.1) ρ) B s.2) :
      ApproxTKWIrrel E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvWIrrel} {A b : Expr Nat} {a : CptWIrrel}
      {g : List (List CptWIrrel × CptWIrrel)}
      (hA : ApproxTKWIrrel E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWIrrel E n (.assumption A :: Γ)
        (EnvWIrrel.cons (demandWIrrel s.1) ρ) b s.2) :
      ApproxTKWIrrel E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvWIrrel} {f a : Expr Nat}
      {g : List (List CptWIrrel × CptWIrrel)} {s : List CptWIrrel × CptWIrrel}
      (hf : ApproxTKWIrrel E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKWIrrel E n Γ ρ a u) :
      ApproxTKWIrrel E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvWIrrel} {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWIrrel} {u : CptWIrrel}
      (hf : ApproxTKWIrrel E n Γ ρ f (.spine r ls args))
      (ha : ApproxTKWIrrel E n Γ ρ a u)
      (hslot : CovWIrrelProofPosition E n r ls args.length → u = .bot) :
      ApproxTKWIrrel E n Γ ρ (.app f a) (.spine r ls (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvWIrrel} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptWIrrel} (hd : DeltaConst E r m b)
      (h : ApproxTKWIrrel E n [] EnvWIrrel.bot (instantiateLevels ls b) c) :
      ApproxTKWIrrel E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvWIrrel} {A v b : Expr Nat} {c : CptWIrrel}
      (h : ApproxTKWIrrel E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKWIrrel E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvWIrrel} {t : Nat} {c : CptWIrrel}
      (h : ApproxTKWIrrel E n Γ ρ (natExpand t) c) :
      ApproxTKWIrrel E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvWIrrel} {c : CptWIrrel} (w : IotaWitnessS E)
      (hsource : ApproxTN E (covWIrrelEnvErase ρ) (iotaLhsOfS w) (covWIrrelErase c))
      (hrhs : ApproxTKWIrrel E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTKWIrrel E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvWIrrel} {c : CptWIrrel} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexGuardAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hsource : ApproxTN E (covWIrrelEnvErase ρ) (recCall (.const w.recRef w.ls) w.preMajor x) (covWIrrelErase c))
      (hrhs : ApproxTKWIrrel E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWIrrel E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

  | eta {Γ : LCtx} {ρ : EnvWIrrel} {e D B : Expr Nat} {a : CptWIrrel}
      {g : List (List CptWIrrel × CptWIrrel)}
      (he : HasTyT E n Γ e (.pi D B))
      (hD : ApproxTKWIrrel E n Γ ρ D a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWIrrel E n (.assumption D :: Γ)
        (EnvWIrrel.cons (demandWIrrel s.1) ρ) (.app (lift 0 1 e) (.bvar 0)) s.2) :
      ApproxTKWIrrel E n Γ ρ e (.lam g)


private theorem rows_typed {E : ResolvedEnv} {a : CptWIrrel}
    {rows : List (List CptWIrrel × CptWIrrel)}
    (h : ∀ s ∈ rows, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a)) :
    ∀ s ∈ rows.map covWIrrelRowErase, ∀ u ∈ s.1, CTyS E u (covWIrrelErase a) := by
  intro s hs u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact h t ht v hv

private theorem rows_nonbottom {rows : List (List CptWIrrel × CptWIrrel)}
    (h : ∃ s ∈ rows, s.2 ≠ .bot) :
    ∃ s ∈ rows.map covWIrrelRowErase, s.2 ≠ .bot := by
  obtain ⟨s, hs, hn⟩ := h
  exact ⟨covWIrrelRowErase s, List.mem_map.mpr ⟨s, hs, rfl⟩,
    fun h => hn ((covWIrrel_erase_bot_iff s.2).mp h)⟩

/-- Erasure forgets the added provenance and proof-position restriction.
This is a one-way theorem; no blanket transfer from the old grammar is used. -/
theorem covWIrrel_raw_forget {E : ResolvedEnv} {n : Nat} {ρ : EnvWIrrel}
    {e : Expr Nat} {c : CptWIrrel} (h : ApproxTWIrrel E n ρ e c) :
    ApproxTW E (covWIrrelEnvErase ρ) e (covWIrrelErase c) := by
  induction h with
  | bot => exact .bot _ _
  | bvar h => exact .bvar ⟨_, h, rfl⟩
  | sort ρ l => rw [covWIrrel_erase_sortCode]; exact .sort _ _
  | pi hA ht hb ihA ihb =>
      simp only [covWIrrelErase, covWIrrel_erase_rows]
      refine .pi ihA (rows_typed ht) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWIrrel_env_erase_cons, covWIrrelRowErase] using ihb t ht
  | lam hA ht hn hb ihA ihb =>
      simp only [covWIrrelErase, covWIrrel_erase_rows]
      refine .lam ihA (rows_typed ht) (rows_nonbottom hn) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWIrrel_env_erase_cons, covWIrrelRowErase] using ihb t ht
  | app hf hs ha ihf iha =>
      simp only [covWIrrelErase, covWIrrel_erase_rows] at ihf
      refine .app ihf (List.mem_map.mpr ⟨_, hs, rfl⟩) ?_
      intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      exact iha v hv
  | const ρ r ls hr hp => exact .const _ _ _ hr hp
  | delta hd h ih =>
      exact .delta hd (by simpa only [covWIrrel_env_erase_bot] using ih)
  | recursor ls hp hpre hf h ih =>
      rw [covWIrrel_erase_curry]
      simp only [List.map_append, List.map_cons, List.map_nil, covWIrrel_erase_ctorDemand]
      apply ApproxTW.recursor ls hp
      · simpa only [List.length_map] using hpre
      · simpa only [List.length_map] using hf
      · rw [covWIrrel_env_erase_push, covWIrrel_env_erase_bot] at ih
        simpa only [List.map_append] using ih
  | appSpine hf ha hslot ihf iha =>
      simpa only [covWIrrelErase, covWIrrel_erase_args, List.map_append, List.map_cons,
        List.map_nil] using ApproxTW.appSpine ihf iha
  | letE h ih => exact .letE ih
  | lit h ih => exact .lit ih

/-- Every repaired guarded observation has its old eta observation after
structural erasure. Negative K controls proved for the complete old eta
grammar therefore remain valid. -/
theorem covWIrrel_guarded_forget {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWIrrel E n Γ ρ e c) :
    ApproxTKWEta E n Γ (covWIrrelEnvErase ρ) e (covWIrrelErase c) := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf (covWIrrel_raw_forget h)
  | pi hA ht hb ihA ihb =>
      simp only [covWIrrelErase, covWIrrel_erase_rows]
      refine .pi ihA (rows_typed ht) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWIrrel_env_erase_cons, covWIrrelRowErase] using ihb t ht
  | lam hA ht hn hb ihA ihb =>
      simp only [covWIrrelErase, covWIrrel_erase_rows]
      refine .lam ihA (rows_typed ht) (rows_nonbottom hn) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWIrrel_env_erase_cons, covWIrrelRowErase] using ihb t ht
  | app hf hs ha ihf iha =>
      simp only [covWIrrelErase, covWIrrel_erase_rows] at ihf
      refine .app ihf (List.mem_map.mpr ⟨_, hs, rfl⟩) ?_
      intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      exact iha v hv
  | appSpine hf ha hslot ihf iha =>
      simpa only [covWIrrelErase, covWIrrel_erase_args, List.map_append, List.map_cons,
        List.map_nil] using ApproxTKWEta.appSpine ihf iha
  | delta hd h ih =>
      exact .delta hd (by simpa only [covWIrrel_env_erase_bot] using ih)
  | letE h ih => exact .letE ih
  | lit h ih => exact .lit ih
  | iota w hs h ih => exact .iota w hs ih
  | recursorPropK w x hk hn hi hc hs h ih =>
      exact .recursorPropK w x hk hn hi hc hs ih
  | eta he hD ht hn hb ihD ihb =>
      simp only [covWIrrelErase, covWIrrel_erase_rows]
      refine .eta he ihD (rows_typed ht) (rows_nonbottom hn) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWIrrel_env_erase_cons, covWIrrelRowErase] using ihb t ht

/-- Raw adequacy is retained constructively, with the landed extensional
graph action at the structurally erased compact. -/
theorem covWIrrelRaw_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptWIrrel}
    (ht : HasTyT E n Γ e A) (ho : ApproxTWIrrel E n EnvWIrrel.bot e c) :
    CovWEtaRawAction E n Γ (covWIrrelErase c) e A :=
  covWEtaRaw_closed hW ht (by
    simpa only [covWIrrel_env_erase_bot] using covWIrrel_raw_forget ho)

/-- A bottom field always supplies the new rule without a classifier. -/
theorem covWIrrel_raw_appSpine_bot {E : ResolvedEnv} {n : Nat} {ρ : EnvWIrrel}
    {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWIrrel}
    (hf : ApproxTWIrrel E n ρ f (.spine r ls args)) :
    ApproxTWIrrel E n ρ (.app f a) (.spine r ls (args ++ [.bot])) :=
  .appSpine hf (.bot _ _) (fun _ => rfl)

theorem covWIrrel_guarded_appSpine_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWIrrel}
    (hf : ApproxTKWIrrel E n Γ ρ f (.spine r ls args)) :
    ApproxTKWIrrel E n Γ ρ (.app f a) (.spine r ls (args ++ [.bot])) :=
  .appSpine hf (.bot _ _ _) (fun _ => rfl)

def ApproxTKWIrrelStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (e : Expr Nat) (c : CptWIrrel) : Prop :=
  ApproxTKWIrrel E arity Γ ρ e c ∧ covTObservationBudget (covWIrrelErase c) ≤ stage

theorem ApproxTKWIrrelStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWIrrelStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKWIrrelStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

structure CovWIrrelRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ i c, ρ i c → ApproxTKWIrrelStage E arity stage [] EnvWIrrel.bot (σ i) c

theorem covWIrrel_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovWIrrelRealized E arity stage [] EnvWIrrel.bot SubstT.id := by
  refine ⟨(covW_realized_nil E arity stage).typing, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

/-- Universe labels are provenance, not additional observable distinctions.
The externally tested compact is the original finite compact after erasure. -/
def CovWIrrelObservation (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (e : Expr Nat) (c : CptT) : Prop :=
  ∃ d : CptWIrrel, covWIrrelErase d = c ∧ ApproxTKWIrrel E n Γ ρ e d

def CovWIrrelRawObservation (E : ResolvedEnv) (n : Nat)
    (ρ : EnvWIrrel) (e : Expr Nat) (c : CptT) : Prop :=
  ∃ d : CptWIrrel, covWIrrelErase d = c ∧ ApproxTWIrrel E n ρ e d

theorem covWIrrel_observation_of {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWIrrel E n Γ ρ e c) :
    CovWIrrelObservation E n Γ ρ e (covWIrrelErase c) := ⟨c, rfl, h⟩

theorem covWIrrel_observation_forget {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e : Expr Nat} {c : CptT}
    (h : CovWIrrelObservation E n Γ ρ e c) :
    ApproxTKWEta E n Γ (covWIrrelEnvErase ρ) e c := by
  obtain ⟨d, rfl, hd⟩ := h
  exact covWIrrel_guarded_forget hd

theorem covWIrrelRaw_observation_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : CovWIrrelRawObservation E n EnvWIrrel.bot e c) :
    CovWEtaRawAction E n Γ c e A := by
  obtain ⟨d, rfl, hd⟩ := ho
  exact covWIrrelRaw_closed hW ht hd

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_ALIGNED_ROOTS
#print axioms ApproxTWIrrel
#print axioms ApproxTKWIrrel
#print axioms covWIrrel_raw_forget
#print axioms covWIrrel_guarded_forget
#print axioms covWIrrelRaw_closed
#print axioms covWIrrel_raw_appSpine_bot
#print axioms covWIrrel_guarded_appSpine_bot
#print axioms ApproxTKWIrrelStage
#print axioms ApproxTKWIrrelStage.mono
#print axioms CovWIrrelRealized
#print axioms covWIrrel_realized_nil
#print axioms CovWIrrelObservation
#print axioms CovWIrrelRawObservation
#print axioms covWIrrel_observation_of
#print axioms covWIrrel_observation_forget
#print axioms covWIrrelRaw_observation_closed
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_ALIGNED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
