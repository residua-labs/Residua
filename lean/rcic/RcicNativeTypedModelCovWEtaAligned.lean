import rcic.RcicNativeTypedModelCovWRealized

/-!
# Native typed eta saturation of guarded observations

The strict raw relation `ApproxTW` is unchanged.  The new guarded relation
copies its landed per-call K grammar and adds an extensional graph rule.
That rule carries an actual native Pi typing of its subject, an observation
of that same native domain, and strict `CTyS` typing of every row demand.
Its premises are finite derivations of applications to the fresh variable.
It neither infers a native lambda head nor introduces an unguarded Prop
recursor rule.  Positive old derivations embed by induction; no converse
forgetful map is asserted.  Stage bounds measure compact information, not
derivation length.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2ConvAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelKAudit TypedModelCovVAudit TypedModelKIndexFreeAudit
open TypedModelCovWAudit TypedModelCovTAudit

inductive ApproxTKWEta (E : ResolvedEnv) (n : Nat) : LCtx → EnvT → Expr Nat → CptT → Prop
  | bot (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) : ApproxTKWEta E n Γ ρ e .bot
  | free {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
      (hfree : KFreeT E e) (h : ApproxTW E ρ e c) : ApproxTKWEta E n Γ ρ e c
  | pi {Γ : LCtx} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
      {f : List (List CptT × CptT)}
      (hA : ApproxTKWEta E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hb : ∀ s ∈ f, ApproxTKWEta E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTKWEta E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvT} {A b : Expr Nat} {a : CptT}
      {g : List (List CptT × CptT)}
      (hA : ApproxTKWEta E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWEta E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTKWEta E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat}
      {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTKWEta E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKWEta E n Γ ρ a u) :
      ApproxTKWEta E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTKWEta E n Γ ρ f (.spine r args))
      (ha : ApproxTKWEta E n Γ ρ a u) :
      ApproxTKWEta E n Γ ρ (.app f a) (.spine r (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptT} (hd : DeltaConst E r m b)
      (h : ApproxTKWEta E n [] EnvT.bot (instantiateLevels ls b) c) :
      ApproxTKWEta E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTKWEta E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKWEta E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTKWEta E n Γ ρ (natExpand t) c) :
      ApproxTKWEta E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitnessS E)
      (hsource : ApproxTN E ρ (iotaLhsOfS w) c)
      (hrhs : ApproxTKWEta E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTKWEta E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexGuardAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hsource : ApproxTN E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c)
      (hrhs : ApproxTKWEta E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWEta E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

  | eta {Γ : LCtx} {ρ : EnvT} {e D B : Expr Nat} {a : CptT}
      {g : List (List CptT × CptT)}
      (he : HasTyT E n Γ e (.pi D B))
      (hD : ApproxTKWEta E n Γ ρ D a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWEta E n (.assumption D :: Γ)
        (EnvT.cons (demandT s.1) ρ) (.app (lift 0 1 e) (.bvar 0)) s.2) :
      ApproxTKWEta E n Γ ρ e (.lam g)

/-- Every landed guarded observation has a derivation in the extension. -/
theorem covWEta_of_old {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTKW E n Γ ρ e c) :
    ApproxTKWEta E n Γ ρ e c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf h
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | delta hd _ ih => exact .delta hd ih
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih
  | iota w hs _ ih => exact .iota w hs ih
  | recursorPropK w x hk hn hi hc hs _ ih =>
      exact .recursorPropK w x hk hn hi hc hs ih

def ApproxTKWEtaStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (e : Expr Nat) (c : CptT) : Prop :=
  ApproxTKWEta E arity Γ ρ e c ∧ covTObservationBudget c ≤ stage

/-- This is only monotonicity of the finite observation budget. -/
theorem ApproxTKWEtaStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKWEtaStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKWEtaStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

theorem covWEta_stage_of_old {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKWStage E arity stage Γ ρ e c) :
    ApproxTKWEtaStage E arity stage Γ ρ e c := ⟨covWEta_of_old h.1, h.2⟩

structure CovWEtaRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ i c, ρ i c → ApproxTKWEtaStage E arity stage [] EnvT.bot (σ i) c

theorem covWEta_realized_of_old {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (h : CovWRealized E arity stage Γ ρ σ) :
    CovWEtaRealized E arity stage Γ ρ σ :=
  ⟨h.typing, fun i c hc => covWEta_stage_of_old (h.observed i c hc)⟩

theorem covWEta_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovWEtaRealized E arity stage [] EnvT.bot SubstT.id :=
  covWEta_realized_of_old (covW_realized_nil E arity stage)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_ALIGNED_ROOTS
#print axioms ApproxTKWEta
#print axioms covWEta_of_old
#print axioms ApproxTKWEtaStage
#print axioms ApproxTKWEtaStage.mono
#print axioms covWEta_stage_of_old
#print axioms CovWEtaRealized
#print axioms covWEta_realized_of_old
#print axioms covWEta_realized_nil
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_ALIGNED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
