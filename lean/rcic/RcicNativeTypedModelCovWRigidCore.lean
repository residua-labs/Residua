import rcic.RcicNativeTypedModelCovWConvSeal

/-!
# Legacy-rigid recursor spines and local-definition head observations

Every recursive premise uses this new grammar. Legacy computation and the
certified derived K rule are unchanged. A recursor with no legacy witness
has a spine observation. A local let entry is observed only through its
lookup value: its valuation is not consulted and outer eta cannot bypass
resolution. Native lookup already carries the required lift.

This is an observation grammar, not an assertion of global ConvT invariance
or code completeness. The no-legacy condition alone is not a native
nonconversion proof. closure_claim = 0.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovWIrrelAudit
open TypedModelCovWNativeAudit TypedModelCovWConvAudit

/-- Actual recursor admission and absence of every legacy witness at its head. -/
def CovWRigidRecursor (E : ResolvedEnv) (r : Nat) : Prop :=
  ∃ m, E.members r = some m ∧ m.mclass = .recursorM ∧
    ∀ w : IotaWitness E, w.recRef ≠ r

/-- Eta works after resolving a context-defined variable at the head. -/
def CovWRigidHeadReady (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∀ i, e = .bvar i → lookupValue Γ i = none

theorem covWRigid_headReady_app (Γ : LCtx) (f a : Expr Nat) :
    CovWRigidHeadReady Γ (.app f a) := by
  intro i h
  cases h

theorem covWRigid_headReady_const (Γ : LCtx) (r : Nat) (ls : List Level) :
    CovWRigidHeadReady Γ (.const r ls) := by
  intro i h
  cases h

theorem covWRigid_no_legacy {E : ResolvedEnv} {r : Nat}
    (h : CovWRigidRecursor E r) (w : IotaWitness E) : w.recRef ≠ r := by
  obtain ⟨m, hm, hk, hn⟩ := h
  exact hn w

inductive ApproxTKWRigid (E : ResolvedEnv) (n : Nat) : LCtx → EnvWConvR → Expr Nat → CptWConvR → Prop
  | bot (Γ : LCtx) (ρ : EnvWConvR) (e : Expr Nat) : ApproxTKWRigid E n Γ ρ e .bot
  | bvar {Γ : LCtx} {ρ : EnvWConvR} {i : Nat} {c : CptWConvR}
      (hlocal : lookupValue Γ i = none)
      (h : ρ i c) : ApproxTKWRigid E n Γ ρ (.bvar i) c
  | zetaLocal {Γ : LCtx} {ρ : EnvWConvR} {i : Nat} {v : Expr Nat} {c : CptWConvR}
      (hv : lookupValue Γ i = some v)
      (h : ApproxTKWRigid E n Γ ρ v c) : ApproxTKWRigid E n Γ ρ (.bvar i) c
  | sort (Γ : LCtx) (ρ : EnvWConvR) (l : Level) :
      ApproxTKWRigid E n Γ ρ (.sort l) (sortCodeWConvR l)
  | const (Γ : LCtx) (ρ : EnvWConvR) (r : Nat) (ls : List Level)
      (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxTKWRigid E n Γ ρ (.const r ls) (.spine r ls [])
  | rigidRecursor (Γ : LCtx) (ρ : EnvWConvR) (r : Nat) (ls : List Level)
      (h : CovWRigidRecursor E r) :
      ApproxTKWRigid E n Γ ρ (.const r ls) (.spine r ls [])
  | recursor {Γ : LCtx} {ρ : EnvWConvR} {w : IotaWitnessS E}
      (ls : List Level) (hi : DerivedIota E (iotaLhsOfS w) (iotaRhsOfS w))
      (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptWConvR)} {us_fields : List (List CptWConvR)} {c : CptWConvR}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTKWRigid E n []
        (EnvWConvR.pushArgs ((us_pre ++ us_fields).map demandWConvR) EnvWConvR.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTKWRigid E n Γ ρ (.const w.recRef ls)
        (curryStepWConvR (us_pre ++ [ctorDemandWConvR w.ctorRef w.lsC w.nparams us_fields]) c)
  | pi {Γ : LCtx} {ρ : EnvWConvR} {A B : Expr Nat} {a : CptWConvR}
      {f : List (List CptWConvR × CptWConvR)}
      (hA : ApproxTKWRigid E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyWConvR E u a)
      (hb : ∀ s ∈ f, ApproxTKWRigid E n (.assumption A :: Γ)
        (EnvWConvR.cons (demandWConvR s.1) ρ) B s.2) :
      ApproxTKWRigid E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvWConvR} {A b : Expr Nat} {a : CptWConvR}
      {g : List (List CptWConvR × CptWConvR)}
      (hA : ApproxTKWRigid E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyWConvR E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWRigid E n (.assumption A :: Γ)
        (EnvWConvR.cons (demandWConvR s.1) ρ) b s.2) :
      ApproxTKWRigid E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvWConvR} {f a : Expr Nat}
      {g : List (List CptWConvR × CptWConvR)} {s : List CptWConvR × CptWConvR}
      (hf : ApproxTKWRigid E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKWRigid E n Γ ρ a u) :
      ApproxTKWRigid E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvWConvR} {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWConvR} {u : CptWConvR}
      (hf : ApproxTKWRigid E n Γ ρ f (.spine r ls args))
      (ha : ApproxTKWRigid E n Γ ρ a u)
      (hslot : CovWIrrelProofPosition E n r ls args.length → u = .bot)
      (hfield : CovWNativeField E n Γ f a (covWConvRawErase u)) :
      ApproxTKWRigid E n Γ ρ (.app f a) (.spine r ls (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvWConvR} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptWConvR} (hd : DeltaConst E r m b)
      (h : ApproxTKWRigid E n [] EnvWConvR.bot (instantiateLevels ls b) c) :
      ApproxTKWRigid E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvWConvR} {A v b : Expr Nat} {c : CptWConvR}
      (h : ApproxTKWRigid E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKWRigid E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvWConvR} {t : Nat} {c : CptWConvR}
      (h : ApproxTKWRigid E n Γ ρ (natExpand t) c) :
      ApproxTKWRigid E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvWConvR} {c : CptWConvR} (w : IotaWitness E)
      {T : Expr Nat} (hl : HasTyT E n Γ (iotaLhsOf w) T)
      (hr : HasTyT E n Γ (iotaRhsOf w) T)
      (hrhs : ApproxTKWRigid E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWRigid E n Γ ρ (iotaLhsOf w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvWConvR} {c : CptWConvR} (w : IotaWitness E) (x : Expr Nat)
       {T : Expr Nat} (hK : CovWConvKData E n Γ w x T)
      (hrhs : ApproxTKWRigid E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWRigid E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

  | eta {Γ : LCtx} {ρ : EnvWConvR} {e D B : Expr Nat} {a : CptWConvR}
      {g : List (List CptWConvR × CptWConvR)}
      (hhead : CovWRigidHeadReady Γ e)
      (he : HasTyT E n Γ e (.pi D B))
      (hD : ApproxTKWRigid E n Γ ρ D a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyWConvR E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWRigid E n (.assumption D :: Γ)
        (EnvWConvR.cons (demandWConvR s.1) ρ) (.app (lift 0 1 e) (.bvar 0)) s.2) :
      ApproxTKWRigid E n Γ ρ e (.lam g)




/-- Public observations keep the landed level quotient and finite code syntax. -/
def CovWRigidObservation (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (e : Expr Nat) (c : CptWConv) : Prop :=
  ∃ d, covWConvCode d = c ∧ ApproxTKWRigid E n Γ ρ e d

theorem covWRigid_observation_of {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWRigid E n Γ ρ e c) :
    CovWRigidObservation E n Γ ρ e (covWConvCode c) := ⟨c, rfl, h⟩

def CovWRigidTypedInvariant (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (A l r : Expr Nat) : Prop :=
  ∀ a, CovWRigidObservation E n Γ ρ A a → ∀ c, CTySConv E c a →
    (CovWRigidObservation E n Γ ρ l c ↔ CovWRigidObservation E n Γ ρ r c)

def ApproxTKWRigidStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (e : Expr Nat) (c : CptWConvR) : Prop :=
  ApproxTKWRigid E arity Γ ρ e c ∧ covTObservationBudget (covWConvCoarse c) ≤ stage

theorem ApproxTKWRigidStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWRigidStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKWRigidStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

/-- The full closed completeness target, recorded without assuming a supplier. -/
def CovWRigidCodesDetermineTypes : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (A B : Expr Nat) (u : Level),
    EnvWfT E → HasTyT E n [] A (.sort u) → HasTyT E n [] B (.sort u) →
    (∀ c, CovWRigidObservation E n [] EnvWConvR.bot A c ↔
      CovWRigidObservation E n [] EnvWConvR.bot B c) →
    Nonempty (ConvT E n [] A B (.sort u))

/-- A single named completeness obligation on legacy Prop recursors with
non-constructor majors. No exhaustion theorem for the global remainder is
assumed by defining this class. -/
def CovWRigidLegacyNeutralCompleteness : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (w₁ w₂ : IotaWitness E)
    (x₁ x₂ : Expr Nat) (u : Level),
    EnvWfT E →
    HasTyT E n [] (majorFamily w₁) (.sort .zero) →
    HasTyT E n [] (majorFamily w₂) (.sort .zero) →
    (¬ IsCtorSpine E x₁) → (¬ IsCtorSpine E x₂) →
    HasTyT E n [] (recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁) (.sort u) →
    HasTyT E n [] (recCall (.const w₂.recRef w₂.ls) w₂.preMajor x₂) (.sort u) →
    (∀ c, CovWRigidObservation E n [] EnvWConvR.bot
        (recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁) c ↔
      CovWRigidObservation E n [] EnvWConvR.bot
        (recCall (.const w₂.recRef w₂.ls) w₂.preMajor x₂) c) →
    Nonempty (ConvT E n []
      (recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁)
      (recCall (.const w₂.recRef w₂.ls) w₂.preMajor x₂) (.sort u))

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidRecursor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidHeadReady
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_headReady_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_headReady_const
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_no_legacy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidObservation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_observation_of
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidTypedInvariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigidStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigidStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidCodesDetermineTypes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidLegacyNeutralCompleteness
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS
