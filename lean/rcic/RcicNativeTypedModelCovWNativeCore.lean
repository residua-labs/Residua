import rcic.RcicNativeTypedModelCovWNativeFields

/-!
# Native computation and occurrence-disciplined guarded observations

The guarded grammar uses the landed native K gates and ordinary structured
constructor iota without the former ApproxTN source filter. Raw ApproxTWIrrel
is unchanged. There is no `.free` rule: every structured observation must
recursively pass this grammar's own field rules. Non-Proposition recursor
schemas are interpreted recursively in the closed schema context; this is a
local observation constructor, not a general native typing supplier.
`closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2ConvAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelKAudit TypedModelCovVAudit TypedModelKIndexFreeAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovWEtaAudit
open TypedModelCovWIrrelAudit

inductive ApproxTKWNative (E : ResolvedEnv) (n : Nat) : LCtx → EnvWIrrel → Expr Nat → CptWIrrel → Prop
  | bot (Γ : LCtx) (ρ : EnvWIrrel) (e : Expr Nat) : ApproxTKWNative E n Γ ρ e .bot
  | bvar {Γ : LCtx} {ρ : EnvWIrrel} {i : Nat} {c : CptWIrrel}
      (h : ρ i c) : ApproxTKWNative E n Γ ρ (.bvar i) c
  | sort (Γ : LCtx) (ρ : EnvWIrrel) (l : Level) :
      ApproxTKWNative E n Γ ρ (.sort l) (sortCodeWIrrel l)
  | const (Γ : LCtx) (ρ : EnvWIrrel) (r : Nat) (ls : List Level)
      (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxTKWNative E n Γ ρ (.const r ls) (.spine r ls [])
  | recursor {Γ : LCtx} {ρ : EnvWIrrel} {w : IotaWitnessS E}
      (ls : List Level) (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptWIrrel)} {us_fields : List (List CptWIrrel)} {c : CptWIrrel}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTKWNative E n []
        (EnvWIrrel.pushArgs ((us_pre ++ us_fields).map demandWIrrel) EnvWIrrel.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTKWNative E n Γ ρ (.const w.recRef ls)
        (curryStepWIrrel (us_pre ++ [ctorDemandWIrrel w.ctorRef w.lsC w.nparams us_fields]) c)
  | pi {Γ : LCtx} {ρ : EnvWIrrel} {A B : Expr Nat} {a : CptWIrrel}
      {f : List (List CptWIrrel × CptWIrrel)}
      (hA : ApproxTKWNative E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hb : ∀ s ∈ f, ApproxTKWNative E n (.assumption A :: Γ)
        (EnvWIrrel.cons (demandWIrrel s.1) ρ) B s.2) :
      ApproxTKWNative E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvWIrrel} {A b : Expr Nat} {a : CptWIrrel}
      {g : List (List CptWIrrel × CptWIrrel)}
      (hA : ApproxTKWNative E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWNative E n (.assumption A :: Γ)
        (EnvWIrrel.cons (demandWIrrel s.1) ρ) b s.2) :
      ApproxTKWNative E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvWIrrel} {f a : Expr Nat}
      {g : List (List CptWIrrel × CptWIrrel)} {s : List CptWIrrel × CptWIrrel}
      (hf : ApproxTKWNative E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKWNative E n Γ ρ a u) :
      ApproxTKWNative E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvWIrrel} {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWIrrel} {u : CptWIrrel}
      (hf : ApproxTKWNative E n Γ ρ f (.spine r ls args))
      (ha : ApproxTKWNative E n Γ ρ a u)
      (hslot : CovWIrrelProofPosition E n r ls args.length → u = .bot)
      (hfield : CovWNativeField E n Γ f a u) :
      ApproxTKWNative E n Γ ρ (.app f a) (.spine r ls (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvWIrrel} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptWIrrel} (hd : DeltaConst E r m b)
      (h : ApproxTKWNative E n [] EnvWIrrel.bot (instantiateLevels ls b) c) :
      ApproxTKWNative E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvWIrrel} {A v b : Expr Nat} {c : CptWIrrel}
      (h : ApproxTKWNative E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKWNative E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvWIrrel} {t : Nat} {c : CptWIrrel}
      (h : ApproxTKWNative E n Γ ρ (natExpand t) c) :
      ApproxTKWNative E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvWIrrel} {c : CptWIrrel} (w : IotaWitnessS E)
      (hrhs : ApproxTKWNative E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTKWNative E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvWIrrel} {c : CptWIrrel} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexConvAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hrhs : ApproxTKWNative E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWNative E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

  | eta {Γ : LCtx} {ρ : EnvWIrrel} {e D B : Expr Nat} {a : CptWIrrel}
      {g : List (List CptWIrrel × CptWIrrel)}
      (he : HasTyT E n Γ e (.pi D B))
      (hD : ApproxTKWNative E n Γ ρ D a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E (covWIrrelErase u) (covWIrrelErase a))
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWNative E n (.assumption D :: Γ)
        (EnvWIrrel.cons (demandWIrrel s.1) ρ) (.app (lift 0 1 e) (.bvar 0)) s.2) :
      ApproxTKWNative E n Γ ρ e (.lam g)



/-- Structured iota backward observation closure uses the actual witness. -/
theorem covWNative_iota_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {c : CptWIrrel} (w : IotaWitnessS E)
    (h : ApproxTKWNative E n Γ ρ (iotaRhsOfS w) c) :
    ApproxTKWNative E n Γ ρ (iotaLhsOfS w) c := .iota w h

/-- Native K backward observation closure consumes precisely the landed gates. -/
theorem covWNative_K_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {c : CptWIrrel} (w : IotaWitness E) (x : Expr Nat)
    (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
    (hindex : KIndexConvAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
    (h : ApproxTKWNative E n Γ ρ (iotaRhsOf w) c) :
    ApproxTKWNative E n Γ ρ
      (recCall (.const w.recRef w.ls) w.preMajor x) c :=
  .recursorPropK w x hcanon hnc hindex hcommon h

/-- Bottom fields require the actual application typing, even though no
argument observation is inspected. -/
theorem covWNative_guarded_appSpine_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {f a D B : Expr Nat} {r : Nat} {ls : List Level}
    {args : List CptWIrrel}
    (hF : HasTyT E n Γ f (.pi D B)) (ha : HasTyT E n Γ a D)
    (hf : ApproxTKWNative E n Γ ρ f (.spine r ls args)) :
    ApproxTKWNative E n Γ ρ (.app f a) (.spine r ls (args ++ [.bot])) :=
  .appSpine hf (.bot _ _ _) (fun _ => rfl) (covWNative_field_bot hF ha)

/-- The native head relation itself supplies the exact K premises. -/
theorem covWNative_KNativeHead_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e e' : Expr Nat} {c : CptWIrrel}
    (hs : KNativeHead E n Γ e e')
    (ho : ApproxTKWNative E n Γ ρ e' c) : ApproxTKWNative E n Γ ρ e c := by
  cases hs with
  | intro hk hn hi hc => exact .recursorPropK _ _ hk hn hi hc ho

def ApproxTKWNativeStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (e : Expr Nat) (c : CptWIrrel) : Prop :=
  ApproxTKWNative E arity Γ ρ e c ∧ covTObservationBudget (covWIrrelErase c) ≤ stage

theorem ApproxTKWNativeStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWNativeStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKWNativeStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

structure CovWNativeRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ i c, ρ i c → ApproxTKWNativeStage E arity stage [] EnvWIrrel.bot (σ i) c

theorem covWNative_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovWNativeRealized E arity stage [] EnvWIrrel.bot SubstT.id := by
  refine ⟨(covW_realized_nil E arity stage).typing, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

/-- Universe labels are provenance, not additional observable distinctions.
The externally tested compact is the original finite compact after erasure. -/
def CovWNativeObservation (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (e : Expr Nat) (c : CptT) : Prop :=
  ∃ d : CptWIrrel, covWIrrelErase d = c ∧ ApproxTKWNative E n Γ ρ e d

theorem covWNative_observation_of {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWNative E n Γ ρ e c) :
    CovWNativeObservation E n Γ ρ e (covWIrrelErase c) := ⟨c, rfl, h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_CORE_ROOTS
#print axioms ApproxTKWNative
#print axioms covWNative_iota_expand
#print axioms covWNative_K_expand
#print axioms covWNative_guarded_appSpine_bot
#print axioms covWNative_KNativeHead_expand
#print axioms ApproxTKWNativeStage
#print axioms ApproxTKWNativeStage.mono
#print axioms CovWNativeRealized
#print axioms covWNative_realized_nil
#print axioms CovWNativeObservation
#print axioms covWNative_observation_of
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
