import rcic.RcicNativeTypedModelCovWConvCompact

/-! The new guarded grammar admits iota only through the legacy witness
of ConvT.iota, with actual endpoint typings. K carries the typed certificate
whose soundness is proved separately. Structured-only recursor schemas are
also excluded. Public observations preserve universe classes. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovWIrrelAudit
open TypedModelCovWNativeAudit

inductive ApproxTKWConv (E : ResolvedEnv) (n : Nat) : LCtx → EnvWConvR → Expr Nat → CptWConvR → Prop
  | bot (Γ : LCtx) (ρ : EnvWConvR) (e : Expr Nat) : ApproxTKWConv E n Γ ρ e .bot
  | bvar {Γ : LCtx} {ρ : EnvWConvR} {i : Nat} {c : CptWConvR}
      (h : ρ i c) : ApproxTKWConv E n Γ ρ (.bvar i) c
  | sort (Γ : LCtx) (ρ : EnvWConvR) (l : Level) :
      ApproxTKWConv E n Γ ρ (.sort l) (sortCodeWConvR l)
  | const (Γ : LCtx) (ρ : EnvWConvR) (r : Nat) (ls : List Level)
      (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxTKWConv E n Γ ρ (.const r ls) (.spine r ls [])
  | recursor {Γ : LCtx} {ρ : EnvWConvR} {w : IotaWitnessS E}
      (ls : List Level) (hi : DerivedIota E (iotaLhsOfS w) (iotaRhsOfS w))
      (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptWConvR)} {us_fields : List (List CptWConvR)} {c : CptWConvR}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTKWConv E n []
        (EnvWConvR.pushArgs ((us_pre ++ us_fields).map demandWConvR) EnvWConvR.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTKWConv E n Γ ρ (.const w.recRef ls)
        (curryStepWConvR (us_pre ++ [ctorDemandWConvR w.ctorRef w.lsC w.nparams us_fields]) c)
  | pi {Γ : LCtx} {ρ : EnvWConvR} {A B : Expr Nat} {a : CptWConvR}
      {f : List (List CptWConvR × CptWConvR)}
      (hA : ApproxTKWConv E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyWConvR E u a)
      (hb : ∀ s ∈ f, ApproxTKWConv E n (.assumption A :: Γ)
        (EnvWConvR.cons (demandWConvR s.1) ρ) B s.2) :
      ApproxTKWConv E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvWConvR} {A b : Expr Nat} {a : CptWConvR}
      {g : List (List CptWConvR × CptWConvR)}
      (hA : ApproxTKWConv E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyWConvR E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWConv E n (.assumption A :: Γ)
        (EnvWConvR.cons (demandWConvR s.1) ρ) b s.2) :
      ApproxTKWConv E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvWConvR} {f a : Expr Nat}
      {g : List (List CptWConvR × CptWConvR)} {s : List CptWConvR × CptWConvR}
      (hf : ApproxTKWConv E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKWConv E n Γ ρ a u) :
      ApproxTKWConv E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvWConvR} {f a : Expr Nat} {r : Nat} {ls : List Level} {args : List CptWConvR} {u : CptWConvR}
      (hf : ApproxTKWConv E n Γ ρ f (.spine r ls args))
      (ha : ApproxTKWConv E n Γ ρ a u)
      (hslot : CovWIrrelProofPosition E n r ls args.length → u = .bot)
      (hfield : CovWNativeField E n Γ f a (covWConvRawErase u)) :
      ApproxTKWConv E n Γ ρ (.app f a) (.spine r ls (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvWConvR} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptWConvR} (hd : DeltaConst E r m b)
      (h : ApproxTKWConv E n [] EnvWConvR.bot (instantiateLevels ls b) c) :
      ApproxTKWConv E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvWConvR} {A v b : Expr Nat} {c : CptWConvR}
      (h : ApproxTKWConv E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKWConv E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvWConvR} {t : Nat} {c : CptWConvR}
      (h : ApproxTKWConv E n Γ ρ (natExpand t) c) :
      ApproxTKWConv E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvWConvR} {c : CptWConvR} (w : IotaWitness E)
      {T : Expr Nat} (hl : HasTyT E n Γ (iotaLhsOf w) T)
      (hr : HasTyT E n Γ (iotaRhsOf w) T)
      (hrhs : ApproxTKWConv E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWConv E n Γ ρ (iotaLhsOf w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvWConvR} {c : CptWConvR} (w : IotaWitness E) (x : Expr Nat)
       {T : Expr Nat} (hK : CovWConvKData E n Γ w x T)
      (hrhs : ApproxTKWConv E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKWConv E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

  | eta {Γ : LCtx} {ρ : EnvWConvR} {e D B : Expr Nat} {a : CptWConvR}
      {g : List (List CptWConvR × CptWConvR)}
      (he : HasTyT E n Γ e (.pi D B))
      (hD : ApproxTKWConv E n Γ ρ D a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyWConvR E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKWConv E n (.assumption D :: Γ)
        (EnvWConvR.cons (demandWConvR s.1) ρ) (.app (lift 0 1 e) (.bvar 0)) s.2) :
      ApproxTKWConv E n Γ ρ e (.lam g)




/-- Exactly the legacy iota premise; no structured-only rule is hidden here. -/
theorem covWConv_iota_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {lhs rhs T : Expr Nat} {c : CptWConvR}
    (hi : DerivedIota E lhs rhs) (hl : HasTyT E n Γ lhs T)
    (hr : HasTyT E n Γ rhs T) (ho : ApproxTKWConv E n Γ ρ rhs c) :
    ApproxTKWConv E n Γ ρ lhs c := by
  cases hi with
  | of w => exact .iota w hl hr ho

theorem covWConv_K_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {w : IotaWitness E} {x T : Expr Nat} {c : CptWConvR}
    (hk : CovWConvKData E n Γ w x T)
    (ho : ApproxTKWConv E n Γ ρ (iotaRhsOf w) c) :
    ApproxTKWConv E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c :=
  .recursorPropK w x hk ho

/-- The externally visible compact retains eqN classes, not coarse erasure. -/
def CovWConvObservation (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (e : Expr Nat) (c : CptWConv) : Prop :=
  ∃ d : CptWConvR, covWConvCode d = c ∧ ApproxTKWConv E n Γ ρ e d

theorem covWConv_observation_of {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConv E n Γ ρ e c) : CovWConvObservation E n Γ ρ e (covWConvCode c) :=
  ⟨c, rfl, h⟩

def ApproxTKWConvStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (e : Expr Nat) (c : CptWConvR) : Prop :=
  ApproxTKWConv E arity Γ ρ e c ∧ covTObservationBudget (covWConvCoarse c) ≤ stage

theorem ApproxTKWConvStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConvStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKWConvStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

def CovWConvTypedInvariant (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (A l r : Expr Nat) : Prop :=
  ∀ a, CovWConvObservation E n Γ ρ A a → ∀ c, CTySConv E c a →
    (CovWConvObservation E n Γ ρ l c ↔ CovWConvObservation E n Γ ρ r c)

/-- One precise completeness obligation, not an assumed supplier. -/
def CovWConvCodesDetermineTypes : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (A B : Expr Nat) (u : Level),
    EnvWfT E → HasTyT E n [] A (.sort u) → HasTyT E n [] B (.sort u) →
    (∀ c, CovWConvObservation E n [] EnvWConvR.bot A c ↔
      CovWConvObservation E n [] EnvWConvR.bot B c) →
    Nonempty (ConvT E n [] A B (.sort u))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_CORE_ROOTS
#print axioms ApproxTKWConv
#print axioms covWConv_iota_expand
#print axioms covWConv_K_expand
#print axioms CovWConvObservation
#print axioms covWConv_observation_of
#print axioms ApproxTKWConvStage
#print axioms ApproxTKWConvStage.mono
#print axioms CovWConvTypedInvariant
#print axioms CovWConvCodesDetermineTypes
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
