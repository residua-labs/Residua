import rcic.RcicNativeTypedModelK

/-!
# Native-K-aligned finite observations

The old relations remain unchanged. `ApproxTN` preserves the old finite
observation grammar and adds precisely the native recursor-eligibility premise
to non-strict Prop elimination. `ApproxTKN` keeps every guarded computation
certificate and requires the aligned source at both computation rules.
The new grammar is inductive and Prop-valued. No derivation is eliminated into
a Type-valued callback. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2ConvAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelKAudit

/-- Environment-wide sufficient condition for retaining every old observation.
This uses native predicates, including their actual legacy witnesses. -/
def CovVPropHeadsNative (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E, PropFamilyS w →
    KFreeRec E w.recRef ∨ KProjRec E w.recRef

/-- The old model with native eligibility on its only non-strict recursor rule. -/
inductive ApproxTN (E : ResolvedEnv) : EnvT → Expr Nat → CptT → Prop
  | bot (ρ : EnvT) (e : Expr Nat) : ApproxTN E ρ e .bot
  | bvar {ρ : EnvT} {i : Nat} {c : CptT} (h : ρ i c) : ApproxTN E ρ (.bvar i) c
  | sort (ρ : EnvT) (l : Level) : ApproxTN E ρ (.sort l) (sortCode l)
  | pi {ρ : EnvT} {A B : Expr Nat} {a : CptT} {f : List (List CptT × CptT)}
      (hA : ApproxTN E ρ A a)
      (hT : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hf : ∀ s ∈ f, ApproxTN E (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTN E ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvT} {A b : Expr Nat} {a : CptT} {g : List (List CptT × CptT)}
      (hA : ApproxTN E ρ A a)
      (hT : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hnt : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTN E (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTN E ρ (.lam A b) (.lam g)
  | app {ρ : EnvT} {f a : Expr Nat} {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTN E ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxTN E ρ a u) :
      ApproxTN E ρ (.app f a) s.2
  | const (ρ : EnvT) (r : Nat) (ls : List Level) (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxTN E ρ (.const r ls) (.spine r [])
  | delta {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat} {c : CptT}
      (hdelta : DeltaConst E r m b)
      (h : ApproxTN E EnvT.bot (instantiateLevels ls b) c) :
      ApproxTN E ρ (.const r ls) c
  | recursor {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level) (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptT)} {us_fields : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTN E (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTN E ρ (.const w.recRef ls)
        (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)
  | recursorProp {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level) (hP : PropFamilyS w)
      (hnative : KFreeRec E w.recRef ∨ KProjRec E w.recRef)
      {us_pre : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (h : ApproxTN E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTN E ρ (.const w.recRef ls) (curryStepT (us_pre ++ [[]]) c)
  | appSpine {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTN E ρ f (.spine r args)) (ha : ApproxTN E ρ a u) :
      ApproxTN E ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTN E ρ (.app (.lam A b) v) c) :
      ApproxTN E ρ (.letE A v b) c
  | lit {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTN E ρ (natExpand t) c) :
      ApproxTN E ρ (.lit t) c

/-- The aligned source together with the existing native guarded rules. -/
inductive ApproxTKN (E : ResolvedEnv) (n : Nat) : LCtx → EnvT → Expr Nat → CptT → Prop
  | bot (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) : ApproxTKN E n Γ ρ e .bot
  | free {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
      (hfree : KFreeT E e) (h : ApproxTN E ρ e c) : ApproxTKN E n Γ ρ e c
  | pi {Γ : LCtx} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
      {f : List (List CptT × CptT)}
      (hA : ApproxTKN E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hb : ∀ s ∈ f, ApproxTKN E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTKN E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvT} {A b : Expr Nat} {a : CptT}
      {g : List (List CptT × CptT)}
      (hA : ApproxTKN E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKN E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTKN E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat}
      {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTKN E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKN E n Γ ρ a u) :
      ApproxTKN E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTKN E n Γ ρ f (.spine r args))
      (ha : ApproxTKN E n Γ ρ a u) :
      ApproxTKN E n Γ ρ (.app f a) (.spine r (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptT} (hd : DeltaConst E r m b)
      (h : ApproxTKN E n [] EnvT.bot (instantiateLevels ls b) c) :
      ApproxTKN E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTKN E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKN E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTKN E n Γ ρ (natExpand t) c) :
      ApproxTKN E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitnessS E)
      (hsource : ApproxTN E ρ (iotaLhsOfS w) c)
      (hrhs : ApproxTKN E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTKN E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexGuardAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hsource : ApproxTN E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c)
      (hrhs : ApproxTKN E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKN E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- The restriction only removes observations. -/
theorem approxTN_forget {e : Expr Nat} {c : CptT}
    (h : ApproxTN E ρ e c) : ApproxT E ρ e c := by
  induction h with
  | bot => exact .bot _ _
  | bvar h => exact .bvar h
  | sort => exact .sort _ _
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | const _ _ _ hr hp => exact .const _ _ _ hr hp
  | delta hd _ ih => exact .delta hd ih
  | recursor ls hp hpre hfld _ ih => exact .recursor ls hp hpre hfld ih
  | recursorProp ls hp _ hpre _ ih => exact .recursorProp ls hp hpre ih
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih

/-- Native eligibility supplies an aligned derivation, by finite derivation induction. -/
theorem covV_approxT_of_native_heads (hE : CovVPropHeadsNative E)
    {e : Expr Nat} {c : CptT} (h : ApproxT E ρ e c) : ApproxTN E ρ e c := by
  induction h with
  | bot => exact .bot _ _
  | bvar h => exact .bvar h
  | sort => exact .sort _ _
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | const _ _ _ hr hp => exact .const _ _ _ hr hp
  | delta hd _ ih => exact .delta hd ih
  | recursor ls hp hpre hfld _ ih => exact .recursor ls hp hpre hfld ih
  | recursorProp ls hp hpre _ ih => exact .recursorProp ls hp (hE _ hp) hpre ih
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih

/-- Guarded observations also refine the landed relation. -/
theorem approxTKN_forget {e : Expr Nat} {c : CptT}
    (h : ApproxTKN E n Γ ρ e c) : ApproxTK E n Γ ρ e c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf (approxTN_forget h)
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | delta hd _ ih => exact .delta hd ih
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih
  | iota w hs _ ih => exact .iota w (approxTN_forget hs) ih
  | recursorPropK w x hk hn hi hc hs _ ih =>
      exact .recursorPropK w x hk hn hi hc (approxTN_forget hs) ih

/-- In particular no unaligned old source can leak through a guarded rule. -/
theorem approxTKN_forgetN {e : Expr Nat} {c : CptT}
    (h : ApproxTKN E n Γ ρ e c) : ApproxTN E ρ e c := by
  induction h with
  | bot => exact .bot _ _
  | free _ h => exact h
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | delta hd _ ih => exact .delta hd ih
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih
  | iota _ hs _ _ => exact hs
  | recursorPropK _ _ _ _ _ _ hs _ _ => exact hs

/-- The guarded grammar is unchanged in environments where every Prop recursor
has native eligibility. This theorem constructs the new derivation. -/
theorem covV_approxTK_of_native_heads (hE : CovVPropHeadsNative E)
    {e : Expr Nat} {c : CptT} (h : ApproxTK E n Γ ρ e c) :
    ApproxTKN E n Γ ρ e c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf (covV_approxT_of_native_heads hE h)
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | delta hd _ ih => exact .delta hd ih
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih
  | iota w hs _ ih => exact .iota w (covV_approxT_of_native_heads hE hs) ih
  | recursorPropK w x hk hn hi hc hs _ ih =>
      exact .recursorPropK w x hk hn hi hc (covV_approxT_of_native_heads hE hs) ih

/-- The finite aligned model has the same certified K-free introduction. -/
theorem approxTKN_iff_approxTN_of_kFree {e : Expr Nat}
    (he : KFreeT E e) (c : CptT) :
    ApproxTKN E n Γ ρ e c ↔ ApproxTN E ρ e c :=
  ⟨approxTKN_forgetN, ApproxTKN.free he⟩

/-- The existing guard is retained literally and supplies the same native head. -/
theorem covV_k_head {w : IotaWitness E} {x : Expr Nat}
    (hk : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
    (hi : KIndexGuardAt E n Γ w) (hc : KCommonAt E n Γ w x) :
    KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  approxTK_k_head hk hnc hi hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_ALIGNED_ROOTS
#print axioms CovVPropHeadsNative
#print axioms ApproxTN
#print axioms ApproxTKN
#print axioms approxTN_forget
#print axioms covV_approxT_of_native_heads
#print axioms approxTKN_forget
#print axioms approxTKN_forgetN
#print axioms covV_approxTK_of_native_heads
#print axioms approxTKN_iff_approxTN_of_kFree
#print axioms covV_k_head
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_ALIGNED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
