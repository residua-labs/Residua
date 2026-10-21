import rcic.RcicNativeTypedModelCovVAligned
import rcic.RcicNativeTypedModelCovVNativeHeads

/-!
# Per-call proposition recursion

`ApproxTW` has no non-strict proposition-recursion rule. `ApproxTKW.free`
uses that raw relation. Non-strict proposition elimination is introduced only
at its actual saturated call, with the unchanged native canon, non-constructor,
index and common-typing certificates. Computation-source premises remain old
aligned observations: they are checks, while every RHS has a new derivation.
No old statement is edited. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2ConvAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelKAudit TypedModelCovVAudit TypedModelKIndexFreeAudit

inductive ApproxTW (E : ResolvedEnv) : EnvT → Expr Nat → CptT → Prop
  | bot (ρ : EnvT) (e : Expr Nat) : ApproxTW E ρ e .bot
  | bvar {ρ : EnvT} {i : Nat} {c : CptT} (h : ρ i c) : ApproxTW E ρ (.bvar i) c
  | sort (ρ : EnvT) (l : Level) : ApproxTW E ρ (.sort l) (sortCode l)
  | pi {ρ : EnvT} {A B : Expr Nat} {a : CptT} {f : List (List CptT × CptT)}
      (hA : ApproxTW E ρ A a)
      (hT : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hf : ∀ s ∈ f, ApproxTW E (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTW E ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvT} {A b : Expr Nat} {a : CptT} {g : List (List CptT × CptT)}
      (hA : ApproxTW E ρ A a)
      (hT : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hnt : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTW E (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTW E ρ (.lam A b) (.lam g)
  | app {ρ : EnvT} {f a : Expr Nat} {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTW E ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxTW E ρ a u) :
      ApproxTW E ρ (.app f a) s.2
  | const (ρ : EnvT) (r : Nat) (ls : List Level) (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxTW E ρ (.const r ls) (.spine r [])
  | delta {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat} {c : CptT}
      (hdelta : DeltaConst E r m b)
      (h : ApproxTW E EnvT.bot (instantiateLevels ls b) c) :
      ApproxTW E ρ (.const r ls) c
  | recursor {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level) (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptT)} {us_fields : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTW E (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTW E ρ (.const w.recRef ls)
        (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)
  | appSpine {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTW E ρ f (.spine r args)) (ha : ApproxTW E ρ a u) :
      ApproxTW E ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTW E ρ (.app (.lam A b) v) c) :
      ApproxTW E ρ (.letE A v b) c
  | lit {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTW E ρ (natExpand t) c) :
      ApproxTW E ρ (.lit t) c

inductive ApproxTKW (E : ResolvedEnv) (n : Nat) : LCtx → EnvT → Expr Nat → CptT → Prop
  | bot (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) : ApproxTKW E n Γ ρ e .bot
  | free {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
      (hfree : KFreeT E e) (h : ApproxTW E ρ e c) : ApproxTKW E n Γ ρ e c
  | pi {Γ : LCtx} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
      {f : List (List CptT × CptT)}
      (hA : ApproxTKW E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hb : ∀ s ∈ f, ApproxTKW E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTKW E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvT} {A b : Expr Nat} {a : CptT}
      {g : List (List CptT × CptT)}
      (hA : ApproxTKW E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKW E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTKW E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat}
      {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTKW E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKW E n Γ ρ a u) :
      ApproxTKW E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTKW E n Γ ρ f (.spine r args))
      (ha : ApproxTKW E n Γ ρ a u) :
      ApproxTKW E n Γ ρ (.app f a) (.spine r (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptT} (hd : DeltaConst E r m b)
      (h : ApproxTKW E n [] EnvT.bot (instantiateLevels ls b) c) :
      ApproxTKW E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTKW E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKW E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTKW E n Γ ρ (natExpand t) c) :
      ApproxTKW E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitnessS E)
      (hsource : ApproxTN E ρ (iotaLhsOfS w) c)
      (hrhs : ApproxTKW E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTKW E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexGuardAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hsource : ApproxTN E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c)
      (hrhs : ApproxTKW E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKW E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c


variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- A strict raw observation supplies an old aligned observation. -/
theorem approxTW_forget {e : Expr Nat} {c : CptT}
    (h : ApproxTW E ρ e c) : ApproxTN E ρ e c := by
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
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih

/-- Every new guarded derivation supplies its old aligned counterpart. -/
theorem approxTKW_forget {e : Expr Nat} {c : CptT}
    (h : ApproxTKW E n Γ ρ e c) : ApproxTKN E n Γ ρ e c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf (approxTW_forget h)
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

/-- This sufficient environment property is instantiated for each transferred
control. It is not claimed for all admitted environments. -/
def CovWPropRecIndexed (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E, PropFamilyS w → w.nindices ≠ 0

/-- On the old K-free fragment, indexed proposition recursion was already
excluded, including from hidden bodies, schemas and literal expansions. -/
theorem covW_raw_of_indexed_prop (hE : CovWPropRecIndexed E)
    {e : Expr Nat} {c : CptT} (h : ApproxTN E ρ e c)
    (he : KFreeT E e) : ApproxTW E ρ e c := by
  revert he
  induction h with
  | bot => intro _; exact .bot _ _
  | bvar h => intro _; exact .bvar h
  | sort => intro _; exact .sort _ _
  | pi _ ht _ ihA ihb =>
      intro he
      obtain ⟨ha, hb⟩ := (kFreeT_pi_iff _ _).mp he
      exact .pi (ihA ha) ht (fun s hs => ihb s hs hb)
  | lam _ ht hne _ ihA ihb =>
      intro he
      obtain ⟨ha, hb⟩ := (kFreeT_lam_iff _ _).mp he
      exact .lam (ihA ha) ht hne (fun s hs => ihb s hs hb)
  | app _ hs _ ihf iha =>
      intro he
      obtain ⟨hf, ha⟩ := (kFreeT_app_iff _ _).mp he
      exact .app (ihf hf) hs (fun u hu => iha u hu ha)
  | const _ _ _ hr hp => intro _; exact .const _ _ _ hr hp
  | delta hd _ ih => intro he; exact .delta hd (ih (kFreeT_delta he hd))
  | @recursor ρ w ls hp us_pre us_fields c hpre hfld h ih =>
      intro he
      exact .recursor ls hp hpre hfld (ih (kFreeT_schema w he))
  | @recursorProp ρ w ls hp hn us_pre c hpre h ih =>
      intro he
      exact (kFreeT_const_not_indexed he ⟨w, rfl, hp, hE w hp⟩).elim
  | appSpine _ _ ihf iha =>
      intro he
      obtain ⟨hf, ha⟩ := (kFreeT_app_iff _ _).mp he
      exact .appSpine (ihf hf) (iha ha)
  | letE _ ih => intro he; exact .letE (ih ((kFreeT_letE_iff _ _ _).mp he))
  | @lit ρ t c h ih =>
      intro he
      exact .lit (ih (kFreeT_support he (fun r hr => by
        simpa only [occursConst, litOccurs_natExpand] using hr)))

/-- An actual old observation is reconstructed; this is used only after
supplying the concrete environment property. -/
theorem covW_guarded_of_indexed_prop (hE : CovWPropRecIndexed E)
    {e : Expr Nat} {c : CptT} (h : ApproxTKN E n Γ ρ e c) :
    ApproxTKW E n Γ ρ e c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf (covW_raw_of_indexed_prop hE h hf)
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

/-- The unchanged per-call premises supply an actual native K step. -/
theorem covW_k_head {w : IotaWitness E} {x : Expr Nat}
    (hk : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
    (hi : KIndexGuardAt E n Γ w) (hc : KCommonAt E n Γ w x) :
    KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  covV_k_head hk hnc hi hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ALIGNED_ROOTS
#print axioms ApproxTW
#print axioms ApproxTKW
#print axioms approxTW_forget
#print axioms approxTKW_forget
#print axioms CovWPropRecIndexed
#print axioms covW_raw_of_indexed_prop
#print axioms covW_guarded_of_indexed_prop
#print axioms covW_k_head
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ALIGNED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
