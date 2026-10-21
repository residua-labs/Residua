import rcic.RcicNativeTypedModelKFragment
import rcic.RcicNativeTypedModelKGuard

/-!
# A saturated K refinement candidate for the typed compact model

`ApproxTK` reuses an entire `ApproxT` derivation on the transitive K-free
fragment.  Outside it, demand composition is explicit and proposition
recursion is introduced at the actual saturated call.  In particular an
indexed proposition recursor constant is not assigned the old blind curried
function compact.  This is necessary: retaining that compact and ordinary
application would immediately recover the apart-index observation.

The K guard imports native conversion from CK2 and separately carries the
stronger, independently testable DI agreement certificate.  The additional
old-model source observation in the computation rules makes the new relation
a refinement without assuming a false global raw iota-soundness premise.
It is not a Fundamental or readback-adequacy assumption.

Binders extend the native context, and a transparent global body is checked
at the empty native context.  Thus the old context-free model interface is
not silently asserted for this family.  Its app inversion in particular has
new saturated computation alternatives, measured in the controls module.

Every recursive premise below is strictly positive; the native and DI guards
are earlier definitions and contain no occurrence of `ApproxTK`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKGuardAudit

/-- The old model is imported at a certified fragment; the new computation
rules are attached to saturated syntax rather than an uninstantiated constant. -/
inductive ApproxTK (E : ResolvedEnv) (n : Nat) : LCtx → EnvT → Expr Nat → CptT → Prop
  | bot (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) : ApproxTK E n Γ ρ e .bot
  | free {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
      (hfree : KFreeT E e) (h : ApproxT E ρ e c) : ApproxTK E n Γ ρ e c
  | pi {Γ : LCtx} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
      {f : List (List CptT × CptT)}
      (hA : ApproxTK E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hb : ∀ s ∈ f, ApproxTK E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTK E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvT} {A b : Expr Nat} {a : CptT}
      {g : List (List CptT × CptT)}
      (hA : ApproxTK E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTK E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTK E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat}
      {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTK E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTK E n Γ ρ a u) :
      ApproxTK E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTK E n Γ ρ f (.spine r args))
      (ha : ApproxTK E n Γ ρ a u) :
      ApproxTK E n Γ ρ (.app f a) (.spine r (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptT} (hd : DeltaConst E r m b)
      (h : ApproxTK E n [] EnvT.bot (instantiateLevels ls b) c) :
      ApproxTK E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTK E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTK E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTK E n Γ ρ (natExpand t) c) :
      ApproxTK E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitnessS E)
      (hsource : ApproxT E ρ (iotaLhsOfS w) c)
      (hrhs : ApproxTK E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTK E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexGuardAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hsource : ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c)
      (hrhs : ApproxTK E n Γ ρ (iotaRhsOf w) c) :
      ApproxTK E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- Forget the new certificate layer; every recursive use is an actual child. -/
theorem approxTK_forget {e : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ e c) : ApproxT E ρ e c := by
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
  | iota _ hsource _ _ => exact hsource
  | recursorPropK _ _ _ _ _ _ hsource _ _ => exact hsource

theorem approxTK_iff_approxT_of_kFree {e : Expr Nat} (he : KFreeT E e) (c : CptT) :
    ApproxTK E n Γ ρ e c ↔ ApproxT E ρ e c :=
  ⟨approxTK_forget, ApproxTK.free he⟩

/-- Freezing the native context exposes exactly the landed model carrier. -/
def ctxModelT_approxTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : CtxModelT E :=
  ⟨ApproxTK E n Γ⟩

theorem modelAgreementAtT_kFree {e : Expr Nat} (he : KFreeT E e) :
    ModelAgreementAtT (ctxModelT_approxTK E n Γ) (ctxModelT_approxT E) e :=
  fun _ c => approxTK_iff_approxT_of_kFree he c

/-- A native K head is supplied by precisely the imported guard conjuncts. -/
theorem approxTK_k_head {w : IotaWitness E} {x : Expr Nat}
    (hk : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
    (hi : KIndexGuardAt E n Γ w) (hc : KCommonAt E n Γ w x) :
    KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  .intro hk hnc hi.1 hc

theorem approxTK_bvar_inv {i : Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ (.bvar i) c) : c = .bot ∨ ρ i c :=
  approxT_bvar_inv (approxTK_forget h)

theorem approxTK_bvar_iff (i : Nat) (c : CptT) :
    ApproxTK E n Γ ρ (.bvar i) c ↔ c = .bot ∨ ρ i c :=
  (approxTK_iff_approxT_of_kFree (kFreeT_bvar E i) c).trans
    (approxT_bvar_iff E ρ i c)

theorem approxTK_sort_inv {l : Level} {c : CptT}
    (h : ApproxTK E n Γ ρ (.sort l) c) : c = .bot ∨ c = sortCode l :=
  approxT_sort_inv (approxTK_forget h)

theorem approxTK_sort_code (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT) (l : Level) :
    ApproxTK E n Γ ρ (.sort l) (sortCode l) :=
  .free (kFreeT_sort E l) (approxT_sort_code E ρ l)

theorem approxTK_pi_bot_nil (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (A B : Expr Nat) : ApproxTK E n Γ ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot _ _ _) (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

/-- The binder context change is part of the statement, not an implicit cast. -/
theorem approxTK_pi_inv {A B : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ (.pi A B) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ ApproxTK E n Γ ρ A a ∧
      ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧
        ApproxTK E n (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) B s.2 := by
  generalize he : Expr.pi A B = e at h
  cases h with
  | bot => exact Or.inl rfl
  | free hf ht =>
      rw [← he] at hf ht
      obtain ⟨hA, hB⟩ := (kFreeT_pi_iff A B).mp hf
      rcases approxT_pi_inv ht with h | ⟨a, f, he, ha, hb⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, f, he, .free hA ha,
          fun s hs => ⟨(hb s hs).1, .free hB (hb s hs).2⟩⟩
  | pi ha ht hb =>
      cases he
      exact Or.inr ⟨_, _, rfl, ha, fun s hs => ⟨ht s hs, hb s hs⟩⟩
  | lam _ _ _ _ => cases he
  | app _ _ _ => cases he
  | appSpine _ _ => cases he
  | delta _ _ => cases he
  | letE _ => cases he
  | lit _ => cases he
  | iota w _ _ => simp only [iotaLhsOfS, recCall_eq_app] at he; cases he
  | recursorPropK w x _ _ _ _ _ _ => simp only [recCall_eq_app] at he; cases he

theorem approxTK_lam_inv {A b : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ (.lam A b) c) :
    c = .bot ∨ ∃ a g, c = .lam g ∧ ApproxTK E n Γ ρ A a ∧
      (∃ s ∈ g, s.2 ≠ .bot) ∧
      ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧
        ApproxTK E n (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) b s.2 := by
  generalize he : Expr.lam A b = e at h
  cases h with
  | bot => exact Or.inl rfl
  | free hf ht =>
      rw [← he] at hf ht
      obtain ⟨hA, hb⟩ := (kFreeT_lam_iff A b).mp hf
      rcases approxT_lam_inv ht with h | ⟨a, g, he, ha, hne, hg⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, g, he, .free hA ha, hne,
          fun s hs => ⟨(hg s hs).1, .free hb (hg s hs).2⟩⟩
  | pi _ _ _ => cases he
  | lam ha ht hne hb =>
      cases he
      exact Or.inr ⟨_, _, rfl, ha, hne, fun s hs => ⟨ht s hs, hb s hs⟩⟩
  | app _ _ _ => cases he
  | appSpine _ _ => cases he
  | delta _ _ => cases he
  | letE _ => cases he
  | lit _ => cases he
  | iota w _ _ => simp only [iotaLhsOfS, recCall_eq_app] at he; cases he
  | recursorPropK w x _ _ _ _ _ _ => simp only [recCall_eq_app] at he; cases he

theorem approxTK_letE_inv {A v b : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ (.letE A v b) c) :
    ApproxTK E n Γ ρ (.app (.lam A b) v) c := by
  generalize he : Expr.letE A v b = e at h
  cases h with
  | bot => exact .bot _ _ _
  | free hf ht =>
      rw [← he] at hf ht
      apply ApproxTK.free ((kFreeT_letE_iff A v b).mp hf)
      cases ht with
      | bot => exact .bot _ _
      | letE ht => exact ht
  | pi _ _ _ => cases he
  | lam _ _ _ _ => cases he
  | app _ _ _ => cases he
  | appSpine _ _ => cases he
  | delta _ _ => cases he
  | letE h => cases he; exact h
  | lit _ => cases he
  | iota w _ _ => simp only [iotaLhsOfS, recCall_eq_app] at he; cases he
  | recursorPropK w x _ _ _ _ _ _ => simp only [recCall_eq_app] at he; cases he

/-- The new alternatives in application inversion expose an actual saturated
computation and its demanded RHS observation. -/
def SaturatedComputationTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (e : Expr Nat) (c : CptT) : Prop :=
  (∃ w : IotaWitnessS E, e = iotaLhsOfS w ∧
    ApproxT E ρ (iotaLhsOfS w) c ∧ ApproxTK E n Γ ρ (iotaRhsOfS w) c) ∨
  (∃ (w : IotaWitness E) (x : Expr Nat),
    e = recCall (.const w.recRef w.ls) w.preMajor x ∧ KCanonW w x ∧
    (¬ IsCtorSpine E x) ∧ KIndexGuardAt E n Γ w ∧ KCommonAt E n Γ w x ∧
    ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c ∧
    ApproxTK E n Γ ρ (iotaRhsOf w) c)

theorem approxTK_of_saturated {e : Expr Nat} {c : CptT}
    (h : SaturatedComputationTK E n Γ ρ e c) : ApproxTK E n Γ ρ e c := by
  rcases h with ⟨w, rfl, hs, hr⟩ | ⟨w, x, rfl, hk, hn, hi, hc, hs, hr⟩
  · exact .iota w hs hr
  · exact .recursorPropK w x hk hn hi hc hs hr

/-- Exact application inversion for this model; it has a saturated computation
alternative, which the landed `CtxModelTLaws.app_inv` does not have. -/
theorem approxTK_app_inv {f a : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ (.app f a) c) :
    c = .bot ∨
    (∃ g s, c = s.2 ∧ ApproxTK E n Γ ρ f (.lam g) ∧ s ∈ g ∧
      ∀ u ∈ s.1, ApproxTK E n Γ ρ a u) ∨
    (∃ r args u, c = .spine r (args ++ [u]) ∧
      ApproxTK E n Γ ρ f (.spine r args) ∧ ApproxTK E n Γ ρ a u) ∨
    SaturatedComputationTK E n Γ ρ (.app f a) c := by
  generalize he : Expr.app f a = e at h
  cases h with
  | bot => exact Or.inl rfl
  | free hf ht =>
      rw [← he] at hf ht
      obtain ⟨hff, hfa⟩ := (kFreeT_app_iff f a).mp hf
      rcases approxT_app_inv ht with hb | hg | hsp
      · exact Or.inl hb
      · obtain ⟨g, s, hc, hg, hs, ha⟩ := hg
        exact Or.inr (Or.inl ⟨g, s, hc, .free hff hg, hs, fun u hu => .free hfa (ha u hu)⟩)
      · obtain ⟨r, args, u, hc, hf, ha⟩ := hsp
        exact Or.inr (Or.inr (Or.inl ⟨r, args, u, hc, .free hff hf, .free hfa ha⟩))
  | pi _ _ _ => cases he
  | lam _ _ _ _ => cases he
  | app hf hs ha =>
      cases he
      exact Or.inr (Or.inl ⟨_, _, rfl, hf, hs, ha⟩)
  | appSpine hf ha =>
      cases he
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, hf, ha⟩))
  | delta _ _ => cases he
  | letE _ => cases he
  | lit _ => cases he
  | iota w hs hr => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, rfl, hs, hr⟩)))
  | recursorPropK w x hk hn hi hc hs hr =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨w, x, rfl, hk, hn, hi, hc, hs, hr⟩)))

/-- Type interpretation reuses the landed compact typing relation. -/
def ElTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, ApproxTK E n Γ ρ A a ∧ CTyS E u a

theorem elTK_bot (A : Expr Nat) : ElTK E n Γ ρ A .bot :=
  ⟨.bot, .bot _ _ _, ctyS_bot _⟩

theorem elTK_forget {A : Expr Nat} {u : CptT} (h : ElTK E n Γ ρ A u) : ElT E ρ A u := by
  obtain ⟨a, ha, ht⟩ := h
  exact ⟨a, approxTK_forget ha, ht⟩

theorem elTK_iff_elT_of_kFree {A : Expr Nat} (hA : KFreeT E A) (u : CptT) :
    ElTK E n Γ ρ A u ↔ ElT E ρ A u := by
  constructor
  · exact elTK_forget
  · rintro ⟨a, ha, ht⟩
    exact ⟨a, .free hA ha, ht⟩

theorem approxTK_mono_env {ρ' : EnvT} (hle : EnvT.le ρ ρ') {e : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ e c) : ApproxTK E n Γ ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _ _
  | free hf h => exact .free hf (approxT_mono_env hle h)
  | pi _ ht _ ihA ihb =>
      refine .pi (ihA hle) ht (fun s hs => ihb s hs ?_)
      intro i c hc
      cases i with
      | zero => exact hc
      | succ i => exact hle i c hc
  | lam _ ht hne _ ihA ihb =>
      refine .lam (ihA hle) ht hne (fun s hs => ihb s hs ?_)
      intro i c hc
      cases i with
      | zero => exact hc
      | succ i => exact hle i c hc
  | app _ hs _ ihf iha => exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | delta hd h _ => exact .delta hd h
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)
  | iota w hs _ ih => exact .iota w (approxT_mono_env hle hs) (ih hle)
  | recursorPropK w x hk hn hi hc hs _ ih =>
      exact .recursorPropK w x hk hn hi hc (approxT_mono_env hle hs) (ih hle)

/-- On the Nat environment the whole new carrier is exactly the landed one. -/
theorem approxTK_nat_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) (c : CptT) :
    ApproxTK natEnvU n Γ ρ e c ↔ ApproxT natEnvU ρ e c :=
  approxTK_iff_approxT_of_kFree (kFreeT_natEnvU e) c

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_ROOTS
#print axioms ApproxTK
#print axioms ApproxTK.bot
#print axioms ApproxTK.free
#print axioms ApproxTK.pi
#print axioms ApproxTK.lam
#print axioms ApproxTK.app
#print axioms ApproxTK.appSpine
#print axioms ApproxTK.delta
#print axioms ApproxTK.letE
#print axioms ApproxTK.lit
#print axioms ApproxTK.iota
#print axioms ApproxTK.recursorPropK
#print axioms approxTK_forget
#print axioms approxTK_iff_approxT_of_kFree
#print axioms ctxModelT_approxTK
#print axioms modelAgreementAtT_kFree
#print axioms approxTK_k_head
#print axioms approxTK_bvar_inv
#print axioms approxTK_bvar_iff
#print axioms approxTK_sort_inv
#print axioms approxTK_sort_code
#print axioms approxTK_pi_bot_nil
#print axioms approxTK_pi_inv
#print axioms approxTK_lam_inv
#print axioms approxTK_letE_inv
#print axioms SaturatedComputationTK
#print axioms approxTK_of_saturated
#print axioms approxTK_app_inv
#print axioms ElTK
#print axioms elTK_bot
#print axioms elTK_forget
#print axioms elTK_iff_elT_of_kFree
#print axioms approxTK_mono_env
#print axioms approxTK_nat_iff
-- END RCIC_NATIVE_TYPED_MODEL_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKAudit
