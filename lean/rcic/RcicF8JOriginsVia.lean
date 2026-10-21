import rcic.RcicF8CtxWfVia
import rcic.RcicF8JOrigins

/-!
J4 Via companion, approved #7139/#6493: decorate ACTUAL J3.dispatchVia outputs
with the existing direct-origin certificate. No new dispatcher or carrier.
The dependent ofWf equality is cast along J3.dispatchVia_ofWf's full output
identity, never merely equal expression endpoints. Coverage remains J3.supported.
The X-facing supplier contract is PARTIAL and conjoined with JContractViaP.
No source CtxWfT is inferred from Via; no generated-origin or WK-2 claim.
closure_claim=0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JOrigins
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- The old J4 proof constructors, applied to the real Via worker's answer. -/
def dispatch_originsVia (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfVia E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (match J3.dispatchVia hW R hΓ h hs with
      | none => PUnit
      | some out => ValleyOrigins hW h out.valley)
  | _, _, _, _, _, .refl _ _ _ ha, hs => refl_origins hW ha hs
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hs => irr_origins hW hP hp hq hs
  | Γ, _, _, _, hΓ, .symm _ a b T h, hs => by
      have ih := dispatch_originsVia hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      simp only [J3.dispatchVia]
      cases he : J3.dispatchVia hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) with
      | none => exact PUnit.unit
      | some out =>
          simp only [he] at ih
          exact swap_origins out ih
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hs => by
      have ih := dispatch_originsVia hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
      simp only [J3.dispatchVia]
      cases he : J3.dispatchVia hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs) with
      | none => exact PUnit.unit
      | some out =>
          simp only [he] at ih
          exact reindex_origins out u hT hs ih
  | _, _, _, _, _, .trans .., _ => PUnit.unit
  | _, _, _, _, _, .beta .., _ => PUnit.unit
  | _, _, _, _, _, .zeta .., _ => PUnit.unit
  | _, _, _, _, _, .zetaLocal .., _ => PUnit.unit
  | _, _, _, _, _, .delta .., _ => PUnit.unit
  | _, _, _, _, _, .iota .., _ => PUnit.unit
  | _, _, _, _, _, .lit .., _ => PUnit.unit
  | _, _, _, _, _, .app .., _ => PUnit.unit
  | _, _, _, _, _, .lam .., _ => PUnit.unit
  | _, _, _, _, _, .pi .., _ => PUnit.unit
  | _, _, _, _, _, .letE .., _ => PUnit.unit
  | _, _, _, _, _, .sorts .., _ => PUnit.unit
  | _, _, _, _, _, .consts .., _ => PUnit.unit
  | _, _, _, _, _, .eta .., _ => PUnit.unit


/-- ALL leaves and BOTH actual stars, on a successful original Via call only. -/
theorem dispatchedVia_contract (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (v : CtxWfVia E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (out : J3.Result hW R h)
    (heq : J3.dispatchVia hW R v h hs = some out) :
    (∀ l ∈ out.valley.leaves, SubOf l (.cv h)) ∧
    Nonempty (ValleyOrigins hW h out.valley) := by
  refine ⟨out.strict, ?_⟩
  have m := dispatch_originsVia hW R v h hs
  rw [heq] at m
  exact ⟨m⟩

/-- The supported DIRECT fragment has at most one translated original irr address.
This is not a claim about trans or a D-generated pair. -/
def source_unique : {Γ : LCtx} → {a b T : Expr Nat} →
    (h : ConvT E n Γ a b T) → J3.supported h = true →
    (o₁ o₂ : IrrOcc h) → o₁ = o₂
  | _, _, _, _, .refl .., _, o, _ => nomatch o
  | _, _, _, _, .irr .., _, o₁, o₂ => by cases o₁; cases o₂; rfl
  | _, _, _, _, .symm _ _ _ _ h, hh, o₁, o₂ => by
      cases o₁ with
      | symm x =>
        cases o₂ with
        | symm y => exact congrArg IrrOcc.symm (source_unique h hh x y)
  | _, _, _, _, .tyConv _ _ _ _ _ _ h ht, hh, o₁, o₂ => by
      cases o₁ with
      | tyConv _ x =>
        cases o₂ with
        | tyConv _ y => exact congrArg (IrrOcc.tyConv ht) (source_unique h hh x y)
  | _, _, _, _, .trans .., hh, _, _ => nomatch hh
  | _, _, _, _, .beta .., hh, _, _ => nomatch hh
  | _, _, _, _, .zeta .., hh, _, _ => nomatch hh
  | _, _, _, _, .zetaLocal .., hh, _, _ => nomatch hh
  | _, _, _, _, .delta .., hh, _, _ => nomatch hh
  | _, _, _, _, .iota .., hh, _, _ => nomatch hh
  | _, _, _, _, .lit .., hh, _, _ => nomatch hh
  | _, _, _, _, .app .., hh, _, _ => nomatch hh
  | _, _, _, _, .lam .., hh, _, _ => nomatch hh
  | _, _, _, _, .pi .., hh, _, _ => nomatch hh
  | _, _, _, _, .letE .., hh, _, _ => nomatch hh
  | _, _, _, _, .sorts .., hh, _, _ => nomatch hh
  | _, _, _, _, .consts .., hh, _, _ => nomatch hh
  | _, _, _, _, .eta .., hh, _, _ => nomatch hh

/-- Uniqueness of actual address data, not just existence of an arbitrary answer. -/
theorem atSource_subsingleton {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (hu : Subsingleton (IrrOcc h)) (s : ProofSite E n) :
    Subsingleton (AtSource h s) := by
  constructor
  rintro ⟨o, ho⟩ ⟨o', ho'⟩
  have he := hu.elim o o'
  cases he
  cases ho
  cases ho'
  rfl

def starOrigins_subsingleton {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (hu : Subsingleton (IrrOcc h)) :
    {Δ : LCtx} → {x y U : Expr Nat} →
    (s : ParRedTStar (PEqLeafT E n) E n Δ x y U) →
    Subsingleton (StarOrigins h s)
  | _, _, _, _, .refl .. => by
      change Subsingleton (PUnit : Type)
      exact ⟨fun x y => by cases x; cases y; rfl⟩
  | _, _, _, _, .tail t ss => by
      letI : ∀ o : Occ t, Subsingleton (AtSource h (site t o)) :=
        fun o => atSource_subsingleton h hu (site t o)
      letI : Subsingleton (StepOrigins h t) := inferInstance
      letI : Subsingleton (StarOrigins h ss) := starOrigins_subsingleton h hu ss
      change Subsingleton (StepOrigins h t × StarOrigins h ss)
      infer_instance

theorem valleyOrigins_subsingleton (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (hu : Subsingleton (IrrOcc h)) (out : Valley R Γ a b T) :
    Subsingleton (ValleyOrigins hW h out) := by
  letI := starOrigins_subsingleton h hu
    (out.left.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
  letI := starOrigins_subsingleton h hu
    (out.right.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
  change Subsingleton (_ × _)
  infer_instance

/-- The exact dependent result fiber of the landed and Via proof fronts. -/
abbrev answerOrigins (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) : Option (J3.Result hW R h) → Type
  | none => PUnit
  | some out => ValleyOrigins hW h out.valley

/-- Normalize the generated matcher fiber, keeping the actual Via certificate. -/
def viaAnswer (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    answerOrigins hW h (J3.dispatchVia hW R v h hs) := by
  have m := dispatch_originsVia hW R v h hs
  cases he : J3.dispatchVia hW R v h hs with
  | none => exact PUnit.unit
  | some out => rw [he] at m; exact m

/-- Normalize the LANDED proof front's fiber, without rebuilding its origins. -/
def wfAnswer (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    answerOrigins hW h (J3.dispatchWf hW R hΓ h hs) := by
  have m := dispatch_origins hW R hΓ h hs
  cases he : J3.dispatchWf hW R hΓ h hs with
  | none => exact PUnit.unit
  | some out => rw [he] at m; exact m

theorem answerOrigins_subsingleton (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Subsingleton (answerOrigins hW h (J3.dispatchWf hW R hΓ h hs)) := by
  cases he : J3.dispatchWf hW R hΓ h hs with
  | none =>
      change Subsingleton (PUnit : Type)
      exact ⟨fun x y => by cases x; cases y; rfl⟩
  | some out =>
      have hc : J3.supported h = true := by
        have hk := J3.dispatchWf_coverage hW hΓ h hs
        rw [he] at hk
        exact hk.symm
      exact valleyOrigins_subsingleton hW h ⟨source_unique h hc⟩ out.valley

/-- Exact certificate agreement after transport along the ACTUAL result equation. -/
theorem dispatch_originsVia_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    cast (congrArg (answerOrigins hW h) (J3.dispatchVia_ofWf hW R hΓ h hs))
      (viaAnswer hW R (.ofWf hΓ) h hs) =
      wfAnswer hW R hΓ h hs :=
  (answerOrigins_subsingleton hW R hΓ h hs).elim _ _

/-- Attach only evidence; this helper makes no acceptance decision. -/
def attachAnswer (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) : (out : Option (J3.Result hW R h)) →
    answerOrigins hW h out →
    Option (Σ' r : J3.Result hW R h, ValleyOrigins hW h r.valley)
  | none, _ => none
  | some r, m => some ⟨r,m⟩

theorem attachAnswer_forget (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (out : Option (J3.Result hW R h))
    (m : answerOrigins hW h out) : (attachAnswer hW h out m).map (·.1) = out := by
  cases out <;> rfl

theorem attachAnswer_transport (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) {x y : Option (J3.Result hW R h)}
    (he : x = y) (m : answerOrigins hW h x) :
    attachAnswer hW h y (cast (congrArg (answerOrigins hW h) he) m) =
      attachAnswer hW h x m := by cases he; rfl

/-- Certificate decorator of the existing Via dispatcher, not a second worker. -/
def withOriginsVia (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :=
  attachAnswer hW h (J3.dispatchVia hW R v h hs) (viaAnswer hW R v h hs)

/-- Only an additive decorator of the landed Wf result. -/
def withOriginsWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :=
  attachAnswer hW h (J3.dispatchWf hW R hΓ h hs) (wfAnswer hW R hΓ h hs)

theorem withOriginsVia_forget (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (withOriginsVia hW R v h hs).map (·.1) = J3.dispatchVia hW R v h hs :=
  attachAnswer_forget hW h _ _

theorem withOriginsVia_coverage (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (withOriginsVia hW R v h hs).isSome = J3.supported h := by
  have hk := J3.dispatchVia_coverage hW R v h hs
  rw [← withOriginsVia_forget hW R v h hs] at hk
  cases he : withOriginsVia hW R v h hs with
  | none => simpa only [he, Option.map, Option.isSome] using hk
  | some o => simpa only [he, Option.map, Option.isSome] using hk

theorem withOriginsVia_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    withOriginsVia hW R (.ofWf hΓ) h hs = withOriginsWf hW R hΓ h hs := by
  unfold withOriginsVia withOriginsWf
  rw [← attachAnswer_transport hW h (J3.dispatchVia_ofWf hW R hΓ h hs)
    (viaAnswer hW R (.ofWf hΓ) h hs)]
  rw [dispatch_originsVia_ofWf]

/-- PARTIAL supplier companion; only actual successful answers carry direct origins. -/
def JOriginContractViaP (hW : EnvWfT E)
    (J : ∀ R : List (Jd E n), JProcViaP R) : Prop :=
  ∀ R {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r)
    (V : Valley R Γ a b T), J R v h hs = some V →
    Nonempty (ValleyOrigins hW h V)

def JContractViaPWithOrigins (hW : EnvWfT E)
    (J : ∀ R : List (Jd E n), JProcViaP R) : Prop :=
  JContractViaP J ∧ JOriginContractViaP hW J

theorem j3Via_origins (hW : EnvWfT E) : JOriginContractViaP (n := n) hW (j3Via hW) := by
  intro R Γ a b T v h hs V hV
  unfold j3Via at hV
  cases hd : J3.dispatchVia hW R v h hs with
  | none => simp only [hd, Option.map] at hV; exact Option.noConfusion hV
  | some out =>
      simp only [hd, Option.map, Option.some.injEq] at hV
      subst V
      exact (dispatchedVia_contract hW v h hs out hd).2

theorem j3Via_bothContracts (hW : EnvWfT E) :
    JContractViaPWithOrigins (n := n) hW (j3Via hW) :=
  ⟨j3Via_contract hW, j3Via_origins hW⟩

/-- Direct fragment no-source consequence on the ACTUAL Via answer. -/
theorem dispatchedVia_no_source (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (v : CtxWfVia E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (out : J3.Result hW R h)
    (he : J3.dispatchVia hW R v h hs = some out) (hn : ∀ _o : IrrOcc h, False) :
    NoProofOccurrences (out.valley.left.val (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW)) ∧
    NoProofOccurrences (out.valley.right.val (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW)) := by
  obtain ⟨m⟩ := (dispatchedVia_contract hW v h hs out he).2
  exact ⟨StarOrigins.no_source hn _ m.1, StarOrigins.no_source hn _ m.2⟩

end Rcic.Declarative.F8Measure.JOrigins
