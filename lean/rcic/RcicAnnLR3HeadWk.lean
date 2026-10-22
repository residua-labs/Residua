import rcic.RcicAnnLR3NormalWk
import rcic.RcicAnnTyRedWk
import rcic.RcicAnnKTransport

/-!
# Exact forward LR3 head transport along context worlds

Old primitive typing, positive leaf/normal/apart certificates and the K
frame are all transported by existing insertion algebra.  For an entire
world, the K case uses a supplied old-stage `MapLaws` for `wkMapA` and
applies `Frame.transport` once.  Consequently it requires only the original
well-formed context, not an extra well-formedness premise for every
intermediate insertion.

The resulting contracts supply forward exact steps for legal insertions
and `WkSpecA` worlds.  No step-reflection contract is postulated here.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

private theorem iota_world {I : IotaIfaceA} (hI : IotaLiftA I) :
    (ρ : WkSpecA) → (e : ExprA) →
    I.fn (wkExprA ρ e) = (I.fn e).map (wkExprA ρ)
  | [], e => by
      change I.fn e = (I.fn e).map id
      cases I.fn e <;> rfl
  | (d, c) :: ρ, e => by
      change I.fn (wkExprA ρ (liftA c 1 e)) = (I.fn e).map (wkExprA ((d, c) :: ρ))
      rw [iota_world hI ρ (liftA c 1 e), hI c e]
      cases I.fn e <;> rfl

private theorem oldHead_world {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (ρ : WkSpecA) → (Γ : LCtxA) → WkSpecA.ok ρ Γ → (e : ExprA) →
    hStepFnA E I.fn (wkCtxA ρ Γ) (wkExprA ρ e) =
      (hStepFnA E I.fn Γ e).map (wkExprA ρ)
  | [], Γ, _, e => by
      change hStepFnA E I.fn Γ e = (hStepFnA E I.fn Γ e).map id
      cases hStepFnA E I.fn Γ e <;> rfl
  | (d, c) :: ρ, Γ, hρ, e => by
      change hStepFnA E I.fn (wkCtxA ρ (insertAtA d c Γ)) (wkExprA ρ (liftA c 1 e)) =
        (hStepFnA E I.fn Γ e).map (wkExprA ((d, c) :: ρ))
      rw [oldHead_world hE hI ρ (insertAtA d c Γ) hρ.2 (liftA c 1 e),
        hStepFnA_liftA hE hI d c Γ hρ.1 e]
      cases hStepFnA E I.fn Γ e <;> rfl

/-- The complete old-stage mapping supply for a world.  Its fields use
only landed typing/conversion weakening and primitive interface algebra. -/
def kStageWorldLawsA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (Γ : LCtxA) (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) :
    KStage.MapLaws E I n Γ (wkCtxA ρ Γ) (wkMapA ρ).toIotaMapA where
  typed := hasTyA_wk hE hI Γ ρ hρ
  args := fun h => convArgsA_wk hE hI ρ hρ h
  iota := fun {lhs rhs T} h _ => by
    change I.rel E (wkCtxA ρ Γ) (wkExprA ρ lhs) (wkExprA ρ rhs)
    refine ⟨?_, ?_⟩
    · rw [iota_world hI ρ lhs, h.graph]
      rfl
    · rw [oldHead_world hE hI ρ Γ hρ lhs, h.exec]
      rfl
  member := by
    intro r m hm ls
    change wkExprA ρ (instantiateLevelsA ls m.mtypeA) =
      instantiateLevelsA (ls.map id) m.mtypeA
    rw [List.map_id]
    exact wkExprA_closed (liftA_instantiateLevelsA_closed (hE r m hm).1 ls) ρ
  zero := wkExprA_sort ρ .zero
  levelZero := rfl

private theorem active_lift {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (c : Nat) {f a : ExprA}
    (h : ActiveA3 E I f a) : ActiveA3 E I (liftA c 1 f) (liftA c 1 a) := by
  cases h with
  | iota b hs hi =>
      exact .iota (liftA c 1 b) (by simpa only [structPosA_liftA] using hs)
        (by simpa only [hi, Option.map_some'] using hI c (.app f a))
  | unit mn hs hi hr hu =>
      exact .unit (liftA c 1 mn) (by simpa only [structPosA_liftA] using hs)
        (by have ht := hI c (.app f a); rw [hi] at ht; exact ht)
        (by simpa only [recAtMajorA_liftA] using hr)
        (by rw [unitMinorA_liftA, hu]; rfl)
  | structArm b hs hb =>
      exact .structArm (liftA c 1 b) (by simpa only [structPosA_liftA] using hs)
        (by rw [structArmA_liftA hE, hb]; rfl)

private theorem leaf_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) {c : Nat} {Γ : LCtxA}
    (hc : c ≤ Γ.length) {e : ExprA} (h : OldLeafA3 E I n Γ e) :
    OldLeafA3 E I n (insertAtA d c Γ) (liftA c 1 e) := by
  cases h with
  | beta A u body arg =>
      exact .beta (liftA c 1 A) u (liftA (c + 1) 1 body) (liftA c 1 arg)
  | zeta A v b => exact .zeta (liftA c 1 A) (liftA c 1 v) (liftA (c + 1) 1 b)
  | varE i => rw [liftA_bvar]; exact .varE _
  | constE r ls => exact .constE r ls
  | litE t => exact .litE t
  | application hf ha =>
      exact .application (neutralA3_lift hI d hc hf) (active_lift hE hI c ha)

private theorem leaf_world {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (ρ : WkSpecA) (Γ : LCtxA)
    (hρ : WkSpecA.ok ρ Γ) {e : ExprA} (h : OldLeafA3 E I n Γ e) :
    OldLeafA3 E I n (wkCtxA ρ Γ) (wkExprA ρ e) := by
  induction ρ generalizing Γ e with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      exact ih (insertAtA d c Γ) hρ.2 (leaf_lift hE hI d hρ.1 h)

private theorem apart_world {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (ρ : WkSpecA) (Γ : LCtxA) {e : ExprA} (h : ApartA3 E I n Γ e) :
    ApartA3 E I n (wkCtxA ρ Γ) (wkExprA ρ e) := by
  induction ρ generalizing Γ e with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      exact ih (insertAtA d c Γ) (apartA3_lift c _ h)

private theorem major_world {E : ResolvedEnvA} {I : IotaIfaceA} (hI : IotaLiftA I)
    (ρ : WkSpecA) {f a : ExprA}
    (h : structPosA E f = false ∧ I.fn (.app f a) = none ∧
      recAtMajorA E f = true ∧ unitMinorA E f = none) :
    structPosA E (wkExprA ρ f) = false ∧
      I.fn (.app (wkExprA ρ f) (wkExprA ρ a)) = none ∧
      recAtMajorA E (wkExprA ρ f) = true ∧ unitMinorA E (wkExprA ρ f) = none := by
  induction ρ generalizing f a with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      apply ih
      exact ⟨by simpa only [structPosA_liftA] using h.1,
        by have ht := hI c (.app f a); rw [h.2.1] at ht; exact ht,
        by simpa only [recAtMajorA_liftA] using h.2.2.1,
        by rw [unitMinorA_liftA, h.2.2.2]; rfl⟩

theorem headA3_wk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ)
    {a b T : ExprA} (h : HeadA3 E I n Γ a b T) :
    HeadA3 E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ T) := by
  induction h with
  | primitive a b T hl ha hs =>
      obtain ⟨hs⟩ := hs
      exact .primitive _ _ _ (leaf_world hE hI ρ Γ hρ hl) (apart_world ρ Γ ha)
        ⟨tyHRedA_wk hE hI Γ ρ hρ hs⟩
  | app f f' a A B T₀ u v hs hc hat ha ih =>
      rw [wkExprA_app, wkExprA_app, wkExprA_instantiate0A]
      have hc' := tyConvA_wk hE hI Γ ρ hρ hc
      rw [wkExprA_pi_ub] at hc'
      have ha' := apart_world ρ Γ ha
      rw [wkExprA_app] at ha'
      exact .app _ _ _ _ _ _ u v ih hc' (hasTyA_wk hE hI Γ ρ hρ hat) ha'
  | major f a a' A B T₀ u v hs hc hft ha hf hst hi hr hu ih =>
      rw [wkExprA_app, wkExprA_app, wkExprA_instantiate0A]
      have hft' := hasTyA_wk hE hI Γ ρ hρ hft
      rw [wkExprA_pi_ub] at hft'
      have ha' := apart_world ρ Γ ha
      rw [wkExprA_app] at ha'
      have hm := major_world hI ρ ⟨hst, hi, hr, hu⟩
      exact .major _ _ _ _ _ _ u v ih (tyConvA_wk hE hI Γ ρ hρ hc) hft' ha'
        (neutralA3_wk hI ρ Γ hρ hf) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  | convert a b T U hs hc ih =>
      exact .convert _ _ _ _ ih (tyConvA_wk hE hI Γ ρ hρ hc)
  | k s hw =>
      obtain ⟨w⟩ := hw
      have hs : HeadA3 E I n (wkCtxA ρ Γ) (s.map (wkMapA ρ).toIotaMapA).source
          (s.map (wkMapA ρ).toIotaMapA).minor
          (s.map (wkMapA ρ).toIotaMapA).resultType :=
        .k (s.map (wkMapA ρ).toIotaMapA)
          (w.transport hE hI hR hIS hΓ (kStageWorldLawsA3 hE hI Γ ρ hρ))
      rw [KStage.Shape.map_source, KStage.Shape.map_resultType] at hs
      exact hs

theorem headA3_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) (d : LocalDeclA) {c : Nat} (hc : c ≤ Γ.length)
    {a b T : ExprA} (h : HeadA3 E I n Γ a b T) :
    HeadA3 E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 T) :=
  headA3_wk hE hI hR hIS hΓ [(d, c)] ⟨hc, trivial⟩ h

def HeadInsertA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ (d : LocalDeclA) (c : Nat), c ≤ Γ.length →
    ∀ a b T, H.step Γ a b T →
      H.step (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 T)

def HeadWorldA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ (ρ : WkSpecA), WkSpecA.ok ρ Γ →
    ∀ a b T, H.step Γ a b T →
      H.step (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ T)

theorem contextualHeadLayerA3_stepInsert {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I) :
    HeadInsertA3 E I n (contextualHeadLayerA3 E I n) :=
  fun _ hΓ d _ hc _ _ _ h => headA3_lift hE hI hR hIS hΓ d hc h

theorem contextualHeadLayerA3_stepWorld {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I) :
    HeadWorldA3 E I n (contextualHeadLayerA3 E I n) :=
  fun _ hΓ ρ hρ _ _ _ h => headA3_wk hE hI hR hIS hΓ ρ hρ h

#print axioms kStageWorldLawsA3
#print axioms headA3_wk
#print axioms headA3_lift
#print axioms HeadInsertA3
#print axioms HeadWorldA3
#print axioms contextualHeadLayerA3_stepInsert
#print axioms contextualHeadLayerA3_stepWorld

end Rcic.Declarative.Ann.LR3
