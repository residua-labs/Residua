import rcic.RcicAnnKStage

/-!
# Transport and the two-stage typed K head relation

`Head` extends the old typed iota relation by `Frame`.  Its guard remains in
the unchanged old annotated conversion.  Both actual Frame witnesses and
Head steps survive typed substitution and context insertion.

These are forward laws for a typed context-aware relation.  They are not
the `Option` equality `IotaLiftA` for a context-free executable function.
The two-stage well-founded order concerns dependencies of the guard; it is
not a normalization theorem for the head relation.
-/

namespace Rcic.Declarative.Ann.KStage

open Rcic.Declarative

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- Transport syntax with the same under-binder map as the existing iota
algebra.  The environment's stored group remains unchanged. -/
def Shape.map (s : Shape) (M : IotaMapA) : Shape where
  recRef := s.recRef
  ctorRef := s.ctorRef
  group := s.group
  recLevels := s.recLevels.map M.ψ
  familyLevels := s.familyLevels.map M.ψ
  ctorLevels := s.ctorLevels.map M.ψ
  params := s.params.map M.φ
  declaredIndices := s.declaredIndices.map M.φ
  actualIndices := s.actualIndices.map M.φ
  motive := M.φ s.motive
  minor := M.φ s.minor
  major := M.φ s.major
  body := M.φb s.body
  codSort := M.ψ s.codSort

theorem Shape.map_pre (s : Shape) (M : IotaMapA) :
    (s.map M).pre = s.pre.map M.φ := by
  simp [Shape.map, Shape.pre, List.map_append]

theorem Shape.map_prefix (s : Shape) (M : IotaMapA) :
    (s.map M).prefix = M.φ s.prefix := by
  change foldAppsA (.const s.recRef (s.recLevels.map M.ψ)) (s.map M).pre =
    M.φ (foldAppsA (.const s.recRef s.recLevels) s.pre)
  rw [Shape.map_pre, M.foldAppsA_map, M.const]

theorem Shape.map_familyHead (s : Shape) (M : IotaMapA) :
    (s.map M).familyHead = M.φ s.familyHead := by
  change foldAppsA (.const s.group.familyRef (s.familyLevels.map M.ψ))
    (s.params.map M.φ) = M.φ (foldAppsA (.const s.group.familyRef s.familyLevels) s.params)
  rw [M.foldAppsA_map, M.const]

theorem Shape.map_actualProp (s : Shape) (M : IotaMapA) :
    (s.map M).actualProp = M.φ s.actualProp := by
  unfold Shape.actualProp
  rw [Shape.map_familyHead, M.foldAppsA_map]
  rfl

theorem Shape.map_declaredProp (s : Shape) (M : IotaMapA) :
    (s.map M).declaredProp = M.φ s.declaredProp := by
  unfold Shape.declaredProp
  rw [Shape.map_familyHead, M.foldAppsA_map]
  rfl

theorem Shape.map_canonical (s : Shape) (M : IotaMapA) :
    (s.map M).canonical = M.φ s.canonical := by
  change foldAppsA (.const s.ctorRef (s.ctorLevels.map M.ψ)) (s.params.map M.φ) =
    M.φ (foldAppsA (.const s.ctorRef s.ctorLevels) s.params)
  rw [M.foldAppsA_map, M.const]

theorem Shape.map_source (s : Shape) (M : IotaMapA) :
    (s.map M).source = M.φ s.source := by
  unfold Shape.source
  rw [Shape.map_prefix, M.app]
  rfl

theorem Shape.map_canonicalCall (s : Shape) (M : IotaMapA) :
    (s.map M).canonicalCall = M.φ s.canonicalCall := by
  unfold Shape.canonicalCall
  rw [Shape.map_prefix, Shape.map_canonical, M.app]

theorem Shape.map_resultType (s : Shape) (M : IotaMapA) :
    (s.map M).resultType = M.φ s.resultType := by
  exact (M.inst s.major s.body).symm

def Target.map {E : ResolvedEnvA} {s : Shape} (w : Target E s) (M : IotaMapA) :
    Target E (s.map M) where
  group := w.group
  oneConstructor := w.oneConstructor
  propFamily := w.propFamily
  noFields := w.noFields
  paramCount := by simpa [Shape.map] using w.paramCount
  arity := by
    change (s.map M).pre.length + 1 = piCountA s.group.recM.mtypeA
    rw [Shape.map_pre, List.length_map]
    exact w.arity

/-- Already-proved laws of the OLD interface under a syntax map.
No new K relation occurs in these requirements. -/
structure MapLaws (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ Δ : LCtxA) (M : IotaMapA) where
  typed : ∀ {e A : ExprA}, HasTyA E I n Γ e A →
    HasTyA E I n Δ (M.φ e) (M.φ A)
  args : ∀ {T : ExprA} {xs ys : List ExprA}, ConvArgsA E I n Γ T xs ys →
    ConvArgsA E I n Δ (M.φ T) (xs.map M.φ) (ys.map M.φ)
  iota : ∀ {lhs rhs T : ExprA}, I.rel E Γ lhs rhs → HasTyA E I n Γ lhs T →
    I.rel E Δ (M.φ lhs) (M.φ rhs)
  member : ∀ r m, E.members r = some m → ∀ ls,
    M.φ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA (ls.map M.ψ) m.mtypeA
  zero : M.φ (.sort .zero) = .sort .zero
  levelZero : M.ψ .zero = .zero

section Transport

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ Δ : LCtxA}
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I) (hΓ : CtxWfA E I n Γ)

include hE hI hR hIS hΓ

/-- Actual K witnesses, including the guard and canonical old iota execution,
transport through any supplied old-interface syntax map. -/
theorem Frame.transport {M : IotaMapA} (H : MapLaws E I n Γ Δ M)
    {s : Shape} (w : Frame E I n Γ s) : Nonempty (Frame E I n Δ (s.map M)) := by
  obtain ⟨halign⟩ := w.canonicalAlignment hE hI hR hIS hΓ
  have hcanonicalCall := convA_hasTy_right hE hI hR hIS hΓ halign
  obtain ⟨_, _, _, _, _, hfm, _⟩ := iotaGroupA_some w.target.group
  refine ⟨{
    target := w.target.map M
    familyTelescope := M.φ w.familyTelescope
    telescope := ?_
    familyHeadType := ?_
    indexGuard := H.args w.indexGuard
    familyResult := ?_
    prefixType := ?_
    majorType := ?_
    canonicalType := ?_
    canonicalIota := ?_
    minorType := ?_ }⟩
  · have ht := M.applyTelA_some s.params w.telescope
    rw [H.member _ _ hfm s.familyLevels] at ht
    exact ht
  · simpa only [Shape.map_familyHead] using H.typed w.familyHeadType
  · have ht := M.applyTelA_some s.declaredIndices w.familyResult
    rw [H.zero] at ht
    exact ht
  · have ht := H.typed w.prefixType
    rw [M.pi, H.levelZero] at ht
    simpa only [Shape.map_prefix, Shape.map_actualProp] using ht
  · simpa only [Shape.map_actualProp] using H.typed w.majorType
  · simpa only [Shape.map_canonical, Shape.map_declaredProp] using H.typed w.canonicalType
  · simpa only [Shape.map_canonicalCall] using H.iota w.canonicalIota hcanonicalCall
  · simpa only [Shape.map_resultType] using H.typed w.minorType

end Transport

section ConcreteMaps

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- Old-interface laws for inserting one declaration at an arbitrary cutoff. -/
def liftLaws (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA)
    {Γ : LCtxA} {c : Nat} (hc : c ≤ Γ.length) :
    MapLaws E I n Γ (insertAtA d c Γ) (liftMapA c).toIotaMapA where
  typed := hasTyWeakenA hE hI d hc
  args := fun h => convArgsA_wk hE hI [(d, c)] ⟨hc, trivial⟩ h
  iota := fun {lhs rhs T} h _ => by
    change I.rel E (insertAtA d c Γ) (liftA c 1 lhs) (liftA c 1 rhs)
    refine ⟨?_, ?_⟩
    · have hg := hI c lhs
      rw [h.graph] at hg
      exact hg
    · have hs := hStepFnA_liftA hE hI d c Γ hc lhs
      rw [h.exec] at hs
      exact hs
  member := by
    intro r m hm ls
    change liftA c 1 (instantiateLevelsA ls m.mtypeA) =
      instantiateLevelsA (ls.map id) m.mtypeA
    rw [List.map_id, ← instantiateLevelsA_liftA, (hE r m hm).1 c]
  zero := rfl
  levelZero := rfl

/-- Old-interface laws for a typed simultaneous substitution. -/
def substLaws (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ Δ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) : MapLaws E I n Γ Δ (substMapA σ) where
  typed := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ
  args := KIndexLaws.convArgs_subst hE hI hR hIS hσ
  iota := fun h ht => iotaRel_substA hE (iotaRecHeadTypedA_of hR) hIS σ h ⟨ht⟩
    ⟨hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ ht⟩
  member := by
    intro r m hm ls
    change substA σ (instantiateLevelsA ls m.mtypeA) =
      instantiateLevelsA (ls.map id) m.mtypeA
    rw [List.map_id]
    exact substA_closed (liftA_instantiateLevelsA_closed (hE r m hm).1 ls) σ
  zero := rfl
  levelZero := rfl

theorem Frame.lift (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    (d : LocalDeclA) {c : Nat} (hc : c ≤ Γ.length) {s : Shape}
    (w : Frame E I n Γ s) :
    Nonempty (Frame E I n (insertAtA d c Γ) (s.map (liftMapA c).toIotaMapA)) :=
  w.transport hE hI hR hIS hΓ (liftLaws hE hI d hc)

theorem Frame.subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ Δ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) {s : Shape}
    (w : Frame E I n Γ s) : Nonempty (Frame E I n Δ (s.map (substMapA σ))) :=
  w.transport hE hI hR hIS hΓ (substLaws hE hI hR hIS hσ)

end ConcreteMaps

/-- The stages name a dependency order.  Guards and their typed conversion
are at `base`; the new relational step is at `k`. -/
inductive Phase where
  | base
  | k

def Phase.rank : Phase → Nat
  | .base => 0
  | .k => 1

def Phase.before (a b : Phase) : Prop := a.rank < b.rank

theorem phaseWellFounded : WellFounded Phase.before :=
  InvImage.wf Phase.rank Nat.lt_wfRel.wf

theorem guardPrecedesStep : Phase.before .base .k := Nat.zero_lt_succ 0

/-- The typed context-aware extension.  Its K arm consumes the old-interface
Frame, not a derivation in this newly-defined relation. -/
inductive Head (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    ExprA → ExprA → ExprA → Prop
  | old {lhs rhs T : ExprA} (h : I.rel E Γ lhs rhs)
      (hl : Nonempty (HasTyA E I n Γ lhs T))
      (hr : Nonempty (HasTyA E I n Γ rhs T)) : Head E I n Γ lhs rhs T
  | k (s : Shape) (h : Nonempty (Frame E I n Γ s)) :
      Head E I n Γ s.source s.minor s.resultType

section HeadLaws

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I) (hΓ : CtxWfA E I n Γ)

include hE hI hR hIS hΓ

theorem Head.sound {lhs rhs T : ExprA} (h : Head E I n Γ lhs rhs T) :
    Nonempty (ConvA E I n Γ lhs rhs T) := by
  cases h with
  | old h hl hr =>
      obtain ⟨hl⟩ := hl
      obtain ⟨hr⟩ := hr
      exact ⟨.iota Γ _ _ _ h hl hr⟩
  | k s h =>
      obtain ⟨w⟩ := h
      exact w.sound hE hI hR hIS hΓ

omit hE hI hIS hΓ in
theorem Head.recHead {lhs rhs T : ExprA} (h : Head E I n Γ lhs rhs T) :
    ∃ r ls m, (appsSpineA lhs).1 = .const r ls ∧
      E.members r = some m ∧ m.mclass = .recursorM ∧
      (appsSpineA lhs).2.length = piCountA m.mtypeA := by
  cases h with
  | old h _ _ => exact hR _ _ h.graph
  | k s h => exact h.elim Frame.recHead

theorem Head.subst {Δ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ)
    {lhs rhs T : ExprA} (h : Head E I n Γ lhs rhs T) :
    Head E I n Δ (substA σ lhs) (substA σ rhs) (substA σ T) := by
  cases h with
  | old h hl hr =>
      obtain ⟨hl⟩ := hl
      obtain ⟨hr⟩ := hr
      let H := substLaws hE hI hR hIS hσ
      exact .old (H.iota h hl) ⟨H.typed hl⟩ ⟨H.typed hr⟩
  | k s h =>
      obtain ⟨w⟩ := h
      have hw := w.subst hE hI hR hIS hΓ hσ
      have hh := Head.k (s.map (substMapA σ)) hw
      simpa only [Shape.map_source, Shape.map_resultType] using hh

theorem Head.lift (d : LocalDeclA) {c : Nat} (hc : c ≤ Γ.length)
    {lhs rhs T : ExprA} (h : Head E I n Γ lhs rhs T) :
    Head E I n (insertAtA d c Γ) (liftA c 1 lhs) (liftA c 1 rhs) (liftA c 1 T) := by
  cases h with
  | old h hl hr =>
      obtain ⟨hl⟩ := hl
      obtain ⟨hr⟩ := hr
      let H := liftLaws (n := n) hE hI d hc
      exact .old (H.iota h hl) ⟨H.typed hl⟩ ⟨H.typed hr⟩
  | k s h =>
      obtain ⟨w⟩ := h
      have hw := w.lift hE hI hR hIS hΓ d hc
      have hh := Head.k (s.map (liftMapA c).toIotaMapA) hw
      simpa only [Shape.map_source, Shape.map_resultType] using hh

end HeadLaws

#print axioms Shape.map
#print axioms Shape.map_pre
#print axioms Shape.map_prefix
#print axioms Shape.map_familyHead
#print axioms Shape.map_actualProp
#print axioms Shape.map_declaredProp
#print axioms Shape.map_canonical
#print axioms Shape.map_source
#print axioms Shape.map_canonicalCall
#print axioms Shape.map_resultType
#print axioms Target.map
#print axioms MapLaws
#print axioms Frame.transport
#print axioms liftLaws
#print axioms substLaws
#print axioms Frame.lift
#print axioms Frame.subst
#print axioms Phase
#print axioms Phase.rank
#print axioms Phase.before
#print axioms phaseWellFounded
#print axioms guardPrecedesStep
#print axioms Head
#print axioms Head.sound
#print axioms Head.recHead
#print axioms Head.subst
#print axioms Head.lift

end Rcic.Declarative.Ann.KStage
