import rcic.RcicNativeTypedModelCovRForall

/-!
# Ordinary arrows at an opaque candidate variable

A candidate supplied at a sort binder need not support every demand stored
in a lambda compact. This operator retains the function-shape gate, positive
collapse, compact-action coverage, and actual typed application behavior.
Its coverage and application premises test demands in the supplied candidate;
it imposes no additional unconditional stored-row support test.

The identity supplier below is conditional on actual demanded membership.
It returns that same membership along native CK2 beta readback. The concrete
polymorphic identity and its landed non-bottom compact therefore satisfy the
fresh sort-binder clause for every supplied candidate. This is a lexical
opaque-domain clause. It does not supply an unconditional substitution
equality with the strict concrete-domain arrow operator. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovPAudit

def covROpaqueArrow (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (positive : Bool)
    (Dty : Expr Nat) (D B : CovRRel) : CovRRel :=
  fun x y c => CovRFunctionShape c ∧ (positive = true → c = .bot) ∧
    CovRArrowCoverage E D B c ∧ CovRArrowAction E n Γ Dty D B x y c

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  {positive domainPositive : Bool} {Dty : Expr Nat} {D B : CovRRel}

theorem covROpaqueArrow_intro {x y : Expr Nat} {c : CptT}
    (hs : CovRFunctionShape c)
    (hp : positive = true → c = .bot)
    (hc : CovRArrowCoverage E D B c)
    (ha : CovRArrowAction E n Γ Dty D B x y c) :
    covROpaqueArrow E n Γ positive Dty D B x y c :=
  ⟨hs, hp, hc, ha⟩

theorem covROpaqueArrow_shape {x y : Expr Nat} {c : CptT}
    (h : covROpaqueArrow E n Γ positive Dty D B x y c) :
    CovRFunctionShape c := h.1

theorem covROpaqueArrow_coverage {x y : Expr Nat} {c : CptT}
    (h : covROpaqueArrow E n Γ positive Dty D B x y c) :
    CovRArrowCoverage E D B c := h.2.2.1

/-- The same explicit singleton semantic row witnesses action coverage.
Only domain-supported demands are exercised by the coverage premise. -/
theorem covROpaqueArrow_singleton_coverage {x y : Expr Nat} {c : CptT}
    (h : covROpaqueArrow E n Γ positive Dty D B x y c)
    {ds : List CptT} {out : CptT} (ha : CovXCompactAction E c ds out)
    (hd : ∀ u ∈ ds, covRSupport D u) :
    ∃ row : List CptT × CovRRel, row ∈ [([], B)] ∧
      (∀ u ∈ row.1, u ∈ ds) ∧ covRSupport row.2 out :=
  ⟨([], B), List.mem_singleton_self _,
    (fun u hu => (List.not_mem_nil u hu).elim), h.2.2.1 ds out ha hd⟩

theorem covROpaqueArrow_apply {x y : Expr Nat} {c : CptT}
    (h : covROpaqueArrow E n Γ positive Dty D B x y c)
    {ds : List CptT} {out : CptT} (ha : CovXCompactAction E c ds out)
    (N N' : Expr Nat) (hN : HasTyT E n Γ N Dty) (hN' : HasTyT E n Γ N' Dty)
    (hconv : Nonempty (ConvT E n Γ N N' Dty))
    (hd : ∀ u ∈ ds, D N N' u) : B (.app x N) (.app y N') out :=
  h.2.2.2 ds out ha N N' hN hN' hconv hd

theorem covROpaqueArrow_bot
    (hB : CandidateCov E (WhStepCK2 E n) Γ positive B) (x y : Expr Nat) :
    covROpaqueArrow E n Γ positive Dty D B x y .bot := by
  refine ⟨Or.inl rfl, fun _ => rfl, ?_, ?_⟩
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot hB
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact hB.bot _ _

theorem covROpaqueArrow_neutral
    (hB : CandidateCov E (WhStepCK2 E n) Γ false B)
    (x y : Expr Nat) (r : Nat) (us : List CptT) (hh : NeutralHeadP E r) :
    covROpaqueArrow E n Γ false Dty D B x y (.spine r us) := by
  refine ⟨Or.inr (Or.inr ⟨r, us, rfl⟩), ?_, ?_, ?_⟩
  · intro he
    cases he
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot hB
    | appSpine _ => exact covRSupport_intro (hB.neutral rfl x y r _ hh)
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact hB.bot _ _
    | appSpine _ => exact hB.neutral rfl _ _ r _ hh

/-- Candidate closure uses actual application congruence and the same
middle native argument. It does not quantify over finite type-code joins. -/
theorem covROpaqueArrow_isCandidate
    (hD : CandidateCov E (WhStepCK2 E n) Γ domainPositive D)
    (hB : CandidateCov E (WhStepCK2 E n) Γ positive B) :
    CandidateCov E (WhStepCK2 E n) Γ positive
      (covROpaqueArrow E n Γ positive Dty D B) where
  symm := by
    intro x y c h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    intro ds out ha N N' hN hN' hconv hd
    obtain ⟨hc⟩ := hconv
    exact hB.symm (h.2.2.2 ds out ha N' N hN' hN
      ⟨.symm _ _ _ _ hc⟩ (fun u hu => hD.symm (hd u hu)))
  trans := by
    intro x y z c hxy hyz
    refine ⟨hxy.1, hxy.2.1, hxy.2.2.1, ?_⟩
    intro ds out ha N N' hN hN' hconv hd
    have hleft := hxy.2.2.2 ds out ha N N hN hN ⟨.refl _ _ _ hN⟩
      (fun u hu => hD.self_left (hd u hu))
    have hright := hyz.2.2.2 ds out ha N N' hN hN' hconv hd
    exact hB.trans hleft hright
  readback := by
    intro x x' y c hx
    constructor
    · intro h
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      intro ds out ha N N' hN hN' hconv hd
      exact (hB.readback (redR_appHead (readbackLaws_whStepCK2 E n) hx)).mp
        (h.2.2.2 ds out ha N N' hN hN' hconv hd)
    · intro h
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      intro ds out ha N N' hN hN' hconv hd
      exact (hB.readback (redR_appHead (readbackLaws_whStepCK2 E n) hx)).mpr
        (h.2.2.2 ds out ha N N' hN hN' hconv hd)
  bot := covROpaqueArrow_bot hB
  neutral := by
    intro he x y r us hh
    subst positive
    exact covROpaqueArrow_neutral hB x y r us hh
  collapse := by
    intro he x y c h
    exact h.2.1 he

/-- The original identity beta step supplies endpoint readback at every
native argument; there is no semantic substitution axiom here. -/
theorem covROpaqueArrow_identity_readback (T N : Expr Nat) :
    RedR (WhStepCK2 E n) Γ (.app (.lam T (.bvar 0)) N) N :=
  redR_single ((readbackLaws_whStepCK2 E n).beta Γ T (.bvar 0) N)

/-- Returning a demanded compact supplies both support coverage and the
actual endpoint relation. No unconditional membership of a stored demand
is assumed or inferred. -/
theorem covROpaqueArrow_identity {S : CovRRel} {c : CptT}
    (hS : CandidateCov E (WhStepCK2 E n) Γ false S) (T : Expr Nat)
    (hshape : CovRFunctionShape c)
    (hidentity : ∀ ds out, CovXCompactAction E c ds out →
      out = .bot ∨ out ∈ ds) :
    covROpaqueArrow E n Γ false T S S
      (.lam T (.bvar 0)) (.lam T (.bvar 0)) c := by
  refine ⟨hshape, ?_, ?_, ?_⟩
  · intro he
    cases he
  · intro ds out ha hd
    rcases hidentity ds out ha with rfl | hm
    · exact covRSupport_bot hS
    · exact hd out hm
  · intro ds out ha N N' _ _ _ hd
    rcases hidentity ds out ha with rfl | hm
    · exact hS.bot _ _
    · exact (hS.readback_both
        (covROpaqueArrow_identity_readback T N)
        (covROpaqueArrow_identity_readback T N')).mpr (hd out hm)

/-- A lambda table whose output is bottom or one of its own demands has
the identity action property in every finite demand environment. -/
theorem covRIdentityRows_action {rows : List (List CptT × CptT)}
    (hrows : ∀ row ∈ rows, row.2 = .bot ∨ row.2 ∈ row.1)
    {ds : List CptT} {out : CptT}
    (ha : CovXCompactAction E (.lam rows) ds out) :
    out = .bot ∨ out ∈ ds := by
  cases ha with
  | bot => exact Or.inl rfl
  | app hs hx =>
      rcases hrows _ hs with hb | hm
      · exact Or.inl hb
      · simpa only [EnvT.cons, demandT] using approxT_bvar_inv (hx _ hm)

theorem covROpaqueArrow_polyIdOut0_action {ds : List CptT} {out : CptT}
    (ha : CovXCompactAction E polyIdOut0 ds out) : out = .bot ∨ out ∈ ds := by
  apply covRIdentityRows_action (rows := [([.prop], .prop)]) _ ha
  intro row hrow
  rcases List.mem_singleton.mp hrow with rfl
  exact Or.inr (List.mem_singleton_self _)

theorem covROpaqueArrow_polyIdOut0 {S : CovRRel}
    (hS : CandidateCov E (WhStepCK2 E n) Γ false S) (T : Expr Nat) :
    covROpaqueArrow E n Γ false T S S
      (.lam T (.bvar 0)) (.lam T (.bvar 0)) polyIdOut0 :=
  covROpaqueArrow_identity hS T (Or.inr (Or.inl ⟨_, rfl⟩))
    (fun _ _ ha => covROpaqueArrow_polyIdOut0_action ha)

theorem covROpaqueArrow_cexPolyId_readback (T : Expr Nat) :
    RedR (WhStepCK2 E n) Γ (.app cexPolyId T) (.lam T (.bvar 0)) :=
  redR_single ((readbackLaws_whStepCK2 E n).beta Γ (.sort (.succ .zero))
    (.lam (.bvar 0) (.bvar 0)) T)

/-- Both native beta steps are composed at the actual type and term
arguments. Candidate readback can consume this trace directly. -/
theorem covROpaqueArrow_cexPolyId_two_beta (T N : Expr Nat) :
    RedR (WhStepCK2 E n) Γ (.app (.app cexPolyId T) N) N :=
  redR_trans
    (redR_appHead (readbackLaws_whStepCK2 E n)
      (covROpaqueArrow_cexPolyId_readback T))
    (covROpaqueArrow_identity_readback T N)

theorem covROpaqueArrow_polyIdCpt0_action {ds : List CptT} {out : CptT}
    (ha : CovXCompactAction E polyIdCpt0 ds out) :
    out = .bot ∨ out = polyIdOut0 := by
  change AppCptT E (EnvT.cons (demandT ds) EnvT.bot)
    (.lam [([.sort], polyIdOut0)]) (.bvar 0) out at ha
  cases ha with
  | bot => exact Or.inl rfl
  | app hs _ =>
      rcases List.mem_singleton.mp hs with rfl
      exact Or.inr rfl

/-- A genuine polymorphic lambda supplier for the fresh forall clause.
Both the native type and its candidate remain universally quantified. -/
theorem covROpaqueArrow_cexPolyId (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covRForall E n Γ (.succ .zero) false false
      (fun T S => covROpaqueArrow E n Γ false T S S)
      cexPolyId cexPolyId polyIdCpt0 := by
  refine ⟨Or.inr (Or.inl ⟨_, rfl⟩), ?_, ?_⟩
  · intro he
    cases he
  · intro ds out ha T _ S hS
    rcases covROpaqueArrow_polyIdCpt0_action ha with rfl | rfl
    · exact covROpaqueArrow_bot hS _ _
    · have hB : CandidateCov E (WhStepCK2 E n) Γ false
          (covROpaqueArrow E n Γ false T S S) :=
        covROpaqueArrow_isCandidate hS hS
      exact (hB.readback_both
        (covROpaqueArrow_cexPolyId_readback T)
        (covROpaqueArrow_cexPolyId_readback T)).mpr
          (covROpaqueArrow_polyIdOut0 hS T)

/-- Native typing, self conversion, saturated-model observation and the
new relation all have inhabitants in the admitted empty environment. -/
theorem covROpaqueArrow_cexPolyId_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (ConvT emptyEnv n [] cexPolyId cexPolyId cexPolyIdTy) ∧
    ApproxTK emptyEnv n [] ρ cexPolyId polyIdCpt0 ∧
    covRForall emptyEnv n [] (.succ .zero) false false
      (fun T S => covROpaqueArrow emptyEnv n [] false T S S)
      cexPolyId cexPolyId polyIdCpt0 ∧
    polyIdCpt0 ≠ .bot ∧ polyIdOut0 ≠ .bot := by
  refine ⟨⟨.empty⟩, ⟨.nil⟩, ⟨hasTyT_cexPolyId emptyEnv n⟩,
    ⟨.refl _ _ _ (hasTyT_cexPolyId emptyEnv n)⟩, ?_,
    covROpaqueArrow_cexPolyId emptyEnv n [], CptT.noConfusion, CptT.noConfusion⟩
  exact ApproxTK.free
    (kFreeT_lam (kFreeT_sort emptyEnv _)
      (kFreeT_lam (kFreeT_bvar emptyEnv 0) (kFreeT_bvar emptyEnv 0)))
    (approxT_cexPolyId_cpt0 emptyEnv ρ)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_OPAQUE_ARROW_ROOTS
#print axioms covROpaqueArrow
#print axioms covROpaqueArrow_intro
#print axioms covROpaqueArrow_shape
#print axioms covROpaqueArrow_coverage
#print axioms covROpaqueArrow_singleton_coverage
#print axioms covROpaqueArrow_apply
#print axioms covROpaqueArrow_bot
#print axioms covROpaqueArrow_neutral
#print axioms covROpaqueArrow_isCandidate
#print axioms covROpaqueArrow_identity_readback
#print axioms covROpaqueArrow_identity
#print axioms covRIdentityRows_action
#print axioms covROpaqueArrow_polyIdOut0_action
#print axioms covROpaqueArrow_polyIdOut0
#print axioms covROpaqueArrow_cexPolyId_readback
#print axioms covROpaqueArrow_cexPolyId_two_beta
#print axioms covROpaqueArrow_polyIdCpt0_action
#print axioms covROpaqueArrow_cexPolyId
#print axioms covROpaqueArrow_cexPolyId_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_OPAQUE_ARROW_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
