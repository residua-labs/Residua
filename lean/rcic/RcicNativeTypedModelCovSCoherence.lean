import rcic.RcicNativeTypedModelCovSCandidate
import rcic.RcicNativeTypedModelCovSOrigin
import rcic.RcicNativeTypedModelCovRSubstitutionBoundary

/-!
# Primitive inclusion and arrow-variance controls

If bottom is interpreted by the total predicate, forward monotonicity from
bottom forces every comparable interpretation to be total. The exact Prop
universe leaf is not total. These statements quantify over the proposed
comparison relation; no landed order on CptT is claimed.

The opaque arrow is contravariant in its domain predicate and covariant in
its codomain predicate. Enlarging its domain from the exact Prop leaf to
the total predicate can destroy membership. The concrete control uses the
actual native Sort-1 identity and its observed `polyIdOut0`, and supplies
its native type observation as well. The displayed domain/codomain
predicates are supplied primitive parameters; the Prop leaf is NOT claimed
to interpret native Sort 1. Consequently this is not a counterexample to
coherence between two interpretations derived from observations of one
native type. Such a claim requires the separate observation-to-template
connection. The strict stored-row gate has an additional variance limit.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit ReadbackCK2Audit TypedModelCovXAudit
open TypedModelCovRAudit

def CovSRelIncl (S T : CovSRel) : Prop :=
  ∀ x y c, S x y c → T x y c

theorem covSRelIncl_refl (S : CovSRel) : CovSRelIncl S S :=
  fun _ _ _ h => h

theorem covSRelIncl_trans {S T U : CovSRel}
    (hST : CovSRelIncl S T) (hTU : CovSRelIncl T U) : CovSRelIncl S U :=
  fun x y c h => hTU x y c (hST x y c h)

theorem covSRelIncl_total (S : CovSRel) : CovSRelIncl S covSTotalRel :=
  fun _ _ _ _ => trivial

/-- A forward monotone interpretation with a total least-information
element has no non-total interpretation above that element. -/
theorem covS_forward_mono_forces_total
    (le : CptT → CptT → Prop) (I : CptT → CovSRel)
    (hle : ∀ a, le .bot a) (hbot : CovSRelIncl covSTotalRel (I .bot))
    (hmono : ∀ a b, le a b → CovSRelIncl (I a) (I b)) :
    ∀ a x y c, I a x y c :=
  fun a x y c => hmono .bot a (hle a) x y c (hbot x y c trivial)

theorem covS_no_forward_mono_at_nontotal
    (le : CptT → CptT → Prop) (I : CptT → CovSRel) (a : CptT)
    (hle : le .bot a) (hbot : CovSRelIncl covSTotalRel (I .bot))
    (x y : Expr Nat) (c : CptT) (hnot : ¬ I a x y c) :
    ¬ (∀ a b, le a b → CovSRelIncl (I a) (I b)) := by
  intro hmono
  exact hnot (hmono .bot a hle x y c (hbot x y c trivial))

theorem covS_total_not_included_prop (E : ResolvedEnv) :
    ¬ CovSRelIncl covSTotalRel (covRCodeRel E .prop) := by
  intro h
  exact covRProp_support_not_prop E
    (covRSupport_intro (h (.sort .zero) (.sort .zero) .prop trivial))

/-- The only required order edge is bot <= prop. Its existence is a
displayed premise, not an invented approximation instance. -/
theorem covS_no_forward_mono_prop (E : ResolvedEnv)
    (le : CptT → CptT → Prop) (I : CptT → CovSRel)
    (hle : le .bot .prop) (hbot : CovSRelIncl covSTotalRel (I .bot))
    (hprop : I .prop = covRCodeRel E .prop) :
    ¬ (∀ a b, le a b → CovSRelIncl (I a) (I b)) := by
  intro hmono
  apply covS_total_not_included_prop E
  rw [← hprop]
  exact covSRelIncl_trans hbot (hmono .bot .prop hle)

/-- A total predicate is also a false-tag R candidate, so the primitive
arrow comparison below has actual inhabitants of all closure premises. -/
theorem covS_total_R_false (E : ResolvedEnv) (R : Readback) (Γ : LCtx) :
    CandidateCov E R Γ false covSTotalRel where
  symm := fun _ => trivial
  trans := fun _ _ => trivial
  readback := fun _ => Iff.rfl
  bot := fun _ _ => trivial
  neutral := fun _ _ _ _ _ _ => trivial
  collapse := by
    intro he
    cases he

/-- Native type, context and positivity tag are fixed. Only the supplied
predicates vary. The domain inclusion points in the opposite direction. -/
theorem covS_opaque_mixed_variance
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {p : Bool} {Dty : Expr Nat}
    {D D' B B' : CovSRel} (hD : CovSRelIncl D' D) (hB : CovSRelIncl B B') :
    CovSRelIncl (covROpaqueArrow E n Γ p Dty D B)
      (covROpaqueArrow E n Γ p Dty D' B') := by
  intro x y c h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro ds out ha hd
    have hds : ∀ u ∈ ds, covRSupport D u := by
      intro u hu
      obtain ⟨a, b, hab⟩ := hd u hu
      exact ⟨a, b, hD a b u hab⟩
    obtain ⟨a, b, hab⟩ := h.2.2.1 ds out ha hds
    exact ⟨a, b, hB a b out hab⟩
  · intro ds out ha N N' hN hN' hc hd
    exact hB _ _ out (h.2.2.2 ds out ha N N' hN hN' hc
      (fun u hu => hD N N' u (hd u hu)))

theorem covS_opaque_domain_antitone
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {p : Bool} {Dty : Expr Nat}
    {D D' B : CovSRel} (hD : CovSRelIncl D' D) :
    CovSRelIncl (covROpaqueArrow E n Γ p Dty D B)
      (covROpaqueArrow E n Γ p Dty D' B) :=
  covS_opaque_mixed_variance hD (covSRelIncl_refl B)

theorem covS_opaque_codomain_mono
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {p : Bool} {Dty : Expr Nat}
    {D B B' : CovSRel} (hB : CovSRelIncl B B') :
    CovSRelIncl (covROpaqueArrow E n Γ p Dty D B)
      (covROpaqueArrow E n Γ p Dty D B') :=
  covS_opaque_mixed_variance (covSRelIncl_refl D) hB

def covSCoherence_idSort1_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ idSort1 idSort1Ty :=
  .lam Γ (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.sort (.succ .zero))
    (.sort Γ (.succ .zero)) (.bvar _ 0 _ rfl)

def covSCoherence_idSort1Ty_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ idSort1Ty (.sort idSort1TySort) :=
  .pi Γ (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort Γ (.succ .zero)) (.sort _ (.succ .zero))

theorem covSCoherence_idSort1_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) : ApproxTK E n Γ ρ idSort1 polyIdOut0 :=
  .free (kFreeT_lam (kFreeT_sort E _) (kFreeT_bvar E 0))
    (approxT_idSort1_polyIdOut0 E ρ)

theorem covSCoherence_idSort1Ty_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) : ApproxTK E n Γ ρ idSort1Ty polyIdDom1 :=
  .free (kFreeT_pi (kFreeT_sort E _) (kFreeT_sort E _))
    (approxT_idSort1Ty_polyIdDom1 E ρ)

theorem covS_opaque_prop_identity (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covROpaqueArrow E n Γ false (.sort (.succ .zero))
      (covRCodeRel E .prop) (covRCodeRel E .prop) idSort1 idSort1 polyIdOut0 :=
  covROpaqueArrow_polyIdOut0 (covRProp_isCandidate E (WhStepCK2 E n) Γ)
    (.sort (.succ .zero))

/-- The actual native argument Prop exercises the stored demand once
the domain predicate is total, forcing the excluded `.prop` output. -/
theorem covS_opaque_total_rejects_identity (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ covROpaqueArrow E n Γ false (.sort (.succ .zero))
      covSTotalRel (covRCodeRel E .prop) idSort1 idSort1 polyIdOut0 := by
  intro h
  have hN : HasTyT E n Γ (.sort .zero) (.sort (.succ .zero)) := .sort Γ .zero
  have hout := covROpaqueArrow_apply h (covRSubstitution_identity_action E)
    (.sort .zero) (.sort .zero) hN hN ⟨.refl _ _ _ hN⟩ (fun _ _ => trivial)
  exact covRProp_support_not_prop E (covRSupport_intro hout)

theorem covS_opaque_domain_not_covariant (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovSRelIncl (covRCodeRel E .prop) covSTotalRel ∧
    ¬ CovSRelIncl
      (covROpaqueArrow E n Γ false (.sort (.succ .zero))
        (covRCodeRel E .prop) (covRCodeRel E .prop))
      (covROpaqueArrow E n Γ false (.sort (.succ .zero))
        covSTotalRel (covRCodeRel E .prop)) :=
  ⟨covSRelIncl_total _, fun h => covS_opaque_total_rejects_identity E n Γ
    (h _ _ _ (covS_opaque_prop_identity E n Γ))⟩

/-- Native and model facts accompany the primitive predicate comparison.
No correspondence from either selected domain predicate to the observed
native Sort-1 code is asserted by this control. -/
theorem covS_opaque_variance_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] idSort1 idSort1Ty) ∧
    Nonempty (HasTyT emptyEnv n [] idSort1Ty (.sort idSort1TySort)) ∧
    Nonempty (ConvT emptyEnv n [] idSort1 idSort1 idSort1Ty) ∧
    ApproxTK emptyEnv n [] EnvT.bot idSort1 polyIdOut0 ∧
    ApproxTK emptyEnv n [] EnvT.bot idSort1Ty polyIdDom1 ∧
    polyIdOut0 ≠ .bot ∧
    Nonempty (HasTyT emptyEnv n [] (.sort .zero) (.sort (.succ .zero))) ∧
    ApproxTK emptyEnv n [] EnvT.bot (.sort .zero) .prop ∧
    CovXCompactAction emptyEnv polyIdOut0 [.prop] .prop ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false (covRCodeRel emptyEnv .prop) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false covSTotalRel ∧
    CovSRelIncl (covRCodeRel emptyEnv .prop) covSTotalRel ∧
    covROpaqueArrow emptyEnv n [] false (.sort (.succ .zero))
      (covRCodeRel emptyEnv .prop) (covRCodeRel emptyEnv .prop)
      idSort1 idSort1 polyIdOut0 ∧
    ¬ covROpaqueArrow emptyEnv n [] false (.sort (.succ .zero))
      covSTotalRel (covRCodeRel emptyEnv .prop) idSort1 idSort1 polyIdOut0 := by
  have hobs : ApproxTK emptyEnv n [] EnvT.bot (.sort .zero) .prop := by
    simpa only [sortCode_zero] using approxTK_sort_code emptyEnv n [] EnvT.bot .zero
  exact ⟨⟨.empty⟩, ⟨.nil⟩, ⟨covSCoherence_idSort1_hasTy emptyEnv n []⟩,
    ⟨covSCoherence_idSort1Ty_hasTy emptyEnv n []⟩,
    ⟨.refl _ _ _ (covSCoherence_idSort1_hasTy emptyEnv n [])⟩,
    covSCoherence_idSort1_observed emptyEnv n [] EnvT.bot,
    covSCoherence_idSort1Ty_observed emptyEnv n [] EnvT.bot, CptT.noConfusion,
    ⟨.sort [] .zero⟩, hobs, covRSubstitution_identity_action emptyEnv,
    covRProp_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [],
    covS_total_R_false emptyEnv (WhStepCK2 emptyEnv n) [], covSRelIncl_total _,
    covS_opaque_prop_identity emptyEnv n [], covS_opaque_total_rejects_identity emptyEnv n []⟩

/-- The strict operator's unconditional stored-domain support adds a
covariant obligation, so its domain is not simply contravariant. -/
theorem covS_strict_total_identity (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covRArrow E n Γ false (.sort (.succ .zero)) covSTotalRel covSTotalRel
      idSort1 idSort1 polyIdOut0 := by
  apply covRArrow_lam_compact (covS_total_R_false E (WhStepCK2 E n) Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact ⟨fun _ _ => ⟨idSort1, idSort1, trivial⟩, ⟨idSort1, idSort1, trivial⟩⟩

theorem covS_strict_prop_rejects_identity (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ covRArrow E n Γ false (.sort (.succ .zero))
      (covRCodeRel E .prop) covSTotalRel idSort1 idSort1 polyIdOut0 := by
  intro h
  have hr := covRArrow_rows h
  exact covRProp_support_not_prop E
    ((hr ([.prop], .prop) (List.mem_singleton_self _)).1 .prop (List.mem_singleton_self _))

theorem covS_strict_domain_not_antitone (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovSRelIncl (covRCodeRel E .prop) covSTotalRel ∧
    ¬ CovSRelIncl
      (covRArrow E n Γ false (.sort (.succ .zero)) covSTotalRel covSTotalRel)
      (covRArrow E n Γ false (.sort (.succ .zero)) (covRCodeRel E .prop) covSTotalRel) :=
  ⟨covSRelIncl_total _, fun h => covS_strict_prop_rejects_identity E n Γ
    (h _ _ _ (covS_strict_total_identity E n Γ))⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_COHERENCE_ROOTS
#print axioms CovSRelIncl
#print axioms covSRelIncl_refl
#print axioms covSRelIncl_trans
#print axioms covSRelIncl_total
#print axioms covS_forward_mono_forces_total
#print axioms covS_no_forward_mono_at_nontotal
#print axioms covS_total_not_included_prop
#print axioms covS_no_forward_mono_prop
#print axioms covS_total_R_false
#print axioms covS_opaque_mixed_variance
#print axioms covS_opaque_domain_antitone
#print axioms covS_opaque_codomain_mono
#print axioms covSCoherence_idSort1_hasTy
#print axioms covSCoherence_idSort1Ty_hasTy
#print axioms covSCoherence_idSort1_observed
#print axioms covSCoherence_idSort1Ty_observed
#print axioms covS_opaque_prop_identity
#print axioms covS_opaque_total_rejects_identity
#print axioms covS_opaque_domain_not_covariant
#print axioms covS_opaque_variance_control
#print axioms covS_strict_total_identity
#print axioms covS_strict_prop_rejects_identity
#print axioms covS_strict_domain_not_antitone
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_COHERENCE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
