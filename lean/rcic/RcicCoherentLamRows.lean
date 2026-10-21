import rcic.RcicCoherentCanonical
import rcic.RcicNativeValleyAppBeta

/-!
# Lambda coherence and the exact beta substitution interfaces

The lambda builder preserves the joining body's target decoration, but
reconstructs its source using the domain typing obtained from `convEnds`.
An original lambda node instead stores an independent target typing.
The scalar source-interface equation below records that difference exactly.

The canonical same-index `lam × lam` row is constructed from one original
body-child call and the two stored-target equations. Actual parent source
decoration equality identifies the written universe tags. Both joining
legs can then use the first parent's domain typing, and the original child
join supplies target equality without a context-witness uniqueness argument.

For beta, canonical head substitution's source bookkeeping is discharged
from the landed `DecoBook` theorem. This yields the exact stored-reduct
source residual. The final target equation remains an equation between the
actual two certified substitution targets, made explicit after removing
their index conversions. No target-substitution commutation law or complete
beta row is silently assumed.

`closure_claim = 0`. No global diamond, type uniqueness, Pi row, or retyping
premise is used. All child calls are on original children.
-/

namespace Rcic.Declarative.NativeValleys.CoherentLamAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open CoherentCanonicalAudit (nativeLeafIface proofLeaf_ctx proofLeaf_ctx_source_deco
  proofLeaf_lift proofLeaf_lift_source_deco native_ofIrr_source_deco)

/-- The existing certified assumption transport, instantiated at public
native proof leaves and their canonical typing transport. -/
def nativeCertAssumpCtx (hcl : EnvClosed E) :
    CertAssumpCtx E n (ProofLeaf E n) :=
  certAssumpCtx_of (PEq := ProofLeaf E n) hcl
    (fun hc h => proofLeaf_ctx hcl (F8EtaK.assumpCtxConvT_to_ctxConvT hc) h)

/-- Canonical certified assumption transport preserves source decoration. -/
theorem nativeCertAssumpCtx_source_deco (hcl : EnvClosed E)
    {Γ : LCtx} {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hA' : HasTyT E n Γ A' (.sort u))
    (hc : ConvT E n Γ A A' (.sort u)) {a b T : Expr Nat}
    (s : CStep E n (ProofLeaf E n) (.assumption A :: Γ) a b T) :
    stepDeco (nativeLeafIface E n) (nativeCertAssumpCtx hcl hA hA' hc s).step =
      stepDeco (nativeLeafIface E n) s.step := by
  unfold nativeCertAssumpCtx certAssumpCtx_of
  exact stepDeco_cstep_assumpCtx (nativeLeafIface E n) hcl
    (fun hcc h => proofLeaf_ctx hcl (F8EtaK.assumpCtxConvT_to_ctxConvT hcc) h)
    (fun hcc h => proofLeaf_ctx_source_deco hcl
      (F8EtaK.assumpCtxConvT_to_ctxConvT hcc) h)
    (.assumption (F8EtaK.assumpCtxConvT_refl Γ) hA hA' hc) s.cert

/-- Package an existing lambda constructor and its original body certificate. -/
def lamNode {Γ : LCtx} {A A' body body' B : Expr Nat} {u v : Level}
    (pb : CStep E n PEq (.assumption A :: Γ) body body' B)
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hr : HasTyT E n Γ (.lam A' body') (.pi A B))
    (c : ConvT E n Γ (.lam A body) (.lam A' body') (.pi A B)) :
    CStep E n PEq Γ (.lam A body) (.lam A' body') (.pi A B) :=
  ⟨.lam Γ A A' body body' B u v hc hA hB pb.step hr, .lam c pb.cert⟩

/-- The actual lambda source decoration reads its original body source. -/
theorem lamNode_source_deco (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A' body body' B : Expr Nat} {u v : Level}
    (pb : CStep E n PEq (.assumption A :: Γ) body body' B)
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hr : HasTyT E n Γ (.lam A' body') (.pi A B))
    (c : ConvT E n Γ (.lam A body) (.lam A' body') (.pi A B)) :
    decoOf ((lamNode pb hc hA hB hr c).leftTyped L hΓ) =
      .lam A body u (decoOf hA) (stepDeco L pb.step) := by
  rw [decoOf_leftTyped]
  rfl

/-- The actual lambda target is the independently stored typing. -/
theorem lamNode_rightTyped (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A' body body' B : Expr Nat} {u v : Level}
    (pb : CStep E n PEq (.assumption A :: Γ) body body' B)
    (hc : ConvT E n Γ A A' (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hr : HasTyT E n Γ (.lam A' body') (.pi A B))
    (c : ConvT E n Γ (.lam A body) (.lam A' body') (.pi A B)) :
    (lamNode pb hc hA hB hr c).rightTyped L hΓ = hr := rfl

/-- The exact source decoration of the landed lambda builder, before any
decoration law is imposed on its assumption-transport operation. -/
theorem lamSide_source_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ body₁ body₃ B : Expr Nat} {u v : Level}
    (hc : ConvT E n Γ A A₁ (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (pb : CStep E n PEq (.assumption A :: Γ) body₁ body₃ B) :
    decoOf ((lamSide hW L Ac hΓ hc hA hB pb).leftTyped L hΓ) =
      .lam A₁ body₁ u (decoOf (convEnds hW hΓ hc).2.1)
        (stepDeco L (Ac hA (convEnds hW hΓ hc).2.1 hc pb).step) := by
  rw [decoOf_leftTyped]
  simp only [lamSide, stepDeco_reindex, stepDeco]

/-- The landed lambda builder's target decoration uses the original-domain
typing and the original joining body's actual target typing. -/
theorem lamSide_target_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ body₁ body₃ B : Expr Nat} {u v : Level}
    (hc : ConvT E n Γ A A₁ (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (pb : CStep E n PEq (.assumption A :: Γ) body₁ body₃ B) :
    decoOf ((lamSide hW L Ac hΓ hc hA hB pb).rightTyped L hΓ) =
      .lam A body₃ u (decoOf hA)
        (decoOf (pb.rightTyped L (.assumption Γ A u hΓ hA))) := by
  unfold lamSide
  dsimp only
  simp only [CStep.reindex, CStep.rightTyped, parRedT_hasTy_right,
    parRedT_typed, decoOf_hasTyT_of_tyConvT, decoOf]

/-- Canonical assumption transport discharges the lambda builder's body
source bookkeeping without a transport premise. -/
theorem lamSide_native_source_deco (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ body₁ body₃ B : Expr Nat} {u v : Level}
    (hc : ConvT E n Γ A A₁ (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (pb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body₁ body₃ B) :
    decoOf ((lamSide hW (nativeLeafIface E n)
      (nativeCertAssumpCtx (envClosed_of_envWfT hW)) hΓ hc hA hB pb).leftTyped
        (nativeLeafIface E n) hΓ) =
      .lam A₁ body₁ u (decoOf (convEnds hW hΓ hc).2.1)
        (decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA))) := by
  rw [lamSide_source_deco, nativeCertAssumpCtx_source_deco, decoOf_leftTyped]

/-- After the original child's source interface is supplied, the exact
remaining lambda source interface is this scalar stored-target equation. -/
theorem lamSide_source_interface_iff (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ body body₁ body₃ B : Expr Nat} {u v : Level}
    (hc : ConvT E n Γ A A₁ (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (sb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body₁ B)
    (pb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body₁ body₃ B)
    (hr : HasTyT E n Γ (.lam A₁ body₁) (.pi A B))
    (hbody :
      decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA)) =
      decoOf (sb.rightTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA))) :
    (decoOf ((lamSide hW (nativeLeafIface E n)
        (nativeCertAssumpCtx (envClosed_of_envWfT hW)) hΓ hc hA hB pb).leftTyped
          (nativeLeafIface E n) hΓ) = decoOf hr) ↔
      (.lam A₁ body₁ u (decoOf (convEnds hW hΓ hc).2.1)
        (decoOf (sb.rightTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA))) =
          decoOf hr) := by
  rw [lamSide_native_source_deco, hbody]

/-- A canonical same-index `lam × lam` coherent row with its exact two
stored-target equations. The only child producer is applied to the original
body steps. The two output legs use the first parent's domain typing after
the parent source equation identifies the written universe tags. -/
def stepJoin_lam_lam_same_index (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ A₂ body body₁ body₂ B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (pb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body₁ B)
    (qb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body₂ B)
    (hc₁ : ConvT E n Γ A A₁ (.sort u₁)) (hA₁ : HasTyT E n Γ A (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁))
    (hc₂ : ConvT E n Γ A A₂ (.sort u₂)) (hA₂ : HasTyT E n Γ A (.sort u₂))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂))
    (hr₁ : HasTyT E n Γ (.lam A₁ body₁) (.pi A B))
    (hr₂ : HasTyT E n Γ (.lam A₂ body₂) (.pi A B))
    (c₁ : ConvT E n Γ (.lam A body) (.lam A₁ body₁) (.pi A B))
    (c₂ : ConvT E n Γ (.lam A body) (.lam A₂ body₂) (.pi A B))
    (hsource :
      decoOf ((lamNode pb hc₁ hA₁ hB₁ hr₁ c₁).leftTyped (nativeLeafIface E n) hΓ) =
      decoOf ((lamNode qb hc₂ hA₂ hB₂ hr₂ c₂).leftTyped (nativeLeafIface E n) hΓ))
    (ihb :
      decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁)) =
      decoOf (qb.leftTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁)) →
        DecoStarAudit.StepJoin (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁) pb qb)
    (hparent₁ : .lam A₁ body₁ u₁ (decoOf (convEnds hW hΓ hc₁).2.1)
      (decoOf (pb.rightTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁))) =
        decoOf hr₁)
    (hparent₂ : .lam A₂ body₂ u₂ (decoOf (convEnds hW hΓ hc₂).2.1)
      (decoOf (qb.rightTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁))) =
        decoOf hr₂) :
    DecoStarAudit.StepJoin (nativeLeafIface E n) hΓ
      (lamNode pb hc₁ hA₁ hB₁ hr₁ c₁) (lamNode qb hc₂ hA₂ hB₂ hr₂ c₂) := by
  have hd :
      Deco.lam A body u₁ (decoOf hA₁) (stepDeco (nativeLeafIface E n) pb.step) =
      Deco.lam A body u₂ (decoOf hA₂) (stepDeco (nativeLeafIface E n) qb.step) := by
    simpa only [lamNode_source_deco] using hsource
  injection hd with _ _ hu _ hdb
  cases hu
  have hbsource :
      decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁)) =
      decoOf (qb.leftTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁)) := by
    simpa only [decoOf_leftTyped] using hdb
  let j := ihb hbsource
  have hjl : stepDeco (nativeLeafIface E n) j.left.step =
      decoOf (pb.rightTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁)) := by
    simpa only [decoOf_leftTyped] using j.leftSource
  have hjr : stepDeco (nativeLeafIface E n) j.right.step =
      decoOf (qb.rightTyped (nativeLeafIface E n) (.assumption Γ A u₁ hΓ hA₁)) := by
    simpa only [decoOf_leftTyped] using j.rightSource
  refine
    { centre := .lam A j.centre
      left := lamSide hW (nativeLeafIface E n)
        (nativeCertAssumpCtx (envClosed_of_envWfT hW)) hΓ hc₁ hA₁ hB₁ j.left
      right := lamSide hW (nativeLeafIface E n)
        (nativeCertAssumpCtx (envClosed_of_envWfT hW)) hΓ hc₂ hA₁ hB₂ j.right
      leftSource := ?_
      rightSource := ?_
      target := ?_ }
  · rw [lamSide_native_source_deco, decoOf_leftTyped, hjl]
    exact hparent₁
  · rw [lamSide_native_source_deco, decoOf_leftTyped, hjr]
    exact hparent₂
  · rw [lamSide_target_deco, lamSide_target_deco, j.target]

/-! ## Canonical head substitution and the beta residuals -/

/-- The landed one-step mixed head substitution, with canonical proof leaves. -/
def nativeCertSubst0 (hW : EnvWfT E) : CertSubst0 E n (ProofLeaf E n) :=
  certSubst0_of hW (nativeLeafIface E n) (proofLeaf_lift (envClosed_of_envWfT hW))

/-- The exact decoration expression in the landed head-substitution law,
including its existing zero-lift cast. -/
def headSubstDeco {v body : Expr Nat} (dv : Deco v) (db : Deco body) :
    Deco (instantiate0 v body) :=
  (congrArg (fun w => instantiate0 w body) (lift_zero 0 v)) ▸
    decoSubst 0 (decoLift0 0 dv) db

/-- The canonical interface discharges both leaf premises of the landed
certified head-substitution source-decoration theorem. -/
theorem nativeCertSubst0_source_deco (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v v' body body' B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (pb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body' B)
    (pv : CStep E n (ProofLeaf E n) Γ v v' A) :
    decoOf ((nativeCertSubst0 hW hΓ hA pb pv).leftTyped (nativeLeafIface E n) hΓ) =
      headSubstDeco (decoOf (pv.leftTyped (nativeLeafIface E n) hΓ))
        (decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA))) := by
  simp only [decoOf_leftTyped]
  exact stepDeco_certSubst0_of hW (nativeLeafIface E n)
    (proofLeaf_lift (envClosed_of_envWfT hW))
    (proofLeaf_lift_source_deco (envClosed_of_envWfT hW))
    native_ofIrr_source_deco hΓ hA pb pv

/-- The actual native beta joining leg has the canonical substitution
source decoration; its final index conversion preserves this equation. -/
theorem betaRight_native_source_deco (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body' b₃ arg arg' a₃ B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    {ha : ParRedT (ProofLeaf E n) E n Γ arg arg' A} (ca : Certified ha)
    (pb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body' b₃ B)
    (pa : CStep E n (ProofLeaf E n) Γ arg' a₃ A) :
    decoOf ((betaRight (nativeLeafIface E n) (nativeCertSubst0 hW)
        hΓ hA hB ca pb pa).leftTyped (nativeLeafIface E n) hΓ) =
      headSubstDeco (decoOf (pa.leftTyped (nativeLeafIface E n) hΓ))
        (decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA))) := by
  simp only [betaRight, decoOf_reindex_left, nativeCertSubst0_source_deco]

/-- After the two original child source interfaces are supplied, beta's
remaining source interface is exactly this scalar equation on its stored
reduct typing. Canonical source bookkeeping supplies no equality with an
arbitrary stored reduct decoration. -/
theorem betaRight_source_interface_iff (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body body' b₃ arg arg' a₃ B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (sb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body body' B)
    (sa : CStep E n (ProofLeaf E n) Γ arg arg' A)
    (pb : CStep E n (ProofLeaf E n) (.assumption A :: Γ) body' b₃ B)
    (pa : CStep E n (ProofLeaf E n) Γ arg' a₃ A)
    (hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B))
    (hbs :
      decoOf (pb.leftTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA)) =
      decoOf (sb.rightTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA)))
    (has : decoOf (pa.leftTyped (nativeLeafIface E n) hΓ) =
      decoOf (sa.rightTyped (nativeLeafIface E n) hΓ)) :
    (decoOf ((betaRight (nativeLeafIface E n) (nativeCertSubst0 hW)
        hΓ hA hB sa.cert pb pa).leftTyped (nativeLeafIface E n) hΓ) = decoOf hred) ↔
      (headSubstDeco (decoOf (sa.rightTyped (nativeLeafIface E n) hΓ))
        (decoOf (sb.rightTyped (nativeLeafIface E n) (.assumption Γ A u hΓ hA))) =
          decoOf hred) := by
  rw [betaRight_native_source_deco, hbs, has]

/-- The beta joining leg's final index transport contributes no target
decoration change. Its remaining target equality is an equality of the
actual certified substitution targets. -/
theorem betaRight_target_deco (L : LeafIface E n PEq) (S : CertSubst0 E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body' b₃ arg arg' a₃ B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    {ha : ParRedT PEq E n Γ arg arg' A} (ca : Certified ha)
    (pb : CStep E n PEq (.assumption A :: Γ) body' b₃ B)
    (pa : CStep E n PEq Γ arg' a₃ A) :
    decoOf ((betaRight L S hΓ hA hB ca pb pa).rightTyped L hΓ) =
      decoOf ((S hΓ hA pb pa).rightTyped L hΓ) := by
  unfold betaRight
  exact decoOf_reindex_right L hΓ _ _

/-- The exact residual target equation for the two existing beta builders,
after their final index conversions are removed. No target-substitution
commutation theorem is assumed by this equivalence. -/
theorem betaRight_target_interface_iff (L : LeafIface E n PEq) (S : CertSubst0 E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body₁ body₂ body₃ arg arg₁ arg₂ arg₃ B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : HasTyT E n Γ A (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : HasTyT E n Γ A (.sort u₂))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂))
    {ha₁ : ParRedT PEq E n Γ arg arg₁ A} (ca₁ : Certified ha₁)
    {ha₂ : ParRedT PEq E n Γ arg arg₂ A} (ca₂ : Certified ha₂)
    (pb : CStep E n PEq (.assumption A :: Γ) body₁ body₃ B)
    (qb : CStep E n PEq (.assumption A :: Γ) body₂ body₃ B)
    (pa : CStep E n PEq Γ arg₁ arg₃ A) (qa : CStep E n PEq Γ arg₂ arg₃ A) :
    (decoOf ((betaRight L S hΓ hA₁ hB₁ ca₁ pb pa).rightTyped L hΓ) =
      decoOf ((betaRight L S hΓ hA₂ hB₂ ca₂ qb qa).rightTyped L hΓ)) ↔
      (decoOf ((S hΓ hA₁ pb pa).rightTyped L hΓ) =
        decoOf ((S hΓ hA₂ qb qa).rightTyped L hΓ)) := by
  rw [betaRight_target_deco, betaRight_target_deco]

end Rcic.Declarative.NativeValleys.CoherentLamAudit
