import rcic.RcicPiRowProj
import rcic.RcicNativeDecoStrip
import rcic.RcicNativeValleyDecoBook

/-!
# Canonical native leaves and elementary coherent diamond rows

The public `Rcic.Declarative.ProofLeaf` stores all three supplied typings.
The canonical interface below returns
its two endpoint typings verbatim. Both irrelevance roundtrips therefore
hold as equalities of typings, as well as of their actual decorations.
Weakening and context transport use the landed native typing operations;
the decoration equations below specialize the existing `DecoBook` laws.

The elementary rows return the existing `DecoStarAudit.StepJoin`, including
both source interfaces and the target equation. The proof-index row joins
back at the original source: its two final typings are the two actual
source typings of the input steps, so the input source-decoration equality
is exactly the output target equality.

No recursive diamond is assumed or constructed. These definitions make no
recursive calls. No type-uniqueness, Pi row, or retyping premise is used.
The public carrier is reused from `RcicPiRowProj` at
`0f5ba888603d425687f9a53d866667560f2b2513`; no new carrier or alias is introduced.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentCanonicalAudit

variable {E : ResolvedEnv} {n : Nat}

/-- The canonical interface returns the stored endpoint typings verbatim. -/
def nativeLeafIface (E : ResolvedEnv) (n : Nat) :
    LeafIface E n (ProofLeaf E n) where
  typed := fun h => ⟨h.hp, h.hq⟩
  conv := fun h => .irr _ _ _ _ h.hT h.hp h.hq
  prop := fun h => h.hT
  ofIrr := fun hP hp hq => ⟨hP, hp, hq⟩

/-- Formation and extraction return exactly the supplied pair of typings. -/
@[simp] theorem native_typed_ofIrr {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (nativeLeafIface E n).typed ((nativeLeafIface E n).ofIrr hP hp hq) =
      (hp, hq) := rfl

/-- The source decoration roundtrip used by mixed certified substitution. -/
@[simp] theorem native_ofIrr_source_deco {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    decoOf ((nativeLeafIface E n).typed
      ((nativeLeafIface E n).ofIrr hP hp hq)).1 = decoOf hp := rfl

/-- The target decoration roundtrip needed at the centre of a coherent row. -/
@[simp] theorem native_ofIrr_target_deco {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    decoOf ((nativeLeafIface E n).typed
      ((nativeLeafIface E n).ofIrr hP hp hq)).2 = decoOf hq := rfl

/-- The actual certified irrelevance step returns the supplied source typing. -/
@[simp] theorem native_irr_leftTyped {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (CStep.irr (nativeLeafIface E n) hP hp hq).leftTyped
      (nativeLeafIface E n) hΓ = hp := rfl

/-- The actual certified irrelevance step returns the supplied target typing. -/
@[simp] theorem native_irr_rightTyped {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (CStep.irr (nativeLeafIface E n) hP hp hq).rightTyped
      (nativeLeafIface E n) hΓ = hq := rfl

/-- Native proof leaves weaken using the existing native typing weakening. -/
def proofLeaf_lift (hcl : EnvClosed E) {Γ : LCtx} {p q T : Expr Nat}
    {d' : LocalDecl} {c : Nat} (h : ProofLeaf E n Γ p q T) :
    ProofLeaf E n (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T) :=
  ⟨hasTyTWeaken d' hcl (c := c) h.hT,
    hasTyTWeaken d' hcl (c := c) h.hp,
    hasTyTWeaken d' hcl (c := c) h.hq⟩

/-- The canonical weakening operation has the required source decoration. -/
theorem proofLeaf_lift_source_deco (hcl : EnvClosed E)
    {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat}
    (h : ProofLeaf E n Γ p q T) :
    decoOf ((nativeLeafIface E n).typed
      (proofLeaf_lift hcl (d' := d') (c := c) h)).1 =
        decoLift c 1 (decoOf ((nativeLeafIface E n).typed h).1) :=
  decoOf_hasTyTWeaken d' hcl h.hp

/-- The canonical weakening operation also has the required target decoration. -/
theorem proofLeaf_lift_target_deco (hcl : EnvClosed E)
    {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat}
    (h : ProofLeaf E n Γ p q T) :
    decoOf ((nativeLeafIface E n).typed
      (proofLeaf_lift hcl (d' := d') (c := c) h)).2 =
        decoLift c 1 (decoOf ((nativeLeafIface E n).typed h).2) :=
  decoOf_hasTyTWeaken d' hcl h.hq

/-- Context transport preserves all three canonical native leaf typings. -/
def proofLeaf_ctx (hcl : EnvClosed E) {Γ Γ' : LCtx}
    (hcc : CtxConvT E n Γ Γ') {p q T : Expr Nat}
    (h : ProofLeaf E n Γ p q T) : ProofLeaf E n Γ' p q T :=
  ⟨hasTyT_ctx hcl hcc h.hT,
    hasTyT_ctx hcl hcc h.hp, hasTyT_ctx hcl hcc h.hq⟩

/-- Native context transport preserves the source decoration exactly. -/
theorem proofLeaf_ctx_source_deco (hcl : EnvClosed E) {Γ Γ' : LCtx}
    (hcc : CtxConvT E n Γ Γ') {p q T : Expr Nat}
    (h : ProofLeaf E n Γ p q T) :
    decoOf ((nativeLeafIface E n).typed (proofLeaf_ctx hcl hcc h)).1 =
      decoOf ((nativeLeafIface E n).typed h).1 :=
  decoOf_hasTyT_ctx hcl hcc h.hp

/-- Native context transport preserves the target decoration exactly. -/
theorem proofLeaf_ctx_target_deco (hcl : EnvClosed E) {Γ Γ' : LCtx}
    (hcc : CtxConvT E n Γ Γ') {p q T : Expr Nat}
    (h : ProofLeaf E n Γ p q T) :
    decoOf ((nativeLeafIface E n).typed (proofLeaf_ctx hcl hcc h)).2 =
      decoOf ((nativeLeafIface E n).typed h).2 :=
  decoOf_hasTyT_ctx hcl hcc h.hq

/-- The landed certified weakening bookkeeping specializes with no leaf-law
premise left over for the canonical native interface. -/
theorem native_cstep_lift_source_deco (d : LocalDecl) (hcl : EnvClosed E)
    {c : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {p : ParRedT (ProofLeaf E n) E n Γ a b T} (cp : Certified p) :
    stepDeco (nativeLeafIface E n)
      (cstep_lift d hcl (proofLeaf_lift hcl) (c := c) cp).step =
        decoLift c 1 (stepDeco (nativeLeafIface E n) p) :=
  stepDeco_cstep_lift (nativeLeafIface E n) d hcl
    (proofLeaf_lift hcl) (proofLeaf_lift_source_deco hcl) cp

/-- The landed abstract context-transport bookkeeping specializes with no
canonical native leaf-law premise left over. -/
theorem native_cstep_ctxTransport_source_deco
    {R : LCtx → LCtx → Type} (I : CtxTransport E n R) (hcl : EnvClosed E)
    {Γ Γ' : LCtx} (hcc : R Γ Γ') {a b T : Expr Nat}
    {p : ParRedT (ProofLeaf E n) E n Γ a b T} (cp : Certified p) :
    stepDeco (nativeLeafIface E n)
      (cstep_ctxTransport (PEq := ProofLeaf E n) I hcl
        (fun hc h => proofLeaf_ctx hcl (I.toCtx hc) h) hcc cp).step =
      stepDeco (nativeLeafIface E n) p :=
  stepDeco_cstep_ctxTransport (nativeLeafIface E n) I hcl
    (fun hc h => proofLeaf_ctx hcl (I.toCtx hc) h)
    (fun hc h => proofLeaf_ctx_source_deco hcl (I.toCtx hc) h) hcc cp

section ElementaryRows

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Swap the two input steps and the two legs of an actual coherent row. -/
def stepJoin_symm (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat} {p : CStep E n PEq Γ b d T}
    {q : CStep E n PEq Γ b e T} (j : DecoStarAudit.StepJoin L hΓ p q) :
    DecoStarAudit.StepJoin L hΓ q p where
  centre := j.centre
  left := j.right
  right := j.left
  leftSource := j.rightSource
  rightSource := j.leftSource
  target := j.target.symm

/-- The `refl × q` coherent row preserves the actual source and target
interfaces. The reflexive input's native certificate is arbitrary. -/
def stepJoin_refl_left (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (hb : HasTyT E n Γ b T) (cb : ConvT E n Γ b b T)
    (q : CStep E n PEq Γ b e T)
    (hsource : decoOf ((⟨.refl Γ b T hb, .refl cb⟩ :
        CStep E n PEq Γ b b T).leftTyped L hΓ) =
      decoOf (q.leftTyped L hΓ)) :
    DecoStarAudit.StepJoin L hΓ ⟨.refl Γ b T hb, .refl cb⟩ q where
  centre := e
  left := q
  right := ⟨.refl Γ e T (q.rightTyped L hΓ),
    .refl (.refl Γ e T (q.rightTyped L hΓ))⟩
  leftSource := hsource.symm
  rightSource := rfl
  target := rfl

/-- The symmetric `p × refl` coherent row, at the same common index. -/
def stepJoin_refl_right (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d T : Expr Nat}
    (p : CStep E n PEq Γ b d T)
    (hb : HasTyT E n Γ b T) (cb : ConvT E n Γ b b T)
    (hsource : decoOf (p.leftTyped L hΓ) =
      decoOf ((⟨.refl Γ b T hb, .refl cb⟩ :
        CStep E n PEq Γ b b T).leftTyped L hΓ)) :
    DecoStarAudit.StepJoin L hΓ p ⟨.refl Γ b T hb, .refl cb⟩ :=
  stepJoin_symm L hΓ (stepJoin_refl_left L hΓ hb cb p hsource.symm)

end ElementaryRows

/-- At a proposition index, join the two actual targets back at the original
source. The input source-decoration equation supplies the target equation;
the source interfaces follow from the canonical irrelevance roundtrips. -/
def stepJoin_of_prop {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat} (hT : HasTyT E n Γ T (.sort .zero))
    (p : CStep E n (ProofLeaf E n) Γ b d T)
    (q : CStep E n (ProofLeaf E n) Γ b e T)
    (hsource : decoOf (p.leftTyped (nativeLeafIface E n) hΓ) =
      decoOf (q.leftTyped (nativeLeafIface E n) hΓ)) :
    DecoStarAudit.StepJoin (nativeLeafIface E n) hΓ p q where
  centre := b
  left := CStep.irr (nativeLeafIface E n) hT
    (p.rightTyped (nativeLeafIface E n) hΓ)
    (p.leftTyped (nativeLeafIface E n) hΓ)
  right := CStep.irr (nativeLeafIface E n) hT
    (q.rightTyped (nativeLeafIface E n) hΓ)
    (q.leftTyped (nativeLeafIface E n) hΓ)
  leftSource := rfl
  rightSource := rfl
  target := hsource

/-- The canonical native `peq × q` row. The existing leaf supplies the
proposition sorting, and its input certificate is retained in the peak. -/
def stepJoin_peq_left {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat} (h : ProofLeaf E n Γ b d T)
    (c : ConvT E n Γ b d T)
    (q : CStep E n (ProofLeaf E n) Γ b e T)
    (hsource : decoOf ((⟨.peq Γ b d T h, .peq c⟩ :
        CStep E n (ProofLeaf E n) Γ b d T).leftTyped (nativeLeafIface E n) hΓ) =
      decoOf (q.leftTyped (nativeLeafIface E n) hΓ)) :
    DecoStarAudit.StepJoin (nativeLeafIface E n) hΓ
      ⟨.peq Γ b d T h, .peq c⟩ q :=
  stepJoin_of_prop hΓ h.hT ⟨.peq Γ b d T h, .peq c⟩ q hsource

/-- The symmetric canonical native `p × peq` row. -/
def stepJoin_peq_right {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (p : CStep E n (ProofLeaf E n) Γ b d T)
    (h : ProofLeaf E n Γ b e T) (c : ConvT E n Γ b e T)
    (hsource : decoOf (p.leftTyped (nativeLeafIface E n) hΓ) =
      decoOf ((⟨.peq Γ b e T h, .peq c⟩ :
        CStep E n (ProofLeaf E n) Γ b e T).leftTyped (nativeLeafIface E n) hΓ)) :
    DecoStarAudit.StepJoin (nativeLeafIface E n) hΓ p
      ⟨.peq Γ b e T h, .peq c⟩ :=
  stepJoin_symm (nativeLeafIface E n) hΓ
    (stepJoin_peq_left hΓ h c p hsource.symm)

end Rcic.Declarative.NativeValleys.CoherentCanonicalAudit
