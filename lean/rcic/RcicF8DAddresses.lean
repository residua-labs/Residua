import rcic.RcicF8JTrans

/-!
G0 execution addressing for ChatGPT's #7160 generated-provenance specification
(PR #7203, §3). Positions select the existing spines and materialized stars.
The `toStar`/`spine` correspondence below is proved by recursion; no equality
between a wrapped `star1` step and its `read` is asserted. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.DAddresses
open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- A selected transported step, including its actual endpoints and object. -/
structure SpineStep (R : List (Jd E n)) (Γ : LCtx) (T : Expr Nat) where
  left : Expr Nat
  right : Expr Nat
  step : DStep R Γ left right T

/-- A selected materialized step, including its actual endpoints and object. -/
structure MaterialStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T : Expr Nat) where
  left : Expr Nat
  right : Expr Nat
  step : ParRedT (PEqLeafT E n) E n Γ left right T

/-- Reading is applied to the selected original DStep. -/
def SpineStep.read (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T : Expr Nat} (s : SpineStep R Γ T) : MaterialStep E n Γ T :=
  ⟨s.left, s.right, s.step.read.val hcl hinst⟩

/-- Closed addresses in an actual DSpine. Refl has no step address. -/
inductive SpinePos {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → DSpine R Γ T a b → Type where
  | head {a b c : Expr Nat} {s : DStep R Γ a b T} {rest : DSpine R Γ T b c} :
      SpinePos (.tail s rest)
  | tail {a b c : Expr Nat} {s : DStep R Γ a b T} {rest : DSpine R Γ T b c}
      (p : SpinePos rest) : SpinePos (.tail s rest)

def SpinePos.selected {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {hs : DSpine R Γ T a b} → SpinePos hs → SpineStep R Γ T
  | _, _, .tail s _, .head => ⟨_, _, s⟩
  | _, _, .tail _ _, .tail p => p.selected

abbrev SpinePos.left {Γ : LCtx} {T a b : Expr Nat} {hs : DSpine R Γ T a b}
    (p : SpinePos hs) : Expr Nat := p.selected.left
abbrev SpinePos.right {Γ : LCtx} {T a b : Expr Nat} {hs : DSpine R Γ T a b}
    (p : SpinePos hs) : Expr Nat := p.selected.right
abbrev SpinePos.step {Γ : LCtx} {T a b : Expr Nat} {hs : DSpine R Γ T a b}
    (p : SpinePos hs) : DStep R Γ p.left p.right T := p.selected.step

/-- Closed addresses in an actual materialized ParRedTStar. -/
inductive StarPos {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → ParRedTStar (PEqLeafT E n) E n Γ a b T → Type where
  | head {a b c : Expr Nat} {s : ParRedT (PEqLeafT E n) E n Γ a b T}
      {rest : ParRedTStar (PEqLeafT E n) E n Γ b c T} : StarPos (.tail s rest)
  | tail {a b c : Expr Nat} {s : ParRedT (PEqLeafT E n) E n Γ a b T}
      {rest : ParRedTStar (PEqLeafT E n) E n Γ b c T}
      (p : StarPos rest) : StarPos (.tail s rest)

def StarPos.selected {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} →
      StarPos ss → MaterialStep E n Γ T
  | _, _, .tail s _, .head => ⟨_, _, s⟩
  | _, _, .tail _ _, .tail p => p.selected

abbrev StarPos.left {Γ : LCtx} {T a b : Expr Nat}
    {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} (p : StarPos ss) : Expr Nat :=
  p.selected.left
abbrev StarPos.right {Γ : LCtx} {T a b : Expr Nat}
    {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} (p : StarPos ss) : Expr Nat :=
  p.selected.right
abbrev StarPos.step {Γ : LCtx} {T a b : Expr Nat}
    {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} (p : StarPos ss) :
    ParRedT (PEqLeafT E n) E n Γ p.left p.right T := p.selected.step

/-- The left append embedding follows the actual recursion of DSpine.append. -/
def SpinePos.appendLeft {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} → {xs : DSpine R Γ T a b} →
    (p : SpinePos xs) → (ys : DSpine R Γ T b c) → SpinePos (xs.append ys)
  | _, _, _, .tail _ _, .head, _ => .head
  | _, _, _, .tail _ _, .tail p, ys => .tail (p.appendLeft ys)

/-- The right append embedding traverses the actual left spine. -/
def SpinePos.appendRight {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} → (xs : DSpine R Γ T a b) →
    {ys : DSpine R Γ T b c} → SpinePos ys → SpinePos (xs.append ys)
  | _, _, _, .refl _, _, p => p
  | _, _, _, .tail _ rest, _, p => .tail (appendRight rest p)

theorem SpinePos.appendLeft_exact {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} → {xs : DSpine R Γ T a b} →
    (p : SpinePos xs) → (ys : DSpine R Γ T b c) →
      (p.appendLeft ys).selected = p.selected
  | _, _, _, .tail _ _, .head, _ => rfl
  | _, _, _, .tail _ _, .tail p, ys => p.appendLeft_exact ys

theorem SpinePos.appendRight_exact {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} → (xs : DSpine R Γ T a b) →
    {ys : DSpine R Γ T b c} → (p : SpinePos ys) →
      (appendRight xs p).selected = p.selected
  | _, _, _, .refl _, _, _ => rfl
  | _, _, _, .tail _ rest, _, p => appendRight_exact rest p

/-- The exact spine of star1 retains the original DStep wrappers. -/
theorem star1_spine_exact : {Γ : LCtx} → {a b T : Expr Nat} →
    (s : DStep R Γ a b T) → s.star1.spine = .tail s (.refl s.rightTy)
  | _, _, _, _, .base _ => rfl
  | _, _, _, _, .conv s c => by
      simp only [DStep.star1, EvParStar.spine, star1_spine_exact s,
        DSpine.conv, DStep.rightTy]
  | _, _, _, _, .wk d k s => by
      simp only [DStep.star1, EvParStar.spine, star1_spine_exact s,
        DSpine.wk, DStep.rightTy]
  | _, _, _, _, .subst0 j s hget hv => by
      simp only [DStep.star1, EvParStar.spine, star1_spine_exact s,
        DSpine.subst0, DStep.rightTy]
  | _, _, _, _, .substLet j s hget hv => by
      simp only [DStep.star1, EvParStar.spine, star1_spine_exact s,
        DSpine.substLet, DStep.rightTy]

/-- This roundtrip is proved from star1 and append, not assumed as input. -/
theorem toStar_spine_exact {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (hs : DSpine R Γ T a b) → hs.toStar.spine = hs
  | _, _, .refl _ => rfl
  | _, _, .tail s rest => by
      simp only [DSpine.toStar, EvParStar.spine, star1_spine_exact,
        DSpine.append, toStar_spine_exact rest]

def SpinePos.cast {Γ : LCtx} {T a b : Expr Nat} {xs ys : DSpine R Γ T a b}
    (h : xs = ys) (p : SpinePos xs) : SpinePos ys := h ▸ p

theorem SpinePos.cast_exact {Γ : LCtx} {T a b : Expr Nat}
    {xs ys : DSpine R Γ T a b} (h : xs = ys) (p : SpinePos xs) :
    (p.cast h).selected = p.selected := by
  cases h
  rfl

/-- Canonical address through the proved toStar/spine roundtrip. -/
def SpinePos.toStarSpine {Γ : LCtx} {T a b : Expr Nat}
    {hs : DSpine R Γ T a b} (p : SpinePos hs) : SpinePos hs.toStar.spine :=
  p.cast (toStar_spine_exact hs).symm

theorem SpinePos.toStarSpine_exact {Γ : LCtx} {T a b : Expr Nat}
    {hs : DSpine R Γ T a b} (p : SpinePos hs) :
    p.toStarSpine.selected = p.selected := p.cast_exact _

/-- Emit a read step at the same head/tail address in readSpine's actual val. -/
def SpinePos.readSpine (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {hs : DSpine R Γ T a b} → (p : SpinePos hs) →
      StarPos ((J5a.readSpine hs).val hcl hinst)
  | _, _, .tail _ _, .head => .head
  | _, _, .tail _ _, .tail p => .tail (p.readSpine hcl hinst)

theorem SpinePos.readSpine_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {hs : DSpine R Γ T a b} → (p : SpinePos hs) →
      (p.readSpine hcl hinst).selected = p.selected.read hcl hinst
  | _, _, .tail _ _, .head => rfl
  | _, _, .tail _ _, .tail p => p.readSpine_exact hcl hinst

/-- readOutput consumes positions of the actual star's derived spine. -/
def SpinePos.readOutput (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T a b : Expr Nat} {ss : EvParStar R Γ a b T}
    (p : SpinePos ss.spine) : StarPos ((J5a.readOutput ss).val hcl hinst) :=
  p.readSpine hcl hinst

theorem SpinePos.readOutput_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {T a b : Expr Nat}
    {ss : EvParStar R Γ a b T} (p : SpinePos ss.spine) :
    (p.readOutput hcl hinst).selected = p.selected.read hcl hinst :=
  p.readSpine_exact hcl hinst

/-- The full actual D output route: toStar, its spine, then readOutput. -/
def SpinePos.emit (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T a b : Expr Nat} {hs : DSpine R Γ T a b} (p : SpinePos hs) :
    StarPos ((J5a.readOutput hs.toStar).val hcl hinst) :=
  p.toStarSpine.readOutput hcl hinst

/-- Includes endpoints and the exact selected proof object, not just its type. -/
theorem emit_read_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T a b : Expr Nat} {hs : DSpine R Γ T a b} (p : SpinePos hs) :
    (p.emit hcl hinst).selected = p.selected.read hcl hinst := by
  exact (p.toStarSpine.readOutput_exact hcl hinst).trans
    (congrArg (fun s : SpineStep R Γ T => s.read hcl hinst) p.toStarSpine_exact)

/-- The left splice embedding follows parRedTStar_trans itself. -/
def StarPos.spliceLeft {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} →
    {xs : ParRedTStar (PEqLeafT E n) E n Γ a b T} → (p : StarPos xs) →
    (ys : ParRedTStar (PEqLeafT E n) E n Γ b c T) →
      StarPos (parRedTStar_trans xs ys)
  | _, _, _, .tail _ _, .head, _ => .head
  | _, _, _, .tail _ _, .tail p, ys => .tail (p.spliceLeft ys)

/-- The right splice embedding traverses the actual left materialized star. -/
def StarPos.spliceRight :
    {Γ : LCtx} → {T a b c : Expr Nat} →
    (xs : ParRedTStar (PEqLeafT E n) E n Γ a b T) →
    {ys : ParRedTStar (PEqLeafT E n) E n Γ b c T} → StarPos ys →
      StarPos (parRedTStar_trans xs ys)
  | _, _, _, _, _, .refl .., _, p => p
  | _, _, _, _, _, .tail _ rest, _, p => .tail (spliceRight rest p)

theorem StarPos.spliceLeft_exact {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} →
    {xs : ParRedTStar (PEqLeafT E n) E n Γ a b T} → (p : StarPos xs) →
    (ys : ParRedTStar (PEqLeafT E n) E n Γ b c T) →
      (p.spliceLeft ys).selected = p.selected
  | _, _, _, .tail _ _, .head, _ => rfl
  | _, _, _, .tail _ _, .tail p, ys => p.spliceLeft_exact ys

theorem StarPos.spliceRight_exact {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} → (xs : ParRedTStar (PEqLeafT E n) E n Γ a b T) →
    {ys : ParRedTStar (PEqLeafT E n) E n Γ b c T} → (p : StarPos ys) →
      (spliceRight xs p).selected = p.selected
  | _, _, _, .refl .., _, _ => by
      simp only [StarPos.spliceRight]
  | _, _, _, .tail _ rest, _, p => by
      simpa only [StarPos.spliceRight, StarPos.selected] using
        spliceRight_exact rest p


/-- Actual lazy conversion wrapper on a materialized selected step. -/
def MaterialStep.reindex {Γ : LCtx} {T U : Expr Nat}
    (s : MaterialStep E n Γ T) (tc : TyConvT E n Γ T U) :
    MaterialStep E n Γ U :=
  ⟨s.left, s.right, .conv Γ s.left s.right T U s.step tc⟩

/-- Conversion follows the existing parRedTStar_conv recursion. -/
def StarPos.reindex {Γ : LCtx} {T U : Expr Nat} (tc : TyConvT E n Γ T U) :
    {a b : Expr Nat} → {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} →
    StarPos ss → StarPos (parRedTStar_conv tc ss)
  | _, _, .tail _ _, .head => .head
  | _, _, .tail _ _, .tail p => .tail (p.reindex tc)

theorem StarPos.reindex_exact {Γ : LCtx} {T U : Expr Nat}
    (tc : TyConvT E n Γ T U) :
    {a b : Expr Nat} → {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} →
    (p : StarPos ss) → (p.reindex tc).selected = p.selected.reindex tc
  | _, _, .tail _ _, .head => rfl
  | _, _, .tail _ _, .tail p => p.reindex_exact tc

/-- Select the actual per-step certificate from the existing certificate family. -/
def StarPos.certificate {X : List (Jd E n)} {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} →
    (p : StarPos ss) → J3.Certified R X ss → J3.StepCertificate R X p.step
  | _, _, .tail _ _, .head, cert => cert.1
  | _, _, .tail _ _, .tail p, cert => p.certificate cert.2

/-- Equality of addresses preserves the dependent selected certificate. -/
theorem StarPos.certificate_heq {X : List (Jd E n)} {Γ : LCtx}
    {T a b : Expr Nat} {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T}
    {p q : StarPos ss} (h : p = q) (cert : J3.Certified R X ss) :
    HEq (p.certificate cert) (q.certificate cert) := by
  cases h
  rfl

/-- Reading selects exactly the owner's baseCertificate for the original read. -/
theorem SpinePos.readSpine_certificate_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (X : List (Jd E n))
    {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {hs : DSpine R Γ T a b} → (p : SpinePos hs) →
    HEq ((p.readSpine hcl hinst).certificate
      (J5a.readSpine_certified hcl hinst X hs))
      (J5a.baseCertificate hcl hinst X p.step.read)
  | _, _, .tail _ _, .head => HEq.rfl
  | _, _, .tail _ _, .tail p => p.readSpine_certificate_exact hcl hinst X


theorem SpinePos.readOutput_certificate_exact (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (X : List (Jd E n))
    {Γ : LCtx} {T a b : Expr Nat} {ss : EvParStar R Γ a b T}
    (p : SpinePos ss.spine) :
    HEq ((p.readOutput hcl hinst).certificate
      (J5a.readOutput_certified hcl hinst X ss))
      (J5a.baseCertificate hcl hinst X p.step.read) :=
  p.readSpine_certificate_exact hcl hinst X

/-- The certificate selected after splicing is the original left certificate. -/
theorem StarPos.spliceLeft_certificate_exact {X : List (Jd E n)}
    {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} →
    {xs : ParRedTStar (PEqLeafT E n) E n Γ a b T} → (p : StarPos xs) →
    (ys : ParRedTStar (PEqLeafT E n) E n Γ b c T) →
    (cx : J3.Certified R X xs) → (cy : J3.Certified R X ys) →
    HEq ((p.spliceLeft ys).certificate (J5a.certifiedSplice xs ys cx cy))
      (p.certificate cx)
  | _, _, _, .tail _ _, .head, _, _, _ => by
      simp only [StarPos.spliceLeft, J5a.certifiedSplice, StarPos.certificate] <;> rfl
  | _, _, _, .tail _ _, .tail p, ys, cx, cy => by
      simpa only [StarPos.spliceLeft, J5a.certifiedSplice, StarPos.certificate] using
        p.spliceLeft_certificate_exact ys cx.2 cy

/-- The certificate selected after splicing is the original right certificate. -/
theorem StarPos.spliceRight_certificate_exact {X : List (Jd E n)}
    {Γ : LCtx} {T : Expr Nat} :
    {a b c : Expr Nat} → (xs : ParRedTStar (PEqLeafT E n) E n Γ a b T) →
    {ys : ParRedTStar (PEqLeafT E n) E n Γ b c T} → (p : StarPos ys) →
    (cx : J3.Certified R X xs) → (cy : J3.Certified R X ys) →
    HEq ((spliceRight xs p).certificate (J5a.certifiedSplice xs ys cx cy))
      (p.certificate cy)
  | a, _, _, .refl _ _ _ h, _, p, _, cy => by
      have hp : spliceRight (.refl Γ a T h) p = p := by
        simp only [StarPos.spliceRight]
      simpa only [J5a.certifiedSplice] using StarPos.certificate_heq hp cy
  | _, _, _, .tail s rest, ys, p, cx, cy => by
      have hp : spliceRight (.tail s rest) p = .tail (spliceRight rest p) := by
        simp only [StarPos.spliceRight]
      refine HEq.trans
        (StarPos.certificate_heq hp (J5a.certifiedSplice (.tail s rest) ys cx cy)) ?_
      simpa only [J5a.certifiedSplice, StarPos.certificate] using
        spliceRight_certificate_exact rest p cx.2 cy

/-- Reindex selects the actual existing StepCertificate.reindex. -/
theorem StarPos.reindex_certificate_exact {X : List (Jd E n)}
    {Γ : LCtx} {T U : Expr Nat} (tc : TyConvT E n Γ T U) :
    {a b : Expr Nat} → {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} →
    (p : StarPos ss) → (cert : J3.Certified R X ss) →
    HEq ((p.reindex tc).certificate (J3.Certified.reindex tc ss cert))
      ((p.certificate cert).reindex tc)
  | _, _, .tail _ _, .head, _ => by
      simp only [StarPos.reindex, J3.Certified.reindex, StarPos.certificate] <;> rfl
  | _, _, .tail _ _, .tail p, cert => by
      simpa only [StarPos.reindex, J3.Certified.reindex, StarPos.certificate] using
        p.reindex_certificate_exact tc cert.2


/-- Packed equality gives equality of the selected proof objects, even at
    endpoints whose expressions are recorded in the package. -/
theorem MaterialStep.step_heq {Γ : LCtx} {T : Expr Nat}
    {s t : MaterialStep E n Γ T} (h : s = t) : HEq s.step t.step := by
  cases h
  rfl

theorem SpineStep.step_heq {Γ : LCtx} {T : Expr Nat}
    {s t : SpineStep R Γ T} (h : s = t) : HEq s.step t.step := by
  cases h
  rfl

theorem emit_read_step_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T a b : Expr Nat} {hs : DSpine R Γ T a b} (p : SpinePos hs) :
    HEq (p.emit hcl hinst).step (p.step.read.val hcl hinst) :=
  MaterialStep.step_heq (emit_read_exact hcl hinst p)

/-- Equality transport changes only the index of an already selected address. -/
def StarPos.cast {Γ : LCtx} {T a b : Expr Nat}
    {xs ys : ParRedTStar (PEqLeafT E n) E n Γ a b T}
    (h : xs = ys) (p : StarPos xs) : StarPos ys := h ▸ p

theorem StarPos.cast_exact {Γ : LCtx} {T a b : Expr Nat}
    {xs ys : ParRedTStar (PEqLeafT E n) E n Γ a b T}
    (h : xs = ys) (p : StarPos xs) : (p.cast h).selected = p.selected := by
  cases h
  rfl

/-- Every actual readSpine output address comes from its original spine address. -/
def StarPos.readSpineSource (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (hs : DSpine R Γ T a b) →
    StarPos ((J5a.readSpine hs).val hcl hinst) → SpinePos hs
  | _, _, .refl h, p => by
      change StarPos (.refl _ _ _ (h.val hcl hinst)) at p
      exact nomatch p
  | _, _, .tail s rest, p => by
      change StarPos (.tail (s.read.val hcl hinst)
        ((J5a.readSpine rest).val hcl hinst)) at p
      exact match p with
        | .head => .head
        | .tail q => .tail (readSpineSource hcl hinst rest q)

theorem SpinePos.readSpine_source (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {hs : DSpine R Γ T a b} → (p : SpinePos hs) →
    StarPos.readSpineSource hcl hinst hs (p.readSpine hcl hinst) = p
  | _, _, .tail _ _, .head => by
      simp only [SpinePos.readSpine, StarPos.readSpineSource] <;> rfl
  | _, _, .tail _ _, .tail p => by
      simpa only [SpinePos.readSpine, StarPos.readSpineSource] using
        congrArg SpinePos.tail (p.readSpine_source hcl hinst)

theorem StarPos.readSpineSource_emit (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → (hs : DSpine R Γ T a b) →
    (p : StarPos ((J5a.readSpine hs).val hcl hinst)) →
    (readSpineSource hcl hinst hs p).readSpine hcl hinst = p
  | _, _, .refl h, p => by
      change StarPos (.refl _ _ _ (h.val hcl hinst)) at p
      cases p
  | _, _, .tail s rest, p => by
      change StarPos (.tail (s.read.val hcl hinst)
        ((J5a.readSpine rest).val hcl hinst)) at p
      cases p with
      | head => simp only [StarPos.readSpineSource, SpinePos.readSpine]
      | tail q =>
          simpa only [StarPos.readSpineSource, SpinePos.readSpine] using
            congrArg StarPos.tail (readSpineSource_emit hcl hinst rest q)


/-- Caller lifting selects the actual recaller operation on this certificate. -/
theorem StarPos.recaller_certificate_exact {X Y : List (Jd E n)}
    (hXY : ∀ x ∈ X, ∃ y ∈ Y, SubEq x y) {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → {ss : ParRedTStar (PEqLeafT E n) E n Γ a b T} →
    (p : StarPos ss) → (cert : J3.Certified R X ss) →
    HEq (p.certificate (J3.Certified.recaller hXY ss cert))
      ((p.certificate cert).recaller hXY)
  | _, _, .tail _ _, .head, _ => by
      simp only [J3.Certified.recaller, StarPos.certificate] <;> rfl
  | _, _, .tail _ _, .tail p, cert => by
      simpa only [J3.Certified.recaller, StarPos.certificate] using
        p.recaller_certificate_exact hXY cert.2

end Rcic.Declarative.F8Measure.DAddresses

#print axioms Rcic.Declarative.F8Measure.DAddresses.star1_spine_exact
#print axioms Rcic.Declarative.F8Measure.DAddresses.toStar_spine_exact
#print axioms Rcic.Declarative.F8Measure.DAddresses.emit_read_exact
#print axioms Rcic.Declarative.F8Measure.DAddresses.StarPos.spliceLeft_exact
#print axioms Rcic.Declarative.F8Measure.DAddresses.StarPos.spliceRight_exact
