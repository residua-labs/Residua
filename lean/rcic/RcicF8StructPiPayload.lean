import rcic.RcicF8Ev

/-!
# RcicF8StructPiPayload — payload for the second EvPar constructor

The structural-Pi provenance payload (piRow O-M4, cc assignment on
`#6933`'s stack). A head-preserving `Π A B ⇒ Π A' B'` source step yields
components that are conversions at the LEFT sorts; the emitted judgment is the
canonical structural step `ParRedT.pi` at those components, re-indexed to the
original `T` by one `conv` wrapper. Every judgment field is B2 provenance over
the same root bundle `R`; materialized endpoints are never relabeled as `lit`.

Adapted with attribution from Devin desktop reference-only #7007 at
`791c16f39ab16f04931da594b3b3bfa69df17b9a`; not merged.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure
open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat}

/-- Provenance payload of `EvPar.structPi`: the domain typing and conversion at
    the left sort `u`, the codomain typing and conversion at `v` under the
    LEFT domain's context, the target `pi`'s typing at `sort (imax u v)` —
    reached lazily through the shared index `T` — and the index chain
    `sort (imax u v) ≡ T`. -/
structure StructPiPayload (R : List (Jd E n)) (Γ : LCtx)
    (A B A' B' T : Expr Nat) where
  u : Level
  v : Level
  hA : EvTy R Γ A (.sort u)
  hc : EvCv R Γ A A' (.sort u)
  hB : EvTy R (.assumption A :: Γ) B (.sort v)
  hcB : EvCv R (.assumption A :: Γ) B B' (.sort v)
  hrt : EvTy R Γ (.pi A' B') (.sort (.imax u v))
  idx : EvTc R Γ (.sort (.imax u v)) T

variable {R : List (Jd E n)} {Γ : LCtx} {A B A' B' T : Expr Nat}

def StructPiPayload.leaves (p : StructPiPayload R Γ A B A' B' T) :
    List (Jd E n) :=
  p.hA.leaves ++ p.hc.leaves ++ p.hB.leaves ++ p.hcB.leaves ++
    p.hrt.leaves ++ p.idx.leaves

def StructPiPayload.size (p : StructPiPayload R Γ A B A' B' T) : Nat :=
  1 + p.hA.size + p.hc.size + p.hB.size + p.hcB.size + p.hrt.size + p.idx.size

theorem StructPiPayload.leaves_root (p : StructPiPayload R Γ A B A' B' T)
    (x : Jd E n) (hx : x ∈ p.leaves) : ∃ r ∈ R, SubEq x r := by
  simp only [StructPiPayload.leaves] at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact p.hA.leaves_root x hx
          · exact p.hc.leaves_root x hx
        · exact p.hB.leaves_root x hx
      · exact p.hcB.leaves_root x hx
    · exact p.hrt.leaves_root x hx
  · exact p.idx.leaves_root x hx

/-- Only widen B2 inputs; never inject a materialized output as lit. -/
def StructPiPayload.widen {R' : List (Jd E n)}
    (hr : ∀ x ∈ R, x ∈ R') (p : StructPiPayload R Γ A B A' B' T) :
    StructPiPayload R' Γ A B A' B' T where
  u := p.u
  v := p.v
  hA := p.hA.widen hr
  hc := p.hc.widen hr
  hB := p.hB.widen hr
  hcB := p.hcB.widen hr
  hrt := p.hrt.widen hr
  idx := p.idx.widen hr

theorem StructPiPayload.leaves_widen {R' : List (Jd E n)}
    (hr : ∀ x ∈ R, x ∈ R') (p : StructPiPayload R Γ A B A' B' T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [StructPiPayload.widen, StructPiPayload.leaves,
    EvTy.leaves_widen, EvTc.leaves_widen, EvCv.leaves_widen]

/-- The plain producer whose output `EvPar.structPi` materializes to, EXACTLY:
    the canonical structural `ParRedT.pi` at the left-sort components, under one
    `conv` that re-indexes `sort (imax u v)` to the original `T`. -/
def structPiStep {Γ : LCtx} {A B A' B' T : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hc : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v))
    (hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v)))
    (idx : TyConvT E n Γ (.sort (.imax u v)) T) :
    ParRedT (PEqLeafT E n) E n Γ (.pi A B) (.pi A' B') T :=
  .conv Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) T
    (.pi Γ A A' B B' u v hA hc hB hcB hrt) idx

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.StructPiPayload
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.leaves
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.size
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.leaves_root
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.widen
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.leaves_widen
#print axioms Rcic.Declarative.F8Measure.structPiStep
