import rcic.RcicCtxConvT

/-!
# Context transport can repeatedly expand the same typing derivation

This pin uses the existing `HasTyT`, `CtxConvT`, and `hasTyT_ctx`.
The source and target contexts are literally equal.  Their context
conversion is built with `CtxConvT.assumption` and a reflexive `ConvT`
certificate, rather than with `CtxConvT.same`.

Transporting the variable typing adds a `HasTyT.conv` constructor.
Transporting again adds another copy of the same conversion certificate.
The resulting infinite sequence consists of distinct derivations of
the same judgment, and every transition is the actual `hasTyT_ctx`
function applied with that fixed context-conversion witness.

Consequently, no well-founded ranking can strictly decrease on every
nonidentity output of this transport operation.  In particular, a
transported typing cannot in general be described as a literal proper
subderivation of its input: the seed below is a `bvar` node with no
typing/conversion premises, whereas its image has a `conv` root.

This does not obstruct the already structural recursion *inside*
`hasTyT_ctx`/`convT_ctx`, or a measure on a larger metatheoretic proof's
actual recursive calls.  Such a measure must account for the consumed
caller obligation; it cannot obtain descent merely from the fact that
one argument was produced by context transport.
-/

namespace Rcic.Declarative

def ctxTransportPinCtx : LCtx := [.assumption (.sort .zero)]

/-- The pin's context is well formed in the empty environment. -/
def ctxTransportPinCtxWf : CtxWfT emptyEnv 0 ctxTransportPinCtx :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

abbrev CtxTransportPinTyping : Type :=
  HasTyT emptyEnv 0 ctxTransportPinCtx (.bvar 0) (.sort .zero)

private theorem ctxTransportPinClosed : EnvClosed emptyEnv := by
  intro r m h
  cases h

/-- A reflexive context conversion whose explicit conversion field
    causes the variable branch of `hasTyT_ctx` to insert a cast. -/
def ctxTransportPinSelfConv :
    CtxConvT emptyEnv 0 ctxTransportPinCtx ctxTransportPinCtx :=
  .assumption .nil (.sort [] .zero) (.sort [] .zero)
    (.refl [] (.sort .zero) (.sort (.succ .zero)) (.sort [] .zero))

def ctxTransportPinSeed : CtxTransportPinTyping :=
  .bvar ctxTransportPinCtx 0 (.sort .zero) rfl

/-- The exact local conversion inserted by the variable branch. -/
def ctxTransportPinCast :
    ConvT emptyEnv 0 ctxTransportPinCtx
      (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .symm ctxTransportPinCtx (.sort .zero) (.sort .zero) (.sort (.succ .zero))
    (.refl ctxTransportPinCtx (.sort .zero) (.sort (.succ .zero))
      (.sort ctxTransportPinCtx .zero))

def ctxTransportPinWrap (h : CtxTransportPinTyping) : CtxTransportPinTyping :=
  .conv ctxTransportPinCtx (.bvar 0) (.sort .zero) (.sort .zero) (.succ .zero)
    h ctxTransportPinCast

def ctxTransportPinApply (h : CtxTransportPinTyping) : CtxTransportPinTyping :=
  hasTyT_ctx ctxTransportPinClosed ctxTransportPinSelfConv h

/-- This is an equality about the original transport function, not
    about an independently implemented model of transport. -/
theorem pin_ctxTransport_adds_conv :
    hasTyT_ctx ctxTransportPinClosed ctxTransportPinSelfConv ctxTransportPinSeed =
      HasTyT.conv ctxTransportPinCtx (.bvar 0) (.sort .zero) (.sort .zero)
        (.succ .zero) ctxTransportPinSeed ctxTransportPinCast := rfl

private theorem ctxTransportPinApply_wrap (h : CtxTransportPinTyping) :
    ctxTransportPinApply (ctxTransportPinWrap h) =
      ctxTransportPinWrap (ctxTransportPinApply h) := rfl

def ctxTransportPinIter : Nat → CtxTransportPinTyping
  | 0 => ctxTransportPinSeed
  | k + 1 => ctxTransportPinWrap (ctxTransportPinIter k)

/-- Every link is one actual application of the fixed context transport. -/
theorem ctxTransportPinApply_iter (k : Nat) :
    ctxTransportPinApply (ctxTransportPinIter k) = ctxTransportPinIter (k + 1) := by
  induction k with
  | zero => exact pin_ctxTransport_adds_conv
  | succ k ih =>
      change ctxTransportPinApply (ctxTransportPinWrap (ctxTransportPinIter k)) =
        ctxTransportPinWrap (ctxTransportPinIter (k + 1))
      rw [ctxTransportPinApply_wrap, ih]

/-- Only the outer `conv` spine is observed; no copy of the full
    derivation-size function is needed for this pin. -/
private def outerConvDepth {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} : HasTyT E n Γ e A → Nat
  | .conv _ _ _ _ _ h _ => outerConvDepth h + 1
  | _ => 0

private theorem outerConvDepth_iter (k : Nat) :
    outerConvDepth (ctxTransportPinIter k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change outerConvDepth (ctxTransportPinIter k) + 1 = k + 1
      exact congrArg (fun n => n + 1) ih

theorem ctxTransportPinIter_ne (k : Nat) :
    ctxTransportPinIter (k + 1) ≠ ctxTransportPinIter k := by
  intro heq
  have hd := congrArg (fun h : CtxTransportPinTyping => outerConvDepth h) heq
  change outerConvDepth (ctxTransportPinIter (k + 1)) =
    outerConvDepth (ctxTransportPinIter k) at hd
  rw [outerConvDepth_iter, outerConvDepth_iter] at hd
  omega

/-- The transport is nonidentity at every point of the concrete chain. -/
theorem pin_ctxTransport_iter_nonidentity (k : Nat) :
    ctxTransportPinApply (ctxTransportPinIter k) ≠ ctxTransportPinIter k := by
  rw [ctxTransportPinApply_iter]
  exact ctxTransportPinIter_ne k

universe uRank

/-- Excludes a strictly decreasing ranking of transport *outputs*.
    It makes no assertion about the recursive-call graph of the
    transport implementation or of an outer U/X/P proof. -/
theorem no_ctxTransport_strict_wf_rank {α : Sort uRank} {r : α → α → Prop}
    (hw : WellFounded r) :
    ¬ ∃ rank : CtxTransportPinTyping → α,
      ∀ h : CtxTransportPinTyping, ctxTransportPinApply h ≠ h →
        r (rank (ctxTransportPinApply h)) (rank h) := by
  rintro ⟨rank, hstrict⟩
  have hstep (k : Nat) :
      r (rank (ctxTransportPinIter (k + 1))) (rank (ctxTransportPinIter k)) := by
    have hs := hstrict (ctxTransportPinIter k) (pin_ctxTransport_iter_nonidentity k)
    simpa only [ctxTransportPinApply_iter] using hs
  have impossible : ∀ a : α, Acc r a →
      ∀ k : Nat, rank (ctxTransportPinIter k) = a → False := by
    intro a ha
    induction ha with
    | intro a _ ih =>
        intro k heq
        apply ih (rank (ctxTransportPinIter (k + 1))) ?_ (k + 1) rfl
        rw [← heq]
        exact hstep k
  exact impossible _ (hw.apply (rank (ctxTransportPinIter 0))) 0 rfl

theorem no_ctxTransport_strict_nat_rank :
    ¬ ∃ rank : CtxTransportPinTyping → Nat,
      ∀ h : CtxTransportPinTyping, ctxTransportPinApply h ≠ h →
        rank (ctxTransportPinApply h) < rank h :=
  no_ctxTransport_strict_wf_rank Nat.lt_wfRel.wf

#print axioms ctxTransportPinCtxWf
#print axioms pin_ctxTransport_adds_conv
#print axioms ctxTransportPinApply_iter
#print axioms ctxTransportPinIter_ne
#print axioms pin_ctxTransport_iter_nonidentity
#print axioms no_ctxTransport_strict_wf_rank
#print axioms no_ctxTransport_strict_nat_rank

end Rcic.Declarative
