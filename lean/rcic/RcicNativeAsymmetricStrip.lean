import rcic.RcicNativeHereditaryPaths

/-!
Source pin: minustwo/residua 76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.
NEW CONDITIONAL DRAFT.
COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound].

The supplied AsymmetricTile is NOT constructed here. This file proves
only the abstract implication from that exact stronger local contract
to certified strip and star joins. It does not replace the contract by
local GoodValleys, and it supplies no NativeConvValleys value.

The first output leg of a tile may be an arbitrary GoodPath. The SECOND
leg must be zero or one actual certified Step. This is sufficient for
the same literal-tail recursion as F8 DTileBase.dStripAt. Quantification
is over ORDERED input peaks, so exchanging the inputs is a separate
required use of the contract. A counterexample in either ordering
invalidates a universal supplier.

No native certificates are inferred from output typings: each actual
Step already carries GoodStep, and append preserves those exact trees.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeAsymmetricStrip76

open NativeHereditaryPaths76

variable {E : ResolvedEnv} {n : Nat}

def edgeCount {Γ : LCtx} {T : Expr Nat} :
    {a b : Expr Nat} → GoodPath E n Γ T a b → Nat
  | _, _, .refl _ => 0
  | _, _, .tail _ _ rest => 1 + edgeCount rest

inductive GoodOpt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T : Expr Nat) :
    Expr Nat → Expr Nat → Type where
  | stay {a : Expr Nat} (ha : HasTyT E n Γ a T) : GoodOpt E n Γ T a a
  | step {a b : Expr Nat} (s : NativeHereditaryPaths76.Step E n Γ a b T) (gs : GoodStep s) :
      GoodOpt E n Γ T a b

def GoodOpt.toPath {Γ : LCtx} {T : Expr Nat} (hΓ : CtxWfT E n Γ) :
    {a b : Expr Nat} → GoodOpt E n Γ T a b → GoodPath E n Γ T a b
  | _, _, .stay ha => .refl ha
  | _, _, .step s gs => GoodPath.one s gs (parRedT_hasTy_right leafTy hΓ s)

structure AsymmetricJoin (Γ : LCtx) (b c T : Expr Nat) where
  centre : Expr Nat
  left : GoodPath E n Γ T b centre
  right : GoodOpt E n Γ T c centre

/-- Deliberately unsupplied local hypothesis. Its short side is always
the reduct of the SECOND input step, not whichever side is convenient. -/
abbrev AsymmetricTile (Γ : LCtx) (T : Expr Nat) : Type :=
  ∀ {a b c : Expr Nat}, (s : NativeHereditaryPaths76.Step E n Γ a b T) → GoodStep s →
    (t : NativeHereditaryPaths76.Step E n Γ a c T) → GoodStep t →
    AsymmetricJoin (E := E) (n := n) Γ b c T

/-- One actual certified Step against a finite certified path.
Recursive calls decrease the supplied path's literal edge count.
The arbitrary-length left output of S is only prepended; no recursive
call is made on it in this worker. -/
def strip {Γ : LCtx} {T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (S : AsymmetricTile (E := E) (n := n) Γ T) :
    {a b c : Expr Nat} → (s : NativeHereditaryPaths76.Step E n Γ a b T) → GoodStep s →
    (p : GoodPath E n Γ T a c) → GoodValley (E := E) (n := n) Γ b c T
  | _, b, _, s, gs, .refl _ =>
      let hb := parRedT_hasTy_right leafTy hΓ s
      ⟨b, .refl hb, GoodPath.one s gs hb⟩
  | _, _, _, s, gs, .tail t gt rest => by
      obtain ⟨d, left, right⟩ := S s gs t gt
      cases right with
      | stay hd =>
          exact ⟨_, left.append rest, .refl rest.rightTy⟩
      | step r gr =>
          let K := strip hΓ S r gr rest
          exact ⟨K.centre, left.append K.left, K.right⟩

/-- Two finite paths. The recursive star call decreases the ORIGINAL
left input tail. The newly generated J.left may be arbitrarily long,
but occurs only in the second parameter, which is not measured. -/
def star {Γ : LCtx} {T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (S : AsymmetricTile (E := E) (n := n) Γ T) :
    {a b c : Expr Nat} → (p : GoodPath E n Γ T a b) →
    (q : GoodPath E n Γ T a c) → GoodValley (E := E) (n := n) Γ b c T
  | _, _, c, .refl _, q => ⟨c, q, .refl q.rightTy⟩
  | _, _, _, .tail s gs rest, q =>
      let J := strip hΓ S s gs q
      let K := star hΓ S rest J.left
      ⟨K.centre, K.left, J.right.append K.right⟩

end Rcic.Declarative.NativeAsymmetricStrip76
