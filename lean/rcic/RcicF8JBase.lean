import rcic.RcicF8EvParStar
import rcic.RcicF8EvInv
import rcic.RcicF8IrrOM

/-!
J1: the two approved ORIGINAL literal cases, refl and irr, over the SINGLE
landed Valley/EvParStar. Not a total JProcWf. Every Valley leaf is strictly
below the input cv literal, including both endpoints and terminal refl typings.
`DirectTiles` is evidence indexed by an EXISTING star, not a second carrier;
it certifies the untransported emitted spines used by these two terminal cases.
It has no val/leaves of its own. General transports and D remain owner work.
Environment/context front is explicit. No reconstruction is admitted into lit.
closure_claim=0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J1
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- A DTile for each emitted step, with exact removed atoms and materialization.
Refl has no emitted step. This certificate does not normalize or copy stars. -/
inductive DirectTiles (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) : {Γ : LCtx} → {a b T : Expr Nat} →
      EvParStar R Γ a b T → Type where
  | refl {Γ a T} (D : EvTy R Γ a T) : DirectTiles hcl hinst X (.refl D)
  | tail {Γ a b c T} {s : EvPar R Γ a b T} {ss : EvParStar R Γ b c T}
      (tile : DTile R) (removed : tile.X = X)
      (exactStep : HEq tile.step (s.val hcl hinst))
      (rest : DirectTiles hcl hinst X ss) : DirectTiles hcl hinst X (.tail s ss)

/-- The packet is a Valley plus proofs about its ACTUAL two stars. -/
structure Result (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T) where
  valley : Valley R Γ a b T
  leftTiles : DirectTiles (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) [Jd.cv h] valley.left
  rightTiles : DirectTiles (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) [Jd.cv h] valley.right
  strict : ∀ ℓ ∈ valley.leaves, SubOf ℓ (Jd.cv h)

section Refl
variable {Γ : LCtx} {a T : Expr Nat}

def reflEndpoint (ha : HasTyT E n Γ a T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.refl Γ a T ha)) r) : EvTy R Γ a T :=
  .lit ha (certOfChild (y := Jd.cv (.refl Γ a T ha)) (.head _) hsub)

def reflValley (ha : HasTyT E n Γ a T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.refl Γ a T ha)) r) : Valley R Γ a a T :=
  let d := reflEndpoint ha hsub
  ⟨a, .refl d, .refl d, d, d⟩

theorem reflValley_leaves (ha : HasTyT E n Γ a T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.refl Γ a T ha)) r) :
    (reflValley ha hsub).leaves = [Jd.ty ha, Jd.ty ha, Jd.ty ha, Jd.ty ha] := rfl

theorem reflValley_strict (ha : HasTyT E n Γ a T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.refl Γ a T ha)) r)
    (ℓ : Jd E n) (hℓ : ℓ ∈ (reflValley ha hsub).leaves) :
    SubOf ℓ (Jd.cv (.refl Γ a T ha)) := by
  rw [reflValley_leaves] at hℓ
  have heq : ℓ = Jd.ty ha := by simpa using hℓ
  subst ℓ
  exact .child (.head _)

theorem reflValley_left_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (ha : HasTyT E n Γ a T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.refl Γ a T ha)) r) :
    (reflValley ha hsub).left.val hcl hinst = ParRedTStar.refl Γ a T ha := rfl

def reflResult (hW : EnvWfT E) (ha : HasTyT E n Γ a T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.refl Γ a T ha)) r) :
    Result hW R (.refl Γ a T ha) where
  valley := reflValley ha hsub
  leftTiles := .refl (reflEndpoint ha hsub)
  rightTiles := .refl (reflEndpoint ha hsub)
  strict := reflValley_strict ha hsub
end Refl

section Irr
variable {Γ : LCtx} {P p q : Expr Nat}

def irrPayload (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    ProofIndexPayload R Γ p q P where
  proposition := P
  propTy := .lit hP (certOfChild (y := Jd.cv (.irr Γ P p q hP hp hq)) (.head _) hsub)
  chain := .refl Γ P
  leftTy := .lit hp (certOfChild (y := Jd.cv (.irr Γ P p q hP hp hq)) (.tail _ (.head _)) hsub)
  rightTy := .lit hq (certOfChild (y := Jd.cv (.irr Γ P p q hP hp hq)) (.tail _ (.tail _ (.head _))) hsub)

def irrStep (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    EvPar R Γ p q P := .proofIndex (irrPayload hP hp hq hsub)

theorem irrStep_leaves (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    (irrStep hP hp hq hsub).leaves = [Jd.ty hP, Jd.ty hp, Jd.ty hq] := rfl

theorem irrStep_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    (irrStep hP hp hq hsub).val hcl hinst =
      (literalIrrProducer hP hp hq).val hcl hinst := rfl

def irrValley (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) : Valley R Γ p q P :=
  let pl := irrPayload hP hp hq hsub
  ⟨q, .tail (irrStep hP hp hq hsub) (.refl pl.rightTy),
    .refl pl.rightTy, pl.leftTy, pl.rightTy⟩

theorem irrValley_leaves (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    (irrValley hP hp hq hsub).leaves =
      [Jd.ty hP, Jd.ty hp, Jd.ty hq, Jd.ty hq, Jd.ty hq, Jd.ty hp, Jd.ty hq] := rfl

theorem irrValley_strict (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r)
    (ℓ : Jd E n) (hℓ : ℓ ∈ (irrValley hP hp hq hsub).leaves) :
    SubOf ℓ (Jd.cv (.irr Γ P p q hP hp hq)) := by
  rw [irrValley_leaves] at hℓ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .child (.head _)
  · exact .child (.tail _ (.head _))
  · exact .child (.tail _ (.tail _ (.head _)))
  · exact .child (.tail _ (.tail _ (.head _)))
  · exact .child (.tail _ (.tail _ (.head _)))
  · exact .child (.tail _ (.head _))
  · exact .child (.tail _ (.tail _ (.head _)))

def irrTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) : DTile R where
  X := [Jd.cv (.irr Γ P p q hP hp hq)]
  step := (irrStep hP hp hq hsub).val hcl hinst
  status := statusOfAnswered (R := R)
    ((irrPayload hP hp hq hsub).requests hcl hinst)
    ((irrPayload hP hp hq hsub).answers hcl hinst)
  om2 := om2_of_answered [Jd.cv (.irr Γ P p q hP hp hq)]
    ((irrPayload hP hp hq hsub).requests hcl hinst)
    ((irrPayload hP hp hq hsub).answers hcl hinst)

theorem irrTile_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    (irrTile hcl hinst hP hp hq hsub).step =
      (literalIrrTile hcl hinst hP hp hq).step := rfl

theorem irrValley_left_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    (irrValley hP hp hq hsub).left.val hcl hinst =
      .tail (irrTile hcl hinst hP hp hq hsub).step (.refl Γ q P hq) := rfl

theorem irrValley_right_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    (irrValley hP hp hq hsub).right.val hcl hinst = .refl Γ q P hq := rfl

theorem irrAnswer_refl (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) (side : Side) :
    (irrPayload hP hp hq hsub).lazyAnswer side = EvTc.refl Γ P := rfl

def irrResult (hW : EnvWfT E) (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv (.irr Γ P p q hP hp hq)) r) :
    Result hW R (.irr Γ P p q hP hp hq) where
  valley := irrValley hP hp hq hsub
  leftTiles := .tail
    (irrTile (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hP hp hq hsub)
    rfl HEq.rfl (.refl (irrPayload hP hp hq hsub).rightTy)
  rightTiles := .refl (irrPayload hP hp hq hsub).rightTy
  strict := irrValley_strict hP hp hq hsub
end Irr

/-- Exact covered constructor domain; no attempt at unimplemented cases. -/
def isBase : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .refl .. => true
  | _, _, _, _, .irr .. => true
  | _, _, _, _, _ => false

/-- Accepted Wf front for ONLY the approved base cases. It is not JProcWf. -/
def dispatchWf (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → CtxWfT E n Γ →
    (h : ConvT E n Γ a b T) → (∃ r ∈ R, SubEq (Jd.cv h) r) →
    Option (Result hW R h)
  | _, _, _, _, _, .refl _ _ _ ha, hsub => some (reflResult hW ha hsub)
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hsub => some (irrResult hW hP hp hq hsub)
  | _, _, _, _, _, _, _ => none

theorem dispatchWf_coverage (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ a b T)
    (hsub : ∃ r ∈ R, SubEq (Jd.cv h) r) :
    (dispatchWf hW R hΓ h hsub).isSome = isBase h := by cases h <;> rfl

/-- ALL output leaves are below the original literal; Z is untouched. -/
theorem result_edge (hW : EnvWfT E) {Γ : LCtx} {a b T : Expr Nat}
    {h : ConvT E n Γ a b T} (out : Result hW R h) (Z : List (Jd E n)) :
    OM3_edge ([Jd.cv h] ++ Z) (out.valley.leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (fun ℓ hℓ => ⟨Jd.cv h, .head _, out.strict ℓ hℓ⟩)

end Rcic.Declarative.F8Measure.J1
