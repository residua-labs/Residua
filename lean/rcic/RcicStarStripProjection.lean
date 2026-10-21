import rcic.RcicCoherentCanonical
import rcic.RcicNativeValleyDecoTransfer

/-!
# The exact canonical proof-leaf boundary of Π-head projection

The public `Rcic.Declarative.ProofLeaf` stores the three premises of
`ConvT.irr`. A Π-shaped source is not excluded by that carrier's
definition. If a Π were a proof of `P`, the identity application
`(λ x : P, x) (Π A, B)` would be an application-shaped proof of the
same `P`; the actual public canonical leaf can connect the two.

Consequently preservation of Π heads by all canonical proof leaves is
equivalent to the absence of Π-shaped proofs. The same equivalence holds
for the actual certified step carrier. The reverse implication reuses
the published `parRedT_pi_inv_of_leaf`, including every existing parallel
constructor; no new reduction, equivalence, or valley carrier is defined.

These are constructive necessity and equivalence statements. They do not
assert an admitted Π-proof counterexample, construct the no-proof side,
or supply `StarStrip`. No sort uniqueness, type uniqueness, Π row,
retyping, diamond, or choice principle is used. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentStarStripProjectionAudit

variable {E : ResolvedEnv} {n : Nat}

/-- Applying the identity at an actually sorted type preserves its typing.
The syntax has an application root regardless of the argument's root. -/
def identityAppTyped {Γ : LCtx} {p P : Expr Nat} {u : Level}
    (hP : HasTyT E n Γ P (.sort u)) (hp : HasTyT E n Γ p P) :
    HasTyT E n Γ (.app (.lam P (.bvar 0)) p) P := by
  have hx : HasTyT E n (.assumption P :: Γ) (.bvar 0) (lift 0 1 P) :=
    .bvar (.assumption P :: Γ) 0 (lift 0 1 P) rfl
  have hi : HasTyT E n Γ (.lam P (.bvar 0)) (.pi P (lift 0 1 P)) :=
    .lam Γ P u (.bvar 0) (lift 0 1 P) hP hx
  simpa only [instantiate0, instantiate_lift_id] using
    (HasTyT.app Γ (.lam P (.bvar 0)) p P (lift 0 1 P) hi hp)

/-- The original public leaf connects every proof to this application-rooted
proof at the same proposition, with the original source typing retained. -/
def proofLeaf_identityApp {Γ : LCtx} {p P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P) :
    Rcic.Declarative.ProofLeaf E n Γ p (.app (.lam P (.bvar 0)) p) P :=
  ⟨hP, hp, identityAppTyped hP hp⟩

/-- Π-head preservation of the actual canonical proof leaves is exactly a
no-Π-proof property, even before imposing environment/context admission. -/
theorem proofLeaf_pi_head_iff {Γ : LCtx} {A B : Expr Nat} :
    (∀ {q P : Expr Nat}, Rcic.Declarative.ProofLeaf E n Γ (.pi A B) q P →
      ∃ A' B' : Expr Nat, q = .pi A' B') ↔
    ¬ F8A2Support.IsProof E n Γ (.pi A B) := by
  constructor
  · intro hhead hproof
    obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := hproof
    obtain ⟨A', B', heq⟩ := hhead (proofLeaf_identityApp hP hp)
    cases heq
  · intro hn q P h
    exact (hn ⟨P, ⟨h.hT⟩, ⟨h.hp⟩⟩).elim

/-- Restricting to certified canonical steps does not avoid that boundary:
the necessity direction uses one actual `CStep.irr`, and sufficiency
specializes the existing full parallel-step projection. -/
theorem canonical_cstep_pi_head_iff {Γ : LCtx} :
    (∀ {A B q T : Expr Nat},
      CStep E n (Rcic.Declarative.ProofLeaf E n) Γ (.pi A B) q T →
        ∃ A' B' : Expr Nat, q = .pi A' B') ↔
    (∀ A B : Expr Nat, ¬ F8A2Support.IsProof E n Γ (.pi A B)) := by
  constructor
  · intro hhead A B
    apply proofLeaf_pi_head_iff.mp
    intro q P h
    exact hhead (CStep.irr (CoherentCanonicalAudit.nativeLeafIface E n) h.hT h.hp h.hq)
  · intro hn A B q T s
    obtain ⟨A', B', heq, _, _⟩ := parRedT_pi_inv_of_leaf
      (fun {A₀ B₀ q₀ T₀} (h : Rcic.Declarative.ProofLeaf E n Γ (.pi A₀ B₀) q₀ T₀) =>
        (hn A₀ B₀ ⟨T₀, ⟨h.hT⟩, ⟨h.hp⟩⟩).elim) s.step rfl
    exact ⟨A', B', heq⟩

#print axioms identityAppTyped
#print axioms proofLeaf_identityApp
#print axioms proofLeaf_pi_head_iff
#print axioms canonical_cstep_pi_head_iff

end Rcic.Declarative.NativeValleys.CoherentStarStripProjectionAudit
