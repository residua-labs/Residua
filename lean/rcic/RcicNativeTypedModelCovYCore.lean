import rcic.RcicNativeTypedModelCovYMeasure
import rcic.RcicNativeTypedModelCovXActions

/-!
# Extensional actions indexed by a finite semantic type code

Only the LAST argument of `LRSCoreCovY`, the compact type code, is the
recursive measure. Its Pi clause recurses to the domain code and an actual
selected row's codomain code, using the separately checked measure module.
Neither native type syntax nor the compact of the related terms decreases.

Every non-bottom compact action on a typed demand list must have an actual
compatible, output-typed row. The relation requires behavior at EVERY such row. Existence and
universal behavior are separate conjuncts; an uncovered action is not ignored.
This policy is stronger than merely choosing an existential row differently
for each relation edge. It is measured separately, never inferred from C.ty.

Bottom observations need no native view. Other non-Pi code leaves compose the
landed relation; their universe payload is explicitly retained, including its
old internal recursion. This module does not claim to replace that payload.
No global native type tree or existential code-coherence theorem is assumed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovNormReadbackAudit TypedModelCovXAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Compatibility uses the actual finite-demand observation, including its
automatic bottom observation. Codomain typing is independent of endpoints. -/
def CovYSelectedRow (C : CovTyping E) (ds : List CptT) (out : CptT)
    (row : List CptT × CptT) : Prop :=
  (∀ u ∈ row.1, u = .bot ∨ u ∈ ds) ∧ C.ty out row.2

/-- Genuine coverage of every non-bottom action by a row of this type code.
This is an additional semantic fact, not a consequence claimed for C.ty. -/
def CovYActionCoverage (C : CovTyping E) (c d : CptT)
    (g : List (List CptT × CptT)) : Prop :=
  ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out →
    (∀ u ∈ ds, C.ty u d) →
    out = .bot ∨ ∃ row ∈ g, CovYSelectedRow C ds out row

/-- The recursive relation, indexed by the compact TYPE code a. Both native
codomain instances are retained. There is no same-head test at a Pi code. -/
def LRSCoreCovY (C : CovTyping E) (R : Readback) (n : Nat) (Γ : LCtx)
    (x y A : Expr Nat) (c a : CptT) : Prop :=
  C.ty c a ∧
  match a with
  | .bot => True
  | .pi d g =>
      c = .bot ∨ ∃ D B : Expr Nat, RedR R Γ A (.pi D B) ∧
        CovYActionCoverage C c d g ∧
        ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out →
        ∀ (row : List CptT × CptT), row ∈ g → CovYSelectedRow C ds out row →
        ∀ (N N' : Expr Nat), HasTyT E n Γ N D → HasTyT E n Γ N' D →
        Nonempty (ConvT E n Γ N N' D) →
        (∀ u ∈ ds, LRSCoreCovY C R n Γ N N' D u d) →
          LRSCoreCovY C R n Γ (.app x N) (.app y N') (instantiate0 N B) out row.2 ∧
          LRSCoreCovY C R n Γ (.app x N) (.app y N') (instantiate0 N' B) out row.2
  | _ => LRSCoreCov C R n Γ x y A c
termination_by sizeOf a
decreasing_by
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt ‹row ∈ g›

theorem lrSCoreCovY_typing (C : CovTyping E) {Γ : LCtx} {x y A : Expr Nat}
    {c a : CptT} (h : LRSCoreCovY C R n Γ x y A c a) : C.ty c a := by
  rw [LRSCoreCovY.eq_def] at h
  exact h.1

theorem lrSCoreCovY_bot (C : CovTyping E) (Γ : LCtx) (x y A : Expr Nat) (a : CptT) :
    LRSCoreCovY C R n Γ x y A .bot a := by
  rw [LRSCoreCovY.eq_def]
  refine ⟨C.bot a, ?_⟩
  cases a with
  | bot => trivial
  | pi d g => exact Or.inl rfl
  | prop => exact lrSCoreCov_bot C _ _ _ _
  | sort => exact lrSCoreCov_bot C _ _ _ _
  | lam g => exact lrSCoreCov_bot C _ _ _ _
  | spine r args => exact lrSCoreCov_bot C _ _ _ _

/-- Local composition at a non-Pi type code. The old payload is not identified
with an extensional Pi interpretation by this theorem. -/
theorem lrSCoreCovY_of_old_leaf (C : CovTyping E)
    {Γ : LCtx} {x y A : Expr Nat} {c a : CptT}
    (hnot : ∀ d g, a ≠ .pi d g) (ht : C.ty c a)
    (h : LRSCoreCov C R n Γ x y A c) : LRSCoreCovY C R n Γ x y A c a := by
  rw [LRSCoreCovY.eq_def]
  refine ⟨ht, ?_⟩
  cases a with
  | bot => trivial
  | pi d g => exact (hnot d g rfl).elim
  | prop => exact h
  | sort => exact h
  | lam g => exact h
  | spine r args => exact h

theorem lrSCoreCovY_pi_iff (C : CovTyping E) (Γ : LCtx) (x y A : Expr Nat)
    (c d : CptT) (g : List (List CptT × CptT)) :
    LRSCoreCovY C R n Γ x y A c (.pi d g) ↔
      C.ty c (.pi d g) ∧
      (c = .bot ∨ ∃ D B : Expr Nat, RedR R Γ A (.pi D B) ∧
        CovYActionCoverage C c d g ∧
        ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out →
        ∀ (row : List CptT × CptT), row ∈ g → CovYSelectedRow C ds out row →
        ∀ (N N' : Expr Nat), HasTyT E n Γ N D → HasTyT E n Γ N' D →
        Nonempty (ConvT E n Γ N N' D) →
        (∀ u ∈ ds, LRSCoreCovY C R n Γ N N' D u d) →
          LRSCoreCovY C R n Γ (.app x N) (.app y N') (instantiate0 N B) out row.2 ∧
          LRSCoreCovY C R n Γ (.app x N) (.app y N') (instantiate0 N' B) out row.2) := by
  rw [LRSCoreCovY.eq_def]

/-- With a displayed native Pi type, every related non-bottom edge supplies
its coverage and both codomain relations at every selected row. -/
theorem lrSCoreCovY_pi_action (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x y D B : Expr Nat} {c d out : CptT}
    {g : List (List CptT × CptT)} {ds : List CptT}
    (h : LRSCoreCovY C R n Γ x y (.pi D B) c (.pi d g))
    (ha : CovXCompactAction E c ds out)
    {row : List CptT × CptT} (hr : row ∈ g) (hsel : CovYSelectedRow C ds out row)
    (N N' : Expr Nat) (hN : HasTyT E n Γ N D) (hN' : HasTyT E n Γ N' D)
    (hc : Nonempty (ConvT E n Γ N N' D))
    (hd : ∀ u ∈ ds, LRSCoreCovY C R n Γ N N' D u d) :
    LRSCoreCovY C R n Γ (.app x N) (.app y N') (instantiate0 N B) out row.2 ∧
    LRSCoreCovY C R n Γ (.app x N) (.app y N') (instantiate0 N' B) out row.2 := by
  rw [lrSCoreCovY_pi_iff] at h
  rcases h.2 with rfl | ⟨D', B', hread, hcover, hact⟩
  · cases ha with
    | bot => exact ⟨lrSCoreCovY_bot C _ _ _ _ _, lrSCoreCovY_bot C _ _ _ _ _⟩
  · have he := redR_of_normal (hL.pi_normal Γ D B) hread
    obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
    exact hact ds out ha row hr hsel N N' hN hN' hc hd

theorem lrSCoreCovY_pi_coverage (C : CovTyping E)
    {Γ : LCtx} {x y A : Expr Nat} {c d : CptT} {g : List (List CptT × CptT)}
    (h : LRSCoreCovY C R n Γ x y A c (.pi d g)) : CovYActionCoverage C c d g := by
  rw [lrSCoreCovY_pi_iff] at h
  rcases h.2 with rfl | ⟨D, B, hr, hc, ha⟩
  · intro ds out ha hd
    cases ha with
    | bot => exact Or.inl rfl
  · exact hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_CORE_ROOTS
#print axioms CovYSelectedRow
#print axioms CovYActionCoverage
#print axioms LRSCoreCovY
#print axioms lrSCoreCovY_typing
#print axioms lrSCoreCovY_bot
#print axioms lrSCoreCovY_of_old_leaf
#print axioms lrSCoreCovY_pi_iff
#print axioms lrSCoreCovY_pi_action
#print axioms lrSCoreCovY_pi_coverage
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
