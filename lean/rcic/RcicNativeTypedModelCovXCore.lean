import rcic.RcicNativeTypedModelCovNormReadback
import rcic.RcicNativeTypedModelCovRelPER
import rcic.RcicNativeTypedModelCovRelExpansion
import rcic.RcicNativeTypedModelIota

/-!
# Finite native type views and an extensional Pi experiment

The recursive measure is an explicit native type-view tree. In particular a
rigid compact may grow after application; its codomain view is nevertheless a
genuine recursive child. No theorem here asserts that every native type has
such a view, or selects a view globally.

Every Pi node uses application only. Both dependent codomain instances are
retained explicitly, so fixed-view symmetry needs no unproved native type
conversion transport. The compact gate is existential compact Pi typing;
it does not demand an observation of the raw source type.

The sort payload composes the old covariant type relation. Consequently this
is a measured repair of the explicit Pi nodes of a view, not a claim that
Pi occurrences inside that old universe payload have also been replaced.
`CovXUniverseCompatibility` below records optional preservation of that
payload; a future replacement may intentionally change its nested Pi clause.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovNormReadbackAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- A well-founded, explicitly supplied native type interpretation tree.
The binder and instantiated codomain views are separate children: no model
substitution principle is hidden in this datatype. -/
inductive CovXTypeView (E : ResolvedEnv) (R : Readback) (n : Nat) :
    LCtx → Expr Nat → Type
  | sort {Γ : LCtx} {A : Expr Nat} (l : Level)
      (read : RedR R Γ A (.sort l)) : CovXTypeView E R n Γ A
  | base {Γ : LCtx} {A : Expr Nat} (Z : Expr Nat)
      (read : RedR R Γ A Z) (normal : NormalR R Γ Z)
      (notSort : ¬ ∃ l, RedR R Γ A (.sort l))
      (notPi : ¬ ∃ D B, RedR R Γ A (.pi D B)) : CovXTypeView E R n Γ A
  | pi {Γ : LCtx} {A : Expr Nat} (D B : Expr Nat)
      (read : RedR R Γ A (.pi D B))
      (dom : CovXTypeView E R n Γ D)
      (body : CovXTypeView E R n (.assumption D :: Γ) B)
      (cod : ∀ N : Expr Nat, HasTyT E n Γ N D →
        CovXTypeView E R n Γ (instantiate0 N B)) : CovXTypeView E R n Γ A

/-- This gate refers to compact typing, never to an observation of the raw
type. Its actual CTyCov2 inhabitants are supplied by the concrete controls. -/
def CovXPiGate (C : CovTyping E) (c : CptT) : Prop :=
  ∃ a g, C.ty c (.pi a g)

/-- The existing compact application relation evaluated at a finite demand
environment. This is an abbreviation of the landed relation, not a new model
application constructor. Saturated ApproxTK computation is not included. -/
abbrev CovXCompactAction (E : ResolvedEnv) (c : CptT) (ds : List CptT)
    (out : CptT) : Prop :=
  AppCptT E (EnvT.cons (demandT ds) EnvT.bot) c (.bvar 0) out

/-- The explicitly view-indexed candidate. At every Pi view its term endpoints
are inspected only by application; no endpoint head or spine equality occurs.
The two codomain conjuncts are intentional and are not silently identified. -/
def LRSCoreCovXAt (C : CovTyping E) {Γ : LCtx} {A : Expr Nat}
    (view : CovXTypeView E R n Γ A) (x y : Expr Nat) (c : CptT) : Prop :=
  match view with
  | .sort l _ => C.ty c (sortCode l) ∧ LRSCoreCov C R n Γ x y A c
  | .base _ _ _ _ _ => LRSCoreCov C R n Γ x y A c
  | .pi D B _ dom _ cod =>
      CovXPiGate C c ∧
      ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out →
      ∀ (N N' : Expr Nat) (hN : HasTyT E n Γ N D) (hN' : HasTyT E n Γ N' D),
      Nonempty (ConvT E n Γ N N' D) →
      (∀ u ∈ ds, LRSCoreCovXAt C dom N N' u) →
        LRSCoreCovXAt C (cod N hN) (.app x N) (.app y N') out ∧
        LRSCoreCovXAt C (cod N' hN') (.app x N) (.app y N') out

/-- Optional agreement with the retained universe payload. It is not a
requirement on future replacements that repair the old nested Pi clause.
No such universal supplier is asserted in this experiment. -/
def CovXUniverseCompatibility (C : CovTyping E)
    (U : LCtx → Expr Nat → Expr Nat → Expr Nat → CptT → Prop) : Prop :=
  ∀ Γ A l, RedR R Γ A (.sort l) → ∀ x y c,
    U Γ x y A c ↔ C.ty c (sortCode l) ∧ LRSCoreCov C R n Γ x y A c

theorem covXPiGate_bot (C : CovTyping E) : CovXPiGate C .bot :=
  ⟨.bot, [], C.bot _⟩

/-- The old compact recursion measure increases in the rigid application arm. -/
theorem covX_spine_application_grows (r : Nat) (args : List CptT) (u : CptT) :
    sizeOf (CptT.spine r args) < sizeOf (CptT.spine r (args ++ [u])) := by
  induction args with
  | nil => simp; omega
  | cons a args ih => simp_all

theorem lrSCoreCovXAt_bot (C : CovTyping E) {Γ : LCtx} {A : Expr Nat}
    (view : CovXTypeView E R n Γ A) (x y : Expr Nat) :
    LRSCoreCovXAt C view x y .bot := by
  induction view generalizing x y with
  | sort l h => exact ⟨C.bot _, lrSCoreCov_bot C _ _ _ _⟩
  | base Z hr hn hs hp => exact lrSCoreCov_bot C _ _ _ _
  | pi D B hr dom body cod ihdom ihbody ihcod =>
      refine ⟨covXPiGate_bot C, ?_⟩
      intro ds out action N N' hN hN' hc hd
      cases action with
      | bot => exact ⟨ihcod N hN _ _, ihcod N' hN' _ _⟩

/-- Exact action extraction at the explicitly displayed Pi view. -/
theorem lrSCoreCovXAt_pi_action (C : CovTyping E) {Γ : LCtx} {A D B : Expr Nat}
    (read : RedR R Γ A (.pi D B)) (dom : CovXTypeView E R n Γ D)
    (body : CovXTypeView E R n (.assumption D :: Γ) B)
    (cod : ∀ N, HasTyT E n Γ N D → CovXTypeView E R n Γ (instantiate0 N B))
    {x y : Expr Nat} {c : CptT}
    (h : LRSCoreCovXAt C (.pi D B read dom body cod) x y c)
    {ds : List CptT} {out : CptT} (ha : CovXCompactAction E c ds out)
    (N N' : Expr Nat) (hN : HasTyT E n Γ N D) (hN' : HasTyT E n Γ N' D)
    (hc : Nonempty (ConvT E n Γ N N' D))
    (hd : ∀ u ∈ ds, LRSCoreCovXAt C dom N N' u) :
    LRSCoreCovXAt C (cod N hN) (.app x N) (.app y N') out ∧
      LRSCoreCovXAt C (cod N' hN') (.app x N) (.app y N') out :=
  h.2 ds out ha N N' hN hN' hc hd

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_CORE_ROOTS
#print axioms CovXTypeView
#print axioms CovXPiGate
#print axioms CovXCompactAction
#print axioms LRSCoreCovXAt
#print axioms CovXUniverseCompatibility
#print axioms covXPiGate_bot
#print axioms covX_spine_application_grows
#print axioms lrSCoreCovXAt_bot
#print axioms lrSCoreCovXAt_pi_action
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit
