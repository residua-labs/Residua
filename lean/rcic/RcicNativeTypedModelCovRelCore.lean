import rcic.RcicNativeTypedModelCovRelBoundary

/-!
# A typing-parametric recursive covariant relation

`CovTyping` records precisely the compact-shape information used by the PER
argument. Its Pi branch selects one covering row, including that row's output
typing. An additional rigid-spine alternative permits a later typing extension
to admit functions represented by rigid spines. No old relation or model escape
principle is a field of this interface.

`LRSCoreCov` is recursive at every demand and output occurrence. Its Pi gate uses
the supplied typing. The imported sort and spine clauses are composed directly.
The model is deliberately absent: model realization belongs to a separate
interface, and cannot be recovered from this relation alone.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- The lambda alternative of compact Pi typing needs a single typed covering
row for each non-bottom result. -/
def CovLamTyping (T : CptT → CptT → Prop) (a : CptT)
    (g f : List (List CptT × CptT)) : Prop :=
  (∀ s ∈ f, ∀ v ∈ s.1, T v a) ∧
  ∀ s ∈ f, s.2 = .bot ∨ ∃ t ∈ g, (∀ v ∈ t.1, v ∈ s.1) ∧ T s.2 t.2

/-- Compact typing laws required by the new recursive PER. In particular,
the Pi inversion permits a rigid spine without pretending it is a lambda. -/
structure CovTyping (E : ResolvedEnv) where
  ty : CptT → CptT → Prop
  bot : ∀ a, ty .bot a
  bot_inv : ∀ {u}, ty u .bot → u = .bot
  prop_inv : ∀ {u}, ty u .prop → u = .bot ∨ IsPropCT E u
  sort_inv : ∀ {u}, ty u .sort → u = .bot ∨ TyCodeCT u
  lam_inv : ∀ {u g}, ty u (.lam g) → u = .bot
  spine_inv : ∀ {u r args}, ty u (.spine r args) →
    u = .bot ∨ ∃ r' args', u = .spine r' args'
  pi_inv : ∀ {u a g}, ty u (.pi a g) →
    u = .bot ∨ (∃ f, u = .lam f ∧ CovLamTyping ty a g f) ∨
      ∃ r args, u = .spine r args
  prop_bot : ∀ {a u}, IsPropCT E a → ty u a → u = .bot

/-- The imported covariant typing implements the parametric interface.
It never uses the extra rigid-spine Pi alternative. -/
def covTypingCTyCov (E : ResolvedEnv) : CovTyping E where
  ty := CTyCov E
  bot := ctyCov_bot
  bot_inv := ctyCov_bot_inv
  prop_inv := ctyCov_prop_inv
  sort_inv := ctyCov_sort_inv
  lam_inv := ctyCov_lam_inv
  spine_inv := by
    intro u r args h
    rcases ctyCov_spine_inv h with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  pi_inv := by
    intro u a g h
    rcases ctyCov_pi_inv h with h | ⟨f, huf, _, hd, hc⟩
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨f, huf, hd, ?_⟩)
      intro s hs
      rcases hc s hs with hb | ⟨t, ht, hsub, hout⟩
      · exact Or.inl hb
      · exact Or.inr ⟨t, ht, hsub, hout⟩
  prop_bot := ctyCov_prop_bot

/-- Optional one-way inclusion for model constructors whose demand typing is
still `CTyS`. The PER interface itself needs no reference to that typing. -/
def CovTypingIncludesS (C : CovTyping E) : Prop :=
  ∀ a u, CTyS E u a → C.ty u a

theorem covTypingCTyCov_includesS (E : ResolvedEnv) :
    CovTypingIncludesS (covTypingCTyCov E) :=
  ctyCov_of_ctyS

/-- The new core. Every occurrence under Pi and lambda is recursive, and the
Pi demand gate is the supplied compact typing. -/
def LRSCoreCov (C : CovTyping E) (R : Readback) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) : CptT → Prop
  | .bot => True
  | .prop => SortClauseT R Γ M M' A
  | .sort => SortClauseT R Γ M M' A
  | .pi a f => (∃ l, RedR R Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ : Expr Nat,
        RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        (∃ w, LRSCoreCov C R n Γ A₁ A₂ (.sort w) a) ∧
        ∀ s ∈ f, (∀ u ∈ s.1, C.ty u a) →
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) →
          (∀ u ∈ s.1, LRSCoreCov C R n Γ N N' A₁ u) →
          ∃ v, LRSCoreCov C R n Γ (instantiate0 N B₁)
            (instantiate0 N' B₂) (.sort v) s.2
  | .lam f =>
      ∃ A₁ B₁ : Expr Nat, RedR R Γ A (.pi A₁ B₁) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ f, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) →
          (∀ u ∈ s.1, LRSCoreCov C R n Γ N N' A₁ u) →
          LRSCoreCov C R n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
  | .spine r args => SpineClauseS R E n Γ M M' A r args
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have := sizeOfT_fst_lt s
       omega)
    | (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have := sizeOfT_snd_lt s
       omega)

/-- Top-level proposition collapse, separated from the recursive core. -/
def LRSCov (C : CovTyping E) (R : Readback) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) (c : CptT) : Prop :=
  IsPropTyR R E n Γ A ∨ LRSCoreCov C R n Γ M M' A c

theorem lrSCoreCov_bot (C : CovTyping E) (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreCov C R n Γ M M' A .bot := by
  rw [LRSCoreCov.eq_def]
  trivial

theorem lrSCoreCov_prop_iff (C : CovTyping E) (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreCov C R n Γ M M' A .prop ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreCov.eq_def]

theorem lrSCoreCov_sort_iff (C : CovTyping E) (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreCov C R n Γ M M' A .sort ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreCov.eq_def]

theorem lrSCoreCov_prop_iff_sort (C : CovTyping E) (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreCov C R n Γ M M' A .prop ↔ LRSCoreCov C R n Γ M M' A .sort :=
  (lrSCoreCov_prop_iff C Γ M M' A).trans (lrSCoreCov_sort_iff C Γ M M' A).symm

theorem lrSCoreCov_spine_iff (C : CovTyping E) (Γ : LCtx) (M M' A : Expr Nat)
    (r : Nat) (args : List CptT) :
    LRSCoreCov C R n Γ M M' A (.spine r args) ↔
      SpineClauseS R E n Γ M M' A r args := by
  rw [LRSCoreCov.eq_def]

/-- As in the imported clauses, only the fact of being a sort index matters. -/
theorem lrSCoreCov_sortIdx_irrel (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {x y A B : Expr Nat}
    (hA : ∃ l, RedR R Γ A (.sort l)) (hB : ∃ l, RedR R Γ B (.sort l))
    (c : CptT) (h : LRSCoreCov C R n Γ x y A c) :
    LRSCoreCov C R n Γ x y B c := by
  cases c with
  | bot => exact lrSCoreCov_bot C _ _ _ _
  | prop =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact ⟨hB, h.2⟩
  | sort =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact ⟨hB, h.2⟩
  | pi a f =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact ⟨hB, h.2⟩
  | lam f =>
      rw [LRSCoreCov.eq_def] at h
      obtain ⟨D, F, hp, _⟩ := h
      obtain ⟨l, hs⟩ := hA
      exact (not_redR_pi_of_redR_sort hL hNU hs D F hp).elim
  | spine r args =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact spineClauseS_idx (fun _ => hB) (fun _ => hA) h

/-- A rigid-spine term at a Pi-coded type transports because both type
endpoints read back to Pis and hence neither can read back to a sort. -/
theorem lrSCoreCov_spine_irrel_pi (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {A B x y : Expr Nat}
    {a : CptT} {g : List (List CptT × CptT)} {w : Level}
    {r : Nat} {args : List CptT}
    (hAB : LRSCoreCov C R n Γ A B (.sort w) (.pi a g))
    (h : LRSCoreCov C R n Γ x y A (.spine r args)) :
    LRSCoreCov C R n Γ x y B (.spine r args) := by
  rw [LRSCoreCov.eq_def] at hAB
  obtain ⟨_, D, F, D', F', hA, hB, _⟩ := hAB
  rw [LRSCoreCov.eq_def] at h ⊢
  apply spineClauseS_idx (h := h)
  · rintro ⟨l, hs⟩
    exact (not_redR_pi_of_redR_sort hL hNU hs D F hA).elim
  · rintro ⟨l, hs⟩
    exact (not_redR_pi_of_redR_sort hL hNU hs D' F' hB).elim

def IrrelAtCov (C : CovTyping E) (R : Readback) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {w : Level},
    LRSCoreCov C R n Γ A B (.sort w) a → C.ty u a →
    ∀ {x y : Expr Nat}, LRSCoreCov C R n Γ x y A u → LRSCoreCov C R n Γ x y B u

def SymmTmAtCov (C : CovTyping E) (R : Readback) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreCov C R n Γ A A (.sort w) a → C.ty u a →
    ∀ {x y : Expr Nat}, LRSCoreCov C R n Γ x y A u → LRSCoreCov C R n Γ y x A u

def TransTmAtCov (C : CovTyping E) (R : Readback) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreCov C R n Γ A A (.sort w) a → C.ty u a →
    ∀ {x y z : Expr Nat}, LRSCoreCov C R n Γ x y A u →
      LRSCoreCov C R n Γ y z A u → LRSCoreCov C R n Γ x z A u

def SymmTyAtCov (C : CovTyping E) (R : Readback) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {w : Level},
    LRSCoreCov C R n Γ A B (.sort w) c → LRSCoreCov C R n Γ B A (.sort w) c

def TransTyAtCov (C : CovTyping E) (R : Readback) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B D : Expr Nat} {w : Level},
    LRSCoreCov C R n Γ A B (.sort w) c →
    LRSCoreCov C R n Γ B D (.sort w) c → LRSCoreCov C R n Γ A D (.sort w) c

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_CORE_ROOTS
#print axioms CovLamTyping
#print axioms CovTyping
#print axioms covTypingCTyCov
#print axioms CovTypingIncludesS
#print axioms covTypingCTyCov_includesS
#print axioms LRSCoreCov
#print axioms LRSCov
#print axioms lrSCoreCov_bot
#print axioms lrSCoreCov_prop_iff
#print axioms lrSCoreCov_sort_iff
#print axioms lrSCoreCov_prop_iff_sort
#print axioms lrSCoreCov_spine_iff
#print axioms lrSCoreCov_sortIdx_irrel
#print axioms lrSCoreCov_spine_irrel_pi
#print axioms IrrelAtCov
#print axioms SymmTmAtCov
#print axioms TransTmAtCov
#print axioms SymmTyAtCov
#print axioms TransTyAtCov
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
