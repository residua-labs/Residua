import rcic.RcicNativeTypedModelFundStrong

/-!
# RcicNativeTypedModelFundLit — FundCases fields `lit`, `litConv`, `sorts` (swe-fsub lane)

Three constructor cases of the fundamental lemma (`RcicNativeTypedModelFundStrong:297`),
each as a theorem whose conclusion is exactly the field's type.

* `sorts` — the sorts conversion.  `SortClauseT` (`RcicNativeTypedModelRel:68`) reads only the
  readback: a sort's compact is `.bot` or its universe code (`sort_inv`), and at either code the
  clause is met by reflexive readbacks — the `eqN` premise is not needed by the clause.
* `lit` — the literal node.  Two facts are consumed, stated exactly and shown satisfiable:
  `ModelLitInvT M` (the model's literal inversion — `ApproxT.lit` makes it definitional for the
  typed model, `approxT_lit_inv`) and `ReadbackLitStepT R` (the one-step literal expansion —
  `WhStepCtx.lit`, hence `WhStepCK` via `.ctx`, supplies it).  The IH runs on `hexp` — the
  expansion's typing is the constructor's OWN child — and the relation closes by readback
  expansion (`lrSCoreS_expand`, `lrSCoreS_expand_right`), never on a manufactured derivation.
* `litConv` — the literal-expansion conversion.  `LiteralExpansion` has the single constructor
  `of`, so `exp = natExpand t`; the right-hand compact is the expansion's, fed straight to the
  IH on `hexp`, and the left closes by one `lrSCoreS_expand` at the lit step.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §0 — the two consumed facts, stated exactly, with satisfiability witnesses -/

/-- **Model fact (`lit`)**: a compact approximating the literal node is `.bot` or approximates
    its expansion — the `CtxModelTLaws`-shaped inversion of `ApproxT.lit`. -/
def ModelLitInvT (M : CtxModelT E) : Prop :=
  ∀ {ρ : EnvT} {t : Nat} {c : CptT}, M.Ap ρ (.lit t) c → c = .bot ∨ M.Ap ρ (natExpand t) c

/-- **Readback fact (`lit`)**: the one-step expansion `.lit t → natExpand t`.  The abstract
    `ReadbackLaws` do not include it; the landed readbacks do. -/
def ReadbackLitStepT (R : Readback) : Prop :=
  ∀ (Γ : LCtx) (t : Nat), R Γ (.lit t) (natExpand t)

/-- `ApproxT` inversion at `.lit t`: only `.bot` and `.lit` constructors reach it. -/
theorem approxT_lit_inv {E : ResolvedEnv} {ρ : EnvT} {t : Nat} {c : CptT}
    (h : ApproxT E ρ (.lit t) c) : c = .bot ∨ ApproxT E ρ (natExpand t) c := by
  cases h with
  | bot => exact Or.inl rfl
  | lit h' => exact Or.inr h'

/-- `ModelLitInvT` holds for the typed model (`ApproxT`'s `lit` clause). -/
theorem modelLitInvT_approxT (E : ResolvedEnv) : ModelLitInvT (ctxModelT_approxT E) :=
  fun h => approxT_lit_inv h

/-- `ReadbackLitStepT` holds for `WhStepCtx` (its `lit` clause). -/
theorem readbackLitStepT_whStepCtx (E : ResolvedEnv) : ReadbackLitStepT (WhStepCtx E) :=
  fun _ t => .lit t

/-! ### §1 — the three fields -/

/-- **`sorts`**: `SortClauseT` is readback-only — reflexive readbacks at every compact code;
    `eqN` is unused by the clause (the two universe codes carry no level constraint). -/
theorem fundT_sorts {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} {l₁ l₂ : Level}
    (_heq : eqN l₁ l₂) (_hΓ : CtxWfT E n Γ) (_hV : CtxValidAt M R n Γ) :
    FundConvAt M R n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) ∧
      TyValidAt M R n Γ (.sort (.succ l₁)) := by
  refine ⟨fun {Δ ρ ρ' σ σ'} _ _ c hc => ?_, .succ (.succ l₁), fundT_sort hM _⟩
  rcases hc with hc | hc <;> rcases hM.sort_inv hc with rfl | rfl
  · exact lrSCoreS_bot _ _ _ _
  · simp only [substT]
    rcases sortCode_prop_or_sort l₁ with h | h <;> rw [h]
    · rw [lrSCoreS_prop_iff]; exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
    · rw [lrSCoreS_sort_iff]; exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
  · exact lrSCoreS_bot _ _ _ _
  · simp only [substT]
    rcases sortCode_prop_or_sort l₂ with h | h <;> rw [h]
    · rw [lrSCoreS_prop_iff]; exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
    · rw [lrSCoreS_sort_iff]; exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩

/-- **`lit`**: the IH on the expansion's own typing (`hexp`, an original child), read back to
    the literal by the lit step at both compacts; the literal's compacts are the expansion's by
    `ModelLitInvT`. -/
theorem fundT_lit (hL : ReadbackLaws E R) (hRlit : ReadbackLitStepT R) {M : CtxModelT E}
    (hMli : ModelLitInvT M) {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (hexp : HasTyT E n Γ (natExpand t) T) (hΓ : CtxWfT E n Γ) (hV : CtxValidAt M R n Γ)
    (ih : IHBelow M R n (sizeOf (HasTyT.lit Γ t T hexp))) :
    FundTyAt M R n Γ (.lit t) T ∧ TyValidAt M R n Γ T := by
  have hlt : sizeOf hexp < sizeOf (HasTyT.lit Γ t T hexp) := by simp; omega
  obtain ⟨ihF, ihV⟩ := ih.1 hexp hlt hΓ hV
  refine ⟨fun {Δ ρ ρ' σ σ'} hΔ hS c hc => ?_, ihV⟩
  rcases hc with hc | hc <;> rcases hMli hc with rfl | hc'
  · exact lrSCoreS_bot _ _ _ _
  · simp only [substT]
    exact lrSCoreS_expand hL (hRlit Δ t) c
      (lrSCoreS_expand_right hL (hRlit Δ t) c
        (by simpa only [substT_natExpand] using ihF hΔ hS c (Or.inl hc')))
  · exact lrSCoreS_bot _ _ _ _
  · simp only [substT]
    exact lrSCoreS_expand hL (hRlit Δ t) c
      (lrSCoreS_expand_right hL (hRlit Δ t) c
        (by simpa only [substT_natExpand] using ihF hΔ hS c (Or.inr hc')))

/-- **`litConv`**: `exp = natExpand t` by the single `LiteralExpansion` constructor; the IH on
    `hexp` at the expansion's compact, read back to the literal on the left. -/
theorem fundT_litConv (hL : ReadbackLaws E R) (hRlit : ReadbackLitStepT R) {M : CtxModelT E}
    (hMli : ModelLitInvT M) {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hl : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp T)
    (hΓ : CtxWfT E n Γ) (hV : CtxValidAt M R n Γ)
    (ih : IHBelow M R n (sizeOf (ConvT.lit Γ t exp T hl hexp))) :
    FundConvAt M R n Γ (.lit t) exp T ∧ TyValidAt M R n Γ T := by
  cases hl with
  | of =>
      have hlt : sizeOf hexp < sizeOf (ConvT.lit Γ t (natExpand t) T (.of t) hexp) := by
        simp
      obtain ⟨ihF, ihV⟩ := ih.1 hexp hlt hΓ hV
      refine ⟨fun {Δ ρ ρ' σ σ'} hΔ hS c hc => ?_, ihV⟩
      rcases hc with hc | hc
      · rcases hMli hc with rfl | hc'
        · exact lrSCoreS_bot _ _ _ _
        · simp only [substT]
          exact lrSCoreS_expand hL (hRlit Δ t) c
            (by simpa only [substT_natExpand] using ihF hΔ hS c (Or.inl hc'))
      · simp only [substT]
        exact lrSCoreS_expand hL (hRlit Δ t) c
          (by simpa only [substT_natExpand] using ihF hΔ hS c (Or.inr hc))

#print axioms fundT_sorts
#print axioms fundT_lit
#print axioms fundT_litConv
#print axioms modelLitInvT_approxT
#print axioms readbackLitStepT_whStepCtx
