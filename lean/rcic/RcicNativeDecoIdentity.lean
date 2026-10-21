import rcic.RcicNativeDecoReindex
import rcic.RcicNativeValleyOf

/-!
# Identity steps between decorations of a nonliteral term

Two native typings of the same nonliteral term at the same index can be
the source and target decoration interfaces of an actual certified identity
step. At an application, pi, lambda, or let root, the original typing
supplies the source data and reflexive children, while the existing
parallel constructor stores the second typing as its target premise.
Regularity supplies the constructor's additional sorting premises.

The only recursive call peels an original source-typing `conv` wrapper.
The second typing is transported backwards along that wrapper's own
conversion; the resulting identity step is then reindexed forwards.
The second typing may grow and is not a decreasing argument. Compound
children are used reflexively, without recursive calls, and may themselves
contain literals.

The statement excludes literal roots. The landed `ParRedT.lit` expands a
literal and has no literal-to-literal congruence constructor with an
independently supplied target typing. This module makes no all-term
identity claim and gives no refutation for literal roots.

`coherentStarOf_nonliteral` uses that identity step before an existing step
and returns a coherent two-step star with an independently supplied source
decoration. It is a local interface repair, not global star completion.

`closure_claim = 0`. No global diamond, type-uniqueness, Pi-row, or
retyping hypothesis is used. No arbitrary change of type index is
constructed here.
-/

namespace Rcic.Declarative.NativeValleys.DecoIdentityAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoReindexAudit (reindex_left_deco reindex_right_deco)

private theorem sortDeco_eq (l : Level) (d₁ d₂ : Deco (.sort l)) : d₁ = d₂ := by
  cases d₁
  cases d₂
  rfl

private theorem bvarDeco_eq (i : Nat) (d₁ d₂ : Deco (.bvar i)) : d₁ = d₂ := by
  cases d₁
  cases d₂
  rfl

private theorem constDeco_eq (r : Nat) (ls : List Level)
    (d₁ d₂ : Deco (.const r ls)) : d₁ = d₂ := by
  cases d₁
  cases d₂
  rfl

/-- An actual identity step at the common index, carrying the first typing's
source decoration and the second typing's target decoration. Only the root
is required to be nonliteral. The sole recursion is on an original `conv`
child of `h₁`; the generated backwards transport of `h₂` is not measured. -/
def identityStepOf_nonliteral (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {e T : Expr Nat} → (h₁ h₂ : HasTyT E n Γ e T) →
    (hnlit : ∀ t : Nat, e ≠ .lit t) →
    Σ' (s : CStep E n PEq Γ e e T),
      decoOf (s.leftTyped L hΓ) = decoOf h₁ ∧
      decoOf (s.rightTyped L hΓ) = decoOf h₂
  | _, _, .sort _ l, h₂, _ => by
      let hs : HasTyT E n Γ (.sort l) (.sort (.succ l)) := .sort Γ l
      let s : CStep E n PEq Γ (.sort l) (.sort l) (.sort (.succ l)) :=
        ⟨.refl Γ _ _ hs, .refl (.refl Γ _ _ hs)⟩
      exact ⟨s, rfl, sortDeco_eq l _ (decoOf h₂)⟩
  | _, _, .bvar _ i A hlookup, h₂, _ => by
      let hs : HasTyT E n Γ (.bvar i) A := .bvar Γ i A hlookup
      let s : CStep E n PEq Γ (.bvar i) (.bvar i) A :=
        ⟨.refl Γ _ _ hs, .refl (.refl Γ _ _ hs)⟩
      exact ⟨s, rfl, bvarDeco_eq i _ (decoOf h₂)⟩
  | _, _, .const _ r ls m hres hlen hwf, h₂, _ => by
      let hs : HasTyT E n Γ (.const r ls) (instantiateLevels ls m.mtype) :=
        .const Γ r ls m hres hlen hwf
      let s : CStep E n PEq Γ (.const r ls) (.const r ls)
          (instantiateLevels ls m.mtype) :=
        ⟨.refl Γ _ _ hs, .refl (.refl Γ _ _ hs)⟩
      exact ⟨s, rfl, constDeco_eq r ls _ (decoOf h₂)⟩
  | _, _, .pi _ A u B v hA hB, h₂, _ => by
      let hs : HasTyT E n Γ (.pi A B) (.sort (.imax u v)) :=
        .pi Γ A u B v hA hB
      let s : CStep E n PEq Γ (.pi A B) (.pi A B) (.sort (.imax u v)) :=
        ⟨.pi Γ A A B B u v hA (.refl Γ A (.sort u) hA)
            hB (.refl (.assumption A :: Γ) B (.sort v) hB) h₂,
          .pi (.refl Γ _ _ hs)⟩
      exact ⟨s, rfl, rfl⟩
  | _, _, .lam _ A u body B hA hb, h₂, _ => by
      let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨v, hB⟩ := tySort hW hΓA hb
      let hs : HasTyT E n Γ (.lam A body) (.pi A B) :=
        .lam Γ A u body B hA hb
      let s : CStep E n PEq Γ (.lam A body) (.lam A body) (.pi A B) :=
        ⟨.lam Γ A A body body B u v (.refl Γ A (.sort u) hA) hA hB
            (.refl (.assumption A :: Γ) body B hb) h₂,
          .lam (.refl Γ _ _ hs) (.refl (.refl _ body B hb))⟩
      exact ⟨s, rfl, rfl⟩
  | _, _, .app _ f a A B hf ha, h₂, _ => by
      obtain ⟨_, v, _, hB, _⟩ := hasTyTInv_pi (tySort hW hΓ hf).2 rfl
      have hTy : HasTyT E n Γ (instantiate0 a B) (.sort v) := by
        simpa only [instantiate0, instantiate] using
          hasTyT_subst0S (envClosed_of_envWfT hW)
            (envMembersSubstStable_of_envWfT hW) hB ha
      let hs : HasTyT E n Γ (.app f a) (instantiate0 a B) :=
        .app Γ f a A B hf ha
      let s : CStep E n PEq Γ (.app f a) (.app f a) (instantiate0 a B) :=
        ⟨.app Γ f f a a A B (.pi A B) v v
            (.refl Γ f (.pi A B) hf) (.refl Γ (.pi A B)) hB hTy
            (.refl Γ a A ha) h₂,
          .app (.refl Γ _ _ hs)
            (.refl (.refl Γ f (.pi A B) hf)) (.refl (.refl Γ a A ha))⟩
      exact ⟨s, rfl, rfl⟩
  | _, _, .letE _ A u value B body hA hv hb, h₂, _ => by
      let hΓL : CtxWfT E n (.letBinding A value :: Γ) :=
        .letBinding Γ A u value hΓ hA hv
      obtain ⟨w, hB⟩ := tySort hW hΓL hb
      have hTy : HasTyT E n Γ (instantiate0 value B) (.sort w) := by
        simpa only [instantiate0, instantiate] using
          hasTyT_substLet0_of_envWfT hW hB hv
      let hs : HasTyT E n Γ (.letE A value body) (instantiate0 value B) :=
        .letE Γ A u value B body hA hv hb
      let s : CStep E n PEq Γ (.letE A value body) (.letE A value body)
          (instantiate0 value B) :=
        ⟨.letE Γ A A value value body body B u w
            (.refl Γ A (.sort u) hA) hA (.refl Γ value A hv) hB hTy
            (.refl (.letBinding A value :: Γ) body B hb) h₂,
          .letE (.refl Γ _ _ hs)
            (.refl (.refl Γ value A hv)) (.refl (.refl _ body B hb))⟩
      exact ⟨s, rfl, rfl⟩
  | _, _, .lit _ t _ _, _, hnlit => False.elim (hnlit t rfl)
  | e, _, .conv _ _ A B u h hc, h₂, hnlit => by
      let h₂A : HasTyT E n Γ e A :=
        .conv Γ e B A u h₂ (.symm Γ A B (.sort u) hc)
      let r := identityStepOf_nonliteral hW L hΓ h h₂A hnlit
      let chain : TyConvT E n Γ A B := .of Γ A B u hc
      refine ⟨r.1.reindex chain, ?_, ?_⟩
      · simpa only [decoOf] using
          (reindex_left_deco L hΓ r.1 chain).trans r.2.1
      · simpa only [h₂A, decoOf] using
          (reindex_right_deco L hΓ r.1 chain).trans r.2.2
  termination_by e T h₁ _ _ => sizeOf h₁
  decreasing_by all_goals (simp; omega)

/-- Repair a step's source decoration by inserting a certified identity
step. The result has two explicit steps, is coherent, and preserves the
original target decoration. No diamond is consulted. -/
def coherentStarOf_nonliteral (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (ha : HasTyT E n Γ a T) (p : CStep E n PEq Γ a b T)
    (hnlit : ∀ t : Nat, a ≠ .lit t) :
    Σ' (s : CStar E n PEq Γ a b T),
      DecoStarAudit.Coherent L hΓ s ∧
      decoOf (s.leftTyped L hΓ) = decoOf ha ∧
      decoOf s.rightTyped = decoOf (p.rightTyped L hΓ) := by
  let r := identityStepOf_nonliteral hW L hΓ ha (p.leftTyped L hΓ) hnlit
  let s : CStar E n PEq Γ a b T :=
    .tail r.1 (.tail p (.refl Γ b T (p.rightTyped L hΓ)))
  refine ⟨s, ?_, ?_, ?_⟩
  · change decoOf (r.1.rightTyped L hΓ) = decoOf (p.leftTyped L hΓ) ∧
        (decoOf (p.rightTyped L hΓ) = decoOf (p.rightTyped L hΓ) ∧ True)
    exact ⟨r.2.2, rfl, True.intro⟩
  · simpa only [s, CStar.leftTyped] using r.2.1
  · simp only [s, CStar.rightTyped]

#print axioms identityStepOf_nonliteral
#print axioms coherentStarOf_nonliteral

end Rcic.Declarative.NativeValleys.DecoIdentityAudit
