import rcic.RcicNativePiModelLRTerm

/-!
# RcicNativePiModelFundCases — cases of the fundamental lemma for terms

The cases of `FundamentalTermI` (#7636) that close in its environment-`⊥` form, and the
exact reason the others do not.

**Compiled.**
* `fundTerm_sorts` — the `sort` typing rule on the diagonal: `⟦Sort l⟧_⊥ = {⊥, sort}` and
  the relation at `sort` is the type-level relation of two equal sorts.
* `fundConv_of_whStep`, `fundConv_of_whRed` — EVERY weak-head conversion case (β, ζ, `lit`;
  δ, ι given `WhApproxInvCore`) reduces to the diagonal on the contractum: the relation is
  closed under expansion (`lrTermI_expand`) and the compact transfers by weak-head
  invariance (`approxI_whRed`).  So the conversion half of `FundamentalTermI` for these
  constructors is the typing half on the contractum.
* `fundConv_refl_of_diag`, `fundConv_trans_of_sound` — `ConvT.refl` is the diagonal; `trans`
  composes given model soundness (`TypeSoundnessI`-style transfer of the compact) and
  transitivity of `LRTermI`, which is the named `LRTermTrans`.

**Three design findings (exact, named).**
1. `FundamentalTermI` is NOT provable by direct induction on derivations: the `lam`, `app`,
   `pi` and `letE` cases need the relation for the body under a RELATED SUBSTITUTION of the
   bound variable (paper §2.7 (Subst)): `Δ ⊨ σ ≡ σ′ : Γ`, with the model environment
   `ρ_σ` interpreting each variable by its substituent's approximations — the `⊥`-form is
   the corollary at the identity substitution.  Named: `FundamentalTermIS` (shape given in
   the PR body; the simultaneous-substitution infrastructure is `RcicSubstT`'s).
2. `symm` and `tyConv` need INDEX TRANSPORT: the function clause's result index `B₁[N]`
   depends on the LEFT argument, so swapping sides or converting the type requires moving
   the relation along `TyConvT` on the index — `LRTermIndexTransport`, by recursion on
   compacts using `LRTypeIN` at matching shapes.
3. `LRTermI`'s `spine` clause reads a spine compact as a TYPE code.  That is right for
   family applications but wrong for the `consts` case at non-sort types (constructor terms,
   and opaque function constants, which `ApproxI` denotes by `spine r []`): the clause must
   be split by the weak-head normal form of `A` (sort / family spine / Π), and opaque
   function constants should not be in the model at all — δ must be given its semantics
   (`agy-pimodel`).  Named: `LRTermSpineSplit`.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ### the `sort` case -/

/-- The `sort` typing rule on the diagonal. -/
theorem fundTerm_sorts {Γ : LCtx} (l : Level) :
    ∀ u, ApproxI EnvI.bot (.sort l) u → LRTermI E n Γ (.sort l) (.sort l) (.sort (.succ l)) u := by
  intro u hu
  rcases approxI_sort_inv hu with h0 | h0 <;> subst h0
  · exact lrTermI_bot _ _ _ _
  · rw [lrTermI_sort_iff]
    exact ⟨⟨_, .refl _⟩, lrTypeIN_sort_congr Γ l l⟩

/-! ### the weak-head conversion cases reduce to the diagonal -/

/-- One weak-head step: the conversion clause from the diagonal on the contractum. -/
theorem fundConv_of_whStep (hinv : WhApproxInv E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : WhStep E M M')
    (hdiag : ∀ u, ApproxI EnvI.bot M' u → LRTermI E n Γ M' M' A u) :
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxI EnvI.bot M' u := (hinv h EnvI.bot u).mp hu
  exact lrTermI_expand (.step h (.refl _)) (.refl _) u (hdiag u hu')

/-- Several weak-head steps. -/
theorem fundConv_of_whRed (hinv : WhApproxInv E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : WhRed E M M')
    (hdiag : ∀ u, ApproxI EnvI.bot M' u → LRTermI E n Γ M' M' A u) :
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxI EnvI.bot M' u := (approxI_whRed hinv h EnvI.bot u).mp hu
  exact lrTermI_expand h (.refl _) u (hdiag u hu')

/-- β as a weak-head step. -/
theorem fundConv_beta (hinv : WhApproxInv E) {Γ : LCtx} (A b a T : Expr Nat)
    (hdiag : ∀ u, ApproxI EnvI.bot (instantiate0 a b) u →
      LRTermI E n Γ (instantiate0 a b) (instantiate0 a b) T u) :
    ∀ u, ApproxI EnvI.bot (.app (.lam A b) a) u →
      LRTermI E n Γ (.app (.lam A b) a) (instantiate0 a b) T u :=
  fundConv_of_whStep hinv (.beta A b a) hdiag

/-- ζ as a weak-head step. -/
theorem fundConv_zeta (hinv : WhApproxInv E) {Γ : LCtx} (A v b T : Expr Nat)
    (hdiag : ∀ u, ApproxI EnvI.bot (instantiate0 v b) u →
      LRTermI E n Γ (instantiate0 v b) (instantiate0 v b) T u) :
    ∀ u, ApproxI EnvI.bot (.letE A v b) u → LRTermI E n Γ (.letE A v b) (instantiate0 v b) T u :=
  fundConv_of_whStep hinv (.zeta A v b) hdiag

/-- Literal expansion as a weak-head step. -/
theorem fundConv_lit (hinv : WhApproxInv E) {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (hdiag : ∀ u, ApproxI EnvI.bot (natExpand t) u →
      LRTermI E n Γ (natExpand t) (natExpand t) T u) :
    ∀ u, ApproxI EnvI.bot (.lit t) u → LRTermI E n Γ (.lit t) (natExpand t) T u :=
  fundConv_of_whStep hinv (.lit t) hdiag

/-! ### `refl` and `trans` of the conversion half -/

/-- `ConvT.refl` is the diagonal. -/
theorem fundConv_refl_of_diag {Γ : LCtx} {M A : Expr Nat}
    (hdiag : ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M A u) :
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M A u := hdiag

/-- Transitivity of the term-level relation (named; the function clause needs index
    transport to compose, see the PR body). -/
def LRTermTrans (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {M N P A : Expr Nat} {u : CptI},
    LRTermI E n Γ M N A u → LRTermI E n Γ N P A u → LRTermI E n Γ M P A u

/-- Index transport of the term-level relation along a type conversion (named). -/
def LRTermIndexTransport (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {M M' A A' : Expr Nat} {u : CptI}, CtxWfT E n Γ →
    TyConvT E n Γ A A' → LRTermI E n Γ M M' A u → LRTermI E n Γ M M' A' u

/-- `ConvT.trans` from transitivity and the transfer of the compact across the middle term
    (model soundness for the first conversion). -/
theorem fundConv_trans_of_sound (htr : LRTermTrans E n) {Γ : LCtx} {M N P A : Expr Nat}
    (hsound : ∀ u, ApproxI EnvI.bot M u → ApproxI EnvI.bot N u)
    (h₁ : ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M N A u)
    (h₂ : ∀ u, ApproxI EnvI.bot N u → LRTermI E n Γ N P A u) :
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M P A u :=
  fun u hu => htr (h₁ u hu) (h₂ u (hsound u hu))

/-- `ConvT.tyConv` from index transport. -/
theorem fundConv_tyConv_of_transport (hT : LRTermIndexTransport E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M M' A A' : Expr Nat} (hc : TyConvT E n Γ A A')
    (h : ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M' A u) :
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M' A' u :=
  fun u hu => hT hΓ hc (h u hu)

/-! ### the spine-clause finding -/

/-- The refined reading of a spine compact as an ELEMENT (named): split by the weak-head
    normal form of the type — a type code at a universe, a constructor spine at a family,
    and no clause at a Π (opaque function constants leave the model once δ unfolds). -/
def LRTermSpineSplit (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptI},
    LRTermI E n Γ M M' A (.spine r args) →
      (∃ u, WhRed E A (.sort u)) ∨
      (∃ X, WhRed E A X ∧ WhNormal E X ∧ ∀ Y, ¬ WhRed E A (.sort Y) ∧ ∀ A₁ B₁, ¬ WhRed E A (.pi A₁ B₁))

/-- In the present relation the spine clause always forces the type-code reading: this is
    the statement that `consts` at a non-sort type cannot be closed as the relation stands. -/
theorem lrTermI_spine_forces_sort {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptI}
    (h : LRTermI E n Γ M M' A (.spine r args)) : ∃ u, WhRed E A (.sort u) :=
  ((lrTermI_spine_iff _ _ _ _ _ _).mp h).1

#print axioms fundTerm_sorts
#print axioms fundConv_of_whStep
#print axioms fundConv_of_whRed
#print axioms fundConv_beta
#print axioms fundConv_zeta
#print axioms fundConv_lit
#print axioms fundConv_refl_of_diag
#print axioms LRTermTrans
#print axioms LRTermIndexTransport
#print axioms fundConv_trans_of_sound
#print axioms fundConv_tyConv_of_transport
#print axioms LRTermSpineSplit
#print axioms lrTermI_spine_forces_sort

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
