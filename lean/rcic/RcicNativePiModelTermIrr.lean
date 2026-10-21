import rcic.RcicNativePiModelLRTerm

/-!
# RcicNativePiModelTermIrr — the irr / η cases of `FundamentalTermI` (#7636): an admitted refutation

devin-fcd's #7636 names `FundamentalTermI` (diagonal for typing, and conversions, at the
degenerate environment) and asks this lane for its `irr`, K, η-K and η cases, on top of the
proof-irrelevance layer (#7633) and the K / η-K compositions (#7634).

**Finding (compiled): `FundamentalTermI` is false as stated — before any irr case.**  `LRTermI`'s
`spine` clause relates `M`, `M′` at `spine r args` only if `A ↝* Sort u` (spine compacts are
read as TYPE codes), but `ApproxI.const` gives `spine r []` to EVERY constant — constructors,
proof constants, function constants.  For a constant `r` without level parameters whose type is a
Π (`whRed_pi_eq`: a Π never weak-head reduces to a sort), `ApproxI ⊥ (const r []) (spine r [])`
holds and `LRTermI Γ c c (Π A B) (spine r [])` does not (`lrTermI_spine_at_pi_false`).  Hence:

* `not_fundamentalTermI_of_pi_member`: the diagonal conjunct fails for any environment with such a
  member (every constructor with arguments, e.g. `And.intro`; every function constant).
* `not_irrCaseT_of_pi_member`: the `irr` case itself (`IrrCaseT`, the second conjunct at
  `ConvT.irr`) fails at a proof constant of a Π-proposition, with `p = q` that constant.

**Repair (stated, for #7636).**  The spine clause must split type codes from data spines
(constructor spines at an inductive type relate by their arguments, the paper's §3.4), and at a
PROPOSITION type the relation must be trivial — the §3.6 collapse that #7633's `tprojI_prop`
gives in the projected model.  With a relation trivial at propositions, the `irr` case is
immediate (totality at proposition codes by definition).

**η, K, η-K.**  `EtaCaseT` names the η case.  #7634's O4 (η is not projected-sound at `⊥`) does
NOT transfer: `LRTermI` at a λ compact whose outputs are `⊥` is trivially true, so the η case
reduces to weak-head expansion (`lrTermI_expand`, β on the left) plus the application case of
the same fundamental lemma for `f`; not refuted here.  K and η-K are #7634's chains
(`pEqI_K`, `pEqI_etaK`): on the term level they reduce to the ι case (δ/ι semantics,
`agy-pimodel`) and the η case, after the spine-clause repair above.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelTermAudit

open Rcic.Declarative.NativeValleys.PiModelIdealAudit

/-- At a Π type no spine compact relates anything: a Π never weak-head reduces to a sort. -/
theorem lrTermI_spine_at_pi_false {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {M M' A B : Expr Nat}
    {r : Nat} {args : List CptI} : ¬ LRTermI E n Γ M M' (.pi A B) (.spine r args) := by
  intro h
  obtain ⟨⟨u, hu⟩, _⟩ := (lrTermI_spine_iff Γ M M' (.pi A B) r args).mp h
  exact nomatch whRed_pi_eq hu

/-- **The diagonal of `FundamentalTermI` fails** at any level-free constant whose type is a Π. -/
theorem not_fundamentalTermI_of_pi_member {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} {A B : Expr Nat} (hres : E.members r = some m) (har : m.arity = 0)
    (hty : instantiateLevels [] m.mtype = .pi A B) : ¬ FundamentalTermI E n := by
  intro F
  have hT : HasTyT E n [] (.const r []) (instantiateLevels [] m.mtype) :=
    HasTyT.const [] r [] m hres har.symm rfl
  rw [hty] at hT
  exact lrTermI_spine_at_pi_false (F.1 CtxWfT.nil hT (.spine r []) (ApproxI.const EnvI.bot r []))

/-- The `irr` case of `FundamentalTermI` (its second conjunct at `ConvT.irr`). -/
def IrrCaseT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {P p q : Expr Nat}, HasTyT E n Γ P (.sort .zero) →
    HasTyT E n Γ p P → HasTyT E n Γ q P →
    ∀ u, ApproxI EnvI.bot p u → LRTermI E n Γ p q P u

/-- **The `irr` case fails** at a level-free proof constant of a Π-proposition. -/
theorem not_irrCaseT_of_pi_member {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} {A B : Expr Nat} (hres : E.members r = some m) (har : m.arity = 0)
    (hty : instantiateLevels [] m.mtype = .pi A B)
    (hprop : HasTyT E n [] (.pi A B) (.sort .zero)) : ¬ IrrCaseT E n := by
  intro F
  have hT : HasTyT E n [] (.const r []) (instantiateLevels [] m.mtype) :=
    HasTyT.const [] r [] m hres har.symm rfl
  rw [hty] at hT
  exact lrTermI_spine_at_pi_false
    (F CtxWfT.nil hprop hT hT (.spine r []) (ApproxI.const EnvI.bot r []))

/-- The η case of `FundamentalTermI` (its second conjunct at `ConvT.eta`), named. -/
def EtaCaseT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f A B : Expr Nat}, HasTyT E n Γ f (.pi A B) →
    ∀ u, ApproxI EnvI.bot (.lam A (.app (lift 0 1 f) (.bvar 0))) u →
      LRTermI E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) u

#print axioms lrTermI_spine_at_pi_false
#print axioms not_fundamentalTermI_of_pi_member
#print axioms IrrCaseT
#print axioms not_irrCaseT_of_pi_member
#print axioms EtaCaseT

end Rcic.Declarative.NativeValleys.PiModelTermAudit
