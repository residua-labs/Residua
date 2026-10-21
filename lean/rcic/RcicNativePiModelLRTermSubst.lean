import rcic.RcicNativePiModelLRTermS
import rcic.RcicSubstT
import rcic.RcicSubstCalc

/-!
# RcicNativePiModelLRTermSubst — related-substitution stability of `LRTermS`

Finding 1 of #7641, on the split-spine relation `LRTermS` (#7646, `devin/fcd11`).
The objective's `LRTermI'` is this relation.

A related substituent is read as its full approximation set: index `j` denotes
`denI (EnvI.drop ρ j) r`, not one compact. That is the lower-ideal equivalence
`approxSubst` (`approxI_subst_intro` / `approxI_subst_elim`).

`FundamentalTermIS` is the part of that step which closes here: `.bot` for
every term, `.sort` for every term (weak-head reduction to a sort commutes
with instantiation; ι is an input `hι`; δ uses `EnvClosed`), and the variable
`j` at every compact of the substituent's full approximation set.

The unrestricted paper statement — every compact of a typed term's
interpretation is a compact of `LRTermS` after a related substitution — is not
this theorem. It is false on this relation for a Π-typed constant:
`ApproxI.const` puts `.spine r []` in the denotation, and
`lrTermS_spine_at_pi_false` says `LRTermS` has no spine reading at a Π.
Closing that is a change to the relation or to δ, neither of which is this
lane (`LRTermS` is not rewritten; δ/ι stay inputs). The λ/conversion remainder
is separately blocked on `LRTermSTransportLam`: a `TyConvT`-chain typing of the
codomain in the moved context. irr, K, and η-K are not proved here.

`closure_claim = 0`. No unfinished proof, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

/-- One instantiation passes through a `0`-instantiation (capture-avoiding lift
    under the binder). -/
private theorem instantiate_instantiate0 (j : Nat) (s a B : Expr Nat) :
    instantiate j s (instantiate0 a B) =
      instantiate0 (instantiate j s a) (instantiate (j + 1) (lift 0 1 s) B) := by
  calc
    instantiate j s (instantiate0 a B)
        = substT (SubstT.single j s) (instantiate0 a B) := by rw [instantiate_eq_substT]
    _ = instantiate0 (substT (SubstT.single j s) a) (substT (SubstT.single j s).up B) :=
        substT_instantiate0 (SubstT.single j s) a B
    _ = instantiate0 (instantiate j s a) (substT (SubstT.single (j + 1) (lift 0 1 s)) B) := by
        rw [← instantiate_eq_substT]
        exact congrArg (fun t => instantiate0 (instantiate j s a) t)
          (substT_ext (SubstT.single_up j s) B)
    _ = instantiate0 (instantiate j s a) (instantiate (j + 1) (lift 0 1 s) B) := by
        rw [← instantiate_eq_substT]

/-- Weak-head steps commute with instantiation. ι is the input; δ uses that
    environment bodies are lift-closed. -/
private theorem whStep_instantiate
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {a b : Expr Nat} (h : WhStep E a b) :
    ∀ (j : Nat) (s : Expr Nat), WhStep E (instantiate j s a) (instantiate j s b) := by
  induction h with
  | beta A body arg =>
      intro j s
      rw [show instantiate j s (.app (.lam A body) arg) =
          .app (.lam (instantiate j s A) (instantiate (j + 1) (lift 0 1 s) body))
            (instantiate j s arg) from rfl,
        instantiate_instantiate0 j s arg body]
      exact WhStep.beta _ _ _
  | zeta A value body =>
      intro j s
      rw [show instantiate j s (.letE A value body) =
          .letE (instantiate j s A) (instantiate j s value)
            (instantiate (j + 1) (lift 0 1 s) body) from rfl,
        instantiate_instantiate0 j s value body]
      exact WhStep.zeta _ _ _
  | @delta rmem ls m b hres hbody =>
      intro j s
      have hbod : ∀ k, lift k 1 b = b := (hcl rmem m hres).2 b hbody
      have hfix : instantiate j s (instantiateLevels ls b) = instantiateLevels ls b := by
        rw [instantiate_eq_substT]
        exact substT_closed (lift_instantiateLevels_closedT hbod ls) _
      rw [show instantiate j s (.const rmem ls) = .const rmem ls from rfl, hfix]
      exact WhStep.delta hres hbody
  | iota h =>
      intro j s
      exact hι h j s
  | lit t =>
      intro j s
      have hfix : instantiate j s (natExpand t) = natExpand t := natExpand_instantiate j s t
      rw [show instantiate j s (.lit t) = .lit t from rfl, hfix]
      exact WhStep.lit t
  | appHead _ ih =>
      intro j s
      exact WhStep.appHead (ih j s)

private theorem whRed_instantiate
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {a b : Expr Nat} (h : WhRed E a b) (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s a) (instantiate j s b) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (whStep_instantiate hι hcl h j s) ih

private theorem whRed_instantiate_sort
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {a : Expr Nat} {l : Level} (h : WhRed E a (.sort l))
    (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s a) (.sort l) := by
  exact whRed_instantiate hι hcl h j s

/-- The lower-ideal substitution equivalence this lane calls `approxSubst`:
    index `j` is `denI (EnvI.drop ρ j) r`, the substitute's full approximation set. -/
theorem approxSubst (ρ : EnvI) (j : Nat) (r e : Expr Nat) (c : CptI) :
    ApproxI ρ (instantiate j (lift 0 j r) e) c ↔
      ApproxI (EnvI.insert ρ j (denI (EnvI.drop ρ j) r)) e c :=
  ⟨fun h => approxI_subst_elim e h, fun h => approxI_subst_intro h ρ j r rfl⟩

/-- Related-substitution stability of `LRTermS` at the clauses this step closes.

`hrel` says the two substituents are related at every compact of the left
substituent's full approximation set. From that and `approxSubst`:

* `.bot` is stable for every term;
* `.sort` is stable for every term (weak-head reduction to a sort commutes with
  instantiation; ι is `hι`);
* the variable `j` is stable at every compact of that full set, because
  instantiating it is the lifted substituent. -/
theorem FundamentalTermIS
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {ρ : EnvI} {j : Nat} {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermS E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ M M' A .sort →
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermS E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  refine ⟨?bot, ?sort, ?var⟩
  case bot =>
    intro _ _ _
    exact lrTermS_bot _ _ _ _
  case sort =>
    intro M M' A h
    rw [lrTermS_sort_iff] at h ⊢
    rcases h with ⟨⟨l, hA⟩, hLR⟩
    cases hLR with
    | sort hM hM' =>
        exact ⟨⟨l, whRed_instantiate_sort hι hcl hA j (lift 0 j r)⟩,
          .sort (whRed_instantiate_sort hι hcl hM j (lift 0 j r))
            (whRed_instantiate_sort hι hcl hM' j (lift 0 j r'))⟩
  case var =>
    intro c hmem
    have hlook : ApproxI (EnvI.insert ρ j (denI (EnvI.drop ρ j) r)) (.bvar j) c :=
      (approxSubst ρ j r (.bvar j) c).mp hmem
    have hL : instantiate j (lift 0 j r) (.bvar j) = lift 0 j r := by
      rw [instantiate, if_pos (rfl : j = j)]
    have hR : instantiate j (lift 0 j r') (.bvar j) = lift 0 j r' := by
      rw [instantiate, if_pos (rfl : j = j)]
    rw [hL, hR]
    rcases approxI_bvar_inv hlook with hbot | hmem
    · subst hbot
      exact lrTermS_bot _ _ _ _
    · rw [EnvI.insert_self] at hmem
      exact hrel c hmem

/-- A spine compact is not a reading of an element at a Π type: the type-code
    reading needs the Π to reduce to a sort, and the constructor reading needs
    the Π itself to be a family spine. `whRed_pi_eq` and `approxI_pi_inv`
    refuse both. A Π-typed constant is still denoted by `.spine r []`
    (`ApproxI.const`), so the unrestricted fundamental lemma is false here. -/
theorem lrTermS_spine_at_pi_false {Γ : LCtx} {M M' A B : Expr Nat} {r : Nat}
    {args : List CptI} : ¬ LRTermS E n Γ M M' (.pi A B) (.spine r args) := by
  intro h
  rcases lrTermS_spine_split h with ⟨_, hl⟩ | ⟨_, _, hsp⟩
  · exact nomatch whRed_pi_eq hl
  · rcases approxI_pi_inv hsp with h0 | ⟨_, _, h0, _, _⟩ <;> cases h0

#print axioms approxSubst
#print axioms FundamentalTermIS
#print axioms lrTermS_spine_at_pi_false

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
