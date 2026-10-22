import rcic.RcicAnnDecl
import rcic.RcicAnnSpineConv

/-!
# The precise derivation descent of annotated irrelevance queries

The rank below counts declarative rule nodes, including all typing premises
of conversion rules and all conversion premises of typing rules.  The query
traversal is exhaustive over those same premises.  At each `ConvA.irr` it
records exactly the given proposition typing, together with a proof that
its rank is strictly smaller than the rank of the original derivation.

This is a descent result for the actual premise `hP : P : sort 0`.  It is
not a proposition-key coherence theorem.  An independent synthesis witness
for `P`, or a separately derived typing of its inferred type, is not made
a subderivation by this traversal.  No bound on the heights of the types
inside `hP` is asserted.  In particular the result does not by itself
supply either D1 bridge.  `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

mutual

/-- Number of declarative nodes in a typing, counting conversion premises. -/
def hasTyDerivationRankA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {e A : ExprA} : HasTyA E I n Γ e A → Nat
  | .sort _ _ => 1
  | .bvar _ _ _ _ _ hA => hasTyDerivationRankA3 hA + 1
  | .const _ _ _ _ _ _ _ _ hT => hasTyDerivationRankA3 hT + 1
  | .pi _ _ _ _ _ hA hB =>
      hasTyDerivationRankA3 hA + hasTyDerivationRankA3 hB + 1
  | .lam _ _ _ _ _ _ hA hB hb =>
      hasTyDerivationRankA3 hA + hasTyDerivationRankA3 hB +
        hasTyDerivationRankA3 hb + 1
  | .app _ _ _ _ _ _ _ _ hB hTy hf ha =>
      hasTyDerivationRankA3 hB + hasTyDerivationRankA3 hTy +
        hasTyDerivationRankA3 hf + hasTyDerivationRankA3 ha + 1
  | .letE _ _ _ _ _ _ _ hA hv hTy hb =>
      hasTyDerivationRankA3 hA + hasTyDerivationRankA3 hv +
        hasTyDerivationRankA3 hTy + hasTyDerivationRankA3 hb + 1
  | .lit _ _ _ h => hasTyDerivationRankA3 h + 1
  | .conv _ _ _ _ _ _ h hAl _ hB hc =>
      hasTyDerivationRankA3 h + hasTyDerivationRankA3 hAl +
        hasTyDerivationRankA3 hB + convDerivationRankA3 hc + 1

/-- Number of declarative nodes in a conversion, counting endpoint typings. -/
def convDerivationRankA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {a b A : ExprA} : ConvA E I n Γ a b A → Nat
  | .refl _ _ _ h => hasTyDerivationRankA3 h + 1
  | .symm _ _ _ _ h => convDerivationRankA3 h + 1
  | .trans _ _ _ _ _ h₁ h₂ =>
      convDerivationRankA3 h₁ + convDerivationRankA3 h₂ + 1
  | .beta _ _ _ _ _ _ hA hb ha hr =>
      hasTyDerivationRankA3 hA + hasTyDerivationRankA3 hb +
        hasTyDerivationRankA3 ha + hasTyDerivationRankA3 hr + 1
  | .zeta _ _ _ _ _ _ hA hv hb hr =>
      hasTyDerivationRankA3 hA + hasTyDerivationRankA3 hv +
        hasTyDerivationRankA3 hb + hasTyDerivationRankA3 hr + 1
  | .zetaLocal _ _ _ _ _ _ hv => hasTyDerivationRankA3 hv + 1
  | .delta _ _ _ _ _ _ _ _ _ _ hb => hasTyDerivationRankA3 hb + 1
  | .iota _ _ _ _ _ hl hr =>
      hasTyDerivationRankA3 hl + hasTyDerivationRankA3 hr + 1
  | .structIota _ _ _ _ _ _ _ _ _ hl hr hc =>
      hasTyDerivationRankA3 hl + hasTyDerivationRankA3 hr +
        convDerivationRankA3 hc + 1
  | .lit _ _ _ h => hasTyDerivationRankA3 h + 1
  | .app _ _ _ _ _ _ _ _ _ hf ha hB hr =>
      convDerivationRankA3 hf + convDerivationRankA3 ha +
        hasTyDerivationRankA3 hB + hasTyDerivationRankA3 hr + 1
  | .lam _ _ _ _ _ _ _ _ _ _ hA hb hr =>
      convDerivationRankA3 hA + convDerivationRankA3 hb +
        hasTyDerivationRankA3 hr + 1
  | .pi _ _ _ _ _ _ _ _ _ _ _ hA hB hr =>
      convDerivationRankA3 hA + convDerivationRankA3 hB +
        hasTyDerivationRankA3 hr + 1
  | .letE _ _ _ _ _ _ _ _ _ hA hv hb hr =>
      convDerivationRankA3 hA + convDerivationRankA3 hv +
        convDerivationRankA3 hb + hasTyDerivationRankA3 hr + 1
  | .sorts _ _ _ _ => 1
  | .consts _ _ _ _ _ _ _ _ _ _ hr => hasTyDerivationRankA3 hr + 1
  | .eta _ _ _ _ _ _ h hr =>
      hasTyDerivationRankA3 h + hasTyDerivationRankA3 hr + 1
  | .irr _ _ _ _ hP hp hq =>
      hasTyDerivationRankA3 hP + hasTyDerivationRankA3 hp +
        hasTyDerivationRankA3 hq + 1
  | .tyConv _ _ _ _ _ _ _ _ h hAl _ hA'l _ hA =>
      convDerivationRankA3 h + hasTyDerivationRankA3 hAl +
        hasTyDerivationRankA3 hA'l + convDerivationRankA3 hA + 1

end

/-- An actual irrelevance typing query below a named derivation rank. -/
structure IrrQueryBelowA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n bound : Nat) where
  context : LCtxA
  proposition : ExprA
  typing : HasTyA E I n context proposition (.sort .zero)
  descends : hasTyDerivationRankA3 typing < bound

private def raiseIrrQueryBelowA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n j k : Nat}
    (h : j ≤ k) (q : IrrQueryBelowA3 E I n j) : IrrQueryBelowA3 E I n k :=
  ⟨q.context, q.proposition, q.typing, Nat.lt_of_lt_of_le q.descends h⟩

private def raiseIrrQueriesA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n j k : Nat}
    (h : j ≤ k) (qs : List (IrrQueryBelowA3 E I n j)) :
    List (IrrQueryBelowA3 E I n k) := qs.map (raiseIrrQueryBelowA3 h)

mutual

/-- All irrelevance nodes below a typing, including nodes in its conversions. -/
def hasTyIrrQueriesA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {e A : ExprA} (d : HasTyA E I n Γ e A) :
    List (IrrQueryBelowA3 E I n (hasTyDerivationRankA3 d)) :=
  match d with
  | .sort _ _ => []
  | .bvar _ _ _ _ _ hA =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA)
  | .const _ _ _ _ _ _ _ _ hT =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hT)
  | .pi _ _ _ _ _ hA hB =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hB)
  | .lam _ _ _ _ _ _ hA hB hb =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hB) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hb)
  | .app _ _ _ _ _ _ _ _ hB hTy hf ha =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hB) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hTy) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hf) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 ha)
  | .letE _ _ _ _ _ _ _ hA hv hTy hb =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hv) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hTy) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hb)
  | .lit _ _ _ h =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 h)
  | .conv _ _ _ _ _ _ h hAl _ hB hc =>
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 h) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hAl) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (hasTyIrrQueriesA3 hB) ++
      raiseIrrQueriesA3 (by simp only [hasTyDerivationRankA3]; omega) (convIrrQueriesA3 hc)

/-- All irrelevance nodes below a conversion, including endpoint typings and
both conversions of `tyConv`.  Each result stores its strict descent proof. -/
def convIrrQueriesA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {a b A : ExprA} (d : ConvA E I n Γ a b A) :
    List (IrrQueryBelowA3 E I n (convDerivationRankA3 d)) :=
  match d with
  | .refl _ _ _ h =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 h)
  | .symm _ _ _ _ h =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 h)
  | .trans _ _ _ _ _ h₁ h₂ =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 h₁) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 h₂)
  | .beta _ _ _ _ _ _ hA hb ha hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hb) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 ha) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .zeta _ _ _ _ _ _ hA hv hb hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hv) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hb) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .zetaLocal _ _ _ _ _ _ hv =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hv)
  | .delta _ _ _ _ _ _ _ _ _ _ hb =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hb)
  | .iota _ _ _ _ _ hl hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hl) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .structIota _ _ _ _ _ _ _ _ _ hl hr hc =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hl) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hc)
  | .lit _ _ _ h =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 h)
  | .app _ _ _ _ _ _ _ _ _ hf ha hB hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hf) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 ha) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hB) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .lam _ _ _ _ _ _ _ _ _ _ hA hb hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hb) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .pi _ _ _ _ _ _ _ _ _ _ _ hA hB hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hB) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .letE _ _ _ _ _ _ _ _ _ hA hv hb hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hA) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hv) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hb) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .sorts _ _ _ _ => []
  | .consts _ _ _ _ _ _ _ _ _ _ hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .eta _ _ _ _ _ _ h hr =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 h) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hr)
  | .irr Γ P _ _ hP hp hq =>
      [⟨Γ, P, hP, by simp only [convDerivationRankA3]; omega⟩] ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hP) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hp) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hq)
  | .tyConv _ _ _ _ _ _ _ _ h hAl _ hA'l _ hA =>
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 h) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hAl) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (hasTyIrrQueriesA3 hA'l) ++
      raiseIrrQueriesA3 (by simp only [convDerivationRankA3]; omega) (convIrrQueriesA3 hA)

end

/-- The local carrier of every collected query is literally `sort 0`. -/
theorem irrQueryBelowA3_prop_typed {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat}
    (q : IrrQueryBelowA3 E I n k) :
    Nonempty (HasTyA E I n q.context q.proposition (.sort .zero)) := ⟨q.typing⟩

/-- A supplied earlier-stage predicate can be consumed at every recorded query.
This is an induction interface, not a supply of the proposition-key predicate. -/
theorem irrQueryBelowA3_use_earlier {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat}
    (Q : ∀ {Γ : LCtxA} {P : ExprA}, HasTyA E I n Γ P (.sort .zero) → Prop)
    (ih : ∀ {Γ : LCtxA} {P : ExprA} (hP : HasTyA E I n Γ P (.sort .zero)),
      hasTyDerivationRankA3 hP < k → Q hP)
    (q : IrrQueryBelowA3 E I n k) : Q q.typing := ih q.typing q.descends

/-- All contexts of a finite query trace are inhabited.  The `Nonempty`
wrapper permits ordinary logical use without choosing context derivations. -/
def IrrQueriesHaveContextsA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat}
    (qs : List (IrrQueryBelowA3 E I n k)) : Prop :=
  ∀ q ∈ qs, Nonempty (CtxWfA E I n q.context)

private theorem irrQueryContexts_nil {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat} :
    @IrrQueriesHaveContextsA3 E I n k [] := by
  intro q h
  cases h

private theorem irrQueryContexts_singleton
    {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat} (q : IrrQueryBelowA3 E I n k) :
    IrrQueriesHaveContextsA3 [q] ↔ Nonempty (CtxWfA E I n q.context) := by
  constructor
  · exact fun h => h q (by simp)
  · intro h r hr
    have he : r = q := by simpa only [List.mem_singleton] using hr
    cases he
    exact h

private theorem irrQueryContexts_append
    {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat}
    (qs rs : List (IrrQueryBelowA3 E I n k)) :
    IrrQueriesHaveContextsA3 (qs ++ rs) ↔
      IrrQueriesHaveContextsA3 qs ∧ IrrQueriesHaveContextsA3 rs := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (List.mem_append.mpr (.inl hq)),
      fun r hr => h r (List.mem_append.mpr (.inr hr))⟩
  · rintro ⟨hqs, hrs⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hqs q hq
    · exact hrs q hq

private theorem irrQueryContexts_raise
    {E : ResolvedEnvA} {I : IotaIfaceA} {n j k : Nat}
    (h : j ≤ k) (qs : List (IrrQueryBelowA3 E I n j)) :
    IrrQueriesHaveContextsA3 (raiseIrrQueriesA3 h qs) ↔ IrrQueriesHaveContextsA3 qs := by
  constructor
  · intro hw q hq
    exact hw (raiseIrrQueryBelowA3 h q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
  · intro hw q hq
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hq
    cases he
    exact hw r hr

section QueryContexts

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I)

include hE hI hR hIS

mutual

/-- Original context well-formedness supplies every local typing-query
context, including those reached through conversion premises. -/
theorem hasTyIrrQueriesA3_contexts : {Γ : LCtxA} → {e A : ExprA} →
    (d : HasTyA E I n Γ e A) → CtxWfA E I n Γ →
    IrrQueriesHaveContextsA3 (hasTyIrrQueriesA3 d)
  | _, _, _, .sort _ _, _ => irrQueryContexts_nil
  | _, _, _, .bvar _ _ _ _ _ hA, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts hA hΓ
  | _, _, _, .const _ _ _ _ _ _ _ _ hT, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts hT hΓ
  | _, _, _, .pi _ _ _ _ _ hA hB, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise]
      exact ⟨hasTyIrrQueriesA3_contexts hA hΓ,
        hasTyIrrQueriesA3_contexts hB (.assumption hΓ hA)⟩
  | _, _, _, .lam _ _ _ _ _ _ hA hB hb, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨hasTyIrrQueriesA3_contexts hA hΓ,
        hasTyIrrQueriesA3_contexts hB (.assumption hΓ hA),
        hasTyIrrQueriesA3_contexts hb (.assumption hΓ hA)⟩
  | _, _, _, .app _ _ _ _ _ _ _ _ hB hTy hf ha, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      have hA := (hasTyA_regular hE hI hR hIS hΓ ha).2
      exact ⟨hasTyIrrQueriesA3_contexts hB (.assumption hΓ hA),
        hasTyIrrQueriesA3_contexts hTy hΓ,
        hasTyIrrQueriesA3_contexts hf hΓ, hasTyIrrQueriesA3_contexts ha hΓ⟩
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hTy hb, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨hasTyIrrQueriesA3_contexts hA hΓ,
        hasTyIrrQueriesA3_contexts hv hΓ, hasTyIrrQueriesA3_contexts hTy hΓ,
        hasTyIrrQueriesA3_contexts hb (.letBinding hΓ hA hv)⟩
  | _, _, _, .lit _ _ _ h, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts h hΓ
  | _, _, _, .conv _ _ _ _ _ _ h hAl _ hB hc, hΓ => by
      simp only [hasTyIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨hasTyIrrQueriesA3_contexts h hΓ,
        hasTyIrrQueriesA3_contexts hAl hΓ, hasTyIrrQueriesA3_contexts hB hΓ,
        convIrrQueriesA3_contexts hc hΓ⟩

/-- Original context well-formedness supplies every local conversion-query
context. The binder cases use only landed declarative regularity. -/
theorem convIrrQueriesA3_contexts : {Γ : LCtxA} → {a b A : ExprA} →
    (d : ConvA E I n Γ a b A) → CtxWfA E I n Γ →
    IrrQueriesHaveContextsA3 (convIrrQueriesA3 d)
  | _, _, _, _, .refl _ _ _ h, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts h hΓ
  | _, _, _, _, .symm _ _ _ _ h, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_raise]
      exact convIrrQueriesA3_contexts h hΓ
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise]
      exact ⟨convIrrQueriesA3_contexts h₁ hΓ, convIrrQueriesA3_contexts h₂ hΓ⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨hasTyIrrQueriesA3_contexts hA hΓ,
        hasTyIrrQueriesA3_contexts hb (.assumption hΓ hA),
        hasTyIrrQueriesA3_contexts ha hΓ, hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨hasTyIrrQueriesA3_contexts hA hΓ,
        hasTyIrrQueriesA3_contexts hv hΓ,
        hasTyIrrQueriesA3_contexts hb (.letBinding hΓ hA hv),
        hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts hv hΓ
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts hb hΓ
  | _, _, _, _, .iota _ _ _ _ _ hl hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise]
      exact ⟨hasTyIrrQueriesA3_contexts hl hΓ, hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ hl hr hc, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨hasTyIrrQueriesA3_contexts hl hΓ, hasTyIrrQueriesA3_contexts hr hΓ,
        convIrrQueriesA3_contexts hc hΓ⟩
  | _, _, _, _, .lit _ _ _ h, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts h hΓ
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ hf ha hB hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      have hA := (hasTyA_regular hE hI hR hIS hΓ
        (convA_hasTy_left hE hI hR hIS hΓ ha)).2
      exact ⟨convIrrQueriesA3_contexts hf hΓ, convIrrQueriesA3_contexts ha hΓ,
        hasTyIrrQueriesA3_contexts hB (.assumption hΓ hA),
        hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ hA hb hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      have hAty := convA_hasTy_left hE hI hR hIS hΓ hA
      exact ⟨convIrrQueriesA3_contexts hA hΓ,
        convIrrQueriesA3_contexts hb (.assumption hΓ hAty),
        hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ hA hB hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      have hAty := convA_hasTy_left hE hI hR hIS hΓ hA
      exact ⟨convIrrQueriesA3_contexts hA hΓ,
        convIrrQueriesA3_contexts hB (.assumption hΓ hAty),
        hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      have hAty := convA_hasTy_left hE hI hR hIS hΓ hA
      have hvty := convA_hasTy_left hE hI hR hIS hΓ hv
      exact ⟨convIrrQueriesA3_contexts hA hΓ, convIrrQueriesA3_contexts hv hΓ,
        convIrrQueriesA3_contexts hb (.letBinding hΓ hAty hvty),
        hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .sorts _ _ _ _, _ => irrQueryContexts_nil
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_raise]
      exact hasTyIrrQueriesA3_contexts hr hΓ
  | _, _, _, _, .eta _ _ _ _ _ _ h hr, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise]
      exact ⟨hasTyIrrQueriesA3_contexts h hΓ, hasTyIrrQueriesA3_contexts hr hΓ⟩
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise,
        irrQueryContexts_singleton, and_assoc]
      exact ⟨⟨hΓ⟩, hasTyIrrQueriesA3_contexts hP hΓ,
        hasTyIrrQueriesA3_contexts hp hΓ, hasTyIrrQueriesA3_contexts hq hΓ⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h hAl _ hA'l _ hA, hΓ => by
      simp only [convIrrQueriesA3, irrQueryContexts_append, irrQueryContexts_raise, and_assoc]
      exact ⟨convIrrQueriesA3_contexts h hΓ, hasTyIrrQueriesA3_contexts hAl hΓ,
        hasTyIrrQueriesA3_contexts hA'l hΓ, convIrrQueriesA3_contexts hA hΓ⟩

end

end QueryContexts

#print axioms hasTyDerivationRankA3
#print axioms convDerivationRankA3
#print axioms IrrQueryBelowA3
#print axioms IrrQueryBelowA3.context
#print axioms IrrQueryBelowA3.proposition
#print axioms IrrQueryBelowA3.typing
#print axioms IrrQueryBelowA3.descends
#print axioms hasTyIrrQueriesA3
#print axioms convIrrQueriesA3
#print axioms irrQueryBelowA3_prop_typed
#print axioms irrQueryBelowA3_use_earlier
#print axioms IrrQueriesHaveContextsA3
#print axioms hasTyIrrQueriesA3_contexts
#print axioms convIrrQueriesA3_contexts

end Rcic.Declarative.Ann.LR3
