import rcic.RcicF3ReaderSubstitution
import rcic.RcicF3EvalRoleDelta

/-!
# The actual bounded source of a transparent reader body

A transparent body is recovered with its original stored derivation,
original predecessor environment, and original zero-valuation bound.
The reader's instantiated body is literally the same closed, level-closed
syntax. Thus the closure may keep that original derivation and valuation;
its semantic map to the reader valuation uses ReaderSubstitution.Levels.

This pays the stored-derivation part of the delta trace case. It neither
assumes a typed reduct at an arbitrary valuation nor substitutes a global
environment-soundness hypothesis for the predecessor invariant.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderDeltaOrigin
open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve)

/-- The type and the typing derivation are exactly the declaration's
original ones. Later environment extensions only compose lookup inclusion. -/
theorem stored (K : Nat → Nat) :
    {E : ResolvedEnv} → (hE : EnvWfT E) → BoundG K hE →
    ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat),
      E.members r = some m → m.body = some b → transparent m.mclass = true →
      ∃ (S : ResolvedEnv) (d : HasTyT S 0 [] b m.mtype),
        (∀ r' m', S.members r' = some m' → E.members r' = some m') ∧
        LOKt (fun _ => 0) 4 K d
  | _, .empty, _, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE hfresh _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨S, d, hs, hd⟩ := stored K hE hB r m b h hb htr
        exact ⟨S, d, fun r' m' hm => members_extend_preserved hfresh r' m' (hs r' m' hm), hd⟩
  | _, .definition E r0 _ _ _ hE hfresh _ hv _ _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
        exact ⟨E, hv, fun r' m' hm => members_extend_preserved hfresh r' m' hm, hB.2⟩
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨S, d, hs, hd⟩ := stored K hE hB.1 r m b h hb htr
        exact ⟨S, d, fun r' m' hm => members_extend_preserved hfresh r' m' (hs r' m' hm), hd⟩
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨S, d, hs, hd⟩ := stored K hE hB.1 r m b h hb htr
        exact ⟨S, d, fun r' m' hm => members_extend_preserved hfresh r' m' (hs r' m' hm), hd⟩
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hB, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        obtain ⟨S, d, hs, hd⟩ := stored K hE hB.1 r m b h hb htr
        exact ⟨S, d, fun r' m' hm => members_extend_preserved hfresh r' m' (hs r' m' hm), hd⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, hB, r, m, b, h, hb, htr => by
      rcases groupMembersT_cases hmem r m h with hold | hnew
      · obtain ⟨S, d, hs, hd⟩ := stored K hE hB.1 r m b hold hb htr
        exact ⟨S, d, fun r' m' hm => groupMembersT_preserve hmem r' m' (hs r' m' hm), hd⟩
      · rw [groupMembersT_body_none hmem r m hnew] at hb
        cases hb

/-- A successful reader lookup itself supplies the original body source.
No arity or numerical-level side condition is added to the reader equation. -/
theorem of_read (K : Nat → Nat) {E : ResolvedEnv}
    (hE : EnvWfT E) (hB : BoundG K hE)
    (r : Nat) (ls : List Level) (b : Expr Nat)
    (hr : transparentBody E r ls = some b) :
    ∃ (m : CheckedMember) (S : ResolvedEnv) (d : HasTyT S 0 [] b m.mtype),
      E.members r = some m ∧ m.body = some b ∧ m.arity = 0 ∧
      (∀ r' m', S.members r' = some m' → E.members r' = some m') ∧
      LOKt (fun _ => 0) 4 K d ∧
      (∀ k, Declarative.lift k 1 b = b) ∧ exprLevelsBounded 0 b = true := by
  obtain ⟨m, source, hm, htr, hb, he⟩ := transparentBody_some hr
  have hmeta := EvalRoleDelta.transparent_body_data hE r m source hm hb htr
  rw [Ann.instantiateLevels_closed ls source hmeta.2.2.2.2] at he
  subst b
  obtain ⟨S, d, hs, hd⟩ := stored K hE hB r m source hm hb htr
  exact ⟨m, S, d, hm, hb, hmeta.2.1, hs, hd, hmeta.2.2.2.1, hmeta.2.2.2.2⟩

end Rcic.F3.PSet.ReaderDeltaOrigin
