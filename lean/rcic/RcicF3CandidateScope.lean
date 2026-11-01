import rcic.RcicF3RawFamilyCandidatePrefix
import rcic.RcicF3PiHereditaryEnv
import rcic.RcicF3BoundDefs

/-!
# The actual field reader at the candidate family-only prefix

The current group adds fresh bodyless members. Its actual recursor-reader
environment and its family-only typing prefix therefore have the same
transparent-body lookup. The beta/zeta/delta reader agrees at every fuel.
This supplies the reader input to typed normalization at the already-produced
candidate prefix; it does not assume soundness of the constructor-bearing
reader environment or candidate constructor closure. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateScope
open Rcic.Declarative

/-- Bodyless extensions preserve the only environment-sensitive operation
used by the field normalizer. Freshness is supplied through preservation of
the old members and the new-member body condition. -/
theorem transparentBody_eq_of_bodyless_extension {E E₁ : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none) :
    ∀ r ls, transparentBody E₁ r ls = transparentBody E r ls := by
  intro r ls
  cases hm : E.members r with
  | none =>
      cases hm₁ : E₁.members r with
      | none => simp [transparentBody, hm, hm₁]
      | some m => simp [transparentBody, hm, hm₁, hnew r m hm₁ hm]
  | some m => simp [transparentBody, hm, hsub r m hm]

/-- The complete normalized domains and body are preserved at the same
reader fuel, including arbitrary nested Pi depth. -/
theorem piTelescopeFuel_of_transparentBody_eq {E E₁ : ResolvedEnv}
    (hb : ∀ r ls, transparentBody E r ls = transparentBody E₁ r ls) :
    ∀ fuel e, piTelescopeFuel E fuel e = piTelescopeFuel E₁ fuel e := by
  intro fuel
  induction fuel with
  | zero => intro e; rfl
  | succ fuel ih =>
      intro e
      rw [piTelescopeFuel, piTelescopeFuel, whnfFuel_congr_env hb]
      cases hw : whnfFuel E₁ fuel e with
      | none => rfl
      | some w =>
          cases w <;> try rfl
          case pi A B =>
            change (match piTelescopeFuel E fuel B with
                | none => none
                | some (ds, body) => some (A :: ds, body)) =
              (match piTelescopeFuel E₁ fuel B with
                | none => none
                | some (ds, body) => some (A :: ds, body))
            rw [ih B]

/-- Both the actual recursor-reader environment and the family-only typing
prefix are bodyless extensions of the same predecessor. -/
theorem recNode_transparentBody_prefix {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    ∀ r ls, transparentBody node.E0 r ls = transparentBody (extendEnv E f fm) r ls := by
  have hfresh : E.members f = none :=
    groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have h0 : ∀ r ls, transparentBody node.E0 r ls = transparentBody E r ls := by
    apply transparentBody_eq_of_bodyless_extension node.base
    intro r m hm hn
    have hm' := node.sub r m (members_extend_preserved node.fresh r m hm)
    rcases groupMembersT_cases hmem r m hm' with hold | hnew
    · rw [hn] at hold
      cases hold
    · exact groupMembersT_body_none hmem r m hnew
  have hS : ∀ r ls, transparentBody (extendEnv E f fm) r ls = transparentBody E r ls := by
    apply transparentBody_eq_of_bodyless_extension
      (fun r m hm => members_extend_preserved hfresh r m hm)
    intro r m hm hn
    by_cases hr : r = f
    · subst r
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      exact hbody
    · rw [members_extend_ne E f fm r hr] at hm
      rw [hn] at hm
      cases hm
  exact fun r ls => (h0 r ls).trans (hS r ls).symm

/-- A successful actual reader is a successful family-prefix reader with
the identical normalized telescope. This is the input consumed by the
existing typed-normalization theorem at that prefix. -/
theorem recNode_read {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    {fuel : Nat} {A b : Expr Nat} {ds : List (Expr Nat)}
    (hw : piTelescopeFuel node.E0 fuel A = some (ds, b)) :
    piTelescopeFuel (extendEnv E f fm) fuel A = some (ds, b) :=
  (piTelescopeFuel_of_transparentBody_eq
    (recNode_transparentBody_prefix hmem node) fuel A).symm.trans hw

/-- Compose the actual-node reader with typed normalization at the family-only
prefix. The old environment's bounded typings, AllSound and final-environment
iota are the existing predecessor inputs. No soundness of node.E0 is used.
The local context is the original field context, before inserting raw IHs. -/
theorem recNode_den_piTelescope (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hW : EnvWfT E) (hB : BoundG K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    {n : Nat} (hES : EnvSound (mkM P μ) σ K (extendEnv E f fm) n)
    {Γ : LCtx} {T : Expr Nat} {l : Level}
    (d : HasTyT (extendEnv E f fm) n Γ T (.sort l)) (hd : LOKt σ 4 K d)
    {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel node.E0 fuel T = some (ds, b))
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ (policyPi ds b)) (den (mkM P μ) σ ρ T) := by
  have hfresh : E.members f = none :=
    groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hsub : ∀ r m, E.members r = some m → (extendEnv E f fm).members r = some m :=
    fun r m hm => members_extend_preserved hfresh r m hm
  have hnew : ∀ r m, (extendEnv E f fm).members r = some m →
      E.members r = none → m.body = none := by
    intro r m hm hn
    by_cases hr : r = f
    · subst r
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      exact hbody
    · rw [members_extend_ne E f fm r hr] at hm
      rw [hn] at hm
      cases hm
  exact PiHereditary.den_piTelescope_of_bound P μ σ K hW hB hA hI
    (Rcic.Model.PS.groupMembersT_preserve hmem) hsub hnew hES d hd
    (recNode_read hmem node hw) ρ hρ

end Rcic.F3.PSet.CandidateScope
