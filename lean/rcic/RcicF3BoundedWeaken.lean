import rcic.RcicF3Defs
import rcic.RcicTypedEnvEntry
import rcic.RcicFamAppTwinLokFund

/-!
# Structural environment inputs for bounded substitution

The bounded substitution proof uses the landed
Rcic.Declarative.Ann.Lok.hasTyT_weaken_lok directly; its proof and the
conversion companion are not redeclared here. This module supplies the
member substitution-stability fact from closedness, and closedness of the
actual first family cell of an admitted group. That family-only prefix
need not have an atomic EnvWfT derivation of its own.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedTransport
open Rcic.Declarative

theorem stable_of_closed {E : ResolvedEnv} (hcl : EnvClosed E) :
    EnvMembersSubstStable E :=
  fun r m hm =>
    let h := hcl r m hm
    ⟨fun ls s k => lift_id_instantiate (instantiateLevels ls m.mtype)
      (instantiateLevels_closed h.1 ls 0) k (Nat.zero_le k) s,
      fun b hb ls s k => lift_id_instantiate (instantiateLevels ls b)
        (instantiateLevels_closed (h.2 b hb) ls 0) k (Nat.zero_le k) s⟩

/-- Header closedness and bodylessness already carried by admission pay
the structural substitution premises at the actual family-only prefix. -/
theorem family_prefix_closed {E E' : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {rest : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: rest) E') :
    EnvClosed (extendEnv E f fm) := by
  obtain ⟨_tail, hfm, hbody⟩ := groupMembersT_consView hmem
  intro r m hm
  by_cases hr : r = f
  · subst r
    rw [members_extend_eq] at hm
    cases hm
    exact ⟨hfm, fun b hb => by rw [hbody] at hb; cases hb⟩
  · rw [members_extend_ne E f fm r hr] at hm
    exact envClosed_of_envWfT hE r m hm

end Rcic.F3.PSet.BoundedTransport
