import rcic.RcicF3PiCanonicalWalk
import rcic.RcicF3PiCanonicalGroupAttack
import rcic.RcicF3PiSyntaxAttack
/-! Reader transport at actual typed W/Acc walks and a transparent-body
counterexample. Reader invariance is universal in fuel/expression. These are
syntax/environment probes; they do not inhabit a universal group producer.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiCanonicalWalkAttack
open Rcic.Declarative PiCanonicalWalk

/-- Every presentation reads identically at the real W node's preceding
constructor environment, before either constructor, and at full admission. -/
theorem w_walk_reads (fuel : Nat) (T : Expr Nat) :
    piTelescopeFuel PendAW.ePre fuel T = piTelescopeFuel PendAW.eLeaf fuel T ∧
    piTelescopeFuel PendAW.ePre fuel T = piTelescopeFuel PendAW.eFam fuel T := by
  have hp : ∀ r m, PendAW.ePre.members r = some m → PendAW.eAll.members r = some m :=
    members_extend_preserved (show PendAW.ePre.members 7 = none from rfl)
  have hl : ∀ r m, PendAW.eLeaf.members r = some m → PendAW.ePre.members r = some m :=
    members_extend_preserved (show PendAW.eLeaf.members 6 = none from rfl)
  have hf : ∀ r m, PendAW.eFam.members r = some m → PendAW.eLeaf.members r = some m :=
    members_extend_preserved (show PendAW.eFam.members 5 = none from rfl)
  have hb : ∀ r m, natEnvU.members r = some m → PendAW.eFam.members r = some m :=
    members_extend_preserved (show natEnvU.members 4 = none from rfl)
  have henv : ∀ r ls, transparentBody PendAW.ePre r ls =
      transparentBody natEnvU r ls := fun r ls =>
    (transparentBody_eq_base PendAW.membersT PendAW.basePreserved hp r ls).symm
  exact ⟨telescope_env (fun r ls => (henv r ls).trans
      (transparentBody_eq_base PendAW.membersT (fun r m hm => hf r m (hb r m hm))
        (fun r m hm => hp r m (hl r m hm)) r ls)) fuel T,
    telescope_env (fun r ls => (henv r ls).trans
      (transparentBody_eq_base PendAW.membersT hb
        (fun r m hm => hp r m (hl r m (hf r m hm))) r ls)) fuel T⟩

open Rcic.Declarative.Ann
/-- Every presentation reads identically before and after the real Acc
constructor; full admission is used only for syntax. -/
theorem acc_walk_reads (fuel : Nat) (T : Expr Nat) :
    piTelescopeFuel accPSupEnvT fuel T = piTelescopeFuel accPFamEnvT fuel T := by
  have hp : ∀ r m, accPSupEnvT.members r = some m → accPEnvT.members r = some m :=
    members_extend_preserved (show accPSupEnvT.members 12 = none from rfl)
  have hf : ∀ r m, accPFamEnvT.members r = some m → accPSupEnvT.members r = some m :=
    members_extend_preserved (show accPFamEnvT.members 11 = none from rfl)
  have hb : ∀ r m, paRelEnvT.members r = some m → accPFamEnvT.members r = some m :=
    members_extend_preserved (show paRelEnvT.members 10 = none from rfl)
  exact telescope_env (fun r ls =>
    (transparentBody_eq_base accPMembersT (fun r m hm => hf r m (hb r m hm)) hp r ls).symm.trans
      (transparentBody_eq_base accPMembersT hb (fun r m hm => hp r m (hf r m hm)) r ls)) fuel T

/- Elementary computation: the added identity really changes the reader.
The positive read is the existing RoleAttacks.deltaRead; do not duplicate it. -/
kernel_rfl_theorem delta_without_body :
  piTelescopeFuel accPEnvT 64 PiSyntaxAttack.deltaField = some ([], PiSyntaxAttack.deltaField)
kernel_rfl_theorem identity_body :
  transparentBody PiSyntaxAttack.env 20 [] = some PiSyntaxAttack.idBody
kernel_rfl_theorem identity_absent : transparentBody accPEnvT 20 [] = none

/-- Elementary contradiction: adding a transparent definition is outside
body agreement, even though the extension itself is actually well typed. -/
theorem changed_body_refused :
    ¬ (∀ r ls, transparentBody PiSyntaxAttack.env r ls = transparentBody accPEnvT r ls) := by
  intro h
  have he := h 20 []
  rw [identity_body, identity_absent] at he
  cases he

end Rcic.F3.PSet.PiCanonicalWalkAttack
