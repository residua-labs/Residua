import rcic.RcicPEqLeafTProp
import rcic.RcicPEqTProofFront

/-!
# Actual mixed-leaf and beta/peq peaks; proof-index boundary controls

The positive examples retain PEqLeafT, not Empty. They reuse the previous
raw counterexample's P, p, q and idP, replacing its untypable r with the
well-typed rGood = idP q. The typed mixed composition is proof then app.
A second pin joins a real beta step against a structural PEq leaf.
Its index is beta-expanded and converted twice before the join.

The negative examples keep the earlier heterogeneous raw edge but show
that it cannot inhabit PEqLeafT at ANY index; and refute a proof-index
certificate for sort 0 in the empty environment. The latter prevents
confusing proofs of P with propositions inhabiting Prop. These negative
results reuse the prior in-scope semantic rows only at emptyEnv. They
are not used by the unconditional proof-sector constructions.
-/

namespace Rcic.Declarative
namespace PEqLeafTPropPins
open PEqTProofFront

/-- A typed replacement for the raw counterexample's last endpoint. -/
def rGood : Expr Nat := .app idP q

def rGood_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ rGood P :=
  .app Γ idP q P P (idP_ty Γ) (q_ty Γ)

def first_leaf {n : Nat} : PEqLeafT emptyEnv n [] p q P :=
  ⟨pq, p_ty [], q_ty []⟩

/-- The second raw edge has an APP root, not a proof root. -/
def second_leaf {n : Nat} : PEqLeafT emptyEnv n [] q rGood P :=
  ⟨.app [] idP idP p q (PEqT.refl idP) pq, q_ty [], rGood_ty []⟩

/-- The repaired actual typed mixed proof/app composition. -/
def mixed_composite {n : Nat} : PEqLeafT emptyEnv n [] p rGood P :=
  peqLeafT_trans_of_propIndex (P_ty []) (.refl [] P) first_leaf second_leaf

theorem mixed_nonidentity : p ≠ rGood := by
  intro h
  cases h

/-- Genuine beta: (fun z : P => z) p steps to p. -/
def beta_branch {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] q p P :=
  .beta [] P (.bvar 0) (.bvar 0) p p P .zero .zero .zero
    (P_ty []) (P_ty [.assumption P]) (P_ty [])
    (.refl [.assumption P] (.bvar 0) P (.bvar [.assumption P] 0 P rfl))
    (.refl [] p P (p_ty [])) (p_ty [])

/-- The same source also moves to rGood via the structural actual leaf. -/
def peq_branch {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] q rGood P :=
  .peq [] q rGood P second_leaf

/-- A nonliteral proof index: a beta-expansion of the proposition P. -/
def aliasP : Expr Nat := .app (.lam (.sort .zero) (.bvar 0)) P

def alias_chain {n : Nat} : TyConvT emptyEnv n [] aliasP P :=
  .trans [] aliasP P P
    (.of [] aliasP P .zero
      (.beta [] (.sort .zero) (.bvar 0) P (.sort .zero) (.succ .zero)
        (.sort [] .zero) (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)
        (P_ty [])))
    (.refl [] P)

theorem alias_nonliteral : aliasP ≠ P := by
  intro h
  cases h

/-- The two original branches are moved to aliasP by actual conv nodes. -/
def beta_at_alias {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] q p aliasP :=
  .conv [] q p aliasP aliasP
    (.conv [] q p P aliasP beta_branch alias_chain.symmT)
    (.refl [] aliasP)

def peq_at_alias {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] q rGood aliasP :=
  .conv [] q rGood aliasP aliasP
    (.conv [] q rGood P aliasP peq_branch alias_chain.symmT)
    (.refl [] aliasP)

/-- beta x structural-peq, two conversion wrappers, nonliteral index.
The resulting steps AND ConvT still have exactly aliasP as their index. -/
def joined_at_alias {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] p rGood aliasP ×'
      (ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] rGood rGood aliasP ×'
        ConvT emptyEnv n [] p rGood aliasP) :=
  parRedT_propIndex_diamond_data (P_ty []) alias_chain beta_at_alias peq_at_alias

/-- The finite-peak API is exercised on nonempty original star chains. -/
theorem joined_stars_at_alias {n : Nat} :
    ∃ d : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT emptyEnv n) emptyEnv n [] p d aliasP) ∧
      Nonempty (ParRedTStar (PEqLeafT emptyEnv n) emptyEnv n [] rGood d aliasP) :=
  parRedTStar_propIndex_confluent (P_ty []) alias_chain
    (.tail beta_at_alias (.refl [] p aliasP
      (hasTyT_of_tyConvT (p_ty []) alias_chain.symmT)))
    (.tail peq_at_alias (.refl [] rGood aliasP
      (hasTyT_of_tyConvT (rGood_ty []) alias_chain.symmT)))

/-- The previously untypable endpoint stays excluded at every index.
The positive raw comparison qr is NOT erased or redefined. -/
theorem heterogeneous_raw_edge_not_leaf {n : Nat} {T : Expr Nat} :
    ¬ Nonempty (PEqLeafT emptyEnv n [] q r T) := by
  rintro ⟨h⟩
  exact r_not_typed h.2.2

/-- sort 0 is the type OF propositions, not a proposition type of
proofs. Thus the new core theorem cannot be used to equate arbitrary
propositions merely because they inhabit sort 0. The concrete rows are
supplied in their existing empty-environment scope only. -/
theorem no_propIndex_sort_zero_empty {n : Nat} {P0 : Expr Nat}
    (hP0 : HasTyT emptyEnv n [] P0 (.sort .zero))
    (hidx : TyConvT emptyEnv n [] (.sort .zero) P0) : False := by
  obtain ⟨cv⟩ := convT_of_tyConvT_sort_scope
    EnvWfT.empty (by trivial) CtxWfT.nil hP0 hidx.symmT
  obtain ⟨ht⟩ := (DT009T_endpoints_envWfT EnvWfT.empty CtxWfT.nil cv).2
  have rows := Ann.typedRowsWf_of_envWfT_semPrefix EnvWfT.empty (by trivial) n
  have hz := rows.sortRow CtxWfT.nil (hasTyTInv_sortT ht rfl)
  have impossible : (some 1 : Option Nat) = some 0 := hz (fun _ => none)
  cases impossible

end PEqLeafTPropPins
end Rcic.Declarative
