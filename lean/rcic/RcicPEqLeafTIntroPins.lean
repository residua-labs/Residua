import rcic.RcicPEqLeafTIntro
import rcic.RcicPEqLeafTPropPins

/-!
# Non-vacuity: generated index chains and dependent type-level Pi leaves

The let value below is an application: the classifier constrains only
the subject/body spine, not every subexpression or conversion premise.
Both peak branches carry a beta-expanded original index and conv wraps.
The Pi example has C = bvar 0: its codomain genuinely depends on the
bound variable, whose type changes from family p to family q.
-/

namespace Rcic.Declarative
namespace PEqLeafTIntroPins
open PEqTProofFront PEqLeafTPropPins

private def emptyCl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def emptySub : EnvMembersSubstStable emptyEnv := envWfT_subst_inst EnvWfT.empty

/-- A let whose value is outside the classifier, but whose body is inside. -/
def sourceLet : Expr Nat := .letE P q (.bvar 0)

def sourceLet_ty {n : Nat} (Γ : LCtx) : HasTyT emptyEnv n Γ sourceLet P :=
  .letE Γ P .zero q P (.bvar 0) (P_ty Γ) (q_ty Γ)
    (.bvar (.letBinding P q :: Γ) 0 P rfl)

def sourceLet_alias {n : Nat} : HasTyT emptyEnv n [] sourceLet aliasP :=
  hasTyT_of_tyConvT (hasTyT_of_tyConvT (sourceLet_ty []) alias_chain.symmT)
    (.refl [] aliasP)

/-- hTP is output, not a separate caller premise. Exercises the let arm. -/
def auto_let_index {n : Nat} : TyConvT emptyEnv n [] aliasP P :=
  proofIndex_of_introSpine emptyCl emptySub (a := sourceLet) rfl (P_ty [])
    (sourceLet_ty []) sourceLet_alias

/-- The lambda/lambda/bvar spine with an outer converted index. -/
def auto_lambda_index {n : Nat} : TyConvT emptyEnv n [] aliasP P :=
  proofIndex_of_introSpine emptyCl emptySub (a := p) rfl (P_ty []) (p_ty [])
    (hasTyT_of_tyConvT (p_ty []) alias_chain.symmT)

private def actualProofRoot {n : Nat} : PEqLeafT emptyEnv n [] sourceLet p aliasP :=
  ⟨.proof [] sourceLet p P P (P_ty []) (P_ty []) (sourceLet_ty []) (p_ty []),
    sourceLet_alias, hasTyT_of_tyConvT (p_ty []) alias_chain.symmT⟩

/-- The producer inspects the actual raw proof root and emits evidence. -/
theorem producer_accepts_let_root {n : Nat} :
    (peqLeafT_introProofIndex? emptyCl emptySub (actualProofRoot (n := n))).isSome = true := rfl

/-- A structural root is not silently treated as a root proof certificate. -/
theorem producer_declines_structural_root {n : Nat} :
    (peqLeafT_introProofIndex? emptyCl emptySub (second_leaf (n := n))).isSome = false := rfl

/-- The q application is a real proof, but outside this partial producer.
Declining it is not a claim that no valid index certificate exists. -/
theorem producer_declines_application_proof {n : Nat} :
    (peqLeafT_introProofIndex? emptyCl emptySub
      (⟨.proof [] q p P P (P_ty []) (P_ty []) (q_ty []) (p_ty []),
        q_ty [], p_ty []⟩ : PEqLeafT emptyEnv n [] q p P)).isSome = false := rfl

/-- The unrestricted Pi proof-head case is explicitly outside this classifier. -/
theorem classifier_pi_boundary (A B : Expr Nat) : introTypeSpine (.pi A B) = false := rfl

private def zetaAtP {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] sourceLet q P :=
  .zeta [] P q q (.bvar 0) (.bvar 0) P .zero .zero (P_ty [])
    (.refl [] q P (q_ty [])) (P_ty [.letBinding P q]) (P_ty [])
    (.refl [.letBinding P q] (.bvar 0) P (.bvar _ 0 P rfl)) (q_ty [])

private def zetaAtAlias {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] sourceLet q aliasP :=
  .conv [] _ _ _ _ (.conv [] _ _ _ _ zetaAtP alias_chain.symmT) (.refl [] aliasP)

private def proofAtAlias {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] sourceLet rGood aliasP :=
  .conv [] _ _ _ _
    (.peq [] sourceLet rGood aliasP
      ⟨.proof [] sourceLet rGood P P (P_ty []) (P_ty []) (sourceLet_ty []) (rGood_ty []),
        sourceLet_alias, hasTyT_of_tyConvT (rGood_ty []) alias_chain.symmT⟩)
    (.refl [] aliasP)

/-- Real zeta/proof peak. The original aliasP index is retained, with
no hTP input at this consumer call site. -/
def auto_index_peak {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] q rGood aliasP ×'
      (ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] rGood rGood aliasP ×'
        ConvT emptyEnv n [] q rGood aliasP) :=
  parRedT_introProof_diamond_data emptyCl emptySub (a := sourceLet) rfl CtxWfT.nil
    (P_ty []) (sourceLet_ty []) zetaAtAlias proofAtAlias

private def aliasTy {n : Nat} : HasTyT emptyEnv n [] aliasP (.sort .zero) :=
  .app [] (.lam (.sort .zero) (.bvar 0)) P (.sort .zero) (.sort .zero)
    (.lam [] (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (.sort [] .zero) (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)) (P_ty [])

/-- family : aliasP -> Type, returning Prop. -/
def family : Expr Nat := .lam aliasP (.sort .zero)

private def familyTy {n : Nat} :
    HasTyT emptyEnv n [] family (.pi aliasP (.sort (.succ .zero))) :=
  .lam [] aliasP .zero (.sort .zero) (.sort (.succ .zero)) aliasTy (.sort _ .zero)

private def familyBeta {n : Nat} :
    ConvT emptyEnv n [] (.app family p) (.sort .zero) (.sort (.succ .zero)) :=
  .beta [] aliasP (.sort .zero) p (.sort (.succ .zero)) .zero
    aliasTy (.sort _ .zero) (hasTyT_of_tyConvT (p_ty []) alias_chain.symmT)

/-- The codomain is the bound VARIABLE, not a closed constant.
Its sort typing genuinely uses the conversion family p -> Prop. -/
private def dependentCodTy {n : Nat} :
    HasTyT emptyEnv n [.assumption (.app family p)] (.bvar 0) (.sort .zero) :=
  .conv _ (.bvar 0) (.app family p) (.sort .zero) (.succ .zero)
    (.bvar _ 0 (.app family p) rfl)
    (convTLiftPrefix emptyCl [.assumption (.app family p)] familyBeta)

def piLeft : Expr Nat := .pi (.app family p) (.bvar 0)
def piRight : Expr Nat := .pi (.app family q) (.bvar 0)
def piIndex : Expr Nat := .sort (.imax (.succ .zero) .zero)

/-- The new type-level leaf producer at a nonliteral family argument
index, with genuinely dependent C. Both raw roots are Pi constructors. -/
def dependent_pi_leaves {n : Nat} :
    PEqLeafT emptyEnv n [] piLeft piRight piIndex ×'
      (PEqLeafT emptyEnv n [] piRight piLeft piIndex ×'
        ConvT emptyEnv n [] piLeft piRight piIndex) :=
  pi_proofFamily_leaf_data emptyCl emptySub rfl (P_ty []) (p_ty [])
    (hasTyT_of_tyConvT (p_ty []) alias_chain.symmT)
    (hasTyT_of_tyConvT (q_ty []) alias_chain.symmT) familyTy dependentCodTy

theorem dependent_pi_nonidentity : piLeft ≠ piRight := by
  intro h
  have hargs := (Expr.app.inj (Expr.pi.inj h).1).2
  cases hargs

/-- Actual typed steps in both directions, not an Empty-leaf instance.
The reflected input peak left->right / left->left joins at left. -/
def dependent_pi_peak_and_join {n : Nat} :
    ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] piLeft piRight piIndex ×'
      (ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] piLeft piLeft piIndex ×'
        ParRedT (PEqLeafT emptyEnv n) emptyEnv n [] piRight piLeft piIndex) :=
  let ⟨forward, backward, _⟩ := dependent_pi_leaves
  ⟨.peq [] piLeft piRight piIndex forward,
    .refl [] piLeft piIndex forward.2.1,
    .peq [] piRight piLeft piIndex backward⟩

end PEqLeafTIntroPins
end Rcic.Declarative
