import rcic.RcicAccPiEnv

/-!
# Typed hidden presentations of the dependent Acc field

The identity definition is closed and installed by `EnvWfT.definition`
over the complete admitted Acc environment. The field has two binders
and a dependent family index. The conversions below are direct typed-rule
applications, reported as elementary checks. They exercise raw syntax;
they do not extract a semantic telescope or produce `StepAG`.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PiSyntaxAttack

open Rcic.Declarative Rcic.Declarative.Ann

abbrev level : Level := .imax (.succ .zero) (.imax .zero .zero)
abbrev idType : Expr Nat := .pi (.sort level) (.sort level)
abbrev idBody : Expr Nat := .lam (.sort level) (.bvar 0)
def idMember : CheckedMember := ⟨.definitionM, 0, idType, some idBody⟩
def env : ResolvedEnv := extendEnv accPEnvT 20 idMember

def idTypeTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ idType (.sort (.imax (.succ level) (.succ level))) :=
  .pi Γ _ _ _ _ (.sort Γ level) (.sort _ level)

def idBodyTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ idBody idType :=
  .lam Γ _ _ _ _ (.sort Γ level) (.bvar _ 0 _ rfl)

/-- The delta test has an actual typed environment, not a free stored body. -/
def envWfT : EnvWfT env :=
  .definition accPEnvT 20 idType idBody (.imax (.succ level) (.succ level))
    accPEnvWfT rfl (idTypeTy _ _ _) (idBodyTy _ _ _)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

abbrev ctx : LCtx := [.assumption (.sort .zero)]

def fieldTy : HasTyT env 0 ctx paFieldDom (.sort level) :=
  accPFieldDomTyT rfl rfl

def betaField : Expr Nat := .app idBody paFieldDom
def deltaField : Expr Nat := .app (.const 20 []) paFieldDom
def zetaField : Expr Nat := .letE (.sort level) paFieldDom (.bvar 0)

def betaTyped : HasTyT env 0 ctx betaField (.sort level) :=
  .app ctx _ _ _ _ (idBodyTy _ _ _) fieldTy

def deltaTyped : HasTyT env 0 ctx deltaField (.sort level) :=
  .app ctx _ _ _ _ (.const ctx 20 [] idMember rfl rfl rfl) fieldTy

def zetaTyped : HasTyT env 0 ctx zetaField (.sort level) :=
  .letE ctx _ _ _ _ _ (.sort ctx level) fieldTy (.bvar _ 0 _ rfl)

def betaConversion : ConvT env 0 ctx betaField paFieldDom (.sort level) :=
  .beta ctx _ _ _ _ _ (.sort ctx level) (.bvar _ 0 _ rfl) fieldTy

def zetaConversion : ConvT env 0 ctx zetaField paFieldDom (.sort level) :=
  .zeta ctx _ _ _ _ _ (.sort ctx level) fieldTy (.bvar _ 0 _ rfl)

def deltaConversion : ConvT env 0 ctx deltaField paFieldDom (.sort level) :=
  .trans ctx _ _ _ _
    (.app ctx _ _ _ _ _ _
      (.delta ctx 20 [] idMember idBody rfl rfl rfl rfl rfl (idBodyTy _ _ _))
      (.refl ctx _ _ fieldTy)) betaConversion

end Rcic.F3.PiSyntaxAttack
