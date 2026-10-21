import rcic.RcicF8CtxWfViaS

namespace Rcic.Declarative.F8Measure
open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

def SepAllViaS (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfViaS E n Γ → ∀ {P : Expr Nat} {l : Level},
    HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False

theorem sepAllViaS_of_sortUnique (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) : SepAllViaS E n :=
  fun v => v.separation hW su

def XCtxKit.viaS (hW : EnvWfT E) (hsep : SepAllViaS E n) : XCtxKit E n R where
  Ctx := CtxWfViaS E n
  sep := hsep
  ins := CtxWfViaS.ins
  sub := fun j hget hv v => v.sub j hget
    (hv.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
  subLet := fun j hget hv v => v.subLet j hget
    (hv.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))

variable (hW : EnvWfT E) (K : ∀ R : List (Jd E n), CtxConvProc R)
  (hK : CtxConvContract K) (hsep : SepAllViaS E n)
  {Γ : LCtx} {A B A₁ B₁ A₂ B₂ : Expr Nat}

def xStructTcViaS (v : CtxWfViaS E n Γ) (c : EvTc R Γ A B)
    (hp : piSpinedTc c = true) (ha : A = .pi A₁ B₁) (hb : B = .pi A₂ B₂) :
    XOut R Γ A₁ B₁ A₂ B₂ :=
  (xTcWithCtx K hK (.viaS hW hsep) c v hp ha hb).1

theorem xStructTcViaS_leaves (v : CtxWfViaS E n Γ) (c : EvTc R Γ A B)
    (hp : piSpinedTc c = true) (ha : A = .pi A₁ B₁) (hb : B = .pi A₂ B₂) :
    ∀ ℓ ∈ XOut.leaves (xStructTcViaS hW K hK hsep v c hp ha hb),
      ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  (xTcWithCtx K hK (.viaS hW hsep) c v hp ha hb).2

theorem xStructTcViaS_eq (hsepOld : SepAll E n) (v : CtxWfViaS E n Γ)
    (c : EvTc R Γ A B) (hp : piSpinedTc c = true)
    (ha : A = .pi A₁ B₁) (hb : B = .pi A₂ B₂) :
    xStructTcViaS hW K hK (fun _ => hsepOld) v c hp ha hb =
      xStructTc K hK hsepOld c hp ha hb := rfl
end Rcic.Declarative.F8Measure
