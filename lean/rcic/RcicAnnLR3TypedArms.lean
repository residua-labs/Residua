import rcic.RcicAnnLR3TypedStatements

/-!
# Exact 9+19 constructor contracts, not a soundness supplier

Every contract retains the source constructor's exact premises and adds an
IH for each original typing/conversion child. The generated surface was
produced outside the repository and is kernel checked here. No host script
is committed. These are propositions, not asserted source-soundness facts.

Global dispatch is HOLD: the constant/member supplier for a truthful
least-fixed-point interpretation is refuted by TypedConstantModel.
Admission does not imply a semantic interpretation of arbitrary source
axioms. `closure_claim = 0`.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Rcic.Declarative.Ann.LR3.TypedArms
open Rcic.Declarative
open TypedStatements

def Ty_sort (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (l : Level),
    TyGoal M E I n Γ (.sort l) (.sort (.succ l))

def Ty_bvar (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (i : Nat)
    (A : ExprA)
    (u : Level)
    (h : lookupTypeA Γ i = some A)
    (hA : HasTyA E I n Γ A (.sort u))
    (ih_hA : TyGoal M E I n Γ A (.sort u)),
    TyGoal M E I n Γ (.bvar i) A

def Ty_const (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (r : Nat)
    (ls : List Level)
    (m : CheckedMemberA)
    (u : Level)
    (hres : E.members r = some m)
    (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hT : HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u))
    (ih_hT : TyGoal M E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u)),
    TyGoal M E I n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA)

def Ty_pi (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u : Level)
    (B : ExprA)
    (v : Level)
    (hA : HasTyA E I n Γ A (.sort u))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (ih_hA : TyGoal M E I n Γ A (.sort u))
    (ih_hB : TyGoal M E I n (.assumption A :: Γ) B (.sort v)),
    TyGoal M E I n Γ (.pi A u B v) (.sort (.imax u v))

def Ty_lam (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u : Level)
    (body B : ExprA)
    (v : Level)
    (hA : HasTyA E I n Γ A (.sort u))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hbody : HasTyA E I n (.assumption A :: Γ) body B)
    (ih_hA : TyGoal M E I n Γ A (.sort u))
    (ih_hB : TyGoal M E I n (.assumption A :: Γ) B (.sort v))
    (ih_hbody : TyGoal M E I n (.assumption A :: Γ) body B),
    TyGoal M E I n Γ (.lam A u body) (.pi A u B v)

def Ty_app (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f a A B : ExprA)
    (u v w : Level)
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (hf : HasTyA E I n Γ f (.pi A u B v))
    (ha : HasTyA E I n Γ a A)
    (ih_hB : TyGoal M E I n (.assumption A :: Γ) B (.sort v))
    (ih_hTy : TyGoal M E I n Γ (instantiate0A a B) (.sort w))
    (ih_hf : TyGoal M E I n Γ f (.pi A u B v))
    (ih_ha : TyGoal M E I n Γ a A),
    TyGoal M E I n Γ (.app f a) (instantiate0A a B)

def Ty_letE (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u w : Level)
    (value B body : ExprA)
    (hA : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ value A)
    (hTy : HasTyA E I n Γ (instantiate0A value B) (.sort w))
    (hb : HasTyA E I n (.letBinding A value :: Γ) body B)
    (ih_hA : TyGoal M E I n Γ A (.sort u))
    (ih_hv : TyGoal M E I n Γ value A)
    (ih_hTy : TyGoal M E I n Γ (instantiate0A value B) (.sort w))
    (ih_hb : TyGoal M E I n (.letBinding A value :: Γ) body B),
    TyGoal M E I n Γ (.letE A value body) (instantiate0A value B)

def Ty_lit (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (t : Nat)
    (T : ExprA)
    (hexp : HasTyA E I n Γ (natExpandA t) T)
    (ih_hexp : TyGoal M E I n Γ (natExpandA t) T),
    TyGoal M E I n Γ (.lit t) T

def Ty_conv (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (e A B : ExprA)
    (l u : Level)
    (h : HasTyA E I n Γ e A)
    (hAl : HasTyA E I n Γ A (.sort l))
    (hlu : eqN l u)
    (hB : HasTyA E I n Γ B (.sort u))
    (hc : ConvA E I n Γ A B (.sort u))
    (ih_h : TyGoal M E I n Γ e A)
    (ih_hAl : TyGoal M E I n Γ A (.sort l))
    (ih_hB : TyGoal M E I n Γ B (.sort u))
    (ih_hc : ConvGoal M E I n Γ A B (.sort u)),
    TyGoal M E I n Γ e B

def Conv_refl (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a A : ExprA)
    (h : HasTyA E I n Γ a A)
    (ih_h : TyGoal M E I n Γ a A),
    ConvGoal M E I n Γ a a A

def Conv_symm (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a b A : ExprA)
    (h : ConvA E I n Γ a b A)
    (ih_h : ConvGoal M E I n Γ a b A),
    ConvGoal M E I n Γ b a A

def Conv_trans (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a b c A : ExprA)
    (h1 : ConvA E I n Γ a b A)
    (h2 : ConvA E I n Γ b c A)
    (ih_h1 : ConvGoal M E I n Γ a b A)
    (ih_h2 : ConvGoal M E I n Γ b c A),
    ConvGoal M E I n Γ a c A

def Conv_beta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u : Level)
    (body arg B : ExprA)
    (hA : HasTyA E I n Γ A (.sort u))
    (hbody : HasTyA E I n (.assumption A :: Γ) body B)
    (harg : HasTyA E I n Γ arg A)
    (hred : HasTyA E I n Γ (instantiate0A arg body) (instantiate0A arg B))
    (ih_hA : TyGoal M E I n Γ A (.sort u))
    (ih_hbody : TyGoal M E I n (.assumption A :: Γ) body B)
    (ih_harg : TyGoal M E I n Γ arg A)
    (ih_hred : TyGoal M E I n Γ (instantiate0A arg body) (instantiate0A arg B)),
    ConvGoal M E I n Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B)

def Conv_zeta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A value body B : ExprA)
    (u : Level)
    (hA : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ value A)
    (hb : HasTyA E I n (.letBinding A value :: Γ) body B)
    (hred : HasTyA E I n Γ (instantiate0A value body) (instantiate0A value B))
    (ih_hA : TyGoal M E I n Γ A (.sort u))
    (ih_hv : TyGoal M E I n Γ value A)
    (ih_hb : TyGoal M E I n (.letBinding A value :: Γ) body B)
    (ih_hred : TyGoal M E I n Γ (instantiate0A value body) (instantiate0A value B)),
    ConvGoal M E I n Γ (.letE A value body) (instantiate0A value body) (instantiate0A value B)

def Conv_zetaLocal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (i : Nat)
    (A v : ExprA)
    (hval : lookupValueA Γ i = some v)
    (hty : lookupTypeA Γ i = some A)
    (hv : HasTyA E I n Γ v A)
    (ih_hv : TyGoal M E I n Γ v A),
    ConvGoal M E I n Γ (.bvar i) v A

def Conv_delta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (r : Nat)
    (ls : List Level)
    (m : CheckedMemberA)
    (b : ExprA)
    (hres : E.members r = some m)
    (hbody : m.bodyA = some b)
    (htr : transparent m.mclass = true)
    (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA))
    (ih_hb : TyGoal M E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)),
    ConvGoal M E I n Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)

def Conv_iota (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (lhs rhs T : ExprA)
    (h : I.rel E Γ lhs rhs)
    (hlhs : HasTyA E I n Γ lhs T)
    (hrhs : HasTyA E I n Γ rhs T)
    (ih_hlhs : TyGoal M E I n Γ lhs T)
    (ih_hrhs : TyGoal M E I n Γ rhs T),
    ConvGoal M E I n Γ lhs rhs T

def Conv_structIota (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f a rhs e T : ExprA)
    (hrec : recAtMajorA E f = true)
    (hs : structArmA E f a = some e)
    (h : I.fn (.app f a) = some rhs)
    (hlhs : HasTyA E I n Γ (.app f a) T)
    (hrhs : HasTyA E I n Γ rhs T)
    (hcv : ConvA E I n Γ rhs e T)
    (ih_hlhs : TyGoal M E I n Γ (.app f a) T)
    (ih_hrhs : TyGoal M E I n Γ rhs T)
    (ih_hcv : ConvGoal M E I n Γ rhs e T),
    ConvGoal M E I n Γ (.app f a) rhs T

def Conv_lit (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (t : Nat)
    (T : ExprA)
    (hexp : HasTyA E I n Γ (natExpandA t) T)
    (ih_hexp : TyGoal M E I n Γ (natExpandA t) T),
    ConvGoal M E I n Γ (.lit t) (natExpandA t) T

def Conv_app (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f g a b A B : ExprA)
    (u v : Level)
    (h1 : ConvA E I n Γ f g (.pi A u B v))
    (h2 : ConvA E I n Γ a b A)
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hrt : HasTyA E I n Γ (.app g b) (instantiate0A a B))
    (ih_h1 : ConvGoal M E I n Γ f g (.pi A u B v))
    (ih_h2 : ConvGoal M E I n Γ a b A)
    (ih_hB : TyGoal M E I n (.assumption A :: Γ) B (.sort v))
    (ih_hrt : TyGoal M E I n Γ (.app g b) (instantiate0A a B)),
    ConvGoal M E I n Γ (.app f a) (.app g b) (instantiate0A a B)

def Conv_lam (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A A' b b' B : ExprA)
    (u u' v : Level)
    (hu : eqN u u')
    (hA : ConvA E I n Γ A A' (.sort u))
    (hb : ConvA E I n (.assumption A :: Γ) b b' B)
    (hrt : HasTyA E I n Γ (.lam A' u' b') (.pi A u B v))
    (ih_hA : ConvGoal M E I n Γ A A' (.sort u))
    (ih_hb : ConvGoal M E I n (.assumption A :: Γ) b b' B)
    (ih_hrt : TyGoal M E I n Γ (.lam A' u' b') (.pi A u B v)),
    ConvGoal M E I n Γ (.lam A u b) (.lam A' u' b') (.pi A u B v)

def Conv_pi (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A A' B B' : ExprA)
    (u u' v v' : Level)
    (hu : eqN u u')
    (hv : eqN v v')
    (hA : ConvA E I n Γ A A' (.sort u))
    (hB : ConvA E I n (.assumption A :: Γ) B B' (.sort v))
    (hrt : HasTyA E I n Γ (.pi A' u' B' v') (.sort (.imax u v)))
    (ih_hA : ConvGoal M E I n Γ A A' (.sort u))
    (ih_hB : ConvGoal M E I n (.assumption A :: Γ) B B' (.sort v))
    (ih_hrt : TyGoal M E I n Γ (.pi A' u' B' v') (.sort (.imax u v))),
    ConvGoal M E I n Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v))

def Conv_letE (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A A' v v' b b' B : ExprA)
    (u : Level)
    (hA : ConvA E I n Γ A A' (.sort u))
    (hv : ConvA E I n Γ v v' A)
    (hb : ConvA E I n (.letBinding A v :: Γ) b b' B)
    (hrt : HasTyA E I n Γ (.letE A' v' b') (instantiate0A v B))
    (ih_hA : ConvGoal M E I n Γ A A' (.sort u))
    (ih_hv : ConvGoal M E I n Γ v v' A)
    (ih_hb : ConvGoal M E I n (.letBinding A v :: Γ) b b' B)
    (ih_hrt : TyGoal M E I n Γ (.letE A' v' b') (instantiate0A v B)),
    ConvGoal M E I n Γ (.letE A v b) (.letE A' v' b') (instantiate0A v B)

def Conv_sorts (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (l₁ l₂ : Level)
    (h : eqN l₁ l₂),
    ConvGoal M E I n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))

def Conv_consts (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (r : Nat)
    (ls ls' : List Level)
    (m : CheckedMemberA)
    (hres : E.members r = some m)
    (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    (hrt : HasTyA E I n Γ (.const r ls') (instantiateLevelsA ls m.mtypeA))
    (ih_hrt : TyGoal M E I n Γ (.const r ls') (instantiateLevelsA ls m.mtypeA)),
    ConvGoal M E I n Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA)

def Conv_eta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f A B : ExprA)
    (u v : Level)
    (h : HasTyA E I n Γ f (.pi A u B v))
    (hrt : HasTyA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v))
    (ih_h : TyGoal M E I n Γ f (.pi A u B v))
    (ih_hrt : TyGoal M E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v)),
    ConvGoal M E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) f (.pi A u B v)

def Conv_irr (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (P p q : ExprA)
    (hP : HasTyA E I n Γ P (.sort .zero))
    (hp : HasTyA E I n Γ p P)
    (hq : HasTyA E I n Γ q P)
    (ih_hP : TyGoal M E I n Γ P (.sort .zero))
    (ih_hp : TyGoal M E I n Γ p P)
    (ih_hq : TyGoal M E I n Γ q P),
    ConvGoal M E I n Γ p q P

def Conv_tyConv (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a b A A' : ExprA)
    (l l' u : Level)
    (h : ConvA E I n Γ a b A)
    (hAl : HasTyA E I n Γ A (.sort l))
    (hlu : eqN l u)
    (hA'l : HasTyA E I n Γ A' (.sort l'))
    (hl'u : eqN l' u)
    (hA : ConvA E I n Γ A A' (.sort u))
    (ih_h : ConvGoal M E I n Γ a b A)
    (ih_hAl : TyGoal M E I n Γ A (.sort l))
    (ih_hA'l : TyGoal M E I n Γ A' (.sort l'))
    (ih_hA : ConvGoal M E I n Γ A A' (.sort u)),
    ConvGoal M E I n Γ a b A'

structure Arms (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop where
  Ty_sort : Ty_sort M E I n
  Ty_bvar : Ty_bvar M E I n
  Ty_const : Ty_const M E I n
  Ty_pi : Ty_pi M E I n
  Ty_lam : Ty_lam M E I n
  Ty_app : Ty_app M E I n
  Ty_letE : Ty_letE M E I n
  Ty_lit : Ty_lit M E I n
  Ty_conv : Ty_conv M E I n
  Conv_refl : Conv_refl M E I n
  Conv_symm : Conv_symm M E I n
  Conv_trans : Conv_trans M E I n
  Conv_beta : Conv_beta M E I n
  Conv_zeta : Conv_zeta M E I n
  Conv_zetaLocal : Conv_zetaLocal M E I n
  Conv_delta : Conv_delta M E I n
  Conv_iota : Conv_iota M E I n
  Conv_structIota : Conv_structIota M E I n
  Conv_lit : Conv_lit M E I n
  Conv_app : Conv_app M E I n
  Conv_lam : Conv_lam M E I n
  Conv_pi : Conv_pi M E I n
  Conv_letE : Conv_letE M E I n
  Conv_sorts : Conv_sorts M E I n
  Conv_consts : Conv_consts M E I n
  Conv_eta : Conv_eta M E I n
  Conv_irr : Conv_irr M E I n
  Conv_tyConv : Conv_tyConv M E I n

/-- Assembly of the original mutual constructor induction. This consumes
all 28 fields and is not an inhabitant of Arms. -/
theorem fundamental_of_arms {M : AnnSemantics} {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (A : Arms M E I n) : Fundamental M E I n := by
  constructor
  · intro Γ e T h
    exact @HasTyA.rec E I n
      (fun Γ e T _ => TyGoal M E I n Γ e T)
      (fun Γ a b T _ => ConvGoal M E I n Γ a b T)
      A.Ty_sort
      A.Ty_bvar
      A.Ty_const
      A.Ty_pi
      A.Ty_lam
      A.Ty_app
      A.Ty_letE
      A.Ty_lit
      A.Ty_conv
      A.Conv_refl
      A.Conv_symm
      A.Conv_trans
      A.Conv_beta
      A.Conv_zeta
      A.Conv_zetaLocal
      A.Conv_delta
      A.Conv_iota
      A.Conv_structIota
      A.Conv_lit
      A.Conv_app
      A.Conv_lam
      A.Conv_pi
      A.Conv_letE
      A.Conv_sorts
      A.Conv_consts
      A.Conv_eta
      A.Conv_irr
      A.Conv_tyConv
      Γ e T h
  · intro Γ a b T h
    exact @ConvA.rec E I n
      (fun Γ e T _ => TyGoal M E I n Γ e T)
      (fun Γ a b T _ => ConvGoal M E I n Γ a b T)
      A.Ty_sort
      A.Ty_bvar
      A.Ty_const
      A.Ty_pi
      A.Ty_lam
      A.Ty_app
      A.Ty_letE
      A.Ty_lit
      A.Ty_conv
      A.Conv_refl
      A.Conv_symm
      A.Conv_trans
      A.Conv_beta
      A.Conv_zeta
      A.Conv_zetaLocal
      A.Conv_delta
      A.Conv_iota
      A.Conv_structIota
      A.Conv_lit
      A.Conv_app
      A.Conv_lam
      A.Conv_pi
      A.Conv_letE
      A.Conv_sorts
      A.Conv_consts
      A.Conv_eta
      A.Conv_irr
      A.Conv_tyConv
      Γ a b T h

end Rcic.Declarative.Ann.LR3.TypedArms
