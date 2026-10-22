import rcic.RcicAnnLR3PairedStatements

/-!
# Exact 9+19 constructor contracts for the paired fundamental statement

Each contract retains exactly the source premises and one paired induction
hypothesis for every original typing or conversion child. Only the goal
family changes from `TypedArms`; the source derivation constructors and
all environment, level, and context quantifiers remain unchanged.

The assembler consumes all 28 fields. Five generic fields are supplied
below from universe and PER algebra. Two further fields consume the
explicit universe-to-element transport law; proof irrelevance consumes
the explicit level-zero irrelevance law. The remaining fields still
require compositional source semantics; no complete paired dispatcher or
global source soundness is asserted. The neutral constant fixture is a
separate unary result and does not fill the paired all-environment
constant field. No reverse K condition occurs in any contract.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Rcic.Declarative.Ann.LR3.PairedArms
open Rcic.Declarative
open TypedStatements PairedStatements
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

def Ty_sort (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (l : Level),
    PairedTyGoal M E I n Γ (.sort l) (.sort (.succ l))

def Ty_bvar (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (i : Nat)
    (A : ExprA)
    (u : Level)
    (h : lookupTypeA Γ i = some A)
    (hA : HasTyA E I n Γ A (.sort u))
    (ih_hA : PairedTyGoal M E I n Γ A (.sort u)),
    PairedTyGoal M E I n Γ (.bvar i) A

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
    (ih_hT : PairedTyGoal M E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u)),
    PairedTyGoal M E I n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA)

def Ty_pi (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u : Level)
    (B : ExprA)
    (v : Level)
    (hA : HasTyA E I n Γ A (.sort u))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (ih_hA : PairedTyGoal M E I n Γ A (.sort u))
    (ih_hB : PairedTyGoal M E I n (.assumption A :: Γ) B (.sort v)),
    PairedTyGoal M E I n Γ (.pi A u B v) (.sort (.imax u v))

def Ty_lam (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u : Level)
    (body B : ExprA)
    (v : Level)
    (hA : HasTyA E I n Γ A (.sort u))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hbody : HasTyA E I n (.assumption A :: Γ) body B)
    (ih_hA : PairedTyGoal M E I n Γ A (.sort u))
    (ih_hB : PairedTyGoal M E I n (.assumption A :: Γ) B (.sort v))
    (ih_hbody : PairedTyGoal M E I n (.assumption A :: Γ) body B),
    PairedTyGoal M E I n Γ (.lam A u body) (.pi A u B v)

def Ty_app (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f a A B : ExprA)
    (u v w : Level)
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (hf : HasTyA E I n Γ f (.pi A u B v))
    (ha : HasTyA E I n Γ a A)
    (ih_hB : PairedTyGoal M E I n (.assumption A :: Γ) B (.sort v))
    (ih_hTy : PairedTyGoal M E I n Γ (instantiate0A a B) (.sort w))
    (ih_hf : PairedTyGoal M E I n Γ f (.pi A u B v))
    (ih_ha : PairedTyGoal M E I n Γ a A),
    PairedTyGoal M E I n Γ (.app f a) (instantiate0A a B)

def Ty_letE (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u w : Level)
    (value B body : ExprA)
    (hA : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ value A)
    (hTy : HasTyA E I n Γ (instantiate0A value B) (.sort w))
    (hb : HasTyA E I n (.letBinding A value :: Γ) body B)
    (ih_hA : PairedTyGoal M E I n Γ A (.sort u))
    (ih_hv : PairedTyGoal M E I n Γ value A)
    (ih_hTy : PairedTyGoal M E I n Γ (instantiate0A value B) (.sort w))
    (ih_hb : PairedTyGoal M E I n (.letBinding A value :: Γ) body B),
    PairedTyGoal M E I n Γ (.letE A value body) (instantiate0A value B)

def Ty_lit (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (t : Nat)
    (T : ExprA)
    (hexp : HasTyA E I n Γ (natExpandA t) T)
    (ih_hexp : PairedTyGoal M E I n Γ (natExpandA t) T),
    PairedTyGoal M E I n Γ (.lit t) T

def Ty_conv (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (e A B : ExprA)
    (l u : Level)
    (h : HasTyA E I n Γ e A)
    (hAl : HasTyA E I n Γ A (.sort l))
    (hlu : eqN l u)
    (hB : HasTyA E I n Γ B (.sort u))
    (hc : ConvA E I n Γ A B (.sort u))
    (ih_h : PairedTyGoal M E I n Γ e A)
    (ih_hAl : PairedTyGoal M E I n Γ A (.sort l))
    (ih_hB : PairedTyGoal M E I n Γ B (.sort u))
    (ih_hc : PairedConvGoal M E I n Γ A B (.sort u)),
    PairedTyGoal M E I n Γ e B

def Conv_refl (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a A : ExprA)
    (h : HasTyA E I n Γ a A)
    (ih_h : PairedTyGoal M E I n Γ a A),
    PairedConvGoal M E I n Γ a a A

def Conv_symm (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a b A : ExprA)
    (h : ConvA E I n Γ a b A)
    (ih_h : PairedConvGoal M E I n Γ a b A),
    PairedConvGoal M E I n Γ b a A

def Conv_trans (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (a b c A : ExprA)
    (h1 : ConvA E I n Γ a b A)
    (h2 : ConvA E I n Γ b c A)
    (ih_h1 : PairedConvGoal M E I n Γ a b A)
    (ih_h2 : PairedConvGoal M E I n Γ b c A),
    PairedConvGoal M E I n Γ a c A

def Conv_beta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A : ExprA)
    (u : Level)
    (body arg B : ExprA)
    (hA : HasTyA E I n Γ A (.sort u))
    (hbody : HasTyA E I n (.assumption A :: Γ) body B)
    (harg : HasTyA E I n Γ arg A)
    (hred : HasTyA E I n Γ (instantiate0A arg body) (instantiate0A arg B))
    (ih_hA : PairedTyGoal M E I n Γ A (.sort u))
    (ih_hbody : PairedTyGoal M E I n (.assumption A :: Γ) body B)
    (ih_harg : PairedTyGoal M E I n Γ arg A)
    (ih_hred : PairedTyGoal M E I n Γ (instantiate0A arg body) (instantiate0A arg B)),
    PairedConvGoal M E I n Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B)

def Conv_zeta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A value body B : ExprA)
    (u : Level)
    (hA : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ value A)
    (hb : HasTyA E I n (.letBinding A value :: Γ) body B)
    (hred : HasTyA E I n Γ (instantiate0A value body) (instantiate0A value B))
    (ih_hA : PairedTyGoal M E I n Γ A (.sort u))
    (ih_hv : PairedTyGoal M E I n Γ value A)
    (ih_hb : PairedTyGoal M E I n (.letBinding A value :: Γ) body B)
    (ih_hred : PairedTyGoal M E I n Γ (instantiate0A value body) (instantiate0A value B)),
    PairedConvGoal M E I n Γ (.letE A value body) (instantiate0A value body) (instantiate0A value B)

def Conv_zetaLocal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (i : Nat)
    (A v : ExprA)
    (hval : lookupValueA Γ i = some v)
    (hty : lookupTypeA Γ i = some A)
    (hv : HasTyA E I n Γ v A)
    (ih_hv : PairedTyGoal M E I n Γ v A),
    PairedConvGoal M E I n Γ (.bvar i) v A

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
    (ih_hb : PairedTyGoal M E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)),
    PairedConvGoal M E I n Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)

def Conv_iota (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (lhs rhs T : ExprA)
    (h : I.rel E Γ lhs rhs)
    (hlhs : HasTyA E I n Γ lhs T)
    (hrhs : HasTyA E I n Γ rhs T)
    (ih_hlhs : PairedTyGoal M E I n Γ lhs T)
    (ih_hrhs : PairedTyGoal M E I n Γ rhs T),
    PairedConvGoal M E I n Γ lhs rhs T

def Conv_structIota (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f a rhs e T : ExprA)
    (hrec : recAtMajorA E f = true)
    (hs : structArmA E f a = some e)
    (h : I.fn (.app f a) = some rhs)
    (hlhs : HasTyA E I n Γ (.app f a) T)
    (hrhs : HasTyA E I n Γ rhs T)
    (hcv : ConvA E I n Γ rhs e T)
    (ih_hlhs : PairedTyGoal M E I n Γ (.app f a) T)
    (ih_hrhs : PairedTyGoal M E I n Γ rhs T)
    (ih_hcv : PairedConvGoal M E I n Γ rhs e T),
    PairedConvGoal M E I n Γ (.app f a) rhs T

def Conv_lit (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (t : Nat)
    (T : ExprA)
    (hexp : HasTyA E I n Γ (natExpandA t) T)
    (ih_hexp : PairedTyGoal M E I n Γ (natExpandA t) T),
    PairedConvGoal M E I n Γ (.lit t) (natExpandA t) T

def Conv_app (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f g a b A B : ExprA)
    (u v : Level)
    (h1 : ConvA E I n Γ f g (.pi A u B v))
    (h2 : ConvA E I n Γ a b A)
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hrt : HasTyA E I n Γ (.app g b) (instantiate0A a B))
    (ih_h1 : PairedConvGoal M E I n Γ f g (.pi A u B v))
    (ih_h2 : PairedConvGoal M E I n Γ a b A)
    (ih_hB : PairedTyGoal M E I n (.assumption A :: Γ) B (.sort v))
    (ih_hrt : PairedTyGoal M E I n Γ (.app g b) (instantiate0A a B)),
    PairedConvGoal M E I n Γ (.app f a) (.app g b) (instantiate0A a B)

def Conv_lam (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A A' b b' B : ExprA)
    (u u' v : Level)
    (hu : eqN u u')
    (hA : ConvA E I n Γ A A' (.sort u))
    (hb : ConvA E I n (.assumption A :: Γ) b b' B)
    (hrt : HasTyA E I n Γ (.lam A' u' b') (.pi A u B v))
    (ih_hA : PairedConvGoal M E I n Γ A A' (.sort u))
    (ih_hb : PairedConvGoal M E I n (.assumption A :: Γ) b b' B)
    (ih_hrt : PairedTyGoal M E I n Γ (.lam A' u' b') (.pi A u B v)),
    PairedConvGoal M E I n Γ (.lam A u b) (.lam A' u' b') (.pi A u B v)

def Conv_pi (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A A' B B' : ExprA)
    (u u' v v' : Level)
    (hu : eqN u u')
    (hv : eqN v v')
    (hA : ConvA E I n Γ A A' (.sort u))
    (hB : ConvA E I n (.assumption A :: Γ) B B' (.sort v))
    (hrt : HasTyA E I n Γ (.pi A' u' B' v') (.sort (.imax u v)))
    (ih_hA : PairedConvGoal M E I n Γ A A' (.sort u))
    (ih_hB : PairedConvGoal M E I n (.assumption A :: Γ) B B' (.sort v))
    (ih_hrt : PairedTyGoal M E I n Γ (.pi A' u' B' v') (.sort (.imax u v))),
    PairedConvGoal M E I n Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v))

def Conv_letE (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (A A' v v' b b' B : ExprA)
    (u : Level)
    (hA : ConvA E I n Γ A A' (.sort u))
    (hv : ConvA E I n Γ v v' A)
    (hb : ConvA E I n (.letBinding A v :: Γ) b b' B)
    (hrt : HasTyA E I n Γ (.letE A' v' b') (instantiate0A v B))
    (ih_hA : PairedConvGoal M E I n Γ A A' (.sort u))
    (ih_hv : PairedConvGoal M E I n Γ v v' A)
    (ih_hb : PairedConvGoal M E I n (.letBinding A v :: Γ) b b' B)
    (ih_hrt : PairedTyGoal M E I n Γ (.letE A' v' b') (instantiate0A v B)),
    PairedConvGoal M E I n Γ (.letE A v b) (.letE A' v' b') (instantiate0A v B)

def Conv_sorts (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (l₁ l₂ : Level)
    (h : eqN l₁ l₂),
    PairedConvGoal M E I n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))

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
    (ih_hrt : PairedTyGoal M E I n Γ (.const r ls') (instantiateLevelsA ls m.mtypeA)),
    PairedConvGoal M E I n Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA)

def Conv_eta (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (f A B : ExprA)
    (u v : Level)
    (h : HasTyA E I n Γ f (.pi A u B v))
    (hrt : HasTyA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v))
    (ih_h : PairedTyGoal M E I n Γ f (.pi A u B v))
    (ih_hrt : PairedTyGoal M E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v)),
    PairedConvGoal M E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) f (.pi A u B v)

def Conv_irr (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA)
    (P p q : ExprA)
    (hP : HasTyA E I n Γ P (.sort .zero))
    (hp : HasTyA E I n Γ p P)
    (hq : HasTyA E I n Γ q P)
    (ih_hP : PairedTyGoal M E I n Γ P (.sort .zero))
    (ih_hp : PairedTyGoal M E I n Γ p P)
    (ih_hq : PairedTyGoal M E I n Γ q P),
    PairedConvGoal M E I n Γ p q P

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
    (ih_h : PairedConvGoal M E I n Γ a b A)
    (ih_hAl : PairedTyGoal M E I n Γ A (.sort l))
    (ih_hA'l : PairedTyGoal M E I n Γ A' (.sort l'))
    (ih_hA : PairedConvGoal M E I n Γ A A' (.sort u)),
    PairedConvGoal M E I n Γ a b A'

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
    (A : Arms M E I n) : PairedFundamental M E I n := by
  constructor
  · intro Γ e T h
    exact @HasTyA.rec E I n
      (fun Γ e T _ => PairedTyGoal M E I n Γ e T)
      (fun Γ a b T _ => PairedConvGoal M E I n Γ a b T)
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
      (fun Γ e T _ => PairedTyGoal M E I n Γ e T)
      (fun Γ a b T _ => PairedConvGoal M E I n Γ a b T)
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


/-- Universe images agree across related valuations at every level,
including levels whose evaluation is `none`. -/
theorem paired_sort_goal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA)
    (n : Nat) (Γ : LCtxA) (l : Level) :
    PairedTyGoal M E I n Γ (.sort l) (.sort (.succ l)) := by
  intro _ ν μ ρ σ hν _
  unfold PairedJudgment
  simp only [M.sort_image]
  rw [← eval_of_valuationRel hν l, ← eval_of_valuationRel hν (.succ l)]
  exact ⟨(eval ν (.succ l)).map Nat.succ,
    M.universePER (eval ν (.succ l)), M.universePER (eval ν (.succ l)),
    CodePair.diagonal (M.universe_code _), M.universe_member _⟩

theorem ty_sort_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) : Ty_sort M E I n :=
  paired_sort_goal M E I n

theorem conv_refl_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) : Conv_refl M E I n := by
  intro Γ a A h ih
  exact ih

/-- Symmetry swaps both semantic worlds before using the induction
hypothesis, so its conclusion has the requested orientation. -/
theorem conv_symm_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) : Conv_symm M E I n := by
  intro Γ a b A h ih hΓ ν μ ρ σ hν hρ
  exact (ih hΓ μ ν σ ρ hν.symm hρ.symm).symm

/-- The second induction hypothesis is used at the right diagonal. The
shared middle type code provides the required coherent transport. -/
theorem conv_trans_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) : Conv_trans M E I n := by
  intro Γ a b c A h1 h2 ih1 ih2 hΓ ν μ ρ σ hν hρ
  exact (ih1 hΓ ν μ ρ σ hν hρ).trans
    (ih2 hΓ μ μ σ σ (ValuationRel.refl μ) hρ.right_diagonal)

theorem conv_sorts_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) : Conv_sorts M E I n := by
  intro Γ l₁ l₂ h hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hc, hm⟩ := paired_sort_goal M E I n Γ l₁ hΓ ν μ ρ σ hν hρ
  have he : M.image μ Γ σ (.sort l₁) = M.image μ Γ σ (.sort l₂) := by
    rw [M.sort_image, M.sort_image, h μ]
  refine ⟨k, R, S, hc, ?_⟩
  rw [← he]
  exact hm

/-- Type conversion follows from the source conversion induction
hypothesis at both diagonal worlds and the explicit universe transport
law. All original source premises remain in the constructor contract. -/
theorem ty_conv_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) (U : UniverseTransport M.toCodeSystem) :
    Ty_conv M E I n := by
  intro Γ e A B l u h hAl hlu hB hc ih_h ih_hAl ih_hB ih_hc hΓ ν μ ρ σ hν hρ
  apply (ih_h hΓ ν μ ρ σ hν hρ).transport_type
  · exact PairedJudgment.related_types U
      (ih_hc hΓ ν ν ρ ρ (ValuationRel.refl ν) hρ.left_diagonal)
  · exact PairedJudgment.related_types U
      (ih_hc hΓ μ μ σ σ (ValuationRel.refl μ) hρ.right_diagonal)

theorem conv_tyConv_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) (U : UniverseTransport M.toCodeSystem) :
    Conv_tyConv M E I n := by
  intro Γ a b A A' l l' u h hAl hlu hA'l hl'u hA ih_h ih_hAl ih_hA'l ih_hA
    hΓ ν μ ρ σ hν hρ
  apply (ih_h hΓ ν μ ρ σ hν hρ).transport_type
  · exact PairedJudgment.related_types U
      (ih_hA hΓ ν ν ρ ρ (ValuationRel.refl ν) hρ.left_diagonal)
  · exact PairedJudgment.related_types U
      (ih_hA hΓ μ μ σ σ (ValuationRel.refl μ) hρ.right_diagonal)

/-- Source typing at `Sort 0` identifies the exact element-code level.
The explicit semantic irrelevance law then relates the two members. -/
theorem conv_irr_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) (J : PropIrrelevance M.toCodeSystem) :
    Conv_irr M E I n := by
  intro Γ P p q hP hp hq ih_hP ih_hp ih_hq hΓ ν μ ρ σ hν hρ
  have hlevel := sort_judgment_membership (ih_hP hΓ ν μ ρ σ hν hρ).left_typing
  obtain ⟨k, R, S, hc, hr⟩ := ih_hp hΓ ν μ ρ σ hν hρ
  obtain ⟨l, T, U, hd, hs⟩ := ih_hq hΓ ν μ ρ σ hν hρ
  have hk : k = some 0 :=
    sortMember_unique (M.level hc.left_code) hlevel.1 (M.defined hc.left_code)
  have hcode : M.Code (some 0) (M.image ν Γ ρ P) R := hk ▸ hc.left_code
  refine ⟨k, R, S, hc, J.relate hcode
    (TypedPER.left_member (M.lawful hc.left_code) hr) ?_⟩
  exact (M.coherent hd.left_code hc.left_code _ _).mp
    (TypedPER.right_member (M.lawful hd.left_code) hs)

/-- Diagonal extraction from a complete paired arm supplier. This consumes
the supplier; the supplied algebraic fields alone do not construct one. -/
theorem unary_fundamental_of_arms {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (A : Arms M E I n) : Fundamental M E I n :=
  fundamental_diagonal (fundamental_of_arms A)

end Rcic.Declarative.Ann.LR3.PairedArms
