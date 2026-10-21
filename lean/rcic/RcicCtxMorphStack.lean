import rcic.RcicTypedSubst
import rcic.RcicTypedSubstLet
import rcic.RcicTypedWeaken
import rcic.RcicParRedTSubst

/-!
# Context-morphism stacks (W-X-SUBST S0 §5, #7107 — the `.val` route of the lazy substitution nodes)

A lazy `subst0`/`substLet` node on a provenance star has to materialize through whatever sits under
it — in particular through a lazy `wk d c` at any `c` and through further lazy substitutions. Pushing
ONE substitution through ONE weakening needs a commutation that does not exist in general (when the
substituted value mentions the inserted variable, `j < c`), and pushing a substitution through a
substitution needs a simultaneous substitution. Both are avoided by never commuting anything: the
pending transports are kept as a STACK of context morphisms, applied in order to the producers' plain
pieces (`HasTyT`/`ConvT`/`TyConvT`), each entry by its landed transport lemma —
`hasTyT_substS`/`hasTyT_substLetS`/`hasTyTWeaken` and the `ConvT`/`TyConvT` twins. Only `hcl`/`hinst`
are consumed. Under a binder the stack shifts entry-wise (`under`): substitution indices by one with the
value's typing by `subst_hvty_wk`, insertion cutoffs by one.

`apply` is the syntactic action; `apply_sort`/`apply_pi` are the two shape laws the producers need.
`closure_claim` 0.
-/

namespace Rcic.Declarative

variable {E : ResolvedEnv} {n : Nat}

/-- a composite context morphism `Γ ⟶ Γ'`: a stack of substitutions (assumption / let) and
    insertions, applied head first. -/
inductive CtxMorph (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type where
  | nil {Γ : LCtx} : CtxMorph E n Γ Γ
  | sub {Γ Γ' : LCtx} {t v : Expr Nat} (j : Nat)
      (hget : Γ[j]? = some (.assumption t))
      (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (σ : CtxMorph E n (substRemove v j Γ) Γ') : CtxMorph E n Γ Γ'
  | subLet {Γ Γ' : LCtx} {t w : Expr Nat} (j : Nat)
      (hget : Γ[j]? = some (.letBinding t w))
      (hv : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
      (σ : CtxMorph E n (substRemove w j Γ) Γ') : CtxMorph E n Γ Γ'
  | ins {Γ Γ' : LCtx} (d : LocalDecl) (c : Nat)
      (σ : CtxMorph E n (insertAt d c Γ) Γ') : CtxMorph E n Γ Γ'

/-- the syntactic action, head first. -/
def CtxMorph.apply : {Γ Γ' : LCtx} → CtxMorph E n Γ Γ' → Expr Nat → Expr Nat
  | _, _, .nil, e => e
  | _, _, @CtxMorph.sub _ _ _ _ _ v j _ _ σ, e => σ.apply (instantiate j (lift 0 j v) e)
  | _, _, @CtxMorph.subLet _ _ _ _ _ w j _ _ σ, e => σ.apply (instantiate j (lift 0 j w) e)
  | _, _, .ins _ c σ, e => σ.apply (lift c 1 e)

/-- a `def` (not a theorem) so that a concrete stack's shape law unfolds to `rfl` and the casts
    along it compute. -/
def CtxMorph.apply_sort : {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') → (u : Level) →
    σ.apply (.sort u) = .sort u
  | _, _, .nil, _ => rfl
  | _, _, @CtxMorph.sub _ _ _ _ _ _ _ _ _ σ, u => σ.apply_sort u
  | _, _, @CtxMorph.subLet _ _ _ _ _ _ _ _ _ σ, u => σ.apply_sort u
  | _, _, .ins _ _ σ, u => σ.apply_sort u

/-- Constants are unchanged by every entry of the stack. -/
def CtxMorph.apply_const : {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') →
    (r : Nat) → (ls : List Level) → σ.apply (.const r ls) = .const r ls
  | _, _, .nil, _, _ => rfl
  | _, _, @CtxMorph.sub _ _ _ _ _ _ _ _ _ σ, r, ls => σ.apply_const r ls
  | _, _, @CtxMorph.subLet _ _ _ _ _ _ _ _ _ σ, r, ls => σ.apply_const r ls
  | _, _, .ins _ _ σ, r, ls => σ.apply_const r ls

/-- Literal syntax is unchanged by every entry of the stack. -/
def CtxMorph.apply_lit : {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') → (t : Nat) →
    σ.apply (.lit t) = .lit t
  | _, _, .nil, _ => rfl
  | _, _, @CtxMorph.sub _ _ _ _ _ _ _ _ _ σ, t => σ.apply_lit t
  | _, _, @CtxMorph.subLet _ _ _ _ _ _ _ _ _ σ, t => σ.apply_lit t
  | _, _, .ins _ _ σ, t => σ.apply_lit t

/-- A literal expansion is closed under each queued substitution or insertion. -/
def CtxMorph.apply_natExpand : {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') → (t : Nat) →
    σ.apply (natExpand t) = natExpand t
  | _, _, .nil, _ => rfl
  | _, _, @CtxMorph.sub _ _ _ _ _ v j _ _ σ, t =>
      (congrArg σ.apply (natExpand_instantiate j (lift 0 j v) t)).trans (σ.apply_natExpand t)
  | _, _, @CtxMorph.subLet _ _ _ _ _ w j _ _ σ, t =>
      (congrArg σ.apply (natExpand_instantiate j (lift 0 j w) t)).trans (σ.apply_natExpand t)
  | _, _, .ins _ c σ, t =>
      (congrArg σ.apply (natExpand_lift c 1 t)).trans (σ.apply_natExpand t)

/-- the stack one assumption binder deeper. -/
def CtxMorph.under (hcl : EnvClosed E) : {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') →
    (A : Expr Nat) → CtxMorph E n (.assumption A :: Γ) (.assumption (σ.apply A) :: Γ')
  | _, _, .nil, _ => .nil
  | _, _, @CtxMorph.sub _ _ _ _ t v j hget hv σ, A =>
      .sub (t := t) (v := v) (j + 1) (by simpa using hget)
        (subst_hvty_wk (.assumption A) hcl hv)
        (σ.under hcl (instantiate j (lift 0 j v) A))
  | _, _, @CtxMorph.subLet _ _ _ _ t w j hget hv σ, A =>
      .subLet (t := t) (w := w) (j + 1) (by simpa using hget)
        (subst_hvty_wk (.assumption A) hcl hv)
        (σ.under hcl (instantiate j (lift 0 j w) A))
  | _, _, .ins d c σ, A => .ins d (c + 1) (σ.under hcl (lift c 1 A))

/-- the action on a Π: the domain by the stack, the codomain by the shifted stack — whose
    binder annotation is irrelevant to the action (`A₀` arbitrary). -/
theorem CtxMorph.apply_pi (hcl : EnvClosed E) : {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') →
    (A B A₀ : Expr Nat) → σ.apply (.pi A B) = .pi (σ.apply A) ((σ.under hcl A₀).apply B)
  | _, _, .nil, _, _, _ => rfl
  | _, _, @CtxMorph.sub _ _ _ _ _ v j _ _ σ, A, B, A₀ => by
      show σ.apply (.pi (instantiate j (lift 0 j v) A)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B)) = _
      rw [σ.apply_pi hcl _ _ (instantiate j (lift 0 j v) A₀),
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v]
      rfl
  | _, _, @CtxMorph.subLet _ _ _ _ _ w j _ _ σ, A, B, A₀ => by
      show σ.apply (.pi (instantiate j (lift 0 j w) A)
          (instantiate (j + 1) (lift 0 1 (lift 0 j w)) B)) = _
      rw [σ.apply_pi hcl _ _ (instantiate j (lift 0 j w) A₀),
        lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w]
      rfl
  | _, _, .ins d c σ, A, B, A₀ => by
      show σ.apply (.pi (lift c 1 A) (lift (c + 1) 1 B)) = _
      rw [σ.apply_pi hcl _ _ (lift c 1 A₀)]
      rfl

/-! ### the three transports -/

/-- typing along the stack. -/
def CtxMorph.hasTyT (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') → {e A : Expr Nat} →
    HasTyT E n Γ e A → HasTyT E n Γ' (σ.apply e) (σ.apply A)
  | _, _, .nil, _, _, h => h
  | _, _, @CtxMorph.sub _ _ _ _ t v _ hget hv σ, _, _, h =>
      σ.hasTyT hcl hinst (hasTyT_substS hcl hinst v t h hget hv)
  | _, _, @CtxMorph.subLet _ _ _ _ t w _ hget hv σ, _, _, h =>
      σ.hasTyT hcl hinst (hasTyT_substLetS hcl hinst t w h hget hv)
  | _, _, .ins d _ σ, _, _, h => σ.hasTyT hcl hinst (hasTyTWeaken d hcl h)

/-- conversion along the stack. -/
def CtxMorph.convT (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') → {a b T : Expr Nat} →
    ConvT E n Γ a b T → ConvT E n Γ' (σ.apply a) (σ.apply b) (σ.apply T)
  | _, _, .nil, _, _, _, h => h
  | _, _, @CtxMorph.sub _ _ _ _ t v _ hget hv σ, _, _, _, h =>
      σ.convT hcl hinst (convT_substS hcl hinst v t h hget hv)
  | _, _, @CtxMorph.subLet _ _ _ _ t w _ hget hv σ, _, _, _, h =>
      σ.convT hcl hinst (convT_substLetS hcl hinst t w h hget hv)
  | _, _, .ins d _ σ, _, _, _, h => σ.convT hcl hinst (convTWeaken d hcl h)

/-- type conversion along the stack. -/
def CtxMorph.tyConvT (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ Γ' : LCtx} → (σ : CtxMorph E n Γ Γ') → {A A' : Expr Nat} →
    TyConvT E n Γ A A' → TyConvT E n Γ' (σ.apply A) (σ.apply A')
  | _, _, .nil, _, _, h => h
  | _, _, @CtxMorph.sub _ _ _ _ t v _ hget hv σ, _, _, h =>
      σ.tyConvT hcl hinst (tyConvT_substS hcl hinst v t h hget hv)
  | _, _, @CtxMorph.subLet _ _ _ _ t w _ hget hv σ, _, _, h =>
      σ.tyConvT hcl hinst (tyConvT_substLetS hcl hinst t w h hget hv)
  | _, _, .ins d _ σ, _, _, h => σ.tyConvT hcl hinst (tyConvTWeaken d hcl h)

/-! ### casts along the shape laws -/

def hasTyT_castE {Γ : LCtx} {e A A' : Expr Nat} (hA : A = A') (h : HasTyT E n Γ e A) :
    HasTyT E n Γ e A' := hA ▸ h

def hasTyT_castEA {Γ : LCtx} {e e' A A' : Expr Nat} (he : e = e') (hA : A = A')
    (h : HasTyT E n Γ e A) : HasTyT E n Γ e' A' := by subst he; subst hA; exact h

def convT_castT {Γ : LCtx} {a b T T' : Expr Nat} (hT : T = T') (h : ConvT E n Γ a b T) :
    ConvT E n Γ a b T' := hT ▸ h

def tyConvT_castL {Γ : LCtx} {A A' B : Expr Nat} (hA : A = A') (h : TyConvT E n Γ A B) :
    TyConvT E n Γ A' B := hA ▸ h

def parRedT_cast {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {Γ : LCtx} {a a' b b' T : Expr Nat} (ha : a = a') (hb : b = b')
    (h : ParRedT PEq E n Γ a b T) : ParRedT PEq E n Γ a' b' T := by
  subst ha; subst hb; exact h

/-! ### pin: a two-entry stack (`ins` then `sub`) acting on a typing -/

section Pin

private def pinCl : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h
private def pinSS : EnvMembersSubstStable emptyEnv := fun _ _ h => Option.noConfusion h

/-- `Sort 0 : Sort 1` at `[]`. -/
private def s01 : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := .sort _ _

/-- insert `x : Sort 1` at 0, then substitute it by `Sort 0`: the composite is the identity on
    closed terms. -/
def pinMorph : CtxMorph emptyEnv 0 [] [] :=
  .ins (.assumption (.sort (.succ .zero))) 0
    (.sub (t := .sort (.succ .zero)) (v := .sort .zero) 0 rfl s01 .nil)

theorem pinMorph_apply : pinMorph.apply (.sort .zero) = .sort .zero := rfl

/-- the transported typing lands at the original statement (the action computes to the identity). -/
def pinMorph_hasTyT : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  pinMorph.hasTyT pinCl pinSS s01

end Pin

end Rcic.Declarative

#print axioms Rcic.Declarative.CtxMorph.apply_sort
#print axioms Rcic.Declarative.CtxMorph.apply_const
#print axioms Rcic.Declarative.CtxMorph.apply_lit
#print axioms Rcic.Declarative.CtxMorph.apply_natExpand
#print axioms Rcic.Declarative.CtxMorph.apply_pi
#print axioms Rcic.Declarative.CtxMorph.hasTyT
#print axioms Rcic.Declarative.CtxMorph.convT
#print axioms Rcic.Declarative.CtxMorph.tyConvT
#print axioms Rcic.Declarative.pinMorph_hasTyT
