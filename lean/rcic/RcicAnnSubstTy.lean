import rcic.RcicAnnLRFund

/-!
# M2-f (6a) — syntactic substitution and functionality, on the copy

`SubstTyA` is a typed parallel substitution from `Γ` into `Δ`: every declared
variable is sent to a term of its substituted type, and a let-bound variable is
sent to something convertible to the substituted value. `ConvSubstA` is a pair
of those, convertible pointwise at the left substitution's type.

Order, not interchangeable:

1. `substTyA_up` / `substTyA_upLet` — the substitution under one binder, by
   `hasTyWeakenA` / `convWeakenA` and `substA_up_liftA`.
2. `hasTyA_substA` / `convA_substA` — subject substitution, one arm per
   constructor of `HasTyA` (9) and `ConvA` (18), the same split as
   `RcicAnnWeaken`. ι rides on `iotaRel_substA`; δ / `const` / `consts` on
   `substA_closed` (`EnvClosedA`).
3. `hasTyA_func` — functionality. A congruence's right-hand typing is subject
   substitution along the right substitution, retyped by functionality on a
   subderivation. Reversing 2 and 3 is the fake "missing `hrt`" stuck point.

`substTyA_id` inhabits the relation (the degeneracy tooth). `hasTyA_inst0` and
`hasTyA_func0` are the one-variable corollaries, built by applying the general
lemmas to `SubstA.cons t SubstA.id`, not by a second induction.

Extra premises, and why the tree forces them:

* `substTyA_id` takes `EnvClosedA` and `IotaLiftA`. A tail variable is typed by
  the context derivation weakened under the head declaration, and weakening
  needs those two. `CtxWfA` does not carry them.
* `hasTyA_inst0` / `hasTyA_func0` take `CtxWfA`. The tail of `SubstA.cons t
  SubstA.id` is the identity, and the identity types a declared variable only
  because the context is well-formed. `HasTyA` / `ConvA` do not carry that.
* `t'` is not an extra premise of `hasTyA_func0`: its typing is
  `convA_right_subst` of `substTyA_id` applied to the conversion.

No `EnvSemA`. Premises are `EnvClosedA`, `IotaLiftA`, `IotaRecHeadA`,
`IotaSubstA`, plus `CtxWfA` on the tooth and the two corollaries.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section SubstTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- 从 Γ 到 Δ 的有类型代换。 -/
structure SubstTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Δ : LCtxA) (σ : SubstA)
    (Γ : LCtxA) : Type where
  ty : ∀ i A, lookupTypeA Γ i = some A → HasTyA E I n Δ (σ i) (substA σ A)
  val : ∀ i A v, lookupTypeA Γ i = some A → lookupValueA Γ i = some v →
    ConvA E I n Δ (σ i) (substA σ v) (substA σ A)

structure ConvSubstA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Δ : LCtxA) (σ σ' : SubstA)
    (Γ : LCtxA) : Type where
  left : SubstTyA E I n Δ σ Γ
  right : SubstTyA E I n Δ σ' Γ
  conv : ∀ i A, lookupTypeA Γ i = some A → ConvA E I n Δ (σ i) (σ' i) (substA σ A)

/-! ## pulling a successor lookup apart, as data (no `Exists` / `Nonempty`) -/

structure LiftedTypeA (Γ : LCtxA) (i : Nat) (B : ExprA) : Type where
  orig : ExprA
  got : lookupTypeA Γ i = some orig
  eq_lift : B = liftA 0 1 orig

structure LiftedValueA (Γ : LCtxA) (i : Nat) (v : ExprA) : Type where
  orig : ExprA
  got : lookupValueA Γ i = some orig
  eq_lift : v = liftA 0 1 orig

def liftedTypeA (y : LocalDeclA) (Γ : LCtxA) {i : Nat} {B : ExprA}
    (h : lookupTypeA (y :: Γ) (i + 1) = some B) : LiftedTypeA Γ i B := by
  have h' := lookupTypeA_cons_succ y Γ i
  rw [h] at h'
  match hB : lookupTypeA Γ i with
  | none =>
      rw [hB, Option.map_none'] at h'
      cases h'
  | some B₀ =>
      rw [hB, Option.map_some'] at h'
      injection h' with h'
      exact ⟨B₀, hB, h'⟩

def liftedValueA (y : LocalDeclA) (Γ : LCtxA) {i : Nat} {v : ExprA}
    (h : lookupValueA (y :: Γ) (i + 1) = some v) : LiftedValueA Γ i v := by
  have h' := lookupValueA_cons_succ y Γ i
  rw [h] at h'
  match hB : lookupValueA Γ i with
  | none =>
      rw [hB, Option.map_none'] at h'
      cases h'
  | some v₀ =>
      rw [hB, Option.map_some'] at h'
      injection h' with h'
      exact ⟨v₀, hB, h'⟩

theorem lookupTypeA_zero_assumption_eq {A B : ExprA} {Γ : LCtxA}
    (h : lookupTypeA (.assumption A :: Γ) 0 = some B) : B = liftA 0 1 A := by
  rw [lookupTypeA_cons_zero_assumption] at h
  injection h with h
  exact h.symm

theorem lookupTypeA_zero_let_eq {A v B : ExprA} {Γ : LCtxA}
    (h : lookupTypeA (.letBinding A v :: Γ) 0 = some B) : B = liftA 0 1 A := by
  rw [lookupTypeA_cons_zero_let] at h
  injection h with h
  exact h.symm

theorem lookupValueA_zero_let_eq {A w v : ExprA} {Γ : LCtxA}
    (h : lookupValueA (.letBinding A w :: Γ) 0 = some v) : v = liftA 0 1 w := by
  rw [lookupValueA_cons_zero_let] at h
  injection h with h
  exact h.symm

theorem lookupValueA_zero_assumption_none {A v : ExprA} {Γ : LCtxA}
    (h : lookupValueA (.assumption A :: Γ) 0 = some v) : False := by
  rw [lookupValueA_cons_zero_assumption] at h
  cases h

/-! ## one step under a binder, for an arbitrary target declaration -/

def substTyA_succ (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) (d y : LocalDeclA) (i : Nat) (B : ExprA)
    (h : lookupTypeA (y :: Γ) (i + 1) = some B) :
    HasTyA E I n (d :: Δ) (σ.up (i + 1)) (substA σ.up B) := by
  let s := liftedTypeA y Γ h
  have hEq : B = liftA 0 1 s.orig := s.eq_lift
  rw [hEq]
  have hw := hasTyWeakenA hE hI d (Nat.zero_le _) (hσ.ty i s.orig s.got)
  rw [SubstA.up_succ, substA_up_liftA]
  exact hw

def substTyA_succ_val (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) (d y : LocalDeclA) (i : Nat) (B v : ExprA)
    (hty : lookupTypeA (y :: Γ) (i + 1) = some B)
    (hval : lookupValueA (y :: Γ) (i + 1) = some v) :
    ConvA E I n (d :: Δ) (σ.up (i + 1)) (substA σ.up v) (substA σ.up B) := by
  let sB := liftedTypeA y Γ hty
  let sv := liftedValueA y Γ hval
  have hB : B = liftA 0 1 sB.orig := sB.eq_lift
  have hv : v = liftA 0 1 sv.orig := sv.eq_lift
  rw [hB, hv]
  have hw := convWeakenA hE hI d (Nat.zero_le _) (hσ.val i sB.orig sv.orig sB.got sv.got)
  rw [SubstA.up_succ, substA_up_liftA, substA_up_liftA]
  exact hw

def convSubstA_succ (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ σ' : SubstA}
    (h : ConvSubstA E I n Δ σ σ' Γ) (d y : LocalDeclA) (i : Nat) (B : ExprA)
    (hlu : lookupTypeA (y :: Γ) (i + 1) = some B) :
    ConvA E I n (d :: Δ) (σ.up (i + 1)) (σ'.up (i + 1)) (substA σ.up B) := by
  let s := liftedTypeA y Γ hlu
  have hEq : B = liftA 0 1 s.orig := s.eq_lift
  rw [hEq]
  have hw := convWeakenA hE hI d (Nat.zero_le _) (h.conv i s.orig s.got)
  rw [SubstA.up_succ, SubstA.up_succ, substA_up_liftA]
  exact hw

/-! ## `SubstTyA` under an assumption, and under a let -/

def substTyA_up (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    {A : ExprA} {u : Level} (hσ : SubstTyA E I n Δ σ Γ)
    (hA : HasTyA E I n Δ (substA σ A) (.sort u)) :
    SubstTyA E I n (.assumption (substA σ A) :: Δ) σ.up (.assumption A :: Γ) :=
  let d : LocalDeclA := .assumption (substA σ A)
  let y : LocalDeclA := .assumption A
  { ty := fun i B h => by
      cases i with
      | zero =>
          have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq h
          subst hB
          rw [SubstA.up_zero, substA_up_liftA]
          exact .bvar _ 0 _ u (lookupTypeA_cons_zero_assumption (substA σ A) Δ)
            (hasTyWeakenA hE hI d (Nat.zero_le _) hA)
      | succ i => exact substTyA_succ hE hI hσ d y i B h
    val := fun i B v hty hval => by
      cases i with
      | zero => exact (lookupValueA_zero_assumption_none hval).elim
      | succ i => exact substTyA_succ_val hE hI hσ d y i B v hty hval }

def substTyA_upLet (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    {A v : ExprA} {u : Level} (hσ : SubstTyA E I n Δ σ Γ)
    (hA : HasTyA E I n Δ (substA σ A) (.sort u))
    (hv : HasTyA E I n Δ (substA σ v) (substA σ A)) :
    SubstTyA E I n (.letBinding (substA σ A) (substA σ v) :: Δ) σ.up
      (.letBinding A v :: Γ) :=
  let d : LocalDeclA := .letBinding (substA σ A) (substA σ v)
  let y : LocalDeclA := .letBinding A v
  { ty := fun i B h => by
      cases i with
      | zero =>
          have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq h
          subst hB
          rw [SubstA.up_zero, substA_up_liftA]
          exact .bvar _ 0 _ u (lookupTypeA_cons_zero_let (substA σ A) (substA σ v) Δ)
            (hasTyWeakenA hE hI d (Nat.zero_le _) hA)
      | succ i => exact substTyA_succ hE hI hσ d y i B h
    val := fun i B w hty hval => by
      cases i with
      | zero =>
          have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hty
          have hw : w = liftA 0 1 v := lookupValueA_zero_let_eq hval
          subst hB; subst hw
          rw [SubstA.up_zero, substA_up_liftA, substA_up_liftA]
          exact .zetaLocal _ 0 _ _
            (lookupValueA_cons_zero_let (substA σ A) (substA σ v) Δ)
            (lookupTypeA_cons_zero_let (substA σ A) (substA σ v) Δ)
            (hasTyWeakenA hE hI d (Nat.zero_le _) hv)
      | succ i => exact substTyA_succ_val hE hI hσ d y i B w hty hval }

/-- a pi's typing ends in `pi` after `conv`s. Returns the derivations, not
`Nonempty` — eliminating `Nonempty` would be `Classical.choice`. -/
def hasTyA_pi_parts : {Γ : LCtxA} → {D : ExprA} → {u : Level} → {C : ExprA} → {v : Level} →
    {T : ExprA} → HasTyA E I n Γ (.pi D u C v) T →
    HasTyA E I n Γ D (.sort u) × HasTyA E I n (.assumption D :: Γ) C (.sort v)
  | _, _, _, _, _, _, .pi _ _ _ _ _ hA hB => ⟨hA, hB⟩
  | _, _, _, _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_pi_parts h

/-! ## the single-variable substitution, as algebra (pointwise, no `funext`) -/

theorem substA_shiftAt_cons_id (t : ExprA) :
    ∀ i, SubstA.shiftAt 0 (SubstA.cons t SubstA.id) i = SubstA.id i := fun i => by
  rw [SubstA.shiftAt, if_pos (Nat.zero_le i), SubstA.cons_succ, SubstA.id_apply]

theorem substA_cons_id_lift (t e : ExprA) :
    substA (SubstA.cons t SubstA.id) (liftA 0 1 e) = e := by
  rw [substA_liftA, substA_ext (substA_shiftAt_cons_id t), substA_id]

theorem cons_id_single (t : ExprA) : ∀ i, SubstA.cons t SubstA.id i = SubstA.single 0 t i
  | 0 => by rw [SubstA.cons_zero, SubstA.single, if_pos rfl]
  | i + 1 => by
      rw [SubstA.cons_succ, SubstA.id_apply, SubstA.single,
        if_neg (Nat.succ_ne_zero i), if_pos (Nat.zero_lt_succ i)]
      rw [Nat.succ_sub_one]

theorem substA_cons_id_instantiate0 (t e : ExprA) :
    substA (SubstA.cons t SubstA.id) e = instantiate0A t e := by
  rw [instantiate0A, instantiateA_eq_substA]
  exact substA_ext (cons_id_single t) e

/-! ## subject substitution, then the typing of each side and of the type -/

mutual

def hasTyA_substA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {e A : ExprA} → HasTyA E I n Γ e A →
      HasTyA E I n Δ (substA σ e) (substA σ A)
  | _, _, .sort _ l => .sort _ l
  | _, _, .bvar _ i A _ h _ => hσ.ty i A h
  | _, _, .const _ r ls m u hres hlen hwf hT => by
      have hcl : substA σ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
        substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) σ
      have hT' := hasTyA_substA hE hI hR hIS hσ hT
      rw [hcl] at hT'
      show HasTyA E I n Δ (.const r ls) (substA σ (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .const _ r ls m u hres hlen hwf hT'
  | _, _, .pi _ A u B v hA hB => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      exact .pi _ _ u _ v hA'
        (hasTyA_substA hE hI hR hIS (substTyA_up hE hI hσ hA') hB)
  | _, _, .lam _ A u body B v hA hB hbody => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hA'
      exact .lam _ _ u _ _ v hA'
        (hasTyA_substA hE hI hR hIS hσ' hB)
        (hasTyA_substA hE hI hR hIS hσ' hbody)
  | _, _, .app _ f a A B u v w hB hTy hf ha => by
      have hA' := (hasTyA_type_subst hE hI hR hIS hσ ha).2
      have hσ' := substTyA_up hE hI hσ hA'
      have hTy' := hasTyA_substA hE hI hR hIS hσ hTy
      rw [substA_instantiate0A] at hTy'
      show HasTyA E I n Δ (.app (substA σ f) (substA σ a)) (substA σ (instantiate0A a B))
      rw [substA_instantiate0A]
      exact .app _ _ _ _ _ u v w
        (hasTyA_substA hE hI hR hIS hσ' hB) hTy'
        (hasTyA_substA hE hI hR hIS hσ hf)
        (hasTyA_substA hE hI hR hIS hσ ha)
  | _, _, .letE _ A u w value B body hA hv hTy hb => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      have hv' := hasTyA_substA hE hI hR hIS hσ hv
      have hσ' := substTyA_upLet hE hI hσ hA' hv'
      have hTy' := hasTyA_substA hE hI hR hIS hσ hTy
      rw [substA_instantiate0A] at hTy'
      show HasTyA E I n Δ (.letE (substA σ A) (substA σ value) (substA σ.up body))
        (substA σ (instantiate0A value B))
      rw [substA_instantiate0A]
      exact .letE _ _ u w _ _ _ hA' hv' hTy'
        (hasTyA_substA hE hI hR hIS hσ' hb)
  | _, _, .lit _ t _ hexp => by
      have hexp' := hasTyA_substA hE hI hR hIS hσ hexp
      rw [substA_natExpandA] at hexp'
      exact .lit _ t _ hexp'
  | _, _, .conv _ _ _ _ l u h hAl hlu hB hc =>
      .conv _ _ _ _ l u (hasTyA_substA hE hI hR hIS hσ h)
        (hasTyA_substA hE hI hR hIS hσ hAl) hlu
        (hasTyA_substA hE hI hR hIS hσ hB)
        (convA_substA hE hI hR hIS hσ hc)

def convA_substA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {a b A : ExprA} → ConvA E I n Γ a b A →
      ConvA E I n Δ (substA σ a) (substA σ b) (substA σ A)
  | _, _, _, .refl _ _ _ h => .refl _ _ _ (hasTyA_substA hE hI hR hIS hσ h)
  | _, _, _, .symm _ _ _ _ h => .symm _ _ _ _ (convA_substA hE hI hR hIS hσ h)
  | _, _, _, .trans _ _ _ _ _ h1 h2 =>
      .trans _ _ _ _ _ (convA_substA hE hI hR hIS hσ h1) (convA_substA hE hI hR hIS hσ h2)
  | _, _, _, .beta _ A u body arg B hA hbody harg hred => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hA'
      have hred' := hasTyA_substA hE hI hR hIS hσ hred
      rw [substA_instantiate0A, substA_instantiate0A] at hred'
      show ConvA E I n Δ
        (.app (.lam (substA σ A) u (substA σ.up body)) (substA σ arg))
        (substA σ (instantiate0A arg body)) (substA σ (instantiate0A arg B))
      rw [substA_instantiate0A, substA_instantiate0A]
      exact .beta _ _ u _ _ _ hA' (hasTyA_substA hE hI hR hIS hσ' hbody)
        (hasTyA_substA hE hI hR hIS hσ harg) hred'
  | _, _, _, .zeta _ A value body B u hA hv hb hred => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      have hv' := hasTyA_substA hE hI hR hIS hσ hv
      have hσ' := substTyA_upLet hE hI hσ hA' hv'
      have hred' := hasTyA_substA hE hI hR hIS hσ hred
      rw [substA_instantiate0A, substA_instantiate0A] at hred'
      show ConvA E I n Δ
        (.letE (substA σ A) (substA σ value) (substA σ.up body))
        (substA σ (instantiate0A value body)) (substA σ (instantiate0A value B))
      rw [substA_instantiate0A, substA_instantiate0A]
      exact .zeta _ _ _ _ _ u hA' hv' (hasTyA_substA hE hI hR hIS hσ' hb) hred'
  | _, _, _, .zetaLocal _ i A v hval hty _ => hσ.val i A v hty hval
  | _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb => by
      have hcl1 : substA σ (instantiateLevelsA ls b) = instantiateLevelsA ls b :=
        substA_closed (liftA_instantiateLevelsA_closed ((hE r m hres).2 b hbody) ls) σ
      have hcl2 : substA σ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
        substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) σ
      have hb' := hasTyA_substA hE hI hR hIS hσ hb
      rw [hcl1, hcl2] at hb'
      show ConvA E I n Δ (.const r ls) (substA σ (instantiateLevelsA ls b))
        (substA σ (instantiateLevelsA ls m.mtypeA))
      rw [hcl1, hcl2]
      exact .delta _ r ls m b hres hbody htr hlen hwf hb'
  | _, _, _, .iota _ _ _ _ h hlhs hrhs =>
      have hl' := hasTyA_substA hE hI hR hIS hσ hlhs
      .iota _ _ _ _ (iotaRel_substA hE hR hIS σ h ⟨hlhs⟩ ⟨hl'⟩) hl'
        (hasTyA_substA hE hI hR hIS hσ hrhs)
  | _, _, _, .structIota _ f a rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota _ (substA σ f) (substA σ a) _ (substA σ e) _
        (recAtMajorA_substA_true E σ hrec) (structArmA_substA hE σ hs)
        (hIS σ (.app f a) rhs h) (hasTyA_substA hE hI hR hIS hσ hlhs)
        (hasTyA_substA hE hI hR hIS hσ hrhs) (convA_substA hE hI hR hIS hσ hcv)
  | _, _, _, .lit _ t T hexp => by
      have hexp' := hasTyA_substA hE hI hR hIS hσ hexp
      rw [substA_natExpandA] at hexp'
      show ConvA E I n Δ (.lit t) (substA σ (natExpandA t)) (substA σ T)
      rw [substA_natExpandA]
      exact .lit _ t _ hexp'
  | _, _, _, .app _ f g a b A B u v h1 h2 hB hrt => by
      have hDom := (convA_type_subst hE hI hR hIS hσ h2).2
      have hσ' := substTyA_up hE hI hσ hDom
      have hrt' := hasTyA_substA hE hI hR hIS hσ hrt
      rw [substA_instantiate0A] at hrt'
      show ConvA E I n Δ (.app (substA σ f) (substA σ a)) (.app (substA σ g) (substA σ b))
        (substA σ (instantiate0A a B))
      rw [substA_instantiate0A]
      exact .app _ _ _ _ _ _ _ u v (convA_substA hE hI hR hIS hσ h1)
        (convA_substA hE hI hR hIS hσ h2)
        (hasTyA_substA hE hI hR hIS hσ' hB) hrt'
  | _, _, _, .lam _ A _ b _ _ u u' v hu hA hb hrt => by
      have hDom := convA_left_subst hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hDom
      exact .lam _ _ _ _ _ _ u u' v hu (convA_substA hE hI hR hIS hσ hA)
        (convA_substA hE hI hR hIS hσ' hb) (hasTyA_substA hE hI hR hIS hσ hrt)
  | _, _, _, .pi _ A _ B _ u u' v v' hu hv hA hB hrt => by
      have hDom := convA_left_subst hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hDom
      exact .pi _ _ _ _ _ u u' v v' hu hv (convA_substA hE hI hR hIS hσ hA)
        (convA_substA hE hI hR hIS hσ' hB) (hasTyA_substA hE hI hR hIS hσ hrt)
  | _, _, _, .letE _ A A' v v' b b' B u hA hv hb hrt => by
      have hDom := convA_left_subst hE hI hR hIS hσ hA
      have hVal := convA_left_subst hE hI hR hIS hσ hv
      have hσ' := substTyA_upLet hE hI hσ hDom hVal
      have hrt' := hasTyA_substA hE hI hR hIS hσ hrt
      rw [substA_instantiate0A] at hrt'
      show ConvA E I n Δ (.letE (substA σ A) (substA σ v) (substA σ.up b))
        (.letE (substA σ A') (substA σ v') (substA σ.up b')) (substA σ (instantiate0A v B))
      rw [substA_instantiate0A]
      exact .letE _ _ _ _ _ _ _ _ u (convA_substA hE hI hR hIS hσ hA)
        (convA_substA hE hI hR hIS hσ hv) (convA_substA hE hI hR hIS hσ' hb) hrt'
  | _, _, _, .sorts _ l₁ l₂ h => .sorts _ l₁ l₂ h
  | _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h hrt => by
      have hcl : substA σ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
        substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) σ
      have hrt' := hasTyA_substA hE hI hR hIS hσ hrt
      rw [hcl] at hrt'
      show ConvA E I n Δ (.const r ls) (.const r ls') (substA σ (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .consts _ r ls ls' m hres hlen hwf hwf' h hrt'
  | _, _, _, .eta _ f A B u v h hrt => by
      have hrt' := hasTyA_substA hE hI hR hIS hσ hrt
      rw [substA_lam, substA_app, substA_bvar, SubstA.up_zero, substA_up_liftA] at hrt'
      rw [substA_lam, substA_app, substA_bvar, SubstA.up_zero, substA_up_liftA]
      exact .eta _ (substA σ f) (substA σ A) (substA σ.up B) u v
        (hasTyA_substA hE hI hR hIS hσ h) hrt'
  | _, _, _, .irr _ _ _ _ hP hp hq =>
      .irr _ _ _ _ (hasTyA_substA hE hI hR hIS hσ hP) (hasTyA_substA hE hI hR hIS hσ hp)
        (hasTyA_substA hE hI hR hIS hσ hq)
  | _, _, _, .tyConv _ _ _ _ _ l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv _ _ _ _ _ l l' u (convA_substA hE hI hR hIS hσ h)
        (hasTyA_substA hE hI hR hIS hσ hAl) hlu
        (hasTyA_substA hE hI hR hIS hσ hA'l) hl'u
        (convA_substA hE hI hR hIS hσ hA)

def hasTyA_type_subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {e A : ExprA} → HasTyA E I n Γ e A →
      Σ u : Level, HasTyA E I n Δ (substA σ A) (.sort u)
  | _, _, .sort _ l => ⟨.succ (.succ l), .sort _ (.succ l)⟩
  | _, _, .bvar _ _ _ u _ hA => ⟨u, hasTyA_substA hE hI hR hIS hσ hA⟩
  | _, _, .const _ _ _ _ u _ _ _ hT => ⟨u, hasTyA_substA hE hI hR hIS hσ hT⟩
  | _, _, .pi _ _ u _ v _ _ => ⟨.succ (.imax u v), .sort _ (.imax u v)⟩
  | _, _, .lam _ A u _ B v hA hB _ => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      exact ⟨.imax u v, .pi _ _ u _ v hA'
        (hasTyA_substA hE hI hR hIS (substTyA_up hE hI hσ hA') hB)⟩
  | _, _, .app _ _ _ _ _ _ _ w _ hTy _ _ => ⟨w, hasTyA_substA hE hI hR hIS hσ hTy⟩
  | _, _, .letE _ _ _ w _ _ _ _ _ hTy _ => ⟨w, hasTyA_substA hE hI hR hIS hσ hTy⟩
  | _, _, .lit _ _ _ hexp => hasTyA_type_subst hE hI hR hIS hσ hexp
  | _, _, .conv _ _ _ _ _ u _ _ _ hB _ => ⟨u, hasTyA_substA hE hI hR hIS hσ hB⟩

def convA_left_subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {a b A : ExprA} → ConvA E I n Γ a b A → HasTyA E I n Δ (substA σ a) (substA σ A)
  | _, _, _, .refl _ _ _ h => hasTyA_substA hE hI hR hIS hσ h
  | _, _, _, .symm _ _ _ _ h => convA_right_subst hE hI hR hIS hσ h
  | _, _, _, .trans _ _ _ _ _ h1 _ => convA_left_subst hE hI hR hIS hσ h1
  | _, _, _, .beta _ A u body arg B hA hbody harg hred => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hA'
      have ⟨v, hBsort⟩ := hasTyA_type_subst hE hI hR hIS hσ' hbody
      have ⟨w, hTy⟩ := hasTyA_type_subst hE hI hR hIS hσ hred
      rw [substA_instantiate0A] at hTy
      have hbody' := hasTyA_substA hE hI hR hIS hσ' hbody
      have hf : HasTyA E I n Δ (.lam (substA σ A) u (substA σ.up body))
          (.pi (substA σ A) u (substA σ.up B) v) :=
        .lam _ _ u _ _ v hA' hBsort hbody'
      show HasTyA E I n Δ (substA σ (.app (.lam A u body) arg)) (substA σ (instantiate0A arg B))
      rw [substA_instantiate0A]
      exact .app _ _ _ _ _ u v w hBsort hTy hf (hasTyA_substA hE hI hR hIS hσ harg)
  | _, _, _, .zeta _ A value body B u hA hv hb hred => by
      have hA' := hasTyA_substA hE hI hR hIS hσ hA
      have hv' := hasTyA_substA hE hI hR hIS hσ hv
      have hσ' := substTyA_upLet hE hI hσ hA' hv'
      have ⟨w, hTy⟩ := hasTyA_type_subst hE hI hR hIS hσ hred
      rw [substA_instantiate0A] at hTy
      show HasTyA E I n Δ (substA σ (.letE A value body)) (substA σ (instantiate0A value B))
      rw [substA_instantiate0A]
      exact .letE _ _ u w _ _ _ hA' hv' hTy (hasTyA_substA hE hI hR hIS hσ' hb)
  | _, _, _, .zetaLocal _ i A _ _ hty _ => hσ.ty i A hty
  | _, _, _, .delta _ r ls m _ hres _ _ hlen hwf hb => by
      have hcl : substA σ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
        substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) σ
      have ⟨u, hT⟩ := hasTyA_type_subst hE hI hR hIS hσ hb
      rw [hcl] at hT
      show HasTyA E I n Δ (.const r ls) (substA σ (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .const _ r ls m u hres hlen hwf hT
  | _, _, _, .iota _ _ _ _ _ hlhs _ => hasTyA_substA hE hI hR hIS hσ hlhs
  | _, _, _, .structIota _ _ _ _ _ _ _ _ _ hlhs _ _ => hasTyA_substA hE hI hR hIS hσ hlhs
  | _, _, _, .lit _ t _ hexp => by
      have hexp' := hasTyA_substA hE hI hR hIS hσ hexp
      rw [substA_natExpandA] at hexp'
      exact .lit _ t _ hexp'
  | _, _, _, .app _ f _ a _ A B u v h1 h2 hB hrt => by
      have hDom := (convA_type_subst hE hI hR hIS hσ h2).2
      have hσ' := substTyA_up hE hI hσ hDom
      have ⟨w, hTy⟩ := hasTyA_type_subst hE hI hR hIS hσ hrt
      rw [substA_instantiate0A] at hTy
      show HasTyA E I n Δ (substA σ (.app f a)) (substA σ (instantiate0A a B))
      rw [substA_instantiate0A]
      exact .app _ _ _ _ _ u v w (hasTyA_substA hE hI hR hIS hσ' hB) hTy
        (convA_left_subst hE hI hR hIS hσ h1) (convA_left_subst hE hI hR hIS hσ h2)
  | _, _, _, .lam _ A _ b _ B u _ v _ hA hb hrt => by
      have hDom := convA_left_subst hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hDom
      have ⟨_, hPi⟩ := hasTyA_type_subst hE hI hR hIS hσ hrt
      rw [substA_pi] at hPi
      have hCod := (hasTyA_pi_parts hPi).2
      exact .lam _ (substA σ A) u (substA σ.up b) (substA σ.up B) v hDom hCod
        (convA_left_subst hE hI hR hIS hσ' hb)
  | _, _, _, .pi _ A _ B _ u _ v _ _ _ hA hB _ => by
      have hDom := convA_left_subst hE hI hR hIS hσ hA
      have hσ' := substTyA_up hE hI hσ hDom
      exact .pi _ (substA σ A) u (substA σ.up B) v hDom
        (convA_left_subst hE hI hR hIS hσ' hB)
  | _, _, _, .letE _ A _ v _ b _ B u hA hv hb hrt => by
      have hDom := convA_left_subst hE hI hR hIS hσ hA
      have hVal := convA_left_subst hE hI hR hIS hσ hv
      have hσ' := substTyA_upLet hE hI hσ hDom hVal
      have ⟨w, hTy⟩ := hasTyA_type_subst hE hI hR hIS hσ hrt
      rw [substA_instantiate0A] at hTy
      show HasTyA E I n Δ (substA σ (.letE A v b)) (substA σ (instantiate0A v B))
      rw [substA_instantiate0A]
      exact .letE _ _ u w _ _ _ hDom hVal hTy (convA_left_subst hE hI hR hIS hσ' hb)
  | _, _, _, .sorts _ l₁ _ _ => .sort _ l₁
  | _, _, _, .consts _ r ls _ m hres hlen hwf _ _ hrt => by
      have hcl : substA σ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
        substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) σ
      have ⟨u, hT⟩ := hasTyA_type_subst hE hI hR hIS hσ hrt
      rw [hcl] at hT
      show HasTyA E I n Δ (.const r ls) (substA σ (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .const _ r ls m u hres hlen hwf hT
  | _, _, _, .eta _ _ _ _ _ _ _ hrt => hasTyA_substA hE hI hR hIS hσ hrt
  | _, _, _, .irr _ _ p _ _ hp _ => hasTyA_substA hE hI hR hIS hσ hp
  | _, _, _, .tyConv _ a _ A A' l l' u h hAl hlu hA'l hl'u hAc =>
      .conv _ _ _ _ l u (convA_left_subst hE hI hR hIS hσ h)
        (hasTyA_substA hE hI hR hIS hσ hAl) hlu
        (hasTyA_retype_sort (hasTyA_substA hE hI hR hIS hσ hA'l) hl'u)
        (convA_substA hE hI hR hIS hσ hAc)

def convA_right_subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {a b A : ExprA} → ConvA E I n Γ a b A → HasTyA E I n Δ (substA σ b) (substA σ A)
  | _, _, _, .refl _ _ _ h => hasTyA_substA hE hI hR hIS hσ h
  | _, _, _, .symm _ _ _ _ h => convA_left_subst hE hI hR hIS hσ h
  | _, _, _, .trans _ _ _ _ _ _ h2 => convA_right_subst hE hI hR hIS hσ h2
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ hred => hasTyA_substA hE hI hR hIS hσ hred
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ hred => hasTyA_substA hE hI hR hIS hσ hred
  | _, _, _, .zetaLocal _ _ _ _ _ _ hv => hasTyA_substA hE hI hR hIS hσ hv
  | _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => hasTyA_substA hE hI hR hIS hσ hb
  | _, _, _, .iota _ _ _ _ _ _ hrhs => hasTyA_substA hE hI hR hIS hσ hrhs
  | _, _, _, .structIota _ _ _ _ _ _ _ _ _ _ hrhs _ => hasTyA_substA hE hI hR hIS hσ hrhs
  | _, _, _, .lit _ _ _ hexp => hasTyA_substA hE hI hR hIS hσ hexp
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_substA hE hI hR hIS hσ hrt
  | _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_substA hE hI hR hIS hσ hrt
  | _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_substA hE hI hR hIS hσ hrt
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_substA hE hI hR hIS hσ hrt
  | _, _, _, .sorts _ l₁ l₂ h => hasTyA_retype_sort (.sort _ l₂) (eqNA_succ (eqNA_symm h))
  | _, _, _, .consts _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_substA hE hI hR hIS hσ hrt
  | _, _, _, .eta _ _ _ _ _ _ h _ => hasTyA_substA hE hI hR hIS hσ h
  | _, _, _, .irr _ _ _ _ _ _ hq => hasTyA_substA hE hI hR hIS hσ hq
  | _, _, _, .tyConv _ _ b _ _ l _ u h hAl hlu hA'l hl'u hAc =>
      .conv _ _ _ _ l u (convA_right_subst hE hI hR hIS hσ h)
        (hasTyA_substA hE hI hR hIS hσ hAl) hlu
        (hasTyA_retype_sort (hasTyA_substA hE hI hR hIS hσ hA'l) hl'u)
        (convA_substA hE hI hR hIS hσ hAc)

def convA_type_subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {a b A : ExprA} → ConvA E I n Γ a b A →
      Σ u : Level, HasTyA E I n Δ (substA σ A) (.sort u)
  | _, _, _, .refl _ _ _ h => hasTyA_type_subst hE hI hR hIS hσ h
  | _, _, _, .symm _ _ _ _ h => convA_type_subst hE hI hR hIS hσ h
  | _, _, _, .trans _ _ _ _ _ h1 _ => convA_type_subst hE hI hR hIS hσ h1
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ hred => hasTyA_type_subst hE hI hR hIS hσ hred
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ hred => hasTyA_type_subst hE hI hR hIS hσ hred
  | _, _, _, .zetaLocal _ _ _ _ _ _ hv => hasTyA_type_subst hE hI hR hIS hσ hv
  | _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => hasTyA_type_subst hE hI hR hIS hσ hb
  | _, _, _, .iota _ _ _ _ _ hlhs _ => hasTyA_type_subst hE hI hR hIS hσ hlhs
  | _, _, _, .structIota _ _ _ _ _ _ _ _ _ hlhs _ _ => hasTyA_type_subst hE hI hR hIS hσ hlhs
  | _, _, _, .lit _ _ _ hexp => hasTyA_type_subst hE hI hR hIS hσ hexp
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_type_subst hE hI hR hIS hσ hrt
  | _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_type_subst hE hI hR hIS hσ hrt
  | _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_type_subst hE hI hR hIS hσ hrt
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_type_subst hE hI hR hIS hσ hrt
  | _, _, _, .sorts _ l₁ _ _ => ⟨.succ (.succ l₁), .sort _ (.succ l₁)⟩
  | _, _, _, .consts _ _ _ _ _ _ _ _ _ _ hrt => hasTyA_type_subst hE hI hR hIS hσ hrt
  | _, _, _, .eta _ _ _ _ _ _ h _ => hasTyA_type_subst hE hI hR hIS hσ h
  | _, _, _, .irr _ P _ _ hP _ _ => ⟨.zero, hasTyA_substA hE hI hR hIS hσ hP⟩
  | _, _, _, .tyConv _ _ _ _ _ _ l' _ _ _ _ hA'l _ _ => ⟨l', hasTyA_substA hE hI hR hIS hσ hA'l⟩

end

/-! ## a convertible pair, under one binder. The target declaration is the LEFT
domain: the right substitution is retyped into it, not extended by its own. -/

def convSubstA_up (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ σ' : SubstA}
    {A : ExprA} {u : Level} (h : ConvSubstA E I n Δ σ σ' Γ)
    (hA : HasTyA E I n Δ (substA σ A) (.sort u))
    (hA' : HasTyA E I n Δ (substA σ' A) (.sort u))
    (hc : ConvA E I n Δ (substA σ A) (substA σ' A) (.sort u)) :
    ConvSubstA E I n (.assumption (substA σ A) :: Δ) σ.up σ'.up (.assumption A :: Γ) :=
  let d : LocalDeclA := .assumption (substA σ A)
  let y : LocalDeclA := .assumption A
  { left := substTyA_up hE hI h.left hA
    right := {
      ty := fun i B hlu => by
        cases i with
        | zero =>
            have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq hlu
            subst hB
            rw [SubstA.up_zero, substA_up_liftA]
            exact .conv _ _ _ _ u u
              (.bvar _ 0 _ u (lookupTypeA_cons_zero_assumption (substA σ A) Δ)
                (hasTyWeakenA hE hI d (Nat.zero_le _) hA))
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA) (eqNA_refl u)
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA')
              (convWeakenA hE hI d (Nat.zero_le _) hc)
        | succ i => exact substTyA_succ hE hI h.right d y i B hlu
      val := fun i B v hty hval => by
        cases i with
        | zero => exact (lookupValueA_zero_assumption_none hval).elim
        | succ i => exact substTyA_succ_val hE hI h.right d y i B v hty hval }
    conv := fun i B hlu => by
      cases i with
      | zero =>
          have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq hlu
          subst hB
          rw [SubstA.up_zero, SubstA.up_zero, substA_up_liftA]
          exact .refl _ _ _
            (.bvar _ 0 _ u (lookupTypeA_cons_zero_assumption (substA σ A) Δ)
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA))
      | succ i => exact convSubstA_succ hE hI h d y i B hlu }

def convSubstA_upLet (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ σ' : SubstA}
    {A v : ExprA} {u : Level} (h : ConvSubstA E I n Δ σ σ' Γ)
    (hA : HasTyA E I n Δ (substA σ A) (.sort u))
    (hA' : HasTyA E I n Δ (substA σ' A) (.sort u))
    (hv : HasTyA E I n Δ (substA σ v) (substA σ A))
    (_hv' : HasTyA E I n Δ (substA σ' v) (substA σ' A))
    (hcA : ConvA E I n Δ (substA σ A) (substA σ' A) (.sort u))
    (hcV : ConvA E I n Δ (substA σ v) (substA σ' v) (substA σ A)) :
    ConvSubstA E I n (.letBinding (substA σ A) (substA σ v) :: Δ) σ.up σ'.up
      (.letBinding A v :: Γ) :=
  let d : LocalDeclA := .letBinding (substA σ A) (substA σ v)
  let y : LocalDeclA := .letBinding A v
  { left := substTyA_upLet hE hI h.left hA hv
    right := {
      ty := fun i B hlu => by
        cases i with
        | zero =>
            have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hlu
            subst hB
            rw [SubstA.up_zero, substA_up_liftA]
            exact .conv _ _ _ _ u u
              (.bvar _ 0 _ u (lookupTypeA_cons_zero_let (substA σ A) (substA σ v) Δ)
                (hasTyWeakenA hE hI d (Nat.zero_le _) hA))
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA) (eqNA_refl u)
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA')
              (convWeakenA hE hI d (Nat.zero_le _) hcA)
        | succ i => exact substTyA_succ hE hI h.right d y i B hlu
      val := fun i B w hty hval => by
        cases i with
        | zero =>
            have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hty
            have hw : w = liftA 0 1 v := lookupValueA_zero_let_eq hval
            subst hB; subst hw
            rw [SubstA.up_zero, substA_up_liftA, substA_up_liftA]
            exact .tyConv _ _ _ _ _ u u u
              (.trans _ _ _ _ _
                (.zetaLocal _ 0 _ _
                  (lookupValueA_cons_zero_let (substA σ A) (substA σ v) Δ)
                  (lookupTypeA_cons_zero_let (substA σ A) (substA σ v) Δ)
                  (hasTyWeakenA hE hI d (Nat.zero_le _) hv))
                (convWeakenA hE hI d (Nat.zero_le _) hcV))
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA) (eqNA_refl u)
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA') (eqNA_refl u)
              (convWeakenA hE hI d (Nat.zero_le _) hcA)
        | succ i => exact substTyA_succ_val hE hI h.right d y i B w hty hval }
    conv := fun i B hlu => by
      cases i with
      | zero =>
          have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hlu
          subst hB
          rw [SubstA.up_zero, SubstA.up_zero, substA_up_liftA]
          exact .refl _ _ _
            (.bvar _ 0 _ u (lookupTypeA_cons_zero_let (substA σ A) (substA σ v) Δ)
              (hasTyWeakenA hE hI d (Nat.zero_le _) hA))
      | succ i => exact convSubstA_succ hE hI h d y i B hlu }

/-! ## functionality. Right-hand typings are `hasTyA_substA` on `σ'`. -/

def hasTyA_func (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ σ' : SubstA} (h : ConvSubstA E I n Δ σ σ' Γ) :
    {e A : ExprA} → HasTyA E I n Γ e A →
      ConvA E I n Δ (substA σ e) (substA σ' e) (substA σ A)
  | _, _, .sort _ l => .refl _ _ _ (.sort _ l)
  | _, _, .bvar _ i A _ hlu _ => h.conv i A hlu
  | _, _, .const _ r ls m u hres hlen hwf hT => by
      have hcl : substA σ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
        substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) σ
      have hT' := hasTyA_substA hE hI hR hIS h.left hT
      rw [hcl] at hT'
      rw [hcl]
      exact .refl _ _ _ (.const _ r ls m u hres hlen hwf hT')
  | _, _, .pi _ A u B v hA hB => by
      have hAσ := hasTyA_substA hE hI hR hIS h.left hA
      have hAσ' := hasTyA_substA hE hI hR hIS h.right hA
      have hcA := hasTyA_func hE hI hR hIS h hA
      have hup := convSubstA_up hE hI h hAσ hAσ' hcA
      have hcB := hasTyA_func hE hI hR hIS hup hB
      have hBσ' := hasTyA_substA hE hI hR hIS (substTyA_up hE hI h.right hAσ') hB
      exact .pi _ _ _ _ _ u u v v (eqNA_refl u) (eqNA_refl v) hcA hcB
        (.pi _ _ u _ v hAσ' hBσ')
  | _, _, .lam _ A u body B v hA hB hbody => by
      have hAσ := hasTyA_substA hE hI hR hIS h.left hA
      have hAσ' := hasTyA_substA hE hI hR hIS h.right hA
      have hcA := hasTyA_func hE hI hR hIS h hA
      have hup := convSubstA_up hE hI h hAσ hAσ' hcA
      have hcBody := hasTyA_func hE hI hR hIS hup hbody
      have hcCod := hasTyA_func hE hI hR hIS hup hB
      have hBσ := hasTyA_substA hE hI hR hIS (substTyA_up hE hI h.left hAσ) hB
      have hBσ' := hasTyA_substA hE hI hR hIS (substTyA_up hE hI h.right hAσ') hB
      have hbody' := hasTyA_substA hE hI hR hIS (substTyA_up hE hI h.right hAσ') hbody
      have hLam' : HasTyA E I n Δ (.lam (substA σ' A) u (substA σ'.up body))
          (.pi (substA σ' A) u (substA σ'.up B) v) :=
        .lam _ _ u _ _ v hAσ' hBσ' hbody'
      have hPi' : HasTyA E I n Δ (.pi (substA σ' A) u (substA σ'.up B) v) (.sort (.imax u v)) :=
        .pi _ _ u _ v hAσ' hBσ'
      have hPi : HasTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.sort (.imax u v)) :=
        .pi _ _ u _ v hAσ hBσ
      have hPiCv : ConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
          (.pi (substA σ' A) u (substA σ'.up B) v) (.sort (.imax u v)) :=
        .pi _ _ _ _ _ u u v v (eqNA_refl u) (eqNA_refl v) hcA hcCod hPi'
      have hrt : HasTyA E I n Δ (.lam (substA σ' A) u (substA σ'.up body))
          (.pi (substA σ A) u (substA σ.up B) v) :=
        .conv _ _ _ _ (.imax u v) (.imax u v) hLam' hPi' (eqNA_refl _) hPi (.symm _ _ _ _ hPiCv)
      exact .lam _ _ _ _ _ _ u u v (eqNA_refl u) hcA hcBody hrt
  | _, _, .app _ f a A B u v w hB hTy hf ha => by
      have hDom := (hasTyA_type_subst hE hI hR hIS h.left ha).2
      have hDom' := (hasTyA_type_subst hE hI hR hIS h.right ha).2
      have hBL := hasTyA_substA hE hI hR hIS (substTyA_up hE hI h.left hDom) hB
      have hB' := hasTyA_substA hE hI hR hIS (substTyA_up hE hI h.right hDom') hB
      have hTy' := hasTyA_substA hE hI hR hIS h.right hTy
      rw [substA_instantiate0A] at hTy'
      have hApp' : HasTyA E I n Δ (.app (substA σ' f) (substA σ' a))
          (instantiate0A (substA σ' a) (substA σ'.up B)) :=
        .app _ _ _ _ _ u v w hB' hTy'
          (hasTyA_substA hE hI hR hIS h.right hf) (hasTyA_substA hE hI hR hIS h.right ha)
      have hcTy := hasTyA_func hE hI hR hIS h hTy
      rw [substA_instantiate0A, substA_instantiate0A] at hcTy
      have hTyL := hasTyA_substA hE hI hR hIS h.left hTy
      rw [substA_instantiate0A] at hTyL
      have hrt : HasTyA E I n Δ (.app (substA σ' f) (substA σ' a))
          (instantiate0A (substA σ a) (substA σ.up B)) :=
        .conv _ _ _ _ w w hApp' hTy' (eqNA_refl w) hTyL (.symm _ _ _ _ hcTy)
      show ConvA E I n Δ (substA σ (.app f a)) (substA σ' (.app f a))
        (substA σ (instantiate0A a B))
      rw [substA_instantiate0A]
      exact .app _ _ _ _ _ _ _ u v (hasTyA_func hE hI hR hIS h hf)
        (hasTyA_func hE hI hR hIS h ha) hBL hrt
  | _, _, .letE _ A u w value B body hA hv hTy hb => by
      have hAσ := hasTyA_substA hE hI hR hIS h.left hA
      have hAσ' := hasTyA_substA hE hI hR hIS h.right hA
      have hvσ := hasTyA_substA hE hI hR hIS h.left hv
      have hvσ' := hasTyA_substA hE hI hR hIS h.right hv
      have hcA := hasTyA_func hE hI hR hIS h hA
      have hcV := hasTyA_func hE hI hR hIS h hv
      have hup := convSubstA_upLet hE hI h hAσ hAσ' hvσ hvσ' hcA hcV
      have hbody' := hasTyA_substA hE hI hR hIS (substTyA_upLet hE hI h.right hAσ' hvσ') hb
      have hTy' := hasTyA_substA hE hI hR hIS h.right hTy
      rw [substA_instantiate0A] at hTy'
      have hLet' : HasTyA E I n Δ
          (.letE (substA σ' A) (substA σ' value) (substA σ'.up body))
          (instantiate0A (substA σ' value) (substA σ'.up B)) :=
        .letE _ _ u w _ _ _ hAσ' hvσ' hTy' hbody'
      have hcTy := hasTyA_func hE hI hR hIS h hTy
      rw [substA_instantiate0A, substA_instantiate0A] at hcTy
      have hTyL := hasTyA_substA hE hI hR hIS h.left hTy
      rw [substA_instantiate0A] at hTyL
      have hrt : HasTyA E I n Δ
          (.letE (substA σ' A) (substA σ' value) (substA σ'.up body))
          (instantiate0A (substA σ value) (substA σ.up B)) :=
        .conv _ _ _ _ w w hLet' hTy' (eqNA_refl w) hTyL (.symm _ _ _ _ hcTy)
      show ConvA E I n Δ (substA σ (.letE A value body)) (substA σ' (.letE A value body))
        (substA σ (instantiate0A value B))
      rw [substA_instantiate0A]
      exact .letE _ _ _ _ _ _ _ _ u hcA hcV (hasTyA_func hE hI hR hIS hup hb) hrt
  | _, _, .lit _ t _ hexp => by
      have ht := hasTyA_substA hE hI hR hIS h.left hexp
      rw [substA_natExpandA] at ht
      exact .refl _ _ _ (.lit _ t _ ht)
  | _, _, .conv _ e A B l u he hAl hlu hB hc =>
      .tyConv _ _ _ _ _ l u u (hasTyA_func hE hI hR hIS h he)
        (hasTyA_substA hE hI hR hIS h.left hAl) hlu
        (hasTyA_substA hE hI hR hIS h.left hB) (eqNA_refl u)
        (convA_substA hE hI hR hIS h.left hc)

/-! ## the identity inhabits `SubstTyA` (weakening supplies the tail) -/

def substTyA_id_succ (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA}
    (ih : SubstTyA E I n Γ SubstA.id Γ) (d : LocalDeclA) (i : Nat) (B : ExprA)
    (h : lookupTypeA (d :: Γ) (i + 1) = some B) :
    HasTyA E I n (d :: Γ) (SubstA.id (i + 1)) (substA SubstA.id B) := by
  let s := liftedTypeA d Γ h
  have hEq : B = liftA 0 1 s.orig := s.eq_lift
  rw [hEq]
  have hty := ih.ty i s.orig s.got
  rw [SubstA.id_apply, substA_id] at hty
  have hw := hasTyWeakenA hE hI d (Nat.zero_le _) hty
  rw [liftA_bvar, shiftIdx, if_pos (Nat.zero_le i)] at hw
  rw [SubstA.id_apply, substA_id]
  exact hw

def substTyA_id_succ_val (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA}
    (ih : SubstTyA E I n Γ SubstA.id Γ) (d : LocalDeclA) (i : Nat) (B v : ExprA)
    (hty : lookupTypeA (d :: Γ) (i + 1) = some B)
    (hval : lookupValueA (d :: Γ) (i + 1) = some v) :
    ConvA E I n (d :: Γ) (SubstA.id (i + 1)) (substA SubstA.id v) (substA SubstA.id B) := by
  let sB := liftedTypeA d Γ hty
  let sv := liftedValueA d Γ hval
  have hB : B = liftA 0 1 sB.orig := sB.eq_lift
  have hv : v = liftA 0 1 sv.orig := sv.eq_lift
  rw [hB, hv]
  have hc := ih.val i sB.orig sv.orig sB.got sv.got
  rw [SubstA.id_apply, substA_id, substA_id] at hc
  have hw := convWeakenA hE hI d (Nat.zero_le _) hc
  rw [liftA_bvar, shiftIdx, if_pos (Nat.zero_le i)] at hw
  rw [SubstA.id_apply, substA_id, substA_id]
  exact hw

def substTyA_id (hE : EnvClosedA E) (hI : IotaLiftA I) : {Γ : LCtxA} → CtxWfA E I n Γ →
    SubstTyA E I n Γ SubstA.id Γ
  | _, .nil => {
      ty := fun i _ h => by
        have hn : lookupTypeA [] i = none := by cases i <;> rfl
        rw [hn] at h; cases h
      val := fun i _ _ h => by
        have hn : lookupTypeA [] i = none := by cases i <;> rfl
        rw [hn] at h; cases h }
  | _, .assumption (A := A) (u := u) hΓ hA =>
      let ih := substTyA_id hE hI hΓ
      let d : LocalDeclA := .assumption A
      { ty := fun i B h => by
          cases i with
          | zero =>
              have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq h
              subst hB
              rw [SubstA.id_apply, substA_id]
              exact .bvar _ 0 _ u (lookupTypeA_cons_zero_assumption A _)
                (hasTyWeakenA hE hI d (Nat.zero_le _) hA)
          | succ i => exact substTyA_id_succ hE hI ih d i B h
        val := fun i B v hty hval => by
          cases i with
          | zero => exact (lookupValueA_zero_assumption_none hval).elim
          | succ i => exact substTyA_id_succ_val hE hI ih d i B v hty hval }
  | _, .letBinding (A := A) (v := v₀) (u := u) hΓ hA hv =>
      let ih := substTyA_id hE hI hΓ
      let d : LocalDeclA := .letBinding A v₀
      { ty := fun i B h => by
          cases i with
          | zero =>
              have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq h
              subst hB
              rw [SubstA.id_apply, substA_id]
              exact .bvar _ 0 _ u (lookupTypeA_cons_zero_let A v₀ _)
                (hasTyWeakenA hE hI d (Nat.zero_le _) hA)
          | succ i => exact substTyA_id_succ hE hI ih d i B h
        val := fun i B w hty hval => by
          cases i with
          | zero =>
              have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hty
              have hw : w = liftA 0 1 v₀ := lookupValueA_zero_let_eq hval
              subst hB; subst hw
              rw [SubstA.id_apply, substA_id, substA_id]
              exact .zetaLocal _ 0 _ _ (lookupValueA_cons_zero_let A v₀ _)
                (lookupTypeA_cons_zero_let A v₀ _)
                (hasTyWeakenA hE hI d (Nat.zero_le _) hv)
          | succ i => exact substTyA_id_succ_val hE hI ih d i B w hty hval }

/-- `0 ↦ t`, and the identity on the tail. The tail is why `CtxWfA` is required. -/
def substTyA_cons_id (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {t A : ExprA}
    (hΓ : CtxWfA E I n Γ) (ht : HasTyA E I n Γ t A) :
    SubstTyA E I n Γ (SubstA.cons t SubstA.id) (.assumption A :: Γ) where
  ty := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq hlu
        subst hB
        rw [SubstA.cons_zero, substA_cons_id_lift]
        exact ht
    | succ i =>
        let s := liftedTypeA (.assumption A) Γ hlu
        have hEq : B = liftA 0 1 s.orig := s.eq_lift
        rw [hEq]
        rw [SubstA.cons_succ, substA_cons_id_lift]
        have hty := (substTyA_id hE hI hΓ).ty i s.orig s.got
        rw [SubstA.id_apply, substA_id] at hty
        exact hty
  val := fun i B v hty hval => by
    cases i with
    | zero => exact (lookupValueA_zero_assumption_none hval).elim
    | succ i =>
        let sB := liftedTypeA (.assumption A) Γ hty
        let sv := liftedValueA (.assumption A) Γ hval
        have hB : B = liftA 0 1 sB.orig := sB.eq_lift
        have hv : v = liftA 0 1 sv.orig := sv.eq_lift
        rw [hB, hv]
        rw [SubstA.cons_succ, substA_cons_id_lift, substA_cons_id_lift]
        have hc := (substTyA_id hE hI hΓ).val i sB.orig sv.orig sB.got sv.got
        rw [SubstA.id_apply, substA_id, substA_id] at hc
        exact hc

def convSubstA_cons (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {t t' A : ExprA}
    (hΓ : CtxWfA E I n Γ) (ht : HasTyA E I n Γ t A) (ht' : HasTyA E I n Γ t' A)
    (hc : ConvA E I n Γ t t' A) :
    ConvSubstA E I n Γ (SubstA.cons t SubstA.id) (SubstA.cons t' SubstA.id)
      (.assumption A :: Γ) where
  left := substTyA_cons_id hE hI hΓ ht
  right := substTyA_cons_id hE hI hΓ ht'
  conv := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq hlu
        subst hB
        rw [SubstA.cons_zero, SubstA.cons_zero, substA_cons_id_lift]
        exact hc
    | succ i =>
        let s := liftedTypeA (.assumption A) Γ hlu
        have hEq : B = liftA 0 1 s.orig := s.eq_lift
        rw [hEq]
        rw [SubstA.cons_succ, SubstA.cons_succ, substA_cons_id_lift]
        have hty := (substTyA_id hE hI hΓ).ty i s.orig s.got
        rw [SubstA.id_apply, substA_id] at hty
        exact .refl _ _ _ hty

def hasTyA_inst0 (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} {e t A B : ExprA} {u : Level}
    (hΓ : CtxWfA E I n Γ) (he : HasTyA E I n (.assumption A :: Γ) e B)
    (ht : HasTyA E I n Γ t A) (_hA : HasTyA E I n Γ A (.sort u)) :
    HasTyA E I n Γ (instantiate0A t e) (instantiate0A t B) := by
  have hsub := hasTyA_substA hE hI hR hIS (substTyA_cons_id hE hI hΓ ht) he
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0] at hsub
  exact hsub

def hasTyA_func0 (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} {e t t' A B : ExprA} {u : Level}
    (hΓ : CtxWfA E I n Γ) (he : HasTyA E I n (.assumption A :: Γ) e B)
    (hc : ConvA E I n Γ t t' A) (_hA : HasTyA E I n Γ A (.sort u)) :
    ConvA E I n Γ (instantiate0A t e) (instantiate0A t' e) (instantiate0A t B) := by
  have ht := convA_left_subst hE hI hR hIS (substTyA_id hE hI hΓ) hc
  have ht' := convA_right_subst hE hI hR hIS (substTyA_id hE hI hΓ) hc
  rw [substA_id, substA_id] at ht
  rw [substA_id, substA_id] at ht'
  have hf := hasTyA_func hE hI hR hIS (convSubstA_cons hE hI hΓ ht ht' hc) he
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0, substA_cons_id_instantiate0] at hf
  exact hf

end SubstTy

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.substTyA_up
#print axioms Rcic.Declarative.Ann.substTyA_upLet
#print axioms Rcic.Declarative.Ann.hasTyA_pi_parts
#print axioms Rcic.Declarative.Ann.hasTyA_substA
#print axioms Rcic.Declarative.Ann.convA_substA
#print axioms Rcic.Declarative.Ann.hasTyA_type_subst
#print axioms Rcic.Declarative.Ann.convA_left_subst
#print axioms Rcic.Declarative.Ann.convA_right_subst
#print axioms Rcic.Declarative.Ann.convA_type_subst
#print axioms Rcic.Declarative.Ann.convSubstA_up
#print axioms Rcic.Declarative.Ann.convSubstA_upLet
#print axioms Rcic.Declarative.Ann.hasTyA_func
#print axioms Rcic.Declarative.Ann.substTyA_id
#print axioms Rcic.Declarative.Ann.substTyA_cons_id
#print axioms Rcic.Declarative.Ann.convSubstA_cons
#print axioms Rcic.Declarative.Ann.hasTyA_inst0
#print axioms Rcic.Declarative.Ann.hasTyA_func0
#print axioms Rcic.Declarative.Ann.substA_cons_id_lift
#print axioms Rcic.Declarative.Ann.substA_cons_id_instantiate0
#print axioms Rcic.Declarative.Ann.liftedTypeA
#print axioms Rcic.Declarative.Ann.liftedValueA
#print axioms Rcic.Declarative.Ann.lookupTypeA_zero_assumption_eq
#print axioms Rcic.Declarative.Ann.lookupTypeA_zero_let_eq
#print axioms Rcic.Declarative.Ann.lookupValueA_zero_let_eq
#print axioms Rcic.Declarative.Ann.lookupValueA_zero_assumption_none
#print axioms Rcic.Declarative.Ann.substTyA_succ
#print axioms Rcic.Declarative.Ann.substTyA_succ_val
#print axioms Rcic.Declarative.Ann.convSubstA_succ
#print axioms Rcic.Declarative.Ann.substA_shiftAt_cons_id
#print axioms Rcic.Declarative.Ann.cons_id_single
#print axioms Rcic.Declarative.Ann.substTyA_id_succ
#print axioms Rcic.Declarative.Ann.substTyA_id_succ_val

