import rcic.RcicDT0709EnvWf
import rcic.RcicTypedRowsWf

/-!
# DT-008's missing half (cc ruling on #6551)

`DT008T_closure_fixedType` (sealed :5111) settles the FIXED-type closure of
`ConvT`; the census r4 doc records the remaining four clauses of the ruling.
This segment builds them on the typed root:

* **(ii) `DT008T_tyConvT_equivalence`** — `TyConvT` is an equivalence on
  well-formed types. Reflexivity is conditioned on sort-typing (the
  `DT008T_closure_fixedType` convention: an unconditional refl would claim
  `TyConvT` at every expression, and `TyConvT.refl` itself needs no premise,
  so the conditioned clause is the honest reading of "on well-formed types");
  symmetry is the sealed `TyConvT.symmT`, transitivity the `TyConvT.trans`
  constructor. No row premise — pure chain properties.
* **(iii) `DT008T_convT_of_tyConvT`** — conversion transport along a type
  chain. The content is the sealed `convT_of_tyConv` (`ConvT.tyConv` folded
  over the chain); this is the DT-008-facing name for it.
* **(iv) `DT008T_convT_trans_cross`** — cross-type transitivity, stated as a
  row-conditional theorem: premise `hrows : TypedRowsWf E n` (the
  `ROWS_INTERFACE.md` interface, #6554), to be instantiated when the semantic
  rows land (`Ann.typedRowsWf_of_envWfT_semPrefix` is today's `InScope`
  producer). The middle term's two typings are reconciled by
  `DT012T_type_uniqueness_of_typedRowsWf` below — the DT-012 shape with the
  `InScope` premise replaced by `hrows`: sort/pi cases consume `sortRow`/`piRow`
  (Prop-valued, so the whole derivation stays `Nonempty`-valued), the `app`/`letE`
  cases ride the existing subst congruences under `EnvWfT`. `famAppRow` is
  unconsumed: family-application chains never arise inside one term's two
  typings.
* **(v) `convT_least`** — `ConvT`'s minimality as an induction principle: any
  relation closed under all eighteen generators contains `ConvT`. One closure
  hypothesis per constructor, recursive hypotheses carried at the subderivation
  positions.

`closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-- (ii) `TyConvT` is an equivalence on well-formed types: reflexivity at
    sort-typed types, symmetry (`TyConvT.symmT`, sealed :4696) and transitivity
    (`TyConvT.trans`) unconditionally. -/
theorem DT008T_tyConvT_equivalence {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (∀ T, (∃ u : Level, Nonempty (HasTyT E n Γ T (.sort u))) →
        Nonempty (TyConvT E n Γ T T))
    ∧ (∀ T T', TyConvT E n Γ T T' → Nonempty (TyConvT E n Γ T' T))
    ∧ (∀ T T' T'', TyConvT E n Γ T T' → TyConvT E n Γ T' T'' →
        Nonempty (TyConvT E n Γ T T'')) :=
  ⟨fun _ _ => ⟨.refl _ _⟩,
   fun _ _ h => ⟨h.symmT⟩,
   fun _ _ _ h₁ h₂ => ⟨.trans _ _ _ _ h₁ h₂⟩⟩

/-- (iii) closure under type conversion — the DT-008 face of the sealed
    `convT_of_tyConv` (:3662). -/
def DT008T_convT_of_tyConvT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T T' : Expr Nat}
    (h : ConvT E n Γ a b T) (hc : TyConvT E n Γ T T') :
    ConvT E n Γ a b T' :=
  convT_of_tyConv h hc

/-- (v) `ConvT` is the LEAST relation closed under its generators: any `R`
    satisfying one closure per `ConvT` constructor contains every derivation.
    Recursive positions carry both the subderivation and its `R`-image, so the
    principle composes at the `symm`/`trans`/congruence/`tyConv` arms the same
    way `ConvT.rec` does. -/
theorem convT_least {E : ResolvedEnv} {n : Nat}
    {R : LCtx → Expr Nat → Expr Nat → Expr Nat → Prop}
    (hrefl : ∀ {Γ a A}, HasTyT E n Γ a A → R Γ a a A)
    (hsymm : ∀ {Γ a b A}, ConvT E n Γ a b A → R Γ a b A → R Γ b a A)
    (htrans : ∀ {Γ a b c A}, ConvT E n Γ a b A → R Γ a b A →
        ConvT E n Γ b c A → R Γ b c A → R Γ a c A)
    (hbeta : ∀ {Γ A body arg B u}, HasTyT E n Γ A (.sort u) →
        HasTyT E n (.assumption A :: Γ) body B → HasTyT E n Γ arg A →
        R Γ (.app (.lam A body) arg) (instantiate0 arg body)
          (instantiate0 arg B))
    (hzeta : ∀ {Γ A value body B u}, HasTyT E n Γ A (.sort u) →
        HasTyT E n Γ value A →
        HasTyT E n (.letBinding A value :: Γ) body B →
        R Γ (.letE A value body) (instantiate0 value body)
          (instantiate0 value B))
    (hzetaLocal : ∀ {Γ i A v}, lookupValue Γ i = some v →
        lookupType Γ i = some A → HasTyT E n Γ v A → R Γ (.bvar i) v A)
    (hdelta : ∀ {Γ r ls m b}, E.members r = some m → m.body = some b →
        transparent m.mclass = true → ls.length = m.arity →
        levelsBounded n ls = true →
        HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) →
        R Γ (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hiota : ∀ {Γ lhs rhs T}, DerivedIota E lhs rhs →
        HasTyT E n Γ lhs T → HasTyT E n Γ rhs T → R Γ lhs rhs T)
    (hlit : ∀ {Γ t exp T}, LiteralExpansion t exp → HasTyT E n Γ exp T →
        R Γ (.lit t) exp T)
    (happ : ∀ {Γ f g a b A B}, ConvT E n Γ f g (.pi A B) → R Γ f g (.pi A B) →
        ConvT E n Γ a b A → R Γ a b A →
        R Γ (.app f a) (.app g b) (instantiate0 a B))
    (hlam : ∀ {Γ A A' b b' B u}, ConvT E n Γ A A' (.sort u) → R Γ A A' (.sort u) →
        ConvT E n (.assumption A :: Γ) b b' B → R (.assumption A :: Γ) b b' B →
        R Γ (.lam A b) (.lam A' b') (.pi A B))
    (hpi : ∀ {Γ A A' B B' u v}, ConvT E n Γ A A' (.sort u) → R Γ A A' (.sort u) →
        ConvT E n (.assumption A :: Γ) B B' (.sort v) →
        R (.assumption A :: Γ) B B' (.sort v) →
        R Γ (.pi A B) (.pi A' B') (.sort (.imax u v)))
    (hlet : ∀ {Γ A A' v v' b b' B u}, ConvT E n Γ A A' (.sort u) →
        R Γ A A' (.sort u) → ConvT E n Γ v v' A → R Γ v v' A →
        ConvT E n (.letBinding A v :: Γ) b b' B →
        R (.letBinding A v :: Γ) b b' B →
        R Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B))
    (hsorts : ∀ {Γ l₁ l₂}, eqN l₁ l₂ →
        R Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)))
    (hconsts : ∀ {Γ r ls ls' m}, E.members r = some m → ls.length = m.arity →
        levelsBounded n ls = true → levelsBounded n ls' = true →
        eqNList ls ls' →
        R Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype))
    (heta : ∀ {Γ f A B}, HasTyT E n Γ f (.pi A B) →
        R Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B))
    (hirr : ∀ {Γ P p q}, HasTyT E n Γ P (.sort .zero) →
        HasTyT E n Γ p P → HasTyT E n Γ q P → R Γ p q P)
    (htyConv : ∀ {Γ a b A A' u}, ConvT E n Γ a b A → R Γ a b A →
        ConvT E n Γ A A' (.sort u) → R Γ A A' (.sort u) → R Γ a b A')
    {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T) : R Γ a b T :=
  ConvT.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ a b T _ => R Γ a b T)
    (fun _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ h _ => hrefl h)
    (fun _ _ _ _ h ih => hsymm h ih)
    (fun _ _ _ _ _ h₁ h₂ ih₁ ih₂ => htrans h₁ ih₁ h₂ ih₂)
    (fun _ _ _ _ _ _ hA hbody harg _ _ _ => hbeta hA hbody harg)
    (fun _ _ _ _ _ _ hA hv hb _ _ _ => hzeta hA hv hb)
    (fun _ _ _ _ hval hty hv _ => hzetaLocal hval hty hv)
    (fun _ _ _ _ _ hres hbody htr hlen hwf hb _ => hdelta hres hbody htr hlen hwf hb)
    (fun _ _ _ _ h hlhs hrhs _ _ => hiota h hlhs hrhs)
    (fun _ _ _ _ h hexp _ => hlit h hexp)
    (fun _ _ _ _ _ _ _ h₁ h₂ ih₁ ih₂ => happ h₁ ih₁ h₂ ih₂)
    (fun _ _ _ _ _ _ _ hA hb ihA ihb => hlam hA ihA hb ihb)
    (fun _ _ _ _ _ _ _ hA hB ihA ihB => hpi hA ihA hB ihB)
    (fun _ _ _ _ _ _ _ _ _ hA hv hb ihA ihv ihb => hlet hA ihA hv ihv hb ihb)
    (fun _ _ _ h => hsorts h)
    (fun _ _ _ _ _ hres hlen hwf hwf' h => hconsts hres hlen hwf hwf' h)
    (fun _ _ _ _ h _ => heta h)
    (fun _ _ _ _ hP hp hq _ _ _ => hirr hP hp hq)
    (fun _ _ _ _ _ _ h hA ih ihA => htyConv h ih hA ihA)
    h

/-- the codomain chain lifted through a Π: each `ConvT`-at-a-sort link under
    the domain binder re-lifts by `ConvT.pi` at a reflexive domain. -/
def tyConvT_pi_cod {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    {u : Level} (hA : HasTyT E n Γ A (.sort u)) :
    {B B' : Expr Nat} → TyConvT E n (.assumption A :: Γ) B B' →
    TyConvT E n Γ (.pi A B) (.pi A B')
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ _ hc =>
      .of _ _ _ _ (ConvT.pi _ _ _ _ _ _ _ (ConvT.refl _ _ _ hA) hc)
  | _, _, .trans _ _ _ _ h₁ h₂ =>
      .trans _ _ _ _ (tyConvT_pi_cod hA h₁) (tyConvT_pi_cod hA h₂)

/-- `convT_subst0_tyConvT`'s let-binder twin: a `TyConvT` chain under
    `letBinding t w0` instantiates at `w0`, each `.of` link by
    `convT_substLet_of_envWfT` at `j = 0`. -/
def convT_substLet0_tyConvT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {t w0 : Expr Nat} {Γ : LCtx} :
    {X Y : Expr Nat} → TyConvT E n (.letBinding t w0 :: Γ) X Y →
    HasTyT E n Γ w0 t →
    Nonempty (TyConvT E n Γ (instantiate0 w0 X) (instantiate0 w0 Y))
  | _, _, .refl _ _, _ => ⟨.refl _ _⟩
  | _, _, .of _ _ _ _ hc, hv => by
      have hc' := convT_substLet_of_envWfT hW t w0 (j := 0) hc (by simp)
        (by rw [lift_zero, lift_zero]; exact hv)
      rw [lift_zero] at hc'
      exact ⟨.of _ _ _ _ hc'⟩
  | _, _, .trans _ _ _ _ h₁ h₂, hv =>
      (convT_substLet0_tyConvT hW h₁ hv).elim fun c₁ =>
        (convT_substLet0_tyConvT hW h₂ hv).elim fun c₂ =>
          ⟨.trans _ _ _ _ c₁ c₂⟩

/-- DT-012's shape at the semantic interface: two typings of one term have a
    `TyConvT` between their types, given `hrows` in place of `InScope`. The
    derivation stays `Nonempty`-valued so `piRow`'s existence form composes;
    `sortRow` collapses the sort chains at the `.pi` arm, `piRow` injects the
    Π chain at the `.app` arm, and the `instantiate0` closures ride
    `convT_subst0_tyConvT` / `convT_substLet0_tyConvT` under `EnvWfT`.
    `famAppRow` is not consumed — two typings of ONE term never produce a
    family-application chain. -/
def DT012T_type_uniqueness_of_typedRowsWf {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} (hrows : TypedRowsWf E n) :
    {Γ : LCtx} → CtxWfT E n Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    {B : Expr Nat} → HasTyT E n Γ e B → Nonempty (TyConvT E n Γ A B)
  | _, _, _, _, .sort _ l, _, hB => ⟨hasTyTInv_sortT hB rfl⟩
  | _, _, _, _, .bvar _ _ _ h, _, hB => by
      obtain ⟨A', hlk', hcv⟩ := hasTyTInv_bvar hB rfl
      obtain rfl : A' = _ := Option.some.inj (hlk'.symm.trans h)
      exact ⟨hcv⟩
  | _, _, _, _, .const _ _ _ _ hres _ _, _, hB => by
      obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const hB rfl
      obtain rfl : m' = _ := Option.some.inj (hres'.symm.trans hres)
      exact ⟨hcv⟩
  | Γ, hΓ, _, _, .pi _ A u _ _ hA hB, _, hBt => by
      obtain ⟨u', v', hA', hB', hcv⟩ := hasTyTInv_pi hBt rfl
      obtain ⟨cA⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ hA hA'
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓA hB hB'
      exact ⟨.trans _ _ _ _
        (.of _ _ _ _ (ConvT.sorts _ _ _
          (Ann.eqNA_imax (hrows.sortRow hΓ cA) (hrows.sortRow hΓA cB)))) hcv⟩
  | Γ, hΓ, _, _, .lam _ A u _ _ hA hb, _, hBt => by
      obtain ⟨_, B', _, hb', hcv⟩ := hasTyTInv_lam hBt rfl
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓA hb hb'
      exact ⟨.trans _ _ _ _ (tyConvT_pi_cod hA cB) hcv⟩
  | _, hΓ, _, _, .app _ _ _ _ _ hf ha, _, hBt => by
      obtain ⟨A', B', hf', _, hcv⟩ := hasTyTInv_app hBt rfl
      obtain ⟨cF⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ hf hf'
      obtain ⟨cB⟩ := (hrows.piRow hΓ cF).2
      obtain ⟨cI⟩ := convT_subst0_tyConvT hW cB ha
      exact ⟨.trans _ _ _ _ cI hcv⟩
  | Γ, hΓ, _, _, .letE _ A u v _ _ hA hv hb, _, hBt => by
      obtain ⟨_, B', _, _, hb', hcv⟩ := hasTyTInv_letE hBt rfl
      have hΓL : CtxWfT E n (.letBinding A v :: Γ) := .letBinding Γ A u v hΓ hA hv
      obtain ⟨cB⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓL hb hb'
      obtain ⟨cI⟩ := convT_substLet0_tyConvT hW cB hv
      exact ⟨.trans _ _ _ _ cI hcv⟩
  | _, hΓ, _, _, .lit _ _ _ hexp, _, hBt => by
      obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit hBt rfl
      obtain ⟨c⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ hexp hnat
      exact ⟨.trans _ _ _ _ c hcv⟩
  | _, hΓ, _, _, .conv _ _ _ _ _ h hc, _, hBt => by
      obtain ⟨c⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ h hBt
      exact ⟨.trans _ _ _ _ (TyConvT.symmT (.of _ _ _ _ hc)) c⟩

/-- (iv) cross-type transitivity, row-conditional: the middle term's two types
    are reconciled by `DT012T_type_uniqueness_of_typedRowsWf`, the right leg is
    transported by (iii), and `ConvT.trans` closes. Premise `hrows` is the
    `TypedRowsWf` interface — discharged when the semantic rows land (today's
    producer is `Ann.typedRowsWf_of_envWfT_semPrefix` at `InScope`). -/
theorem DT008T_convT_trans_cross {E : ResolvedEnv} {n : Nat}
    (hrows : TypedRowsWf E n) (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b c T T' : Expr Nat}
    (h₁ : ConvT E n Γ a b T) (h₂ : ConvT E n Γ b c T') :
    ∃ T'' : Expr Nat, Nonempty (ConvT E n Γ a c T'') := by
  obtain ⟨_, ⟨hbT⟩⟩ := convT_endpoints hW hΓ h₁
  obtain ⟨⟨hbT'⟩, _⟩ := convT_endpoints hW hΓ h₂
  obtain ⟨hU⟩ := DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ hbT hbT'
  exact ⟨T, ⟨ConvT.trans _ _ _ _ _ h₁ (convT_of_tyConv h₂ hU.symmT)⟩⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.DT008T_tyConvT_equivalence
#print axioms Rcic.Declarative.DT008T_convT_of_tyConvT
#print axioms Rcic.Declarative.convT_least
#print axioms Rcic.Declarative.tyConvT_pi_cod
#print axioms Rcic.Declarative.convT_substLet0_tyConvT
#print axioms Rcic.Declarative.DT012T_type_uniqueness_of_typedRowsWf
#print axioms Rcic.Declarative.DT008T_convT_trans_cross
