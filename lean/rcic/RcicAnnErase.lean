import rcic.RcicAnnIotaCorr
import rcic.RcicTypedJ

/-!
# M3-c1 — erasure of the copy's derivations

The bridge's erasure half: a derivation on the copy erases to a derivation of main's syntax, in
the erased environment and context. It is stated for ANY target, a typing predicate `HT` and a
conversion predicate `CT` on `Expr Nat`, that is closed under the copy's rules with their
premises erased (`CopyRulesClosed`). The typed root that lands on `main` (M3-b) instantiates it.
Every field keeps all of the copy rule's premises, so a typed presentation whose rules have fewer
premises satisfies each field by dropping them. The typed face's rules are of that kind (R-TypedRules,
measured in M3-b-0).

The targets are propositions, by M3-b-0 O5: the copy's rows are existence results, so the landing
states its consumers as existence statements. A `Type`-valued root enters as `Nonempty`.

ι is the one rule that does not erase by syntax. The copy's ι rules (`ConvA.iota`, and at a struct
group `ConvA.structIota`, W-1 (e)) read its interface's function; main's reads `DerivedIota`. The
erasure takes the correspondence on the function's graph as a premise (`hI`). At the concrete ι it is
`IotaErasesA` (`RcicAnnIotaCorr`), which every admitted environment has (`iotaErasesA_of_envWfA`): since
W-1 (e) the copy's ι contracts to the fields everywhere, as main's does. The entries below read it
(`hNS`, named for its callers since W-1 (b′)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the copy's rules, erased -/

/-- a typing predicate `HT` and a conversion predicate `CT` on main's syntax are CLOSED UNDER THE
    COPY'S RULES when each rule of `HasTyA` / `ConvA`, with every premise and the conclusion
    erased, holds of them. The `pi` / `lam` annotations are gone, so the binders that only
    annotated are gone too. -/
structure CopyRulesClosed (E : ResolvedEnv) (n : Nat) (HT : LCtx → Expr Nat → Expr Nat → Prop)
    (CT : LCtx → Expr Nat → Expr Nat → Expr Nat → Prop) : Prop where
  sort : ∀ Γ l, HT Γ (.sort l) (.sort (.succ l))
  bvar : ∀ Γ i A u, lookupType Γ i = some A → HT Γ A (.sort u) → HT Γ (.bvar i) A
  const : ∀ Γ r ls (m : CheckedMember) u, E.members r = some m → ls.length = m.arity →
    levelsBounded n ls = true → HT Γ (instantiateLevels ls m.mtype) (.sort u) →
    HT Γ (.const r ls) (instantiateLevels ls m.mtype)
  pi : ∀ Γ A u B v, HT Γ A (.sort u) → HT (.assumption A :: Γ) B (.sort v) →
    HT Γ (.pi A B) (.sort (.imax u v))
  lam : ∀ Γ A u body B v, HT Γ A (.sort u) → HT (.assumption A :: Γ) B (.sort v) →
    HT (.assumption A :: Γ) body B → HT Γ (.lam A body) (.pi A B)
  app : ∀ Γ f a A B v w, HT (.assumption A :: Γ) B (.sort v) → HT Γ (instantiate0 a B) (.sort w) →
    HT Γ f (.pi A B) → HT Γ a A → HT Γ (.app f a) (instantiate0 a B)
  letE : ∀ Γ A u w value B body, HT Γ A (.sort u) → HT Γ value A →
    HT Γ (instantiate0 value B) (.sort w) → HT (.letBinding A value :: Γ) body B →
    HT Γ (.letE A value body) (instantiate0 value B)
  lit : ∀ Γ t T, HT Γ (natExpand t) T → HT Γ (.lit t) T
  conv : ∀ Γ e A B l u, HT Γ e A → HT Γ A (.sort l) → eqN l u → HT Γ B (.sort u) →
    CT Γ A B (.sort u) → HT Γ e B
  refl : ∀ Γ a A, HT Γ a A → CT Γ a a A
  symm : ∀ Γ a b A, CT Γ a b A → CT Γ b a A
  trans : ∀ Γ a b c A, CT Γ a b A → CT Γ b c A → CT Γ a c A
  beta : ∀ Γ A u body arg B, HT Γ A (.sort u) → HT (.assumption A :: Γ) body B → HT Γ arg A →
    HT Γ (instantiate0 arg body) (instantiate0 arg B) →
    CT Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B)
  zeta : ∀ Γ A value body B u, HT Γ A (.sort u) → HT Γ value A →
    HT (.letBinding A value :: Γ) body B → HT Γ (instantiate0 value body) (instantiate0 value B) →
    CT Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B)
  zetaLocal : ∀ Γ i A v, lookupValue Γ i = some v → lookupType Γ i = some A → HT Γ v A →
    CT Γ (.bvar i) v A
  delta : ∀ Γ r ls (m : CheckedMember) b, E.members r = some m → m.body = some b →
    transparent m.mclass = true → ls.length = m.arity → levelsBounded n ls = true →
    HT Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) →
    CT Γ (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype)
  iota : ∀ Γ lhs rhs T, Nonempty (DerivedIota E lhs rhs) → HT Γ lhs T → HT Γ rhs T →
    CT Γ lhs rhs T
  litConv : ∀ Γ t T, HT Γ (natExpand t) T → CT Γ (.lit t) (natExpand t) T
  appConv : ∀ Γ f g a b A B v, CT Γ f g (.pi A B) → CT Γ a b A → HT (.assumption A :: Γ) B (.sort v) →
    HT Γ (.app g b) (instantiate0 a B) → CT Γ (.app f a) (.app g b) (instantiate0 a B)
  lamConv : ∀ Γ A A' b b' B u u', eqN u u' → CT Γ A A' (.sort u) →
    CT (.assumption A :: Γ) b b' B → HT Γ (.lam A' b') (.pi A B) →
    CT Γ (.lam A b) (.lam A' b') (.pi A B)
  piConv : ∀ Γ A A' B B' u u' v v', eqN u u' → eqN v v' → CT Γ A A' (.sort u) →
    CT (.assumption A :: Γ) B B' (.sort v) → HT Γ (.pi A' B') (.sort (.imax u v)) →
    CT Γ (.pi A B) (.pi A' B') (.sort (.imax u v))
  letEConv : ∀ Γ A A' v v' b b' B u, CT Γ A A' (.sort u) → CT Γ v v' A →
    CT (.letBinding A v :: Γ) b b' B → HT Γ (.letE A' v' b') (instantiate0 v B) →
    CT Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B)
  sorts : ∀ Γ l₁ l₂, eqN l₁ l₂ → CT Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))
  consts : ∀ Γ r ls ls' (m : CheckedMember), E.members r = some m → ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    HT Γ (.const r ls') (instantiateLevels ls m.mtype) →
    CT Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype)
  eta : ∀ Γ f A B, HT Γ f (.pi A B) → HT Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) →
    CT Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B)
  irr : ∀ Γ P p q, HT Γ P (.sort .zero) → HT Γ p P → HT Γ q P → CT Γ p q P
  tyConv : ∀ Γ a b A A' l l' u, CT Γ a b A → HT Γ A (.sort l) → eqN l u → HT Γ A' (.sort l') →
    eqN l' u → CT Γ A A' (.sort u) → CT Γ a b A'

/-! ## (2) erasure -/

section Erase
variable {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {HT : LCtx → Expr Nat → Expr Nat → Prop}
  {CT : LCtx → Expr Nat → Expr Nat → Expr Nat → Prop}

theorem members_eraseEnv_some {r : Nat} {m : CheckedMemberA} (h : EA.members r = some m) :
    (eraseEnv EA).members r = some (eraseMember m) := by
  rw [members_eraseEnv, h]; rfl

theorem lookupType_eraseCtx_some {Γ : LCtxA} {i : Nat} {A : ExprA} (h : lookupTypeA Γ i = some A) :
    lookupType (eraseCtx Γ) i = some (erase A) := by
  rw [lookupType_eraseCtx, h]; rfl

theorem lookupValue_eraseCtx_some {Γ : LCtxA} {i : Nat} {v : ExprA} (h : lookupValueA Γ i = some v) :
    lookupValue (eraseCtx Γ) i = some (erase v) := by
  rw [lookupValue_eraseCtx, h]; rfl

mutual

/-- ERASURE OF TYPING: a typing on the copy erases to `HT`, in the erased context, when `HT` /
    `CT` are closed under the copy's rules and the interface's ι steps are derived ι steps of the
    erased environment. -/
theorem erase_hasTyA (C : CopyRulesClosed (eraseEnv EA) n HT CT)
    (hI : ∀ lhs rhs, I.fn lhs = some rhs → Nonempty (DerivedIota (eraseEnv EA) (erase lhs) (erase rhs))) :
    {Γ : LCtxA} → {e T : ExprA} → HasTyA EA I n Γ e T → HT (eraseCtx Γ) (erase e) (erase T)
  | _, _, _, .sort Γ l => C.sort _ l
  | _, _, _, .bvar Γ i A u h hA =>
      C.bvar _ i _ u (lookupType_eraseCtx_some h) (erase_hasTyA C hI hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT => by
      have hT' := erase_hasTyA C hI hT
      rw [erase_instantiateLevelsA] at hT' ⊢
      exact C.const _ r ls (eraseMember m) u (members_eraseEnv_some hres) hlen hwf hT'
  | _, _, _, .pi Γ A u B v hA hB =>
      C.pi _ _ u _ v (erase_hasTyA C hI hA) (erase_hasTyA C hI hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      C.lam _ _ u _ _ v (erase_hasTyA C hI hA) (erase_hasTyA C hI hB) (erase_hasTyA C hI hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha => by
      have hTy' := erase_hasTyA C hI hTy
      rw [erase_instantiate0A] at hTy' ⊢
      exact C.app _ _ _ _ _ v w (erase_hasTyA C hI hB) hTy' (erase_hasTyA C hI hf)
        (erase_hasTyA C hI ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb => by
      have hTy' := erase_hasTyA C hI hTy
      rw [erase_instantiate0A] at hTy' ⊢
      exact C.letE _ _ u w _ _ _ (erase_hasTyA C hI hA) (erase_hasTyA C hI hv) hTy'
        (erase_hasTyA C hI hb)
  | _, _, _, .lit Γ t T hexp => by
      have h := erase_hasTyA C hI hexp
      rw [erase_natExpandA] at h
      exact C.lit _ t _ h
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      C.conv _ _ _ _ l u (erase_hasTyA C hI h) (erase_hasTyA C hI hAl) hlu (erase_hasTyA C hI hB)
        (erase_convA C hI hc)

/-- ERASURE OF CONVERSION: a conversion on the copy erases to `CT`. -/
theorem erase_convA (C : CopyRulesClosed (eraseEnv EA) n HT CT)
    (hI : ∀ lhs rhs, I.fn lhs = some rhs → Nonempty (DerivedIota (eraseEnv EA) (erase lhs) (erase rhs))) :
    {Γ : LCtxA} → {a b T : ExprA} → ConvA EA I n Γ a b T →
      CT (eraseCtx Γ) (erase a) (erase b) (erase T)
  | _, _, _, _, .refl Γ a A h => C.refl _ _ _ (erase_hasTyA C hI h)
  | _, _, _, _, .symm Γ a b A h => C.symm _ _ _ _ (erase_convA C hI h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      C.trans _ _ _ _ _ (erase_convA C hI h1) (erase_convA C hI h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred => by
      have hred' := erase_hasTyA C hI hred
      rw [erase_instantiate0A, erase_instantiate0A] at hred' ⊢
      exact C.beta _ _ u _ _ _ (erase_hasTyA C hI hA) (erase_hasTyA C hI hbody)
        (erase_hasTyA C hI harg) hred'
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred => by
      have hred' := erase_hasTyA C hI hred
      rw [erase_instantiate0A, erase_instantiate0A] at hred' ⊢
      exact C.zeta _ _ _ _ _ u (erase_hasTyA C hI hA) (erase_hasTyA C hI hv)
        (erase_hasTyA C hI hb) hred'
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      C.zetaLocal _ i _ _ (lookupValue_eraseCtx_some hval) (lookupType_eraseCtx_some hty)
        (erase_hasTyA C hI hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb => by
      have hb' := erase_hasTyA C hI hb
      rw [erase_instantiateLevelsA, erase_instantiateLevelsA] at hb' ⊢
      exact C.delta _ r ls (eraseMember m) (erase b) (members_eraseEnv_some hres)
        (by show m.bodyA.map erase = some (erase b); rw [hbody]; rfl) htr hlen hwf hb'
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      C.iota _ _ _ _ (hI lhs rhs h.graph) (erase_hasTyA C hI hlhs) (erase_hasTyA C hI hrhs)
  | _, _, _, _, .structIota Γ f a rhs _ T _ _ h hlhs hrhs _ =>
      -- W-1 (e): `main`'s ι, from ι's graph; the carried conversion is the copy's alone
      C.iota _ _ _ _ (hI (.app f a) rhs h) (erase_hasTyA C hI hlhs) (erase_hasTyA C hI hrhs)
  | _, _, _, _, .lit Γ t T hexp => by
      have h := erase_hasTyA C hI hexp
      rw [erase_natExpandA] at h ⊢
      exact C.litConv _ t _ h
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt => by
      have hrt' := erase_hasTyA C hI hrt
      rw [erase_instantiate0A] at hrt' ⊢
      exact C.appConv _ _ _ _ _ _ _ v (erase_convA C hI h1) (erase_convA C hI h2)
        (erase_hasTyA C hI hB) hrt'
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      C.lamConv _ _ _ _ _ _ u u' hu (erase_convA C hI hA) (erase_convA C hI hb)
        (erase_hasTyA C hI hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      C.piConv _ _ _ _ _ u u' v v' hu hv (erase_convA C hI hA) (erase_convA C hI hB)
        (erase_hasTyA C hI hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt => by
      have hrt' := erase_hasTyA C hI hrt
      rw [erase_instantiate0A] at hrt' ⊢
      exact C.letEConv _ _ _ _ _ _ _ _ u (erase_convA C hI hA) (erase_convA C hI hv)
        (erase_convA C hI hb) hrt'
  | _, _, _, _, .sorts Γ l₁ l₂ h => C.sorts _ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt => by
      have hrt' := erase_hasTyA C hI hrt
      rw [erase_instantiateLevelsA] at hrt' ⊢
      exact C.consts _ r ls ls' (eraseMember m) (members_eraseEnv_some hres) hlen hwf hwf' h hrt'
  | _, _, _, _, .eta Γ f A B u v h hrt => by
      have hrt' := erase_hasTyA C hI hrt
      show CT (eraseCtx Γ) (.lam (erase A) (.app (erase (liftA 0 1 f)) (.bvar 0))) (erase f)
        (.pi (erase A) (erase B))
      change HT (eraseCtx Γ) (.lam (erase A) (.app (erase (liftA 0 1 f)) (.bvar 0)))
        (.pi (erase A) (erase B)) at hrt'
      rw [erase_liftA] at hrt' ⊢
      exact C.eta _ _ _ _ (erase_hasTyA C hI h) hrt'
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      C.irr _ _ _ _ (erase_hasTyA C hI hP) (erase_hasTyA C hI hp) (erase_hasTyA C hI hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      C.tyConv _ _ _ _ _ l l' u (erase_convA C hI h) (erase_hasTyA C hI hAl) hlu
        (erase_hasTyA C hI hA'l) hl'u (erase_convA C hI hA)

end

/-- the derived chain: `TyConvA` erases into any relation that is reflexive, transitive and
    contains `CT` at a sort between two typed types (the shape of main's `TyConv`). -/
theorem erase_tyConvA (C : CopyRulesClosed (eraseEnv EA) n HT CT)
    (hI : ∀ lhs rhs, I.fn lhs = some rhs → Nonempty (DerivedIota (eraseEnv EA) (erase lhs) (erase rhs)))
    {TT : LCtx → Expr Nat → Expr Nat → Prop} (hrefl : ∀ Γ A, TT Γ A A)
    (hof : ∀ Γ A B l l' u, HT Γ A (.sort l) → eqN l u → HT Γ B (.sort l') → eqN l' u →
      CT Γ A B (.sort u) → TT Γ A B)
    (htrans : ∀ Γ A B C, TT Γ A B → TT Γ B C → TT Γ A C) :
    {Γ : LCtxA} → {A B : ExprA} → TyConvA EA I n Γ A B → TT (eraseCtx Γ) (erase A) (erase B)
  | _, _, _, .refl Γ A => hrefl _ _
  | _, _, _, .of Γ A B l l' u hAl hlu hBl hl'u h =>
      hof _ _ _ l l' u (erase_hasTyA C hI hAl) hlu (erase_hasTyA C hI hBl) hl'u (erase_convA C hI h)
  | _, _, _, .trans Γ A B C' h1 h2 =>
      htrans _ _ _ _ (erase_tyConvA C hI hrefl hof htrans h1) (erase_tyConvA C hI hrefl hof htrans h2)

/-! ## (3) at the concrete ι, under the copy's admission -/

/-- at the concrete ι the erasure's correspondence is the environment's `IotaErasesA`. -/
theorem erase_hasTyA_wf (hNS : IotaErasesA EA)
    (C : CopyRulesClosed (eraseEnv EA) n HT CT)
    {Γ : LCtxA} {e T : ExprA} (h : HasTyA EA (iotaIfaceA EA) n Γ e T) :
    HT (eraseCtx Γ) (erase e) (erase T) :=
  erase_hasTyA (I := iotaIfaceA EA) C hNS h

theorem erase_convA_wf (hNS : IotaErasesA EA)
    (C : CopyRulesClosed (eraseEnv EA) n HT CT)
    {Γ : LCtxA} {a b T : ExprA} (h : ConvA EA (iotaIfaceA EA) n Γ a b T) :
    CT (eraseCtx Γ) (erase a) (erase b) (erase T) :=
  erase_convA (I := iotaIfaceA EA) C hNS h

end Erase

/-! ## (4) satisfiability: `main`'s current rules are closed under the copy's

`main`'s current `HasTy` and untyped `Conv` satisfy the interface at a positive universe arity:
every erased copy rule is one of main's rules with premises dropped (the six reduction lines
through `Conv.step`, ι through `Step.iota` from the derived step). So the interface is consistent and
does not over-demand. The instance says little about the copy: `main`'s `Conv` relates every pair of
terms (R-ConvCollapse), which is why the landing replaces it by the typed root (M3-b). At arity `0`
main's `const` rule reads a dummy-eval bound that `levelsBounded` does not give (R-LevelBound). -/

theorem copyRulesClosed_main {E : ResolvedEnv} {n : Nat} (hn : 0 < n) :
    CopyRulesClosed E n (fun Γ e T => Nonempty (HasTy E n Γ e T)) (fun Γ a b _ => Nonempty (Conv E n Γ a b)) where
  sort Γ l := ⟨.sort Γ l⟩
  bvar Γ i A _ h _ := ⟨.bvar Γ i A h⟩
  const Γ r ls m _ hres hlen _ _ := ⟨.const Γ r ls m hres hlen (fun _ _ => ⟨0, Or.inr hn⟩)⟩
  pi Γ A u B v := fun ⟨hA⟩ ⟨hB⟩ => ⟨.pi Γ A u B v hA hB⟩
  lam Γ A u body B _ := fun ⟨hA⟩ _ ⟨hb⟩ => ⟨.lam Γ A u body B hA hb⟩
  app Γ f a A B _ _ := fun _ _ ⟨hf⟩ ⟨ha⟩ => ⟨.app Γ f a A B hf ha⟩
  letE Γ A u _ value B body := fun ⟨hA⟩ ⟨hv⟩ _ ⟨hb⟩ => ⟨.letE Γ A u value B hA hv hb⟩
  lit Γ t T := fun ⟨h⟩ => ⟨.lit Γ t T h⟩
  conv Γ e A B _ _ := fun ⟨h⟩ _ _ _ ⟨hc⟩ => ⟨.conv Γ e A B h hc⟩
  refl Γ a _ _ := ⟨.refl Γ a⟩
  symm Γ a b _ := fun ⟨h⟩ => ⟨.symm Γ a b h⟩
  trans Γ a b c _ := fun ⟨h1⟩ ⟨h2⟩ => ⟨.trans Γ a b c h1 h2⟩
  beta Γ A _ body arg _ _ _ _ _ := ⟨.step Γ _ _ (.beta Γ A body arg)⟩
  zeta Γ A value body _ _ _ _ _ _ := ⟨.step Γ _ _ (.zeta Γ A value body)⟩
  zetaLocal Γ i _ v hval _ _ := ⟨.step Γ _ _ (.zetaLocal Γ i v hval)⟩
  delta Γ r ls m b hres hbody htr _ _ _ := ⟨.step Γ _ _ (.delta Γ r ls m b hres hbody htr)⟩
  iota Γ lhs rhs _ := fun ⟨h⟩ _ _ => ⟨.step Γ _ _ (.iota Γ lhs rhs h)⟩
  litConv Γ t _ _ := ⟨.step Γ _ _ (.lit Γ t _ (.of t))⟩
  appConv Γ f g a b _ _ _ := fun ⟨h1⟩ ⟨h2⟩ _ _ => ⟨.app Γ f g a b h1 h2⟩
  lamConv Γ A A' b b' _ _ _ _ := fun ⟨hA⟩ ⟨hb⟩ _ => ⟨.lam Γ A A' b b' hA hb⟩
  piConv Γ A A' B B' _ _ _ _ _ _ := fun ⟨hA⟩ ⟨hB⟩ _ => ⟨.pi Γ A A' B B' hA hB⟩
  letEConv Γ A A' v v' b b' _ _ := fun ⟨hA⟩ ⟨hv⟩ ⟨hb⟩ _ => ⟨.letE Γ A A' v v' b b' hA hv hb⟩
  sorts Γ l₁ l₂ h := ⟨.sorts Γ l₁ l₂ h⟩
  consts Γ r ls ls' _ _ _ _ _ h _ := ⟨.consts Γ r ls ls' h⟩
  eta Γ f A B := fun ⟨h⟩ _ => ⟨.eta Γ f A B h⟩
  irr Γ P p q := fun ⟨hP⟩ ⟨hp⟩ ⟨hq⟩ => ⟨.irr Γ P p q hP hp hq⟩
  tyConv _ _ _ _ _ _ _ _ h _ _ _ _ _ := h

/-- the copy's typings are typings of `main`'s current rules, on the erasure, at a positive arity
    and under the copy's admission. -/
theorem hasTy_main_of_hasTyA {J : IotaIfaceA} {EA : ResolvedEnvA} (_hW : EnvWfA J EA)
    (hNS : IotaErasesA EA) {n : Nat}
    (hn : 0 < n) {Γ : LCtxA} {e T : ExprA} (h : HasTyA EA (iotaIfaceA EA) n Γ e T) :
    Nonempty (HasTy (eraseEnv EA) n (eraseCtx Γ) (erase e) (erase T)) :=
  erase_hasTyA_wf hNS (copyRulesClosed_main hn) h

/-! ## (5) into R-CIC's typed judgment

`HasTyT` / `ConvT` (`RcicTypedJ`, R-TypedRules on `main`'s syntax) satisfy the interface at every
arity: each field is one of their rules with the copy's extra premises dropped. So the copy's
derivations, under its admission, are derivations of the typed judgment on the erasure. That is the
bridge's erasure direction, into the judgment the landing makes `main`'s root. -/

theorem copyRulesClosed_typed {E : ResolvedEnv} {n : Nat} :
    CopyRulesClosed E n (fun Γ e T => Nonempty (HasTyT E n Γ e T))
      (fun Γ a b T => Nonempty (ConvT E n Γ a b T)) where
  sort Γ l := ⟨.sort Γ l⟩
  bvar Γ i A _ h _ := ⟨.bvar Γ i A h⟩
  const Γ r ls m _ hres hlen hwf _ := ⟨.const Γ r ls m hres hlen hwf⟩
  pi Γ A u B v := fun ⟨hA⟩ ⟨hB⟩ => ⟨.pi Γ A u B v hA hB⟩
  lam Γ A u body B _ := fun ⟨hA⟩ _ ⟨hb⟩ => ⟨.lam Γ A u body B hA hb⟩
  app Γ f a A B _ _ := fun _ _ ⟨hf⟩ ⟨ha⟩ => ⟨.app Γ f a A B hf ha⟩
  letE Γ A u _ value B body := fun ⟨hA⟩ ⟨hv⟩ _ ⟨hb⟩ => ⟨.letE Γ A u value B body hA hv hb⟩
  lit Γ t T := fun ⟨h⟩ => ⟨.lit Γ t T h⟩
  conv Γ e A B _ u := fun ⟨h⟩ _ _ _ ⟨hc⟩ => ⟨.conv Γ e A B u h hc⟩
  refl Γ a A := fun ⟨h⟩ => ⟨.refl Γ a A h⟩
  symm Γ a b A := fun ⟨h⟩ => ⟨.symm Γ a b A h⟩
  trans Γ a b c A := fun ⟨h1⟩ ⟨h2⟩ => ⟨.trans Γ a b c A h1 h2⟩
  beta Γ A u body arg B := fun ⟨hA⟩ ⟨hb⟩ ⟨ha⟩ _ => ⟨.beta Γ A body arg B u hA hb ha⟩
  zeta Γ A value body B u := fun ⟨hA⟩ ⟨hv⟩ ⟨hb⟩ _ => ⟨.zeta Γ A value body B u hA hv hb⟩
  zetaLocal Γ i A v hval hty := fun ⟨hv⟩ => ⟨.zetaLocal Γ i A v hval hty hv⟩
  delta Γ r ls m b hres hbody htr hlen hwf := fun ⟨hb⟩ =>
    ⟨.delta Γ r ls m b hres hbody htr hlen hwf hb⟩
  iota Γ lhs rhs T := fun ⟨h⟩ ⟨hl⟩ ⟨hr⟩ => ⟨.iota Γ lhs rhs T h hl hr⟩
  litConv Γ t T := fun ⟨h⟩ => ⟨.lit Γ t _ T (.of t) h⟩
  appConv Γ f g a b A B _ := fun ⟨h1⟩ ⟨h2⟩ _ _ => ⟨.app Γ f g a b A B h1 h2⟩
  lamConv Γ A A' b b' B u _ _ := fun ⟨hA⟩ ⟨hb⟩ _ => ⟨.lam Γ A A' b b' B u hA hb⟩
  piConv Γ A A' B B' u _ v _ _ _ := fun ⟨hA⟩ ⟨hB⟩ _ => ⟨.pi Γ A A' B B' u v hA hB⟩
  letEConv Γ A A' v v' b b' B u := fun ⟨hA⟩ ⟨hv⟩ ⟨hb⟩ _ => ⟨.letE Γ A A' v v' b b' B u hA hv hb⟩
  sorts Γ l₁ l₂ h := ⟨.sorts Γ l₁ l₂ h⟩
  consts Γ r ls ls' m hres hlen hwf hwf' h _ := ⟨.consts Γ r ls ls' m hres hlen hwf hwf' h⟩
  eta Γ f A B := fun ⟨h⟩ _ => ⟨.eta Γ f A B h⟩
  irr Γ P p q := fun ⟨hP⟩ ⟨hp⟩ ⟨hq⟩ => ⟨.irr Γ P p q hP hp hq⟩
  tyConv Γ a b A A' _ _ u := fun ⟨h⟩ _ _ _ _ ⟨hA⟩ => ⟨.tyConv Γ a b A A' u h hA⟩

section Typed
variable {J : IotaIfaceA} {EA : ResolvedEnvA} {n : Nat}

/-- ERASURE INTO THE TYPED JUDGMENT, typing. -/
theorem hasTyT_of_hasTyA (_hW : EnvWfA J EA) (hNS : IotaErasesA EA) {Γ : LCtxA} {e T : ExprA}
    (h : HasTyA EA (iotaIfaceA EA) n Γ e T) :
    Nonempty (HasTyT (eraseEnv EA) n (eraseCtx Γ) (erase e) (erase T)) :=
  erase_hasTyA_wf hNS copyRulesClosed_typed h

/-- ERASURE INTO THE TYPED JUDGMENT, conversion. -/
theorem convT_of_convA (_hW : EnvWfA J EA) (hNS : IotaErasesA EA) {Γ : LCtxA} {a b T : ExprA}
    (h : ConvA EA (iotaIfaceA EA) n Γ a b T) :
    Nonempty (ConvT (eraseEnv EA) n (eraseCtx Γ) (erase a) (erase b) (erase T)) :=
  erase_convA_wf hNS copyRulesClosed_typed h

/-- ERASURE INTO THE TYPED JUDGMENT, the derived chain. -/
theorem tyConvT_of_tyConvA (_hW : EnvWfA J EA) (hNS : IotaErasesA EA) {Γ : LCtxA} {A B : ExprA}
    (h : TyConvA EA (iotaIfaceA EA) n Γ A B) :
    Nonempty (TyConvT (eraseEnv EA) n (eraseCtx Γ) (erase A) (erase B)) :=
  erase_tyConvA (I := iotaIfaceA EA) copyRulesClosed_typed hNS
    (TT := fun Γ A B => Nonempty (TyConvT (eraseEnv EA) n Γ A B))
    (fun Γ A => ⟨.refl Γ A⟩)
    (fun Γ A B _ _ u _ _ _ _ ⟨hc⟩ => ⟨.of Γ A B u hc⟩)
    (fun Γ A B C ⟨h1⟩ ⟨h2⟩ => ⟨.trans Γ A B C h1 h2⟩) h

end Typed

#print axioms erase_hasTyA
#print axioms erase_convA
#print axioms erase_tyConvA
#print axioms erase_hasTyA_wf
#print axioms erase_convA_wf
#print axioms copyRulesClosed_main
#print axioms hasTy_main_of_hasTyA
#print axioms copyRulesClosed_typed
#print axioms hasTyT_of_hasTyA
#print axioms convT_of_convA
#print axioms tyConvT_of_tyConvA

end Rcic.Declarative.Ann
