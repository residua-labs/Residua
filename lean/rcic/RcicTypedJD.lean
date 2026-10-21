import rcic.RcicAnnErase
import rcic.RcicAnnIotaCorrN

/-!
# R-NoDeltaRec-4d-iv — the typed judgment keyed on the annotated environment

`HasTyT`/`ConvT`/`TyConvT`/`CtxWfT`/`ConvArgsT` (`RcicTypedJ`) are stated on `main`'s syntax
(`Expr Nat`) over a `main`-side environment `E : ResolvedEnv` — at a `.drecD` group that
judgment is unusable as the copy's correspondence target in EITHER direction
(`drCtorMemberA_diverge`: stored and normalized constructor types erase differently, so
`DerivedIota (eraseEnv E)` is inhabited exactly where the copy's ι does NOT fire).

This module states the same rules over the ANNOTATED environment `EA : ResolvedEnvA`, with ι
keyed on `DerivedIotaN EA` — the normalized witness `RcicAnnIotaCorrN` proves corresponds to
the copy's ι unconditionally (`IotaCorrN`, no `EnvNormEraseA`). Member types and bodies are
read erased, as every erased reader reads them:

- `HasTyTD.const` / `ConvTD.delta` / `ConvTD.consts` read `EA.members r = some m` with
  `m : CheckedMemberA` and instantiate `erase m.mtypeA` / `erase b` — the same data
  `ConvT (eraseEnv EA)` reads off `eraseMember m`, with no erase-transport in between.
- `ConvTD.iota` reads `DerivedIotaN EA`, the witness the copy's ι provably corresponds to.

(0) the judgment (`HasTyTD`/`ConvTD`, `TyConvTD`, `CtxWfTD`, `ConvArgsTD`);
(1) `CopyRulesClosedD`, the copy-rule interface keyed on `EA` + `DerivedIotaN`;
(2) `erase_hasTyAD`/`erase_convAD`/`erase_tyConvAD`, the erasure direction into any `HT`/`CT`
    closed under the D-rules — the `hI` premise is `IotaErasesAN`'s shape;
(3) `copyRulesClosedTD`, the instance at `HasTyTD`/`ConvTD`, and the concrete
    `hasTyTD_of_hasTyA`/`convTD_of_convA`/`tyConvTD_of_tyConvA`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) the judgment -/

mutual

/-- `HasTyT` on `main`'s syntax, at the annotated environment: member types read erased. -/
inductive HasTyTD (EA : ResolvedEnvA) (n : Nat) : LCtx → Expr Nat → Expr Nat → Type
  | sort (Γ : LCtx) (l : Level) : HasTyTD EA n Γ (.sort l) (.sort (.succ l))
  | bvar (Γ : LCtx) (i : Nat) (A : Expr Nat) (h : lookupType Γ i = some A) :
      HasTyTD EA n Γ (.bvar i) A
  | const (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMemberA)
      (hres : EA.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) :
      HasTyTD EA n Γ (.const r ls) (instantiateLevels ls (erase m.mtypeA))
  | pi (Γ : LCtx) (A : Expr Nat) (u : Level) (B : Expr Nat) (v : Level)
      (hA : HasTyTD EA n Γ A (.sort u))
      (hB : HasTyTD EA n (.assumption A :: Γ) B (.sort v)) :
      HasTyTD EA n Γ (.pi A B) (.sort (.imax u v))
  | lam (Γ : LCtx) (A : Expr Nat) (u : Level) (body B : Expr Nat)
      (hA : HasTyTD EA n Γ A (.sort u))
      (hbody : HasTyTD EA n (.assumption A :: Γ) body B) :
      HasTyTD EA n Γ (.lam A body) (.pi A B)
  | app (Γ : LCtx) (f a A B : Expr Nat)
      (hf : HasTyTD EA n Γ f (.pi A B)) (ha : HasTyTD EA n Γ a A) :
      HasTyTD EA n Γ (.app f a) (instantiate0 a B)
  | letE (Γ : LCtx) (A : Expr Nat) (u : Level) (value B body : Expr Nat)
      (hA : HasTyTD EA n Γ A (.sort u)) (hv : HasTyTD EA n Γ value A)
      (hb : HasTyTD EA n (.letBinding A value :: Γ) body B) :
      HasTyTD EA n Γ (.letE A value body) (instantiate0 value B)
  | lit (Γ : LCtx) (t : Nat) (T : Expr Nat) (hexp : HasTyTD EA n Γ (natExpand t) T) :
      HasTyTD EA n Γ (.lit t) T
  | conv (Γ : LCtx) (e A B : Expr Nat) (u : Level) (h : HasTyTD EA n Γ e A)
      (hc : ConvTD EA n Γ A B (.sort u)) : HasTyTD EA n Γ e B

/-- `ConvT` on `main`'s syntax, at the annotated environment: member data read erased, ι the
    normalized derived ι (`DerivedIotaN`) — the correspondence the copy proves with no
    norm-erasure premise. -/
inductive ConvTD (EA : ResolvedEnvA) (n : Nat) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (a A : Expr Nat) (h : HasTyTD EA n Γ a A) : ConvTD EA n Γ a a A
  | symm (Γ : LCtx) (a b A : Expr Nat) (h : ConvTD EA n Γ a b A) : ConvTD EA n Γ b a A
  | trans (Γ : LCtx) (a b c A : Expr Nat) (h1 : ConvTD EA n Γ a b A) (h2 : ConvTD EA n Γ b c A) :
      ConvTD EA n Γ a c A
  | beta (Γ : LCtx) (A body arg B : Expr Nat) (u : Level)
      (hA : HasTyTD EA n Γ A (.sort u)) (hbody : HasTyTD EA n (.assumption A :: Γ) body B)
      (harg : HasTyTD EA n Γ arg A) :
      ConvTD EA n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B)
  | zeta (Γ : LCtx) (A value body B : Expr Nat) (u : Level)
      (hA : HasTyTD EA n Γ A (.sort u)) (hv : HasTyTD EA n Γ value A)
      (hb : HasTyTD EA n (.letBinding A value :: Γ) body B) :
      ConvTD EA n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B)
  | zetaLocal (Γ : LCtx) (i : Nat) (A v : Expr Nat) (hval : lookupValue Γ i = some v)
      (hty : lookupType Γ i = some A) (hv : HasTyTD EA n Γ v A) :
      ConvTD EA n Γ (.bvar i) v A
  | delta (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMemberA) (b : ExprA)
      (hres : EA.members r = some m) (hbody : m.bodyA = some b)
      (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hb : HasTyTD EA n Γ (instantiateLevels ls (erase b))
        (instantiateLevels ls (erase m.mtypeA))) :
      ConvTD EA n Γ (.const r ls) (instantiateLevels ls (erase b))
        (instantiateLevels ls (erase m.mtypeA))
  | iota (Γ : LCtx) (lhs rhs T : Expr Nat) (h : DerivedIotaN EA lhs rhs)
      (hlhs : HasTyTD EA n Γ lhs T) (hrhs : HasTyTD EA n Γ rhs T) :
      ConvTD EA n Γ lhs rhs T
  | lit (Γ : LCtx) (t : Nat) (exp T : Expr Nat) (h : LiteralExpansion t exp)
      (hexp : HasTyTD EA n Γ exp T) : ConvTD EA n Γ (.lit t) exp T
  | app (Γ : LCtx) (f g a b A B : Expr Nat) (h1 : ConvTD EA n Γ f g (.pi A B))
      (h2 : ConvTD EA n Γ a b A) : ConvTD EA n Γ (.app f a) (.app g b) (instantiate0 a B)
  | lam (Γ : LCtx) (A A' b b' B : Expr Nat) (u : Level) (hA : ConvTD EA n Γ A A' (.sort u))
      (hb : ConvTD EA n (.assumption A :: Γ) b b' B) :
      ConvTD EA n Γ (.lam A b) (.lam A' b') (.pi A B)
  | pi (Γ : LCtx) (A A' B B' : Expr Nat) (u v : Level) (hA : ConvTD EA n Γ A A' (.sort u))
      (hB : ConvTD EA n (.assumption A :: Γ) B B' (.sort v)) :
      ConvTD EA n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))
  | letE (Γ : LCtx) (A A' v v' b b' B : Expr Nat) (u : Level) (hA : ConvTD EA n Γ A A' (.sort u))
      (hv : ConvTD EA n Γ v v' A) (hb : ConvTD EA n (.letBinding A v :: Γ) b b' B) :
      ConvTD EA n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B)
  | sorts (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
      ConvTD EA n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))
  | consts (Γ : LCtx) (r : Nat) (ls ls' : List Level) (m : CheckedMemberA)
      (hres : EA.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
      (h : eqNList ls ls') :
      ConvTD EA n Γ (.const r ls) (.const r ls') (instantiateLevels ls (erase m.mtypeA))
  | eta (Γ : LCtx) (f A B : Expr Nat) (h : HasTyTD EA n Γ f (.pi A B)) :
      ConvTD EA n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B)
  | irr (Γ : LCtx) (P p q : Expr Nat) (hP : HasTyTD EA n Γ P (.sort .zero))
      (hp : HasTyTD EA n Γ p P) (hq : HasTyTD EA n Γ q P) : ConvTD EA n Γ p q P
  | tyConv (Γ : LCtx) (a b A A' : Expr Nat) (u : Level) (h : ConvTD EA n Γ a b A)
      (hA : ConvTD EA n Γ A A' (.sort u)) : ConvTD EA n Γ a b A'

end

/-- the derived type conversion at `ConvTD` (`TyConvT`'s twin). -/
inductive TyConvTD (EA : ResolvedEnvA) (n : Nat) : LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (A : Expr Nat) : TyConvTD EA n Γ A A
  | of (Γ : LCtx) (A B : Expr Nat) (u : Level) (h : ConvTD EA n Γ A B (.sort u)) :
      TyConvTD EA n Γ A B
  | trans (Γ : LCtx) (A B C : Expr Nat) (h1 : TyConvTD EA n Γ A B) (h2 : TyConvTD EA n Γ B C) :
      TyConvTD EA n Γ A C

/-- a well-formed local context at `HasTyTD` (`CtxWfT`'s twin). -/
inductive CtxWfTD (EA : ResolvedEnvA) (n : Nat) : LCtx → Type
  | nil : CtxWfTD EA n []
  | assumption (Γ : LCtx) (A : Expr Nat) (u : Level) (hΓ : CtxWfTD EA n Γ)
      (hA : HasTyTD EA n Γ A (.sort u)) : CtxWfTD EA n (.assumption A :: Γ)
  | letBinding (Γ : LCtx) (A : Expr Nat) (u : Level) (v : Expr Nat) (hΓ : CtxWfTD EA n Γ)
      (hA : HasTyTD EA n Γ A (.sort u)) (hv : HasTyTD EA n Γ v A) :
      CtxWfTD EA n (.letBinding A v :: Γ)

/-- arguments pointwise `ConvTD`-convertible along a telescope (`ConvArgsT`'s twin). -/
inductive ConvArgsTD (EA : ResolvedEnvA) (n : Nat) (Γ : LCtx) :
    Expr Nat → List (Expr Nat) → List (Expr Nat) → Prop
  | nil (T : Expr Nat) : ConvArgsTD EA n Γ T [] []
  | cons (A B f f' : Expr Nat) (fs fs' : List (Expr Nat)) (h : Nonempty (ConvTD EA n Γ f f' A))
      (hs : ConvArgsTD EA n Γ (instantiate0 f B) fs fs') :
      ConvArgsTD EA n Γ (.pi A B) (f :: fs) (f' :: fs')

/-! ## (1) the copy-rule interface at `EA` + `DerivedIotaN` -/

/-- `CopyRulesClosed` keyed on the annotated environment: the erased rules read `EA.members`
    and annotated member data (no `eraseMember` transport), and ι is `DerivedIotaN EA` — the
    correspondence `RcicAnnIotaCorrN` proves with no `EnvNormEraseA`. -/
structure CopyRulesClosedD (EA : ResolvedEnvA) (n : Nat)
    (HT : LCtx → Expr Nat → Expr Nat → Prop)
    (CT : LCtx → Expr Nat → Expr Nat → Expr Nat → Prop) : Prop where
  sort : ∀ Γ l, HT Γ (.sort l) (.sort (.succ l))
  bvar : ∀ Γ i A u, lookupType Γ i = some A → HT Γ A (.sort u) → HT Γ (.bvar i) A
  const : ∀ Γ r ls (m : CheckedMemberA) u, EA.members r = some m → ls.length = m.arity →
    levelsBounded n ls = true → HT Γ (instantiateLevels ls (erase m.mtypeA)) (.sort u) →
    HT Γ (.const r ls) (instantiateLevels ls (erase m.mtypeA))
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
  delta : ∀ Γ r ls (m : CheckedMemberA) (b : ExprA), EA.members r = some m → m.bodyA = some b →
    transparent m.mclass = true → ls.length = m.arity → levelsBounded n ls = true →
    HT Γ (instantiateLevels ls (erase b)) (instantiateLevels ls (erase m.mtypeA)) →
    CT Γ (.const r ls) (instantiateLevels ls (erase b)) (instantiateLevels ls (erase m.mtypeA))
  iota : ∀ Γ lhs rhs T, Nonempty (DerivedIotaN EA lhs rhs) → HT Γ lhs T → HT Γ rhs T →
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
  consts : ∀ Γ r ls ls' (m : CheckedMemberA), EA.members r = some m → ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    HT Γ (.const r ls') (instantiateLevels ls (erase m.mtypeA)) →
    CT Γ (.const r ls) (.const r ls') (instantiateLevels ls (erase m.mtypeA))
  eta : ∀ Γ f A B, HT Γ f (.pi A B) → HT Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) →
    CT Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B)
  irr : ∀ Γ P p q, HT Γ P (.sort .zero) → HT Γ p P → HT Γ q P → CT Γ p q P
  tyConv : ∀ Γ a b A A' l l' u, CT Γ a b A → HT Γ A (.sort l) → eqN l u → HT Γ A' (.sort l') →
    eqN l' u → CT Γ A A' (.sort u) → CT Γ a b A'

/-! ## (2) erasure into a D-closed pair -/

section EraseD
variable {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
  {HT : LCtx → Expr Nat → Expr Nat → Prop}
  {CT : LCtx → Expr Nat → Expr Nat → Expr Nat → Prop}

mutual

/-- ERASURE OF TYPING into a D-closed pair: `erase_hasTyA`'s twin at the annotated environment —
    every member read is already annotated (`hres` itself), the ι premise is `DerivedIotaN`. -/
theorem erase_hasTyAD (C : CopyRulesClosedD EA n HT CT)
    (hI : ∀ lhs rhs, I.fn lhs = some rhs → Nonempty (DerivedIotaN EA (erase lhs) (erase rhs))) :
    {Γ : LCtxA} → {e T : ExprA} → HasTyA EA I n Γ e T → HT (eraseCtx Γ) (erase e) (erase T)
  | _, _, _, .sort Γ l => C.sort _ l
  | _, _, _, .bvar Γ i A u h hA =>
      C.bvar _ i _ u (lookupType_eraseCtx_some h) (erase_hasTyAD C hI hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT => by
      have hT' := erase_hasTyAD C hI hT
      rw [erase_instantiateLevelsA] at hT' ⊢
      exact C.const _ r ls m u hres hlen hwf hT'
  | _, _, _, .pi Γ A u B v hA hB =>
      C.pi _ _ u _ v (erase_hasTyAD C hI hA) (erase_hasTyAD C hI hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      C.lam _ _ u _ _ v (erase_hasTyAD C hI hA) (erase_hasTyAD C hI hB) (erase_hasTyAD C hI hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha => by
      have hTy' := erase_hasTyAD C hI hTy
      rw [erase_instantiate0A] at hTy' ⊢
      exact C.app _ _ _ _ _ v w (erase_hasTyAD C hI hB) hTy' (erase_hasTyAD C hI hf)
        (erase_hasTyAD C hI ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb => by
      have hTy' := erase_hasTyAD C hI hTy
      rw [erase_instantiate0A] at hTy' ⊢
      exact C.letE _ _ u w _ _ _ (erase_hasTyAD C hI hA) (erase_hasTyAD C hI hv) hTy'
        (erase_hasTyAD C hI hb)
  | _, _, _, .lit Γ t T hexp => by
      have h := erase_hasTyAD C hI hexp
      rw [erase_natExpandA] at h
      exact C.lit _ t _ h
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      C.conv _ _ _ _ l u (erase_hasTyAD C hI h) (erase_hasTyAD C hI hAl) hlu
        (erase_hasTyAD C hI hB) (erase_convAD C hI hc)

/-- ERASURE OF CONVERSION into a D-closed pair. -/
theorem erase_convAD (C : CopyRulesClosedD EA n HT CT)
    (hI : ∀ lhs rhs, I.fn lhs = some rhs → Nonempty (DerivedIotaN EA (erase lhs) (erase rhs))) :
    {Γ : LCtxA} → {a b T : ExprA} → ConvA EA I n Γ a b T →
      CT (eraseCtx Γ) (erase a) (erase b) (erase T)
  | _, _, _, _, .refl Γ a A h => C.refl _ _ _ (erase_hasTyAD C hI h)
  | _, _, _, _, .symm Γ a b A h => C.symm _ _ _ _ (erase_convAD C hI h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      C.trans _ _ _ _ _ (erase_convAD C hI h1) (erase_convAD C hI h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred => by
      have hred' := erase_hasTyAD C hI hred
      rw [erase_instantiate0A, erase_instantiate0A] at hred' ⊢
      exact C.beta _ _ u _ _ _ (erase_hasTyAD C hI hA) (erase_hasTyAD C hI hbody)
        (erase_hasTyAD C hI harg) hred'
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred => by
      have hred' := erase_hasTyAD C hI hred
      rw [erase_instantiate0A, erase_instantiate0A] at hred' ⊢
      exact C.zeta _ _ _ _ _ u (erase_hasTyAD C hI hA) (erase_hasTyAD C hI hv)
        (erase_hasTyAD C hI hb) hred'
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      C.zetaLocal _ i _ _ (lookupValue_eraseCtx_some hval) (lookupType_eraseCtx_some hty)
        (erase_hasTyAD C hI hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb => by
      have hb' := erase_hasTyAD C hI hb
      rw [erase_instantiateLevelsA, erase_instantiateLevelsA] at hb' ⊢
      exact C.delta _ r ls m b hres hbody htr hlen hwf hb'
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      C.iota _ _ _ _ (hI lhs rhs h.graph) (erase_hasTyAD C hI hlhs) (erase_hasTyAD C hI hrhs)
  | _, _, _, _, .structIota Γ f a rhs _ T _ _ h hlhs hrhs _ =>
      C.iota _ _ _ _ (hI (.app f a) rhs h) (erase_hasTyAD C hI hlhs) (erase_hasTyAD C hI hrhs)
  | _, _, _, _, .lit Γ t T hexp => by
      have h := erase_hasTyAD C hI hexp
      rw [erase_natExpandA] at h ⊢
      exact C.litConv _ t _ h
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt => by
      have hrt' := erase_hasTyAD C hI hrt
      rw [erase_instantiate0A] at hrt' ⊢
      exact C.appConv _ _ _ _ _ _ _ v (erase_convAD C hI h1) (erase_convAD C hI h2)
        (erase_hasTyAD C hI hB) hrt'
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      C.lamConv _ _ _ _ _ _ u u' hu (erase_convAD C hI hA) (erase_convAD C hI hb)
        (erase_hasTyAD C hI hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      C.piConv _ _ _ _ _ u u' v v' hu hv (erase_convAD C hI hA) (erase_convAD C hI hB)
        (erase_hasTyAD C hI hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt => by
      have hrt' := erase_hasTyAD C hI hrt
      rw [erase_instantiate0A] at hrt' ⊢
      exact C.letEConv _ _ _ _ _ _ _ _ u (erase_convAD C hI hA) (erase_convAD C hI hv)
        (erase_convAD C hI hb) hrt'
  | _, _, _, _, .sorts Γ l₁ l₂ h => C.sorts _ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt => by
      have hrt' := erase_hasTyAD C hI hrt
      rw [erase_instantiateLevelsA] at hrt' ⊢
      exact C.consts _ r ls ls' m hres hlen hwf hwf' h hrt'
  | _, _, _, _, .eta Γ f A B u v h hrt => by
      have hrt' := erase_hasTyAD C hI hrt
      show CT (eraseCtx Γ) (.lam (erase A) (.app (erase (liftA 0 1 f)) (.bvar 0))) (erase f)
        (.pi (erase A) (erase B))
      change HT (eraseCtx Γ) (.lam (erase A) (.app (erase (liftA 0 1 f)) (.bvar 0)))
        (.pi (erase A) (erase B)) at hrt'
      rw [erase_liftA] at hrt' ⊢
      exact C.eta _ _ _ _ (erase_hasTyAD C hI h) hrt'
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      C.irr _ _ _ _ (erase_hasTyAD C hI hP) (erase_hasTyAD C hI hp) (erase_hasTyAD C hI hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      C.tyConv _ _ _ _ _ l l' u (erase_convAD C hI h) (erase_hasTyAD C hI hAl) hlu
        (erase_hasTyAD C hI hA'l) hl'u (erase_convAD C hI hA)

end

/-- `TyConvA` erases through a D-closed pair into any reflexive-transitive relation containing
    `CT` at a sort (`erase_tyConvA`'s twin). -/
theorem erase_tyConvAD (C : CopyRulesClosedD EA n HT CT)
    (hI : ∀ lhs rhs, I.fn lhs = some rhs → Nonempty (DerivedIotaN EA (erase lhs) (erase rhs)))
    {TT : LCtx → Expr Nat → Expr Nat → Prop} (hrefl : ∀ Γ A, TT Γ A A)
    (hof : ∀ Γ A B l l' u, HT Γ A (.sort l) → eqN l u → HT Γ B (.sort l') → eqN l' u →
      CT Γ A B (.sort u) → TT Γ A B)
    (htrans : ∀ Γ A B C, TT Γ A B → TT Γ B C → TT Γ A C) :
    {Γ : LCtxA} → {A B : ExprA} → TyConvA EA I n Γ A B → TT (eraseCtx Γ) (erase A) (erase B)
  | _, _, _, .refl Γ A => hrefl _ _
  | _, _, _, .of Γ A B l l' u hAl hlu hBl hl'u h =>
      hof _ _ _ l l' u (erase_hasTyAD C hI hAl) hlu (erase_hasTyAD C hI hBl) hl'u
        (erase_convAD C hI h)
  | _, _, _, .trans Γ A B C' h1 h2 =>
      htrans _ _ _ _ (erase_tyConvAD C hI hrefl hof htrans h1)
        (erase_tyConvAD C hI hrefl hof htrans h2)

/-- at the concrete ι the D-erasure's ι premise is `IotaErasesAN`. -/
theorem erase_hasTyAD_wf (hNS : IotaErasesAN EA)
    (C : CopyRulesClosedD EA n HT CT)
    {Γ : LCtxA} {e T : ExprA} (h : HasTyA EA (iotaIfaceA EA) n Γ e T) :
    HT (eraseCtx Γ) (erase e) (erase T) :=
  erase_hasTyAD (I := iotaIfaceA EA) C hNS h

theorem erase_convAD_wf (hNS : IotaErasesAN EA)
    (C : CopyRulesClosedD EA n HT CT)
    {Γ : LCtxA} {a b T : ExprA} (h : ConvA EA (iotaIfaceA EA) n Γ a b T) :
    CT (eraseCtx Γ) (erase a) (erase b) (erase T) :=
  erase_convAD (I := iotaIfaceA EA) C hNS h

end EraseD

/-! ## (3) the instance at `HasTyTD`/`ConvTD` and the concrete erasure -/

/-- `HasTyTD`/`ConvTD` are closed under the D-rules: each field is one of their rules. -/
theorem copyRulesClosedTD {EA : ResolvedEnvA} {n : Nat} :
    CopyRulesClosedD EA n (fun Γ e T => Nonempty (HasTyTD EA n Γ e T))
      (fun Γ a b T => Nonempty (ConvTD EA n Γ a b T)) where
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

section ConcreteD
variable {J : IotaIfaceA} {EA : ResolvedEnvA} {n : Nat}

/-- ERASURE INTO THE D-JUDGMENT, typing: `hasTyT_of_hasTyA` with no `EnvNormEraseA` — the
    premise is `IotaErasesAN`, discharged by `iotaCorrN_of_envWfA`. -/
theorem hasTyTD_of_hasTyA (hNS : IotaErasesAN EA) {Γ : LCtxA} {e T : ExprA}
    (h : HasTyA EA (iotaIfaceA EA) n Γ e T) :
    Nonempty (HasTyTD EA n (eraseCtx Γ) (erase e) (erase T)) :=
  erase_hasTyAD_wf hNS copyRulesClosedTD h

/-- ERASURE INTO THE D-JUDGMENT, conversion. -/
theorem convTD_of_convA (hNS : IotaErasesAN EA) {Γ : LCtxA} {a b T : ExprA}
    (h : ConvA EA (iotaIfaceA EA) n Γ a b T) :
    Nonempty (ConvTD EA n (eraseCtx Γ) (erase a) (erase b) (erase T)) :=
  erase_convAD_wf hNS copyRulesClosedTD h

/-- ERASURE INTO THE D-JUDGMENT, the derived chain. -/
theorem tyConvTD_of_tyConvA (hNS : IotaErasesAN EA) {Γ : LCtxA} {A B : ExprA}
    (h : TyConvA EA (iotaIfaceA EA) n Γ A B) :
    Nonempty (TyConvTD EA n (eraseCtx Γ) (erase A) (erase B)) :=
  erase_tyConvAD (I := iotaIfaceA EA) copyRulesClosedTD hNS
    (TT := fun Γ A B => Nonempty (TyConvTD EA n Γ A B))
    (fun Γ A => ⟨.refl Γ A⟩)
    (fun Γ A B _ _ u _ _ _ _ ⟨hc⟩ => ⟨.of Γ A B u hc⟩)
    (fun Γ A B C ⟨h1⟩ ⟨h2⟩ => ⟨.trans Γ A B C h1 h2⟩) h

/-- pointwise conversions along a telescope erase into `ConvArgsTD`. -/
theorem convArgsTD_of_convArgsA (hNS : IotaErasesAN EA) {Γ : LCtxA} :
    {T : ExprA} → {xs xs' : List ExprA} → ConvArgsA EA (iotaIfaceA EA) n Γ T xs xs' →
      ConvArgsTD EA n (eraseCtx Γ) (erase T) (xs.map erase) (xs'.map erase)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A _ B _ f f' _ _ ⟨h⟩ hs => by
      have ih := convArgsTD_of_convArgsA hNS hs
      rw [erase_instantiate0A] at ih
      exact .cons (erase A) (erase B) (erase f) (erase f') _ _ (convTD_of_convA hNS h) ih

/-- a well-formed annotated context erases well-formed at `HasTyTD`. -/
theorem ctxWfTD_of_ctxWfA (hNS : IotaErasesAN EA) {Γ : LCtxA}
    (hΓ : CtxWfA EA (iotaIfaceA EA) n Γ) : Nonempty (CtxWfTD EA n (eraseCtx Γ)) := by
  induction hΓ with
  | nil => exact ⟨.nil⟩
  | @assumption Γ A u hΓ hA ihΓ =>
      obtain ⟨hΓ'⟩ := ihΓ
      obtain ⟨hA'⟩ := hasTyTD_of_hasTyA hNS hA
      exact ⟨.assumption _ _ _ hΓ' hA'⟩
  | @letBinding Γ A v u hΓ hA hv ihΓ =>
      obtain ⟨hΓ'⟩ := ihΓ
      obtain ⟨hA'⟩ := hasTyTD_of_hasTyA hNS hA
      obtain ⟨hv'⟩ := hasTyTD_of_hasTyA hNS hv
      exact ⟨.letBinding _ _ _ _ hΓ' hA' hv'⟩

end ConcreteD

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.HasTyTD
#print axioms Rcic.Declarative.Ann.ConvTD
#print axioms Rcic.Declarative.Ann.TyConvTD
#print axioms Rcic.Declarative.Ann.CtxWfTD
#print axioms Rcic.Declarative.Ann.ConvArgsTD
#print axioms Rcic.Declarative.Ann.CopyRulesClosedD
#print axioms Rcic.Declarative.Ann.erase_hasTyAD
#print axioms Rcic.Declarative.Ann.erase_convAD
#print axioms Rcic.Declarative.Ann.erase_tyConvAD
#print axioms Rcic.Declarative.Ann.copyRulesClosedTD
#print axioms Rcic.Declarative.Ann.hasTyTD_of_hasTyA
#print axioms Rcic.Declarative.Ann.convTD_of_convA
#print axioms Rcic.Declarative.Ann.tyConvTD_of_tyConvA
#print axioms Rcic.Declarative.Ann.convArgsTD_of_convArgsA
#print axioms Rcic.Declarative.Ann.ctxWfTD_of_ctxWfA
