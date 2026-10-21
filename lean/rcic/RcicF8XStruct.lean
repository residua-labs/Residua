import rcic.RcicF8OMEtaKAnnotPins
import rcic.RcicTypedInvert

/-!
# `RcicF8XStruct` — the X tile, Stratum A: Π-spined chains (S0 §4, PR #7026)

X on provenance (`XProc`/`XContract`, `RcicF8OM23`) restricted to chains whose every
intermediate type is syntactically a Π (`piSpinedTc`). On such a chain X is a structural
recursion with no U/D/J call: `refl`, `piCod`, `symm`, `trans` with a Π middle, the lazy
transports with a Π→Π inner chain (re-wrapped, never pushed — `EvTc.subst0` has no
`hvT`), and, inside literals through `certOfChild`, `TyConvT.refl/of/trans` and the
`ConvT` arms `refl`/`symm`/`trans`/`pi`/`tyConv`. The one non-structural link is
`ConvT.irr`, refuted by Prop/sort separation on the inverted literal proof typing
(`hasTyTInv_pi hp rfl`), never by endpoint typing (which fails without `CtxWfT`,
`Q1_SEPALL_ILLCTX_PIN`). The twelve other `ConvT` arms cannot sit between two Π's and
`piSpinedConv` is `false` on them. `EvCv.refl` (SP-1, batch 66) is a Π→Π link with equal
endpoints: `(refl, refl)`.

Two named hypotheses at the module boundary, both consumed and neither discharged here
(cc ruling on #7026):
- H-CTX `CtxConvProc`/`CtxConvContract`: moving a chain under a binder along a WEAK
  domain chain (S0 §3; discharged by D-VAR in S2, `EvTy.var`).
- H-SEP `SepAll`: Prop/sort separation, Γ-unconditional (Q1 measurement: not refuted).

Workers return the output together with its leaf bound (B3b's bundled pattern); the
public `xStruct` has `XProc`'s shape and `xStruct_contract` is `XContract`'s clause for
Π-spined inputs: every output leaf is `SubEq` an input leaf. Literal workers give the
strict `SubOf`. Consumer note (S0 §6.4, cc Q6): a re-wrapped transport repeats its
parameter `hv` once per component; `XContract` is `SubEq` without multiplicity and a
consumer feeding both components into one call accounts for `hv` as a kept atom.

Pins: `EtaKAnnotPins.request` is Π-spined (`rfl`) and `xStruct` on it yields the
`X_outputs_edge` fact for the fixture's actual caller; a β-redex middle is rejected
(`piSpinedTc = false`). `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### the named hypotheses (S0 §7) -/

/-- H-CTX: a chain under a binder moves to a convertible binder along a WEAK domain
    chain (no sort typing of either binder). -/
abbrev CtxConvProc (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A A' B B' : Expr Nat},
    EvTc R Γ A A' → EvTc R (.assumption A' :: Γ) B B' → EvTc R (.assumption A :: Γ) B B'

/-- H-CTX's leaf contract: the moved chain cites only the two inputs' leaves. -/
def CtxConvContract (K : ∀ R : List (Jd E n), CtxConvProc R) : Prop :=
  ∀ R {Γ : LCtx} {A A' B B' : Expr Nat}
    (cA : EvTc R Γ A A') (e : EvTc R (.assumption A' :: Γ) B B'),
    ∀ ℓ ∈ (K R cA e).leaves, ℓ ∈ cA.leaves ++ e.leaves

/-- H-SEP: Prop/sort separation in the Γ-unconditional form the sealed `XProc` forces
    (the landed `separationAt_of_sortUniq` is this under `CtxWfT`). -/
def SepAll (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {P : Expr Nat} {l : Level},
    HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False

/-! ### immediate-premise witnesses for `TyConvT` and `ConvT` nodes -/

def tcChildFst {Γ : LCtx} {A B C : Expr Nat} (h1 : TyConvT E n Γ A B)
    (h2 : TyConvT E n Γ B C) : Child (.tc h1) (.tc (.trans Γ A B C h1 h2)) := by
  show (Jd.tc h1 : Jd E n) ∈ ([Jd.tc h1, Jd.tc h2] : List (Jd E n))
  exact .head _

def tcChildSnd {Γ : LCtx} {A B C : Expr Nat} (h1 : TyConvT E n Γ A B)
    (h2 : TyConvT E n Γ B C) : Child (.tc h2) (.tc (.trans Γ A B C h1 h2)) := by
  show (Jd.tc h2 : Jd E n) ∈ ([Jd.tc h1, Jd.tc h2] : List (Jd E n))
  exact .tail _ (.head _)

def tcChildOf {Γ : LCtx} {A B : Expr Nat} {u : Level} (h : ConvT E n Γ A B (.sort u)) :
    Child (.cv h) (.tc (.of Γ A B u h)) := by
  show (Jd.cv h : Jd E n) ∈ ([Jd.cv h] : List (Jd E n))
  exact .head _

def cvChildSymm {Γ : LCtx} {a b A : Expr Nat} (h : ConvT E n Γ a b A) :
    Child (.cv h) (.cv (.symm Γ a b A h)) := by
  show (Jd.cv h : Jd E n) ∈ ([Jd.cv h] : List (Jd E n))
  exact .head _

def cvChildTransFst {Γ : LCtx} {a b c A : Expr Nat} (h1 : ConvT E n Γ a b A)
    (h2 : ConvT E n Γ b c A) : Child (.cv h1) (.cv (.trans Γ a b c A h1 h2)) := by
  show (Jd.cv h1 : Jd E n) ∈ ([Jd.cv h1, Jd.cv h2] : List (Jd E n))
  exact .head _

def cvChildTransSnd {Γ : LCtx} {a b c A : Expr Nat} (h1 : ConvT E n Γ a b A)
    (h2 : ConvT E n Γ b c A) : Child (.cv h2) (.cv (.trans Γ a b c A h1 h2)) := by
  show (Jd.cv h2 : Jd E n) ∈ ([Jd.cv h1, Jd.cv h2] : List (Jd E n))
  exact .tail _ (.head _)

def cvChildTyConv {Γ : LCtx} {a b A A' : Expr Nat} {u : Level} (h : ConvT E n Γ a b A)
    (hA : ConvT E n Γ A A' (.sort u)) :
    Child (.cv h) (.cv (.tyConv Γ a b A A' u h hA)) := by
  show (Jd.cv h : Jd E n) ∈ ([Jd.cv h, Jd.cv hA] : List (Jd E n))
  exact .head _

def cvChildPiFst {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    Child (.cv hA) (.cv (.pi Γ A A' B B' u v hA hB)) := by
  show (Jd.cv hA : Jd E n) ∈ ([Jd.cv hA, Jd.cv hB] : List (Jd E n))
  exact .head _

def cvChildPiSnd {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    Child (.cv hB) (.cv (.pi Γ A A' B B' u v hA hB)) := by
  show (Jd.cv hB : Jd E n) ∈ ([Jd.cv hA, Jd.cv hB] : List (Jd E n))
  exact .tail _ (.head _)

/-! ### Π-spined chains -/

/-- syntactic Π head. -/
def isPi : Expr Nat → Bool
  | .pi _ _ => true
  | _ => false

theorem isPi_true : {e : Expr Nat} → isPi e = true → ∃ A B, e = .pi A B
  | .pi A B, _ => ⟨A, B, rfl⟩
  | .bvar _, h => nomatch h
  | .sort _, h => nomatch h
  | .const _ _, h => nomatch h
  | .app _ _, h => nomatch h
  | .lam _ _, h => nomatch h
  | .letE _ _ _, h => nomatch h
  | .lit _, h => nomatch h

/-- the same, as data (the workers build data and cannot eliminate an `∃`). -/
def isPiD : (e : Expr Nat) → isPi e = true → Σ' (A B : Expr Nat), e = .pi A B
  | .pi A B, _ => ⟨A, B, rfl⟩
  | .bvar _, h => nomatch h
  | .sort _, h => nomatch h
  | .const _ _, h => nomatch h
  | .app _ _, h => nomatch h
  | .lam _ _, h => nomatch h
  | .letE _ _ _, h => nomatch h
  | .lit _, h => nomatch h

/-- a plain conversion is Π-spined: only `refl`/`symm`/`trans`/`pi`/`irr`/`tyConv`
    nodes, every `trans` middle a Π. The twelve other arms never sit between two Π's. -/
def piSpinedConv : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .refl _ _ _ _ => true
  | _, _, _, _, .symm _ _ _ _ h => piSpinedConv h
  | _, _, _, _, .trans _ _ m _ _ h1 h2 => isPi m && piSpinedConv h1 && piSpinedConv h2
  | _, _, _, _, .pi .. => true
  | _, _, _, _, .irr .. => true
  | _, _, _, _, .tyConv _ _ _ _ _ _ h _ => piSpinedConv h
  | _, _, _, _, .beta .. => false
  | _, _, _, _, .zeta .. => false
  | _, _, _, _, .zetaLocal .. => false
  | _, _, _, _, .delta .. => false
  | _, _, _, _, .iota .. => false
  | _, _, _, _, .lit .. => false
  | _, _, _, _, .app .. => false
  | _, _, _, _, .lam .. => false
  | _, _, _, _, .letE .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false
  | _, _, _, _, .eta .. => false

/-- a plain type-conversion chain is Π-spined. -/
def piSpinedT : {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → Bool
  | _, _, _, .refl _ _ => true
  | _, _, _, .of _ _ _ _ h => piSpinedConv h
  | _, _, _, .trans _ _ M _ h1 h2 => isPi M && piSpinedT h1 && piSpinedT h2

mutual

/-- a provenance chain is Π-spined: every `trans` middle is a Π, and every lazy
    transport's inner chain is Π→Π and Π-spined (the substituted-variable case of
    `subst0`/`substLet` is Stratum B, S0 §5.4). -/
def piSpinedTc : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .lit d _ => piSpinedT d
  | _, _, _, .ofCv _ c => piSpinedCv c
  | _, _, _, .refl _ _ => true
  | _, _, _, .symm c => piSpinedTc c
  | _, _, _, @EvTc.trans _ _ _ _ _ M _ c₁ c₂ => isPi M && piSpinedTc c₁ && piSpinedTc c₂
  | _, _, _, .piCod _ _ _ => true
  | _, _, _, @EvTc.subst0 _ _ _ _ A₀ A₀' _ _ _ c _ _ => isPi A₀ && isPi A₀' && piSpinedTc c
  | _, _, _, @EvTc.substLet _ _ _ _ A₀ A₀' _ _ _ c _ _ => isPi A₀ && isPi A₀' && piSpinedTc c
  | _, _, _, @EvTc.wk _ _ _ _ A₀ B₀ _ _ h => isPi A₀ && isPi B₀ && piSpinedTc h

/-- a provenance conversion is Π-spined. -/
def piSpinedCv : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Bool
  | _, _, _, _, .lit h _ => piSpinedConv h
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false
  | _, _, _, _, .symm c => piSpinedCv c
  | _, _, _, _, @EvCv.trans _ _ _ _ _ m _ _ c₁ c₂ => isPi m && piSpinedCv c₁ && piSpinedCv c₂
  | _, _, _, _, .tyConv _ c _ => piSpinedCv c
  | _, _, _, _, .rety c _ => piSpinedCv c
  | _, _, _, _, @EvCv.wk _ _ _ _ a₀ b₀ _ _ _ h => isPi a₀ && isPi b₀ && piSpinedCv h
  | _, _, _, _, @EvCv.esub _ _ _ _ a₀ b₀ _ _ _ _ _ h _ _ _ => isPi a₀ && isPi b₀ && piSpinedCv h
  | _, _, _, _, @EvCv.subst0 _ _ _ _ a₀ b₀ _ _ _ _ h _ _ => isPi a₀ && isPi b₀ && piSpinedCv h
  | _, _, _, _, @EvCv.substLet _ _ _ _ a₀ b₀ _ _ _ _ h _ _ => isPi a₀ && isPi b₀ && piSpinedCv h

end

/-! ### the output and the binder-shift of a substitution parameter -/

/-- the weak-row components: `XProc`'s output. -/
abbrev XOut (R : List (Jd E n)) (Γ : LCtx) (A₁ B₁ A₂ B₂ : Expr Nat) : Type :=
  EvTc R Γ A₁ A₂ × EvTc R (.assumption A₁ :: Γ) B₁ B₂

def XOut.leaves {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat} (o : XOut R Γ A₁ B₁ A₂ B₂) :
    List (Jd E n) :=
  o.1.leaves ++ o.2.leaves

/-- the substituted value's typing one binder deeper (B3b's `esubBinderArg`, public):
    `wk` inserts the substituted declaration head at position 0 of the removed context,
    and `lift_lift_merge` folds `lift 0 1 (lift 0 j x) = lift 0 (j+1) x`. -/
def substBinderArg {Γ₀ : LCtx} {j : Nat} {d : LocalDecl} {v x y : Expr Nat}
    (h : EvTy R (substRemove v j Γ₀) (lift 0 j x) (lift 0 j y)) :
    EvTy R (substRemove v (j + 1) (d :: Γ₀)) (lift 0 (j + 1) x) (lift 0 (j + 1) y) :=
  EvTy.cast rfl
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) x)
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) y)
    (EvTy.wk (instDecl j v d) 0 h)

theorem substBinderArg_leaves {Γ₀ : LCtx} {j : Nat} {d : LocalDecl} {v x y : Expr Nat}
    (h : EvTy R (substRemove v j Γ₀) (lift 0 j x) (lift 0 j y)) :
    (substBinderArg (d := d) h).leaves = h.leaves := by
  simp only [substBinderArg, EvTy.cast_leaves, EvTy.leaves]

/-! ### the workers (bundled with their leaf bounds) -/

/-- Context capabilities needed only while certifying structural separation leaves. -/
structure XCtxKit (E : ResolvedEnv) (n : Nat) (R : List (Jd E n)) where
  Ctx : LCtx → Type
  sep : ∀ {Γ}, Ctx Γ → ∀ {P : Expr Nat} {l : Level},
    HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False
  ins : ∀ {Γ}, (d : LocalDecl) → (k : Nat) → Ctx (insertAt d k Γ) → Ctx Γ
  sub : ∀ {Γ} {t v : Expr Nat}, (j : Nat) → Γ[j]? = some (.assumption t) →
    EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t) → Ctx (substRemove v j Γ) → Ctx Γ
  subLet : ∀ {Γ} {t w : Expr Nat}, (j : Nat) → Γ[j]? = some (.letBinding t w) →
    EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t) → Ctx (substRemove w j Γ) → Ctx Γ

def XCtxKit.universal (hsep : SepAll E n) : XCtxKit E n R where
  Ctx := fun _ => PUnit
  sep := fun _ => hsep
  ins := fun _ _ _ => PUnit.unit
  sub := fun _ _ _ _ => PUnit.unit
  subLet := fun _ _ _ _ => PUnit.unit

/-- Proof-only readiness: exactly the separation leaves visited by the worker.
The computational recursion receives this common proposition, so changing the context
certificate cannot change a component or census. -/
def XConvReady : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Prop
  | _, _, _, _, .symm _ _ _ _ h => XConvReady h
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂ => XConvReady h₁ ∧ XConvReady h₂
  | Γ, _, _, _, .irr .. => ∀ {P : Expr Nat} {l : Level},
      HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False
  | _, _, _, _, .tyConv _ _ _ _ _ _ h _ => XConvReady h
  | _, _, _, _, _ => True

def XTReady : {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → Prop
  | _, _, _, .of _ _ _ _ h => XConvReady h
  | _, _, _, .trans _ _ _ _ h₁ h₂ => XTReady h₁ ∧ XTReady h₂
  | _, _, _, .refl .. => True

mutual
def XTcReady : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Prop
  | _, _, _, .lit d _ => XTReady d
  | _, _, _, .ofCv _ c => XCvReady c
  | _, _, _, .symm c => XTcReady c
  | _, _, _, .trans c₁ c₂ => XTcReady c₁ ∧ XTcReady c₂
  | _, _, _, .wk _ _ c => XTcReady c
  | _, _, _, .subst0 _ c _ _ => XTcReady c
  | _, _, _, .substLet _ c _ _ => XTcReady c
  | _, _, _, _ => True

def XCvReady : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Prop
  | _, _, _, _, .lit h _ => XConvReady h
  | _, _, _, _, .symm c => XCvReady c
  | _, _, _, _, .trans c₁ c₂ => XCvReady c₁ ∧ XCvReady c₂
  | _, _, _, _, .tyConv _ c _ => XCvReady c
  | _, _, _, _, .rety c _ => XCvReady c
  | _, _, _, _, .wk _ _ c => XCvReady c
  | _, _, _, _, .esub _ _ c _ _ _ => XCvReady c
  | _, _, _, _, .subst0 _ c _ _ => XCvReady c
  | _, _, _, _, .substLet _ c _ _ => XCvReady c
  | _, _, _, _, _ => True
end

def XConvReady.ofCtx (C : XCtxKit E n R) {Γ a b T} (h : ConvT E n Γ a b T)
    (v : C.Ctx Γ) : XConvReady h := by
  cases h with
  | symm _ _ _ _ h => exact XConvReady.ofCtx C h v
  | trans _ _ _ _ _ h₁ h₂ => exact ⟨XConvReady.ofCtx C h₁ v, XConvReady.ofCtx C h₂ v⟩
  | irr => exact C.sep v
  | tyConv _ _ _ _ _ _ h _ => exact XConvReady.ofCtx C h v
  | _ => trivial

def XTReady.ofCtx (C : XCtxKit E n R) : {Γ : LCtx} → {A B : Expr Nat} →
    (h : TyConvT E n Γ A B) → C.Ctx Γ → XTReady h
  | _, _, _, .of _ _ _ _ h, v => by simpa only [XTReady] using XConvReady.ofCtx C h v
  | _, _, _, .trans _ _ _ _ h₁ h₂, v => by
      simpa only [XTReady] using And.intro (XTReady.ofCtx C h₁ v) (XTReady.ofCtx C h₂ v)
  | _, _, _, .refl .., _ => by simp only [XTReady]

mutual
def XTcReady.ofCtx (C : XCtxKit E n R) : {Γ : LCtx} → {A B : Expr Nat} →
    (c : EvTc R Γ A B) → C.Ctx Γ → XTcReady c
  | _, _, _, .lit d _, v => XTReady.ofCtx C d v
  | _, _, _, .ofCv _ c, v => XCvReady.ofCtx C c v
  | _, _, _, .symm c, v => XTcReady.ofCtx C c v
  | _, _, _, .trans c₁ c₂, v => ⟨XTcReady.ofCtx C c₁ v, XTcReady.ofCtx C c₂ v⟩
  | _, _, _, .wk d k c, v => XTcReady.ofCtx C c (C.ins d k v)
  | _, _, _, .subst0 j c hget hv, v => XTcReady.ofCtx C c (C.sub j hget hv v)
  | _, _, _, .substLet j c hget hv, v => XTcReady.ofCtx C c (C.subLet j hget hv v)
  | _, _, _, .refl .., _ => trivial
  | _, _, _, .piCod .., _ => trivial

def XCvReady.ofCtx (C : XCtxKit E n R) : {Γ : LCtx} → {a b T : Expr Nat} →
    (c : EvCv R Γ a b T) → C.Ctx Γ → XCvReady c
  | _, _, _, _, .lit h _, v => XConvReady.ofCtx C h v
  | _, _, _, _, .symm c, v => XCvReady.ofCtx C c v
  | _, _, _, _, .trans c₁ c₂, v => ⟨XCvReady.ofCtx C c₁ v, XCvReady.ofCtx C c₂ v⟩
  | _, _, _, _, .tyConv _ c _, v => XCvReady.ofCtx C c v
  | _, _, _, _, .rety c _, v => XCvReady.ofCtx C c v
  | _, _, _, _, .wk d k c, v => XCvReady.ofCtx C c (C.ins d k v)
  | _, _, _, _, .esub j _ c hget hv _, v => XCvReady.ofCtx C c (C.sub j hget hv v)
  | _, _, _, _, .subst0 j c hget hv, v => XCvReady.ofCtx C c (C.sub j hget hv v)
  | _, _, _, _, .substLet j c hget hv, v => XCvReady.ofCtx C c (C.subLet j hget hv v)
  | _, _, _, _, .refl .., _ => trivial
  | _, _, _, _, .sorts .., _ => trivial
  | _, _, _, _, .consts .., _ => trivial
end

section Workers

variable (K : ∀ R : List (Jd E n), CtxConvProc R) (hK : CtxConvContract K)

/-- Stratum A on a plain conversion between two Π's: the output and the strict bound
    (every output leaf is a strict sub-derivation of the literal). -/
def xConvReady : {Γ : LCtx} → {a b T : Expr Nat} → (h : ConvT E n Γ a b T) → XConvReady h →
    (∃ r ∈ R, SubEq (.cv h) r) → piSpinedConv h = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.cv h)
  | Γ, _, _, _, .refl _ a A _, ready, _, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, _, .symm _ a b A h, ready, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedConv] using hp
      obtain ⟨r, hr⟩ := xConvReady h ready (certOfChild (cvChildSymm h) hsub) hp' hb ha
      refine ⟨(.symm r.1, K R (.symm r.1) (.symm r.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      have hin : ℓ ∈ r.1.leaves ++ r.2.leaves := by
        rcases hℓ with hℓ | hℓ
        · exact List.mem_append.mpr (.inl hℓ)
        · have := hK R (.symm r.1) (.symm r.2) ℓ hℓ
          simpa only [EvTc.leaves] using this
      exact .trans (hr ℓ hin) (.child (cvChildSymm h))
  | _, _, _, _, .trans _ a m c A h1 h2, ready, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedConv, Bool.and_eq_true] at hp'
      have hm := hp'.1.1
      have hp1 := hp'.1.2
      have hp2 := hp'.2
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      obtain ⟨r₁, hr₁⟩ := xConvReady h1 ready.1 (certOfChild (cvChildTransFst h1 h2) hsub) hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xConvReady h2 ready.2 (certOfChild (cvChildTransSnd h1 h2) hsub) hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (K R r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (cvChildTransFst h1 h2))
      · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (cvChildTransSnd h1 h2))
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inr hℓ))) (.child (cvChildTransFst h1 h2))
      · have hk := hK R r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hk))) (.child (cvChildTransFst h1 h2))
        · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inr hk))) (.child (cvChildTransSnd h1 h2))
  | _, _, _, _, .pi _ A A' B B' u v hA hB, ready, hsub, _, A₁, B₁, A₂, B₂, ha, hb => by
      injection ha with h1 h2
      injection hb with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.ofCv u (.lit hA (certOfChild (cvChildPiFst hA hB) hsub)),
        .ofCv v (.lit hB (certOfChild (cvChildPiSnd hA hB) hsub))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvCv.leaves, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hℓ
      rcases hℓ with rfl | rfl
      · exact .child (cvChildPiFst hA hB)
      · exact .child (cvChildPiSnd hA hB)
  | _, _, _, _, .irr _ P p q hP hp _, ready, _, _, A₁, B₁, A₂, B₂, ha, _ => by
      subst ha
      obtain ⟨_, _, _, _, hc⟩ := hasTyTInv_pi hp rfl
      exact (ready hP hc).elim
  | _, _, _, _, .tyConv _ a b A A' u h hA, ready, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedConv] using hp
      obtain ⟨r, hr⟩ := xConvReady h ready (certOfChild (cvChildTyConv h hA) hsub) hp' ha hb
      exact ⟨r, fun ℓ hℓ => .trans (hr ℓ hℓ) (.child (cvChildTyConv h hA))⟩
  | _, _, _, _, .beta .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .zeta .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .zetaLocal .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .delta .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .iota .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .lit .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .app .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .lam .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .letE .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .sorts .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .consts .., _, _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .eta .., _, _, hp, _, _, _, _, _, _ => nomatch hp

/-- Stratum A on a plain type-conversion chain between two Π's, strict bound. -/
def xTReady : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) → XTReady d →
    (∃ r ∈ R, SubEq (.tc d) r) → piSpinedT d = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.tc d)
  | Γ, _, _, .refl _ A, ready, _, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, .of _ A B u h, ready, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedT] using hp
      have ready : XConvReady h := by simpa only [XTReady] using ready
      obtain ⟨r, hr⟩ := xConvReady K hK h ready (certOfChild (tcChildOf h) hsub) hp' ha hb
      exact ⟨r, fun ℓ hℓ => .trans (hr ℓ hℓ) (.child (tcChildOf h))⟩
  | _, _, _, .trans _ A M B d₁ d₂, ready, hsub, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedT, Bool.and_eq_true] at hp'
      have hm := hp'.1.1
      have hp1 := hp'.1.2
      have hp2 := hp'.2
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      have ready : XTReady d₁ ∧ XTReady d₂ := by simpa only [XTReady] using ready
      obtain ⟨r₁, hr₁⟩ := xTReady d₁ ready.1 (certOfChild (tcChildFst d₁ d₂) hsub) hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xTReady d₂ ready.2 (certOfChild (tcChildSnd d₁ d₂) hsub) hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (K R r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (tcChildFst d₁ d₂))
      · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inl hℓ))) (.child (tcChildSnd d₁ d₂))
      · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inr hℓ))) (.child (tcChildFst d₁ d₂))
      · have hk := hK R r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · exact .trans (hr₁ ℓ (List.mem_append.mpr (.inl hk))) (.child (tcChildFst d₁ d₂))
        · exact .trans (hr₂ ℓ (List.mem_append.mpr (.inr hk))) (.child (tcChildSnd d₁ d₂))

mutual

/-- Stratum A on a provenance chain between two Π's: the output and `XContract`'s
    bound (every output leaf is `SubEq` an input leaf). -/
def xTcReady : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) → XTcReady c → piSpinedTc c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, ready, hp, _, _, _, _, ha, hb => by
      have hp' : piSpinedT d = true := by simpa only [piSpinedTc] using hp
      obtain ⟨r, hr⟩ := xTReady K hK d ready hsub hp' ha hb
      exact ⟨r, fun ℓ hℓ => ⟨.tc d, by
        simp only [EvTc.leaves, List.mem_cons, List.not_mem_nil, or_false],
        .inr (hr ℓ hℓ)⟩⟩
  | _, _, _, .ofCv _ c, ready, hp, _, _, _, _, ha, hb =>
      xCvReady c ready (by simpa only [piSpinedTc] using hp) ha hb
  | Γ, _, _, .refl _ A, ready, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, .symm c, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedTc c = true := by simpa only [piSpinedTc] using hp
      obtain ⟨r, hr⟩ := xTcReady c ready hp' hb ha
      refine ⟨(.symm r.1, K R (.symm r.1) (.symm r.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      have hin : ℓ ∈ r.1.leaves ++ r.2.leaves := by
        rcases hℓ with hℓ | hℓ
        · exact List.mem_append.mpr (.inl hℓ)
        · have := hK R (.symm r.1) (.symm r.2) ℓ hℓ
          simpa only [EvTc.leaves] using this
      obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ hin
      exact ⟨ℓ', by simpa only [EvTc.leaves] using hℓ', hs⟩
  | _, _, _, @EvTc.trans _ _ _ _ _ M _ c₁ c₂, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedTc, Bool.and_eq_true] at hp'
      have hm := hp'.1.1
      have hp1 := hp'.1.2
      have hp2 := hp'.2
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      obtain ⟨r₁, hr₁⟩ := xTcReady c₁ ready.1 hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xTcReady c₂ ready.2 hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (K R r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      simp only [EvTc.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr₁ ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr₂ ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inr hℓ', hs⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr₁ ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · have hk := hK R r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨ℓ', hℓ', hs⟩ := hr₁ ℓ (List.mem_append.mpr (.inl hk))
          exact ⟨ℓ', .inl hℓ', hs⟩
        · obtain ⟨ℓ', hℓ', hs⟩ := hr₂ ℓ (List.mem_append.mpr (.inr hk))
          exact ⟨ℓ', .inr hℓ', hs⟩
  | _, _, _, .piCod _ hA c, ready, _, A₁, B₁, A₂, B₂, ha, hb => by
      injection ha with h1 h2
      injection hb with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.refl _ _, c), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.nil_append] at hℓ
      exact ⟨ℓ, by simp only [EvTc.leaves, List.mem_append]; exact .inr hℓ, .inl rfl⟩
  | _, _, _, @EvTc.wk _ _ _ Γ₀ A₀ B₀ d k h, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedTc, Bool.and_eq_true] at hp'
      have hpa := hp'.1.1
      have hpb := hp'.1.2
      have hph := hp'.2
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xTcReady h ready hph hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (lift k 1 P₁) (lift (k + 1) 1 P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (lift k 1 Q₁) (lift (k + 1) 1 Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.wk d k r.1, .wk d (k + 1) r.2), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves] at hℓ
      obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ hℓ
      exact ⟨ℓ', by simpa only [EvTc.leaves] using hℓ', hs⟩
  | _, _, _, @EvTc.subst0 _ _ _ Γ₀ A₀ A₀' t v j c hget hv, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedTc, Bool.and_eq_true] at hp'
      have hpa := hp'.1.1
      have hpb := hp'.1.2
      have hpc := hp'.2
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xTcReady c ready hpc hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (instantiate j (lift 0 j v) P₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (instantiate j (lift 0 j v) Q₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.subst0 j r.1 hget hv,
        EvTc.cast rfl
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
          (.subst0 (j + 1) r.2 (by simpa using hget)
            (substBinderArg (d := .assumption P₁) hv))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ
      simp only [EvTc.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩
  | _, _, _, @EvTc.substLet _ _ _ Γ₀ A₀ A₀' t w0 j c hget hv, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedTc, Bool.and_eq_true] at hp'
      have hpa := hp'.1.1
      have hpb := hp'.1.2
      have hpc := hp'.2
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xTcReady c ready hpc hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (instantiate j (lift 0 j w0) P₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j w0)) P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (instantiate j (lift 0 j w0) Q₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j w0)) Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.substLet j r.1 hget hv,
        EvTc.cast rfl
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w0])
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w0])
          (.substLet (j + 1) r.2 (by simpa using hget)
            (substBinderArg (d := .assumption P₁) hv))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ
      simp only [EvTc.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩

/-- Stratum A on a provenance conversion between two Π's, `XContract`'s bound. -/
def xCvReady : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) → XCvReady c → piSpinedCv c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ'
  | _, _, _, _, .lit h hsub, ready, hp, _, _, _, _, ha, hb => by
      have hp' : piSpinedConv h = true := by simpa only [piSpinedCv] using hp
      obtain ⟨r, hr⟩ := xConvReady K hK h ready hsub hp' ha hb
      exact ⟨r, fun ℓ hℓ => ⟨.cv h, by
        simp only [EvCv.leaves, List.mem_cons, List.not_mem_nil, or_false],
        .inr (hr ℓ hℓ)⟩⟩
  | Γ, _, _, _, .refl _, ready, _, A₁, B₁, A₂, B₂, ha, hb => by
      subst ha
      injection hb with h1 h2
      subst h1; subst h2
      exact ⟨(.refl Γ A₁, .refl _ B₁), fun ℓ hℓ => by
        simp only [XOut.leaves, EvTc.leaves, List.append_nil] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, _, .symm c, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedCv c = true := by simpa only [piSpinedCv] using hp
      obtain ⟨r, hr⟩ := xCvReady c ready hp' hb ha
      refine ⟨(.symm r.1, K R (.symm r.1) (.symm r.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      have hin : ℓ ∈ r.1.leaves ++ r.2.leaves := by
        rcases hℓ with hℓ | hℓ
        · exact List.mem_append.mpr (.inl hℓ)
        · have := hK R (.symm r.1) (.symm r.2) ℓ hℓ
          simpa only [EvTc.leaves] using this
      obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ hin
      exact ⟨ℓ', by simpa only [EvCv.leaves] using hℓ', hs⟩
  | _, _, _, _, @EvCv.trans _ _ _ _ _ m _ _ c₁ c₂, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedCv, Bool.and_eq_true] at hp'
      have hm := hp'.1.1
      have hp1 := hp'.1.2
      have hp2 := hp'.2
      obtain ⟨M₁, M₂, hmeq⟩ := isPiD _ hm
      obtain ⟨r₁, hr₁⟩ := xCvReady c₁ ready.1 hp1 ha hmeq
      obtain ⟨r₂, hr₂⟩ := xCvReady c₂ ready.2 hp2 hmeq hb
      refine ⟨(.trans r₁.1 r₂.1, .trans r₁.2 (K R r₁.1 r₂.2)), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, List.mem_append] at hℓ
      simp only [EvCv.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr₁ ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr₂ ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inr hℓ', hs⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr₁ ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · have hk := hK R r₁.1 r₂.2 ℓ hℓ
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨ℓ', hℓ', hs⟩ := hr₁ ℓ (List.mem_append.mpr (.inl hk))
          exact ⟨ℓ', .inl hℓ', hs⟩
        · obtain ⟨ℓ', hℓ', hs⟩ := hr₂ ℓ (List.mem_append.mpr (.inr hk))
          exact ⟨ℓ', .inr hℓ', hs⟩
  | _, _, _, _, .sorts .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .consts .., _, hp, _, _, _, _, _, _ => nomatch hp
  | _, _, _, _, .tyConv _ c cA, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedCv c = true := by simpa only [piSpinedCv] using hp
      obtain ⟨r, hr⟩ := xCvReady c ready hp' ha hb
      refine ⟨r, fun ℓ hℓ => ?_⟩
      obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ hℓ
      exact ⟨ℓ', by simp only [EvCv.leaves, List.mem_append]; exact .inl hℓ', hs⟩
  | _, _, _, _, .rety c cA, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' : piSpinedCv c = true := by simpa only [piSpinedCv] using hp
      obtain ⟨r, hr⟩ := xCvReady c ready hp' ha hb
      refine ⟨r, fun ℓ hℓ => ?_⟩
      obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ hℓ
      exact ⟨ℓ', by simp only [EvCv.leaves, List.mem_append]; exact .inl hℓ', hs⟩
  | _, _, _, _, @EvCv.wk _ _ _ Γ₀ a₀ b₀ T₀ d k h, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedCv, Bool.and_eq_true] at hp'
      have hpa := hp'.1.1
      have hpb := hp'.1.2
      have hph := hp'.2
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xCvReady h ready hph hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (lift k 1 P₁) (lift (k + 1) 1 P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (lift k 1 Q₁) (lift (k + 1) 1 Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.wk d k r.1, .wk d (k + 1) r.2), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves] at hℓ
      obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ hℓ
      exact ⟨ℓ', by simpa only [EvCv.leaves] using hℓ', hs⟩
  | _, _, _, _, @EvCv.esub _ _ _ Γ₀ a₀ b₀ T₀ t v j u h hget hv hvT, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedCv, Bool.and_eq_true] at hp'
      have hpa := hp'.1.1
      have hpb := hp'.1.2
      have hph := hp'.2
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xCvReady h ready hph hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (instantiate j (lift 0 j v) P₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (instantiate j (lift 0 j v) Q₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.subst0 j r.1 hget hv,
        EvTc.cast rfl
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
          (.subst0 (j + 1) r.2 (by simpa using hget)
            (substBinderArg (d := .assumption P₁) hv))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ
      simp only [EvCv.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl (.inl hℓ'), hs⟩
      · exact ⟨ℓ, .inl (.inr hℓ), .inl rfl⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl (.inl hℓ'), hs⟩
      · exact ⟨ℓ, .inl (.inr hℓ), .inl rfl⟩

  | _, _, _, _, @EvCv.subst0 _ _ _ Γ₀ a₀ b₀ T₀ t v j h hget hv, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedCv, Bool.and_eq_true] at hp'
      obtain ⟨⟨hpa, hpb⟩, hph⟩ := hp'
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xCvReady h ready hph hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (instantiate j (lift 0 j v) P₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (instantiate j (lift 0 j v) Q₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j v)) Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.subst0 j r.1 hget hv,
        EvTc.cast rfl
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
          (.subst0 (j + 1) r.2 (by simpa using hget)
            (substBinderArg (d := .assumption P₁) hv))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ
      simp only [EvCv.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩

  | _, _, _, _, @EvCv.substLet _ _ _ Γ₀ a₀ b₀ T₀ t w j h hget hv, ready, hp, A₁, B₁, A₂, B₂, ha, hb => by
      have hp' := hp
      simp only [piSpinedCv, Bool.and_eq_true] at hp'
      obtain ⟨⟨hpa, hpb⟩, hph⟩ := hp'
      obtain ⟨P₁, P₂, hP⟩ := isPiD _ hpa
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD _ hpb
      obtain ⟨r, hr⟩ := xCvReady h ready hph hP hQ
      subst hP; subst hQ
      have ha' : Expr.pi (instantiate j (lift 0 j w) P₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j w)) P₂) = .pi A₁ B₁ := ha
      have hb' : Expr.pi (instantiate j (lift 0 j w) Q₁)
          (instantiate (j + 1) (lift 0 1 (lift 0 j w)) Q₂) = .pi A₂ B₂ := hb
      injection ha' with h1 h2
      injection hb' with h3 h4
      subst h1; subst h2; subst h3; subst h4
      refine ⟨(.substLet j r.1 hget hv,
        EvTc.cast rfl
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
          (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
          (.substLet (j + 1) r.2 (by simpa using hget)
            (substBinderArg (d := .assumption P₁) hv))), fun ℓ hℓ => ?_⟩
      simp only [XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ
      simp only [EvCv.leaves, List.mem_append]
      rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inl hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩
      · obtain ⟨ℓ', hℓ', hs⟩ := hr ℓ (List.mem_append.mpr (.inr hℓ))
        exact ⟨ℓ', .inl hℓ', hs⟩
      · exact ⟨ℓ, .inr hℓ, .inl rfl⟩

end

end Workers

section ContextWorkers
variable (K : ∀ R : List (Jd E n), CtxConvProc R) (hK : CtxConvContract K)
def xConvWithCtx (C : XCtxKit E n R) : {Γ : LCtx} → {a b T : Expr Nat} → (h : ConvT E n Γ a b T) → C.Ctx Γ →
    (∃ r ∈ R, SubEq (.cv h) r) → piSpinedConv h = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.cv h) :=
  fun {_} {_} {_} {_} c v => xConvReady K hK c (XConvReady.ofCtx C c v)

def xConv' (hsep : SepAll E n) : {Γ : LCtx} → {a b T : Expr Nat} → (h : ConvT E n Γ a b T) →
    (∃ r ∈ R, SubEq (.cv h) r) → piSpinedConv h = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.cv h) :=
  fun {_} {_} {_} {_} c => xConvWithCtx K hK (.universal hsep) c PUnit.unit

def xTWithCtx (C : XCtxKit E n R) : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) → C.Ctx Γ →
    (∃ r ∈ R, SubEq (.tc d) r) → piSpinedT d = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.tc d) :=
  fun {_} {_} {_} c v => xTReady K hK c (XTReady.ofCtx C c v)

def xT' (hsep : SepAll E n) : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
    (∃ r ∈ R, SubEq (.tc d) r) → piSpinedT d = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, SubOf ℓ (.tc d) :=
  fun {_} {_} {_} c => xTWithCtx K hK (.universal hsep) c PUnit.unit

def xTcWithCtx (C : XCtxKit E n R) : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) → C.Ctx Γ → piSpinedTc c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  fun {_} {_} {_} c v => xTcReady K hK c (XTcReady.ofCtx C c v)

def xTc' (hsep : SepAll E n) : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) → piSpinedTc c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  fun {_} {_} {_} c => xTcWithCtx K hK (.universal hsep) c PUnit.unit

def xCvWithCtx (C : XCtxKit E n R) : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) → C.Ctx Γ → piSpinedCv c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  fun {_} {_} {_} {_} c v => xCvReady K hK c (XCvReady.ofCtx C c v)

def xCv' (hsep : SepAll E n) : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) → piSpinedCv c = true →
    ∀ {A₁ B₁ A₂ B₂ : Expr Nat}, a = .pi A₁ B₁ → b = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  fun {_} {_} {_} {_} c => xCvWithCtx K hK (.universal hsep) c PUnit.unit

end ContextWorkers


/-! ### the public X on Π-spined chains, in `XProc`'s shape -/

section Public

variable (K : ∀ R : List (Jd E n), CtxConvProc R) (hK : CtxConvContract K) (hsep : SepAll E n)

/-- Stratum A at the general endpoint equations (for S3's segment assembly). -/
def xStructTc {Γ : LCtx} {A B : Expr Nat} (c : EvTc R Γ A B) (hp : piSpinedTc c = true)
    {A₁ B₁ A₂ B₂ : Expr Nat} (ha : A = .pi A₁ B₁) (hb : B = .pi A₂ B₂) :
    XOut R Γ A₁ B₁ A₂ B₂ :=
  (xTc' K hK hsep c hp ha hb).1

theorem xStructTc_leaves {Γ : LCtx} {A B : Expr Nat} (c : EvTc R Γ A B)
    (hp : piSpinedTc c = true) {A₁ B₁ A₂ B₂ : Expr Nat} (ha : A = .pi A₁ B₁)
    (hb : B = .pi A₂ B₂) :
    ∀ ℓ ∈ XOut.leaves (xStructTc K hK hsep c hp ha hb), ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  (xTc' K hK hsep c hp ha hb).2

/-- Stratum A X: exactly `XProc`'s shape, on Π-spined inputs. -/
def xStruct {Γ : LCtx} {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hp : piSpinedTc c = true) : EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B' :=
  (xTc' K hK hsep c hp rfl rfl).1

/-- `XContract`'s clause on Π-spined inputs: every output leaf is `SubEq` an input leaf. -/
theorem xStruct_contract {Γ : LCtx} {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    ∀ ℓ ∈ (xStruct K hK hsep c hp).1.leaves ++ (xStruct K hK hsep c hp).2.leaves,
      ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  (xTc' K hK hsep c hp rfl rfl).2

end Public

/-! ### pins -/

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the fixture's actual X request (`trans (lit cL) (symm (lit cR))`, middle `piL`) is
    Π-spined, and its `symm`'d `ConvT.pi` link has `A ≠ A'`: a real context conversion. -/
theorem pin_request_piSpined : piSpinedTc request = true := by
  simp only [request, annotRequest, cL, cR, piConversion, piSpinedTc, piSpinedT, piSpinedConv,
    isPi, Bool.and_self, Bool.true_and, Bool.and_true]

/-- `xStruct` on the fixture's request yields `X_outputs_edge`'s fact for the fixture's
    actual caller, for any `K`, `hK`, `hsep`: every output leaf is strictly below an
    ORIGINAL removed D input. -/
theorem pin_request_edge (K : ∀ R : List (Jd emptyEnv 0), CtxConvProc R)
    (hK : CtxConvContract K) (hsep : SepAll emptyEnv 0) :
    OM3_edge (callerAtoms dL dR cL cR frame)
      (((xStruct K hK hsep request pin_request_piSpined).1.leaves ++
        (xStruct K hK hsep request pin_request_piSpined).2.leaves) ++ frame) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun ℓ hℓ => by
    obtain ⟨ℓ', hm, hs⟩ := xStruct_contract K hK hsep request pin_request_piSpined ℓ hℓ
    obtain ⟨root, hr, ht⟩ := annotRequest_strict dL dR cL cR ℓ' hm
    exact ⟨root, hr, subEq_trans_subOf hs ht⟩)

/-- `Π (Sort 0), Sort 0` and its own sort. -/
abbrev piX : Expr Nat := .pi (.sort .zero) (.sort .zero)
abbrev sX : Expr Nat := .sort (.imax (.succ .zero) (.succ .zero))

/-- `(λ x : sX. x) piX ≡ piX` at `emptyEnv`, by `beta`. -/
def betaRedexConv : ConvT emptyEnv 0 [] (.app (.lam sX (.bvar 0)) piX) piX sX :=
  .beta [] sX (.bvar 0) piX sX (.succ (.imax (.succ .zero) (.succ .zero)))
    (.sort [] _) (.bvar [.assumption sX] 0 sX rfl) (pinPiT emptyEnv 0)

/-- `piX ≡ (λ x. x) piX ≡ piX`: a Π→Π chain with an application in the middle. -/
def betaMiddleT : TyConvT emptyEnv 0 [] piX piX :=
  .trans [] piX (.app (.lam sX (.bvar 0)) piX) piX
    (.of [] piX _ (.imax (.succ .zero) (.succ .zero)) (.symm [] _ _ _ betaRedexConv))
    (.of [] _ piX (.imax (.succ .zero) (.succ .zero)) betaRedexConv)

/-- negative control: a non-Π middle is rejected (Stratum B, S0 §5). -/
theorem pin_betaMiddle_not_piSpined :
    piSpinedTc (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
      EvTc [Jd.tc betaMiddleT] [] piX piX) = false := by
  simp only [piSpinedTc, piSpinedT, betaMiddleT, isPi, Bool.false_and]

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.CtxConvProc
#print axioms Rcic.Declarative.F8Measure.CtxConvContract
#print axioms Rcic.Declarative.F8Measure.SepAll
#print axioms Rcic.Declarative.F8Measure.tcChildFst
#print axioms Rcic.Declarative.F8Measure.tcChildSnd
#print axioms Rcic.Declarative.F8Measure.tcChildOf
#print axioms Rcic.Declarative.F8Measure.cvChildSymm
#print axioms Rcic.Declarative.F8Measure.cvChildTransFst
#print axioms Rcic.Declarative.F8Measure.cvChildTransSnd
#print axioms Rcic.Declarative.F8Measure.cvChildTyConv
#print axioms Rcic.Declarative.F8Measure.cvChildPiFst
#print axioms Rcic.Declarative.F8Measure.cvChildPiSnd
#print axioms Rcic.Declarative.F8Measure.isPi
#print axioms Rcic.Declarative.F8Measure.isPi_true
#print axioms Rcic.Declarative.F8Measure.isPiD
#print axioms Rcic.Declarative.F8Measure.piSpinedConv
#print axioms Rcic.Declarative.F8Measure.piSpinedT
#print axioms Rcic.Declarative.F8Measure.piSpinedTc
#print axioms Rcic.Declarative.F8Measure.piSpinedCv
#print axioms Rcic.Declarative.F8Measure.XOut
#print axioms Rcic.Declarative.F8Measure.XOut.leaves
#print axioms Rcic.Declarative.F8Measure.substBinderArg
#print axioms Rcic.Declarative.F8Measure.substBinderArg_leaves
#print axioms Rcic.Declarative.F8Measure.xConv'
#print axioms Rcic.Declarative.F8Measure.xT'
#print axioms Rcic.Declarative.F8Measure.xTc'
#print axioms Rcic.Declarative.F8Measure.xCv'
#print axioms Rcic.Declarative.F8Measure.xStructTc
#print axioms Rcic.Declarative.F8Measure.xStructTc_leaves
#print axioms Rcic.Declarative.F8Measure.xStruct
#print axioms Rcic.Declarative.F8Measure.xStruct_contract
#print axioms Rcic.Declarative.F8Measure.pin_request_piSpined
#print axioms Rcic.Declarative.F8Measure.pin_request_edge
#print axioms Rcic.Declarative.F8Measure.betaRedexConv
#print axioms Rcic.Declarative.F8Measure.betaMiddleT
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_not_piSpined
