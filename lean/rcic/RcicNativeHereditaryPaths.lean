import rcic.RcicNativeFamilyProjection
import rcic.RcicDT0709EnvWf
import rcic.RcicCtxConvT

/-!
Hereditary extension of the finite constructions in NativeCertifiedPathsDraft.
Source pin: 76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.
COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound]. Remains a research draft in scope.

This module deliberately reuses NativeFamilyProjection.ProofLeaf and Step,
so GoodPath.toCertifiedStar lands in that draft's actual CertifiedStar.
It keeps every literal ParRedT constructor. It does not turn arbitrary
root-certified paths or arbitrary raw Steps into hereditary ones.

Every recursive Step child has its own exact native certificate and its
own recursive child data. Native ConvT/typing/witness fields are not Step
children. No total valley producer or residual/strip theorem is claimed.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeHereditaryPaths76

variable {E : ResolvedEnv} {n : Nat}

abbrev ProofLeaf := NativeFamilyProjection.ProofLeaf
abbrev Step (E : ResolvedEnv) (n : Nat) :=
  ParRedT (ProofLeaf E n) E n

def leafTy {Γ : LCtx} {p q T : Expr Nat} (h : ProofLeaf E n Γ p q T) :
    HasTyT E n Γ p T × HasTyT E n Γ q T :=
  NativeFamilyProjection.ProofLeaf.endpoints h

def leafConv {Γ : LCtx} {p q T : Expr Nat} (h : ProofLeaf E n Γ p q T) :
    ConvT E n Γ p q T :=
  NativeFamilyProjection.ProofLeaf.native h

/-- Full hereditary child data for the literal eighteen-constructor tree.
The root certificate for each child is stored at THAT child's context and
index. In particular app's function child stays at T0, and let bodies stay
under the original LEFT value. Every constructor is written explicitly.
-/
def ChildCerts :
    {Γ : LCtx} → {a b T : Expr Nat} → Step E n Γ a b T → Type
  | _, _, _, _, .refl _ _ _ _ => PUnit
  | _, _, _, _, .sortEq _ _ _ _ _ _ _ => PUnit
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ => PUnit
  | Γ, _, _, _, .bvarZeta _ i A v v' _ _ hv _ _ =>
      ConvT E n (Γ.drop (i + 1)) v v' A × ChildCerts hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _ => PUnit
  | Γ, _, _, _, .app _ f f' a a' A _ T0 _ _ hf _ _ _ ha _ =>
      (ConvT E n Γ f f' T0 × ChildCerts hf) ×
        (ConvT E n Γ a a' A × ChildCerts ha)
  | Γ, _, _, _, .beta _ A body body' arg arg' B _ _ _ _ _ _ hb ha _ =>
      (ConvT E n (.assumption A :: Γ) body body' B × ChildCerts hb) ×
        (ConvT E n Γ arg arg' A × ChildCerts ha)
  | Γ, _, _, _, .lam _ A _ body body' B _ _ _ _ _ hb _ =>
      ConvT E n (.assumption A :: Γ) body body' B × ChildCerts hb
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ => PUnit
  | Γ, _, _, _, .letE _ A _ value value' body body' B _ _ _ _ hv _ _ hb _ =>
      (ConvT E n Γ value value' A × ChildCerts hv) ×
        (ConvT E n (.letBinding A value :: Γ) body body' B × ChildCerts hb)
  | Γ, _, _, _, .zeta _ A value value' body body' B _ _ _ hv _ _ hb _ =>
      (ConvT E n Γ value value' A × ChildCerts hv) ×
        (ConvT E n (.letBinding A value :: Γ) body body' B × ChildCerts hb)
  | Γ, _, _, _, .iotaSpine _ lhs lhs' _ T hs _ _ _ =>
      ConvT E n Γ lhs lhs' T × ChildCerts hs
  | _, _, _, _, .iotaStarK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => PUnit
  | _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => PUnit
  | _, _, _, _, .lit _ _ _ _ => PUnit
  | Γ, _, _, _, .eta _ f f' A B hf _ =>
      ConvT E n Γ f f' (.pi A B) × ChildCerts hf
  | _, _, _, _, .peq _ _ _ _ _ => PUnit
  | Γ, _, _, _, .conv _ a b A _ hs _ =>
      ConvT E n Γ a b A × ChildCerts hs

/-- A root certificate together with the certificates of all literal children,
recursively. This is data indexed by the ACTUAL Step derivation. -/
abbrev GoodStep {Γ : LCtx} {a b T : Expr Nat} (s : Step E n Γ a b T) : Type :=
  ConvT E n Γ a b T × ChildCerts s

def goodRefl {Γ : LCtx} {a T : Expr Nat} (h : HasTyT E n Γ a T) :
    GoodStep (.refl Γ a T h) :=
  ⟨.refl Γ a T h, PUnit.unit⟩

def goodPeq {Γ : LCtx} {p q T : Expr Nat} (h : ProofLeaf E n Γ p q T) :
    GoodStep (.peq Γ p q T h) :=
  ⟨leafConv h, PUnit.unit⟩

def goodConv {Γ : LCtx} {a b T T' : Expr Nat}
    {s : Step E n Γ a b T} (g : GoodStep s) (d : TyConvT E n Γ T T') :
    GoodStep (.conv Γ a b T T' s d) :=
  ⟨convT_of_tyConv g.1 d, g⟩

/-- The exact family-decoder condition, using its original ProofLeaf carrier. -/
abbrev ArgCert {Γ : LCtx} {a b T : Expr Nat} (s : Step E n Γ a b T) : Prop :=
  NativeFamilyProjection.ArgCert s

/-- This needs no environment regularity, row, backlift, or schema supplier.
At app, use the actual function-child tree and the actual argument-child
root ConvT at A. All other constructor clauses match the decoder literally.
-/
def goodStep_argCert :
    {Γ : LCtx} → {a b T : Expr Nat} → (s : Step E n Γ a b T) →
      GoodStep s → ArgCert s
  | _, _, _, _, .refl _ _ _ _, _ => True.intro
  | _, _, _, _, .sortEq _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .consts _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ _ _, g =>
      ⟨goodStep_argCert hf g.2.1, ⟨g.2.2.1⟩⟩
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _, g =>
      goodStep_argCert hs g.2
  | _, _, _, _, .iotaStarK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .lit _ _ _ _, _ => True.intro
  | _, _, _, _, .eta _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, _, .peq _ _ _ _ _, _ => True.intro
  | _, _, _, _, .conv _ _ _ _ _ hs _, g => goodStep_argCert hs g.2

inductive GoodPath (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T : Expr Nat) :
    Expr Nat → Expr Nat → Type where
  | refl {a : Expr Nat} (h : HasTyT E n Γ a T) : GoodPath E n Γ T a a
  | tail {a b c : Expr Nat} (s : Step E n Γ a b T)
      (good : GoodStep s) (rest : GoodPath E n Γ T b c) :
      GoodPath E n Γ T a c

def GoodPath.erase {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    GoodPath E n Γ T a b → ParRedTStar (ProofLeaf E n) E n Γ a b T
  | _, _, .refl h => .refl Γ _ T h
  | _, _, .tail s _ rest => .tail s rest.erase

def GoodPath.toCertifiedStar {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    GoodPath E n Γ T a b →
      NativeFamilyProjection.CertifiedStar (E := E) (n := n) Γ a b T
  | _, _, .refl h => .refl _ _ h
  | _, _, .tail s g rest =>
      .tail s (goodStep_argCert s g) rest.toCertifiedStar

def GoodPath.rightTy {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    GoodPath E n Γ T a b → HasTyT E n Γ b T
  | _, _, .refl h => h
  | _, _, .tail _ _ rest => rest.rightTy

def GoodPath.leftTy {Γ : LCtx} (hΓ : CtxWfT E n Γ) {T : Expr Nat} :
    {a b : Expr Nat} → GoodPath E n Γ T a b → HasTyT E n Γ a T
  | _, _, .refl h => h
  | _, _, .tail s _ _ => parRedT_hasTy_left leafTy hΓ s

def GoodPath.toConv {Γ : LCtx} {T : Expr Nat} : {a b : Expr Nat} →
    GoodPath E n Γ T a b → ConvT E n Γ a b T
  | _, _, .refl h => .refl Γ _ T h
  | _, _, .tail _ g rest => .trans Γ _ _ _ T g.1 rest.toConv

def GoodPath.append {Γ : LCtx} {T : Expr Nat} : {a b c : Expr Nat} →
    GoodPath E n Γ T a b → GoodPath E n Γ T b c → GoodPath E n Γ T a c
  | _, _, _, .refl _, q => q
  | _, _, _, .tail s g rest, q => .tail s g (rest.append q)

def GoodPath.one {Γ : LCtx} {a b T : Expr Nat} (s : Step E n Γ a b T)
    (g : GoodStep s) (hb : HasTyT E n Γ b T) : GoodPath E n Γ T a b :=
  .tail s g (.refl hb)

def GoodPath.changeIndex {Γ : LCtx} {T T' : Expr Nat}
    (d : TyConvT E n Γ T T') : {a b : Expr Nat} →
    GoodPath E n Γ T a b → GoodPath E n Γ T' a b
  | _, _, .refl h => .refl (hasTyT_of_tyConvT h d)
  | _, _, .tail s g rest =>
      .tail (.conv Γ _ _ T T' s d) (goodConv g d) (rest.changeIndex d)

structure GoodValley (Γ : LCtx) (a b T : Expr Nat) where
  centre : Expr Nat
  left : GoodPath E n Γ T a centre
  right : GoodPath E n Γ T b centre

def GoodValley.toCertifiedValley {Γ : LCtx} {a b T : Expr Nat}
    (v : GoodValley (E := E) (n := n) Γ a b T) :
    NativeFamilyProjection.CertifiedValley (E := E) (n := n) Γ a b T :=
  ⟨v.centre, v.left.toCertifiedStar, v.right.toCertifiedStar⟩

def GoodValley.symm {Γ : LCtx} {a b T : Expr Nat}
    (v : GoodValley (E := E) (n := n) Γ a b T) :
    GoodValley (E := E) (n := n) Γ b a T :=
  ⟨v.centre, v.right, v.left⟩

/-- Raw inputs are allowed here because the new output is a fresh peq leaf.
Their hereditary data is not needed or asserted. -/
def proofIndexPeak {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b c T : Expr Nat} (hT : HasTyT E n Γ T (.sort .zero))
    (sL : Step E n Γ a b T) (sR : Step E n Γ a c T) :
    GoodValley (E := E) (n := n) Γ b c T := by
  let hb := parRedT_hasTy_right leafTy hΓ sL
  let hc := parRedT_hasTy_right leafTy hΓ sR
  let leaf : ProofLeaf E n Γ b c T := ⟨hT, hb, hc⟩
  exact ⟨c, GoodPath.one (.peq Γ b c T leaf) (goodPeq leaf) hc, .refl hc⟩

/-- The entire incoming function-child tree is preserved. -/
noncomputable def appFun {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' a A B : Expr Nat} {v : Level}
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort v))
    (ha : HasTyT E n Γ a A)
    (p : GoodPath E n Γ (.pi A B) f f') :
    GoodPath E n Γ (instantiate0 a B) (.app f a) (.app f' a) := by
  induction p with
  | refl hf => exact .refl (.app Γ _ a A B hf ha)
  | @tail f g f' s gs rest ih =>
      have hg := parRedT_hasTy_right leafTy hΓ s
      let sApp : Step E n Γ (.app f a) (.app g a) (instantiate0 a B) :=
        .app Γ f g a a A B (.pi A B) v v s (.refl Γ _) hB hTy
          (.refl Γ a A ha) (.app Γ g a A B hg ha)
      let gApp : GoodStep sApp :=
        ⟨.app Γ f g a a A B gs.1 (.refl Γ a A ha), gs, goodRefl ha⟩
      exact .tail sApp gApp ih

/-- The whole incoming argument-child tree survives under app and conv.
Only its stored root certificate is used for the native type accumulator. -/
noncomputable def appArgGo {Γ : LCtx} (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {f a₀ a a' A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (ha₀ : HasTyT E n Γ a₀ A) (p : GoodPath E n Γ A a a') :
    HasTyT E n Γ a A → ConvT E n Γ a₀ a A →
    GoodPath E n Γ (instantiate0 a₀ B) (.app f a) (.app f a') := by
  induction p with
  | @refl a ha =>
      intro _ cacc
      exact .refl
        (.conv Γ (.app f a) (instantiate0 a B) (instantiate0 a₀ B) v
          (.app Γ f a A B hf ha)
          (convT_inst0_valueSort hA hB ha ha₀ (.symm Γ a₀ a A cacc)))
  | @tail a aNext a' s gs rest ih =>
      intro ha cacc
      let cs := gs.1
      have hNext := parRedT_hasTy_right leafTy hΓ s
      have cnext : ConvT E n Γ a₀ aNext A := .trans Γ _ _ _ A cacc cs
      have d : TyConvT E n Γ (instantiate0 a B) (instantiate0 a₀ B) :=
        .of Γ _ _ v
          (convT_inst0_valueSort hA hB ha ha₀ (.symm Γ a₀ a A cacc))
      have hr : HasTyT E n Γ (.app f aNext) (instantiate0 a B) :=
        .conv Γ _ (instantiate0 aNext B) (instantiate0 a B) v
          (.app Γ f aNext A B hf hNext)
          (convT_inst0_valueSort hA hB hNext ha (.symm Γ a aNext A cs))
      let sApp : Step E n Γ (.app f a) (.app f aNext) (instantiate0 a B) :=
        .app Γ f f a aNext A B (.pi A B) v v
          (.refl Γ f (.pi A B) hf) (.refl Γ _) hB
          (hasTyT_subst0_of_envWfT hW hB ha) s hr
      let cApp : ConvT E n Γ (.app f a) (.app f aNext) (instantiate0 a B) :=
        .app Γ f f a aNext A B (.refl Γ f (.pi A B) hf) cs
      let gApp : GoodStep sApp := ⟨cApp, goodRefl hf, gs⟩
      exact .tail (.conv Γ _ _ _ _ sApp d) (goodConv gApp d)
        (ih hNext cnext)

noncomputable def appArg {Γ : LCtx} (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {f a a' A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (ha : HasTyT E n Γ a A) (p : GoodPath E n Γ A a a') :
    GoodPath E n Γ (instantiate0 a B) (.app f a) (.app f a') :=
  appArgGo hW hΓ hA hB hf ha p ha (.refl Γ a A ha)

noncomputable def appValley {Γ : LCtx} (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (ca : ConvT E n Γ a b A)
    (vf : GoodValley (E := E) (n := n) Γ f g (.pi A B))
    (va : GoodValley (E := E) (n := n) Γ a b A) :
    GoodValley (E := E) (n := n) Γ (.app f a) (.app g b) (instantiate0 a B) := by
  let ha := va.left.leftTy hΓ
  let hb := va.right.leftTy hΓ
  let hF := vf.left.rightTy
  let leftFun := appFun hΓ hB (hasTyT_subst0_of_envWfT hW hB ha) ha vf.left
  let rightFun := appFun hΓ hB (hasTyT_subst0_of_envWfT hW hB hb) hb vf.right
  let leftArg := appArg hW hΓ hA hB hF ha va.left
  let rightArg := appArg hW hΓ hA hB hF hb va.right
  let d : TyConvT E n Γ (instantiate0 b B) (instantiate0 a B) :=
    .of Γ _ _ v (convT_inst0_valueSort hA hB hb ha (.symm Γ a b A ca))
  exact ⟨.app vf.centre va.centre,
    leftFun.append leftArg, (rightFun.append rightArg).changeIndex d⟩

/-- Although ArgCert at a lambda root is trivial, the stronger invariant
keeps the complete incoming body tree under the actual left binder. -/
noncomputable def lamBody {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A b b' B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (p : GoodPath E n (.assumption A :: Γ) B b b') :
    GoodPath E n Γ (.pi A B) (.lam A b) (.lam A b') := by
  induction p with
  | refl hb => exact .refl (.lam Γ A u _ B hA hb)
  | @tail b bm b' s gs rest ih =>
      have hbm := parRedT_hasTy_right leafTy (.assumption Γ A u hΓ hA) s
      let sLam : Step E n Γ (.lam A b) (.lam A bm) (.pi A B) :=
        .lam Γ A A b bm B u v (.refl Γ A (.sort u) hA) hA hB s
          (.lam Γ A u bm B hA hbm)
      let gLam : GoodStep sLam :=
        ⟨.lam Γ A A b bm B u (.refl Γ A (.sort u) hA) gs.1, gs⟩
      exact .tail sLam gLam ih

def lamAnnotationBack {Γ : LCtx} (hW : EnvWfT E)
    {A A' b B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hA' : HasTyT E n Γ A' (.sort u))
    (cA : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hb : HasTyT E n (.assumption A :: Γ) b B) :
    GoodPath E n Γ (.pi A B) (.lam A' b) (.lam A b) := by
  let hcc : CtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ) :=
    .assumption (ctxConvT_refl Γ) hA hA' cA
  let hB' := hasTyT_ctx (envClosed_of_envWfT hW) hcc hB
  let hb' := hasTyT_ctx (envClosed_of_envWfT hW) hcc hb
  let cPi : ConvT E n Γ (.pi A' B) (.pi A B) (.sort (.imax u v)) :=
    .pi Γ A' A B B u v (.symm Γ A A' (.sort u) cA)
      (.refl (.assumption A' :: Γ) B (.sort v) hB')
  let htarget : HasTyT E n Γ (.lam A b) (.pi A' B) :=
    .conv Γ _ (.pi A B) (.pi A' B) (.imax u v)
      (.lam Γ A u b B hA hb) (.symm Γ _ _ _ cPi)
  let s : Step E n Γ (.lam A' b) (.lam A b) (.pi A' B) :=
    .lam Γ A' A b b B u v (.symm Γ A A' (.sort u) cA) hA' hB'
      (.refl (.assumption A' :: Γ) b B hb') htarget
  let cs : ConvT E n Γ (.lam A' b) (.lam A b) (.pi A' B) :=
    .lam Γ A' A b b B u (.symm Γ A A' (.sort u) cA)
      (.refl (.assumption A' :: Γ) b B hb')
  let gs : GoodStep s := ⟨cs, goodRefl hb'⟩
  let d : TyConvT E n Γ (.pi A' B) (.pi A B) := .of Γ _ _ (.imax u v) cPi
  exact GoodPath.one (.conv Γ _ _ _ _ s d) (goodConv gs d)
    (.lam Γ A u b B hA hb)

noncomputable def lamValley {Γ : LCtx} (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A A' b b' B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hA' : HasTyT E n Γ A' (.sort u))
    (cA : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (vb : GoodValley (E := E) (n := n) (.assumption A :: Γ) b b' B) :
    GoodValley (E := E) (n := n) Γ (.lam A b) (.lam A' b') (.pi A B) := by
  let hb' := vb.right.leftTy (.assumption Γ A u hΓ hA)
  exact ⟨.lam A vb.centre,
    lamBody hΓ hA hB vb.left,
    (lamAnnotationBack hW hA hA' cA hB hb').append
      (lamBody hΓ hA hB vb.right)⟩

/-- Full hereditary evidence along the actual generated tree:
iotaSpine -> conv -> app -> {refl, peq}. No syntactic K gate is needed. -/
def fixedPrefixIotaThroughProof {Γ : LCtx} (hW : EnvWfT E)
    {f major ctor A B rhs T : Expr Nat} {v : Level}
    (hA0 : HasTyT E n Γ A (.sort .zero))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (hmajor : HasTyT E n Γ major A) (hctor : HasTyT E n Γ ctor A)
    (d : TyConvT E n Γ (instantiate0 ctor B) T)
    (hι : DerivedIota E (.app f ctor) rhs)
    (hrhs : HasTyT E n Γ rhs T) :
    GoodPath E n Γ T (.app f major) rhs := by
  let leaf : ProofLeaf E n Γ major ctor A := ⟨hA0, hmajor, hctor⟩
  let cMajor : ConvT E n Γ major ctor A := leafConv leaf
  let cIndex : ConvT E n Γ (instantiate0 major B) (instantiate0 ctor B) (.sort v) :=
    convT_inst0_valueSort hA0 hB hmajor hctor cMajor
  let dMajor : TyConvT E n Γ (instantiate0 major B) T :=
    .trans Γ _ _ _ (.of Γ _ _ v cIndex) d
  let hCtorAtMajor : HasTyT E n Γ (.app f ctor) (instantiate0 major B) :=
    .conv Γ _ (instantiate0 ctor B) (instantiate0 major B) v
      (.app Γ f ctor A B hf hctor) (.symm Γ _ _ _ cIndex)
  let sApp : Step E n Γ (.app f major) (.app f ctor) (instantiate0 major B) :=
    .app Γ f f major ctor A B (.pi A B) v v
      (.refl Γ f (.pi A B) hf) (.refl Γ _) hB
      (hasTyT_subst0_of_envWfT hW hB hmajor)
      (.peq Γ major ctor A leaf) hCtorAtMajor
  let cApp : ConvT E n Γ (.app f major) (.app f ctor) (instantiate0 major B) :=
    .app Γ f f major ctor A B (.refl Γ f (.pi A B) hf) cMajor
  let gApp : GoodStep sApp := ⟨cApp, goodRefl hf, goodPeq leaf⟩
  let sPre : Step E n Γ (.app f major) (.app f ctor) T :=
    .conv Γ _ _ _ _ sApp dMajor
  let gPre : GoodStep sPre := goodConv gApp dMajor
  let hCtorCall : HasTyT E n Γ (.app f ctor) T :=
    hasTyT_of_tyConvT (.app Γ f ctor A B hf hctor) d
  let cι : ConvT E n Γ (.app f ctor) rhs T := .iota Γ _ _ T hι hCtorCall hrhs
  let s : Step E n Γ (.app f major) rhs T :=
    .iotaSpine Γ _ _ _ T sPre (derivedIotaU_ofDerivedIota hι) hCtorCall hrhs
  let gs : GoodStep s := ⟨.trans Γ _ _ _ T gPre.1 cι, gPre⟩
  exact GoodPath.one s gs hrhs

/-- K has no recursive Step children. This constructs its hereditary data
from the actual gated constructor and an existing native endpoint anchor.
It is not a universal raw-K backlift. -/
def generatedKAtLegacyCentre {Γ : LCtx} (w : IotaWitness E)
    (major Tm rhs T : Expr Nat) (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n Γ major Tm)
    (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hι : DerivedIota E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T)
    (hrhs : HasTyT E n Γ rhs T)
    (cApp : ConvT E n Γ (iotaLhsOf w)
      (recCall (.const w.recRef w.ls) w.preMajor major) T) :
    GoodPath E n Γ T (recCall (.const w.recRef w.ls) w.preMajor major) rhs := by
  let s : Step E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) rhs T :=
    .iotaStarK Γ w major Tm rhs T rl afs hrl hsel hfam hmajor hmk hTm0
      (derivedIotaU_ofDerivedIota hι) hlι hlhs hrhs
  let cι : ConvT E n Γ (iotaLhsOf w) rhs T := .iota Γ _ _ T hι hlι hrhs
  let cs : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) rhs T :=
    .trans Γ _ _ _ T (.symm Γ _ _ T cApp) cι
  exact GoodPath.one s ⟨cs, PUnit.unit⟩ hrhs

end Rcic.Declarative.NativeHereditaryPaths76

