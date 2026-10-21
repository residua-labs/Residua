import rcic.RcicPinEqIotaStarK
import rcic.RcicParRedT
import rcic.RcicIotaLegacyAdm
import rcic.RcicNativeHereditaryPaths

/-!
Moving-minor eta-K peak at pin
76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.

COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound]. Remains a research draft in scope.
No sorry, no axiom, no native-normalization or InScope premise.
The environment is the actual three-cell pinEqGroupWfT fixture.
This file constructs a legal peak and its two-step residual valley.
It DOES NOT claim the zero/one-step common-successor negation.
That negation's all18 successor analysis and proof-escape boundary are
recorded in nv_resume_etak_report.md. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.NativeMovingMinor76

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

abbrev ProofLeaf := NativeHereditaryPaths76.ProofLeaf
abbrev Step := NativeHereditaryPaths76.Step eqEnvT 2
abbrev Star := ParRedTStar (ProofLeaf eqEnvT 2) eqEnvT 2

def actualEnvWf : EnvWfT eqEnvT := pinEqGroupWfT
def actualCtxWf : CtxWfT eqEnvT 2 [] := .nil

/-- Closed proposition Pi P:Prop, P. This is used as an Eq parameter,
not as an inhabited proposition. -/
def propParam : Expr Nat := .pi (.sort .zero) (.bvar 0)

def familyAt (b : Expr Nat) : Expr Nat :=
  foldApps (.const 63 []) [.sort .zero, propParam, b]

def domain : Expr Nat := familyAt propParam
def ctor : Expr Nat := foldApps (.const 64 []) [.sort .zero, propParam]

/-- Constant Sort-1 motive. Its codomain universe is 2. -/
def motive : Expr Nat :=
  .lam (.sort .zero) (.lam (familyAt (.bvar 0)) (.sort one))

def motiveType : Expr Nat :=
  .pi (.sort .zero) (.pi (familyAt (.bvar 0)) (.sort two))

def motiveAp (b p : Expr Nat) : Expr Nat := .app (.app motive b) p

def partialApp (x : Expr Nat) : Expr Nat :=
  foldApps (.const 65 [two]) [.sort .zero, propParam, motive, x, propParam]

def commonType : Expr Nat := .pi domain (.sort one)
abbrev commonSort : Level := .imax .zero two

def movingMinor : Expr Nat :=
  .app (.lam (.sort one) (.bvar 0)) (.sort .zero)

def parent : Expr Nat :=
  .app (.lam (.sort one) (partialApp (.bvar 0))) movingMinor

def leftEnd : Expr Nat := partialApp movingMinor
def rightEnd : Expr Nat := .lam domain (.sort .zero)
def middle : Expr Nat := .lam domain movingMinor

private def appTy {Gamma : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT eqEnvT 2 Gamma f (.pi A B))
    (ha : HasTyT eqEnvT 2 Gamma a A) :
    HasTyT eqEnvT 2 Gamma (.app f a) (instantiate0 a B) :=
  .app Gamma f a A B hf ha

def propParamTy (Gamma : LCtx) :
    HasTyT eqEnvT 2 Gamma propParam (.sort .zero) :=
  .conv Gamma propParam (.sort (.imax one .zero)) (.sort .zero)
    (.succ (.imax one .zero))
    (.pi Gamma (.sort .zero) one (.bvar 0) .zero
      (.sort Gamma .zero) (.bvar _ 0 _ rfl))
    (.sorts Gamma (.imax one .zero) .zero (fun _ => rfl))

def familyTy (Gamma : LCtx) {b : Expr Nat}
    (hb : HasTyT eqEnvT 2 Gamma b (.sort .zero)) :
    HasTyT eqEnvT 2 Gamma (familyAt b) (.sort .zero) := by
  have h0 := HasTyT.const (E := eqEnvT) (n := 2)
    Gamma 63 [] eqFamT rfl rfl rfl
  have h1 := appTy h0 (.sort Gamma .zero)
  have h2 := appTy h1 (propParamTy Gamma)
  exact appTy h2 hb

def domainTy (Gamma : LCtx) :
    HasTyT eqEnvT 2 Gamma domain (.sort .zero) :=
  familyTy Gamma (propParamTy Gamma)

def ctorTy (Gamma : LCtx) : HasTyT eqEnvT 2 Gamma ctor domain := by
  have h0 := HasTyT.const (E := eqEnvT) (n := 2)
    Gamma 64 [] eqReflT rfl rfl rfl
  exact appTy (appTy h0 (.sort Gamma .zero)) (propParamTy Gamma)

def motiveBodyTy (Gamma : LCtx) :
    HasTyT eqEnvT 2 (.assumption (.sort .zero) :: Gamma)
      (.lam (familyAt (.bvar 0)) (.sort one))
      (.pi (familyAt (.bvar 0)) (.sort two)) :=
  .lam _ (familyAt (.bvar 0)) .zero (.sort one) (.sort two)
    (familyTy _ (.bvar _ 0 _ rfl)) (.sort _ one)

def motiveTy (Gamma : LCtx) :
    HasTyT eqEnvT 2 Gamma motive motiveType :=
  .lam Gamma (.sort .zero) one _ _ (.sort Gamma .zero) (motiveBodyTy Gamma)

/-- Two native beta edges evaluating the constant motive. -/
def motiveEval (Gamma : LCtx) {b p : Expr Nat}
    (hb : HasTyT eqEnvT 2 Gamma b (.sort .zero))
    (hp : HasTyT eqEnvT 2 Gamma p (familyAt b)) :
    ConvT eqEnvT 2 Gamma (motiveAp b p) (.sort one) (.sort two) := by
  have h1 : ConvT eqEnvT 2 Gamma (.app motive b)
      (.lam (familyAt b) (.sort one))
      (.pi (familyAt b) (.sort two)) :=
    .beta Gamma (.sort .zero)
      (.lam (familyAt (.bvar 0)) (.sort one)) b
      (.pi (familyAt (.bvar 0)) (.sort two)) one
      (.sort Gamma .zero) (motiveBodyTy Gamma) hb
  have h2 : ConvT eqEnvT 2 Gamma (motiveAp b p)
      (.app (.lam (familyAt b) (.sort one)) p) (.sort two) :=
    .app Gamma _ _ p p (familyAt b) (.sort two)
      h1 (.refl Gamma p (familyAt b) hp)
  exact .trans Gamma _ _ _ (.sort two) h2
    (.beta Gamma (familyAt b) (.sort one) p (.sort two) .zero
      (familyTy Gamma hb) (.sort _ one) hp)

def minorTy (Gamma : LCtx) {x : Expr Nat}
    (hx : HasTyT eqEnvT 2 Gamma x (.sort one)) :
    HasTyT eqEnvT 2 Gamma x (motiveAp propParam ctor) :=
  .conv Gamma x (.sort one) (motiveAp propParam ctor) two hx
    (.symm Gamma _ _ (.sort two)
      (motiveEval Gamma (propParamTy Gamma) (ctorTy Gamma)))

/-- The actual recursor application is typed by its stored declaration.
Its sole result-type conversion consists of two explicit motive beta edges
under the major binder, packaged by ConvT.pi. No Pi projection is read. -/
def partialTy (Gamma : LCtx) {x : Expr Nat}
    (hx : HasTyT eqEnvT 2 Gamma x (.sort one)) :
    HasTyT eqEnvT 2 Gamma (partialApp x) commonType := by
  have h0 := HasTyT.const (E := eqEnvT) (n := 2)
    Gamma 65 [two] eqRecT rfl rfl rfl
  have h1 := appTy h0 (.sort Gamma .zero)
  have h2 := appTy h1 (propParamTy Gamma)
  have h3 := appTy h2 (motiveTy Gamma)
  have h4 := appTy h3 (minorTy Gamma hx)
  have h5 : HasTyT eqEnvT 2 Gamma (partialApp x)
      (.pi domain (motiveAp propParam (.bvar 0))) :=
    appTy h4 (propParamTy Gamma)
  exact .conv Gamma _ _ commonType commonSort h5
    (.pi Gamma domain domain (motiveAp propParam (.bvar 0)) (.sort one)
      .zero two (.refl Gamma domain (.sort .zero) (domainTy Gamma))
      (motiveEval _ (propParamTy _) (.bvar _ 0 _ rfl)))

def commonTypeTy (Gamma : LCtx) :
    HasTyT eqEnvT 2 Gamma commonType (.sort commonSort) :=
  .pi Gamma domain .zero (.sort one) two (domainTy Gamma) (.sort _ one)

def movingMinorTy (Gamma : LCtx) :
    HasTyT eqEnvT 2 Gamma movingMinor (.sort one) :=
  appTy
    (.lam Gamma (.sort one) two (.bvar 0) (.sort one)
      (.sort Gamma one) (.bvar _ 0 _ rfl))
    (.sort Gamma .zero)

def movingMinorStep (Gamma : LCtx) :
    Step Gamma movingMinor (.sort .zero) (.sort one) :=
  .beta Gamma (.sort one) (.bvar 0) (.bvar 0)
    (.sort .zero) (.sort .zero) (.sort one) two two two
    (.sort Gamma one) (.sort _ one) (.sort Gamma one)
    (.refl _ (.bvar 0) (.sort one) (.bvar _ 0 _ rfl))
    (.refl Gamma (.sort .zero) (.sort one) (.sort Gamma .zero))
    (.sort Gamma .zero)

def movingMinorConv (Gamma : LCtx) :
    ConvT eqEnvT 2 Gamma movingMinor (.sort .zero) (.sort one) :=
  .beta Gamma (.sort one) (.bvar 0) (.sort .zero) (.sort one) two
    (.sort Gamma one) (.bvar _ 0 _ rfl) (.sort Gamma .zero)

/-- A literal valid field-free Eq witness. The minor remains exactly
lift x. No parallel predecessor is present in this record. -/
def witness (x : Expr Nat) : IotaWitness eqEnvT where
  recRef := 65
  ctorRef := 64
  ls := [two]
  lsC := []
  recMember := eqRecT
  ctorMember := eqReflT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.sort .zero, propParam, motive, lift 0 1 x, propParam]
  fields := []
  ctorParams := [.sort .zero, propParam]
  kinds := []
  minor := lift 0 1 x
  hlen := rfl
  familyRef := 63
  famMember := eqFamT
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort one, .bvar 0]
  ctorResult := foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort one, .bvar 0, eqMotT, eqMinorT, .bvar 3,
    foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := domain
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

def etaK (Gamma : LCtx) {x : Expr Nat}
    (hx : HasTyT eqEnvT 2 Gamma x (.sort one))
    (hxl : HasTyT eqEnvT 2 (.assumption domain :: Gamma)
      (lift 0 1 x) (.sort one)) :
    Step Gamma (partialApp x) (.lam domain (lift 0 1 x)) commonType :=
  .iotaStarKEta Gamma (witness x) (partialApp x) domain (.sort one)
    domain (lift 0 1 x) .zero .zero True
    rfl (domainTy Gamma) (partialTy Gamma hx) rfl
    (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ (.bvar _ 0 _ rfl) (ctorTy _) (domainTy _)
    (.ofU (witness x))
    (appTy (partialTy _ hxl) (ctorTy _))
    (appTy (partialTy _ hxl) (.bvar _ 0 _ rfl)) hxl

def etaBody : Step [.assumption (.sort one)]
    (partialApp (.bvar 0)) (.lam domain (.bvar 1)) commonType :=
  etaK _ (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl)

def rightTy (Gamma : LCtx) : HasTyT eqEnvT 2 Gamma rightEnd commonType :=
  .lam Gamma domain .zero (.sort .zero) (.sort one)
    (domainTy Gamma) (.sort _ .zero)

def leftBranch : Step [] parent leftEnd commonType :=
  .beta [] (.sort one) (partialApp (.bvar 0)) (partialApp (.bvar 0))
    movingMinor movingMinor commonType two commonSort commonSort
    (.sort [] one) (commonTypeTy _) (commonTypeTy [])
    (.refl _ _ commonType (partialTy _ (.bvar _ 0 _ rfl)))
    (.refl [] movingMinor (.sort one) (movingMinorTy []))
    (partialTy [] (movingMinorTy []))

def rightBranch : Step [] parent rightEnd commonType :=
  .beta [] (.sort one) (partialApp (.bvar 0)) (.lam domain (.bvar 1))
    movingMinor (.sort .zero) commonType two commonSort commonSort
    (.sort [] one) (commonTypeTy _) (commonTypeTy [])
    etaBody (movingMinorStep []) (rightTy [])

/-- The valid peak is NOT a counterexample to finite native valleys. -/
def leftToMiddle : Step [] leftEnd middle commonType :=
  etaK [] (movingMinorTy []) (movingMinorTy _)

def middleToRight : Step [] middle rightEnd commonType :=
  .lam [] domain domain movingMinor (.sort .zero) (.sort one) .zero two
    (.refl [] domain (.sort .zero) (domainTy []))
    (domainTy []) (.sort _ one) (movingMinorStep _) (rightTy [])

def residualValley : Star [] leftEnd rightEnd commonType :=
  .tail leftToMiddle (.tail middleToRight (.refl [] rightEnd commonType (rightTy [])))

/-- An original native certificate for this eta-K instance, constructed
directly from eta, application congruence, proof irrelevance, and legacy iota.
No generic ParRedT-to-ConvT back-lift or type uniqueness is used. -/
def etaKConv (Gamma : LCtx) {x : Expr Nat}
    (hx : HasTyT eqEnvT 2 Gamma x (.sort one))
    (hxl : HasTyT eqEnvT 2 (.assumption domain :: Gamma)
      (lift 0 1 x) (.sort one)) :
    ConvT eqEnvT 2 Gamma (partialApp x) (.lam domain (lift 0 1 x)) commonType := by
  let GammaI := .assumption domain :: Gamma
  have hf := partialTy GammaI hxl
  have hp : HasTyT eqEnvT 2 GammaI (.bvar 0) domain := .bvar _ 0 _ rfl
  have hmk := ctorTy GammaI
  have hmajor : ConvT eqEnvT 2 GammaI (.bvar 0) ctor domain :=
    .irr GammaI domain (.bvar 0) ctor (domainTy GammaI) hp hmk
  have happ : ConvT eqEnvT 2 GammaI
      (.app (lift 0 1 (partialApp x)) (.bvar 0))
      (iotaLhsOf (witness x)) (.sort one) :=
    .app GammaI _ _ (.bvar 0) ctor domain (.sort one)
      (.refl GammaI _ commonType hf) hmajor
  have hiota : ConvT eqEnvT 2 GammaI (iotaLhsOf (witness x))
      (lift 0 1 x) (.sort one) :=
    .iota GammaI _ _ (.sort one) (.of (witness x)) (appTy hf hmk) hxl
  have hbody := ConvT.trans GammaI _ _ _ (.sort one) happ hiota
  have hlam := ConvT.lam Gamma domain domain _ (lift 0 1 x) (.sort one)
    .zero (.refl Gamma domain (.sort .zero) (domainTy Gamma)) hbody
  exact .trans Gamma _ _ _ commonType
    (.symm Gamma _ _ commonType
      (.eta Gamma (partialApp x) domain (.sort one) (partialTy Gamma hx))) hlam

def leftCertificate : ConvT eqEnvT 2 [] parent leftEnd commonType :=
  .beta [] (.sort one) (partialApp (.bvar 0)) movingMinor commonType two
    (.sort [] one) (partialTy _ (.bvar _ 0 _ rfl)) (movingMinorTy [])

def rightCertificate : ConvT eqEnvT 2 [] parent rightEnd commonType := by
  have hb : ConvT eqEnvT 2 [.assumption (.sort one)]
      (partialApp (.bvar 0)) (.lam domain (.bvar 1)) commonType :=
    etaKConv _ (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl)
  have hf : ConvT eqEnvT 2 []
      (.lam (.sort one) (partialApp (.bvar 0)))
      (.lam (.sort one) (.lam domain (.bvar 1)))
      (.pi (.sort one) commonType) :=
    .lam [] (.sort one) (.sort one) _ _ commonType two
      (.refl [] (.sort one) (.sort two) (.sort [] one)) hb
  have happ := ConvT.app [] _ _ movingMinor (.sort .zero)
    (.sort one) commonType hf (movingMinorConv [])
  have hred := ConvT.beta [] (.sort one) (.lam domain (.bvar 1))
    (.sort .zero) commonType two (.sort [] one)
    (.lam _ domain .zero (.bvar 1) (.sort one)
      (domainTy _) (.bvar _ 1 _ rfl)) (.sort [] .zero)
  exact .trans [] _ _ _ commonType happ hred

/-! Exact hereditary receipts for the SAME Step values above. -/

def movingMinorGood (Gamma : LCtx) :
    NativeHereditaryPaths76.GoodStep (movingMinorStep Gamma) :=
  ⟨movingMinorConv Gamma,
    NativeHereditaryPaths76.goodRefl
      (show HasTyT eqEnvT 2 (.assumption (.sort one) :: Gamma)
        (.bvar 0) (.sort one) from
        .bvar (.assumption (.sort one) :: Gamma) 0 (.sort one) rfl),
    NativeHereditaryPaths76.goodRefl (.sort Gamma .zero)⟩

def etaBodyGood : NativeHereditaryPaths76.GoodStep etaBody :=
  ⟨etaKConv _ (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl), PUnit.unit⟩

def leftBranchGood : NativeHereditaryPaths76.GoodStep leftBranch :=
  ⟨leftCertificate,
    NativeHereditaryPaths76.goodRefl
      (partialTy (.assumption (.sort one) :: [])
        (.bvar _ 0 _ rfl)),
    NativeHereditaryPaths76.goodRefl (movingMinorTy [])⟩

def rightBranchGood : NativeHereditaryPaths76.GoodStep rightBranch :=
  ⟨rightCertificate, etaBodyGood, movingMinorGood []⟩

def leftToMiddleGood : NativeHereditaryPaths76.GoodStep leftToMiddle :=
  ⟨etaKConv [] (movingMinorTy []) (movingMinorTy _), PUnit.unit⟩

def middleToRightGood : NativeHereditaryPaths76.GoodStep middleToRight :=
  ⟨.lam [] domain domain movingMinor (.sort .zero) (.sort one) .zero
    (.refl [] domain (.sort .zero) (domainTy [])) (movingMinorConv _),
    movingMinorGood _⟩

def residualGoodPath :
    NativeHereditaryPaths76.GoodPath eqEnvT 2 [] commonType leftEnd rightEnd :=
  .tail leftToMiddle leftToMiddleGood
    (.tail middleToRight middleToRightGood (.refl (rightTy [])))

def residualGoodValley : NativeHereditaryPaths76.GoodValley
    (E := eqEnvT) (n := 2) [] leftEnd rightEnd commonType :=
  ⟨rightEnd, residualGoodPath, .refl (rightTy [])⟩

theorem endpoints_distinct : leftEnd ≠ rightEnd := by decide
theorem middle_distinct : middle ≠ rightEnd := by decide

end Rcic.Declarative.NativeMovingMinor76
