import rcic.RcicSynDispForPath

/-!
Concrete fixtures exercising every `DispForPath` step on small contexts, plus
mutants that a stale disposition would wrongly admit. Every step's source
endpoint is read from the stored child path, never re-derived by inversion.
These pins do not assert arbitrary-`AssumptionPrefix` coverage.
`closure_claim = 0`.
-/

namespace Rcic.Syn.DispForPathPins

open Rcic.Declarative

private def closed : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def stable : EnvMembersSubstStable emptyEnv :=
  envMembersSubstStable_of_envWfT EnvWfT.empty
private def levels : EnvLevelsT emptyEnv := envWfT_levels EnvWfT.empty
private def iotaLevels : IotaLevelsT emptyEnv := iotaLevelsT_of_envWfT EnvWfT.empty

def one : Level := .succ .zero
def two : Level := .succ one
def s0 : Expr Nat := .sort .zero
def s1 : Expr Nat := .sort one

def hs0 : TyP emptyEnv 0 [] s0 (.sort one) :=
  .sort emptyEnv 0 [] .zero one (eqN_refl _)
def hs1 : TyP emptyEnv 0 [] s1 (.sort two) :=
  .sort emptyEnv 0 [] one two (eqN_refl _)
def hs0s : TyP emptyEnv 0 [.assumption s1] s0 (.sort one) :=
  .sort emptyEnv 0 _ .zero one (eqN_refl _)
def hs1s : TyP emptyEnv 0 [.assumption s1] s1 (.sort two) :=
  .sort emptyEnv 0 _ one two (eqN_refl _)
def hs0a : TyP emptyEnv 0 [.assumption s0] s0 (.sort one) :=
  .sort emptyEnv 0 _ .zero one (eqN_refl _)

def C0 : CtxP emptyEnv 0 [] := .nil emptyEnv 0
def hC0 : DispForC id C0 [] := .nil levelSub_id

/-- `sort` is a rule leaf: its path retains only the endpoint's `DispForC`. -/
def p0 : DispForPathTy hs0 id [] C0 := .sort hC0
def p1 : DispForPathTy hs1 id [] C0 := .sort hC0

/-! ## `wk` -/

def wkSpine : CtxP emptyEnv 0 [.assumption s1] := .assumption emptyEnv 0 [] s1 two C0 hs1
def hCw : DispForC id wkSpine [.keep] := .assumption hs1 hC0
def wkTy : TyP emptyEnv 0 [.assumption s1] s0 (.sort one) :=
  .wk emptyEnv 0 [] s0 (.sort one) (.assumption s1) 0 hs0
def pWk : DispForPathTy wkTy id [.keep] wkSpine := .wk hCw closed p0

/-- The `wk` path's source endpoint is `removeAt ρ c`. -/
theorem pin_wk_source : removeAt [.keep] 0 = ([] : List Disp) := rfl

/-! ## `esub` -/

def bvarSrc : TyP emptyEnv 0 [.assumption s1] (.bvar 0) s1 :=
  .bvar emptyEnv 0 [.assumption s1] 0 s1 two rfl hs1s
def esubTy : TyP emptyEnv 0 [] s0 s1 :=
  .esub emptyEnv 0 [.assumption s1] (.bvar 0) s1 s1 s0 0 two bvarSrc rfl hs0 hs1
def hvN : HasTyT emptyEnv 0 [] s0 s1 := .sort [] .zero
def pBvarSrc : DispForPathTy bvarSrc id [.keep] wkSpine := .bvar hCw (.sort hCw)
def pEsub : DispForPathTy esubTy id [] C0 :=
  .esub hC0 closed stable hvN pBvarSrc p0 p1

/-- The `esub` path's source disposition inserts the removed slot's clause. -/
theorem pin_esub_source : insertDisp .keep 0 ([] : List Disp) = [.keep] := rfl

/-! ## `lsub` -/

def letSpine : CtxP emptyEnv 0 [.letBinding s1 s0] :=
  .letBinding emptyEnv 0 [] s1 two s0 C0 hs1 hs0
def hCl : DispForC id letSpine [.inline (.sort .zero)] := .letInline hs1 hs0 hC0
def bvarSrcL : TyP emptyEnv 0 [.letBinding s1 s0] (.bvar 0) s1 :=
  .bvar emptyEnv 0 [.letBinding s1 s0] 0 s1 two rfl
    (.sort emptyEnv 0 _ one two (eqN_refl _))
def lsubTy : TyP emptyEnv 0 [] s0 s1 :=
  .lsub emptyEnv 0 [.letBinding s1 s0] (.bvar 0) s1 s1 s0 0 two bvarSrcL rfl hs0 hs1
def pBvarSrcL : DispForPathTy bvarSrcL id [.inline (.sort .zero)] letSpine :=
  .bvar hCl (.sort hCl)
def pLsub : DispForPathTy lsubTy id [] C0 :=
  .lsub hC0 closed stable hvN pBvarSrcL p0 p1

/-! ## `linst` -/

def hs0L : TyP emptyEnv 1 [] s0 (.sort one) := .sort emptyEnv 1 [] .zero one (eqN_refl _)
def linstTy : TyP emptyEnv 0 [] s0 s1 :=
  .linst emptyEnv 1 0 [] s0 (.sort one) [.zero] rfl rfl hs0L
def pLinst : DispForPathTy linstTy id [] C0 :=
  .linst hC0 levels iotaLevels (.sort (.nil (levelSub_id.linst [.zero])))

/-! ## `ewk` -/

def ewkTy : TyP emptyEnv 0 [] s0 s1 := .ewk emptyEnv emptyEnv 0 [] s0 s1 (envExt_refl _) hs0
def pEwk : DispForPathTy ewkTy id [] C0 := .ewk hC0 p0

/-! ## `cctx` (typing side) -/

def s0Spine : CtxP emptyEnv 0 [.assumption s0] := .assumption emptyEnv 0 [] s0 one C0 hs0
def hCs0 : DispForC id s0Spine [.keep] := .assumption hs0 hC0
def cctxSrc : TyP emptyEnv 0 [.assumption s0] (.bvar 0) s0 :=
  .bvar emptyEnv 0 [.assumption s0] 0 s0 one rfl hs0a
def bridgeCv : CvP emptyEnv 0 [] s0 s0 (.sort one) :=
  .refl emptyEnv 0 [] s0 (.sort one) hs0 hs0 hs0
def pBridge : DispForPathCv bridgeCv id [] C0 := .refl hC0 p0 p0 p0
def cctxTy : TyP emptyEnv 0 [.assumption s0] (.bvar 0) s0 :=
  .cctx emptyEnv 0 [] (.bvar 0) s0 s0 s0 one cctxSrc bridgeCv
def pCctx : DispForPathTy cctxTy id [.keep] s0Spine :=
  .cctx hCs0 (.bvar hCs0 (.sort hCs0)) pBridge

/-! ## `cctx` (conversion side) and a `CvP` transport -/

def cctxCvSrc : CvP emptyEnv 0 [.assumption s0] (.bvar 0) (.bvar 0) s0 :=
  .refl emptyEnv 0 [.assumption s0] (.bvar 0) s0 cctxSrc cctxSrc cctxSrc
def cctxCv : CvP emptyEnv 0 [.assumption s0] (.bvar 0) (.bvar 0) s0 :=
  .cctx emptyEnv 0 [] (.bvar 0) (.bvar 0) s0 s0 s0 one cctxCvSrc bridgeCv
def pCctxCv : DispForPathCv cctxCv id [.keep] s0Spine :=
  .cctx hCs0 (.refl hCs0 (.bvar hCs0 (.sort hCs0)) (.bvar hCs0 (.sort hCs0))
    (.bvar hCs0 (.sort hCs0))) pBridge

def wkCv : CvP emptyEnv 0 [.assumption s1] s0 s0 s1 :=
  .wk emptyEnv 0 [] s0 s0 (.sort one) (.assumption s1) 0 bridgeCv
def pWkCv : DispForPathCv wkCv id [.keep] wkSpine := .wk hCw closed pBridge

/-! ## rule children: `pi`, `conv`, `letE` -/

def piTy : TyP emptyEnv 0 [] (.pi s0 s0) (.sort (.imax one one)) :=
  .pi emptyEnv 0 [] s0 one s0 one hs0 (.sort emptyEnv 0 _ .zero one (eqN_refl _))
def pPi : DispForPathTy piTy id [] C0 := .pi hC0 p0 (.sort (.assumption hs0 hC0))

def convTy : TyP emptyEnv 0 [] s0 s1 :=
  .conv emptyEnv 0 [] s0 s1 s1 two hs0 (.refl emptyEnv 0 [] s1 (.sort two) hs1 hs1 hs1)
def pConv : DispForPathTy convTy id [] C0 := .conv hC0 p0 (.refl hC0 p1 p1 p1)

def letBody : TyP emptyEnv 0 [.letBinding s1 s0] (.bvar 0) s1 := bvarSrcL
def letTy : TyP emptyEnv 0 [] (.letE s1 s0 (.bvar 0)) s1 :=
  .letE emptyEnv 0 [] s1 two s0 s1 (.bvar 0) two hs1 hs0 letBody
    (TyP.sort emptyEnv 0 [] one two (eqN_refl _))
def pLet : DispForPathTy letTy id [] C0 :=
  .letE hC0 p1 p0 (.bvar hCl (.sort hCl)) p1

/-! ## `refl` exact-child regression -/

/-- Three distinct derivations of `s0 : .sort one` (`hs0`, `ewkTy`, `convTy`)
    as the `h`/`dl`/`dr` children of a `refl`. With `pdl`/`pdr` indexed by
    `dl`/`dr`, each premise stores a path of its own child; an indexing that
    types all three by `h` does not elaborate here. -/
def reflMixed : CvP emptyEnv 0 [] s0 s0 (.sort one) :=
  .refl emptyEnv 0 [] s0 (.sort one) hs0 ewkTy convTy
def pReflMixed : DispForPathCv reflMixed id [] C0 :=
  .refl hC0 p0 pEwk pConv

/-! ## spine forest -/

def pSpineW : DispForPathSpine wkSpine id [.keep] := .assumption p1 .nil
def pSpineL : DispForPathSpine letSpine id [.inline (.sort .zero)] :=
  .letBinding p1 p0 .nil

/-! ## retained validity is readable back -/

theorem pin_hC_wk : pWk.hC = hCw := rfl
theorem pin_hC_esub : pEsub.hC = hC0 := rfl
theorem pin_hC_cctx : pCctx.hC = hCs0 := rfl
theorem pin_toDispFor_ewk : DispFor id emptyEnv 0 [] ([] : List Disp) := pEwk.toDispFor

/-! ## mutants: a stale disposition is refused by the retained `DispForC` -/

/-- `levelIsZero (id two) = false`, so the `.assumption s1` head must be `.keep`;
    `.drop` has no `DispForC` and hence admits no path. -/
theorem pin_drop_rejected : ¬ DispForC id wkSpine [.drop] := by
  intro h
  cases h

/-- A `.letBinding` head is never `.keep`: the let clause is `.drop` or
    `.inline`, so a `.keep` disposition admits no `DispForC`. -/
theorem pin_let_keep_rejected : ¬ DispForC id letSpine [.keep] := by
  intro h
  cases h

/-- The empty context carries only the empty disposition. -/
theorem pin_nil_nonempty_rejected : ¬ DispForC id C0 [.keep] := by
  intro h
  cases h

end Rcic.Syn.DispForPathPins
