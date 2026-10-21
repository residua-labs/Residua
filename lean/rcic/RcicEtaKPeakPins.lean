import rcic.RcicPinEqIotaStarK
import rcic.RcicKGateNoGo
import rcic.RcicTypedLevels
import rcic.RcicPEqLeafTProp
set_option maxRecDepth 8192
/-!
A-2: real eta/lam-iotaStarK peaks at Eq refs 63/64/65.
Concrete positive universe 1 and a separate Prop-motive control, both at n=2.
The Prop control joins; positive non-joinability remains an open residual.
No ParRedT rule is changed. closure_claim = 0.
-/

namespace Rcic.Declarative.F8EtaK

def ctx (u : Level) : LCtx := instLvlsCtx [u] eqJoinCtx.tail
def domain : Expr Nat := eqPTy
def codomain : Expr Nat := eqMotAp
def partialRec (u : Level) : Expr Nat :=
  instantiateLevels [u] (foldApps (.const 65 [.param 0])
    [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2])
def expanded (u : Level) : Expr Nat :=
  .lam domain (.app (lift 0 1 (partialRec u)) (.bvar 0))
def contracted : Expr Nat := .lam domain (.bvar 1)
def commonIndex : Expr Nat := .pi domain codomain

private def el : EnvLevelsT eqEnvT := envWfT_levels pinEqGroupWfT
private def il : IotaLevelsT eqEnvT := iotaLevelsT_of_envWfT pinEqGroupWfT
private def instTy (u : Level) (hu : levelsBounded 2 [u] = true)
    {Γ : LCtx} {e T : Expr Nat} (h : HasTyT eqEnvT 1 Γ e T) :
    HasTyT eqEnvT 2 (instLvlsCtx [u] Γ)
      (instantiateLevels [u] e) (instantiateLevels [u] T) :=
  hasTyT_instLevels el il hu rfl h
private def instCv (u : Level) (hu : levelsBounded 2 [u] = true)
    {Γ : LCtx} {e e' T : Expr Nat} (h : ConvT eqEnvT 1 Γ e e' T) :
    ConvT eqEnvT 2 (instLvlsCtx [u] Γ)
      (instantiateLevels [u] e) (instantiateLevels [u] e') (instantiateLevels [u] T) :=
  convT_instLevels el il hu rfl h

private def baseAlpha : HasTyT eqEnvT 1 eqJoinCtx.tail (.bvar 3) (.sort (.succ .zero)) :=
  .bvar _ 3 _ rfl
private def baseA : HasTyT eqEnvT 1 eqJoinCtx.tail (.bvar 2) (.bvar 3) :=
  .bvar _ 2 _ rfl
private def baseM : HasTyT eqEnvT 1 eqJoinCtx.tail (.bvar 1) (lift 0 2 eqMotT) :=
  .bvar _ 1 _ rfl
private def baseMinor : HasTyT eqEnvT 1 eqJoinCtx.tail (.bvar 0) (lift 0 1 eqMinorT) :=
  .bvar _ 0 _ rfl
private def baseRec : HasTyT eqEnvT 1 eqJoinCtx.tail
    (foldApps (.const 65 [.param 0]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2])
    commonIndex :=
  let h0 := HasTyT.const (E := eqEnvT) (n := 1) eqJoinCtx.tail 65 [.param 0] eqRecT rfl rfl rfl
  let h1 := HasTyT.app _ _ _ _ _ h0 baseAlpha
  let h2 := HasTyT.app _ _ _ _ _ h1 baseA
  let h3 := HasTyT.app _ _ _ _ _ h2 baseM
  let h4 := HasTyT.app _ _ _ _ _ h3 baseMinor
  HasTyT.app _ _ _ _ _ h4 baseA

private def baseBody : HasTyT eqEnvT 1 eqJoinCtx
    (.app eqRecFive (.bvar 0)) codomain :=
  .app _ _ _ _ _ eqRecTy5 pinEqGate_met
private def baseCodTy : HasTyT eqEnvT 1 eqJoinCtx codomain (.sort (.param 0)) :=
  .app _ _ _ _ _ eqMaTy pinEqGate_met

/-- The admitted Eq environment is unchanged. -/
def envWf : EnvWfT eqEnvT := pinEqGroupWfT

/-- The context itself is certified, including the motive and minor slots. -/
def contextWf (u : Level) (hu : levelsBounded 2 [u] = true) :
    CtxWfT eqEnvT 2 (ctx u) :=
  .assumption _ _ _
    (.assumption _ _ _
      (.assumption _ _ _
        (.assumption [] (.sort (.succ .zero)) (.succ (.succ .zero))
          .nil (.sort [] (.succ .zero)))
        (instTy u hu Rcic.kgATy))
      (instTy u hu Rcic.kgMotTy))
    (instTy u hu Rcic.kgMinorTy)

def domainTy (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (ctx u) domain (.sort .zero) := instTy u hu Rcic.kgPTyTy

def codomainTy (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (.assumption domain :: ctx u) codomain (.sort u) :=
  instTy u hu baseCodTy

def partialRecTy (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (ctx u) (partialRec u) commonIndex := instTy u hu baseRec

private def bodyTy (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (.assumption domain :: ctx u)
      (.app (lift 0 1 (partialRec u)) (.bvar 0)) codomain := instTy u hu baseBody

private def atP (u : Level) (hu : levelsBounded 2 [u] = true)
    {e : Expr Nat} (h : HasTyT eqEnvT 1 eqJoinCtx e eqEqLhs) :
    HasTyT eqEnvT 2 (.assumption domain :: ctx u)
      (instantiateLevels [u] e) codomain :=
  .conv _ _ _ _ u (instTy u hu h) (.symm _ _ _ _ (instCv u hu eqTyX))

def witness (u : Level) : IotaWitness eqEnvT :=
  lvlsWitness [u] eqKWitness (by decide)

/-- The actual bound-major K step, including both type-index exchanges. -/
def bodyK (u : Level) (hu : levelsBounded 2 [u] = true) :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (.assumption domain :: ctx u)
      (.app (lift 0 1 (partialRec u)) (.bvar 0)) (.bvar 1) codomain :=
  .iotaStarK _ (witness u) (.bvar 0) eqPTyAt0 (.bvar 1) codomain .zero True
    rfl (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ (instTy u hu pinEqGate_met) (instTy u hu eqReflTy2)
    (instTy u hu eqFamTy3) (.ofU (witness u))
    (atP u hu eqRecLhsTy) (bodyTy u hu) (atP u hu eqTym)

def expandedTy (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (ctx u) (expanded u) commonIndex :=
  .lam _ domain .zero _ codomain (domainTy u hu) (bodyTy u hu)

def contractedTy (u : Level) (hu : levelsBounded 2 [u] = true) :
    HasTyT eqEnvT 2 (ctx u) contracted commonIndex :=
  .lam _ domain .zero (.bvar 1) codomain (domainTy u hu) (atP u hu eqTym)

def etaBranch (u : Level) (hu : levelsBounded 2 [u] = true) :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx u)
      (expanded u) (partialRec u) commonIndex :=
  .eta _ (partialRec u) (partialRec u) domain codomain
    (.refl _ _ _ (partialRecTy u hu)) (expandedTy u hu)

def kBranch (u : Level) (hu : levelsBounded 2 [u] = true) :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx u)
      (expanded u) contracted commonIndex :=
  .lam _ domain domain _ (.bvar 1) codomain .zero u
    (.refl _ domain (.sort .zero) (domainTy u hu))
    (domainTy u hu) (codomainTy u hu) (bodyK u hu) (contractedTy u hu)

theorem positive_levels : levelsBounded 2 [.succ .zero] = true := by decide
theorem prop_levels : levelsBounded 2 [.zero] = true := by decide

def positive_peak :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx (.succ .zero))
      (expanded (.succ .zero)) (partialRec (.succ .zero)) commonIndex ×'
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx (.succ .zero))
      (expanded (.succ .zero)) contracted commonIndex :=
  ⟨etaBranch _ positive_levels, kBranch _ positive_levels⟩

def positive_index_sort : HasTyT eqEnvT 2 (ctx (.succ .zero)) commonIndex
    (.sort (.imax .zero (.succ .zero))) :=
  .pi _ domain .zero codomain (.succ .zero)
    (domainTy _ positive_levels) (codomainTy _ positive_levels)

theorem positive_sort_value (ρ : Nat → Option Nat) :
    eval ρ (.imax .zero (.succ .zero)) = some 1 := rfl

def prop_peak :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx .zero)
      (expanded .zero) (partialRec .zero) commonIndex ×'
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx .zero)
      (expanded .zero) contracted commonIndex :=
  ⟨etaBranch _ prop_levels, kBranch _ prop_levels⟩

def prop_index_sort : HasTyT eqEnvT 2 (ctx .zero) commonIndex (.sort .zero) :=
  .conv _ commonIndex (.sort (.imax .zero .zero)) (.sort .zero)
    (.succ (.imax .zero .zero))
    (.pi _ domain .zero codomain .zero (domainTy _ prop_levels) (codomainTy _ prop_levels))
    (.sorts _ (.imax .zero .zero) .zero (fun _ => rfl))

/-- Prop control: this real peak DOES join by the existing proof sector. -/
def prop_peak_joined :
    ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx .zero)
      (partialRec .zero) contracted commonIndex ×'
      (ParRedT (PEqLeafT eqEnvT 2) eqEnvT 2 (ctx .zero)
        contracted contracted commonIndex ×'
        ConvT eqEnvT 2 (ctx .zero) (partialRec .zero) contracted commonIndex) :=
  parRedT_propIndex_diamond_data prop_index_sort (.refl _ commonIndex)
    prop_peak.1 prop_peak.2

/-- No non-joinability theorem is asserted for positive_peak. -/
theorem positive_endpoints_differ : partialRec (.succ .zero) ≠ contracted := by
  intro h
  cases h

end Rcic.Declarative.F8EtaK
