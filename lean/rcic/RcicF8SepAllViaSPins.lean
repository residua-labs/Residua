import rcic.RcicF8XStructViaS
import rcic.RcicF8XValleyViaS
import rcic.RcicF8SepAllPins

namespace Rcic.Declarative.F8Measure.SepAllViaSPins
open F8SepAllPins
open Rcic.Syn
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def sep : SepAllViaS emptyEnv 0 :=
  sepAllViaS_of_sortUnique EnvWfT.empty (emptyEnv_sortUnique 0)
def K : ∀ R : List (Jd emptyEnv 0), CtxConvProc R :=
  fun _ {_ _ _ _ _} c e => ctxConvVar c e
theorem hK : CtxConvContract K := fun _ {_ _ _ _ _} c e => ctxConvVar_contract c e

def P : Expr Nat := .pi (.bvar 1) (.bvar 2)
def root : Jd emptyEnv 0 := .ty depthHv
def roots : List (Jd emptyEnv 0) := [root]
def hv : EvTy roots depthTarget (.sort .zero) (.sort (.succ .zero)) :=
  .lit depthHv ⟨root, .head _, .inl rfl⟩
def base : EvTc roots depthCtx P P := .refl _ _
def wkInput := EvTc.wk twoDecl 1 base
def wkWitness : CtxWfViaS emptyEnv 0 (insertAt twoDecl 1 depthCtx) :=
  .sub (v := .sort .zero) 2 rfl (.sort _ _) (.ofWf twoTargetWf)
def wkOut := xStructTcViaS EnvWfT.empty K hK sep wkWitness wkInput rfl rfl rfl

theorem wk_components : wkOut =
    (EvTc.wk twoDecl 1 (.refl depthCtx (.bvar 1)),
     EvTc.wk twoDecl 2 (.refl (.assumption (.bvar 1) :: depthCtx) (.bvar 2))) := by
  simp [wkOut, wkInput, base, P, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

def subInput := EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 1 base (by rfl) hv
def subOut := xStructTcViaS EnvWfT.empty K hK sep (.ofWf depthTargetWf)
  subInput rfl rfl rfl

theorem sub_components : subOut =
    (EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 1 (.refl depthCtx (.bvar 1)) (by rfl) hv,
     EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 2 (.refl (.assumption (.bvar 1) :: depthCtx) (.bvar 2))
       (by rfl) (substBinderArg (y := .sort (.succ .zero)) (v := .sort .zero) (d := .assumption (.bvar 1)) hv)) := by
  simp [subOut, subInput, base, P, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

theorem sub_leaves : XOut.leaves subOut = [root, root] := by
  simp [subOut, subInput, base, P, hv, roots, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

def letCtx : LCtx := [.assumption (.bvar 0),
  .letBinding (.sort (.succ .zero)) (.sort .zero)]
def letInput : EvTc roots depthTarget
    (instantiate 1 (.sort .zero) P) (instantiate 1 (.sort .zero) P) :=
  .substLet 1 (.refl letCtx P) rfl hv
def letOut := xStructTcViaS EnvWfT.empty K hK sep (.ofWf depthTargetWf)
  letInput rfl rfl rfl

theorem let_components : letOut =
    (EvTc.substLet 1 (.refl letCtx (.bvar 1)) (by rfl) hv,
     EvTc.substLet 2 (.refl (.assumption (.bvar 1) :: letCtx) (.bvar 2))
       (by rfl) (substBinderArg (y := .sort (.succ .zero)) (v := .sort .zero) (d := .assumption (.bvar 1)) hv)) := by
  simp [letOut, letInput, P, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

theorem let_leaves : XOut.leaves letOut = [root, root] := by
  simp [letOut, letInput, P, hv, roots, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

def mixedInput := EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 2 wkInput (by rfl)
  (EvTy.sort (R := roots) .zero)
def mixedOut := xStructTcViaS EnvWfT.empty K hK sep (.ofWf twoTargetWf)
  mixedInput rfl rfl rfl

theorem mixed_source_witness :
    (XCtxKit.viaS (R := roots) EnvWfT.empty sep).ins twoDecl 1
      ((XCtxKit.viaS (R := roots) EnvWfT.empty sep).sub (Γ := insertAt twoDecl 1 depthCtx) (v := .sort .zero) 2 rfl (.sort .zero)
        (.ofWf twoTargetWf)) = twoViaS := rfl

theorem mixed_components : mixedOut =
    (EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 2
       (EvTc.wk twoDecl 1 (.refl depthCtx (.bvar 1))) (by rfl) (.sort .zero),
     EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 3
       (EvTc.wk twoDecl 2 (.refl (.assumption (.bvar 1) :: depthCtx) (.bvar 2)))
       (by rfl) (substBinderArg (y := .sort (.succ .zero)) (v := .sort .zero)
         (d := .assumption (.bvar 2)) (.sort .zero))) := by
  simp [mixedOut, mixedInput, wkInput, base, P, xStructTcViaS, xTcWithCtx,
    xTcReady, isPiD, EvTc.cast]

theorem mixed_leaves : XOut.leaves mixedOut = [] := by
  simp [mixedOut, mixedInput, wkInput, base, P, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

def typedPi (Γ : LCtx) : HasTyT emptyEnv 0 Γ
    (.pi (.sort .zero) (.sort .zero)) (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ _ _ _ _ (.sort _ _) (.sort _ _)
def cvRoots : List (Jd emptyEnv 0) := [.ty (typedPi depthCtx), root]
def cvBase : EvCv cvRoots depthCtx (.pi (.sort .zero) (.sort .zero))
    (.pi (.sort .zero) (.sort .zero)) (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .refl (.lit (typedPi depthCtx) ⟨_, .head _, .inl rfl⟩)
def cvHv : EvTy cvRoots depthTarget (.sort .zero) (.sort (.succ .zero)) :=
  .lit depthHv ⟨root, .tail _ (.head _), .inl rfl⟩
def esubInput := EvTc.ofCv (.imax (.succ .zero) (.succ .zero))
  (EvCv.esub (v := .sort .zero) 1 (.succ (.succ .zero)) cvBase rfl cvHv
    (.sort (.succ .zero)))
def esubOut := xStructTcViaS EnvWfT.empty K hK sep (.ofWf depthTargetWf)
  esubInput rfl rfl rfl

theorem esub_components : esubOut =
    (EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 1 (.refl depthCtx (.sort .zero)) (by rfl) cvHv,
     EvTc.subst0 (t := .sort (.succ .zero)) (v := .sort .zero) 2 (.refl (.assumption (.sort .zero) :: depthCtx) (.sort .zero))
       (by rfl) (substBinderArg (y := .sort (.succ .zero)) (v := .sort .zero) (d := .assumption (.sort .zero)) cvHv)) := by
  simp [esubOut, esubInput, cvBase, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

theorem esub_leaves : XOut.leaves esubOut = [root, root] := by
  simp [esubOut, esubInput, cvBase, cvHv, cvRoots, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

def cvWkInput := EvTc.ofCv (.imax (.succ .zero) (.succ .zero))
  (EvCv.wk twoDecl 1 cvBase)
def cvWkOut := xStructTcViaS EnvWfT.empty K hK sep wkWitness cvWkInput rfl rfl rfl

theorem cvWk_components : cvWkOut =
    (EvTc.wk twoDecl 1 (.refl depthCtx (.sort .zero)),
     EvTc.wk twoDecl 2 (.refl (.assumption (.sort .zero) :: depthCtx) (.sort .zero))) := by
  simp [cvWkOut, cvWkInput, cvBase, xStructTcViaS, xTcWithCtx, xTcReady, xCvReady, isPiD, XOut.leaves, EvTc.leaves, EvTc.cast_leaves, substBinderArg_leaves, EvTc.cast, EvTy.leaves, root]

-- Exact output bounds, not only endpoint well-typedness.
theorem transport_bounds :
    (∀ ℓ ∈ XOut.leaves subOut, ∃ ℓ' ∈ subInput.leaves, SubEq ℓ ℓ') ∧
    (∀ ℓ ∈ XOut.leaves letOut, ∃ ℓ' ∈ letInput.leaves, SubEq ℓ ℓ') ∧
    (∀ ℓ ∈ XOut.leaves esubOut, ∃ ℓ' ∈ esubInput.leaves, SubEq ℓ ℓ') ∧
    (∀ ℓ ∈ XOut.leaves mixedOut, ∃ ℓ' ∈ mixedInput.leaves, SubEq ℓ ℓ') :=
  ⟨xStructTcViaS_leaves _ _ _ _ _ _ _ _ _,
   xStructTcViaS_leaves _ _ _ _ _ _ _ _ _,
   xStructTcViaS_leaves _ _ _ _ _ _ _ _ _,
   xStructTcViaS_leaves _ _ _ _ _ _ _ _ _⟩

def binderWitness : CtxWfViaS emptyEnv 0 (.assumption (.sort .zero) :: depthCtx) :=
  depthViaS.ext (envClosed_of_envWfT EnvWfT.empty) (envMembersSubstStable_of_envWfT EnvWfT.empty) (.sort _ _)
theorem binder_shift : binderWitness.σ.apply (.bvar 2) = .sort .zero := rfl

theorem ill_domain_tooth : ¬ Nonempty (CtxWfViaS emptyEnv 0 XTileQ1.illCtx) :=
  illCtx_no_viaS
theorem ill_mutantU_accepts : Nonempty (CtxWfViaSMutU emptyEnv 0 XTileQ1.illCtx) :=
  mutantU_accepts_illCtx
theorem ill_mutantW_accepts : Nonempty (CtxWfViaSMutW emptyEnv 0 XTileQ1.illCtx) :=
  mutantW_accepts_illCtx

def badBinder : Expr Nat := .const 0 []
theorem bad_binder_refused :
    ¬ Nonempty (CtxWfViaS emptyEnv 0 [.assumption badBinder]) := by
  rintro ⟨v⟩
  exact const0_stack_refuted v.σ ⟨[], [], rfl⟩ v.wf

theorem bad_binder_untyped (u : Level) :
    ¬ Nonempty (HasTyT emptyEnv 0 [] badBinder (.sort u)) := by
  rintro ⟨h⟩
  exact bad_binder_refused ⟨(CtxWfViaS.ofWf CtxWfT.nil).ext
    (envClosed_of_envWfT EnvWfT.empty) (envMembersSubstStable_of_envWfT EnvWfT.empty) h⟩

def UntypedBinderAdmission (Γ : LCtx) : Prop :=
  ∃ A, Γ = [.assumption A] ∧ Nonempty (CtxWfViaS emptyEnv 0 [])
theorem mutant_binder_accepts : UntypedBinderAdmission [.assumption badBinder] :=
  ⟨badBinder, rfl, ⟨.ofWf .nil⟩⟩

end Rcic.Declarative.F8Measure.SepAllViaSPins

#print axioms Rcic.Declarative.F8Measure.XCtxKit
#print axioms Rcic.Declarative.F8Measure.XCtxKit.universal
#print axioms Rcic.Declarative.F8Measure.XConvReady
#print axioms Rcic.Declarative.F8Measure.XTReady
#print axioms Rcic.Declarative.F8Measure.XTcReady
#print axioms Rcic.Declarative.F8Measure.XCvReady
#print axioms Rcic.Declarative.F8Measure.XConvReady.ofCtx
#print axioms Rcic.Declarative.F8Measure.XTReady.ofCtx
#print axioms Rcic.Declarative.F8Measure.XTcReady.ofCtx
#print axioms Rcic.Declarative.F8Measure.XCvReady.ofCtx
#print axioms Rcic.Declarative.F8Measure.xConvReady
#print axioms Rcic.Declarative.F8Measure.xTReady
#print axioms Rcic.Declarative.F8Measure.xTcReady
#print axioms Rcic.Declarative.F8Measure.xCvReady
#print axioms Rcic.Declarative.F8Measure.xConvWithCtx
#print axioms Rcic.Declarative.F8Measure.xTWithCtx
#print axioms Rcic.Declarative.F8Measure.xTcWithCtx
#print axioms Rcic.Declarative.F8Measure.xCvWithCtx
#print axioms Rcic.Declarative.F8Measure.SepAllViaS
#print axioms Rcic.Declarative.F8Measure.sepAllViaS_of_sortUnique
#print axioms Rcic.Declarative.F8Measure.XCtxKit.viaS
#print axioms Rcic.Declarative.F8Measure.xStructTcViaS
#print axioms Rcic.Declarative.F8Measure.xStructTcViaS_leaves
#print axioms Rcic.Declarative.F8Measure.xStructTcViaS_eq
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.sep
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.K
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.hK
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.P
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.root
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.roots
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.hv
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.base
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.wkInput
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.wkWitness
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.wkOut
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.wk_components
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.subInput
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.subOut
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.sub_components
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.sub_leaves
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.letCtx
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.letInput
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.letOut
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.let_components
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.let_leaves
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.mixedInput
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.mixedOut
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.mixed_source_witness
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.mixed_components
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.mixed_leaves
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.typedPi
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.cvRoots
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.cvBase
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.cvHv
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.esubInput
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.esubOut
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.esub_components
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.esub_leaves
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.cvWkInput
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.cvWkOut
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.cvWk_components
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.transport_bounds
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.binderWitness
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.binder_shift
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.ill_domain_tooth
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.ill_mutantU_accepts
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.ill_mutantW_accepts
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.badBinder
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.bad_binder_refused
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.bad_binder_untyped
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.UntypedBinderAdmission
#print axioms Rcic.Declarative.F8Measure.SepAllViaSPins.mutant_binder_accepts

namespace Rcic.Declarative.F8Measure.SepAllViaSPins
open Rcic.Syn F8SepAllPins

def closedBundle : SuppliersViaS emptyEnv 0 := .declining sep

theorem closed_separation (v : CtxWfViaS emptyEnv 0 Γ)
    (hp : HasTyT emptyEnv 0 Γ P (.sort .zero))
    (hc : TyConvT emptyEnv 0 Γ (.sort l) P) : False := closedBundle.hsep v hp hc

theorem roundtrip (X : SuppliersVia E n) : X.toS.toViaWithSep X.hsep = X :=
  SuppliersVia.toS_toViaWithSep X

-- This supplier accepts actual reflexive forks, with the original leaf bound.
def sentinelD : ∀ R : List (Jd emptyEnv 0), DProcViaSP R :=
  fun _ {_ _ _ _ _} _ h₁ h₂ => match h₁, h₂ with
    | .refl h, .refl h' => some ⟨_, .refl h, .refl h'⟩
    | _, _ => none

theorem sentinelD_contract : DContractViaSP sentinelD := by
  intro R Γ a b c T v h₁ h₂ r hr
  cases h₁ <;> try { simp [sentinelD] at hr }
  cases h₂ <;> simp [sentinelD] at hr
  cases hr
  exact fun ℓ h => ⟨ℓ, h, .inl rfl⟩

def sentinel : SuppliersViaS emptyEnv 0 :=
  { closedBundle with D := sentinelD, hD := sentinelD_contract }
def offStar : EvParStar ([] : List (Jd emptyEnv 0)) depthTarget
    (.sort .zero) (.sort .zero) (.sort (.succ .zero)) := .refl (.sort .zero)

theorem guard_refuses :
    (sentinel.core.atOps (.ofWf CtxWfT.nil)).D [] offStar offStar = none :=
  SuppliersViaS.atOps_D_ne _ _ (by decide) _ _

def mutantNoGuard : Option (Σ' d : Expr Nat,
    EvParStar ([] : List (Jd emptyEnv 0)) depthTarget (.sort .zero) d (.sort (.succ .zero)) ×
    EvParStar ([] : List (Jd emptyEnv 0)) depthTarget (.sort .zero) d (.sort (.succ .zero))) :=
  sentinel.D [] (.ofWf depthTargetWf) offStar offStar

theorem mutant_guard_accepts : mutantNoGuard = some ⟨.sort .zero, offStar, offStar⟩ := rfl

theorem helper_specializations (X : Suppliers E n) :
    (@sjoin E n R Γ X = @ValleyOps.sjoin E n R Γ X.toValleyOps) ∧
    (@scombine E n R Γ X = @ValleyOps.scombine E n R Γ X.toValleyOps) ∧
    (@readStarC E n R X = @ValleyOps.readStarC E n R X.toValleyOps) ∧
    (@readValleyC E n R Γ X = @ValleyOps.readValleyC E n R Γ X.toValleyOps) ∧
    (@sread E n R Γ X = @ValleyOps.sread E n R Γ X.toValleyOps) ∧
    (@SegOut.comp E n R Γ X = @ValleyOps.comp E n R Γ X.toValleyOps) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
end Rcic.Declarative.F8Measure.SepAllViaSPins

namespace Rcic.Declarative.F8Measure.SepAllViaSPins
open Rcic.Syn

def controlTy : HasTyT emptyEnv 0 [] piX sX := pinPiT emptyEnv 0
def controlCv : ConvT emptyEnv 0 [] piX piX sX := .refl [] piX sX controlTy
def controlRoots : List (Jd emptyEnv 0) := [.cv controlCv]
def controlCert : ∃ r ∈ controlRoots, SubEq (.cv controlCv) r :=
  ⟨.cv controlCv, .head _, .inl rfl⟩
def controlInput : EvCv controlRoots [] piX piX sX :=
  .trans (.lit controlCv controlCert) (.lit controlCv controlCert)
-- These fixtures answer only equal-index U and reflexive-left/equal-endpoint D.
-- They make no totality claim and leave the production suppliers unchanged.
def controlU : ∀ R : List (Jd emptyEnv 0), UProcP R := by
  intro R Γ e T₁ T₂ _ _
  exact if h : T₁ = T₂ then some (h ▸ EvTc.refl Γ T₁) else none

theorem controlU_contract : UContractP controlU := by
  intro R Γ e T₁ T₂ h₁ h₂ u hu
  unfold controlU at hu
  split at hu
  · rename_i he
    subst T₂
    cases hu
    intro ℓ hℓ
    simp [EvTc.leaves] at hℓ
  · contradiction

def controlD : ∀ R : List (Jd emptyEnv 0), DProcViaSP R := by
  intro R Γ a b c T _ h₁ _
  cases h₁ with
  | refl h =>
      exact if he : c = a then by subst c; exact some ⟨a, .refl h, .refl h⟩ else none
  | tail => exact none
  | conv => exact none
  | wk => exact none
  | trans => exact none
  | subst0 => exact none
  | substLet => exact none

theorem controlD_contract : DContractViaSP controlD := by
  intro R Γ a b c T v h₁ h₂ r hr
  cases h₁ <;> try { simp [controlD] at hr }
  simp only [controlD] at hr
  split at hr
  · rename_i he
    subst c
    cases hr
    intro ℓ hℓ
    simp only [EvParStar.leaves, List.mem_append] at hℓ
    rcases hℓ with hℓ | hℓ <;> exact ⟨ℓ, List.mem_append.mpr (.inl hℓ), .inl rfl⟩
  · contradiction

def executingBundle : SuppliersViaS emptyEnv 0 :=
  { closedBundle with
    J := j1ViaS EnvWfT.empty
    hJ := j1ViaS_contract EnvWfT.empty
    U := controlU
    hU := controlU_contract
    D := controlD
    hD := controlD_contract }

def controlRun := SepAllViaS.svalleyCvViaS EnvWfT.empty executingBundle controlInput (.id [])
  (.ofWf CtxWfT.nil) rfl
-- This is an actual public subworker execution, not an outer Stratum-B availability claim.
theorem control_executes : controlRun.isSome = true := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [controlRun, SepAllViaS.svalleyCvViaS, ViaSEngine.svalleyCvViaS, controlInput,
    executingBundle, SuppliersViaS.core, SuppliersViaS.atOps,
    ValleyOps.scombine, ValleyOps.sjoin, controlU, controlD, j1ViaS,
    J1.dispatchViaS, J1.reflResult, J1.reflValley, J1.reflEndpoint,
    controlCv, controlTy, controlRoots, reduceAnd,
    Valley.admitSubst, Valley.hasSubst, EvParStar.hasSubst,
    Valley.thinDeep, EvParStar.thinDeep, EvTy.thin, Wk.map, Valley.conv, EvTy.leaves, EvParStar.leaves, EvTc.leaves]

def controlEndpoint : EvTy controlRoots [] piX sX :=
  J1.reflEndpoint controlTy controlCert

def controlCalls : List (List (Jd emptyEnv 0)) :=
  [[.ty controlTy, .ty controlTy], [.ty controlTy, .ty controlTy]]

def controlExpected : SOut controlRoots [] piX piX sX :=
  ⟨.val ⟨piX,
    .trans (.refl controlEndpoint) (.refl controlEndpoint),
    .trans (.conv (.refl controlEndpoint) (.symm (.refl [] sX))) (.refl controlEndpoint),
    controlEndpoint, controlEndpoint.rety (.symm (.refl [] sX))⟩ (.refl [] sX),
    controlCalls, [.cv controlCv, .cv controlCv]⟩

theorem control_sout : controlRun.map (fun r => r.1) = some controlExpected := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [controlExpected, controlEndpoint, controlCalls, controlRun, SepAllViaS.svalleyCvViaS, ViaSEngine.svalleyCvViaS, controlInput,
    executingBundle, SuppliersViaS.core, SuppliersViaS.atOps,
    ValleyOps.scombine, ValleyOps.sjoin, controlU, controlD, j1ViaS,
    J1.dispatchViaS, J1.reflResult, J1.reflValley, J1.reflEndpoint,
    controlCv, controlTy, controlRoots, reduceAnd,
    Valley.admitSubst, Valley.hasSubst, EvParStar.hasSubst,
    Valley.thinDeep, EvParStar.thinDeep, EvTy.thin, Wk.map, Valley.conv, EvTy.leaves, EvParStar.leaves, EvTc.leaves]

def controlReadRun := controlRun.bind (fun r =>
  ValleyOps.sread (executingBundle.core.atOps (.ofWf CtxWfT.nil)) r.1 r.2 rfl rfl)

def controlPartA : EvTc controlRoots [] (.sort .zero) (.sort .zero) :=
  .trans (.refl _ _) (.refl _ _)
def controlPartB : EvTc controlRoots [.assumption (.sort .zero)] (.sort .zero) (.sort .zero) :=
  .trans (.refl _ _) (closedBundle.K controlRoots (.refl _ (.sort .zero)) (.refl _ _))
def controlComponents : XOut controlRoots [] (.sort .zero) (.sort .zero) (.sort .zero) (.sort .zero) :=
  (.trans controlPartA (.symm controlPartA),
   .trans controlPartB (closedBundle.K controlRoots
     (.trans controlPartA (.symm controlPartA)) (.symm controlPartB)))

theorem control_read_data : controlReadRun.map (fun r => (r.1, r.2.1, r.2.2.1)) =
    some (controlComponents, controlCalls, [.cv controlCv, .cv controlCv]) := by
  obtain ⟨r, hr, he⟩ := Option.map_eq_some'.mp control_sout
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp only [controlReadRun, hr, Option.bind_some]
  rcases r with ⟨o, ho⟩
  dsimp at he
  subst o
  simp [ValleyOps.sread, controlExpected, ValleyOps.readValleyC,
    ValleyOps.readStarC, controlComponents, controlPartA, controlPartB,
    executingBundle, SuppliersViaS.core, SuppliersViaS.atOps, reduceAnd]

def noneJBundle : SuppliersViaS emptyEnv 0 :=
  { executingBundle with J := closedBundle.J, hJ := closedBundle.hJ }
def noneJRun := SepAllViaS.svalleyCvViaS EnvWfT.empty noneJBundle controlInput (.id [])
  (.ofWf CtxWfT.nil) rfl

theorem noneJ_refuses_same_input : noneJRun = none := rfl
theorem coverage_rejects_same_refusal : noneJRun.isSome = false := rfl
-- The mutant equates a successful-output contract with coverage, accepting refusal.
def mutantCoverage (_ : Option (SOutB controlRoots [] piX piX sX controlInput.leaves)) : Bool := true
theorem mutant_coverage_accepts_same_refusal : mutantCoverage noneJRun = true := rfl

-- The observation retains the actual component terms. Only one J census entry is deleted.
abbrev ControlObservation := XOut controlRoots [] (.sort .zero) (.sort .zero) (.sort .zero) (.sort .zero) ×
  List (List (Jd emptyEnv 0)) × List (Jd emptyEnv 0)
def actualObservation : ControlObservation :=
  (controlComponents, controlCalls, [.cv controlCv, .cv controlCv])
def alteredObservation : ControlObservation :=
  (controlComponents, controlCalls, [.cv controlCv])
-- The XOut type fixes all four endpoints. This stronger mutant even checks the
-- complete component terms, yet still loses the J demand when ignoring census.
def componentsOnly (o : ControlObservation) : Prop := o.1 = actualObservation.1
def fullObservation (o : ControlObservation) : Prop := o = actualObservation

theorem mutant_endpoint_accepts_altered : componentsOnly alteredObservation := rfl
theorem census_rejects_same_altered : ¬ fullObservation alteredObservation := by
  intro h
  have bad := congrArg (fun o : ControlObservation => o.2.2.length) h
  contradiction

def transportRun := SepAllViaS.xValleySViaS? EnvWfT.empty closedBundle (.ofWf depthTargetWf) subInput rfl
theorem transport_executes : transportRun.isSome = true :=
  SepAllViaS.xValleySViaS?_isSome_of_piSpined EnvWfT.empty closedBundle (.ofWf depthTargetWf) subInput rfl

def transportResult := transportRun.get transport_executes
theorem transport_explicit_some : transportRun = some transportResult := by
  exact (Option.some_get transport_executes).symm

def transportComponents : XOut roots depthTarget (.sort .zero) (.sort .zero) (.sort .zero) (.sort .zero) :=
  (.trans subOut.1 (.refl _ _),
   .trans subOut.2 (closedBundle.K roots subOut.1 (.refl _ _)))
theorem transport_components : transportResult.1 = transportComponents := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [transportResult, transportRun, SepAllViaS.xValleySViaS?, ViaSEngine.xValleySViaS?,
    ViaSEngine.xSegsViaS, ViaSEngine.xSegSViaS, flattenTc, flattenT,
    Flat.segment, Flat.segmentF, Flat.splitPi, Flat.length, isPiD, piSpinedTc,
    subInput, base, P, SuppliersViaS.structRunner, SegOut.ofA,
    SegOut.cast, ValleyOps.comp, transportComponents, SuppliersViaS.core,
    SuppliersViaS.atOps, subOut, instantiate, lift, isPi, closedBundle, SuppliersViaS.declining, K, EvTc.cast, reduceAnd]
  exact ⟨rfl, rfl, rfl⟩

end Rcic.Declarative.F8Measure.SepAllViaSPins
