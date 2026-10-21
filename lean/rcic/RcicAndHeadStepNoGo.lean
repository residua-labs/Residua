import rcic.RcicHeadStepT
import rcic.RcicTypedGroupPins

/-! `RcicAndHeadStepNoGo` — the And mixed pair (cc ruling on #6293,
05:15Z, item (2); r1b).

The Π-injectivity wall needs an index-gated K elimination whose major
is a PROOF, mixed through a sort row. `And` (the `RcicTypedGroupPins`
group at refs 0/1/2 — family `Π (a b : Prop), Prop`, one constructor
`intro a b x y` with two plain proof fields, AnySort recursor) is the
fixture. At context `[h : And a b, y : b, x : a, b, a]`:

* `mixAnd_conv` — the `ConvT` derivation of the MIXED conversion
  `And.rec (λ _ : And a b. Sort 1) (λ (x : a)(y : b). Sort 0 → Sort 0) h
  ≡ Sort 0 → Sort 0`: `irr` identifies the proof major `h` with the
  `intro`-headed `mk a b x y` (`ConvT.app` + `ConvT.irr`), ordinary ι
  fires on the substituted major (`ConvT.iota` at `mixAndW`), and two
  β steps unwind `m x y` to `Π (S : Sort 0), Sort 0`.

* `mixAnd_headStepT_none` — `HeadStepT` refuses the mixed pair:
  β needs a `lam` head (the head is `const 2`), ordinary ι needs the
  major to BE `ctorMajor` (it is `bvar 0`), and ι★K carries
  `hfields0 : w.fields = []` while the env forces `w.fields.length`
  to `piCount andIntroMember.mtype - nparams = 4 - nparams` — with
  `hnmin`/`hpre` pinning `nparams + nindices = 2`, `fields = []` gives
  `nparams = 4 > 2`, contradiction. The K-like step exists only for
  field-free constructors; `intro` is fieldful.

So `ConvT` reaches the reduct `HeadStepT` cannot compute — the mixed
pair is a conversion-closure obligation, not a head step.
`closure_claim` stays 0. -/

namespace Rcic

open Rcic.Declarative

/-! ## context and terms -/

/-- `[h : And a b, y : b, x : a, b : Sort 0, a : Sort 0]` (innermost
first). `h`'s stored type is written under `[y, x, b, a]`. -/
def mixAndCtx : LCtx :=
  [.assumption (andApp (.bvar 3) (.bvar 2)), .assumption (.bvar 1),
   .assumption (.bvar 1), .assumption (.sort .zero),
   .assumption (.sort .zero)]

/-- `And a b` at `mixAndCtx`. -/
def mixAndFamApp : Expr Nat := andApp (.bvar 4) (.bvar 3)

/-- the `Sort 1`-valued motive `λ _ : And a b. Sort 1`. -/
def mixAndMot : Expr Nat := .lam mixAndFamApp (.sort (.succ .zero))

/-- `Π (S : Sort 0), Sort 0`. -/
def mixPi : Expr Nat := .pi (.sort .zero) (.sort .zero)

/-- the minor `λ (x : a)(y : b). Sort 0 → Sort 0`. -/
def mixAndMin : Expr Nat := .lam (.bvar 4) (.lam (.bvar 4) mixPi)

/-- the constructor major `intro a b x y`. -/
def mixAndMkApp : Expr Nat :=
  foldApps (.const 1 []) [.bvar 4, .bvar 3, .bvar 2, .bvar 1]

/-- pre-major spine `[a, b, M, m]` (2 params, motive, 1 minor, no
indices). -/
def mixAndSpine : List (Expr Nat) :=
  [.bvar 4, .bvar 3, mixAndMot, mixAndMin]

/-- `And.rec a b M m` (level `[2]` — the AnySort `param 0` carried at
`Sort 2`). -/
def mixAndRec : Expr Nat :=
  foldApps (.const 2 [.succ (.succ .zero)]) mixAndSpine

/-- THE MIXED PAIR `And.rec M m h`. -/
def mixAndRedex : Expr Nat := .app mixAndRec (.bvar 0)

/-- the constructor-headed variant `And.rec M m (mk a b x y)` —
`iotaLhsOf mixAndW`. -/
def mixAndLhs : Expr Nat := .app mixAndRec mixAndMkApp

/-- the iota reduct `m x y` — `iotaRhsOf mixAndW`. -/
def mixAndRhs : Expr Nat := .app (.app mixAndMin (.bvar 2)) (.bvar 1)

/-! ## context leaves -/

def mixTyA : HasTyT andEnvU 0 mixAndCtx (.bvar 4) (.sort .zero) :=
  .bvar _ 4 _ rfl

def mixTyB : HasTyT andEnvU 0 mixAndCtx (.bvar 3) (.sort .zero) :=
  .bvar _ 3 _ rfl

/-- `x : a` by lookup. -/
def mixTyX : HasTyT andEnvU 0 mixAndCtx (.bvar 2) (.bvar 4) :=
  .bvar _ 2 _ rfl

/-- `y : b` by lookup. -/
def mixTyY : HasTyT andEnvU 0 mixAndCtx (.bvar 1) (.bvar 3) :=
  .bvar _ 1 _ rfl

/-- `h : And a b` by lookup. -/
def mixTyH : HasTyT andEnvU 0 mixAndCtx (.bvar 0) mixAndFamApp :=
  .bvar _ 0 _ rfl

/-! ## family / motive / constructor typings -/

/-- `And a b : Sort 0` — the Prop premise `irr` needs. -/
def mixAndFamTy : HasTyT andEnvU 0 mixAndCtx mixAndFamApp (.sort .zero) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.const _ 0 [] andFamMember rfl rfl rfl) mixTyA)
    mixTyB

/-- `λ _ : And a b. Sort 1 : Π _ : And a b, Sort 2`. -/
def mixAndMotTy : HasTyT andEnvU 0 mixAndCtx mixAndMot
    (.pi mixAndFamApp (.sort (.succ (.succ .zero)))) :=
  .lam _ mixAndFamApp .zero (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    mixAndFamTy (.sort _ _)

/-- `intro a b x y : And a b` — four `HasTyT.app` legs on the stored
`Π (a b : Prop), a → b → And a b`. -/
def mixAndMkTy : HasTyT andEnvU 0 mixAndCtx mixAndMkApp mixAndFamApp :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.const _ 1 [] andIntroMember rfl rfl rfl) mixTyA)
        mixTyB)
      mixTyX)
    mixTyY

/-! ## the minor's natural type and the transport to `Π x y. M (mk x y)` -/

private def mixCtxX : LCtx := .assumption (.bvar 4) :: mixAndCtx

private def mixCtxXY : LCtx := .assumption (.bvar 4) :: mixCtxX

private def mixTyBX : HasTyT andEnvU 0 mixCtxX (.bvar 4) (.sort .zero) :=
  .bvar _ 4 _ rfl

private def mixPiTyXY : HasTyT andEnvU 0 mixCtxXY mixPi
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero)

private def mixAndMinInner : HasTyT andEnvU 0 mixCtxX
    (.lam (.bvar 4) mixPi) (.pi (.bvar 4) (.sort (.imax (.succ .zero) (.succ .zero)))) :=
  .lam _ _ _ _ _ mixTyBX mixPiTyXY

/-- `λ x y. Π (S : Sort 0), Sort 0` at its OWN type — the codomain is
`Sort (imax 1 1)`, not yet the motive application the recursor wants. -/
def mixAndMinTyNat : HasTyT andEnvU 0 mixAndCtx mixAndMin
    (.pi (.bvar 4) (.pi (.bvar 4) (.sort (.imax (.succ .zero) (.succ .zero))))) :=
  .lam _ _ _ _ _ mixTyA mixAndMinInner

/-- `mk a b x y` under `[y' : b, x' : a]` (telescope-style index
positions — the minor's expected codomain `M (mk a b x y)`). -/
def mixAndMkTel : Expr Nat :=
  foldApps (.const 1 []) [.bvar 6, .bvar 5, .bvar 1, .bvar 0]

private def mixTyAXY : HasTyT andEnvU 0 mixCtxXY (.bvar 6) (.sort .zero) :=
  .bvar _ 6 _ rfl

private def mixTyBXY : HasTyT andEnvU 0 mixCtxXY (.bvar 5) (.sort .zero) :=
  .bvar _ 5 _ rfl

private def mixTyXXY : HasTyT andEnvU 0 mixCtxXY (.bvar 1) (.bvar 6) :=
  .bvar _ 1 _ rfl

private def mixTyYXY : HasTyT andEnvU 0 mixCtxXY (.bvar 0) (.bvar 5) :=
  .bvar _ 0 _ rfl

private def mixAndABXY : HasTyT andEnvU 0 mixCtxXY (andApp (.bvar 6) (.bvar 5))
    (.sort .zero) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.const _ 0 [] andFamMember rfl rfl rfl) mixTyAXY)
    mixTyBXY

/-- `mk a b x y : And a b` under `[y', x']`. -/
private def mixAndMkTelTy : HasTyT andEnvU 0 mixCtxXY mixAndMkTel
    (andApp (.bvar 6) (.bvar 5)) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.const _ 1 [] andIntroMember rfl rfl rfl) mixTyAXY)
        mixTyBXY)
      mixTyXXY)
    mixTyYXY

/-- `(λ _. Sort 1) (mk a b x y) ≡ Sort 1` — β at the shifted motive. -/
private def mixMkTelBeta : ConvT andEnvU 0 mixCtxXY
    (.app (lift 0 2 mixAndMot) mixAndMkTel) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  ConvT.beta _ _ _ _ _ _ mixAndABXY (.sort _ _) mixAndMkTelTy

private def mixEqN_imax11 :
    eqN (.imax (.succ .zero) (.succ .zero)) (.succ .zero) := fun _ => rfl

private def mixEqN_succImax11 :
    eqN (.succ (.imax (.succ .zero) (.succ .zero))) (.succ (.succ .zero)) :=
  fun _ => rfl

/-- `Sort (imax 1 1) ≡ Sort 1` at `Sort 2` (`ConvT.sorts` annotates at
`Sort (succ l)`; `tyConv` re-annotates). -/
private def mixCImax11 (Γ' : LCtx) : ConvT andEnvU 0 Γ'
    (.sort (.imax (.succ .zero) (.succ .zero))) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  ConvT.tyConv _ _ _ _ _ _
    (ConvT.sorts _ _ _ mixEqN_imax11)
    (ConvT.sorts _ _ _ mixEqN_succImax11)

/-- the codomain leg: `Sort (imax 1 1) ≡ (λ_.Sort 1) (mk …)` at
`Sort 2` under `[y', x']`. -/
private def mixAndMinCod : ConvT andEnvU 0 mixCtxXY
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.app (lift 0 2 mixAndMot) mixAndMkTel) (.sort (.succ (.succ .zero))) :=
  ConvT.trans _ _ _ _ _ (mixCImax11 mixCtxXY)
    (ConvT.symm _ _ _ _ mixMkTelBeta)

/-- the minor's expected type `Π (x : a)(y : b). M (mk a b x y)` is
conversion-equal to its lam-inferred type, at `Sort (imax 0 (imax 0 2))`. -/
private def mixAndMinConv : ConvT andEnvU 0 mixAndCtx
    (.pi (.bvar 4) (.pi (.bvar 4) (.sort (.imax (.succ .zero) (.succ .zero)))))
    (.pi (.bvar 4) (.pi (.bvar 4) (.app (lift 0 2 mixAndMot) mixAndMkTel)))
    (.sort (.imax .zero (.imax .zero (.succ (.succ .zero))))) :=
  ConvT.pi _ _ _ _ _ _ _
    (ConvT.refl _ _ _ mixTyA)
    (ConvT.pi _ _ _ _ _ _ _
      (ConvT.refl _ _ _ mixTyBX)
      mixAndMinCod)

/-- `λ x y. Sort 0 → Sort 0` at the recursor's minor domain. -/
def mixAndMinTy : HasTyT andEnvU 0 mixAndCtx mixAndMin
    (.pi (.bvar 4) (.pi (.bvar 4)
      (.app (lift 0 2 mixAndMot) mixAndMkTel))) :=
  HasTyT.conv _ _ _ _ _ mixAndMinTyNat mixAndMinConv

/-! ## the recursor spine typing -/

private def mixAndRec0 : HasTyT andEnvU 0 mixAndCtx
    (.const 2 [.succ (.succ .zero)])
    (instantiateLevels [.succ (.succ .zero)] andRecMemberU.mtype) :=
  .const _ 2 [.succ (.succ .zero)] andRecMemberU rfl rfl rfl

private def mixAndRec1 := HasTyT.app _ _ _ _ _ mixAndRec0 mixTyA
private def mixAndRec2 := HasTyT.app _ _ _ _ _ mixAndRec1 mixTyB
private def mixAndRec3 := HasTyT.app _ _ _ _ _ mixAndRec2 mixAndMotTy
private def mixAndRec4 := HasTyT.app _ _ _ _ _ mixAndRec3 mixAndMinTy

/-- `And.rec a b M m : Π (h' : And a b), M h'`. -/
def mixAndRecTy : HasTyT andEnvU 0 mixAndCtx mixAndRec
    (.pi mixAndFamApp (.app (lift 0 1 mixAndMot) (.bvar 0))) :=
  mixAndRec4

/-- `And.rec M m (mk a b x y) : M (mk a b x y)` — the iota lhs. -/
def mixAndLhsTy : HasTyT andEnvU 0 mixAndCtx mixAndLhs
    (.app mixAndMot mixAndMkApp) :=
  HasTyT.app _ _ _ _ _ mixAndRecTy mixAndMkTy

/-- `m x y` at `M (mk a b x y)` — its own type is `Sort (imax 1 1)`,
transported through `imax 1 1 = 1` and the motive β. -/
def mixAndRhsTy : HasTyT andEnvU 0 mixAndCtx mixAndRhs
    (.app mixAndMot mixAndMkApp) :=
  HasTyT.conv _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _ mixAndMinTyNat mixTyX) mixTyY)
    (ConvT.trans _ _ _ _ _ (mixCImax11 mixAndCtx)
      (ConvT.symm _ _ _ _
        (ConvT.beta _ _ _ _ _ _ mixAndFamTy (.sort _ _) mixAndMkTy)))

/-! ## the iota witness and the mixed conversion -/

/-- The iota witness at the `intro`-headed major: params `[a, b]`,
FIELDS `[x, y]` — nonempty; `hfields0`-incompatible by `hnpar`. -/
def mixAndW : IotaWitness andEnvU where
  recRef := 2
  ctorRef := 1
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := andRecMemberU
  ctorMember := andIntroMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := mixAndSpine
  fields := [.bvar 2, .bvar 1]
  ctorParams := [.bvar 4, .bvar 3]
  kinds := [.plain, .plain]
  minor := mixAndMin
  hlen := rfl
  familyRef := 0
  famMember := andFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 0
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
  ctorDoms := [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
  ctorResult := andApp (.bvar 3) (.bvar 2)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort .zero, .sort .zero, andMotTy, andMinorTy,
    andApp (.bvar 3) (.bvar 2)]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := .pi (.bvar 4) (.pi (.bvar 4) (andApp (.bvar 6) (.bvar 5)))
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `irr` at the proof major: `h ≡ mk a b x y` at `And a b`. -/
def mixAndIrr : ConvT andEnvU 0 mixAndCtx (.bvar 0) mixAndMkApp
    mixAndFamApp :=
  .irr _ _ _ _ mixAndFamTy mixTyH mixAndMkTy

/-- the conversion lifts through the spine's last argument:
`rec … h ≡ rec … (mk …)` at `M h`. -/
def mixAndAppCong : ConvT andEnvU 0 mixAndCtx mixAndRedex mixAndLhs
    (.app mixAndMot (.bvar 0)) :=
  .app _ _ _ _ _ _ _ (ConvT.refl _ _ _ mixAndRecTy) mixAndIrr

/-- honest ι: `rec a b M m (mk a b x y) ⇒ m x y` at `M (mk …)`. -/
def mixAndIota : ConvT andEnvU 0 mixAndCtx mixAndLhs mixAndRhs
    (.app mixAndMot mixAndMkApp) :=
  .iota _ _ _ _ (.of mixAndW) mixAndLhsTy mixAndRhsTy

/-- `M h ≡ Sort (imax 1 1)` — motive β + `imax`-collapse, the
annotation exchange. -/
private def mixMhSort : ConvT andEnvU 0 mixAndCtx
    (.app mixAndMot (.bvar 0))
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ (.succ .zero))) :=
  ConvT.trans _ _ _ _ _
    (ConvT.beta _ _ _ _ _ _ mixAndFamTy (.sort _ _) mixTyH)
    (ConvT.symm _ _ _ _ (mixCImax11 mixAndCtx))

/-- `M (mk …) ≡ Sort (imax 1 1)` — same exchange at the ctor major. -/
private def mixMmkSort : ConvT andEnvU 0 mixAndCtx
    (.app mixAndMot mixAndMkApp)
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ (.succ .zero))) :=
  ConvT.trans _ _ _ _ _
    (ConvT.beta _ _ _ _ _ _ mixAndFamTy (.sort _ _) mixAndMkTy)
    (ConvT.symm _ _ _ _ (mixCImax11 mixAndCtx))

/-- `m x y ≡ λ (_ : b). Π (S : Sort 0), Sort 0` under the x-application —
the first β inside the rhs. -/
private def mixBeta1 : ConvT andEnvU 0 mixAndCtx
    (.app mixAndMin (.bvar 2)) (.lam (.bvar 3) mixPi)
    (.pi (.bvar 3) (.sort (.imax (.succ .zero) (.succ .zero)))) :=
  ConvT.beta _ _ _ _ _ _ mixTyA mixAndMinInner mixTyX

/-- `m x y ≡ Π (S : Sort 0), Sort 0` — outer β moved under the y-app,
then inner β. -/
private def mixRhsToPi : ConvT andEnvU 0 mixAndCtx mixAndRhs mixPi
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  ConvT.trans _ _ _ _ _
    (ConvT.app _ _ _ _ _ _ _ mixBeta1 (ConvT.refl _ _ _ mixTyY))
    (ConvT.beta _ _ _ _ _ _ mixTyB
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero)) mixTyY)

/-- THE MIXED PAIR:
`And.rec (λ_. Sort 1) (λ x y. Sort 0 → Sort 0) h ≡ Sort 0 → Sort 0`
at `Sort (imax 1 1)` — `irr`-lift + ι + two β. -/
def mixAnd_conv : Nonempty (ConvT andEnvU 0 mixAndCtx mixAndRedex mixPi
    (.sort (.imax (.succ .zero) (.succ .zero)))) :=
  ⟨ConvT.trans _ _ _ _ _
    (ConvT.trans _ _ _ _ _
      (ConvT.tyConv _ _ _ _ _ _ mixAndAppCong mixMhSort)
      (ConvT.tyConv _ _ _ _ _ _ mixAndIota mixMmkSort))
    mixRhsToPi⟩

/-! ## `HeadStepT` refusal -/

/-- `HeadStepT` REFUSES the mixed pair. β needs a `lam` head (the head
is `const 2`); ι needs the major to BE `ctorMajor` (it is `bvar 0`);
ι★K needs `w.fields = []` and ι★KField needs `w.fields = [major]`, but
the env pins `w.recMember = andRecMemberU` and `w.ctorMember =
andIntroMember`, so `hnpar`/`hnmin`/`hfields*` pin `fields.length` at
2 and `4 = w.nparams` against `w.nparams + w.nindices = 2`. -/
theorem mixAnd_headStepT_none {n : Nat} {a T : Expr Nat}
    (h : HeadStepT andEnvU n mixAndCtx mixAndRedex a T) : False := by
  have he : mixAndRedex =
      .app (foldApps (.const 2 [.succ (.succ .zero)])
        mixAndSpine) (.bvar 0) := rfl
  match headStepT_inv_app h he with
  | .beta A body B u v w' hf' ha' =>
      exact absurd hf' headStepT_foldApps_const_ne_lam
  | .iota w heq ha =>
      have hs := congrArg appsSpine heq
      rw [← foldApps_snoc, appsSpine_foldApps_const,
        headStepT_iotaLhs_spine] at hs
      injection hs with _hhead hargs
      obtain ⟨_, hmaj⟩ := list_snoc_inj hargs
      have hcm : (appsSpine (.bvar 0)).1 =
          (appsSpine (ctorMajor w)).1 :=
        congrArg (fun e => (appsSpine e).1) hmaj
      rw [appsSpine_bvar, headStepT_ctorMajor_spine] at hcm
      have hbc : Expr.bvar 0 = Expr.const w.ctorRef w.lsC := hcm
      exact nomatch hbc
  | .iotaStarK w major Tm rl afs heq hfam hmajor hcv hnmin1 hfields0
      ha =>
      have hs := congrArg appsSpine heq
      rw [← foldApps_snoc, appsSpine_foldApps_const,
        appsSpine_recCall] at hs
      injection hs with hhead _hargs
      injection hhead with hrec _hls
      have hmemr : w.recMember = andRecMemberU := by
        have a := w.hrec; rw [← hrec] at a
        exact (Option.some.inj a).symm
      have hmin5 : w.nparams + 1 + w.nMinors + w.nindices + 1 = 5 := by
        have hnm := w.hnmin; rw [hmemr] at hnm; exact hnm
      have hfam0 : w.familyRef = 0 := by
        have hri := w.hrecIdx; omega
      have hidx0 : w.ctorIdx = 0 := by
        have hi := w.hidx; omega
      have hctor1 : w.ctorRef = 1 := by
        have hci := w.hctorIdx; omega
      have hmemc : w.ctorMember = andIntroMember := by
        have a := w.hctor; rw [hctor1] at a
        exact (Option.some.inj a).symm
      have hpar : w.nparams + w.fields.length = 4 := by
        have hnp := w.hnpar; rw [hmemc] at hnp; exact hnp
      have hfl : w.fields.length = 0 := congrArg List.length hfields0
      omega
  | .iotaStarKField w major Tm rl afs heq hfam hmajor hcv hnmin1
      hfields1 hnctor ha =>
      have hs := congrArg appsSpine heq
      rw [← foldApps_snoc, appsSpine_foldApps_const,
        appsSpine_recCall] at hs
      injection hs with hhead _hargs
      injection hhead with hrec _hls
      have hmemr : w.recMember = andRecMemberU := by
        have a := w.hrec; rw [← hrec] at a
        exact (Option.some.inj a).symm
      have hmin5 : w.nparams + 1 + w.nMinors + w.nindices + 1 = 5 := by
        have hnm := w.hnmin; rw [hmemr] at hnm; exact hnm
      have hfam0 : w.familyRef = 0 := by
        have hri := w.hrecIdx; omega
      have hidx0 : w.ctorIdx = 0 := by
        have hi := w.hidx; omega
      have hctor1 : w.ctorRef = 1 := by
        have hci := w.hctorIdx; omega
      have hmemc : w.ctorMember = andIntroMember := by
        have a := w.hctor; rw [hctor1] at a
        exact (Option.some.inj a).symm
      have hpar : w.nparams + w.fields.length = 4 := by
        have hnp := w.hnpar; rw [hmemc] at hnp; exact hnp
      have hfl : w.fields.length = 1 := by
        rw [hfields1, List.length_singleton]
      omega

#check mixAnd_conv
#check mixAnd_headStepT_none
#print axioms mixAnd_conv
#print axioms mixAnd_headStepT_none

end Rcic
