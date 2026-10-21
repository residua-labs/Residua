import rcic.RcicAnnIotaSR

/-!
# typed Nat ι redex — non-vacuity of `iotaSRA`

`Γ₀ = ctxMs []`. The redex is `rec [.param 0] P mz ms (succ zero)`, typed by
`HasTyA.app` / `.const` / `.bvar` only (no `ConvA.iota`). `iotaSRA` supplies the
reduct's typing. `HasTyA.const` asks `levelsBounded n [.param 0]`, so the redex
is stated for `0 < n`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

abbrev pinSRIface : IotaIfaceA := iotaIfaceA pinNatBuiltEnvA

theorem pinSR_fam : pinNatBuiltEnvA.members 10 = some pinNatFamA := rfl
theorem pinSR_zero : pinNatBuiltEnvA.members 11 = some pinZeroA := rfl
theorem pinSR_succM : pinNatBuiltEnvA.members 12 = some pinSuccA := rfl

abbrev Γ₀ : LCtxA := ctxMs []

/-- `rec [.param 0] (bvar 2) (bvar 1) (bvar 0) (succ zero)`. -/
def lhs₀ : ExprA :=
  .app (.app (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
    (.app (.const 12 []) (.const 11 []))

/-- `P (succ zero)`. -/
def T₀ : ExprA := .app (.bvar 2) (.app (.const 12 []) (.const 11 []))

/-- `ms zero (rec [.param 0] P mz ms zero)`. -/
def rhs₀ : ExprA :=
  .app (.app (.bvar 0) (.const 11 []))
    (.app (.app (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.const 11 []))

/-! ## shifted telescopes: motive is a context variable, not the recursor's binder -/

def pinSR_ihDom (m : Nat) : ExprA := .app (.bvar m) (.bvar 0)

def pinSR_ihBody (m : Nat) : ExprA :=
  .app (.bvar (m + 1)) (.app (.const 12 []) (.bvar 1))

def pinSR_ihTy (m : Nat) : ExprA :=
  .pi (pinSR_ihDom m) (.param 0) (pinSR_ihBody m) (.param 0)

def pinSR_msTy (m : Nat) : ExprA :=
  .pi (.const 10 []) (.succ .zero) (pinSR_ihTy m) pinMsSortInnerA

def pinSR_majBody (m : Nat) : ExprA := .app (.bvar m) (.bvar 0)

def pinSR_majTy (m : Nat) : ExprA :=
  .pi (.const 10 []) (.succ .zero) (pinSR_majBody m) (.param 0)

/-- `motive zero` with the context motive at `bvar 2`. -/
abbrev mzDom0 : ExprA := .app (.bvar 2) (.const 11 [])

/-- codomain of `rec P`, still under the `mz` binder. -/
abbrev body1 : ExprA :=
  .pi (pinSR_msTy 4) pinMsSortA (pinSR_majTy 5) pinMajorSortA

abbrev ty1 : ExprA := .pi mzDom0 (.param 0) body1 pinMsPiSortA

/-- type of `rec P mz` in `Γ₀`. -/
abbrev ty2 : ExprA :=
  .pi (pinSR_msTy 3) pinMsSortA (pinSR_majTy 4) pinMajorSortA

theorem pinSR_msTy_std : pinSR_msTy 2 = pinMsTyA := rfl
theorem pinSR_majTy_std : pinSR_majTy 3 = pinMajorTyA := rfl
theorem pinSR_levelInst :
    instantiateLevelsA [.param 0] pinNatRecBuiltA = pinNatRecBuiltA := rfl
theorem pinSR_ty1_red : instantiate0A (.bvar 2) pinMzPiA = ty1 := rfl
theorem pinSR_ty2_red : instantiate0A (.bvar 1) body1 = ty2 := rfl
theorem pinSR_maj_red : instantiate0A (.bvar 0) (pinSR_majTy 4) = pinSR_majTy 3 := rfl
theorem pinSR_T0_red :
    instantiate0A (.app (.const 12 []) (.const 11 [])) (pinSR_majBody 3) = T₀ := rfl
theorem pinSR_lu_ms : lookupTypeA Γ₀ 0 = some (pinSR_msTy 3) := rfl
theorem pinSR_lu_mz : lookupTypeA Γ₀ 1 = some mzDom0 := rfl
theorem pinSR_lu_mot : lookupTypeA Γ₀ 2 = some pinMotTyA := rfl

/-! ## typing the open telescope, from `app` / `const` / `bvar` -/

def pinSR_bvarNat {n : Nat} {Γ : LCtxA} (i : Nat)
    (h : lookupTypeA Γ i = some (.const 10 [])) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ (.bvar i) (.const 10 []) :=
  .bvar Γ i (.const 10 []) (.succ .zero) h (pinNatConstTy pinSR_fam)

def pinSR_motApp {n : Nat} {Γ : LCtxA} (i : Nat) (a : ExprA)
    (ha : HasTyA pinNatBuiltEnvA pinSRIface n Γ a (.const 10 []))
    (hm : lookupTypeA Γ i = some pinMotTyA) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ (.app (.bvar i) a) (.sort (.param 0)) :=
  .app Γ (.bvar i) a (.const 10 []) (.sort (.param 0))
    (.succ .zero) (.succ (.param 0)) (.succ (.param 0))
    (.sort (.assumption (.const 10 []) :: Γ) (.param 0))
    (.sort Γ (.param 0))
    (.bvar Γ i pinMotTyA pinMotSortA hm (pinMotTyTy pinSR_fam))
    ha

def pinSR_succOn {n : Nat} {Γ : LCtxA} (a : ExprA)
    (ha : HasTyA pinNatBuiltEnvA pinSRIface n Γ a (.const 10 [])) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ (.app (.const 12 []) a) (.const 10 []) :=
  .app Γ (.const 12 []) a (.const 10 []) (.const 10 [])
    (.succ .zero) (.succ .zero) (.succ .zero)
    (pinNatConstTy (Γ := .assumption (.const 10 []) :: Γ) pinSR_fam)
    (pinNatConstTy pinSR_fam)
    (pinSuccConstTy pinSR_succM pinSR_fam)
    ha

def pinSR_ihDomTy {n : Nat} {Δ : LCtxA} (m : Nat)
    (hm : lookupTypeA (.assumption (.const 10 []) :: Δ) m = some pinMotTyA) :
    HasTyA pinNatBuiltEnvA pinSRIface n (.assumption (.const 10 []) :: Δ)
      (pinSR_ihDom m) (.sort (.param 0)) :=
  pinSR_motApp m (.bvar 0) (pinSR_bvarNat 0 rfl) hm

def pinSR_ihBodyTy {n : Nat} {Δ : LCtxA} (m : Nat)
    (hm : lookupTypeA
      (.assumption (pinSR_ihDom m) :: .assumption (.const 10 []) :: Δ) (m + 1) =
        some pinMotTyA) :
    HasTyA pinNatBuiltEnvA pinSRIface n
      (.assumption (pinSR_ihDom m) :: .assumption (.const 10 []) :: Δ)
      (pinSR_ihBody m) (.sort (.param 0)) :=
  pinSR_motApp (m + 1) (.app (.const 12 []) (.bvar 1))
    (pinSR_succOn (.bvar 1) (pinSR_bvarNat 1 rfl)) hm

def pinSR_ihHasTy {n : Nat} {Δ : LCtxA} (m : Nat)
    (hm : lookupTypeA (.assumption (.const 10 []) :: Δ) m = some pinMotTyA)
    (hmb : lookupTypeA
      (.assumption (pinSR_ihDom m) :: .assumption (.const 10 []) :: Δ) (m + 1) =
        some pinMotTyA) :
    HasTyA pinNatBuiltEnvA pinSRIface n (.assumption (.const 10 []) :: Δ)
      (pinSR_ihTy m) (.sort pinMsSortInnerA) :=
  .pi (.assumption (.const 10 []) :: Δ) (pinSR_ihDom m) (.param 0) (pinSR_ihBody m) (.param 0)
    (pinSR_ihDomTy m hm) (pinSR_ihBodyTy m hmb)

def pinSR_msTyAt {n : Nat} {Δ : LCtxA} (m : Nat)
    (hm : lookupTypeA (.assumption (.const 10 []) :: Δ) m = some pinMotTyA)
    (hmb : lookupTypeA
      (.assumption (pinSR_ihDom m) :: .assumption (.const 10 []) :: Δ) (m + 1) =
        some pinMotTyA) :
    HasTyA pinNatBuiltEnvA pinSRIface n Δ (pinSR_msTy m) (.sort pinMsSortA) :=
  .pi Δ (.const 10 []) (.succ .zero) (pinSR_ihTy m) pinMsSortInnerA
    (pinNatConstTy pinSR_fam) (pinSR_ihHasTy m hm hmb)

def pinSR_majTyAt {n : Nat} {Δ : LCtxA} (m : Nat)
    (hm : lookupTypeA (.assumption (.const 10 []) :: Δ) m = some pinMotTyA) :
    HasTyA pinNatBuiltEnvA pinSRIface n Δ (pinSR_majTy m) (.sort pinMajorSortA) :=
  .pi Δ (.const 10 []) (.succ .zero) (pinSR_majBody m) (.param 0)
    (pinNatConstTy pinSR_fam) (pinSR_ihDomTy m hm)

def pinSR_mzDomTy {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatBuiltEnvA pinSRIface n (ctxMot Γ) pinMzDomA (.sort (.param 0)) :=
  pinSR_motApp 0 (.const 11 []) (pinZeroConstTy pinSR_fam pinSR_zero) rfl

def pinSR_msPiHasTy {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatBuiltEnvA pinSRIface n (ctxMz Γ) pinMsPiA (.sort pinMsPiSortA) :=
  .pi (ctxMz Γ) pinMsTyA pinMsSortA pinMajorTyA pinMajorSortA
    (pinSR_msTyAt (Δ := ctxMz Γ) 2 rfl rfl)
    (pinSR_majTyAt (Δ := ctxMs Γ) 3 rfl)

def pinSR_mzPiHasTy {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatBuiltEnvA pinSRIface n (ctxMot Γ) pinMzPiA (.sort pinMzPiSortA) :=
  .pi (ctxMot Γ) pinMzDomA (.param 0) pinMsPiA pinMsPiSortA
    (pinSR_mzDomTy (Γ := Γ)) (pinSR_msPiHasTy (Γ := Γ))

def pinSR_recHasTy (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ pinNatRecBuiltA (.sort pinRecSortA) :=
  .pi Γ₀ pinMotTyA pinMotSortA pinMzPiA pinMzPiSortA
    (pinMotTyTy pinSR_fam) (pinSR_mzPiHasTy (Γ := Γ₀))

def pinSR_levels (n : Nat) (hn : 0 < n) : levelsBounded n [.param 0] = true := by
  simp only [levelsBounded, levelBounded, Bool.and_true, decide_eq_true hn]

def hΓ₀ (n : Nat) :
    CtxWfA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ₀ :=
  .assumption
    (.assumption
      (.assumption .nil (pinMotTyTy (Γ := []) pinSR_fam))
      (pinSR_mzDomTy (Γ := [])))
    (pinSR_msTyAt (n := n) (Δ := ctxMz []) 2 rfl rfl)

/-! ## `hlhs`, then the step, then one call to `iotaSRA` -/

def pinSR_mzDom0Ty (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ mzDom0 (.sort (.param 0)) :=
  pinSR_motApp 2 (.const 11 []) (pinZeroConstTy pinSR_fam pinSR_zero) pinSR_lu_mot

def pinSR_body2Ty (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n (.assumption (pinSR_msTy 3) :: Γ₀)
      (pinSR_majTy 4) (.sort pinMajorSortA) :=
  pinSR_majTyAt (Δ := .assumption (pinSR_msTy 3) :: Γ₀) 4 rfl

def pinSR_ty2Ty (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ ty2 (.sort pinMsPiSortA) :=
  .pi Γ₀ (pinSR_msTy 3) pinMsSortA (pinSR_majTy 4) pinMajorSortA
    (pinSR_msTyAt (Δ := Γ₀) 3 rfl rfl) (pinSR_body2Ty n)

def pinSR_body1Ty (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n (.assumption mzDom0 :: Γ₀) body1
      (.sort pinMsPiSortA) :=
  .pi (.assumption mzDom0 :: Γ₀) (pinSR_msTy 4) pinMsSortA (pinSR_majTy 5) pinMajorSortA
    (pinSR_msTyAt (Δ := .assumption mzDom0 :: Γ₀) 4 rfl rfl)
    (pinSR_majTyAt (Δ := .assumption (pinSR_msTy 4) :: .assumption mzDom0 :: Γ₀) 5 rfl)

def pinSR_ty1Ty (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ ty1 (.sort pinMzPiSortA) :=
  .pi Γ₀ mzDom0 (.param 0) body1 pinMsPiSortA (pinSR_mzDom0Ty n) (pinSR_body1Ty n)

def pinSR_majOpenTy (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ (pinSR_majTy 3) (.sort pinMajorSortA) :=
  pinSR_majTyAt (Δ := Γ₀) 3 rfl

def pinSR_T0Ty (n : Nat) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ T₀ (.sort (.param 0)) :=
  pinSR_motApp 2 (.app (.const 12 []) (.const 11 []))
    (pinSR_succOn (.const 11 []) (pinZeroConstTy pinSR_fam pinSR_zero)) pinSR_lu_mot

def pinSR_f0 (n : Nat) (hn : 0 < n) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀ (.const 13 [.param 0]) pinNatRecBuiltA :=
  .const Γ₀ 13 [.param 0] pinNatRecMemberA pinRecSortA pinNatBuilt_recMember rfl
    (pinSR_levels n hn) (pinSR_recHasTy n)

def pinSR_f1 (n : Nat) (hn : 0 < n) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀
      (.app (.const 13 [.param 0]) (.bvar 2)) ty1 :=
  .app Γ₀ (.const 13 [.param 0]) (.bvar 2) pinMotTyA pinMzPiA
    pinMotSortA pinMzPiSortA pinMzPiSortA
    (pinSR_mzPiHasTy (Γ := Γ₀)) (pinSR_ty1Ty n) (pinSR_f0 n hn)
    (.bvar Γ₀ 2 pinMotTyA pinMotSortA pinSR_lu_mot (pinMotTyTy pinSR_fam))

def pinSR_f2 (n : Nat) (hn : 0 < n) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀
      (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) ty2 :=
  .app Γ₀ (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1) mzDom0 body1
    (.param 0) pinMsPiSortA pinMsPiSortA
    (pinSR_body1Ty n) (pinSR_ty2Ty n) (pinSR_f1 n hn)
    (.bvar Γ₀ 1 mzDom0 (.param 0) pinSR_lu_mz (pinSR_mzDom0Ty n))

def pinSR_f3 (n : Nat) (hn : 0 < n) :
    HasTyA pinNatBuiltEnvA pinSRIface n Γ₀
      (.app (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (pinSR_majTy 3) :=
  .app Γ₀ (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0)
    (pinSR_msTy 3) (pinSR_majTy 4) pinMsSortA pinMajorSortA pinMajorSortA
    (pinSR_body2Ty n) (pinSR_majOpenTy n) (pinSR_f2 n hn)
    (.bvar Γ₀ 0 (pinSR_msTy 3) pinMsSortA pinSR_lu_ms (pinSR_msTyAt (Δ := Γ₀) 3 rfl rfl))

/-- the redex, typed at `P (succ zero)` before the ι step is used. -/
def hlhs (n : Nat) (hn : 0 < n) :
    HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ₀ lhs₀ T₀ :=
  .app Γ₀
    (.app (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
    (.app (.const 12 []) (.const 11 []))
    (.const 10 []) (pinSR_majBody 3)
    (.succ .zero) (.param 0) (.param 0)
    (pinSR_ihDomTy (Δ := Γ₀) 3 rfl)
    (pinSR_T0Ty n)
    (pinSR_f3 n hn)
    (pinSR_succOn (.const 11 []) (pinZeroConstTy pinSR_fam pinSR_zero))

/-- tooth (a): the reduct is the succ minor, and it contains `rec … zero`. -/
example : iotaFnA pinNatBuiltEnvA lhs₀ =
    some (.app (.app (.bvar 0) (.const 11 []))
      (.app (.app (.app (.app (.const 13 [.param 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.const 11 []))) := by decide

theorem hstep : iotaFnA pinNatBuiltEnvA lhs₀ = some rhs₀ := by decide

theorem pinNat_iotaSR_succ (n : Nat) (hn : 0 < n) :
    Nonempty (HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ₀ rhs₀ T₀) :=
  iotaSRA_ty annEnvA_pinNat (hΓ₀ n) hstep (hlhs n hn)

#print axioms pinSR_levelInst
#print axioms pinSR_ty1_red
#print axioms pinSR_ty2_red
#print axioms pinSR_maj_red
#print axioms pinSR_T0_red
#print axioms pinSR_levels
#print axioms hΓ₀
#print axioms hlhs
#print axioms hstep
#print axioms pinNat_iotaSR_succ

end Rcic.Declarative.Ann
