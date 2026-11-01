import rcic.RcicF3RecFieldOrigin
import rcic.RcicF3PiIndependent
import rcic.RcicF3Whnf

/-!
# Bounded conversion and type exclusion for recursive origins

An actual bounded type-conversion chain transports the two decoded types
of an Origin in the two original fitting environments. The same actual
value, remaining recursive depth and complete leaf keys are retained.
The conversion-rule instance consumes the bounds of that literal rule.

A family-free expected type has identical denotation in the source and
enlarged family models at the same original environment. The produced
Origin separator therefore makes a typed origin value empty. At an
expected sort this is impossible: actual bounded typehood makes its value
an element of a universe, and no height-four universe contains pempty.

These are conversion and type-exclusion cases for the bounded masking
induction. They do not establish its binder/reader composition or any
all-world domain mask. No masked environment is asserted to fit.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldOriginCases
open Rcic.Declarative RawFamily RecFieldOrigin

/-- The actual chain is interpreted twice, at its unchanged full valuation
and bounds. The original environments may differ; both fit the same Γ. -/
theorem bounded_conversion (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {M : Interp.{4}} {fd : FamData} {C : Frame}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (hμ : EnvSound (mkM P μ) σ K E n)
    (hν : EnvSound (mkM P ν) σ K E n)
    (ρ η : Nat → PSet.{4})
    (hρ : Fits (mkM P μ) σ Γ ρ) (hη : Fits (mkM P ν) σ Γ η)
    (c : TyConvT E n Γ A B) (hc : BoundedBVar.Bounded σ 4 K c)
    {m : Nat} {z : PSet.{4}}
    (ho : Origin M fd C m
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A))
      (Ed (mkM P ν) (den (mkM P ν) σ η A)) z) :
    Origin M fd C m
      (Ed (mkM P μ) (den (mkM P μ) σ ρ B))
      (Ed (mkM P ν) (den (mkM P ν) σ η B)) z := by
  have hA := BoundedBVar.chain_sound P μ σ K hμ ρ hρ c hc
  have hB := BoundedBVar.chain_sound P ν σ K hν η hη c hc
  exact ho.transport (ed_congr (mkM P μ) hA) (ed_congr (mkM P ν) hB) Equiv.rfl

/-- The conversion edge and its bound are actual premises of the supplied
typing rule. This does not synthesize an unbounded conversion or a new Γ. -/
theorem conversion_rule (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {M : Interp.{4}} {fd : FamData} {C : Frame}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (hμ : EnvSound (mkM P μ) σ K E n)
    (hν : EnvSound (mkM P ν) σ K E n)
    (ρ η : Nat → PSet.{4})
    (hρ : Fits (mkM P μ) σ Γ ρ) (hη : Fits (mkM P ν) σ Γ η)
    (d : HasTyT E n Γ e A) (c : ConvT E n Γ A B (.sort u))
    (hd : LOKt σ 4 K (HasTyT.conv Γ e A B u d c))
    {m : Nat}
    (ho : Origin M fd C m
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A))
      (Ed (mkM P ν) (den (mkM P ν) σ η A)) (den (mkM P μ) σ ρ e)) :
    Origin M fd C m
      (Ed (mkM P μ) (den (mkM P μ) σ ρ B))
      (Ed (mkM P ν) (den (mkM P ν) σ η B)) (den (mkM P μ) σ ρ e) := by
  exact bounded_conversion P μ ν σ K hμ hν ρ η hρ hη
    (.of Γ A B u c) (by simpa only [BoundedBVar.Bounded] using hd.2) ho

/-- Actual typing supplies membership. Independence of the expected type
supplies equal decoded types at the SAME original local environment. -/
theorem clean_expected (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    {e A : Expr Nat} (hfree : occursConst fd.fref A = false)
    (d : HasTyT E n Γ e A) (hd : LOKt σ 4 K d) {m : Nat}
    (ho : Origin (mkM P μ) fd C m
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A))
      (den (mkM P (table P μ fd C)) σ ρ e)) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ e) pempty := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  have he : den MC σ ρ A = den MD σ ρ A :=
    PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
      (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ A hfree ρ
  have htypes : Equiv (Ed MC (den MC σ ρ A)) (Ed MD (den MD σ ρ A)) := by
    change Equiv (Ed (mkM P μ) (den MC σ ρ A))
      (Ed (mkM P μ) (den MD σ ρ A))
    simpa only [he] using
      (Equiv.rfl : Equiv (Ed (mkM P μ) (den MD σ ρ A))
        (Ed (mkM P μ) (den MD σ ρ A)))
  exact separator ho (sound_ty (P.good MC rfl) hE d hd ρ hρ) htypes

/-- The tainted branch cannot occur for a bounded typed type. In particular,
this conclusion needs no typing or fit for a masked local environment. -/
theorem sort_exclusion (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    {e : Expr Nat} {l : Level}
    (d : HasTyT E n Γ e (.sort l)) (hd : LOKt σ 4 K d) {m : Nat}
    (ho : Origin (mkM P μ) fd C m
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ (.sort l)))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (.sort l)))
      (den (mkM P (table P μ fd C)) σ ρ e)) : False := by
  have hz := clean_expected P μ fd C σ K hE ρ hρ (A := .sort l) rfl d hd ho
  exact den_type_ne_pempty (mkM P (table P μ fd C)) σ
    (fun k => pempty_not_mem_U4 P k) ρ
    (sound_ty (P.good _ rfl) hE d hd ρ hρ) hz

end Rcic.F3.PSet.RecFieldOriginCases
