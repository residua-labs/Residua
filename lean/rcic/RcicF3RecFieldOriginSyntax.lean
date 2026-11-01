import rcic.RcicF3RecFieldOrigin
import rcic.RcicF3RecFieldConsumer

/-!
# Actual recursive lookups and typed applications produce origin facts

Every recursive lookup is interpreted through its successful reader, its
original membership and its complete parameter/index arguments. The proof
builds the proof-valued Origin relation directly along the actual semantic
telescope, without choosing a telescope separately for each branch.

The application theorem uses the actual bounded application-rule premises
in the two original fitted contexts. The full valuation and original key
are retained. These are two cases of the bounded masking induction; they
do not establish its binder/normalizer composition or all-world masks.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldOriginSyntax
open Rcic.Declarative RawFamily PiIndex RecFieldOrigin
open RecFieldSeparation (leaf)

/-- At the supplied positive DATA stage, source membership supplies reached
family fits with the exact parameter/index key retained. -/
theorem of_telescope (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (vs : List Nat)
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    {m : Nat} → (t : RecTel.{4,5} (List PSet.{4}) m) → t.DomainsDich →
      (∀ p, (t.result p).length = (fd.params ++ fd.indices).length) →
      (x : PSet.{4}) → x ∈ Ed (mkM P μ) (t.erasedType (mkM P μ) (leaf P μ fd C vs)) →
      Origin (mkM P μ) fd C m
        (Ed (mkM P μ) (t.erasedType (mkM P μ) (leaf P μ fd C vs)))
        (Ed (mkM P μ) (t.erasedType (mkM P μ)
          (leaf P μ fd (RawFamilyEnlarge.enlarge fd C) vs))) x
  | _, .ret xs, _ht, hl, x, hx => by
      let M := mkM P μ
      have hm : x ∈ leaf P μ fd C vs xs :=
        mem_congr_right (ed_tyv M (dich_ed M _)) hx
      have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0 xs := by
        apply fits_of_fapps_ne M (σOf vs)
          (endValue_resp C vs (fd.params.length + fd.indices.length))
          (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 xs (hl PUnit.unit)
        intro he
        exact not_mem_pempty (mem_congr_right
          ((ed_congr M he).trans (ed_pempty M)) hm)
      exact .leaf vs (key xs) h0
        ((ed_tyv M (dich_ed M _)).trans
          (apply_ofFrame_ed P μ fd C hC vs xs hfit))
        ((ed_tyv M (dich_ed M _)).trans
          (apply_ofFrame_ed P μ fd (RawFamilyEnlarge.enlarge fd C)
            (RawFamilyEnlarge.admissible P fd C hC) vs xs hfit))
  | _, .pi A B, ht, hl, x, hx => by
      let M := mkM P μ
      let LC := leaf P μ fd C vs
      let LD := leaf P μ fd (RawFamilyEnlarge.enlarge fd C) vs
      let BC := fun a => tyv (classFiber A
        (fun q => Ed M ((B q).erasedType M LC)) a)
      let BD := fun a => tyv (classFiber A
        (fun q => Ed M ((B q).erasedType M LD)) a)
      have hBC : ∀ a a', Equiv a a' → Equiv (BC a) (BC a') :=
        fun _ _ he => tyv_congr (classFiber_congr A _ he)
      have hBD : ∀ a a', Equiv a a' → Equiv (BD a) (BD a') :=
        fun _ _ he => tyv_congr (classFiber_congr A _ he)
      apply Origin.pi (tyv A) BC BD hBC hBD Equiv.rfl Equiv.rfl
      intro a ha
      have happ : fapp x a ∈ Ed M (BC a) := app_mem M hBC hx ha
      obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
      let q := Quotient.mk (FSetoid A) i
      have ec : Equiv (classFiber A (fun q => Ed M ((B q).erasedType M LC)) a)
          (Ed M ((B q).erasedType M LC)) :=
        (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
      have ed : Equiv (classFiber A (fun q => Ed M ((B q).erasedType M LD)) a)
          (Ed M ((B q).erasedType M LD)) :=
        (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
      have eC : Equiv (Ed M (BC a)) (Ed M ((B q).erasedType M LC)) :=
        (ed_tyv M ((dich_congr ec).mpr (dich_ed M _))).trans ec
      have eD : Equiv (Ed M (BD a)) (Ed M ((B q).erasedType M LD)) :=
        (ed_tyv M ((dich_congr ed).mpr (dich_ed M _))).trans ed
      have ho := of_telescope P μ fd C hC vs h0 (B q) (ht.2 q)
        (fun p => hl ⟨q, p⟩) (fapp x a) (mem_congr_right eC happ)
      exact ho.transport eC.symm eD.symm Equiv.rfl

/-- Both normalizations are produced from the same actual lookup member.
The source and enlarged models retain the whole original local context. -/
theorem lookup (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (hb : BodiesOK E σ K) (ρ : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (k : Nat) (T : Expr Nat) (hlook : lookupType Γ k = some T)
    (ar fuel : Nat) (ds args : List (Expr Nat))
    (hw : piTelescopeFuel E fuel T = some (ds, foldApps (.const fd.fref (canonL ar)) args))
    (hI : InstOK E σ K T)
    (hds : ∀ A ∈ ds, occursConst fd.fref A = false)
    (hargs : ∀ a ∈ args, occursConst fd.fref a = false)
    (hlen : args.length = (fd.params ++ fd.indices).length)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0) :
    Origin (mkM P μ) fd C ds.length
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ T))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ T)) (ρ k) := by
  let M := mkM P μ
  let MC := mkM P (table P μ fd C)
  let vs := (canonL ar).map (evalTotal σ)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P μ σ args) ds ρ
  have hNC := RecFieldConsumer.lookup_field_eq P μ fd C σ K hEC hb ρ hρC
    k T hlook ar fuel ds args hw hI hds hargs
  have hND := RecFieldConsumer.lookup_field_eq P μ fd (RawFamilyEnlarge.enlarge fd C)
    σ K hED hb ρ hρD k T hlook ar fuel ds args hw hI hds hargs
  dsimp only at hNC hND
  have hx : ρ k ∈ Ed MC (den MC σ ρ T) :=
    sound_ty (P.good MC rfl) hEC (HasTyT.bvar Γ k T hlook) True.intro ρ hρC
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ
    (PiIndependent.leafArgs P μ σ args) ds ρ
  have hl : ∀ p, (t.result p).length = (fd.params ++ fd.indices).length :=
    PiPropField.compile_result_property M σ (PiIndependent.leafArgs P μ σ args)
      (fun xs => xs.length = (fd.params ++ fd.indices).length)
      (fun _ => (List.length_map _ _).trans hlen) ds ρ
  exact (of_telescope P μ fd C hC vs h0 t ht hl (ρ k)
    (mem_congr_right hNC.symm hx)).transport hNC hND Equiv.rfl

/-- Every semantic premise of the origin-head application case comes
from the two actual bounded application-rule derivations. -/
theorem typed_application (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (ρ : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (f a A B : Expr Nat)
    (hf : occursConst fd.fref f = false) (ha : occursConst fd.fref a = false)
    (df : HasTyT E n Γ f (.pi A B)) (hdf : LOKt σ 4 K df)
    (da : HasTyT E n Γ a A) (hda : LOKt σ 4 K da)
    (m : Nat)
    (ho : Origin (mkM P μ) fd C m
      (Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρ (.pi A B)))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (.pi A B)))
      (den (mkM P (table P μ fd C)) σ ρ f)) :
    Origin (mkM P μ) fd C (m - 1)
      (Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρ (instantiate0 a B)))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ (instantiate0 a B)))
      (den (mkM P (table P μ fd C)) σ ρ (.app f a)) := by
  let M := mkM P μ
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  have ef : den MC σ ρ f = den MD σ ρ f :=
    PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
      (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ f hf ρ
  have ea : den MC σ ρ a = den MD σ ρ a :=
    PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
      (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ a ha ρ
  have hz := sound_ty (P.good MC rfl) hEC df hdf ρ hρC
  have hzD : den MC σ ρ f ∈ Ed MD (den MD σ ρ (.pi A B)) := by
    rw [ef]
    exact sound_ty (P.good MD rfl) hED df hdf ρ hρD
  have harg := sound_ty (P.good MC rfl) hEC da hda ρ hρC
  have h := RecFieldOrigin.application
    (M := M) (fd := fd) (C := C)
    (den_resp MC σ ρ B) (den_resp MD σ ρ B) ho hz hzD harg
  change Origin M fd C (m - 1)
    (Ed MC (den MC σ ρ (instantiate0 a B)))
    (Ed MD (den MD σ ρ (instantiate0 a B)))
    (fapp (den MC σ ρ f) (den MC σ ρ a))
  rw [den_inst0, den_inst0, ← ea]
  exact h

end Rcic.F3.PSet.RecFieldOriginSyntax
