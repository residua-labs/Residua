import rcic.RcicF3RawFamilyEnlarge
import rcic.RcicF3PiPropField

/-!
# Reachable-path separation of higher-order DATA fields

A full application of an admissible frame yields its exact fibre only at
fitting complete arguments. Actual leaf membership produces that fit here.
At every reached leaf, the enlarged frame contains a fresh data spike.
Encoding those spikes through the actual dependent telescope separates the
two field element sets whenever a complete path exists. With no complete
path, exact erased readback makes every field value the empty proof value.

No inner domain is required to be inhabited. All arguments, dependencies,
and family universe entries are retained. This semantic component does not
produce a domain mask from typed admission or a universal small frame.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldSeparation
open Rcic.Declarative RawFamily PiIndex
universe v

/-- The full leaf application retains both parameter and index values. -/
def leaf (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (xs : List PSet.{4}) : PSet.{4} :=
  Ed (mkM P μ) (fapps (ofFrame P μ fd C vs) xs)

private theorem leaf_fits (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length)
    (z : PSet.{4}) (hz : z ∈ leaf P μ fd C vs xs) :
    TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs := by
  apply fits_of_fapps_ne (mkM P μ) (σOf vs)
    (endValue_resp C vs (fd.params.length + fd.indices.length))
    (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 xs hl
  intro he
  exact not_mem_pempty (mem_congr_right
    ((ed_congr (mkM P μ) he).trans (ed_pempty (mkM P μ))) hz)

private theorem spike_leaf_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (vs : List Nat)
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length)
    (z : PSet.{4}) (hz : z ∈ leaf P μ fd C vs xs) :
    RawFamilyEnlarge.spike (C vs (key xs)) ∈
      leaf P μ fd (RawFamilyEnlarge.enlarge fd C) vs xs := by
  have hfit := leaf_fits P μ fd C vs xs hl z hz
  apply mem_congr_right (apply_ofFrame_ed P μ fd (RawFamilyEnlarge.enlarge fd C)
    (RawFamilyEnlarge.admissible P fd C hC) vs xs hfit).symm
  rw [RawFamilyEnlarge.enlarge, if_neg h0]
  exact mem_insert.mpr (Or.inl Equiv.rfl)

private theorem spike_not_leaf (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (vs : List Nat) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length) :
    RawFamilyEnlarge.spike (C vs (key xs)) ∉ leaf P μ fd C vs xs := by
  intro hz
  have hfit := leaf_fits P μ fd C vs xs hl _ hz
  exact RawFamilyEnlarge.spike_fresh (C vs (key xs))
    (mem_congr_right (apply_ofFrame_ed P μ fd C hC vs xs hfit) hz)

/-- Interpreting an already-constructed telescope does not read the global
constant table. Its domain and leaf sets are kept literally fixed. -/
theorem erasedType_table (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) {I : Type v} {m : Nat}
    (t : RecTel.{4,v} I m) (X : I → PSet.{4}) :
    t.erasedType (mkM P μ) X = t.erasedType (mkM P ν) X := by
  induction t with
  | ret _ => rfl
  | pi A B ih =>
      change piVal (mkM P μ) (tyv A) (fun a =>
        tyv (classFiber A (fun q => Ed (mkM P μ) ((B q).erasedType (mkM P μ) X)) a)) =
        piVal (mkM P ν) (tyv A) (fun a =>
          tyv (classFiber A (fun q => Ed (mkM P ν) ((B q).erasedType (mkM P ν) X)) a))
      have he : (fun q => Ed (mkM P μ) ((B q).erasedType (mkM P μ) X)) =
          (fun q => Ed (mkM P ν) ((B q).erasedType (mkM P ν) X)) := by
        funext q
        exact congrArg (Ed (mkM P μ)) (ih q)
      exact congrArg (fun F => piVal (mkM P μ) (tyv A)
        (fun a => tyv (classFiber A F a))) he

/-- At the supplied positive DATA stage, actual membership and equality
of the original and enlarged field element sets force the complete path
type to be empty. Unflattening constructs the fresh nested assignment. -/
theorem no_path_of_equiv (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (vs : List Nat)
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) {m : Nat}
    (t : RecTel.{4,5} (List PSet.{4}) m) (ht : t.DomainsDich)
    (hl : ∀ p, (t.result p).length = (fd.params ++ fd.indices).length)
    (x : PSet.{4}) (hx : x ∈ Ed (mkM P μ) (t.erasedType (mkM P μ) (leaf P μ fd C vs)))
    (he : Equiv (Ed (mkM P μ) (t.erasedType (mkM P μ) (leaf P μ fd C vs)))
      (Ed (mkM P μ) (t.erasedType (mkM P μ)
        (leaf P μ fd (RawFamilyEnlarge.enlarge fd C) vs)))) :
    ∀ p : t.tel.Path, False := by
  let M := mkM P μ
  let D := RawFamilyEnlarge.enlarge fd C
  let f : PiTel.Value.{4,5} t.tel (fun _ => PSet.{4}) :=
    t.tel.unflatten (fun p => RawFamilyEnlarge.spike (C vs (key (t.result p))))
  have hX : ∀ xs, Dich (leaf P μ fd C vs xs) := fun _ => dich_ed M _
  have hY : ∀ xs, Dich (leaf P μ fd D vs xs) := fun _ => dich_ed M _
  have hr := (t.erasedRead_spec M ht (leaf P μ fd C vs) hX hx).1
  have hf : t.Rel (leaf P μ fd D vs) f := by
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    simpa only [f, PiTel.flatten_unflatten] using
      spike_leaf_mem P μ fd C hC vs h0 (t.result p) (hl p) _
      ((PiTel.all_iff _ _ _).mp hr p)
  have hy := t.erasedEncode_mem M ht (leaf P μ fd D vs) hY f hf
  have hc := (t.erasedEncode_mem_iff M ht (leaf P μ fd C vs) hX f).mp
    (mem_congr_right he.symm hy)
  intro p
  have hp := (PiTel.all_iff _ _ _).mp hc p
  simp only [f, PiTel.flatten_unflatten] at hp
  exact spike_not_leaf P μ fd C hC vs (t.result p) (hl p) hp

/-- A telescope with no complete path has only the erased empty value,
even when some outer domains themselves are inhabited. -/
theorem empty_of_no_path (M : Interp.{4}) {I : Type v} {m : Nat}
    (t : RecTel.{4,v} I m) (ht : t.DomainsDich)
    (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (hn : ∀ p : t.tel.Path, False) (x : PSet.{4})
    (hx : x ∈ Ed M (t.erasedType M X)) : Equiv x pempty := by
  have hr := t.erasedRead_spec M ht X hX hx
  exact hr.2.trans (PiPropField.encode_empty M t ht _ (fun p => (hn p).elim))

end Rcic.F3.PSet.RecFieldSeparation
