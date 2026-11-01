import rcic.RcicF3PropEvalCandidate
import rcic.RcicF3PiCleanViews
import rcic.RcicF3PiTupleMono
import rcic.RcicF3CandidateScope

/-!
# Original constructor fields from the candidate to the raw interpretation

Normalized recursive membership is monotone at complete family arguments.
For an original hidden field, forward normalization uses its actual inhabitant;
reverse normalization uses its original bounded typing at the growing raw
ordinary prefix. The same field values and complete indices are retained.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateFields
open Rcic.Declarative RawFamily PiIndex

theorem normalized_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (X R : Frame) (hX : Admissible fd X) (hR : Admissible fd R)
    (hsub : FrameSub X R)
    (hFamily : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd R vs))
    (σ : Nat → Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst fd.fref e = false)
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (hlen : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4}) :
    Sub (Ed (mkM P (table P μ fd X))
      (den (mkM P (table P μ fd X)) σ ρ
        (policyPi ds (foldApps (.const fd.fref ls) args))))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ
        (policyPi ds (foldApps (.const fd.fref ls) args)))) := by
  have h := PiIndependent.recursiveField_sub_length P μ fd.fref
    (ofFrame P μ fd X) (μ fd.fref) σ ls ds args hd ha ρ (fun xs hx => ?_)
  · rw [PiIndependent.upd_self] at h
    exact h
  · intro z hz
    have hr := apply_ofFrame_sub P μ fd X R hX hR hsub
      (ls.map (evalTotal σ)) xs (hx.trans hlen) z hz
    exact mem_congr_right
      (ed_congr (mkM P μ) (fapps_congr (hFamily _).symm xs)) hr

/-- Pointwise field inclusion only needs the already-built raw prefix. -/
theorem telFits_mono_prefix (Mc M : Interp.{4}) (σ : Nat → Nat) :
    ∀ (Fs : List (Expr Nat)) (ρ : Nat → PSet.{4}),
      (∀ k (hk : k < Fs.length) pre, TelFits M σ (Fs.take k) ρ pre →
        Sub (Ed Mc (den Mc σ (push pre ρ) (Fs[k]'hk)))
          (Ed M (den M σ (push pre ρ) (Fs[k]'hk)))) →
      ∀ xs, TelFits Mc σ Fs ρ xs → TelFits M σ Fs ρ xs := by
  intro Fs
  induction Fs with
  | nil => intro ρ _ xs hx; cases xs <;> exact hx
  | cons A Fs ih =>
      intro ρ h xs hx
      cases xs with
      | nil => exact hx.elim
      | cons x xs =>
          have hxR := h 0 (Nat.succ_pos _) [] trivial x hx.1
          refine ⟨hxR, ih (vcons x ρ) ?_ xs hx.2⟩
          intro k hk pre hpre
          exact h (k + 1) (Nat.succ_lt_succ hk) (x :: pre) ⟨hxR, hpre⟩

/-- The actual clean scan gives the member transport for one original field.
The reverse denotation equality is supplied by the original raw typed prefix. -/
theorem original_field_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (X R : Frame) (hX : Admissible fd X) (hR : Admissible fd R)
    (hsub : FrameSub X R)
    (hFamily : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd R vs))
    (σ K : Nat → Nat) {S E : ResolvedEnv} {n fuel nu : Nat}
    (hBodies : ∀ r ls, transparentBody E r ls = transparentBody S r ls)
    (hES : EnvSound (mkM P (table P μ fd X)) σ K S n) (hb : BodiesOK S σ K)
    (A : Expr Nat) (s : FieldShape)
    (hClean : PiCleanViews.Clean E fuel fd.fref nu fd.params.length fd.indices.length A s)
    (hI : InstOK S σ K A) (ρ : Nat → PSet.{4})
    (hReverse : ∀ ds b, piTelescopeFuel E fuel A = some (ds, b) →
      Equiv (den (mkM P μ) σ ρ (policyPi ds b)) (den (mkM P μ) σ ρ A)) :
    Sub (Ed (mkM P (table P μ fd X)) (den (mkM P (table P μ fd X)) σ ρ A))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A)) := by
  intro x hx
  cases s with
  | nonrecursive =>
      have he := PiIndependent.den_free P μ fd.fref (ofFrame P μ fd X)
        (μ fd.fref) σ A hClean ρ
      rw [PiIndependent.upd_self] at he
      change x ∈ Ed (mkM P μ)
        (den (mkM P (upd μ fd.fref (ofFrame P μ fd X))) σ ρ A) at hx
      rw [he] at hx
      exact hx
  | recursive inner =>
      obtain ⟨ds, args, _, hlen, hread, hd, ha⟩ := hClean
      have hreadS :=
        (CandidateScope.piTelescopeFuel_of_transparentBody_eq hBodies fuel A).symm.trans hread
      have hn := den_piTelescope_of_mem (mkM P (table P μ fd X)) σ K hES hb
        fuel A ds (foldApps (.const fd.fref (canonL nu)) args) ρ x hreadS hI hx
      have hxN := mem_congr_right (ed_congr (mkM P (table P μ fd X)) hn.symm) hx
      have hxR := normalized_sub P μ fd X R hX hR hsub hFamily σ (canonL nu)
        ds args hd ha (by simpa only [List.length_append] using hlen) ρ x hxN
      exact mem_congr_right (ed_congr (mkM P μ) (hReverse _ _ hread)) hxR

end Rcic.F3.PSet.CandidateFields
