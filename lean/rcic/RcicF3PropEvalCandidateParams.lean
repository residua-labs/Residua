import rcic.RcicF3PropEvalCandidate

/-!
# Exact parameter slicing of a guarded candidate constructor

The complete constructor key determines the parameter prefix up to LEq.
That equality transports the actual parameter and dependent-field fits,
while preserving the original field values and the complete result key.
No evaluation existence, candidate closure or constructor monotonicity is
assumed. The theorem is the Prop constructor face used by the indexed
evaluation producer. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidate
open Rcic.Declarative PiIndex RawFamilyRec RawFamily

/-- Replace the constructor's parameter witnesses by the fixed guarded slice.
Dependent result indices are transported, never discarded. -/
theorem ctorAt_parameters (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (X : Frame) (vs : List Nat) (i : Index.{4}) (z : PSet.{4})
    (hc : CtorAt P μ fd X vs i z) (ps₀ : List PSet.{4})
    (hkey : paramKey fd.params.length i = key ps₀)
    (h0 : evalTotal (σOf vs) fd.resLevel = 0) :
    let M := mkM P (table P μ fd X)
    ∃ (j : Fin fd.ctors.length) (xs : List PSet.{4}),
      TelFits M (σOf vs) fd.params ρ0 ps₀ ∧
      TelFits M (σOf vs) (fd.ctors.get j).1 (push ps₀ ρ0) xs ∧
      i = key (ps₀ ++ (fd.ctors.get j).2.map
        (den M (σOf vs) (push xs (push ps₀ ρ0)))) ∧
      Equiv z pempty := by
  dsimp only
  let M := mkM P (table P μ fd X)
  obtain ⟨j, ps, xs, hps, hxs, _, hi, hz⟩ := hc
  have hpsEq : LEq ps ps₀ :=
    paramKey_reflect fd.params.length ps ps₀
      ((fd.ctors.get j).2.map (den M (σOf vs) (push xs (push ps ρ0))))
      hps.length (by rw [← hi]; exact hkey)
  have henv : ∀ k, Equiv (push ps ρ0 k) (push ps₀ ρ0 k) :=
    push_congr hpsEq (fun _ => Equiv.rfl)
  have hps₀ : TelFits M (σOf vs) fd.params ρ0 ps₀ :=
    TelFits_congr M (σOf vs) fd.params (fun _ => Equiv.rfl) hpsEq hps
  have hxs₀ : TelFits M (σOf vs) (fd.ctors.get j).1 (push ps₀ ρ0) xs :=
    TelFits_congr M (σOf vs) (fd.ctors.get j).1 henv (LEq.refl xs) hxs
  have hresult := LEq_map_den M (σOf vs)
    (push_congr (LEq.refl xs) henv) (fd.ctors.get j).2
  refine ⟨j, xs, hps₀, hxs₀,
    hi.trans ((key_eq_iff _ _).mpr (LEq_append hpsEq hresult)), ?_⟩
  simpa only [if_pos h0] using hz

end Rcic.F3.PSet.PropEvalCandidate
