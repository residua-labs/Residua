import rcic.RcicF3RawFamilyIHView
import rcic.RcicF3PiRawMinor
import rcic.RcicF3PiRecPlan

/-!
# Producing the complete field/IH spine

Original field views and the fixed-parameter local recursive map produce all
interleaved Inputs. Every recursive field uses the actual executable IH type
at its admitted depth and the motive's own universe valuation. The recursive
map is required only below the supplied constructor value.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.RawFamilyMinor
open Rcic.Declarative PiIndex RawFamily

theorem instOK_liftFields {E : ResolvedEnv} {σ K : Nat → Nat}
    (Fs : List (Expr Nat)) (hI : ∀ A ∈ Fs, InstOK E σ K A) (a c : Nat) :
    ∀ A ∈ liftFields a Fs c, InstOK E σ K A := by
  induction Fs generalizing c with
  | nil => intro A hA; exact (List.not_mem_nil _ hA).elim
  | cons A Fs ih =>
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · simpa only [InstOK, constInsts_lift] using hI A (List.mem_cons_self _ _)
    · exact ih (fun B hB => hI B (List.mem_cons_of_mem _ hB)) (c + 1) B hB

theorem inputs_of_views (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (σ K : Nat → Nat) (nu : Nat) (hB : FamBounded fd nu)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (h0 : evalTotal σ fd.resLevel ≠ 0) :
    let vs := (canonL nu).map (evalTotal σ)
    let M := mkM P (table P μ fd C)
    ∀ (v : Level) (ps : List PSet.{4}) (hps : ps.length = fd.params.length)
      (mo z : PSet.{4}) (g : PSet.{4} → PSet.{4})
      (hg : ∀ a b, Equiv a b → Equiv (g a) (g b))
      (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
        (policyPi fd.indices (.pi (foldApps (.const fd.fref (canonL nu))
          (policyLocals (fd.params.length + fd.indices.length))) (.sort v)))))
      (hmap : ∀ i y, RawFamilyRec.paramKey ps.length i = key ps →
        MemT y z → y ∈ C vs i → g y ∈
          PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ fd.fref vs)
            mo ps fd.indices (push ps ρ0) i y)
      (E : ResolvedEnv) (n : Nat) (htf : TypeFacts E)
      (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K) (fuel : Nat)
      (ss : List FieldShape) (Fs : List (Expr Nat)) (prior : Nat)
      (hv : PiRawFieldViews.Views E fuel fd.fref nu fd.params.length
        fd.indices.length prior ss Fs)
      (pre : List PSet.{4}) (hpre : pre.length = prior)
      (Tend Mx acc : Expr Nat) (xs : List PSet.{4})
      (hI : ∀ A ∈ Fs, InstOK E σ K A)
      (hMx : den M σ (push pre (push ps ρ0)) Mx = mo)
      (hx : TelFits M σ Fs (push pre (push ps ρ0)) xs)
      (hchild : ∀ x ∈ xs, MemT x z),
    ∃ out, PiRawMinor.Inputs M σ E fuel fd.params.length Mx acc ss
      (policyPi Fs Tend) (push pre (push ps ρ0)) xs (RecPlan.args g ss xs) out := by
  dsimp only
  intro v ps hps mo z g hg hmo hmap E n htf hE hb fuel ss
  let M := mkM P (table P μ fd C)
  have hcl : EnvClosed E := fun r m hm =>
    ⟨(htf r m hm).1, fun b hb => ((htf r m hm).2.2 b hb).1⟩
  induction ss with
  | nil =>
    intro Fs prior hv pre hpre Tend Mx acc xs hI hMx hx hchild
    cases hv with
    | nil prior =>
      cases xs with
      | nil => exact ⟨_, PiRawMinor.Inputs.done Mx acc Tend (push pre (push ps ρ0))⟩
      | cons x xs => exact hx.elim
  | cons s ss ih =>
    intro Fs prior hv pre hpre Tend Mx acc xs hI hMx hx hchild
    cases hv with
    | @cons prior s A ss Fs hh ht =>
      cases xs with
      | nil => exact hx.elim
      | cons x xs =>
        have hIt : ∀ B ∈ Fs, InstOK E σ K B :=
          fun B hB => hI B (List.mem_cons_of_mem _ hB)
        have hct : ∀ y ∈ xs, MemT y z :=
          fun y hy => hchild y (List.mem_cons_of_mem _ hy)
        cases s with
        | nonrecursive =>
          have hpre' : (pre ++ [x]).length = prior + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil, hpre]
          have hMx' : den M σ (push (pre ++ [x]) (push ps ρ0))
              (Rcic.Declarative.lift 0 1 Mx) = mo := by
            rw [push_append]
            exact (den_lift0_push M σ [x] (push pre (push ps ρ0)) Mx).trans hMx
          have hx' : TelFits M σ Fs (push (pre ++ [x]) (push ps ρ0)) xs := by
            rw [push_append]
            exact hx.2
          obtain ⟨out, hout⟩ := ih Fs (prior + 1) ht (pre ++ [x]) hpre' Tend
            (Rcic.Declarative.lift 0 1 Mx)
            (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0))
            xs hIt hMx' hx' hct
          refine ⟨out, PiRawMinor.Inputs.plain x hx.1 ?_⟩
          simpa only [push_append] using hout
        | recursive inner =>
          have hh' : PiRawFieldViews.View E fuel fd.fref nu fd.params.length
              fd.indices.length pre.length A (.recursive inner) := by
            rw [hpre]
            exact hh
          obtain ⟨ihT, hread, hih⟩ := RawFamilyIH.view_builder_mem P μ fd C hC σ K nu hB hf h0
            v ps pre hps mo x z g hg hmo hmap E n htf hE hb fuel inner A Mx hh'
            (hI A (List.mem_cons_self _ _)) hMx hx.1 (hchild x (List.mem_cons_self _ _))
          let ix := ihAtN g inner x
          have hpre' : (pre ++ [x, ix]).length = prior + 2 := by
            simp only [List.length_append, List.length_cons, List.length_nil, hpre]
          have hv' : PiRawFieldViews.Views E fuel fd.fref nu fd.params.length
              fd.indices.length (prior + 2) ss (liftFields 1 Fs 0) := by
            simpa only [Nat.add_assoc] using ht.lift hcl 0 1 (Nat.zero_le _)
          have hMx' : den M σ (push (pre ++ [x, ix]) (push ps ρ0))
              (Rcic.Declarative.lift 0 2 Mx) = mo := by
            rw [push_append]
            exact (den_lift0_push M σ [x, ix] (push pre (push ps ρ0)) Mx).trans hMx
          have hx' : TelFits M σ (liftFields 1 Fs 0)
              (push (pre ++ [x, ix]) (push ps ρ0)) xs := by
            rw [push_append]
            exact (TelFits_liftFields M σ [ix] (vcons x (push pre (push ps ρ0)))
              Fs [] xs).mpr hx.2
          obtain ⟨out, hout⟩ := ih (liftFields 1 Fs 0) (prior + 2) hv'
            (pre ++ [x, ix]) hpre' (Rcic.Declarative.lift Fs.length 1 Tend)
            (Rcic.Declarative.lift 0 2 Mx)
            (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1))
            xs (instOK_liftFields Fs hIt 1 0) hMx' hx' hct
          refine ⟨out, PiRawMinor.Inputs.recursive inner ihT hread x ix hx.1 hih ?_⟩
          rw [lift_policyPi, Nat.zero_add]
          simpa only [push_append] using hout

end Rcic.F3.PSet.RawFamilyMinor
