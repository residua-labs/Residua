import rcic.RcicF3PropEval
import rcic.RcicF3RawFamilyMinorInputs

/-!
# Interleaved evaluation inputs from certified recursive heads

The finite spine carries the same ordinary field tuple in the raw and
candidate interpretations. Each inserted IH is skipped by the lifted
original fields in both models. The recursive-head packet remains an
explicit intermediate callback; its concrete extractor/builder producer
and original-field certificates must be composed before this is a
candidate constructor-step theorem. No evaluation totality is asserted.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- Literal non-tail obligations of Inputs.recursive. -/
def RecursivePacket (C : Context) (fuel inner : Nat)
    (A Mx : Expr Nat) (ρ : Nat → PSet.{4}) (x : PSet.{4}) : Prop :=
  ∃ (ihT : Expr Nat) (ih : PSet.{4}) (ds args : List (Expr Nat)),
    funIHType C.node.E0 fuel C.node.a.family.parameters.length A Mx inner = some ihT ∧
    ih ∈ Ed C.M (den C.M C.σ (vcons x ρ) ihT) ∧
    piTelescopeFuel C.node.E0 fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const C.node.a.family.ref
        (canonL C.node.a.family.member.arity)) args) ∧
    ds.length = inner ∧
    args.length = C.node.a.family.parameters.length + C.node.a.family.indices.length ∧
    ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      Eval C (key (args.map (den C.M C.σ (push zs (vcons x ρ))))) (fapps ih zs)

/-- A structural list of original-field certificates. The certificate itself
may retain the original normalization evidence and the clean reader facts. -/
def FieldCertificates (Cert : Nat → Expr Nat → FieldShape → Prop) :
    Nat → List FieldShape → List (Expr Nat) → Prop
  | _, [], [] => True
  | prior, s :: ss, A :: Fs =>
      Cert prior A s ∧ FieldCertificates Cert (prior + 1) ss Fs
  | _, _, _ => False

theorem FieldCertificates.lift
    (Cert : Nat → Expr Nat → FieldShape → Prop)
    (hLift : ∀ prior A s c a, c ≤ prior → Cert prior A s →
      Cert (prior + a) (Rcic.Declarative.lift c a A) s) :
    ∀ (ss : List FieldShape) (Fs : List (Expr Nat)) (prior : Nat),
      FieldCertificates Cert prior ss Fs → ∀ (c a : Nat), c ≤ prior →
      FieldCertificates Cert (prior + a) ss (liftFields a Fs c) := by
  intro ss
  induction ss with
  | nil =>
      intro Fs prior hcert c a _
      cases Fs with
      | nil => trivial
      | cons A Fs => exact hcert.elim
  | cons s ss ih =>
      intro Fs prior hcert c a hc
      cases Fs with
      | nil => exact hcert.elim
      | cons A Fs =>
          change Cert (prior + a) (Rcic.Declarative.lift c a A) s ∧
            FieldCertificates Cert (prior + a + 1) ss (liftFields a Fs (c + 1))
          refine ⟨hLift prior A s c a hc hcert.1, ?_⟩
          have hr := ih Fs (prior + 1) hcert.2 (c + 1) a (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 a] using hr

/-- A supplied local head producer is assembled into the actual mutual
Inputs relation. Candidate IH membership is never assumed: inserted raw
IH values are skipped by the lifted ordinary fields in the candidate model.
The later concrete callback must derive its child evaluations from the
guarded candidate; this structural theorem does not do that derivation. -/
theorem inputs_of_certified_views (C : Context) (Mc : Interp.{4})
    (S : ResolvedEnv) (K : Nat → Nat) (fuel : Nat)
    (hcl : EnvClosed C.node.E0) (ps : List PSet.{4})
    (Cert : Nat → Expr Nat → FieldShape → Prop)
    (hCertLift : ∀ prior A s c a, c ≤ prior → Cert prior A s →
      Cert (prior + a) (Rcic.Declarative.lift c a A) s)
    (hPacket : ∀ (prior : Nat) (A : Expr Nat) (inner : Nat),
      PiRawFieldViews.View C.node.E0 fuel C.node.a.family.ref
        C.node.a.family.member.arity C.node.a.family.parameters.length
        C.node.a.family.indices.length prior A (.recursive inner) →
      Cert prior A (.recursive inner) →
      ∀ (pre : List PSet.{4}), pre.length = prior → ∀ (Mx : Expr Nat) (x : PSet.{4}),
      InstOK S C.σ K A →
      den C.M C.σ (push pre (push ps ρ0)) Mx = C.motive →
      x ∈ Ed C.M (den C.M C.σ (push pre (push ps ρ0)) A) →
      x ∈ Ed Mc (den Mc C.σ (push pre (push ps ρ0)) A) →
      RecursivePacket C fuel inner A Mx (push pre (push ps ρ0)) x) :
    ∀ (ss : List FieldShape) (Fs : List (Expr Nat)) (prior : Nat),
      PiRawFieldViews.Views C.node.E0 fuel C.node.a.family.ref
        C.node.a.family.member.arity C.node.a.family.parameters.length
        C.node.a.family.indices.length prior ss Fs →
      FieldCertificates Cert prior ss Fs →
      ∀ (pre : List PSet.{4}), pre.length = prior →
      ∀ (Tend Mx acc : Expr Nat) (xs : List PSet.{4}),
      (∀ A ∈ Fs, InstOK S C.σ K A) →
      den C.M C.σ (push pre (push ps ρ0)) Mx = C.motive →
      TelFits C.M C.σ Fs (push pre (push ps ρ0)) xs →
      TelFits Mc C.σ Fs (push pre (push ps ρ0)) xs →
      ∃ ys out, Inputs C fuel Mx acc ss (policyPi Fs Tend)
        (push pre (push ps ρ0)) xs ys out := by
  intro ss
  induction ss with
  | nil =>
      intro Fs prior hv hcert pre hpre Tend Mx acc xs hI hMx hx hc
      cases hv with
      | nil prior =>
          cases xs with
          | nil => exact ⟨[], _, Inputs.done fuel Mx acc Tend (push pre (push ps ρ0))⟩
          | cons x xs => exact hx.elim
  | cons s ss ih =>
      intro Fs prior hv hcert pre hpre Tend Mx acc xs hI hMx hx hc
      cases hv with
      | @cons prior s A ss Fs hh ht =>
          cases xs with
          | nil => exact hx.elim
          | cons x xs =>
              have hIt : ∀ B ∈ Fs, InstOK S C.σ K B :=
                fun B hB => hI B (List.mem_cons_of_mem _ hB)
              cases s with
              | nonrecursive =>
                  have hpre' : (pre ++ [x]).length = prior + 1 := by
                    simp only [List.length_append, List.length_cons, List.length_nil, hpre]
                  have hMx' : den C.M C.σ (push (pre ++ [x]) (push ps ρ0))
                      (Rcic.Declarative.lift 0 1 Mx) = C.motive := by
                    rw [push_append]
                    exact (den_lift0_push C.M C.σ [x] (push pre (push ps ρ0)) Mx).trans hMx
                  have hx' : TelFits C.M C.σ Fs (push (pre ++ [x]) (push ps ρ0)) xs := by
                    rw [push_append]
                    exact hx.2
                  have hc' : TelFits Mc C.σ Fs (push (pre ++ [x]) (push ps ρ0)) xs := by
                    rw [push_append]
                    exact hc.2
                  obtain ⟨ys, out, hout⟩ := ih Fs (prior + 1) ht hcert.2
                    (pre ++ [x]) hpre' Tend (Rcic.Declarative.lift 0 1 Mx)
                    (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0))
                    xs hIt hMx' hx' hc'
                  refine ⟨x :: ys, out, Inputs.plain x hx.1 ?_⟩
                  simpa only [push_append] using hout
              | recursive inner =>
                  obtain ⟨ihT, ix, ds, args, hread, hih, hscan, hdepth, hargc, hchildren⟩ :=
                    hPacket prior A inner hh hcert.1 pre hpre Mx x
                      (hI A (List.mem_cons_self _ _)) hMx hx.1 hc.1
                  have hpre' : (pre ++ [x, ix]).length = prior + 2 := by
                    simp only [List.length_append, List.length_cons, List.length_nil, hpre]
                  have hv' : PiRawFieldViews.Views C.node.E0 fuel C.node.a.family.ref
                      C.node.a.family.member.arity C.node.a.family.parameters.length
                      C.node.a.family.indices.length (prior + 2) ss (liftFields 1 Fs 0) := by
                    simpa only [Nat.add_assoc] using ht.lift hcl 0 1 (Nat.zero_le _)
                  have hcert' : FieldCertificates Cert (prior + 2) ss (liftFields 1 Fs 0) := by
                    simpa only [Nat.add_assoc] using
                      FieldCertificates.lift Cert hCertLift ss Fs (prior + 1) hcert.2 0 1
                        (Nat.zero_le _)
                  have hMx' : den C.M C.σ (push (pre ++ [x, ix]) (push ps ρ0))
                      (Rcic.Declarative.lift 0 2 Mx) = C.motive := by
                    rw [push_append]
                    exact (den_lift0_push C.M C.σ [x, ix] (push pre (push ps ρ0)) Mx).trans hMx
                  have hx' : TelFits C.M C.σ (liftFields 1 Fs 0)
                      (push (pre ++ [x, ix]) (push ps ρ0)) xs := by
                    rw [push_append]
                    exact (TelFits_liftFields C.M C.σ [ix]
                      (vcons x (push pre (push ps ρ0))) Fs [] xs).mpr hx.2
                  have hc' : TelFits Mc C.σ (liftFields 1 Fs 0)
                      (push (pre ++ [x, ix]) (push ps ρ0)) xs := by
                    rw [push_append]
                    exact (TelFits_liftFields Mc C.σ [ix]
                      (vcons x (push pre (push ps ρ0))) Fs [] xs).mpr hc.2
                  obtain ⟨ys, out, hout⟩ := ih (liftFields 1 Fs 0) (prior + 2) hv' hcert'
                    (pre ++ [x, ix]) hpre' (Rcic.Declarative.lift Fs.length 1 Tend)
                    (Rcic.Declarative.lift 0 2 Mx)
                    (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1))
                    xs (RawFamilyMinor.instOK_liftFields Fs hIt 1 0) hMx' hx' hc'
                  refine ⟨x :: ix :: ys, out,
                    Inputs.recursive inner ihT hread x ix hx.1 hih
                      ds args hscan hdepth hargc hchildren ?_⟩
                  rw [lift_policyPi, Nat.zero_add]
                  simpa only [push_append] using hout

end Rcic.F3.PSet.PropEval
