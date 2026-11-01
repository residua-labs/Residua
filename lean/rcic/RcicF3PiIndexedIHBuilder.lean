import rcic.RcicF3PiIndexedIH
import rcic.RcicF3PiRawIHAny
import rcic.RcicF3PiIndependentField
import rcic.RcicF3PiLeafParams

/-!
# Indexed IHs in the executable any-sort builder

This Prop-field component uses actual normalized domains and complete keys.
Its recursive map is required only at reached leaf keys, preserving the
fixed parameter slice. The normalized field and leaf-map premises remain
explicit; universal Eval existence and the original-field producer are open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawIHAny
open Rcic.Declarative PiIndex

/-- Produce the executable IH expression and membership at the actual motive sort. -/
theorem indexed_builder_mem (M : Interp.{4}) (hU : M.U = U W4)
    (σ : Nat → Nat) (f : Nat) (ls : List Level)
    (endVal : (Nat → PSet.{4}) → PSet.{4}) (hEnd : EnvResp endVal)
    (w v : Level) (Ps Is : List (Expr Nat)) (ps : List PSet.{4})
    (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (ls.map (evalTotal σ)))
      (piLam M σ endVal ρ0 (policyPi (Ps ++ Is) (.sort w))))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls)
        (policyLocals (Ps.length + Is.length))) (.sort v)))))
    (E : ResolvedEnv) (fuel : Nat) (A : Expr Nat)
    (ds args : List (Expr Nat)) (ha : args.length = (Ps ++ Is).length)
    (ρ : Nat → PSet.{4})
    (hprefix : ∀ xs, TelFits M σ ds ρ xs →
      (args.take Ps.length).map (den M σ (push xs ρ)) = ps)
    (Mx : Expr Nat) (hMx : den M σ ρ (Rcic.Declarative.lift 0 1 Mx) = mo)
    (hread : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const f ls) args))
    (hProp : ∀ ys, ys.length = args.length → ∀ z,
      z ∈ Ed M (fapps (M.μ f (ls.map (evalTotal σ))) ys) → Equiv z pempty)
    (hx : ρ 0 ∈ Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) :
    let F := M.μ f (ls.map (evalTotal σ))
    let t := PiIndex.tel M σ ds args ρ
    let C := PiRawMotiveAny.guarded M σ (evalTotal σ v) F mo ps Is (push ps ρ0)
    ∀ (recMap : Index.{4} → PSet.{4} → PSet.{4}),
      (∀ p x, x ∈ proofFibre M F (t.result p) →
        recMap (t.result p) x ∈ C (t.result p) x) →
      ∃ ih, funIHType E fuel Ps.length A Mx ds.length = some ih ∧
        t.indexedIH M recMap (ρ 0) ∈ Ed M (den M σ ρ ih) := by
  dsimp only
  intro recMap hmap
  let F := M.μ f (ls.map (evalTotal σ))
  let t := PiIndex.tel M σ ds args ρ
  let X := proofFibre M F
  let C := PiRawMotiveAny.guarded M σ (evalTotal σ v) F mo ps Is (push ps ρ0)
  have hL : ∀ τ, Equiv (X (key (args.map (den M σ τ))))
      (Ed M (den M σ τ (foldApps (.const f ls) args))) := by
    intro τ
    rw [den_foldApps]
    exact proofFibre_key M F (args.map (den M σ τ))
      (fun ys hys z hz => hProp ys (by simpa only [List.length_map] using hys) z hz)
  have hfield : Equiv (Ed M (t.erasedType M X))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) :=
    PiIndependent.compile_ed M σ (read M σ args) X (proofFibre_dich M F)
      (foldApps (.const f ls) args) hL ds ρ
  have hxf := mem_congr_right hfield.symm hx
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ (read M σ args) ds ρ
  let S : Index.{4} → Prop := fun i => ∃ p, t.result p = i
  have hs : ∀ p, S (t.result p) := fun p => ⟨p, rfl⟩
  have hmapS : ∀ i x, S i → x ∈ X i → recMap i x ∈ C i x := by
    rintro i x ⟨p, rfl⟩ hxi
    exact hmap p x hxi
  have hmem := t.indexedIH_mem_scoped M ht X (proofFibre_dich M F)
    C (PiRawMotiveAny.guarded_dich M σ (evalTotal σ v) F mo ps Is (push ps ρ0))
    recMap S hs hmapS hxf
  let ih := policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length
    (Rcic.Declarative.lift 0 1 Mx)) (args.drop Ps.length ++ [PiRawIH.fieldApp ds.length]))
  have hih : funIHType E fuel Ps.length A Mx ds.length = some ih :=
    PiRawIH.funIHType_eq E fuel Ps.length A Mx ds args f ls hread
  have he := builder_spec M hU σ f ls endVal hEnd w v Ps Is ps hps hF mo hmo
    E fuel A ds args ha ρ hprefix Mx hMx hread ih hih hx
  exact ⟨ih, hih, mem_congr_right (ed_congr M he) hmem⟩

/-- Actual normalized readback restricts the recursive map to its parameter slice. -/
theorem indexed_map_at_parameters (M : Interp.{4}) (σ : Nat → Nat)
    (ds args : List (Expr Nat)) (ρ : Nat → PSet.{4}) (ps : List PSet.{4})
    (hp : ∀ xs, TelFits M σ ds ρ xs →
      (args.take ps.length).map (den M σ (push xs ρ)) = ps)
    (X : Index.{4} → PSet.{4}) (C : Index.{4} → PSet.{4} → PSet.{4})
    (g : Index.{4} → PSet.{4} → PSet.{4})
    (hmap : ∀ i x, RawFamilyRec.paramKey ps.length i = key ps →
      x ∈ X i → g i x ∈ C i x) :
    ∀ p x, x ∈ X ((tel M σ ds args ρ).result p) →
      g ((tel M σ ds args ρ).result p) x ∈ C ((tel M σ ds args ρ).result p) x :=
  fun p x hx => hmap _ x (PiLeafParams.result_parameters M σ ds args ρ ps hp p) hx

end Rcic.F3.PSet.PiRawIHAny
