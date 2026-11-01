import rcic.RcicF3RecFieldSeparation
import rcic.RcicF3PropIota

/-!
# One actual consumer application erases its recursive-field argument

The inputs are the bounded function and argument premises of an actual
application rule, the literal variable lookup, and its successful recursive
field reader. Both original contexts fit the source and enlarged models.
Inhabited normalization supplies the two lookup-type equations internally.

The consumer expression is family-free, so it has the same value in both
models. If that value is nonempty, its graph fixes its exact domain in both
models. The bounded argument derivation then equates the source and enlarged
recursive-field element sets. Reachable-path separation forces the field
to be empty; otherwise the consumer was already empty. In either case the
application agrees with the same consumer applied to pempty.

No family-freeness of the application's expected domain is assumed. This
is a local erasure theorem at actual fitting prefixes, not the still-unpaid
induction producing a domain mask for arbitrary typed syntax or all vectors.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldConsumer
open Rcic.Declarative RawFamily PiIndex

private theorem common_pi_domain (M : Interp.{4}) (g A A' : PSet.{4})
    (B B' : PSet.{4} → PSet.{4})
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (hB' : ∀ a a', Equiv a a' → Equiv (B' a) (B' a'))
    (hg : g ∈ Ed M (piVal M A B)) (hg' : g ∈ Ed M (piVal M A' B'))
    (hn : ¬ Equiv g pempty) : Equiv (Ed M A) (Ed M A') := by
  have h := mem_congr_right (ed_piVal M A B hB) hg
  have h' := mem_congr_right (ed_piVal M A' B' hB') hg'
  cases M.dec (PiProp M A B) with
  | isTrue hp =>
      rw [cond_pos hp] at h
      exact (hn (mem_tv.mp h).2).elim
  | isFalse hp =>
      rw [cond_neg hp] at h
      cases M.dec (PiProp M A' B') with
      | isTrue hp' =>
          rw [cond_pos hp'] at h'
          exact (hn (mem_tv.mp h').2).elim
      | isFalse hp' =>
          rw [cond_neg hp'] at h'
          exact ext fun a =>
            ⟨fun ha => piSet_dom (fun x y e => ed_congr M (hB' x y e))
              (fun x y e => ed_congr M (hB x y e)) h' h ha,
             fun ha => piSet_dom (fun x y e => ed_congr M (hB x y e))
              (fun x y e => ed_congr M (hB' x y e)) h h' ha⟩

/-- Actual lookup membership pays normalization. The resulting semantic
telescope retains the reader's domains and complete leaf argument list. -/
theorem lookup_field_eq (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (X : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd X)) σ K E n)
    (hb : BodiesOK E σ K) (ρ : Nat → PSet.{4})
    (hρ : Fits (mkM P (table P μ fd X)) σ Γ ρ)
    (k : Nat) (T : Expr Nat) (hlook : lookupType Γ k = some T)
    (ar fuel : Nat) (ds args : List (Expr Nat))
    (hw : piTelescopeFuel E fuel T = some (ds, foldApps (.const fd.fref (canonL ar)) args))
    (hI : InstOK E σ K T)
    (hds : ∀ A ∈ ds, occursConst fd.fref A = false)
    (hargs : ∀ a ∈ args, occursConst fd.fref a = false) :
    let t := PiSyntaxCompile.compile (mkM P μ) σ (PiIndependent.leafArgs P μ σ args) ds ρ
    Equiv (Ed (mkM P μ) (t.erasedType (mkM P μ)
      (RecFieldSeparation.leaf P μ fd X ((canonL ar).map (evalTotal σ)))))
      (Ed (mkM P (table P μ fd X)) (den (mkM P (table P μ fd X)) σ ρ T)) := by
  dsimp only
  let M := mkM P μ
  let MX := mkM P (table P μ fd X)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P μ σ args) ds ρ
  have hx : ρ k ∈ Ed MX (den MX σ ρ T) :=
    sound_ty (P.good MX rfl) hE (HasTyT.bvar Γ k T hlook) True.intro ρ hρ
  have hn := den_piTelescope_of_mem MX σ K hE hb fuel T ds
    (foldApps (.const fd.fref (canonL ar)) args) ρ (ρ k) hw hI hx
  have hc := PiIndependent.recursiveField_ed P μ fd.fref (ofFrame P μ fd X) σ
    (canonL ar) ds args hds hargs ρ
  change Equiv (Ed M (t.erasedType MX
      (RecFieldSeparation.leaf P μ fd X ((canonL ar).map (evalTotal σ)))))
    (Ed MX (den MX σ ρ (policyPi ds (foldApps (.const fd.fref (canonL ar)) args)))) at hc
  rw [RecFieldSeparation.erasedType_table P (table P μ fd X) μ t] at hc
  exact hc.trans (ed_congr MX hn)

/-- The actual bounded application-rule premises imply local argument
erasure. The original context, full valuation and complete family key are
unchanged. Neither the expected Pi domain nor its codomain is assumed clean. -/
theorem consumer_erasure (P : Premises4)
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
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (g A B : Expr Nat) (hg : occursConst fd.fref g = false)
    (dg : HasTyT E n Γ g (.pi A B)) (hdg : LOKt σ 4 K dg)
    (dx : HasTyT E n Γ (.bvar k) A) (hdx : LOKt σ 4 K dx) :
    let MC := mkM P (table P μ fd C)
    (Equiv (den MC σ ρ g) pempty ∨ Equiv (ρ k) pempty) ∧
      Equiv (den MC σ ρ (.app g (.bvar k))) (fapp (den MC σ ρ g) pempty) := by
  dsimp only
  let M := mkM P μ
  let D := RawFamilyEnlarge.enlarge fd C
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd D)
  let vs := (canonL ar).map (evalTotal σ)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P μ σ args) ds ρ
  have hNormC := lookup_field_eq P μ fd C σ K hEC hb ρ hρC k T hlook ar fuel ds args hw hI hds hargs
  have hNormD := lookup_field_eq P μ fd D σ K hED hb ρ hρD k T hlook ar fuel ds args hw hI hds hargs
  dsimp only at hNormC hNormD
  have hlookup : ρ k ∈ Ed MC (den MC σ ρ T) :=
    sound_ty (P.good MC rfl) hEC (HasTyT.bvar Γ k T hlook) True.intro ρ hρC
  have hx : ρ k ∈ Ed M (t.erasedType M (RecFieldSeparation.leaf P μ fd C vs)) :=
    mem_congr_right hNormC.symm hlookup
  have hcase : Equiv (den MC σ ρ g) pempty ∨ Equiv (ρ k) pempty := by
    cases P.dec (Equiv (den MC σ ρ g) pempty) with
    | isTrue he => exact Or.inl he
    | isFalse hn =>
        have hgC := sound_ty (P.good MC rfl) hEC dg hdg ρ hρC
        have hgD := sound_ty (P.good MD rfl) hED dg hdg ρ hρD
        have hgEq : den MC σ ρ g = den MD σ ρ g :=
          PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
            (ofFrame P μ fd D) σ g hg ρ
        have hgD' : den MC σ ρ g ∈ Ed M (piVal M (den MD σ ρ A)
            (fun a => den MD σ (vcons a ρ) B)) := by
          rw [hgEq]
          exact hgD
        have hDom := common_pi_domain M (den MC σ ρ g) (den MC σ ρ A) (den MD σ ρ A)
          (fun a => den MC σ (vcons a ρ) B) (fun a => den MD σ (vcons a ρ) B)
          (den_resp MC σ ρ B) (den_resp MD σ ρ B) hgC hgD' hn
        have hconvC := BoundedBVar.lookup_equiv P (table P μ fd C) σ K hEC
          hlook dx hdx ρ hρC
        have hconvD := BoundedBVar.lookup_equiv P (table P μ fd D) σ K hED
          hlook dx hdx ρ hρD
        have he : Equiv (Ed M (t.erasedType M (RecFieldSeparation.leaf P μ fd C vs)))
            (Ed M (t.erasedType M (RecFieldSeparation.leaf P μ fd D vs))) :=
          hNormC.trans ((ed_congr MC hconvC).trans
            (hDom.trans ((ed_congr MD hconvD).symm.trans hNormD.symm)))
        have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ
          (PiIndependent.leafArgs P μ σ args) ds ρ
        have hl : ∀ p, (t.result p).length = (fd.params ++ fd.indices).length :=
          PiPropField.compile_result_property M σ (PiIndependent.leafArgs P μ σ args)
            (fun xs => xs.length = (fd.params ++ fd.indices).length)
            (fun _ => (List.length_map _ _).trans hlen) ds ρ
        have hnone := RecFieldSeparation.no_path_of_equiv P μ fd C hC vs h0 t ht hl (ρ k) hx he
        exact Or.inr (RecFieldSeparation.empty_of_no_path M t ht
          (RecFieldSeparation.leaf P μ fd C vs) (fun _ => dich_ed M _) hnone (ρ k) hx)
  refine ⟨hcase, ?_⟩
  rcases hcase with he | he
  · exact ((fapp_congr he Equiv.rfl).trans (fapp_pempty (ρ k))).trans
      ((fapp_congr he Equiv.rfl).trans (fapp_pempty pempty)).symm
  · exact fapp_congr Equiv.rfl he

end Rcic.F3.PSet.RecFieldConsumer
