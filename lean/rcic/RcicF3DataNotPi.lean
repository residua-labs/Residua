import rcic.RcicF3RawFamilyEnlarge
import rcic.RcicF3PropIota

/-!
# DATA values cannot be members of semantic Pi types

A data value contains the singleton of the empty set. Every member of a
function graph is an ordered pair, and no ordered pair contains the empty
set. The proof face of a Pi contains only the empty proof value, which is
also distinct from every data value. This argument includes empty domains.

The admissible enlargement therefore separates a complete fitting DATA
family head from an arbitrary Pi type in one model. The target Pi's domain
and codomain may read the family and the entire original local environment.
Actual bounded variable inversion then excludes applications of a local
whose literal lookup type is that family head.

The semantic argument still consumes an actual fitting original context,
a fitting complete key, and the actual conversion bound. It does not
produce a recursive-local domain mask or an all-universe small signature.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.DataNotPi
open Rcic.Declarative RawFamily PiIndex
universe u

private theorem empty_not_mem_ordPair (a b : PSet.{u}) :
    pempty ∉ ordPair a b := by
  intro h
  rcases mem_pair.mp h with hs | hp
  · have ha : a ∈ singleton a := mem_singleton.mpr Equiv.rfl
    exact not_mem_pempty (mem_congr_right hs.symm ha)
  · have ha : a ∈ pair a b := mem_pair.mpr (Or.inl Equiv.rfl)
    exact not_mem_pempty (mem_congr_right hp.symm ha)

/-- The actual graph-membership characterization excludes every data tag,
without any assumption that the function domain is inhabited. -/
theorem dataVal_not_piSet (j : Nat) (xs : List PSet.{u})
    (A : PSet.{u}) (B : PSet.{u} → PSet.{u})
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) :
    dataVal j xs ∉ piSet A B := by
  intro h
  have htag : singleton pempty ∈ dataVal j xs :=
    mem_pair.mpr (Or.inl Equiv.rfl)
  obtain ⟨a, _, b, _, he⟩ := (isFuncOnDep_of_mem_piSet hB h).2.1 _ htag
  exact empty_not_mem_ordPair a b
    (mem_congr_right he (mem_singleton.mpr Equiv.rfl))

/-- Both semantic Pi branches are covered, including an erased proposition
and a graph on an empty domain. No typehood premise is needed. -/
theorem dataVal_not_piVal (M : Interp.{u}) (j : Nat) (xs : List PSet.{u})
    (A : PSet.{u}) (B : PSet.{u} → PSet.{u})
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) :
    dataVal j xs ∉ Ed M (piVal M A B) := by
  intro h
  have h' := mem_congr_right (ed_piVal M A B hB) h
  cases M.dec (PiProp M A B) with
  | isTrue hp =>
      rw [cond_pos hp] at h'
      exact dataVal_ne_pempty j xs (mem_tv.mp h').2
  | isFalse hp =>
      rw [cond_neg hp] at h'
      exact dataVal_not_piSet j xs (Ed M A) (fun a => Ed M (B a))
        (fun a a' ha => ed_congr M (hB a a' ha)) h'

/-- Only the enlarged model is used for conversion soundness. The full
canonical family vector and full argument key are retained; no restriction
is placed on the target Pi domain or codomain. -/
theorem no_pi_type_conversion (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (ar : Nat) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      σ K E n)
    (ρ : Nat → PSet.{4})
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (args : List (Expr Nat)) (A B : Expr Nat)
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ)))
    (d : TyConvT E n Γ (foldApps (.const fd.fref (canonL ar)) args) (.pi A B))
    (hd : BoundedBVar.Bounded σ 4 K d) : False := by
  let vs := (canonL ar).map (evalTotal σ)
  let i := key (args.map (den (mkM P μ) σ ρ))
  let D := RawFamilyEnlarge.enlarge fd C
  let M := mkM P (table P μ fd D)
  have hz : RawFamilyEnlarge.spike (C vs i) ∈ D vs i := by
    change RawFamilyEnlarge.spike (C vs i) ∈ RawFamilyEnlarge.enlarge fd C vs i
    rw [RawFamilyEnlarge.enlarge, if_neg h0]
    exact mem_insert.mpr (Or.inl Equiv.rfl)
  have hf : RawFamilyEnlarge.spike (C vs i) ∈
      Ed M (den M σ ρ (foldApps (.const fd.fref (canonL ar)) args)) :=
    mem_congr_right
      (RawFamilyEnlarge.application_read P μ fd D
        (RawFamilyEnlarge.admissible P fd C hC) ar σ ρ args ha hfit).symm hz
  have hc := BoundedBVar.chain_sound P (table P μ fd D) σ K hED ρ hρD d hd
  have hp := mem_congr_right (ed_congr M hc) hf
  exact dataVal_not_piVal M 0 [C vs i] (den M σ ρ A)
    (fun a => den M σ (vcons a ρ) B) (den_resp M σ ρ B) hp

/-- The bounded conversion is extracted from the actual variable typing.
The target Pi may mention the fresh family and the original locals. -/
theorem no_variable_pi (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (ar : Nat) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      σ K E n)
    (ρ : Nat → PSet.{4})
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (args : List (Expr Nat)) (A B : Expr Nat)
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ)))
    (k : Nat) (hlook : lookupType Γ k =
      some (foldApps (.const fd.fref (canonL ar)) args))
    (d : HasTyT E n Γ (.bvar k) (.pi A B)) (hd : LOKt σ 4 K d) : False := by
  obtain ⟨c, hc⟩ := BoundedBVar.extract_of_lookup σ 4 K hlook d hd
  exact no_pi_type_conversion P μ fd C hC ar σ K hED ρ hρD
    args A B ha h0 hfit c hc

/-- A nonempty application spine headed by this DATA local is impossible.
Both inversions use the original bounded derivation, including conversions
around the whole application and around the variable's function type. -/
theorem no_variable_application (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (ar : Nat) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      σ K E n)
    (ρ : Nat → PSet.{4})
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (args : List (Expr Nat))
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ)))
    (k : Nat) (hlook : lookupType Γ k =
      some (foldApps (.const fd.fref (canonL ar)) args))
    (a : Expr Nat) (as : List (Expr Nat)) (T : Expr Nat)
    (d : HasTyT E n Γ (foldApps (.bvar k) (a :: as)) T)
    (hd : LOKt σ 4 K d) : False := by
  obtain ⟨U, dh, hh⟩ := lok_head σ 4 K as (.app (.bvar k) a) d hd
  obtain ⟨A, B, df, hf⟩ := lok_app_inv_aux σ 4 K dh hh rfl
  exact no_variable_pi P μ fd C hC ar σ K hED ρ hρD args A B
    ha h0 hfit k hlook df hf

end Rcic.F3.PSet.DataNotPi
