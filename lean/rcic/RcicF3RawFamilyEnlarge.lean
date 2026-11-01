import rcic.RcicF3RawFamilyInduction
import rcic.RcicF3RawFamilyView
import rcic.RcicF3PiIndependent
import rcic.RcicF3LimDef
import rcic.RcicF3BoundedBVar

/-!
# Strict admissible enlargements of data fibres

Each data fibre is enlarged by a data value containing that entire fibre.
Well-founded membership excludes this value from the original fibre.
Finite set closure preserves the exact stage, and proof fibres are left
unchanged. This construction uses no choice and no constructor closure.

At a complete fitting family application, the two interpretations cannot
both identify the fresh family head with the same family-free expression.
Actual bounded conversion soundness therefore excludes such a conversion
when the same original local environment fits both candidate models.

This is a bounded head-separation component. It does not produce fitting
of an erased context, remove earlier recursive locals from a domain, or
construct a common small DATA signature. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyEnlarge
open Rcic.Declarative RawFamily PiIndex

/-- A constructor code containing its source set as an actual field. -/
def spike (S : PSet.{4}) : PSet.{4} := dataVal 0 [S]

theorem spike_fresh (S : PSet.{4}) : spike S ∉ S := by
  intro hs
  have hbelow : MemT S (spike S) :=
    memT_dataVal (List.mem_singleton_self S)
  have hirr : ∀ z : PSet.{4}, ¬ MemT z z := by
    intro z
    induction z using memT_wf.induction with
    | h z ih => intro hzz; exact ih z hzz hzz
  exact hirr S (.tail hbelow hs)

theorem spike_mem_stage {W S : PSet.{4}} (hW : Stage W) (hS : S ∈ W) :
    spike S ∈ W := by
  change ordPair pempty (ordPair (ord 0) (ordPair S pempty)) ∈ W
  exact hW.ordPair_mem hW.empty
    (hW.ordPair_mem (ord_mem_stage hW 0) (hW.ordPair_mem hS hW.empty))

/-- This changes every data fibre at its full key and universe vector.
The proof face remains literally the supplied frame. -/
def enlarge (fd : FamData) (C : Frame) : Frame := fun vs i =>
  if evalTotal (σOf vs) fd.resLevel = 0 then C vs i
  else insert (spike (C vs i)) (C vs i)

theorem frame_sub (fd : FamData) (C : Frame) : FrameSub C (enlarge fd C) := by
  intro vs i z hz
  unfold enlarge
  split
  · exact hz
  · exact mem_insert.mpr (Or.inr hz)

/-- Admissibility is produced at all universe vectors and all full keys;
there is no requirement that the starting frame be constructor-closed. -/
theorem admissible (P : Premises4) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) : Admissible fd (enlarge fd C) := by
  intro vs i
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · simpa only [enlarge, if_pos h0] using hC vs i
  · have hW := stageW4 P (evalTotal (σOf vs) fd.resLevel)
    have hs := spike_mem_stage hW (hC vs i).1
    have hm : insert (spike (C vs i)) (C vs i) ∈
        W4 (evalTotal (σOf vs) fd.resLevel) := by
      apply hW.subset (hW.sUnion (hW.pair (hW.singleton_mem hs) (hC vs i).1))
      intro z hz
      rcases mem_insert.mp hz with hz | hz
      · exact mem_sUnion.mpr ⟨singleton (spike (C vs i)),
          mem_pair.mpr (Or.inl Equiv.rfl), mem_singleton.mpr hz⟩
      · exact mem_sUnion.mpr ⟨C vs i, mem_pair.mpr (Or.inr Equiv.rfl), hz⟩
    have hface := (hC vs i).2
    rw [if_neg h0] at hface
    refine ⟨?_, ?_⟩
    · simpa only [enlarge, if_neg h0] using hm
    · simp only [enlarge, if_neg h0]
      intro z hz he
      rcases mem_insert.mp hz with hz | hz
      · exact dataVal_ne_pempty 0 [C vs i] (hz.symm.trans he)
      · exact hface z hz he

theorem strict (fd : FamData) (C : Frame) (vs : List Nat) (i : Index.{4})
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    ¬ Equiv (C vs i) (enlarge fd C vs i) := by
  intro he
  have hz : spike (C vs i) ∈ enlarge fd C vs i := by
    rw [enlarge, if_neg h0]
    exact mem_insert.mpr (Or.inl Equiv.rfl)
  exact spike_fresh (C vs i) (mem_congr_right he.symm hz)

/-- The literal family application reads the unchanged complete key.
Only its argument expressions are required to be family-free. -/
theorem application_read (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (ar : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (args : List (Expr Nat))
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ))) :
    Equiv (Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) σ ρ
        (foldApps (.const fd.fref (canonL ar)) args)))
      (C ((canonL ar).map (evalTotal σ))
        (key (args.map (den (mkM P μ) σ ρ)))) := by
  change Equiv (Ed (mkM P (upd μ fd.fref (ofFrame P μ fd C)))
    (den (mkM P (upd μ fd.fref (ofFrame P μ fd C))) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args))) _
  rw [den_recApp P μ (ofFrame P μ fd C) σ ρ ha]
  exact apply_ofFrame_ed P μ fd C hC _ _ hfit

private theorem clean_equations_false (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (ar : Nat) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) (args : List (Expr Nat)) (A : Expr Nat)
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (hA : occursConst fd.fref A = false)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ)))
    (hCeq : Equiv (den (mkM P (table P μ fd C)) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args))
      (den (mkM P (table P μ fd C)) σ ρ A))
    (hDeq : Equiv (den (mkM P (table P μ fd (enlarge fd C))) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args))
      (den (mkM P (table P μ fd (enlarge fd C))) σ ρ A)) : False := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (enlarge fd C))
  have hc := (application_read P μ fd C hC ar σ ρ args ha hfit).symm.trans
    (ed_congr MC hCeq)
  have hd := (application_read P μ fd (enlarge fd C) (admissible P fd C hC)
    ar σ ρ args ha hfit).symm.trans (ed_congr MD hDeq)
  have he : Equiv (Ed MC (den MC σ ρ A)) (Ed MD (den MD σ ρ A)) := by
    have hden := PiIndependent.den_free P μ fd.fref
      (ofFrame P μ fd C) (ofFrame P μ fd (enlarge fd C)) σ A hA ρ
    change den MC σ ρ A = den MD σ ρ A at hden
    change Equiv (Ed (mkM P μ) (den MC σ ρ A))
      (Ed (mkM P μ) (den MD σ ρ A))
    rw [hden]
    exact Equiv.rfl
  exact strict fd C _ _ h0 (hc.trans (he.trans hd.symm))

/-- An actual bounded type-conversion chain is incompatible with a clean
target at the same original context fitting both admissible models. The
two context fits are explicit here; no local-context erasure is inferred. -/
theorem no_clean_type_conversion (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (ar : Nat) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (enlarge fd C))) σ K E n)
    (ρ : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (enlarge fd C))) σ Γ ρ)
    (args : List (Expr Nat)) (A : Expr Nat)
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (hA : occursConst fd.fref A = false)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ)))
    (d : TyConvT E n Γ (foldApps (.const fd.fref (canonL ar)) args) A)
    (hd : BoundedBVar.Bounded σ 4 K d) : False := by
  exact clean_equations_false P μ fd C hC ar σ ρ args A ha hA h0 hfit
    (BoundedBVar.chain_sound P (table P μ fd C) σ K hEC ρ hρC d hd)
    (BoundedBVar.chain_sound P (table P μ fd (enlarge fd C)) σ K hED ρ hρD d hd)

/-- Variable inversion supplies the bounded chain internally, from the
actual lookup and typing derivation. No conversion witness is assumed. -/
theorem no_clean_variable_type (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (ar : Nat) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (enlarge fd C))) σ K E n)
    (ρ : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (enlarge fd C))) σ Γ ρ)
    (args : List (Expr Nat)) (A : Expr Nat)
    (ha : ∀ e ∈ args, occursConst fd.fref e = false)
    (hA : occursConst fd.fref A = false)
    (h0 : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0)
    (hfit : TelFits (mkM P μ) (σOf ((canonL ar).map (evalTotal σ)))
      (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ)))
    (k : Nat) (hlook : lookupType Γ k =
      some (foldApps (.const fd.fref (canonL ar)) args))
    (d : HasTyT E n Γ (.bvar k) A) (hd : LOKt σ 4 K d) : False := by
  obtain ⟨c, hc⟩ := BoundedBVar.extract_of_lookup σ 4 K hlook d hd
  exact no_clean_type_conversion P μ fd C hC ar σ K hEC hED ρ hρC hρD
    args A ha hA h0 hfit c hc

end Rcic.F3.PSet.RawFamilyEnlarge
