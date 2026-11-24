import NfCompose.Basic

/-!
Tagged dependent sum of pinned `ExecModel`s.

This is `ProfileFamily.compositeModel` with the `active` field deleted:
carriers are `Sigma`, `q` and `eval` keep the tag, `sigma` and `rho` are
`Option.map (Sigma.mk tag)`. `sum_active_iff` is the image fact the Bool
field was standing in for. `sum_profile` needs no hypothesis beyond the
component profiles, because `activeClass` is derived from `q`.
-/

namespace NfCompose

open MSTNecessityExecModelMWE

variable {ι : Type} (F : ι → ExecModel)

def sumModel : ExecModel where
  Raw := Σ i, (F i).Raw
  Class := Σ i, (F i).Class
  Rep := Σ i, (F i).Rep
  Residue := Σ i, (F i).Residue
  Outcome := Σ i, (F i).Outcome
  q := fun raw => ⟨raw.1, (F raw.1).q raw.2⟩
  evalRaw := fun raw => ⟨raw.1, (F raw.1).evalRaw raw.2⟩
  evalClass := fun cls => ⟨cls.1, (F cls.1).evalClass cls.2⟩
  admissible := fun cls => (F cls.1).admissible cls.2
  rho := fun cls => ((F cls.1).rho cls.2).map (Sigma.mk cls.1)
  sigma := fun cls => ((F cls.1).sigma cls.2).map (Sigma.mk cls.1)

theorem sum_active_iff (i : ι) (c : (F i).Class) :
    activeClass (sumModel F) ⟨i, c⟩ ↔ activeClass (F i) c := by
  constructor
  · rintro ⟨raw, hr⟩
    rcases raw with ⟨j, r⟩
    have hj : j = i := congrArg Sigma.fst hr
    subst hj
    exact ⟨r, sigma_eq_snd hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨i, r⟩, Sigma.ext rfl (heq_of_eq hr)⟩

theorem sum_profile (h : ∀ i, hasMSTNFProfile (F i)) :
    hasMSTNFProfile (sumModel F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro raw
    rcases raw with ⟨i, r⟩
    exact Sigma.ext rfl (heq_of_eq ((h i).1 r))
  · intro cls rep hs
    rcases cls with ⟨i, c⟩
    cases hsig : (F i).sigma c with
    | none =>
        have hnone : (sumModel F).sigma ⟨i, c⟩ = none := by
          simp [sumModel, hsig]
        cases hnone.symm.trans hs
    | some crep =>
        exact (h i).2.1 c crep hsig
  · intro cls hc hadm
    rcases cls with ⟨i, c⟩
    have hca := (sum_active_iff F i c).mp hc
    have hrho := (h i).2.2.1 c hca hadm
    cases hr : (F i).rho c with
    | none => exact absurd hr hrho
    | some _ =>
        intro hnone
        simp [sumModel, hr] at hnone
  · intro cls hc hadm
    rcases cls with ⟨i, c⟩
    have hca := (sum_active_iff F i c).mp hc
    have hsig := (h i).2.2.2 c hca hadm
    cases hs : (F i).sigma c with
    | none => exact absurd hs hsig
    | some _ =>
        intro hnone
        simp [sumModel, hs] at hnone

end NfCompose
