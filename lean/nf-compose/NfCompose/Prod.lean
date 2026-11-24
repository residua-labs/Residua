import NfCompose.Basic

/-!
Product: both components run, both must admit. A refusal is tagged by stage.
When both refuse, both residues are kept. `prod_active_iff` is the image of a
pair map. `prod_profile` needs no hypothesis beyond the two profiles.
-/

namespace NfCompose

open MSTNecessityExecModelMWE

inductive ProdResidue (R1 R2 : Type) where
  | stage1 (r : R1)
  | stage2 (r : R2)
  | both (r1 : R1) (r2 : R2)
  deriving DecidableEq

inductive ProdRep (P1 P2 : Type) where
  | both (p1 : P1) (p2 : P2)
  deriving DecidableEq

inductive ProdOutcome (O1 O2 : Type) where
  | both (o1 : O1) (o2 : O2)
  deriving DecidableEq

def prodRhoOf {R1 R2 : Type} (a1 a2 : Bool) (rho1 : Option R1) (rho2 : Option R2) :
    Option (ProdResidue R1 R2) :=
  match a1, a2 with
  | false, false =>
      match rho1, rho2 with
      | some x, some y => some (.both x y)
      | some x, none => some (.stage1 x)
      | none, some y => some (.stage2 y)
      | none, none => none
  | false, true => rho1.map .stage1
  | true, false => rho2.map .stage2
  | true, true => none

def prodSigmaOf {P1 P2 : Type} (s1 : Option P1) (s2 : Option P2) :
    Option (ProdRep P1 P2) :=
  match s1, s2 with
  | some p1, some p2 => some (.both p1 p2)
  | _, _ => none

variable (M1 M2 : ExecModel)

def prodModel : ExecModel where
  Raw := M1.Raw × M2.Raw
  Class := M1.Class × M2.Class
  Rep := ProdRep M1.Rep M2.Rep
  Residue := ProdResidue M1.Residue M2.Residue
  Outcome := ProdOutcome M1.Outcome M2.Outcome
  q := fun r => (M1.q r.1, M2.q r.2)
  evalRaw := fun r => .both (M1.evalRaw r.1) (M2.evalRaw r.2)
  evalClass := fun c => .both (M1.evalClass c.1) (M2.evalClass c.2)
  admissible := fun c => M1.admissible c.1 && M2.admissible c.2
  rho := fun c => prodRhoOf (M1.admissible c.1) (M2.admissible c.2) (M1.rho c.1) (M2.rho c.2)
  sigma := fun c => prodSigmaOf (M1.sigma c.1) (M2.sigma c.2)

theorem prod_active_iff (c1 : M1.Class) (c2 : M2.Class) :
    activeClass (prodModel M1 M2) (c1, c2) ↔ activeClass M1 c1 ∧ activeClass M2 c2 := by
  constructor
  · rintro ⟨r, hr⟩
    rcases r with ⟨r1, r2⟩
    exact ⟨⟨r1, congrArg Prod.fst hr⟩, ⟨r2, congrArg Prod.snd hr⟩⟩
  · rintro ⟨⟨r1, h1⟩, ⟨r2, h2⟩⟩
    exact ⟨(r1, r2), Prod.ext h1 h2⟩

theorem prod_profile (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2) :
    hasMSTNFProfile (prodModel M1 M2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    rcases r with ⟨r1, r2⟩
    simp only [prodModel]
    rw [h1.1 r1, h2.1 r2]
  · intro c rep hs
    rcases c with ⟨c1, c2⟩
    cases h1s : M1.sigma c1 with
    | none => simp [prodModel, prodSigmaOf, h1s] at hs
    | some p1 =>
        cases h2s : M2.sigma c2 with
        | none => simp [prodModel, prodSigmaOf, h1s, h2s] at hs
        | some p2 =>
            have a1 := h1.2.1 c1 p1 h1s
            have a2 := h2.2.1 c2 p2 h2s
            simp [prodModel, a1, a2]
  · intro c hc hadm
    rcases c with ⟨c1, c2⟩
    have ⟨hc1, hc2⟩ := (prod_active_iff M1 M2 c1 c2).mp hc
    cases ha1 : M1.admissible c1 <;> cases ha2 : M2.admissible c2
    · have hr1 := h1.2.2.1 c1 hc1 ha1
      have hr2 := h2.2.2.1 c2 hc2 ha2
      cases hρ1 : M1.rho c1 <;> cases hρ2 : M2.rho c2
      · exact absurd hρ1 hr1
      · exact absurd hρ1 hr1
      · exact absurd hρ2 hr2
      · intro hnone
        simp [prodModel, prodRhoOf, ha1, ha2, hρ1, hρ2] at hnone
    · have hr1 := h1.2.2.1 c1 hc1 ha1
      cases hρ1 : M1.rho c1 with
      | none => exact absurd hρ1 hr1
      | some _ =>
          intro hnone
          simp [prodModel, prodRhoOf, ha1, ha2, hρ1] at hnone
    · have hr2 := h2.2.2.1 c2 hc2 ha2
      cases hρ2 : M2.rho c2 with
      | none => exact absurd hρ2 hr2
      | some _ =>
          intro hnone
          simp [prodModel, prodRhoOf, ha1, ha2, hρ2] at hnone
    · have : (prodModel M1 M2).admissible (c1, c2) = true := by
        simp [prodModel, ha1, ha2]
      cases hadm.symm.trans this
  · intro c hc hadm
    rcases c with ⟨c1, c2⟩
    have ⟨hc1, hc2⟩ := (prod_active_iff M1 M2 c1 c2).mp hc
    have hadmAnd : (M1.admissible c1 && M2.admissible c2) = true := by
      simpa [prodModel] using hadm
    have ⟨ha1, ha2⟩ := bool_and_true hadmAnd
    have hs1 := h1.2.2.2 c1 hc1 ha1
    have hs2 := h2.2.2.2 c2 hc2 ha2
    cases h1s : M1.sigma c1 with
    | none => exact absurd h1s hs1
    | some _ =>
        cases h2s : M2.sigma c2 with
        | none => exact absurd h2s hs2
        | some _ =>
            intro hnone
            simp [prodModel, prodSigmaOf, h1s, h2s] at hnone

end NfCompose
