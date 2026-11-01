import rcic.RcicF3PiSmallFrame
import rcic.RcicF3RawFamilyInduction

/-!
# A separate pointwise nonvacuous intersection

This is an alternative DATA-family interpretation, not a change to
RawFamily.frame, NormRole, StepAG, or either checked condition.  A local
candidate is closed at one canonical family world.  The intersection is
explicitly empty when that local candidate class is empty.  This differs
semantically from the existing global InAll interpretation.

The auxiliary embedding places a local fibre at precisely its canonical
world and is empty elsewhere.  It lets the existing constructor operator
and produced monotonicity be reused without assuming an all-world closed
candidate.  No numeric bound selects a world or changes admission.

Smallness is unconditional; local closure still requires a locally small
closed candidate.  Production of those candidates at the bounded worlds
needed by the checked tier is a separate, unpaid obligation.  Full keys,
constructor values, and the exact W4 stage are retained. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseData
open Rcic.Declarative PiIndex RawFamily

abbrev Fibre := Index.{4} → PSet.{4}

def AdmissibleAt (fd : FamData) (w : List Nat) (X : Fibre) : Prop :=
  ∀ i, X i ∈ W4 (evalTotal (σOf w) fd.resLevel) ∧
    (if evalTotal (σOf w) fd.resLevel = 0 then
      ∀ z, z ∈ X i → Equiv z pempty
    else ∀ z, z ∈ X i → ¬ Equiv z pempty)

/-- An auxiliary globally admissible frame, with no numeric world guard. -/
noncomputable def embed (ar : Nat) (w : List Nat) (X : Fibre) : Frame :=
  fun vs i => if PiSmallFrame.canonical ar vs = w then X i else pempty

theorem embed_at (ar : Nat) (w : List Nat)
    (hw : PiSmallFrame.canonical ar w = w) (X : Fibre) (i : Index.{4}) :
    embed ar w X w i = X i := by
  simp [embed, hw]

theorem embed_sub (ar : Nat) (w : List Nat) (X Y : Fibre)
    (h : ∀ i, Sub (X i) (Y i)) : FrameSub (embed ar w X) (embed ar w Y) := by
  intro vs i z hz
  by_cases hw : PiSmallFrame.canonical ar vs = w
  · simp only [embed, if_pos hw] at hz ⊢
    exact h i z hz
  · simp only [embed, if_neg hw] at hz
    exact (not_mem_pempty hz).elim

theorem embed_admissible (P : Premises4) (fd : FamData) (ar : Nat)
    (hB : FamBounded fd ar) (w : List Nat) (X : Fibre)
    (hX : AdmissibleAt fd w X) : Admissible fd (embed ar w X) := by
  intro vs i
  by_cases hw : PiSmallFrame.canonical ar vs = w
  · have hk := evalTotal_agree (PiSmallFrame.canonical_agree ar vs)
      fd.resLevel hB.res
    rw [hw] at hk
    simpa only [embed, if_pos hw, hk] using hX i
  · simp only [embed, if_neg hw]
    refine ⟨(stageW4 P _).empty, ?_⟩
    by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
    · rw [if_pos h0]
      exact fun _ hz => (not_mem_pempty hz).elim
    · rw [if_neg h0]
      exact fun _ hz => (not_mem_pempty hz).elim

def ClosedAt (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) (X : Fibre) : Prop :=
  ∀ i z, CtorAt P μ fd (embed ar w X) w i z → z ∈ X i

def ExistsAt (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) : Prop :=
  ∃ X : Fibre, AdmissibleAt fd w X ∧ ClosedAt P μ fd ar w X

def InAllAt (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) (i : Index.{4}) (z : PSet.{4}) : Prop :=
  ∀ X : Fibre, AdmissibleAt fd w X → ClosedAt P μ fd ar w X → z ∈ X i

/-- The explicit existence conjunct makes the empty local class empty. -/
noncomputable def localFrame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) : Fibre :=
  fun i => sep (fun z => ExistsAt P μ fd ar w ∧ InAllAt P μ fd ar w i z)
    (W4 (evalTotal (σOf w) fd.resLevel))

theorem inAllAt_resp (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) (i : Index.{4})
    {z z' : PSet.{4}} (he : Equiv z z') :
    InAllAt P μ fd ar w i z ↔ InAllAt P μ fd ar w i z' := by
  exact ⟨fun h X hX hc => mem_congr_left he (h X hX hc),
    fun h X hX hc => mem_congr_left he.symm (h X hX hc)⟩

/-- The local separating carrier adds no membership condition when the
local candidate class is inhabited. No candidate is selected as data. -/
theorem local_mem_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) (i : Index.{4}) (z : PSet.{4}) :
    z ∈ localFrame P μ fd ar w i ↔
      ExistsAt P μ fd ar w ∧ InAllAt P μ fd ar w i z := by
  constructor
  · intro hz
    obtain ⟨a, h, he⟩ := mem_sep.mp hz
    exact ⟨h.1, (inAllAt_resp P μ fd ar w i he).mp h.2⟩
  · intro h
    obtain ⟨X, hX, hc⟩ := h.1
    obtain ⟨a, ha⟩ := (stageW4 P _).trans (hX i).1 (h.2 X hX hc)
    exact mem_sep.mpr ⟨a, ⟨⟨X, hX, hc⟩,
      (inAllAt_resp P μ fd ar w i ha.symm).mp h.2⟩, ha⟩

theorem local_empty (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat)
    (hn : ¬ ExistsAt P μ fd ar w) (i : Index.{4}) :
    Equiv (localFrame P μ fd ar w i) pempty := by
  apply ext
  intro z
  exact ⟨fun hz => (hn ((local_mem_iff P μ fd ar w i z).mp hz).1).elim,
    fun hz => (not_mem_pempty hz).elim⟩

theorem local_least (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) (X : Fibre)
    (hX : AdmissibleAt fd w X) (hc : ClosedAt P μ fd ar w X)
    (i : Index.{4}) : Sub (localFrame P μ fd ar w i) (X i) := by
  intro z hz
  exact ((local_mem_iff P μ fd ar w i z).mp hz).2 X hX hc

/-- Smallness is unconditional, including worlds whose local candidate
class is empty. The decision operation is supplied Premises4 data. -/
theorem local_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (w : List Nat) :
    AdmissibleAt fd w (localFrame P μ fd ar w) := by
  intro i
  refine ⟨?_, ?_⟩
  · cases P.dec (ExistsAt P μ fd ar w) with
    | isTrue h =>
        obtain ⟨X, hX, hc⟩ := h
        exact (stageW4 P _).subset (hX i).1
          (local_least P μ fd ar w X hX hc i)
    | isFalse hn =>
        exact mem_congr_left (local_empty P μ fd ar w hn i).symm
          (stageW4 P _).empty
  · by_cases h0 : evalTotal (σOf w) fd.resLevel = 0
    · rw [if_pos h0]
      intro z hz
      obtain ⟨hex, hall⟩ := (local_mem_iff P μ fd ar w i z).mp hz
      obtain ⟨X, hX, hc⟩ := hex
      have hf := (hX i).2
      rw [if_pos h0] at hf
      exact hf z (hall X hX hc)
    · rw [if_neg h0]
      intro z hz
      obtain ⟨hex, hall⟩ := (local_mem_iff P μ fd ar w i z).mp hz
      obtain ⟨X, hX, hc⟩ := hex
      have hf := (hX i).2
      rw [if_neg h0] at hf
      exact hf z (hall X hX hc)

/-- Every universe vector reads the local intersection at its canonical
family world. Canonicalization does not bound any universe value. -/
noncomputable def frame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) : Frame :=
  fun vs => localFrame P μ fd ar (PiSmallFrame.canonical ar vs)

theorem frame_canonical (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (vs : List Nat) :
    frame P μ fd ar (PiSmallFrame.canonical ar vs) = frame P μ fd ar vs := by
  simp only [frame, PiSmallFrame.canonical_idem]

/-- Global admissibility no longer requires global candidate inhabitation. -/
theorem frame_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar) :
    Admissible fd (frame P μ fd ar) := by
  intro vs i
  have hk := evalTotal_agree (PiSmallFrame.canonical_agree ar vs)
    fd.resLevel hB.res
  simpa only [frame, hk] using
    local_admissible P μ fd ar (PiSmallFrame.canonical ar vs) i

/-- This separate family value has an explicit arity argument. It is not
an instance of the existing arity-free FamilyValue interface. -/
noncomputable def role (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (vs : List Nat) : PSet.{4} :=
  ofFrame P μ fd (frame P μ fd ar) vs

theorem role_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar) (vs : List Nat) :
    role P μ fd ar vs ∈ Ed (mkM P μ)
      (den (mkM P μ) (σOf vs) ρ0 (famType fd)) :=
  ofFrame_mem P μ fd (frame P μ fd ar) (frame_admissible P μ fd ar hB) vs

theorem constructor_mono_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hmono : ConstructorMono P μ fd) (w : List Nat) (X Y : Fibre)
    (hX : AdmissibleAt fd w X) (hY : AdmissibleAt fd w Y)
    (hsub : ∀ i, Sub (X i) (Y i)) (i : Index.{4}) (z : PSet.{4})
    (hz : CtorAt P μ fd (embed ar w X) w i z) :
    CtorAt P μ fd (embed ar w Y) w i z :=
  hmono _ _ (embed_admissible P fd ar hB w X hX)
    (embed_admissible P fd ar hB w Y hY) (embed_sub ar w X Y hsub) w i z hz

/-- Only this one local candidate class is required for closure here. -/
theorem local_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hmono : ConstructorMono P μ fd) (w : List Nat)
    (hex : ExistsAt P μ fd ar w) :
    ClosedAt P μ fd ar w (localFrame P μ fd ar w) := by
  intro i z hz
  apply (local_mem_iff P μ fd ar w i z).mpr
  refine ⟨hex, ?_⟩
  intro X hX hc
  exact hc i z (constructor_mono_at P μ fd ar hB hmono w _ X
    (local_admissible P μ fd ar w) hX
    (local_least P μ fd ar w X hX hc) i z hz)

noncomputable def restrictAt (X : Fibre) (Q : Index.{4} → PSet.{4} → Prop) : Fibre :=
  fun i => sep (Q i) (X i)

theorem restrictAt_admissible (P : Premises4) (fd : FamData) (w : List Nat)
    (X : Fibre) (hX : AdmissibleAt fd w X) (Q : Index.{4} → PSet.{4} → Prop) :
    AdmissibleAt fd w (restrictAt X Q) := by
  intro i
  refine ⟨(stageW4 P _).subset (hX i).1 (fun _ hz => mem_sep_subset hz), ?_⟩
  by_cases h0 : evalTotal (σOf w) fd.resLevel = 0
  · rw [if_pos h0]
    have hf := (hX i).2
    rw [if_pos h0] at hf
    exact fun z hz => hf z (mem_sep_subset hz)
  · rw [if_neg h0]
    have hf := (hX i).2
    rw [if_neg h0] at hf
    exact fun z hz => hf z (mem_sep_subset hz)

/-- Induction retains the entire key and actual output value. The step
uses the embedded property-restricted local frame. -/
theorem local_induction (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hmono : ConstructorMono P μ fd) (w : List Nat)
    (Q : Index.{4} → PSet.{4} → Prop)
    (hQ : ∀ i z z', Equiv z z' → Q i z → Q i z')
    (hstep : ∀ i z, CtorAt P μ fd
      (embed ar w (restrictAt (localFrame P μ fd ar w) Q)) w i z → Q i z) :
    ∀ i z, z ∈ localFrame P μ fd ar w i → Q i z := by
  intro i z hz
  have hex := ((local_mem_iff P μ fd ar w i z).mp hz).1
  let L := localFrame P μ fd ar w
  let R := restrictAt L Q
  have hL : AdmissibleAt fd w L := local_admissible P μ fd ar w
  have hR : AdmissibleAt fd w R := restrictAt_admissible P fd w L hL Q
  have hsub : ∀ k, Sub (R k) (L k) := fun _ _ hx => mem_sep_subset hx
  have hcL : ClosedAt P μ fd ar w L := local_closed P μ fd ar hB hmono w hex
  have hcR : ClosedAt P μ fd ar w R := by
    intro k x hx
    have hmem := hcL k x (constructor_mono_at P μ fd ar hB hmono w R L
      hR hL hsub k x hx)
    obtain ⟨a, ha⟩ := hmem
    exact mem_sep.mpr ⟨a, hQ k x _ ha.symm (hstep k x hx), ha⟩
  obtain ⟨a, hqa, ha⟩ := mem_sep.mp (local_least P μ fd ar w R hR hcR i z hz)
  exact hQ i _ z ha hqa

/-- Members have a literal constructor presentation even though no
candidate existence hypothesis is supplied: membership itself supplies it. -/
theorem local_dense (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hmono : ConstructorMono P μ fd) (w : List Nat) :
    ∀ i z, z ∈ localFrame P μ fd ar w i →
      CtorAt P μ fd (embed ar w (localFrame P μ fd ar w)) w i z := by
  apply local_induction P μ fd ar hB hmono w
    (fun i z => CtorAt P μ fd (embed ar w (localFrame P μ fd ar w)) w i z)
    (fun i _ _ he hz => ctorAt_resp P μ fd _ w i he hz)
  intro i z hz
  exact constructor_mono_at P μ fd ar hB hmono w _ _
    (restrictAt_admissible P fd w _ (local_admissible P μ fd ar w) _)
    (local_admissible P μ fd ar w) (fun _ _ hm => mem_sep_subset hm) i z hz

end Rcic.F3.PSet.PointwiseData
