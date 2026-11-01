import rcic.RcicF3PointwiseData
import rcic.RcicF3RawFamilyReads

/-!
# Read congruence of the separate pointwise interpretation

The existing literal constructor read law applies to each fixed embedded
local fibre. Local closed classes, their existence propositions and their
nonvacuous intersections therefore agree. Neither closure nor candidate
inhabitation is assumed. No representative is selected. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseData
open Rcic.Declarative PiIndex RawFamily

theorem closedAt_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (ar : Nat) (w : List Nat) (X : Fibre) :
    ClosedAt P μ fd ar w X ↔ ClosedAt P ν fd ar w X := by
  constructor
  · intro hX i z hz
    exact hX i z ((ctorAt_agreeOn P h fd hp hc (embed ar w X) w i z).mpr hz)
  · intro hX i z hz
    exact hX i z ((ctorAt_agreeOn P h fd hp hc (embed ar w X) w i z).mp hz)

theorem existsAt_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (ar : Nat) (w : List Nat) :
    ExistsAt P μ fd ar w ↔ ExistsAt P ν fd ar w := by
  constructor
  · rintro ⟨X, hX, hcl⟩
    exact ⟨X, hX, (closedAt_agreeOn P h fd hp hc ar w X).mp hcl⟩
  · rintro ⟨X, hX, hcl⟩
    exact ⟨X, hX, (closedAt_agreeOn P h fd hp hc ar w X).mpr hcl⟩

theorem inAllAt_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (ar : Nat) (w : List Nat) (i : Index.{4}) (z : PSet.{4}) :
    InAllAt P μ fd ar w i z ↔ InAllAt P ν fd ar w i z := by
  constructor
  · intro hz X hX hcl
    exact hz X hX ((closedAt_agreeOn P h fd hp hc ar w X).mpr hcl)
  · intro hz X hX hcl
    exact hz X hX ((closedAt_agreeOn P h fd hp hc ar w X).mp hcl)

theorem localFrame_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (ar : Nat) (w : List Nat) : localFrame P μ fd ar w = localFrame P ν fd ar w := by
  have he : ExistsAt P μ fd ar w = ExistsAt P ν fd ar w :=
    propext (existsAt_agreeOn P h fd hp hc ar w)
  have hi : InAllAt P μ fd ar w = InAllAt P ν fd ar w :=
    funext fun i => funext fun z => propext (inAllAt_agreeOn P h fd hp hc ar w i z)
  unfold localFrame
  rw [he, hi]

theorem frame_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd) (ar : Nat) :
    frame P μ fd ar = frame P ν fd ar :=
  funext fun vs => localFrame_agreeOn P h fd hp hc ar (PiSmallFrame.canonical ar vs)

theorem role_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd) (ar : Nat) (vs : List Nat) :
    role P μ fd ar vs = role P ν fd ar vs := by
  unfold role
  rw [frame_agreeOn P h fd hp hc ar]
  exact ofFrame_agreeOn P h fd hp _ vs

end Rcic.F3.PSet.PointwiseData
