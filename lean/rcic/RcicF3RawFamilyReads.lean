import rcic.RcicF3RawFamily
import rcic.RcicF3RoleTable

/-!
# Read congruence of the raw intersection role

Ported from #8474 at 194a2cf433fcc81ecf190d1c0f2950b24a378fc7.
The core read law imports RoleTable directly; the historical RoleModel
AdmittedReads adapter belongs to the later checked-consumer integration.
The planned-table composition is in RcicF3RawFamilyPlanReads.

For each fixed candidate frame, agreement of the ambient tables transports
the literal constructor predicate. The admissible closed frames therefore
give the same intersection. No closure, smallness, or shape premise is
required. This supplies the read law only; `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex

theorem ofFrame_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices)) (C : Frame) (vs : List Nat) :
    ofFrame P μ fd C vs = ofFrame P ν fd C vs := by
  unfold ofFrame
  rw [mkM_eq_withμ, mkM_eq_withμ]
  exact piLam_agree _ _ _ _ (fun r hr => h r (famType_refs fd hp r hr)) _

theorem table_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices)) (C : Frame) :
    AgreeOn (table P μ fd C) (table P ν fd C) (fun r => S r ∨ r = fd.fref) := by
  intro r hr vs
  by_cases he : r = fd.fref
  · subst r
    rw [table, table, upd_eq, upd_eq]
    exact ofFrame_agreeOn P h fd hp C vs
  · rw [table, table, upd_ne μ fd.fref _ he, upd_ne ν fd.fref _ he]
    exact h r (hr.resolve_right he) vs

theorem smallAlong_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (σ : Nat → Nat) (W : PSet.{4}) :
    ∀ Ds, RefsIn S Ds → ∀ (ρ : Nat → PSet.{4}) xs,
      SmallAlong (mkM P μ) σ W Ds ρ xs ↔ SmallAlong (mkM P ν) σ W Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil => intro _ ρ xs; rfl
  | cons A Ds ih =>
    intro hb ρ xs
    cases xs with
    | nil => rfl
    | cons x xs =>
      show (Ed (mkM P μ) (den (mkM P μ) σ ρ A) ∈ W ∧ _) ↔
        (Ed (mkM P ν) (den (mkM P ν) σ ρ A) ∈ W ∧ _)
      rw [den_agreeOn P h σ A (hb A (List.mem_cons_self _ _)) ρ]
      exact and_congr Iff.rfl (ih (fun e he => hb e (List.mem_cons_of_mem _ he))
        (vcons x ρ) xs)

theorem ctorAt_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (C : Frame) (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) :
    CtorAt P μ fd C vs i z ↔ CtorAt P ν fd C vs i z := by
  have ht := table_agreeOn P h fd hp C
  have hparams : RefsIn (fun r => S r ∨ r = fd.fref) fd.params :=
    fun e he r hr => Or.inl (hp e (List.mem_append_left _ he) r hr)
  unfold CtorAt
  apply exists_congr
  intro j
  apply exists_congr
  intro ps
  apply exists_congr
  intro xs
  have hj : fd.ctors.get j ∈ fd.ctors := List.get_mem _ j.val j.isLt
  rw [TelFits_agreeOn P ht _ _ hparams,
    TelFits_agreeOn P ht _ _ (hc _ hj).1,
    map_den_agreeOn P ht _ _ (hc _ hj).2]
  by_cases hl : evalTotal (σOf vs) fd.resLevel = 0
  · simp only [hl, ite_true]
  · simp only [hl, ite_false]
    rw [smallAlong_agreeOn P ht _ _ _ (hc _ hj).1]

theorem closed_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd) (C : Frame) :
    Closed P μ fd C ↔ Closed P ν fd C := by
  constructor
  · intro hC vs i z hz
    exact hC vs i z ((ctorAt_agreeOn P h fd hp hc C vs i z).mpr hz)
  · intro hC vs i z hz
    exact hC vs i z ((ctorAt_agreeOn P h fd hp hc C vs i z).mp hz)

theorem inAll_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) :
    InAll P μ fd vs i z ↔ InAll P ν fd vs i z := by
  constructor
  · intro hz C hA hC
    exact hz C hA ((closed_agreeOn P h fd hp hc C).mpr hC)
  · intro hz C hA hC
    exact hz C hA ((closed_agreeOn P h fd hp hc C).mp hC)

theorem frame_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd) :
    frame P μ fd = frame P ν fd := by
  have hi : InAll P μ fd = InAll P ν fd :=
    funext fun vs => funext fun i => funext fun z =>
      propext (inAll_agreeOn P h fd hp hc vs i z)
  unfold frame
  rw [hi]

theorem role_agreeOn (P : Premises4)
    {μ ν : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : AgreeOn μ ν S) (fd : FamData)
    (hp : RefsIn S (fd.params ++ fd.indices))
    (hc : FamRefsIn (fun r => S r ∨ r = fd.fref) fd) (vs : List Nat) :
    role P μ fd vs = role P ν fd vs := by
  unfold role
  rw [frame_agreeOn P h fd hp hc]
  exact ofFrame_agreeOn P h fd hp _ vs

theorem familyReads (P : Premises4) (fd : FamData) :
    RoleModel.FamilyReads role P fd := by
  intro μ ν S h hp hc vs
  rw [role_agreeOn P h fd hp hc vs]
  exact Equiv.rfl

/-- Direct specialization of the universal family law to any role context. -/
theorem familyReadsCtx (P : Premises4) (ctx : Nat → Role) :
    RoleModel.FamilyReadsCtx role P ctx :=
  fun _ fd _ => familyReads P fd

end Rcic.F3.PSet.RawFamily
