import rcic.RcicAnnLR3UnitEqProbe

/-!
# Exact, noncumulative universe membership in the unit probe

The level index is the full `Option Nat` evaluation. A tagged observation
retains that index and an arbitrary payload; payloads are not inspected to
decide a universe. The missing-information bottom may belong to every
universe, so uniqueness also explicitly consumes a full-tag observation.
Canonical sort/Pi codes and the actual Eq probe supply this observation.
This is not the old `TyCodeCT` inclusion of every Prop code into `sort`.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

inductive TagAt (i : Option Nat) : CptI → Prop
  | bot : TagAt i .bot
  | tagged (a payload : CptI) (ha : a = .bot ∨ a = .spine (levelRef i) []) :
      TagAt i (.spine 10 [a, payload])

def SortMember (i : Option Nat) (v : Value) : Prop := ∀ c, v c → TagAt i c

def TypeDefined (v : Value) : Prop :=
  ∃ i payload, v (.spine 10 [.spine (levelRef i) [], payload])

theorem tagAt_full_index {i j : Option Nat} {payload : CptI}
    (h : TagAt i (.spine 10 [.spine (levelRef j) [], payload])) : i = j := by
  cases h with
  | tagged a b ha =>
      rcases ha with h | h
      · cases h
      · have hr : levelRef j = levelRef i := (CptI.spine.inj h).1
        exact (levelRef_injective hr).symm

/-- Same defined value, two ordinary universe memberships: exact equality,
not just equality of their zero bits. -/
theorem sortMember_unique {i j : Option Nat} {v : Value}
    (hi : SortMember i v) (hj : SortMember j v) (hd : TypeDefined v) : i = j := by
  obtain ⟨k, payload, hk⟩ := hd
  exact (tagAt_full_index (hi _ hk)).trans (tagAt_full_index (hj _ hk)).symm

theorem sortMember_congr {i : Option Nat} {v w : Value}
    (h : ValueEq v w) (hv : SortMember i v) : SortMember i w :=
  fun c hc => hv c ((h c).mpr hc)

theorem typeDefined_congr {v w : Value} (h : ValueEq v w) (hv : TypeDefined v) : TypeDefined w := by
  obtain ⟨i,p,hp⟩ := hv
  exact ⟨i,p,(h _).mp hp⟩

theorem typeDefined_nonbottom {v : Value} (h : TypeDefined v) : ¬ ValueEq v bottom := by
  obtain ⟨i,p,hp⟩ := h
  intro he
  have hf := (he _).mp hp
  cases hf

/-- Membership of a tagged code is derived by inversion of the inherited
compositional application semantics, not assigned per source expression. -/
theorem tagged_member (ρ : EnvI) (i : Option Nat) (p : Expr Nat) :
    SortMember i (denI ρ (taggedTerm i p)) := by
  intro c hc
  have h := approxI_foldApps_const_inv (r := 10) (ls := [])
    (xs := [levelTerm i, p]) hc
  rcases h with rfl | ⟨us, he, hs⟩
  · exact .bot
  · cases hs with
    | cons ha hs =>
      cases hs with
      | cons hb hs =>
        cases hs
        subst c
        exact .tagged _ _ (approxI_const_inv ha)

theorem tagged_defined (ρ : EnvI) (i : Option Nat) (p : Expr Nat) :
    TypeDefined (denI ρ (taggedTerm i p)) := by
  refine ⟨i, .bot, ?_⟩
  exact approxI_famApp 10 []
    (.cons (.const ρ (levelRef i) []) (.cons (.bot ρ p) .nil))

theorem sort_member (ρ : EnvI) (i : Option Nat) :
    SortMember (i.map Nat.succ) (denI ρ (sortTerm i)) := tagged_member ρ _ _

theorem sort_defined (ρ : EnvI) (i : Option Nat) :
    TypeDefined (denI ρ (sortTerm i)) := tagged_defined ρ _ _

/-- Different evaluated levels give genuinely different semantic sort
codes, including two distinct positive levels and the undefined index. -/
theorem sort_code_injective {ρ : EnvI} {i j : Option Nat}
    (h : ValueEq (denI ρ (sortTerm i)) (denI ρ (sortTerm j))) : i = j := by
  have hs : i.map Nat.succ = j.map Nat.succ :=
    sortMember_unique (sort_member ρ i)
      (sortMember_congr h.symm (sort_member ρ j)) (sort_defined ρ i)
  cases i with
  | none => cases j <;> first | rfl | cases hs
  | some a =>
    cases j with
    | none => cases hs
    | some b =>
      have hab : Nat.succ a = Nat.succ b := Option.some.inj hs
      exact congrArg some (Nat.succ.inj hab)

theorem sort_values_eq_iff (ρ : EnvI) (i j : Option Nat) :
    ValueEq (denI ρ (sortTerm i)) (denI ρ (sortTerm j)) ↔ i = j :=
  ⟨sort_code_injective, fun h => h ▸ ValueEq.refl _⟩

theorem evaluated_sort_eq_iff_eqN (ρ : EnvI) (u v : Level) :
    (∀ ν : Valuation, InterpretedEq ν ρ (.sort u) (.sort v)) ↔ eqN u v := by
  constructor
  · intro h ν; exact sort_code_injective (h ν)
  · intro h ν
    change ValueEq (denI ρ (sortTerm (eval ν u))) (denI ρ (sortTerm (eval ν v)))
    rw [h ν]
    exact ValueEq.refl _

theorem pi_member (ν : Valuation) (ρ : EnvI) (A B : ExprA) (u v : Level) :
    SortMember (eval ν (.imax u v)) (denote ν ρ (.pi A u B v)) := tagged_member ρ _ _

theorem pi_defined (ν : Valuation) (ρ : EnvI) (A B : ExprA) (u v : Level) :
    TypeDefined (denote ν ρ (.pi A u B v)) := tagged_defined ρ _ _

theorem fixture_parameter_member (ν : Valuation) (ρ : EnvI) :
    SortMember (some 0) (denote ν ρ EqLargeFixture.parameter) := pi_member ν ρ _ _ _ _

theorem fixture_parameter_defined (ν : Valuation) (ρ : EnvI) :
    TypeDefined (denote ν ρ EqLargeFixture.parameter) := pi_defined ν ρ _ _ _ _

theorem fixture_result_member (ν : Valuation) (ρ : EnvI) :
    SortMember (some 1) (denote ν ρ EqLargeFixture.result) := pi_member ν ρ _ _ _ _

theorem fixture_result_defined (ν : Valuation) (ρ : EnvI) :
    TypeDefined (denote ν ρ EqLargeFixture.result) := pi_defined ν ρ _ _ _ _

theorem fixture_result_not_prop (ν : Valuation) (ρ : EnvI) :
    ¬ SortMember (some 0) (denote ν ρ EqLargeFixture.result) := by
  intro hp
  have he := sortMember_unique (fixture_result_member ν ρ) hp (fixture_result_defined ν ρ)
  cases he

theorem fixture_parameter_not_positive (ν : Valuation) (ρ : EnvI) (k : Nat) :
    ¬ SortMember (some (k + 1)) (denote ν ρ EqLargeFixture.parameter) := by
  intro hp
  have he := sortMember_unique (fixture_parameter_member ν ρ) hp (fixture_parameter_defined ν ρ)
  have hz := Option.some.inj he
  omega

/-- Semantic typing and nonbottomness of the actual interpreted open call,
not a hypothetical source-soundness field. -/
theorem fixture_open_member {ν : Valuation} {ρ : EnvI} (hρ : FitsFixture ν ρ) :
    SortMember (some 1) (denote ν ρ (EqLargeFixture.call (.bvar 0))) ∧
    TypeDefined (denote ν ρ (EqLargeFixture.call (.bvar 0))) :=
  ⟨sortMember_congr (open_conversion_sound hρ).symm (fixture_result_member ν ρ),
    typeDefined_congr (open_conversion_sound hρ).symm (fixture_result_defined ν ρ)⟩

theorem fixture_closed_member (ν : Valuation) (ρ : EnvI) :
    SortMember (some 1) (denote ν ρ StrictProofModelBoundary.canonicalCallA3) ∧
    TypeDefined (denote ν ρ StrictProofModelBoundary.canonicalCallA3) :=
  ⟨sortMember_congr (canonical_iota_sound ν ρ).symm (fixture_result_member ν ρ),
    typeDefined_congr (canonical_iota_sound ν ρ).symm (fixture_result_defined ν ρ)⟩

/-- The proof unit is not itself a type-code inhabitant of any universe. -/
theorem unit_not_sort_member (ρ : EnvI) (i : Option Nat) :
    ¬ SortMember i (unitValue ρ) := by
  intro h
  have hc := h unitProbe (unit_observed ρ)
  cases hc

theorem fixture_result_not_unit (ν : Valuation) (ρ : EnvI) :
    ¬ ValueEq (denote ν ρ EqLargeFixture.result) (unitValue ρ) := by
  intro h
  exact unit_not_sort_member ρ (some 1)
    (sortMember_congr h (fixture_result_member ν ρ))

/-- The actual equality domain interprets to its tagged Eq descriptor;
its carrier reads exactly these two semantically equal endpoints. -/
theorem fixture_domain_code (ν : Valuation) (ρ : EnvI) :
    SemEqI ρ (translate ν EqLargeFixture.domain)
      (taggedTerm (some 0) (.app (.app (.app (.const 12 [])
        (translate ν (.sort .zero))) (translate ν EqLargeFixture.parameter))
        (translate ν EqLargeFixture.parameter))) := by
  apply eq_of_betaRun (k := 3)
  rfl

theorem fixture_domain_member (ν : Valuation) (ρ : EnvI) :
    SortMember (some 0) (denote ν ρ EqLargeFixture.domain) ∧
    TypeDefined (denote ν ρ EqLargeFixture.domain) :=
  ⟨sortMember_congr (SemEqI.symm (fixture_domain_code ν ρ)) (tagged_member ρ _ _),
    typeDefined_congr (SemEqI.symm (fixture_domain_code ν ρ)) (tagged_defined ρ _ _)⟩

/-- Exact regression: two positive universes are not merged into one tag. -/
theorem positive_sort_codes_distinct (ρ : EnvI) :
    ¬ ValueEq (denI ρ (sortTerm (some 1))) (denI ρ (sortTerm (some 2))) := by
  intro h
  have he := sort_code_injective h
  cases he

end Rcic.Declarative.Ann.LR3.UnitModel
