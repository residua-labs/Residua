import rcic.RcicAnnLR3IotaRecursorLaw
import rcic.RcicAnnLR3PairedArms

/-!
# The exact `Conv_iota` / `Conv_structIota` PairedArms contracts

`RawIotaLaw M E I n` is the forward raw ι computation of an image at every typed
redex of the interface graph `I.fn`. It is a property of the image alone; it does
not mention codes, PERs, neutral support or a Fundamental theorem.

`conv_iota_of_rawIota` and `conv_structIota_of_rawIota` supply the two exact
PairedArms contracts for **any** `AnnSemantics` with that law. Every source premise
and every child-IH position of the contracts is kept; the proof consumes the
right-hand typing IH `ih_hrhs` (its code pair and element relation) and rewrites the
left image by the raw law. The struct contract's `hcv`/`ih_hcv` positions are kept
and unused: `I.fn (.app f a) = some rhs` already states the redex.

For the EnvironmentEval model with the recursor hook,

```lean
EnvironmentEval.annSemantics C V H     -- any CodeSystem C, any routing view/hook
```

the law is `IotaRecursor.denote_iota`, so `conv_iota_supplied` /
`conv_structIota_supplied` hold for every code system, at `I = iotaIfaceA E`, under
`FirstOrderArity E` alone (`*_plain` for `V = E`, `H = iotaHook E`).

`pinNat_firstOrderArity` discharges that side condition for the admitted-shape Nat
group pinned in `RcicAnnIota`, so `pinNat_conv_iota` / `pinNat_conv_structIota` are
unconditional exact arms on a recursive environment, and `pinNat_iota_succ` is the
actual computed ι equation `rec P mz ms (succ zero) = ms zero (rec P mz ms zero)` in
the raw image. The function-recursive class (e.g. the pinned `node : (Sort 0 → T) →
T` group) is not covered here. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.IotaRecursor

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

/-- The raw forward ι law of an image at every typed redex of the interface. -/
def RawIotaLaw (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA) (lhs rhs T : ExprA), I.fn lhs = some rhs → HasTyA E I n Γ lhs T →
    ∀ (ν : Valuation) (ρ : EnvI), M.image ν Γ ρ lhs = M.image ν Γ ρ rhs

/-- The exact `Conv_iota` contract from the raw ι law. -/
theorem conv_iota_of_rawIota {M : AnnSemantics} {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : RawIotaLaw M E I n) : PairedArms.Conv_iota M E I n := by
  intro Γ lhs rhs T hrel hlhs _hrhs _ih_hlhs ih_hrhs hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hr⟩ := ih_hrhs hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  rw [h Γ lhs rhs T hrel.graph hlhs ν ρ]
  exact hr

/-- The exact `Conv_structIota` contract from the raw ι law. -/
theorem conv_structIota_of_rawIota {M : AnnSemantics} {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} (h : RawIotaLaw M E I n) : PairedArms.Conv_structIota M E I n := by
  intro Γ f a rhs e T _hrec _hs hfn hlhs _hrhs _hcv _ih_hlhs ih_hrhs _ih_hcv hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hr⟩ := ih_hrhs hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  rw [h Γ (.app f a) rhs T hfn hlhs ν ρ]
  exact hr

/-! ## The EnvironmentEval model -/

/-- The raw ι law of the EnvironmentEval image for every routing view/hook. -/
theorem rawIota_of_routes (C : CodeSystem) {E V : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    (hroute : Routes E V H) (harity : FirstOrderArity E) (n : Nat) :
    RawIotaLaw (EnvironmentEval.annSemantics C V H) E (iotaIfaceA E) n :=
  fun _ _ _ _ h _ ν ρ => denote_iota hroute harity h ν ρ

theorem conv_iota_supplied (C : CodeSystem) {E V : ResolvedEnvA}
    {H : EnvironmentEval.FamilySyntax} (hroute : Routes E V H) (harity : FirstOrderArity E)
    (n : Nat) : PairedArms.Conv_iota (EnvironmentEval.annSemantics C V H) E (iotaIfaceA E) n :=
  conv_iota_of_rawIota (rawIota_of_routes C hroute harity n)

theorem conv_structIota_supplied (C : CodeSystem) {E V : ResolvedEnvA}
    {H : EnvironmentEval.FamilySyntax} (hroute : Routes E V H) (harity : FirstOrderArity E)
    (n : Nat) :
    PairedArms.Conv_structIota (EnvironmentEval.annSemantics C V H) E (iotaIfaceA E) n :=
  conv_structIota_of_rawIota (rawIota_of_routes C hroute harity n)

theorem conv_iota_plain (C : CodeSystem) (E : ResolvedEnvA) (harity : FirstOrderArity E)
    (n : Nat) :
    PairedArms.Conv_iota (EnvironmentEval.annSemantics C E (iotaHook E)) E (iotaIfaceA E) n :=
  conv_iota_supplied C (routes_plain E) harity n

theorem conv_structIota_plain (C : CodeSystem) (E : ResolvedEnvA) (harity : FirstOrderArity E)
    (n : Nat) :
    PairedArms.Conv_structIota (EnvironmentEval.annSemantics C E (iotaHook E)) E
      (iotaIfaceA E) n :=
  conv_structIota_supplied C (routes_plain E) harity n

/-! ## A recursive positive control: the pinned Nat group -/

theorem pinNat_members {r : Nat} {m : CheckedMemberA} (h : pinNatEnvA.members r = some m) :
    (r = 10 ∧ m = pinNatFamA) ∨ (r = 11 ∧ m = pinZeroA) ∨ (r = 12 ∧ m = pinSuccA) ∨
      (r = 13 ∧ m = pinNatRecA) := by
  simp only [pinNatEnvA, extendEnvA, emptyEnvA] at h
  by_cases h13 : r = 13
  · rw [if_pos h13] at h; injection h with h; exact .inr (.inr (.inr ⟨h13, h.symm⟩))
  · rw [if_neg h13] at h
    by_cases h12 : r = 12
    · rw [if_pos h12] at h; injection h with h; exact .inr (.inr (.inl ⟨h12, h.symm⟩))
    · rw [if_neg h12] at h
      by_cases h11 : r = 11
      · rw [if_pos h11] at h; injection h with h; exact .inr (.inl ⟨h11, h.symm⟩)
      · rw [if_neg h11] at h
        by_cases h10 : r = 10
        · rw [if_pos h10] at h; injection h with h; exact .inl ⟨h10, h.symm⟩
        · rw [if_neg h10] at h; exact Option.noConfusion h

theorem pinNat_group_data_zero :
    (iotaGroupA pinNatEnvA 13 11).map
      (fun g => (g.nparams, g.nindices, g.familyRef, g.ctorM.arity, ctorTypeOf g)) =
      some (0, 0, 10, 0, pinNatTyA) := by decide

theorem pinNat_group_data_succ :
    (iotaGroupA pinNatEnvA 13 12).map
      (fun g => (g.nparams, g.nindices, g.familyRef, g.ctorM.arity, ctorTypeOf g)) =
      some (0, 0, 10, 0, .pi pinNatTyA (.succ .zero) pinNatTyA (.succ .zero)) := by decide

theorem pinNat_shapes_zero : ctorShapesA 10 0 pinNatTyA = some [] := by decide

theorem pinNat_shapes_succ :
    ctorShapesA 10 0 (.pi pinNatTyA (.succ .zero) pinNatTyA (.succ .zero)) =
      some [.recursive 0] := by decide

/-- The Nat group satisfies the first-order arity side condition at every
instantiation the source ι can read. -/
theorem pinNat_firstOrderArity : FirstOrderArity pinNatEnvA := by
  intro recRef c g shapes pre ls args ctorAfter hg hsh htel hft
  obtain ⟨hrecM, hrecC, hctorM, hctorC, _⟩ := iotaGroupA_some hg
  rcases pinNat_members hrecM with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨hr, _⟩ <;>
    try (rw [hm] at hrecC; exact absurd hrecC (by decide))
  subst hr
  rcases pinNat_members hctorM with ⟨_, hm⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, hm⟩ <;>
    try (rw [hm] at hctorC; exact absurd hctorC (by decide))
  · subst hc
    have hd := pinNat_group_data_zero
    rw [hg] at hd
    injection hd with hd
    injection hd with hnp hd
    injection hd with hni hd
    injection hd with hfam hd
    injection hd with har hty
    rw [hnp, hfam, hty, pinNat_shapes_zero] at hsh
    injection hsh with hsh
    subst hsh
    rw [hnp, hni]
    rw [hnp] at hft
    have hl := fieldsTelA_length _ _ _ hft
    simp only [List.length_nil, List.drop_zero] at hl
    rw [List.drop_zero, List.length_eq_zero.mp hl]
    trivial
  · subst hc
    have hd := pinNat_group_data_succ
    rw [hg] at hd
    injection hd with hd
    injection hd with hnp hd
    injection hd with hni hd
    injection hd with hfam hd
    injection hd with har hty
    rw [hnp, hfam, hty, pinNat_shapes_succ] at hsh
    injection hsh with hsh
    subst hsh
    rw [hnp, har, hty] at htel
    simp only [List.take_zero] at htel
    injection htel with htel
    subst htel
    rw [hnp, hni]
    rw [hnp] at hft
    have hl := fieldsTelA_length _ _ _ hft
    simp only [List.drop_zero, List.length_singleton] at hl ⊢
    obtain ⟨f, hf⟩ := List.length_eq_one.mp hl
    subst hf
    exact ⟨rfl, trivial⟩

theorem pinNat_conv_iota (C : CodeSystem) (n : Nat) :
    PairedArms.Conv_iota (EnvironmentEval.annSemantics C pinNatEnvA (iotaHook pinNatEnvA))
      pinNatEnvA (iotaIfaceA pinNatEnvA) n :=
  conv_iota_plain C pinNatEnvA pinNat_firstOrderArity n

theorem pinNat_conv_structIota (C : CodeSystem) (n : Nat) :
    PairedArms.Conv_structIota
      (EnvironmentEval.annSemantics C pinNatEnvA (iotaHook pinNatEnvA))
      pinNatEnvA (iotaIfaceA pinNatEnvA) n :=
  conv_structIota_plain C pinNatEnvA pinNat_firstOrderArity n

/-- The actual computed ι step at a recursive constructor, in the raw image:
`rec P mz ms (succ zero)` and `ms zero (rec P mz ms zero)` have equal images. -/
theorem pinNat_iota_succ (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote pinNatEnvA (iotaHook pinNatEnvA) ν ρ
        (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA
          (.app (.const 12 []) (.const 11 []))) =
      EnvironmentEval.denote pinNatEnvA (iotaHook pinNatEnvA) ν ρ
        (.app (.app pinMsA (.const 11 []))
          (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.const 11 []))) :=
  denote_iota (routes_plain pinNatEnvA) pinNat_firstOrderArity (by decide) ν ρ

end Rcic.Declarative.Ann.LR3.IotaRecursor
