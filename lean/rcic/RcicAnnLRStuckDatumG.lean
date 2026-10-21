import rcic.RcicAnnLRRowsG
import rcic.RcicAnnPropKey

/-!
# DT-025 / A-6 S1-g.2 (ruling R-A6-S1g, pass 2) — `hstuck` from the guarded fundamental theorem

Pass 1 (S1-g.1, `RcicAnnPropKey`) proved, from main's relation, that the Prop key `IsPropTy`
agrees with the declared sort; `propKeyA_holds` packages it as `PropKeyA`. Pass 2 is the
guarded copy `TyKAg` (`RcicAnnLRG` … `RcicAnnLRRowsG`): its `stuck` clause carries both
terms' head chains at a non-proposition, its `EqKAg.stuck` the two normal forms' side of the
key, its `sortP` key-propositions; its fundamental theorem `fundAg` consumes `PropKeyA`.

Here the payoff: a related pair at a type whose normal form is stuck and not a proposition
carries chains BY THE RELATION (`hstuck_of_datumg`, no `hstuck` premise), and `fund_selfg`
relates every typed term to itself — so every term typed at a non-`Prop` stuck type has a head
chain to an `hStepFnA`-normal form (`chain_of_fund_stuckg`). Proofs (terms at a proposition)
get none: the prop clause's relation.

Pinned at the empty environment: `(λ x : T. x) y`, typed at the neutral type `T : Sort 1`,
gets its chain from the theorem, and its normal form is `y` — read back through determinism and
checked a second time by evaluating `whnfA` (`decide`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Datum
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- **S1-g.1, packaged for pass 2**: the six environment hypotheses give `PropKeyA`. -/
theorem propKeyA_holds (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) : PropKeyA E I n :=
  ⟨fun hΓ hX hN hn => by
    obtain ⟨c⟩ := hN
    obtain ⟨hNu⟩ := whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ c ⟨hX⟩
    exact isPropTy_iff_of_normal hE hI hIS hEN hNC hR hS hρ hΓ hNu hn,
   fun hΓ hc hA hB hn hn' => propKey_K3 hE hI hIS hEN hNC hR hS hρ hΓ hc hA hB hn hn'⟩

/-- **the guarded datum discharges `hstuck` at a non-proposition**: any pair related at `A`
    (guarded relation), with `A`'s normal form stuck and not `IsPropTy`, has head chains at
    `A`. No `hstuck` premise: the reached clause is the guarded `stuck` one
    (`TyKA_uniqueg`), whose relation is the chained quadruple. -/
theorem hstuck_of_datumg {k : Nat} {Γ : LCtxA} {A a b N : ExprA}
    (hrel : LRRelAg E I n ρ₀ k Γ A a b)
    (hA : WhTyA E I n Γ A N) (hN : StuckA E I Γ N) (hnp : ¬ IsPropTy E I Γ N) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  obtain ⟨R, hR, hab⟩ := hrel
  rw [LRTyA_eqg] at hR
  rw [TyKA_uniqueg hR (TyKAg.stuck hA hN hnp)] at hab
  obtain ⟨_, _, _, Na, cha, hna, Nb, chb, hnb⟩ := hab
  have hcA := tyConvA_symm_ne (whTyA_tyConv hA)
  exact ⟨Na, tyHRedStarA_retype hcA cha, hna, Nb, tyHRedStarA_retype hcA chb, hnb⟩

/-- **R-A6-S1g — `fund_selfg` at a non-`Prop` stuck type yields `hstuck`**: on main's six
    environment hypotheses and the guarded copy's member semantics `EnvSemAg`, every term typed
    at a type whose normal form is stuck and not a proposition has a head chain to an
    `hStepFnA`-normal form at that type. -/
theorem chain_of_fund_stuckg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hSg : EnvSemAg E I n ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {e A N : ExprA} (ht : HasTyA E I n Γ e A)
    (hA : WhTyA E I n Γ A N) (hN : StuckA E I Γ N) (hnp : ¬ IsPropTy E I Γ N) :
    ∃ Ne, TyHRedStarA E I n Γ e Ne A ∧ hStepFnA E I.fn Γ Ne = none := by
  obtain ⟨k₀, hk⟩ := fund_selfg hE hI hIS hEN hNC hR hSg hρ (propKeyA_holds hE hI hIS hEN hNC hR hS hρ) hΓ ht
  obtain ⟨Ne, ch, hn, _⟩ := hstuck_of_datumg (hk k₀ (Nat.le_refl _)) hA hN hnp
  exact ⟨Ne, ch, hn⟩

/-- **`chain_of_fund_stuckg` at a well-formed environment** — W2g DISCHARGED (R-NoDeltaRec-4d-iii,
    PR #6263): the premise list minus `hEN`/`hNC`, which `envWfA_normCtorType`/`envWfA_normClosed`
    supply from any `EnvWfA` of the environment. -/
theorem chain_of_fund_stuckg_wf {J : IotaIfaceA} (hW : EnvWfA J E) (hE : EnvClosedA E)
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hSg : EnvSemAg E I n ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {e A N : ExprA} (ht : HasTyA E I n Γ e A)
    (hA : WhTyA E I n Γ A N) (hN : StuckA E I Γ N) (hnp : ¬ IsPropTy E I Γ N) :
    ∃ Ne, TyHRedStarA E I n Γ e Ne A ∧ hStepFnA E I.fn Γ Ne = none :=
  chain_of_fund_stuckg hE hI hIS (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hS hSg hρ hΓ ht
    hA hN hnp

end Datum

/-! ## the pin — a real β-step, from the theorem, at the empty environment -/

/-- `Γ = [y : T, T : Sort 1]`: `T` a neutral type at a non-`Prop` sort, `y` a variable of it. -/
def pinDatumCtxA : LCtxA :=
  [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `(λ x : T. x) y` (in `Γ`, `T` is `bvar 1`). -/
def pinDatumTermA : ExprA := .app (.lam (.bvar 1) (.succ .zero) (.bvar 0)) (.bvar 0)

def pinDatumCtxA_wf : CtxWfA emptyEnvA noIotaA 0 pinDatumCtxA :=
  .assumption (.assumption .nil (.sort [] _)) (.bvar _ 0 _ (.succ (.succ .zero)) rfl (.sort _ _))

def pinDatumTermA_ty : HasTyA emptyEnvA noIotaA 0 pinDatumCtxA pinDatumTermA (.bvar 1) :=
  .app _ (.lam (.bvar 1) (.succ .zero) (.bvar 0)) (.bvar 0) (.bvar 1) (.bvar 2) (.succ .zero)
    (.succ .zero) (.succ .zero)
    (.bvar _ 2 _ (.succ (.succ .zero)) rfl (.sort _ _))
    (.bvar _ 1 _ (.succ (.succ .zero)) rfl (.sort _ _))
    (.lam _ _ _ _ _ (.succ .zero)
      (.bvar _ 1 _ (.succ (.succ .zero)) rfl (.sort _ _))
      (.bvar _ 2 _ (.succ (.succ .zero)) rfl (.sort _ _))
      (.bvar _ 0 _ (.succ .zero) rfl (.bvar _ 2 _ (.succ (.succ .zero)) rfl (.sort _ _))))
    (.bvar _ 0 _ (.succ .zero) rfl (.bvar _ 1 _ (.succ (.succ .zero)) rfl (.sort _ _)))

theorem pinDatum_T_stuck : StuckA emptyEnvA noIotaA pinDatumCtxA (.bvar 1) :=
  ⟨rfl, by simp [appsSpineA, isShapeHeadA]⟩

/-- `T : Sort 1` is no proposition for the key (`inferSortA` gives `1`). -/
theorem pinDatum_T_notProp : ¬ IsPropTy emptyEnvA noIotaA pinDatumCtxA (.bvar 1) :=
  not_isPropTy_of_inferSortA (fuel := 2) (l := .succ .zero) (by decide) rfl

/-- **the pin**: the theorem hands `(λ x : T. x) y` a chain to a normal form, and that normal
    form is `y` (determinism of chains to normal forms, `RedTo_det` through erasure). -/
theorem pin_chain_of_fund_stuckg :
    ∃ Ne, TyHRedStarA emptyEnvA noIotaA 0 pinDatumCtxA pinDatumTermA Ne (.bvar 1) ∧
      hStepFnA emptyEnvA noIotaA.fn pinDatumCtxA Ne = none ∧ Ne = .bvar 0 := by
  obtain ⟨Ne, ch, hn⟩ := chain_of_fund_stuckg emptyEnvA_closed noIotaA_lift noIotaA_subst
    (fun _ _ h => Option.noConfusion h) (fun _ _ h => Option.noConfusion h) (noIotaA_recHead _) (emptyEnvA_sem noIotaA 0 (fun _ => 1)) (emptyEnvA_semg noIotaA 0 (fun _ => 1))
    posValA_one pinDatumCtxA_wf pinDatumTermA_ty
    (whTyA_of_hasTy (.bvar _ 1 _ (.succ (.succ .zero)) rfl (.sort _ _))) pinDatum_T_stuck
    pinDatum_T_notProp
  refine ⟨Ne, ch, hn, ?_⟩
  obtain ⟨c⟩ := ch
  exact RedTo_det (tmChainA_redTo c hn) ⟨2, rfl⟩

/-- the second instrument: `whnfA` itself computes `y` from `(λ x : T. x) y`. -/
example : whnfA emptyEnvA noIotaA.fn pinDatumCtxA 2 pinDatumTermA = some (.bvar 0) := by decide

#print axioms propKeyA_holds
#print axioms hstuck_of_datumg
#print axioms chain_of_fund_stuckg
#print axioms chain_of_fund_stuckg_wf
#print axioms pinDatumCtxA_wf
#print axioms pin_chain_of_fund_stuckg

end Rcic.Declarative.Ann
