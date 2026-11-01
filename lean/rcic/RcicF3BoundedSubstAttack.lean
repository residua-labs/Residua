import rcic.RcicF3BoundedSubst
import rcic.RcicF3BoundedPiSpineAttack

/-!
# Bounded beta and zeta expose a dependent depth-three family spine

The auxiliary type is `(fun f : Prop -> Prop => forall (P : Prop)
(x : P) (y : P), f P) AccR`. Its actual typed beta contraction substitutes
the family constant through three dependent Pi binders. The resulting
complete argument list still contains P, and the bounded-substitution
producer supplies the reduct's typing and every domain at the original K.
The corresponding let uses the same actual family constant. Its local
zeta conversion is also substituted through the new own-let-slot rule,
so that branch is exercised directly rather than only by a bvar lookup.
The let itself carries an outer type conversion, which the public
zeta_subject_reduction producer preserves at the original requested type.

All typings live in the real AccR family's constructor prefix; its
closedness is produced from the actual admission walk. The earlier
inhabited tuple `[True, proof, proof]` fits the three domains in the same
normalized table. No inhabitant of AccR True is asserted. The retained
actual AccR fixture has its explicitly empty recursive child domain.

This is a typed normalization component in an admitted prefix, not a new
admitted constructor or a proof of arbitrary converted-Pi beta reduction,
full fuelled typed normalization, bounded delta unfolding, or domain erasure.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.BoundedSubstAttack
open Rcic.Declarative BoundedTransport BoundedPiSpine
open BoundedPiSpineAttack (threeDs threeArgs three threeLevel values)
open NormRoleTableAttack (table)
open PropEvalAdmittedInputsAttack (bound)

theorem prefix_closed : EnvClosed accFamOnly :=
  family_prefix_closed EnvWfT.empty AccEnv.accMembersT

def kind : Expr Nat := .pi (.sort .zero) (.sort .zero)
def body : Expr Nat := policyPi threeDs (foldApps (.bvar 3) threeArgs)
def hidden : Expr Nat := .app (.lam kind body) (.const 0 [])
def letHidden : Expr Nat := .letE kind (.const 0 []) body

noncomputable def kind_typed : HasTyT accFamOnly 0 [] kind
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero)

theorem kind_bound (σ K : Nat → Nat) : LOKt σ 4 K kind_typed := by
  change 1 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4
  exact ⟨by decide, by decide, by decide, by decide⟩

noncomputable def argument_typed : HasTyT accFamOnly 0 [] (.const 0 []) kind :=
  .const [] 0 [] accFamMember rfl rfl rfl

theorem argument_bound (σ K : Nat → Nat) : LOKt σ 4 K argument_typed :=
  fun l hl => (List.not_mem_nil l hl).elim

noncomputable def body_base : HasTyT accFamOnly 0 [.assumption kind]
    body (.sort threeLevel) :=
  .pi [.assumption kind] (.sort .zero) (.succ .zero)
    (.pi (.bvar 0) (.pi (.bvar 1) (.app (.bvar 3) (.bvar 2))))
    (.imax .zero (.imax .zero .zero))
    (.sort _ .zero)
    (.pi [.assumption (.sort .zero), .assumption kind] (.bvar 0) .zero
      (.pi (.bvar 1) (.app (.bvar 3) (.bvar 2))) (.imax .zero .zero)
      (.bvar _ 0 _ rfl)
      (.pi [.assumption (.bvar 0), .assumption (.sort .zero), .assumption kind]
        (.bvar 1) .zero (.app (.bvar 3) (.bvar 2)) .zero
        (.bvar _ 1 _ rfl)
        (.app _ (.bvar 3) (.bvar 2) (.sort .zero) (.sort .zero)
          (.bvar _ 3 kind rfl) (.bvar _ 2 (.sort .zero) rfl))))

/-- An actual outer type conversion is included in the source body. -/
noncomputable def body_typed : HasTyT accFamOnly 0 [.assumption kind]
    body (.sort .zero) :=
  .conv _ body (.sort threeLevel) (.sort .zero) (.succ threeLevel)
    body_base (.sorts _ threeLevel .zero (fun _ => rfl))

theorem body_bound (σ K : Nat → Nat) : LOKt σ 4 K body_typed := by
  change (1 ≤ 4 ∧ 0 ≤ 4 ∧ 1 ≤ 4 ∧
    (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧
      (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧ (True ∧ True)))) ∧ 1 ≤ 4
  exact ⟨⟨by decide, Nat.zero_le _, by decide,
    Nat.zero_le _, Nat.zero_le _, True.intro,
    Nat.zero_le _, Nat.zero_le _, True.intro, True.intro, True.intro⟩, by decide⟩

noncomputable def hidden_typed : HasTyT accFamOnly 0 [] hidden (.sort .zero) :=
  .app [] (.lam kind body) (.const 0 []) kind (.sort .zero)
    (.lam [] kind (.imax (.succ .zero) (.succ .zero)) body (.sort .zero)
      kind_typed body_typed) argument_typed

theorem hidden_bound (σ K : Nat → Nat) : LOKt σ 4 K hidden_typed :=
  ⟨⟨kind_bound σ K, body_bound σ K⟩, argument_bound σ K⟩

theorem reduct : instantiate0 (.const 0 []) body = three := rfl

theorem hidden_read : piTelescopeFuel accFamOnly 16 hidden =
    some (threeDs, foldApps (.const 0 []) threeArgs) := rfl

/-- The new producer, not an independently supplied normalized typing,
contracts this actual bounded body and its typed family argument. -/
theorem normalized_typed (σ K : Nat → Nat) :
    ∃ d : HasTyT accFamOnly 0 [] three (.sort .zero), LOKt σ 4 K d := by
  have h := (beta_reduct prefix_closed σ 4 K kind_typed (kind_bound σ K)
    body_typed (body_bound σ K) argument_typed (argument_bound σ K)).1
  change ∃ d : HasTyT accFamOnly 0 [] (instantiate0 (.const 0 []) body)
    (.sort .zero), LOKt σ 4 K d at h
  rw [reduct] at h
  exact h

theorem normalized_domains (σ K : Nat → Nat) :
    Domains (E := accFamOnly) (n := 0) σ 4 K [] threeDs ∧
      ∃ (v : Level) (d : HasTyT accFamOnly 0 (context [] threeDs)
        (foldApps (.const 0 []) threeArgs) (.sort v)), LOKt σ 4 K d :=
  beta_telescope prefix_closed σ 4 K kind_typed (kind_bound σ K)
    body_typed (body_bound σ K) argument_typed (argument_bound σ K)
    threeDs (foldApps (.const 0 []) threeArgs) reduct

theorem normalized_parameter (σ K : Nat → Nat) :
    ∃ (A T : Expr Nat), lookupType (context [] threeDs) 2 = some A ∧
      (∃ d : HasTyT accFamOnly 0 (context [] threeDs) (.bvar 2) T,
        LOKt σ 4 K d) ∧
      ∃ c : TyConvT accFamOnly 0 (context [] threeDs) A T,
        BoundedBVar.Bounded σ 4 K c := by
  obtain ⟨d, hd⟩ := normalized_typed σ K
  exact variable_argument σ 4 K threeDs threeArgs (.const 0 [])
    d hd 2 (List.mem_cons_self _ _)

/-- The same produced domains, not a replacement context, are used with
the inhabited dependent tuple in the actual normalized AccR table. -/
theorem composition (P : Premises4) (σ : Nat → Nat) :
    Nonempty (CtxWfT accFamOnly 0 (context [] threeDs)) ∧
    Fits (mkM P (table P)) σ (context [] threeDs) (push values ρ0) ∧
    ∃ (A T : Expr Nat), lookupType (context [] threeDs) 2 = some A ∧
      (∃ c : TyConvT accFamOnly 0 (context [] threeDs) A T,
        BoundedBVar.Bounded σ 4 bound c) ∧
      Equiv (den (mkM P (table P)) σ (push values ρ0) A)
        (den (mkM P (table P)) σ (push values ρ0) T) := by
  obtain ⟨d, hd⟩ := normalized_typed σ bound
  have hf := BoundedPiSpineAttack.values_fit P σ
  exact ⟨context_wf σ 4 bound threeDs (normalized_domains σ bound).1 .nil,
    context_fits (mkM P (table P)) σ threeDs ρ0 values True.intro hf,
    variable_argument_sound P (table P) σ bound (BoundedBVarAttack.prefix_sound P σ)
      threeDs threeArgs (.const 0 []) d hd 2 (List.mem_cons_self _ _)
      ρ0 values True.intro hf⟩

noncomputable def let_body_base :
    HasTyT accFamOnly 0 [.letBinding kind (.const 0 [])] body (.sort threeLevel) :=
  .pi [.letBinding kind (.const 0 [])] (.sort .zero) (.succ .zero)
    (.pi (.bvar 0) (.pi (.bvar 1) (.app (.bvar 3) (.bvar 2))))
    (.imax .zero (.imax .zero .zero))
    (.sort _ .zero)
    (.pi [.assumption (.sort .zero), .letBinding kind (.const 0 [])]
      (.bvar 0) .zero (.pi (.bvar 1) (.app (.bvar 3) (.bvar 2)))
      (.imax .zero .zero) (.bvar _ 0 _ rfl)
      (.pi [.assumption (.bvar 0), .assumption (.sort .zero),
        .letBinding kind (.const 0 [])]
        (.bvar 1) .zero (.app (.bvar 3) (.bvar 2)) .zero
        (.bvar _ 1 _ rfl)
        (.app _ (.bvar 3) (.bvar 2) (.sort .zero) (.sort .zero)
          (.bvar _ 3 kind rfl) (.bvar _ 2 (.sort .zero) rfl))))

noncomputable def let_body_typed :
    HasTyT accFamOnly 0 [.letBinding kind (.const 0 [])] body (.sort .zero) :=
  .conv _ body (.sort threeLevel) (.sort .zero) (.succ threeLevel)
    let_body_base (.sorts _ threeLevel .zero (fun _ => rfl))

theorem let_body_bound (σ K : Nat → Nat) : LOKt σ 4 K let_body_typed := by
  change (1 ≤ 4 ∧ 0 ≤ 4 ∧ 1 ≤ 4 ∧
    (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧
      (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧ (True ∧ True)))) ∧ 1 ≤ 4
  exact ⟨⟨by decide, Nat.zero_le _, by decide,
    Nat.zero_le _, Nat.zero_le _, True.intro,
    Nat.zero_le _, Nat.zero_le _, True.intro, True.intro, True.intro⟩, by decide⟩

noncomputable def let_hidden_typed : HasTyT accFamOnly 0 [] letHidden (.sort .zero) :=
  .conv [] letHidden (.sort threeLevel) (.sort .zero) (.succ threeLevel)
    (.letE [] kind (.imax (.succ .zero) (.succ .zero)) (.const 0 [])
      (.sort threeLevel) body kind_typed argument_typed let_body_base)
    (.sorts [] threeLevel .zero (fun _ => rfl))

theorem let_hidden_bound (σ K : Nat → Nat) : LOKt σ 4 K let_hidden_typed :=
  ⟨⟨kind_bound σ K, argument_bound σ K, (let_body_bound σ K).1⟩,
    (let_body_bound σ K).2⟩

theorem let_hidden_read : piTelescopeFuel accFamOnly 16 letHidden =
    some (threeDs, foldApps (.const 0 []) threeArgs) := rfl

/-- A selected own-let conversion is an actual input to subst_any_c. -/
noncomputable def local_zeta : ConvT accFamOnly 0 [.letBinding kind (.const 0 [])]
    (.bvar 0) (.const 0 []) kind :=
  .zetaLocal _ 0 kind (.const 0 []) rfl rfl
    (.const _ 0 [] accFamMember rfl rfl rfl)

theorem local_zeta_bound (σ K : Nat → Nat) : LOKc σ 4 K local_zeta :=
  fun l hl => (List.not_mem_nil l hl).elim

theorem local_zeta_substituted (σ K : Nat → Nat) :
    ∃ c : ConvT accFamOnly 0 [] (.const 0 []) (.const 0 []) kind,
      LOKc σ 4 K c := by
  have h := subst_any_c prefix_closed σ 4 K (.const 0 []) kind (j := 0)
    local_zeta (local_zeta_bound σ K) (Or.inr rfl)
    argument_typed (argument_bound σ K)
  exact h

/-- Both endpoints are supplied by the actual typed-let producer. -/
theorem let_normalized (σ K : Nat → Nat) :
    (∃ d : HasTyT accFamOnly 0 [] three (.sort .zero), LOKt σ 4 K d) ∧
    (∃ c : ConvT accFamOnly 0 [] letHidden three (.sort .zero), LOKc σ 4 K c) := by
  have ht := zeta_subject_reduction prefix_closed σ 4 K
    let_hidden_typed (let_hidden_bound σ K)
  rw [reduct] at ht
  have hc := (zeta_reduct prefix_closed σ 4 K kind_typed (kind_bound σ K)
    argument_typed (argument_bound σ K) let_body_typed (let_body_bound σ K)).2
  change ∃ c : ConvT accFamOnly 0 [] letHidden (instantiate0 (.const 0 []) body)
    (.sort .zero), LOKc σ 4 K c at hc
  rw [reduct] at hc
  exact ⟨ht, hc⟩

def ZetaWitness (P : Premises4) : Prop :=
  piTelescopeFuel accFamOnly 16 letHidden =
    some (threeDs, foldApps (.const 0 []) threeArgs) ∧
  Nonempty (HasTyT accFamOnly 0 [] letHidden (.sort .zero)) ∧
  (∀ σ K, LOKt σ 4 K let_hidden_typed) ∧
  (∀ σ K, ∃ c : ConvT accFamOnly 0 [] (.const 0 []) (.const 0 []) kind,
    LOKc σ 4 K c) ∧
  (∀ σ K,
    (∃ d : HasTyT accFamOnly 0 [] three (.sort .zero), LOKt σ 4 K d) ∧
    (∃ c : ConvT accFamOnly 0 [] letHidden three (.sort .zero), LOKc σ 4 K c)) ∧
  (∀ σ K, Domains (E := accFamOnly) (n := 0) σ 4 K [] threeDs ∧
    ∃ (v : Level) (d : HasTyT accFamOnly 0 (context [] threeDs)
      (foldApps (.const 0 []) threeArgs) (.sort v)), LOKt σ 4 K d) ∧
  (∀ σ, Nonempty (CtxWfT accFamOnly 0 (context [] threeDs)) ∧
    Fits (mkM P (table P)) σ (context [] threeDs) (push values ρ0) ∧
    ∃ (A T : Expr Nat), lookupType (context [] threeDs) 2 = some A ∧
      (∃ c : TyConvT accFamOnly 0 (context [] threeDs) A T,
        BoundedBVar.Bounded σ 4 bound c) ∧
      Equiv (den (mkM P (table P)) σ (push values ρ0) A)
        (den (mkM P (table P)) σ (push values ρ0) T))

theorem zeta_witness (P : Premises4) : ZetaWitness P := by
  refine ⟨let_hidden_read, ⟨let_hidden_typed⟩, let_hidden_bound,
    local_zeta_substituted, let_normalized, ?_, ?_⟩
  · intro σ K
    exact zeta_telescope_of_typing prefix_closed σ 4 K
      let_hidden_typed (let_hidden_bound σ K)
      threeDs (foldApps (.const 0 []) threeArgs) reduct
  · intro σ
    obtain ⟨d, hd⟩ := (let_normalized σ bound).1
    have hds := zeta_telescope_of_typing prefix_closed σ 4 bound
      let_hidden_typed (let_hidden_bound σ bound)
      threeDs (foldApps (.const 0 []) threeArgs) reduct
    have hf := BoundedPiSpineAttack.values_fit P σ
    exact ⟨context_wf σ 4 bound threeDs hds.1 .nil,
      context_fits (mkM P (table P)) σ threeDs ρ0 values True.intro hf,
      variable_argument_sound P (table P) σ bound (BoundedBVarAttack.prefix_sound P σ)
        threeDs threeArgs (.const 0 []) d hd 2 (List.mem_cons_self _ _)
        ρ0 values True.intro hf⟩

theorem zeta_nonrefutable (P : Premises4) :
    ¬ (ZetaWitness P → (Premises4 → False)) :=
  fun h => h (zeta_witness P) P

def Witness (P : Premises4) : Prop :=
  BoundedPiSpineAttack.Witness P ∧ ZetaWitness P ∧ EnvClosed accFamOnly ∧
  instantiate0 (.const 0 []) body = three ∧
  piTelescopeFuel accFamOnly 16 hidden =
    some (threeDs, foldApps (.const 0 []) threeArgs) ∧
  Nonempty (HasTyT accFamOnly 0 [] hidden (.sort .zero)) ∧
  (∀ σ K, LOKt σ 4 K hidden_typed) ∧
  (∀ σ K, ∃ d : HasTyT accFamOnly 0 [] three (.sort .zero), LOKt σ 4 K d) ∧
  (∀ σ K, Domains (E := accFamOnly) (n := 0) σ 4 K [] threeDs ∧
    ∃ (v : Level) (d : HasTyT accFamOnly 0 (context [] threeDs)
      (foldApps (.const 0 []) threeArgs) (.sort v)), LOKt σ 4 K d) ∧
  (∀ σ, Nonempty (CtxWfT accFamOnly 0 (context [] threeDs)) ∧
    Fits (mkM P (table P)) σ (context [] threeDs) (push values ρ0) ∧
    ∃ (A T : Expr Nat), lookupType (context [] threeDs) 2 = some A ∧
      (∃ c : TyConvT accFamOnly 0 (context [] threeDs) A T,
        BoundedBVar.Bounded σ 4 bound c) ∧
      Equiv (den (mkM P (table P)) σ (push values ρ0) A)
        (den (mkM P (table P)) σ (push values ρ0) T))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨BoundedPiSpineAttack.component_witness P, zeta_witness P, prefix_closed, reduct,
    hidden_read, ⟨hidden_typed⟩, hidden_bound, normalized_typed,
    normalized_domains, composition P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.BoundedSubstAttack
