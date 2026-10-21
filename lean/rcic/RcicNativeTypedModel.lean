import rcic.RcicNativeFamModelLRSPER
import rcic.RcicLevelDec

/-!
# RcicNativeTypedModel — the typed-demand model `ApproxT` (paper §3.6 / Fig. 4)

The ruling after #7673's segment 2: W-UNTYPED-DEMANDS is measured (`sort_shape_of_symm_pi`), so
the model changes, not the compacts.  This module ships items (1)–(3) of that ruling.

**(1) The interpretation, and why it is well-founded.**  The ruling asks for `⟦A⟧` by
well-founded recursion over the universe structure, never on the compact.  In the compact
(domain) model the answer is structural rather than universe-recursive:

* the interpretation of a *type* is the union of the finitary projections of its approximants,
  `ElT E ρ A u := ∃ a, ApproxT E ρ A a ∧ CTyS E u a` — "`u` is an element of some code `a` of
  `A`";
* `CTyS E u a` (strict semantic typing of compacts: the landed `CTy` of `RcicNativePiModelIrr`
  with the Prop universe split in — `CTyT` — plus coverage of every λ output by a compatible
  codomain step; `ctyT_permissive` is the recorded reason the universal form is not enough) is
  defined by well-founded recursion on the type code — finite data, with no reference to the
  relation or the model;
* `ApproxT` is an inductive on *terms* (the `ApproxDI` shape) whose Π/λ clauses type the step
  demands at the domain's code — a positive side condition, so no mutual dependency with any
  relation arises.

So the only place RCIC's universe structure enters is the **universe code** `sortCode l`:
`prop` when `l ≡ 0` (`decEqN`, sound and complete), `sort` otherwise — levels above Prop are
collapsed, exactly as every landed model collapses them, and nothing the Π-row route probes
distinguishes them.  The dependency order is `CptT → CTyS → ApproxT → ElT → (relation)`; each
is a plain inductive or a definition after the previous one.  No universe-indexed recursion is
needed because the semantic types are not defined by recursion on the syntactic type's universe
at all: the finite codes carry their own typing.  (The unfolding lemmas `elT_*` are the
interpretation's equations.)

**(2) `ApproxT`.**  `ApproxDI`'s clauses with typed demands: `pi`/`lam` require every demand of
every step to be typed at the domain's code `a` (`CTyS E u a`); `sort l` has the code
`sortCode l`; the recursor clauses are `ApproxDI.recursor` for a family not declared into
`Sort 0`, and **`recursorProp`** for a family declared into `Sort 0` — the major's demand is `[]`
and the fields' interpretations are `⊥` (§3.6: a recursor at a proposition major does not inspect
it; this is where K dissolves model-side).  A proposition family has only the non-strict clause,
so the canonical major's denotation is not larger than a variable's.  **The proof collapse**
(T1 of #7689): a λ compact must have a non-`⊥` output (`λ⊥ = ⊥`, the identification the paper's
domain makes), and a constructor of a family declared into `Sort 0` (`PropCtorT`) denotes `⊥`
only; `IsPropCT.pi` carries a type-code domain.  These three are forced by the model typing
lemma (`RcicNativeTypedModelTyping`), whose λ, constructor and Π cases they are.

**(3) The probe instances.**
* The `⊥`-demand fragment: on `BotPiCptT` compacts the typing side conditions are vacuous
  (`approxT_pi_botDemand_iff`, `approxT_lam_botDemand_iff`), and the probe compacts are present
  (`approxT_pi_bot_nil`, `approxT_sort_code`); the general transfer `ApproxDI ⇒ ApproxT` is the
  model typing lemma (demands realised by a well-typed argument are typed at its type's code),
  stated in the PR body.
* W-DEMAND: the refuting compact `pi prop [([sort], sort)]` is **not** a typed compact of
  `Π (P : Sort 0), P` (`not_approxT_idPiProp_sortStep`: the demand `sort` on `P : Prop` is not a
  proposition code), and every typed compact of `Π (P : Sort 0), P` is a proposition code
  (`isPropCT_of_approxT_idPiProp`) — the typed model sees the impredicative Π as a proposition,
  which the untyped one cannot (`not_isPropIdealI_pi_propBinder_bot`).
* The collapse that dissolves `AppPropArgs`: at a proposition domain every step demand is `⊥`
  (`approxT_pi_prop_dom_botDemand`, `approxT_lam_prop_dom_botDemand`, from `ctyT_prop_bot`);
  the elements of `True` are `⊥` (`elT_true_bot`), so a proof major can only be demanded at `⊥`
  — W-K's model side.
* W-ZETALOCAL: the context environment `ctxEnvT` with `semEqT_zetaLocal` and the
  `zetaLocalPiCtx` instance (`semEqT_ctxEnvT_zetaLocalPiCtx`), via the lifting algebra.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelTermDFundAudit

/-! ### §1 — compacts with a Prop code -/

/-- Compacts with two universe codes: `prop` (the code of `Sort 0`) below `sort` (every other
    universe). -/
inductive CptT where
  | bot
  | prop
  | sort
  | pi (a : CptT) (f : List (List CptT × CptT))
  | lam (g : List (List CptT × CptT))
  | spine (r : Nat) (args : List CptT)

/-- The universe code of `Sort l`: `prop` exactly when `l ≡ 0`. -/
def sortCode (l : Level) : CptT := if decEqN l .zero then .prop else .sort

theorem sortCode_eq_prop_iff (l : Level) : sortCode l = .prop ↔ eqN l .zero := by
  unfold sortCode
  constructor
  · intro h
    by_cases hd : decEqN l .zero = true
    · exact decEqN_sound l .zero hd
    · rw [if_neg hd] at h; exact CptT.noConfusion h
  · intro h
    rw [if_pos (decEqN_complete l .zero h)]

theorem sortCode_eq_sort_iff (l : Level) : sortCode l = .sort ↔ ¬ eqN l .zero := by
  unfold sortCode
  constructor
  · intro h he
    rw [if_pos (decEqN_complete l .zero he)] at h
    exact CptT.noConfusion h
  · intro he
    by_cases hd : decEqN l .zero = true
    · exact (he (decEqN_sound l .zero hd)).elim
    · rw [if_neg hd]

theorem sortCode_zero : sortCode .zero = .prop :=
  (sortCode_eq_prop_iff .zero).mpr (fun _ => rfl)

theorem sortCode_prop_or_sort (l : Level) : sortCode l = .prop ∨ sortCode l = .sort := by
  unfold sortCode
  by_cases hd : decEqN l .zero = true
  · rw [if_pos hd]; exact Or.inl rfl
  · rw [if_neg hd]; exact Or.inr rfl

/-- Environments over `CptT`. -/
abbrev EnvT : Type := Nat → CptT → Prop

def EnvT.bot : EnvT := fun _ c => c = .bot

def EnvT.cons (S : CptT → Prop) (ρ : EnvT) : EnvT
  | 0 => S
  | i + 1 => ρ i

def EnvT.insert (ρ : EnvT) (k : Nat) (S : CptT → Prop) : EnvT :=
  fun i => if i < k then ρ i else if i = k then S else ρ (i - 1)

def EnvT.le (ρ ρ' : EnvT) : Prop := ∀ i c, ρ i c → ρ' i c

/-- The finite set of a demand. -/
def demandT (us : List CptT) : CptT → Prop := fun c => c ∈ us

def botSetT : CptT → Prop := fun c => c = .bot

theorem EnvT.insert_zero (S : CptT → Prop) (ρ : EnvT) : EnvT.insert ρ 0 S = EnvT.cons S ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [EnvT.insert, EnvT.cons]

theorem EnvT.cons_insert (S T : CptT → Prop) (ρ : EnvT) (k : Nat) :
    EnvT.cons S (EnvT.insert ρ k T) = EnvT.insert (EnvT.cons S ρ) (k + 1) T := by
  funext i
  cases i with
  | zero => simp [EnvT.insert, EnvT.cons]
  | succ i =>
      show EnvT.insert ρ k T i = EnvT.insert (EnvT.cons S ρ) (k + 1) T (i + 1)
      simp only [EnvT.insert, EnvT.cons, Nat.succ_lt_succ_iff, Nat.succ.injEq,
        Nat.add_sub_cancel]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : i = k
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          cases i with
          | zero =>
              exact absurd (Nat.eq_zero_of_le_zero (Nat.le_of_not_lt h1)).symm h2
          | succ j => rfl

/-! ### §2 — proposition codes, type codes, semantic typing of compacts (§3.6 built in) -/

/-- Type codes: what `sort` types (`prop` included: `Prop : Type`). -/
inductive TyCodeCT : CptT → Prop
  | bot : TyCodeCT .bot
  | prop : TyCodeCT .prop
  | sort : TyCodeCT .sort
  | pi {a : CptT} {g : List (List CptT × CptT)} (ha : TyCodeCT a) (hg : ∀ t ∈ g, TyCodeCT t.2) :
      TyCodeCT (.pi a g)
  | spine (r : Nat) (args : List CptT) : TyCodeCT (.spine r args)

/-- Proposition codes, impredicatively: a Π code with a type-code domain all of whose outputs are
    proposition codes, a spine of a family declared into `Sort 0`, or `⊥`.  `prop` and `sort` are
    not proposition codes (`Prop : Type`). -/
inductive IsPropCT (E : ResolvedEnv) : CptT → Prop
  | bot : IsPropCT E .bot
  | pi {a : CptT} {g : List (List CptT × CptT)} (ha : TyCodeCT a) (h : ∀ t ∈ g, IsPropCT E t.2) :
      IsPropCT E (.pi a g)
  | spine {r : Nat} {args : List CptT} {m : CheckedMember} (hres : E.members r = some m)
      (hsort : piBody m.mtype = .sort .zero) : IsPropCT E (.spine r args)

/-- Semantic typing of compacts `u : a` with the two universe codes: the elements of `prop` are
    the proposition codes, the elements of `sort` the type codes; λ inhabits only
    non-proposition Π codes, spines only non-proposition spine codes (the landed `CTy`, with the
    universe split). -/
inductive CTyT (E : ResolvedEnv) : CptT → CptT → Prop
  | bot (a : CptT) : CTyT E .bot a
  | univProp {c : CptT} (h : IsPropCT E c) : CTyT E c .prop
  | univ {c : CptT} (h : TyCodeCT c) : CTyT E c .sort
  | lam {f : List (List CptT × CptT)} {a : CptT} {g : List (List CptT × CptT)}
      (hnp : ¬ IsPropCT E (.pi a g))
      (hdom : ∀ s ∈ f, ∀ u ∈ s.1, CTyT E u a)
      (hcod : ∀ s ∈ f, ∀ t ∈ g, (∀ u ∈ t.1, u ∈ s.1) → CTyT E s.2 t.2) :
      CTyT E (.lam f) (.pi a g)
  | spine {r r' : Nat} {args args' : List CptT} (hnp : ¬ IsPropCT E (.spine r' args')) :
      CTyT E (.spine r args) (.spine r' args')

/-- **§3.6**: every inhabitant of a proposition code is `⊥`. -/
theorem ctyT_prop_bot {E : ResolvedEnv} {a u : CptT} (hP : IsPropCT E a) (h : CTyT E u a) :
    u = .bot := by
  cases h with
  | bot => rfl
  | univProp _ => cases hP
  | univ _ => cases hP
  | lam hnp _ _ => exact absurd hP hnp
  | spine hnp => exact absurd hP hnp

theorem ctyT_bot_inv {E : ResolvedEnv} {c : CptT} (h : CTyT E c .bot) : c = .bot := by
  cases h; rfl

theorem ctyT_prop_inv {E : ResolvedEnv} {c : CptT} (h : CTyT E c .prop) : c = .bot ∨ IsPropCT E c := by
  cases h with
  | bot => exact Or.inl rfl
  | univProp h => exact Or.inr h

theorem ctyT_sort_inv {E : ResolvedEnv} {c : CptT} (h : CTyT E c .sort) : c = .bot ∨ TyCodeCT c := by
  cases h with
  | bot => exact Or.inl rfl
  | univ h => exact Or.inr h

theorem ctyT_lam_inv {E : ResolvedEnv} {c : CptT} {g : List (List CptT × CptT)}
    (h : CTyT E c (.lam g)) : c = .bot := by
  cases h; rfl

theorem ctyT_pi_inv {E : ResolvedEnv} {c a : CptT} {g : List (List CptT × CptT)}
    (h : CTyT E c (.pi a g)) :
    c = .bot ∨ ∃ f, c = .lam f ∧ ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ u ∈ s.1, CTyT E u a) ∧
      (∀ s ∈ f, ∀ t ∈ g, (∀ u ∈ t.1, u ∈ s.1) → CTyT E s.2 t.2) := by
  cases h with
  | bot => exact Or.inl rfl
  | lam hnp hdom hcod => exact Or.inr ⟨_, rfl, hnp, hdom, hcod⟩

theorem ctyT_spine_inv {E : ResolvedEnv} {c : CptT} {r' : Nat} {args' : List CptT}
    (h : CTyT E c (.spine r' args')) :
    c = .bot ∨ ∃ r args, c = .spine r args ∧ ¬ IsPropCT E (.spine r' args') := by
  cases h with
  | bot => exact Or.inl rfl
  | spine hnp => exact Or.inr ⟨_, _, rfl, hnp⟩

/-- Neither universe code is a proposition code. -/
theorem not_isPropCT_prop (E : ResolvedEnv) : ¬ IsPropCT E .prop := fun h => nomatch h
theorem not_isPropCT_sort (E : ResolvedEnv) : ¬ IsPropCT E .sort := fun h => nomatch h
theorem not_isPropCT_lam (E : ResolvedEnv) (g : List (List CptT × CptT)) : ¬ IsPropCT E (.lam g) :=
  fun h => nomatch h

/-- A proposition code is a type code. -/
theorem tyCodeCT_of_isPropCT {E : ResolvedEnv} : ∀ {c : CptT}, IsPropCT E c → TyCodeCT c
  | _, .bot => .bot
  | _, .pi ha h => .pi ha (fun t ht => tyCodeCT_of_isPropCT (h t ht))
  | _, .spine _ _ => .spine _ _

/-! #### strict semantic typing: `CTyT` plus coverage -/

theorem sizeOfT_fst_lt (s : List CptT × CptT) : sizeOf s.1 < sizeOf s := by
  cases s; simp; omega

theorem sizeOfT_snd_lt (s : List CptT × CptT) : sizeOf s.2 < sizeOf s := by
  cases s; simp; omega

theorem CptT.sizeOf_pos (c : CptT) : 0 < sizeOf c := by
  cases c <;> simp <;> omega

/-- `CTyT` plus coverage: every non-`⊥` output of a λ step has a compatible codomain step. -/
def CTyS (E : ResolvedEnv) : CptT → CptT → Prop
  | u, .bot => u = .bot
  | u, .prop => u = .bot ∨ IsPropCT E u
  | u, .sort => u = .bot ∨ TyCodeCT u
  | u, .pi a g => u = .bot ∨ ∃ f, u = .lam f ∧ ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ v ∈ s.1, CTyS E v a) ∧
      (∀ s ∈ f, ∀ t ∈ g, (∀ v ∈ t.1, v ∈ s.1) → CTyS E s.2 t.2) ∧
      (∀ s ∈ f, s.2 = .bot ∨ ∃ t ∈ g, ∀ v ∈ t.1, v ∈ s.1)
  | u, .lam _ => u = .bot
  | u, .spine r' args' => u = .bot ∨ ((∃ r args, u = .spine r args) ∧ ¬ IsPropCT E (.spine r' args'))
termination_by _ a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show t ∈ g from ‹_›)
       have h₂ := sizeOfT_snd_lt t
       omega)

theorem ctyS_bot_inv {u : CptT} (h : CTyS E u .bot) : u = .bot := by rw [CTyS] at h; exact h
theorem ctyS_prop_inv {u : CptT} (h : CTyS E u .prop) : u = .bot ∨ IsPropCT E u := by rw [CTyS] at h; exact h
theorem ctyS_sort_inv {u : CptT} (h : CTyS E u .sort) : u = .bot ∨ TyCodeCT u := by rw [CTyS] at h; exact h
theorem ctyS_lam_inv {u : CptT} {g : List (List CptT × CptT)} (h : CTyS E u (.lam g)) : u = .bot := by
  rw [CTyS] at h; exact h
theorem ctyS_pi_inv {u a : CptT} {g : List (List CptT × CptT)} (h : CTyS E u (.pi a g)) :
    u = .bot ∨ ∃ f, u = .lam f ∧ ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ v ∈ s.1, CTyS E v a) ∧
      (∀ s ∈ f, ∀ t ∈ g, (∀ v ∈ t.1, v ∈ s.1) → CTyS E s.2 t.2) ∧
      (∀ s ∈ f, s.2 = .bot ∨ ∃ t ∈ g, ∀ v ∈ t.1, v ∈ s.1) := by
  rw [CTyS] at h; exact h
theorem ctyS_spine_inv {u : CptT} {r' : Nat} {args' : List CptT} (h : CTyS E u (.spine r' args')) :
    u = .bot ∨ ((∃ r args, u = .spine r args) ∧ ¬ IsPropCT E (.spine r' args')) := by
  rw [CTyS] at h; exact h

theorem ctyS_bot (a : CptT) : CTyS E .bot a := by
  cases a <;> rw [CTyS] <;> first | rfl | exact Or.inl rfl

/-- Strict typing is typing. -/
theorem ctyT_of_ctyS : ∀ (a u : CptT), CTyS E u a → CTyT E u a
  | .bot, u, h => by rw [ctyS_bot_inv h]; exact .bot _
  | .prop, u, h => by
      rcases ctyS_prop_inv h with rfl | h
      · exact .bot _
      · exact .univProp h
  | .sort, u, h => by
      rcases ctyS_sort_inv h with rfl | h
      · exact .bot _
      · exact .univ h
  | .pi a g, u, h => by
      rcases ctyS_pi_inv h with rfl | ⟨f, rfl, hnp, hdom, hcod, _⟩
      · exact .bot _
      · exact .lam hnp (fun s hs v hv => ctyT_of_ctyS a v (hdom s hs v hv))
          (fun s hs t ht hc => ctyT_of_ctyS t.2 s.2 (hcod s hs t ht hc))
  | .lam g, u, h => by rw [ctyS_lam_inv h]; exact .bot _
  | .spine r' args', u, h => by
      rcases ctyS_spine_inv h with rfl | ⟨⟨r, args, rfl⟩, hnp⟩
      · exact .bot _
      · exact .spine hnp
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show t ∈ g from ‹_›)
       have h₂ := sizeOfT_snd_lt t
       omega)

/-- **§3.6** for strict typing. -/
theorem ctyS_prop_bot {a u : CptT} (hP : IsPropCT E a) (h : CTyS E u a) : u = .bot :=
  ctyT_prop_bot hP (ctyT_of_ctyS a u h)

/-- **The permissiveness of the universal typing**: a constant universe-valued function is typed
    at a Π code whose only codomain information is proposition-valued, because its single step
    covers no codomain step. -/
theorem ctyT_permissive (E : ResolvedEnv) :
    CTyT E (.lam [([], .sort)]) (.pi .bot [([.prop], .prop)]) := by
  refine .lam ?_ ?_ ?_
  · intro h
    cases h with
    | pi _ h => exact not_isPropCT_prop E (h ([.prop], .prop) (List.mem_singleton.mpr rfl))
  · intro s hs v hv
    have := List.mem_singleton.mp hs
    subst this
    exact (List.not_mem_nil _ hv).elim
  · intro s hs t ht hc
    have := List.mem_singleton.mp hs
    subst this
    have := List.mem_singleton.mp ht
    subst this
    exact (List.not_mem_nil _ (hc .prop (List.mem_singleton.mpr rfl))).elim

theorem not_ctyS_permissive (E : ResolvedEnv) :
    ¬ CTyS E (.lam [([], .sort)]) (.pi .bot [([.prop], .prop)]) := by
  intro h
  rcases ctyS_pi_inv h with h0 | ⟨f, hf, _, _, _, hcov⟩
  · exact CptT.noConfusion h0
  · injection hf with hf
    subst hf
    rcases hcov ([], .sort) (List.mem_singleton.mpr rfl) with h0 | ⟨t, ht, hc⟩
    · exact CptT.noConfusion h0
    · have := List.mem_singleton.mp ht
      subst this
      exact (List.not_mem_nil _ (hc .prop (List.mem_singleton.mpr rfl))).elim

/-! ### §3 — the typed-demand model -/

/-- The family of a structured ι-witness is declared into `Sort 0` (the K-free condition). -/
def PropFamilyS {E : ResolvedEnv} (w : IotaWitnessS E) : Prop := piBody w.famMember.mtype = .sort .zero

/-- Curried step function over `CptT` (`curryStep`). -/
def curryStepT : List (List CptT) → CptT → CptT
  | [], c => c
  | us :: uss, c => .lam [(us, curryStepT uss c)]

/-- Per-field spine demand vectors (`fieldDemandVectors`). -/
def fieldDemandVectorsT : List (List CptT) → List (List CptT)
  | [] => []
  | us :: uss =>
      us.map (fun u => u :: List.replicate uss.length .bot) ++
        (fieldDemandVectorsT uss).map (fun vec => .bot :: vec)

/-- The constructor-major demand (`ctorDemand`). -/
def ctorDemandT (ctorRef nparams : Nat) (us_fields : List (List CptT)) : List CptT :=
  .spine ctorRef (List.replicate nparams .bot ++ List.replicate us_fields.length .bot) ::
    (fieldDemandVectorsT us_fields).map
      (fun vec => .spine ctorRef (List.replicate nparams .bot ++ vec))

/-- The head constant of an application spine. -/
def headConst : Expr Nat → Option Nat
  | .app f _ => headConst f
  | .const r _ => some r
  | _ => none

/-- `r` is a constructor of a family declared into `Sort 0` — a proof constant. -/
def PropCtorT (E : ResolvedEnv) (r : Nat) : Prop :=
  ∃ (m : CheckedMember) (fam : Nat) (fm : CheckedMember),
    E.members r = some m ∧ m.mclass = .constructorM ∧ headConst (piBody m.mtype) = some fam ∧
    E.members fam = some fm ∧ piBody fm.mtype = .sort .zero

/-- Push argument interpretations (`EnvI.pushArgs`). -/
def EnvT.pushArgs : List (CptT → Prop) → EnvT → EnvT
  | [], ρ => ρ
  | S :: Ss, ρ => EnvT.pushArgs Ss (EnvT.cons S ρ)



/-- **The typed-demand model.**  `ApproxDI`'s clauses with the step demands of Π and λ typed at
    the domain's code, the universe code of `Sort l` reading the level, the two recursor clauses
    (strict / non-strict in a proposition major), and the proof collapse: a λ compact has a
    non-`⊥` output (`λ⊥ = ⊥`), and a constructor of a family declared into `Sort 0` denotes `⊥`. -/
inductive ApproxT (E : ResolvedEnv) : EnvT → Expr Nat → CptT → Prop
  | bot (ρ : EnvT) (e : Expr Nat) : ApproxT E ρ e .bot
  | bvar {ρ : EnvT} {i : Nat} {c : CptT} (h : ρ i c) : ApproxT E ρ (.bvar i) c
  | sort (ρ : EnvT) (l : Level) : ApproxT E ρ (.sort l) (sortCode l)
  | pi {ρ : EnvT} {A B : Expr Nat} {a : CptT} {f : List (List CptT × CptT)}
      (hA : ApproxT E ρ A a)
      (hT : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hf : ∀ s ∈ f, ApproxT E (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxT E ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvT} {A b : Expr Nat} {a : CptT} {g : List (List CptT × CptT)}
      (hA : ApproxT E ρ A a)
      (hT : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hnt : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxT E (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxT E ρ (.lam A b) (.lam g)
  | app {ρ : EnvT} {f a : Expr Nat} {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxT E ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxT E ρ a u) :
      ApproxT E ρ (.app f a) s.2
  | const (ρ : EnvT) (r : Nat) (ls : List Level) (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
      ApproxT E ρ (.const r ls) (.spine r [])
  | delta {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat} {c : CptT}
      (hdelta : DeltaConst E r m b)
      (h : ApproxT E EnvT.bot (instantiateLevels ls b) c) :
      ApproxT E ρ (.const r ls) c
  | recursor {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level) (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptT)} {us_fields : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxT E (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxT E ρ (.const w.recRef ls)
        (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)
  | recursorProp {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level) (hP : PropFamilyS w)
      {us_pre : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (h : ApproxT E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxT E ρ (.const w.recRef ls) (curryStepT (us_pre ++ [[]]) c)
  | appSpine {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxT E ρ f (.spine r args)) (ha : ApproxT E ρ a u) :
      ApproxT E ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxT E ρ (.app (.lam A b) v) c) :
      ApproxT E ρ (.letE A v b) c
  | lit {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxT E ρ (natExpand t) c) :
      ApproxT E ρ (.lit t) c

/-- **The interpretation of a type** as a set of element compacts: the union of the semantic
    typings at its approximants.  Defined after `ApproxT`; no recursion. -/
def ElT (E : ResolvedEnv) (ρ : EnvT) (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, ApproxT E ρ A a ∧ CTyS E u a

def denT (E : ResolvedEnv) (ρ : EnvT) (e : Expr Nat) : CptT → Prop := fun c => ApproxT E ρ e c

def SemEqT (E : ResolvedEnv) (ρ : EnvT) (a b : Expr Nat) : Prop :=
  ∀ c, ApproxT E ρ a c ↔ ApproxT E ρ b c

/-! #### inversions and monotonicity -/

theorem approxT_bvar_inv {E : ResolvedEnv} {ρ : EnvT} {i : Nat} {c : CptT}
    (h : ApproxT E ρ (.bvar i) c) : c = .bot ∨ ρ i c := by
  cases h with
  | bot => exact Or.inl rfl
  | bvar h => exact Or.inr h

theorem approxT_bvar_iff (E : ResolvedEnv) (ρ : EnvT) (i : Nat) (c : CptT) :
    ApproxT E ρ (.bvar i) c ↔ c = .bot ∨ ρ i c :=
  ⟨approxT_bvar_inv, fun h => h.elim (fun e => e ▸ .bot _ _) (fun h => .bvar h)⟩

theorem approxT_sort_inv {E : ResolvedEnv} {ρ : EnvT} {l : Level} {c : CptT}
    (h : ApproxT E ρ (.sort l) c) : c = .bot ∨ c = sortCode l := by
  cases h with
  | bot => exact Or.inl rfl
  | sort => exact Or.inr rfl

theorem approxT_sort_code (E : ResolvedEnv) (ρ : EnvT) (l : Level) :
    ApproxT E ρ (.sort l) (sortCode l) := .sort ρ l

theorem approxT_pi_inv {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat} {c : CptT}
    (h : ApproxT E ρ (.pi A B) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ ApproxT E ρ A a ∧
      ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧ ApproxT E (EnvT.cons (demandT s.1) ρ) B s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | pi hA hT hf => exact Or.inr ⟨_, _, rfl, hA, fun s hs => ⟨hT s hs, hf s hs⟩⟩

theorem approxT_lam_inv {E : ResolvedEnv} {ρ : EnvT} {A b : Expr Nat} {c : CptT}
    (h : ApproxT E ρ (.lam A b) c) :
    c = .bot ∨ ∃ a g, c = .lam g ∧ ApproxT E ρ A a ∧ (∃ s ∈ g, s.2 ≠ .bot) ∧
      ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧ ApproxT E (EnvT.cons (demandT s.1) ρ) b s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | lam hA hT hnt hb => exact Or.inr ⟨_, _, rfl, hA, hnt, fun s hs => ⟨hT s hs, hb s hs⟩⟩

theorem approxT_app_inv {E : ResolvedEnv} {ρ : EnvT} {f a : Expr Nat} {c : CptT}
    (h : ApproxT E ρ (.app f a) c) :
    c = .bot ∨
      (∃ g s, c = s.2 ∧ ApproxT E ρ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, ApproxT E ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxT E ρ f (.spine r args) ∧ ApproxT E ρ a u) := by
  cases h with
  | bot => exact Or.inl rfl
  | app hf hs ha => exact Or.inr (Or.inl ⟨_, _, rfl, hf, hs, ha⟩)
  | appSpine hf ha => exact Or.inr (Or.inr ⟨_, _, _, rfl, hf, ha⟩)

theorem approxT_rigid_const_inv {E : ResolvedEnv} {ρ : EnvT} {r : Nat} {ls : List Level}
    (hrigid : RigidConst E r) {c : CptT} (h : ApproxT E ρ (.const r ls) c) :
    c = .bot ∨ c = .spine r [] := by
  cases h with
  | bot => exact Or.inl rfl
  | const => exact Or.inr rfl
  | delta hd _ => exact absurd hrigid (not_rigidConst_of_deltaConst hd)
  | @recursor _ w _ _ _ _ _ _ _ _ => exact absurd w.hrecK (hrigid _ w.hrec).2
  | @recursorProp _ w _ _ _ _ _ _ => exact absurd w.hrecK (hrigid _ w.hrec).2

theorem approxT_mono_env {E : ResolvedEnv} {ρ ρ' : EnvT} (hle : EnvT.le ρ ρ') {e : Expr Nat}
    {c : CptT} (h : ApproxT E ρ e c) : ApproxT E ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _
  | bvar h => exact .bvar (hle _ _ h)
  | sort => exact .sort _ _
  | pi _ hT _ ihA ihf =>
      refine .pi (ihA hle) hT (fun s hs => (ihf s hs) ?_)
      intro i c h
      cases i with
      | zero => exact h
      | succ i => exact hle i c h
  | lam _ hT hnt _ ihA ihb =>
      refine .lam (ihA hle) hT hnt (fun s hs => (ihb s hs) ?_)
      intro i c h
      cases i with
      | zero => exact h
      | succ i => exact hle i c h
  | app _ hs _ ihf iha => exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | const _ _ _ hrigid hnp => exact .const _ _ _ hrigid hnp
  | delta hd h _ => exact .delta hd h
  | recursor ls hnp hpre hflds h _ => exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h _ => exact .recursorProp ls hP hpre h
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)

theorem approxT_pi_bot_nil (E : ResolvedEnv) (ρ : EnvT) (A B : Expr Nat) :
    ApproxT E ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-! #### the interpretation's equations -/

theorem elT_bot (E : ResolvedEnv) (ρ : EnvT) (A : Expr Nat) : ElT E ρ A .bot :=
  ⟨.bot, .bot ρ A, ctyS_bot _⟩

/-- Elements of `Sort 0` are the proposition codes (and `⊥`). -/
theorem elT_sort_zero_iff (E : ResolvedEnv) (ρ : EnvT) (u : CptT) :
    ElT E ρ (.sort .zero) u ↔ u = .bot ∨ IsPropCT E u := by
  constructor
  · rintro ⟨a, ha, hu⟩
    rcases approxT_sort_inv ha with rfl | rfl
    · exact Or.inl (ctyS_bot_inv hu)
    · rw [sortCode_zero] at hu
      exact ctyS_prop_inv hu
  · rintro (rfl | hP)
    · exact elT_bot _ _ _
    · exact ⟨.prop, sortCode_zero ▸ approxT_sort_code E ρ .zero, by rw [CTyS]; exact Or.inr hP⟩

/-- Elements of a non-proposition universe are the type codes (and `⊥`). -/
theorem elT_sort_iff (E : ResolvedEnv) (ρ : EnvT) {l : Level} (hl : ¬ eqN l .zero) (u : CptT) :
    ElT E ρ (.sort l) u ↔ u = .bot ∨ TyCodeCT u := by
  have hc : sortCode l = .sort := (sortCode_eq_sort_iff l).mpr hl
  constructor
  · rintro ⟨a, ha, hu⟩
    rcases approxT_sort_inv ha with rfl | rfl
    · exact Or.inl (ctyS_bot_inv hu)
    · rw [hc] at hu
      exact ctyS_sort_inv hu
  · rintro (rfl | hT)
    · exact elT_bot _ _ _
    · exact ⟨.sort, hc ▸ approxT_sort_code E ρ l, by rw [CTyS]; exact Or.inr hT⟩

/-- A λ element of a Π-type: a step function whose demands are typed at a code of the domain and
    whose outputs are typed at the codomain's codes. -/
theorem elT_pi_lam_inv {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat} {f : List (List CptT × CptT)}
    (h : ElT E ρ (.pi A B) (.lam f)) :
    ∃ a g, ApproxT E ρ A a ∧
      (∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧ ApproxT E (EnvT.cons (demandT s.1) ρ) B s.2) ∧
      ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a) ∧
      (∀ s ∈ f, ∀ t ∈ g, (∀ u ∈ t.1, u ∈ s.1) → CTyS E s.2 t.2) := by
  obtain ⟨c, hc, hu⟩ := h
  rcases approxT_pi_inv hc with rfl | ⟨a, g, rfl, hA, hg⟩
  · exact (CptT.noConfusion (ctyS_bot_inv hu))
  · rcases ctyS_pi_inv hu with h0 | ⟨f', hf', hnp, hdom, hcod, _⟩
    · exact CptT.noConfusion h0
    · injection hf' with hf'
      subst hf'
      exact ⟨a, g, hA, hg, hnp, hdom, hcod⟩

/-- A Π-type has no universe element. -/
theorem not_elT_pi_sort {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat} : ¬ ElT E ρ (.pi A B) .sort := by
  rintro ⟨c, hc, hu⟩
  rcases approxT_pi_inv hc with rfl | ⟨a, g, rfl, _, _⟩
  · exact CptT.noConfusion (ctyS_bot_inv hu)
  · rcases ctyS_pi_inv hu with h0 | ⟨_, h0, _⟩ <;> exact CptT.noConfusion h0

/-- **The collapse.**  If every approximant of `A` is a proposition code, `A` has no element
    but `⊥`. -/
theorem elT_bot_of_propIdeal {E : ResolvedEnv} {ρ : EnvT} {A : Expr Nat}
    (hP : ∀ a, ApproxT E ρ A a → IsPropCT E a) {u : CptT} (h : ElT E ρ A u) : u = .bot := by
  obtain ⟨a, ha, hu⟩ := h
  exact ctyS_prop_bot (hP a ha) hu

/-! ### §4 — the `⊥`-demand fragment, and the probe instances -/

/-- `⊥` demands over `CptT`. -/
def BotDemandT (us : List CptT) : Prop := ∀ u ∈ us, u = .bot

/-- The `⊥`-demand fragment (the `BotPiCpt` shapes over `CptT`). -/
inductive BotPiCptT : CptT → Prop
  | bot : BotPiCptT .bot
  | prop : BotPiCptT .prop
  | sort : BotPiCptT .sort
  | pi {a : CptT} {f : List (List CptT × CptT)} (ha : BotPiCptT a) (hbd : ∀ s ∈ f, BotDemandT s.1)
      (hf : ∀ s ∈ f, BotPiCptT s.2) : BotPiCptT (.pi a f)

/-- On `⊥` demands the typing side condition of the Π clause is vacuous: the fragment's clause
    is `ApproxDI`'s clause. -/
theorem approxT_pi_botDemand_iff {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
    {f : List (List CptT × CptT)} (hbd : ∀ s ∈ f, BotDemandT s.1) :
    ApproxT E ρ (.pi A B) (.pi a f) ↔
      ApproxT E ρ A a ∧ ∀ s ∈ f, ApproxT E (EnvT.cons (demandT s.1) ρ) B s.2 := by
  constructor
  · intro h
    rcases approxT_pi_inv h with h0 | ⟨a', f', e, hA, hf⟩
    · exact CptT.noConfusion h0
    · injection e with ea ef
      subst ea; subst ef
      exact ⟨hA, fun s hs => (hf s hs).2⟩
  · rintro ⟨hA, hf⟩
    exact .pi hA (fun s hs u hu => by rw [hbd s hs u hu]; exact ctyS_bot a) hf

theorem approxT_lam_botDemand_iff {E : ResolvedEnv} {ρ : EnvT} {A b : Expr Nat}
    {g : List (List CptT × CptT)} (hbd : ∀ s ∈ g, BotDemandT s.1) :
    ApproxT E ρ (.lam A b) (.lam g) ↔
      (∃ s ∈ g, s.2 ≠ .bot) ∧ ∀ s ∈ g, ApproxT E (EnvT.cons (demandT s.1) ρ) b s.2 := by
  constructor
  · intro h
    rcases approxT_lam_inv h with h0 | ⟨a', g', e, _, hnt, hg⟩
    · exact CptT.noConfusion h0
    · injection e with eg
      subst eg
      exact ⟨hnt, fun s hs => (hg s hs).2⟩
  · rintro ⟨hnt, hg⟩
    exact .lam (.bot ρ A) (fun s hs u hu => by rw [hbd s hs u hu]; exact ctyS_bot .bot) hnt hg

/-! #### W-DEMAND in the typed model -/

/-- The W-DEMAND compact, over `CptT`: domain code `prop`, one step demanding `sort` on `P`. -/
def idPiPropSortStepT : CptT := .pi .prop [([.sort], .sort)]

/-- **The refuting compact is not a typed compact**: the demand `sort` on `P : Prop` is not a
    proposition code. -/
theorem not_approxT_idPiProp_sortStep (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ApproxT E ρ idPiProp idPiPropSortStepT := by
  intro h
  rcases approxT_pi_inv h with h0 | ⟨a, f, e, _, hf⟩
  · exact CptT.noConfusion h0
  · injection e with ea ef
    subst ea; subst ef
    have h1 := (hf ([.sort], .sort) (List.mem_singleton.mpr rfl)).1 .sort (List.mem_singleton.mpr rfl)
    rcases ctyS_prop_inv h1 with h2 | h2
    · exact CptT.noConfusion h2
    · exact not_isPropCT_sort E h2

/-- **Every typed compact of `Π (P : Sort 0), P` is a proposition code**: the typed model sees
    the impredicative Π as a proposition (contrast `not_isPropIdealI_pi_propBinder_bot` for the
    untyped model). -/
theorem isPropCT_of_approxT_idPiProp {E : ResolvedEnv} {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ idPiProp c) : IsPropCT E c := by
  rcases approxT_pi_inv h with rfl | ⟨a, f, rfl, hA, hf⟩
  · exact .bot
  · have hta : TyCodeCT a := by
      rcases approxT_sort_inv hA with rfl | rfl
      · exact .bot
      · rw [sortCode_zero]; exact .prop
    refine .pi hta (fun s hs => ?_)
    obtain ⟨hdem, hB⟩ := hf s hs
    rcases approxT_sort_inv hA with rfl | rfl
    · -- domain code `⊥`: only `⊥` demands, so `P` denotes `⊥`
      rcases approxT_bvar_inv hB with h0 | h0
      · rw [h0]; exact .bot
      · have := hdem s.2 h0
        rw [ctyS_bot_inv this]; exact .bot
    · rw [sortCode_zero] at hdem
      rcases approxT_bvar_inv hB with h0 | h0
      · rw [h0]; exact .bot
      · rcases ctyS_prop_inv (hdem s.2 h0) with h1 | h1
        · rw [h1]; exact .bot
        · exact h1

/-- Hence the elements of `Π (P : Sort 0), P` are `⊥` — its proofs collapse. -/
theorem elT_idPiProp_bot (E : ResolvedEnv) (ρ : EnvT) {u : CptT} (h : ElT E ρ idPiProp u) :
    u = .bot :=
  elT_bot_of_propIdeal (fun _ ha => isPropCT_of_approxT_idPiProp ha) h

/-! #### the collapse at proposition domains (what dissolves `AppPropArgs`) -/

/-- At a proposition domain code every step demand of a Π compact is `⊥`. -/
theorem approxT_pi_prop_dom_botDemand {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
    {f : List (List CptT × CptT)} (h : ApproxT E ρ (.pi A B) (.pi a f)) (hP : IsPropCT E a) :
    ∀ s ∈ f, BotDemandT s.1 := by
  rcases approxT_pi_inv h with h0 | ⟨a', f', e, _, hf⟩
  · exact CptT.noConfusion h0
  · injection e with ea ef
    subst ea; subst ef
    exact fun s hs u hu => ctyS_prop_bot hP ((hf s hs).1 u hu)

/-- ... and of a λ compact whose annotation has a proposition code. -/
theorem approxT_lam_prop_dom_botDemand {E : ResolvedEnv} {ρ : EnvT} {A b : Expr Nat}
    {g : List (List CptT × CptT)} (h : ApproxT E ρ (.lam A b) (.lam g))
    (hP : ∀ a, ApproxT E ρ A a → IsPropCT E a) : ∀ s ∈ g, BotDemandT s.1 := by
  rcases approxT_lam_inv h with h0 | ⟨a, g', e, hA, _, hg⟩
  · exact CptT.noConfusion h0
  · injection e with eg
    subst eg
    exact fun s hs u hu => ctyS_prop_bot (hP a hA) ((hg s hs).1 u hu)

/-! #### W-K's model side: proofs of `True` are `⊥` -/

/-- `True`'s only code is its (proposition) spine. -/
theorem isPropCT_true_spine (args : List CptT) : IsPropCT trueEnvU (.spine 0 args) :=
  .spine (m := ⟨.inductiveM, 0, .sort .zero, none⟩) rfl rfl

theorem approxT_true_inv {ρ : EnvT} {c : CptT} (h : ApproxT trueEnvU ρ (.const 0 []) c) :
    c = .bot ∨ c = .spine 0 [] :=
  approxT_rigid_const_inv (fun m hm => by
    have e : (⟨.inductiveM, 0, .sort .zero, none⟩ : CheckedMember) = m := Option.some.inj hm
    subst e
    exact ⟨Or.inl rfl, MemberClass.noConfusion⟩) h

/-- **Elements of `True` are `⊥`**: a proof major can only be demanded at `⊥`. -/
theorem elT_true_bot (ρ : EnvT) {u : CptT} (h : ElT trueEnvU ρ (.const 0 []) u) : u = .bot :=
  elT_bot_of_propIdeal (fun a ha => by
    rcases approxT_true_inv ha with rfl | rfl
    · exact .bot
    · exact isPropCT_true_spine []) h

/-! ### §5 — lifting, the context environment, and W-ZETALOCAL -/

theorem approxT_lift_intro {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e c) :
    ∀ (k : Nat) (S : CptT → Prop), ApproxT E (EnvT.insert ρ k S) (lift k 1 e) c := by
  induction h with
  | bot => intro k S; exact .bot _ _
  | @bvar ρ i c h =>
      intro k S
      simp only [lift]
      by_cases hk : k ≤ i
      · rw [if_pos hk]
        refine .bvar ?_
        simp only [EnvT.insert]
        rw [if_neg (by omega), if_neg (by omega)]
        simpa using h
      · rw [if_neg hk]
        refine .bvar ?_
        simp only [EnvT.insert]
        rw [if_pos (by omega)]
        exact h
  | sort => intro k S; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro k S
      simp only [lift]
      refine .pi (ihA k S) hT (fun s hs => ?_)
      rw [EnvT.cons_insert]
      exact ihf s hs (k + 1) S
  | lam _ hT hnt _ ihA ihb =>
      intro k S
      simp only [lift]
      refine .lam (ihA k S) hT hnt (fun s hs => ?_)
      rw [EnvT.cons_insert]
      exact ihb s hs (k + 1) S
  | app _ hs _ ihf iha =>
      intro k S
      simp only [lift]
      exact .app (ihf k S) hs (fun u hu => iha u hu k S)
  | const _ _ _ hrigid hnp => intro k S; simp only [lift]; exact .const _ _ _ hrigid hnp
  | delta hd h _ => intro k S; simp only [lift]; exact .delta hd h
  | recursor ls hnp hpre hflds h _ => intro k S; simp only [lift]; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h _ => intro k S; simp only [lift]; exact .recursorProp ls hP hpre h
  | appSpine _ _ ihf iha =>
      intro k S
      simp only [lift]
      exact .appSpine (ihf k S) (iha k S)
  | letE _ ih =>
      intro k S
      simp only [lift]
      exact .letE (by simpa [lift] using ih k S)
  | lit _ ih =>
      intro k S
      simp only [lift]
      exact .lit (by simpa [natExpand_lift] using ih k S)

theorem approxT_lift_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvT} {k : Nat} {S : CptT → Prop} {c : CptT},
      ApproxT E (EnvT.insert ρ k S) (lift k 1 e) c → ApproxT E ρ e c
  | .bvar i, ρ, k, S, c, h => by
      simp only [lift] at h
      by_cases hk : k ≤ i
      · rw [if_pos hk] at h
        rcases approxT_bvar_inv h with h0 | h0
        · exact h0 ▸ .bot _ _
        · refine .bvar ?_
          simp only [EnvT.insert] at h0
          rw [if_neg (by omega), if_neg (by omega)] at h0
          simpa using h0
      · rw [if_neg hk] at h
        rcases approxT_bvar_inv h with h0 | h0
        · exact h0 ▸ .bot _ _
        · refine .bvar ?_
          simp only [EnvT.insert] at h0
          rw [if_pos (by omega)] at h0
          exact h0
  | .sort l, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxT_sort_inv h with rfl | rfl
      · exact .bot _ _
      · exact .sort _ _
  | .const r ls, ρ, k, S, c, h => by
      simp only [lift] at h
      cases h with
      | bot => exact .bot _ _
      | const _ _ _ hrigid hnp => exact .const _ _ _ hrigid hnp
      | delta hd h => exact .delta hd h
      | recursor ls hnp hpre hflds h => exact .recursor ls hnp hpre hflds h
      | recursorProp ls hP hpre h => exact .recursorProp ls hP hpre h
  | .app f a, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨r, args, u, rfl, hf, ha⟩
      · exact .bot _ _
      · exact .app (approxT_lift_elim f hf) hs (fun u hu => approxT_lift_elim a (ha u hu))
      · exact .appSpine (approxT_lift_elim f hf) (approxT_lift_elim a ha)
  | .lam A b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxT_lam_inv h with rfl | ⟨a, g, rfl, hA, hnt, hg⟩
      · exact .bot _ _
      · refine .lam (approxT_lift_elim A hA) (fun s hs => (hg s hs).1) hnt (fun s hs => ?_)
        have := (hg s hs).2
        rw [EnvT.cons_insert] at this
        exact approxT_lift_elim b this
  | .pi A B, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxT_pi_inv h with rfl | ⟨a, f, rfl, hA, hf⟩
      · exact .bot _ _
      · refine .pi (approxT_lift_elim A hA) (fun s hs => (hf s hs).1) (fun s hs => ?_)
        have := (hf s hs).2
        rw [EnvT.cons_insert] at this
        exact approxT_lift_elim B this
  | .letE A v b, ρ, k, S, c, h => by
      simp only [lift] at h
      cases h with
      | bot => exact .bot _ _
      | letE h =>
          rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨r, args, u, rfl, hf, ha⟩
          · exact .letE (.bot _ _)
          · rcases approxT_lam_inv hf with h1 | ⟨a', g', e, hA', hnt', hg'⟩
            · cases h1
            · injection e with eg
              subst eg
              exact .letE (.app
                (.lam (approxT_lift_elim A hA')
                  (fun s' hs' => (hg' s' hs').1)
                  hnt'
                  (fun s' hs' => approxT_lift_elim b (by
                    have := (hg' s' hs').2
                    rw [EnvT.cons_insert] at this
                    exact this)))
                hs
                (fun u hu => approxT_lift_elim v (ha u hu)))
          · rcases approxT_lam_inv hf with h1 | ⟨a', g', e, _, _, _⟩
            · cases h1
            · cases e
  | .lit t, ρ, k, S, c, h => by
      simp only [lift] at h
      cases h with
      | bot => exact .bot _ _
      | lit h =>
          refine .lit ?_
          have constEnv : ∀ {r : Nat} {c₀ : CptT} {ρ₁ ρ₂ : EnvT},
              ApproxT E ρ₁ (.const r []) c₀ → ApproxT E ρ₂ (.const r []) c₀ := by
            intro r c₀ ρ₁ ρ₂ h
            generalize hge : (Expr.const r [] : Expr Nat) = e at h
            cases h with
            | bot => cases hge; exact .bot _ _
            | bvar => cases hge
            | sort => cases hge
            | pi => cases hge
            | lam => cases hge
            | app => cases hge
            | const _ _ _ hrigid hnp => cases hge; exact .const _ _ _ hrigid hnp
            | delta hd hh => cases hge; exact .delta hd hh
            | recursor ls hnp hpre hflds hh => cases hge; exact .recursor [] hnp hpre hflds hh
            | recursorProp ls hP hpre hh => cases hge; exact .recursorProp [] hP hpre hh
            | appSpine => cases hge
            | letE => cases hge
            | lit => cases hge
          have aux : ∀ (t : Nat) {c : CptT} {ρ' : EnvT},
              ApproxT E ρ' (natExpand t) c → ApproxT E ρ (natExpand t) c := by
            intro t
            induction t with
            | zero =>
                intro c ρ' h'
                exact constEnv h'
            | succ t ih =>
                intro c ρ' h'
                rcases approxT_app_inv h' with rfl | ⟨g, s, rfl, hf, hs, ha⟩
                  | ⟨r, args, u, rfl, hf, ha⟩
                · exact .bot _ _
                · exact .app (constEnv hf) hs (fun u hu => ih (ha u hu))
                · exact .appSpine (constEnv hf) (ih ha)
          exact aux t h

theorem approxT_cons_lift0_iff (E : ResolvedEnv) (ρ : EnvT) (S : CptT → Prop) (e : Expr Nat)
    (c : CptT) : ApproxT E (EnvT.cons S ρ) (lift 0 1 e) c ↔ ApproxT E ρ e c := by
  rw [← EnvT.insert_zero S ρ]
  exact ⟨approxT_lift_elim e, fun h => approxT_lift_intro h 0 S⟩

/-- A context environment for the typed model: every let-bound variable denotes its value. -/
def CtxEnvT (E : ResolvedEnv) (Γ : LCtx) (ρ : EnvT) : Prop :=
  ∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v → SemEqT E ρ (.bvar i) v

/-- The canonical context environment. -/
def ctxEnvT (E : ResolvedEnv) : LCtx → EnvT
  | [] => EnvT.bot
  | .assumption _ :: Γ => EnvT.cons botSetT (ctxEnvT E Γ)
  | .letBinding _ v :: Γ => EnvT.cons (denT E (ctxEnvT E Γ) v) (ctxEnvT E Γ)

theorem ctxEnvT_respects (E : ResolvedEnv) : ∀ (Γ : LCtx), CtxEnvT E Γ (ctxEnvT E Γ)
  | [] => fun i _ hw => by cases i <;> exact nomatch hw
  | .assumption A :: Γ => by
      intro i w hw
      cases i with
      | zero => exact nomatch hw
      | succ j =>
          rw [Rcic.Declarative.lookupValue_cons_succ] at hw
          cases hv : lookupValue Γ j with
          | none => rw [hv] at hw; exact nomatch hw
          | some v =>
              rw [hv] at hw
              have e : w = lift 0 1 v := (Option.some.inj hw).symm
              subst e
              intro c
              rw [show ctxEnvT E (.assumption A :: Γ) =
                    EnvT.cons botSetT (ctxEnvT E Γ) from rfl,
                approxT_cons_lift0_iff]
              have ih := ctxEnvT_respects E Γ j v hv c
              rw [approxT_bvar_iff] at ih ⊢
              exact ih
  | .letBinding A v₀ :: Γ => by
      intro i w hw
      cases i with
      | zero =>
          have e : w = lift 0 1 v₀ := (Option.some.inj hw).symm
          subst e
          intro c
          rw [show ctxEnvT E (.letBinding A v₀ :: Γ) =
                EnvT.cons (denT E (ctxEnvT E Γ) v₀) (ctxEnvT E Γ) from rfl,
            approxT_cons_lift0_iff, approxT_bvar_iff]
          constructor
          · rintro (rfl | h)
            · exact .bot _ _
            · exact h
          · intro h; exact Or.inr h
      | succ j =>
          rw [Rcic.Declarative.lookupValue_cons_succ] at hw
          cases hv : lookupValue Γ j with
          | none => rw [hv] at hw; exact nomatch hw
          | some v =>
              rw [hv] at hw
              have e : w = lift 0 1 v := (Option.some.inj hw).symm
              subst e
              intro c
              rw [show ctxEnvT E (.letBinding A v₀ :: Γ) =
                    EnvT.cons (denT E (ctxEnvT E Γ) v₀) (ctxEnvT E Γ) from rfl,
                approxT_cons_lift0_iff]
              have ih := ctxEnvT_respects E Γ j v hv c
              rw [approxT_bvar_iff] at ih ⊢
              exact ih

/-- `zetaLocal` is sound in the typed model at every context environment. -/
theorem semEqT_zetaLocal {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hctx : CtxEnvT E Γ ρ)
    {i : Nat} {v : Expr Nat} (hv : lookupValue Γ i = some v) : SemEqT E ρ (.bvar i) v :=
  hctx i v hv

/-- W-ZETALOCAL's `piRow` instance in the typed model. -/
theorem semEqT_ctxEnvT_zetaLocalPiCtx (E : ResolvedEnv) :
    SemEqT E (ctxEnvT E zetaLocalPiCtx) (.bvar 0) idPiProp :=
  semEqT_zetaLocal (ctxEnvT_respects E zetaLocalPiCtx) rfl

/-- `ctxEnvT` at an assumption is `{⊥}`. -/
theorem ctxEnvT_none_bot (E : ResolvedEnv) : ∀ (Γ : LCtx) (i : Nat), lookupValue Γ i = none →
    ∀ c, ctxEnvT E Γ i c → c = .bot
  | [], _, _, _, h => h
  | .assumption _ :: Γ, i, h0, c, h => by
      cases i with
      | zero => exact h
      | succ i =>
          apply ctxEnvT_none_bot E Γ i _ c h
          have := h0
          rw [Rcic.Declarative.lookupValue_cons_succ] at this
          cases hv : lookupValue Γ i with
          | none => rfl
          | some v => rw [hv] at this; exact Option.noConfusion this
  | .letBinding _ _ :: Γ, i, h0, c, h => by
      cases i with
      | zero => exact Option.noConfusion h0
      | succ i =>
          apply ctxEnvT_none_bot E Γ i _ c h
          have := h0
          rw [Rcic.Declarative.lookupValue_cons_succ] at this
          cases hv : lookupValue Γ i with
          | none => rfl
          | some v => rw [hv] at this; exact Option.noConfusion this

#print axioms CptT
#print axioms sortCode
#print axioms sortCode_eq_prop_iff
#print axioms sortCode_eq_sort_iff
#print axioms sortCode_zero
#print axioms sortCode_prop_or_sort
#print axioms EnvT
#print axioms EnvT.bot
#print axioms EnvT.cons
#print axioms EnvT.insert
#print axioms EnvT.le
#print axioms demandT
#print axioms botSetT
#print axioms EnvT.insert_zero
#print axioms EnvT.cons_insert
#print axioms IsPropCT
#print axioms TyCodeCT
#print axioms CTyT
#print axioms ctyT_prop_bot
#print axioms ctyT_bot_inv
#print axioms ctyT_prop_inv
#print axioms ctyT_sort_inv
#print axioms ctyT_lam_inv
#print axioms ctyT_pi_inv
#print axioms ctyT_spine_inv
#print axioms not_isPropCT_prop
#print axioms not_isPropCT_sort
#print axioms not_isPropCT_lam
#print axioms tyCodeCT_of_isPropCT
#print axioms sizeOfT_fst_lt
#print axioms sizeOfT_snd_lt
#print axioms CptT.sizeOf_pos
#print axioms CTyS
#print axioms ctyS_bot_inv
#print axioms ctyS_prop_inv
#print axioms ctyS_sort_inv
#print axioms ctyS_lam_inv
#print axioms ctyS_pi_inv
#print axioms ctyS_spine_inv
#print axioms ctyS_bot
#print axioms ctyT_of_ctyS
#print axioms ctyS_prop_bot
#print axioms ctyT_permissive
#print axioms not_ctyS_permissive
#print axioms PropFamilyS
#print axioms curryStepT
#print axioms fieldDemandVectorsT
#print axioms ctorDemandT
#print axioms EnvT.pushArgs
#print axioms headConst
#print axioms PropCtorT
#print axioms ApproxT
#print axioms ElT
#print axioms denT
#print axioms SemEqT
#print axioms approxT_bvar_inv
#print axioms approxT_bvar_iff
#print axioms approxT_sort_inv
#print axioms approxT_sort_code
#print axioms approxT_pi_inv
#print axioms approxT_lam_inv
#print axioms approxT_app_inv
#print axioms approxT_rigid_const_inv
#print axioms approxT_mono_env
#print axioms approxT_pi_bot_nil
#print axioms elT_bot
#print axioms elT_sort_zero_iff
#print axioms elT_sort_iff
#print axioms elT_pi_lam_inv
#print axioms not_elT_pi_sort
#print axioms elT_bot_of_propIdeal
#print axioms BotDemandT
#print axioms BotPiCptT
#print axioms approxT_pi_botDemand_iff
#print axioms approxT_lam_botDemand_iff
#print axioms idPiPropSortStepT
#print axioms not_approxT_idPiProp_sortStep
#print axioms isPropCT_of_approxT_idPiProp
#print axioms elT_idPiProp_bot
#print axioms approxT_pi_prop_dom_botDemand
#print axioms approxT_lam_prop_dom_botDemand
#print axioms isPropCT_true_spine
#print axioms approxT_true_inv
#print axioms elT_true_bot
#print axioms approxT_lift_intro
#print axioms approxT_lift_elim
#print axioms approxT_cons_lift0_iff
#print axioms CtxEnvT
#print axioms ctxEnvT
#print axioms ctxEnvT_respects
#print axioms semEqT_zetaLocal
#print axioms semEqT_ctxEnvT_zetaLocalPiCtx
#print axioms ctxEnvT_none_bot

end Rcic.Declarative.NativeValleys.TypedModelAudit
