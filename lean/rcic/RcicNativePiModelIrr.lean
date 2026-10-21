import rcic.RcicNativePiModelIdeal
import rcic.RcicNativePiModelLR
import rcic.RcicParRedT

/-!
# RcicNativePiModelIrr — the proof-irrelevance (finitary projection) layer over the ideal model

Built over devin-fcd's ideal approximation relation `ApproxI` (`RcicNativePiModelIdeal`,
devin/fcd7: compacts `CptI` with bounded steps, set-valued environments `EnvI`, finite-demand
factorization, substitution and β-soundness). New definitions only; nothing there is edited.
Paper: Carneiro–Coquand–Frabetti Mathieu–Lennon-Bertrand–Melliès–Weirich, *Definitional
Inversion, Without Normalisation* (arXiv 2607.13662), §2.2 (semantic typing of compacts), Fig. 4
(typed λ/Π semantics), §3.6 (a universe of strict propositions: "if `u : a : Prop` then `u = ⊥`").

**What the layer is.**  ChatGPT #7613/#7619: `irr` is not sound for the untyped model — two
proofs of one proposition have different untyped denotations, and proofs occur inside types.
The paper's answer is to interpret types by finitary projections and to make every proposition
one-point.  Over `CptI`:

* `IsPropC` — proposition codes, impredicatively: a Π code is a proposition iff all its codomain
  codes are (whatever the domain); a spine code iff its family is declared into `Sort 0`.
* `CTy E u a` — semantic typing of compacts (§2.2), with the §3.6 constraint BUILT IN: λ inhabits
  only non-proposition Π codes, spines only non-proposition spine codes, so `cty_prop_bot`:
  every inhabitant of a proposition code is `⊥` (the paper's coalescing `λ(⊥) = ⊥`).
* `tprojI E T` — the typed projector at the type ideal `T` (keep the compacts typed at some code
  of `T`), a finitary projection (`tyProjI : ProjI`: deflationary, idempotent, monotone); at a
  proposition ideal it is one-point (`tprojI_prop`).
* `PEqI E ρ A a b` — projected equality at a type.  **`ConvT.irr` is sound**: `pEqI_irr` at a
  proposition ideal, `pEqI_convT_irr` for the native constructor given `PropDen` (types typed at
  `Sort 0` denote proposition ideals at fitting environments).
* **Stability.**  Under substitution: the projector commutes with semantic substitution
  (`denI_instantiate0`, `pEqI_subst`) — from fcd7's `approxI_subst_intro`/`_elim`.  Under
  dependent application: if the function's steps demand only typed arguments at a proposition
  domain (`DomTyped`, the paper's `dom(f, a)`) and it has no spine elements, its application does
  not see which proof it is given (`semEqI_app_stable`, `pEqI_app_stable`).
* **K via irr + ι** (`pEqI_k_of_irr_iota`): `rec M m h ≡ m` for a proof `h` of a proposition is
  the composite of `irr` (`h ≡ refl`), stability of the eliminator in its major, and ι at `refl`.

**What fails over fcd7's model as it stands (admitted, compiled).**
* (O1) The model has ONE universe code: `approxI_sort_collapse` (`⟦Sort 0⟧ = ⟦Sort 1⟧`).  Hence
  `irr_unsound_of_universe_code`: for ANY code typing in which the universe code types a code with
  a non-`⊥` inhabitant (needed for `Nat : Sort 1` already), semantic fitting lets a
  proposition variable be interpreted by that code, and the projections of two proofs differ —
  at the context `P : Sort 0, p : P, q : P`, where the native `ConvT.irr` derivation exists
  (`irrCtx_conv`).  Instance: `irr_unsound_collapsed` for `CTy`, and `not_propDen_collapsed`
  (`PropDen` is false).  Repair (§3.6): a code `Prop` below `U`, with `⟦Sort l⟧` reading the level
  (proposition universe exactly when the level is zero), and `Ty u Prop` only for proposition codes.
* (O2) fcd7's λ is untyped: its steps demand arbitrary compacts (`lam_id_not_domTyped`), so the dom
  condition `DomTyped` that application-stability needs is not met; the repair is the typed λ/Π of
  the paper's Fig. 4 (demands restricted to the domain type).
* (O3) Recursors are opaque constant spines in `ApproxI`, and spine extension consumes the
  argument's codes (`approxI_app_const_spine`); so ι — and with it K — needs recursor semantics,
  non-strict in a proposition major.  `pEqI_k_of_irr_iota` takes that as its ι and stability
  hypotheses.

**What `LRTypeI` (#7628) needs from irr.**  `FundamentalLRI` is stated at the degenerate
environment `EnvI.bot`.  There every proof VARIABLE is `{⊥}` (`isPropIdealI_bvar_bot`,
`pEqI_irr_bvar_bot`), so (O1) does not bite at the root.  But Π evaluates its codomain at
`cons (demand us) ⊥` with ARBITRARY demands, so the impredicative `Π Q : Sort 0, Q` is not a
proposition ideal even at `⊥` (`not_isPropIdealI_pi_propBinder_bot`): the irr case cannot go
through `PropDen` at `⊥` without the typed Π (dom condition) and a `Prop` code.  Types depend on
proofs only through large elimination, so once ι is sound (non-strict recursors on K-eligible
proposition majors) the readback `WhRed` also needs K-reduction (`rec M m h ↝ m` for any `h`),
or the Π clause fails on the side whose major is a variable; that is the exact remaining object
behind "K via irr + ι" for the relation.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIrrAudit

open Rcic.Declarative.NativeValleys.PiModelIdealAudit

/-! ### proposition codes, type codes, semantic typing of compacts -/

/-- Proposition codes, impredicatively. -/
inductive IsPropC (E : ResolvedEnv) : CptI → Prop
  | bot : IsPropC E .bot
  | pi {a : CptI} {g : List (List CptI × CptI)} (h : ∀ t ∈ g, IsPropC E t.2) :
      IsPropC E (.pi a g)
  | spine {r : Nat} {args : List CptI} {m : CheckedMember} (hres : E.members r = some m)
      (hsort : piBody m.mtype = .sort .zero) : IsPropC E (.spine r args)

/-- Type codes: what the universe code types. -/
inductive TyCodeC : CptI → Prop
  | bot : TyCodeC .bot
  | sort : TyCodeC .sort
  | pi {a : CptI} {g : List (List CptI × CptI)} (ha : TyCodeC a) (hg : ∀ t ∈ g, TyCodeC t.2) :
      TyCodeC (.pi a g)
  | spine (r : Nat) (args : List CptI) : TyCodeC (.spine r args)

/-- Semantic typing of compacts `u : a` (§2.2), with the §3.6 constraint built in: λ inhabits
    only non-proposition Π codes, spines only non-proposition spine codes.  A λ step's output is
    typed at every codomain code whose demand it covers (stated universally: the kernel refuses
    a nested occurrence under `∃`). -/
inductive CTy (E : ResolvedEnv) : CptI → CptI → Prop
  | bot (a : CptI) : CTy E .bot a
  | univ {c : CptI} (h : TyCodeC c) : CTy E c .sort
  | lam {f : List (List CptI × CptI)} {a : CptI} {g : List (List CptI × CptI)}
      (hnp : ¬ IsPropC E (.pi a g))
      (hdom : ∀ s ∈ f, ∀ u ∈ s.1, CTy E u a)
      (hcod : ∀ s ∈ f, ∀ t ∈ g, (∀ u ∈ t.1, u ∈ s.1) → CTy E s.2 t.2) :
      CTy E (.lam f) (.pi a g)
  | spine {r r' : Nat} {args args' : List CptI} (hnp : ¬ IsPropC E (.spine r' args')) :
      CTy E (.spine r args) (.spine r' args')

/-- **§3.6**: every inhabitant of a proposition code is `⊥`. -/
theorem cty_prop_bot {E : ResolvedEnv} {a u : CptI} (hP : IsPropC E a) (h : CTy E u a) :
    u = .bot := by
  cases h with
  | bot => rfl
  | univ _ => cases hP
  | lam hnp _ _ => exact absurd hP hnp
  | spine hnp => exact absurd hP hnp

/-- An ideal of proposition codes. -/
def IsPropIdealI (E : ResolvedEnv) (T : CptI → Prop) : Prop := ∀ a, T a → IsPropC E a

/-! ### the typed projector -/

/-- The typed projector at a type ideal `T`: keep the compacts typed at some code of `T`. -/
def tprojI (E : ResolvedEnv) (T S : CptI → Prop) : CptI → Prop :=
  fun u => S u ∧ ∃ a, T a ∧ CTy E u a

/-- Finitary projections on sets of compacts. -/
structure ProjI where
  run : (CptI → Prop) → CptI → Prop
  defl : ∀ S u, run S u → S u
  idem : ∀ S u, run (run S) u ↔ run S u
  mono : ∀ S S', (∀ u, S u → S' u) → ∀ u, run S u → run S' u

/-- The typed projector is a finitary projection. -/
def tyProjI (E : ResolvedEnv) (T : CptI → Prop) : ProjI where
  run := tprojI E T
  defl := fun _ _ h => h.1
  idem := fun _ _ => ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩
  mono := fun _ _ hSS' _ h => ⟨hSS' _ h.1, h.2⟩

/-- Every denotation contains `⊥`. -/
theorem denI_bot (ρ : EnvI) (e : Expr Nat) : denI ρ e .bot := .bot ρ e

/-- `⊥` survives every projection of a denotation at a type denotation. -/
theorem tprojI_bot (E : ResolvedEnv) (ρ : EnvI) (A e : Expr Nat) :
    tprojI E (denI ρ A) (denI ρ e) .bot :=
  ⟨denI_bot ρ e, .bot, denI_bot ρ A, .bot _⟩

/-- At a proposition ideal the projector is one-point. -/
theorem tprojI_prop {E : ResolvedEnv} {T S : CptI → Prop} (hT : IsPropIdealI E T)
    (hTb : T .bot) (hSb : S .bot) (u : CptI) : tprojI E T S u ↔ u = .bot := by
  constructor
  · rintro ⟨_, a, ha, hc⟩
    exact cty_prop_bot (hT a ha) hc
  · rintro rfl
    exact ⟨hSb, .bot, hTb, .bot _⟩

/-! ### projected equality and the `irr` clause -/

/-- Projected equality at a type. -/
def PEqI (E : ResolvedEnv) (ρ : EnvI) (A a b : Expr Nat) : Prop :=
  ∀ u, tprojI E (denI ρ A) (denI ρ a) u ↔ tprojI E (denI ρ A) (denI ρ b) u

theorem PEqI.refl (E : ResolvedEnv) (ρ : EnvI) (A a : Expr Nat) : PEqI E ρ A a a :=
  fun _ => Iff.rfl

theorem PEqI.symm {E : ResolvedEnv} {ρ : EnvI} {A a b : Expr Nat} (h : PEqI E ρ A a b) :
    PEqI E ρ A b a := fun u => (h u).symm

theorem PEqI.trans {E : ResolvedEnv} {ρ : EnvI} {A a b c : Expr Nat} (h₁ : PEqI E ρ A a b)
    (h₂ : PEqI E ρ A b c) : PEqI E ρ A a c := fun u => (h₁ u).trans (h₂ u)

/-- Untyped semantic equality is projected equality at every type. -/
theorem pEqI_of_semEqI {E : ResolvedEnv} {ρ : EnvI} {A a b : Expr Nat} (h : SemEqI ρ a b) :
    PEqI E ρ A a b :=
  fun u => ⟨fun hu => ⟨(h u).mp hu.1, hu.2⟩, fun hu => ⟨(h u).mpr hu.1, hu.2⟩⟩

/-- **The `irr` clause**: at a proposition type, all terms are projected-equal. -/
theorem pEqI_irr {E : ResolvedEnv} {ρ : EnvI} {P : Expr Nat} (hP : IsPropIdealI E (denI ρ P))
    (p q : Expr Nat) : PEqI E ρ P p q := fun u =>
  (tprojI_prop hP (denI_bot ρ P) (denI_bot ρ p) u).trans
    (tprojI_prop hP (denI_bot ρ P) (denI_bot ρ q) u).symm

/-- Semantic fitting of an environment to a context: each variable's compacts are typed at some
    code of its declared type. -/
def EnvFitsSem (E : ResolvedEnv) (ρ : EnvI) (Γ : LCtx) : Prop :=
  ∀ i A, lookupType Γ i = some A → ∀ u, ρ i u → ∃ a, denI ρ A a ∧ CTy E u a

/-- The semantic typing lemma at `Sort 0`, named: types typed at `Sort 0` denote proposition
    ideals at fitting environments. -/
def PropDen (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {P : Expr Nat}, HasTyT E n Γ P (.sort .zero) →
    ∀ ρ, EnvFitsSem E ρ Γ → IsPropIdealI E (denI ρ P)

/-- **Soundness of the native `ConvT.irr`** for the projected semantics, given `PropDen`. -/
theorem pEqI_convT_irr {E : ResolvedEnv} {n : Nat} (hD : PropDen E n) {Γ : LCtx}
    {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) (_hp : HasTyT E n Γ p P)
    (_hq : HasTyT E n Γ q P) (ρ : EnvI) (hρ : EnvFitsSem E ρ Γ) : PEqI E ρ P p q :=
  pEqI_irr (hD hP ρ hρ) p q

/-! ### impredicativity, and two teeth -/

/-- Impredicativity in the model: a Π whose codomain denotes proposition ideals at every finite
    demand is a proposition, whatever its domain. -/
theorem isPropIdealI_pi_of_cod (E : ResolvedEnv) {ρ : EnvI} {A B : Expr Nat}
    (hB : ∀ us, IsPropIdealI E (denI (EnvI.cons (demand us) ρ) B)) :
    IsPropIdealI E (denI ρ (.pi A B)) := by
  intro c hc
  rcases approxI_pi_inv hc with h0 | ⟨a, f, heq, _, hf⟩
  · subst h0; exact .bot
  · subst heq; exact .pi (fun t ht => hB t.1 t.2 (hf t ht))

/-- A sort is never a proposition ideal. -/
theorem not_isPropIdealI_sort (E : ResolvedEnv) (ρ : EnvI) (l : Level) :
    ¬ IsPropIdealI E (denI ρ (.sort l)) := by
  intro h
  have := h .sort (.sort ρ l)
  cases this

/-- A Π into a sort is never a proposition ideal. -/
theorem not_isPropIdealI_pi_sort (E : ResolvedEnv) (ρ : EnvI) (A : Expr Nat) (l : Level) :
    ¬ IsPropIdealI E (denI ρ (.pi A (.sort l))) := by
  intro h
  have := h (.pi .bot [([], .sort)])
    (.pi (.bot ρ A) (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs; exact .sort _ _))
  cases this with
  | pi hf =>
      have := hf ([], .sort) (List.mem_singleton.mpr rfl)
      cases this

/-! ### stability under substitution -/

/-- Semantic substitution at the outermost variable (fcd7's `approxI_subst_intro`/`_elim`). -/
theorem denI_instantiate0 (ρ : EnvI) (r e : Expr Nat) (c : CptI) :
    denI ρ (instantiate0 r e) c ↔ denI (EnvI.cons (denI ρ r) ρ) e c := by
  constructor
  · intro h
    have h₁ : ApproxI ρ (instantiate 0 (lift 0 0 r) e) c := by rw [lift_zero_idx]; exact h
    have h₂ := approxI_subst_elim e h₁
    rw [EnvI.insert_zero, EnvI.drop_zero] at h₂
    exact h₂
  · intro h
    have h' : ApproxI (EnvI.cons (denI ρ r) ρ) e c := h
    have h₂ := approxI_subst_intro h' ρ 0 r (by rw [EnvI.insert_zero, EnvI.drop_zero])
    rw [lift_zero_idx] at h₂
    exact h₂

/-- **Stability under substitution**: projected equality of instantiated terms at an instantiated
    type is projected equality at the extended environment. -/
theorem pEqI_subst (E : ResolvedEnv) (ρ : EnvI) (r B a b : Expr Nat) :
    PEqI E ρ (instantiate0 r B) (instantiate0 r a) (instantiate0 r b) ↔
      PEqI E (EnvI.cons (denI ρ r) ρ) B a b := by
  have key : ∀ t u, tprojI E (denI ρ (instantiate0 r B)) (denI ρ (instantiate0 r t)) u ↔
      tprojI E (denI (EnvI.cons (denI ρ r) ρ) B) (denI (EnvI.cons (denI ρ r) ρ) t) u := by
    intro t u
    constructor
    · rintro ⟨h, c, hc, hty⟩
      exact ⟨(denI_instantiate0 ρ r t u).mp h, c, (denI_instantiate0 ρ r B c).mp hc, hty⟩
    · rintro ⟨h, c, hc, hty⟩
      exact ⟨(denI_instantiate0 ρ r t u).mpr h, c, (denI_instantiate0 ρ r B c).mpr hc, hty⟩
  constructor
  · intro h u
    exact (key a u).symm.trans ((h u).trans (key b u))
  · intro h u
    exact (key a u).trans ((h u).trans (key b u).symm)

/-! ### stability under dependent application -/

/-- The dom condition (paper Fig. 4, `dom(f, a)`) on a function denotation `F` at a domain type
    ideal `T`: every step demands only compacts typed at a code of `T`. -/
def DomTyped (E : ResolvedEnv) (T F : CptI → Prop) : Prop :=
  ∀ g, F (.lam g) → ∀ s ∈ g, ∀ u ∈ s.1, ∃ a, T a ∧ CTy E u a

/-- No constant-headed spine elements (spine extension consumes argument codes untyped). -/
def NoSpine (F : CptI → Prop) : Prop := ∀ r args, ¬ F (.spine r args)

/-- **Stability under application at a proposition domain**: a dom-typed, spine-free function
    does not see which argument it is applied to — any two, in particular two proofs. -/
theorem semEqI_app_stable {E : ResolvedEnv} {ρ : EnvI} {A f : Expr Nat}
    (hA : IsPropIdealI E (denI ρ A)) (hdom : DomTyped E (denI ρ A) (denI ρ f))
    (hns : NoSpine (denI ρ f)) (a b : Expr Nat) : SemEqI ρ (.app f a) (.app f b) := by
  have dir : ∀ x y c, ApproxI ρ (.app f x) c → ApproxI ρ (.app f y) c := by
    intro x y c h
    cases h with
    | bot => exact .bot _ _
    | app hf hs _ =>
        refine .app hf hs (fun u hu => ?_)
        obtain ⟨a', ha', hc⟩ := hdom _ hf _ hs u hu
        have hu0 : u = .bot := cty_prop_bot (hA a' ha') hc
        subst hu0
        exact .bot _ _
    | appSpine hf _ => exact absurd hf (hns _ _)
  exact fun c => ⟨dir a b c, dir b a c⟩

/-- The projected form, at any result type. -/
theorem pEqI_app_stable {E : ResolvedEnv} {ρ : EnvI} {A f : Expr Nat} (T : Expr Nat)
    (hA : IsPropIdealI E (denI ρ A)) (hdom : DomTyped E (denI ρ A) (denI ρ f))
    (hns : NoSpine (denI ρ f)) (a b : Expr Nat) : PEqI E ρ T (.app f a) (.app f b) :=
  pEqI_of_semEqI (semEqI_app_stable hA hdom hns a b)

/-- (O2) fcd7's λ is untyped: the identity's step `[sort] ↦ sort` demands a non-`⊥` compact, so
    at a proposition domain the dom condition fails. -/
theorem lam_id_not_domTyped (E : ResolvedEnv) (ρ : EnvI) (A : Expr Nat)
    (hA : IsPropIdealI E (denI ρ A)) : ¬ DomTyped E (denI ρ A) (denI ρ (.lam A (.bvar 0))) := by
  intro h
  have hl : denI ρ (.lam A (.bvar 0)) (.lam [([.sort], .sort)]) :=
    .lam (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs
      exact .bvar (List.mem_singleton.mpr rfl))
  obtain ⟨a, ha, hc⟩ := h _ hl _ (List.mem_singleton.mpr rfl) _ (List.mem_singleton.mpr rfl)
  exact nomatch cty_prop_bot (hA a ha) hc

/-- Inversion of a constant applied to one argument. -/
theorem approxI_app_const_inv {ρ : EnvI} {r : Nat} {ls : List Level} {x : Expr Nat} {c : CptI}
    (h : ApproxI ρ (.app (.const r ls) x) c) :
    c = .bot ∨ ∃ u, c = .spine r [u] ∧ ApproxI ρ x u := by
  cases h with
  | bot => exact Or.inl rfl
  | app hf _ _ => cases hf
  | appSpine hf ha =>
      cases hf with
      | const => exact Or.inr ⟨_, rfl, ha⟩

/-- (O3) Spine extension consumes the argument's codes: a constant applied to `x` has the spine
    `[u]` exactly for the compacts `u` of `x`. -/
theorem approxI_app_const_spine (ρ : EnvI) (r : Nat) (ls : List Level) (x : Expr Nat) (u : CptI) :
    ApproxI ρ (.app (.const r ls) x) (.spine r [u]) ↔ ApproxI ρ x u := by
  constructor
  · intro h
    rcases approxI_app_const_inv h with h0 | ⟨u', heq, ha⟩
    · exact nomatch h0
    · cases heq; exact ha
  · intro h
    exact .appSpine (args := []) (.const ρ r ls) h

/-! ### K via irr + ι -/

/-- **K via irr + ι.**  For an eliminator `R` (the recursor applied to motive and minor), a proof
    `h` and the canonical proof `rfl'` of a proposition `P`: `irr` gives `h ≡ rfl'` at `P`;
    stability of `R` in its major turns that into `R h ≡ R rfl'`; ι gives `R rfl' ≡ m`.  The two
    model obligations are the hypotheses `hstab` (dom-typed recursor semantics, cf. O2/O3) and
    `hι` (ι-soundness at the canonical proof). -/
theorem pEqI_k_of_irr_iota {E : ResolvedEnv} {ρ : EnvI} {P T R h rfl' m : Expr Nat}
    (hP : IsPropIdealI E (denI ρ P))
    (hstab : ∀ x y, PEqI E ρ P x y → PEqI E ρ T (.app R x) (.app R y))
    (hι : PEqI E ρ T (.app R rfl') m) : PEqI E ρ T (.app R h) m :=
  (hstab h rfl' (pEqI_irr hP h rfl')).trans hι

/-- K with the stability obligation discharged by `pEqI_app_stable`: only ι remains. -/
theorem pEqI_k_of_iota {E : ResolvedEnv} {ρ : EnvI} {P T R h rfl' m : Expr Nat}
    (hP : IsPropIdealI E (denI ρ P)) (hdom : DomTyped E (denI ρ P) (denI ρ R))
    (hns : NoSpine (denI ρ R)) (hι : PEqI E ρ T (.app R rfl') m) :
    PEqI E ρ T (.app R h) m :=
  pEqI_k_of_irr_iota hP (fun x y _ => pEqI_app_stable T hP hdom hns x y) hι

/-! ### (O1) the collapsed universe: the admitted obstruction -/

/-- fcd7's model has one universe code: all sorts have the same denotation. -/
theorem approxI_sort_collapse (ρ : EnvI) (l₁ l₂ : Level) : SemEqI ρ (.sort l₁) (.sort l₂) := by
  intro c
  constructor <;> intro h <;> cases h
  · exact .bot _ _
  · exact .sort _ _
  · exact .bot _ _
  · exact .sort _ _

/-- The context `P : Sort 0, p : P, q : P` (innermost first). -/
def irrCtx : LCtx := [.assumption (.bvar 1), .assumption (.bvar 0), .assumption (.sort .zero)]

/-- The native `irr` instance at `irrCtx`: `p ≡ q : P`. -/
def irrCtx_conv (E : ResolvedEnv) (n : Nat) : ConvT E n irrCtx (.bvar 1) (.bvar 0) (.bvar 2) :=
  ConvT.irr irrCtx (.bvar 2) (.bvar 1) (.bvar 0) (HasTyT.bvar irrCtx 2 _ rfl)
    (HasTyT.bvar irrCtx 1 _ rfl) (HasTyT.bvar irrCtx 0 _ rfl)

/-- `P` is typed at `Sort 0` in `irrCtx`. -/
def irrCtx_prop (E : ResolvedEnv) (n : Nat) : HasTyT E n irrCtx (.bvar 2) (.sort .zero) :=
  HasTyT.bvar irrCtx 2 _ rfl

/-- The environment interpreting `P` by the code `c`, `p` by its inhabitant `w`, `q` by `⊥`. -/
def badEnv (c w : CptI) : EnvI := fun i u =>
  match i with
  | 0 => u = .bot
  | 1 => u = .bot ∨ u = w
  | 2 => u = .bot ∨ u = c
  | _ => u = .bot

theorem approxI_bvar_iff {ρ : EnvI} {i : Nat} {u : CptI} :
    ApproxI ρ (.bvar i) u ↔ u = .bot ∨ ρ i u := by
  constructor
  · intro h
    cases h with
    | bot => exact Or.inl rfl
    | bvar h => exact Or.inr h
  · rintro (rfl | h)
    · exact .bot _ _
    · exact .bvar h

/-- **(O1), general form.**  Let `Ty` be any typing of compacts in which `⊥` inhabits every code,
    the universe code types a code `c`, and `c` has an inhabitant `w ≠ ⊥` (e.g. `Nat : Sort 1`).
    Over fcd7's single universe code, the environment `P ↦ {⊥, c}, p ↦ {⊥, w}, q ↦ {⊥}` fits
    `irrCtx` semantically, and the `Ty`-projections of `p` and `q` at `P` differ — although
    `p ≡ q : P` is a native `ConvT.irr` (`irrCtx_conv`). -/
theorem irr_unsound_of_universe_code (Ty : CptI → CptI → Prop) (hbot : ∀ a, Ty .bot a)
    {c w : CptI} (hc : Ty c .sort) (hw : Ty w c) (hw0 : w ≠ .bot) :
    (∀ i A, lookupType irrCtx i = some A → ∀ u, badEnv c w i u →
        ∃ a, ApproxI (badEnv c w) A a ∧ Ty u a) ∧
      ¬ (∀ u, (ApproxI (badEnv c w) (.bvar 1) u ∧ ∃ a, ApproxI (badEnv c w) (.bvar 2) a ∧ Ty u a) ↔
          (ApproxI (badEnv c w) (.bvar 0) u ∧ ∃ a, ApproxI (badEnv c w) (.bvar 2) a ∧ Ty u a)) := by
  refine ⟨?_, ?_⟩
  · intro i A hA u hu
    match i, hA, hu with
    | 0, hA, hu =>
        simp [lookupType, irrCtx, lift] at hA
        subst hA
        have hu' : u = .bot := hu
        subst hu'
        exact ⟨.bot, .bot _ _, hbot _⟩
    | 1, hA, hu =>
        simp [lookupType, irrCtx, lift] at hA
        subst hA
        rcases (hu : u = .bot ∨ u = w) with rfl | rfl
        · exact ⟨.bot, .bot _ _, hbot _⟩
        · exact ⟨c, approxI_bvar_iff.mpr (Or.inr (Or.inr rfl)), hw⟩
    | 2, hA, hu =>
        simp [lookupType, irrCtx, lift] at hA
        subst hA
        rcases (hu : u = .bot ∨ u = c) with rfl | rfl
        · exact ⟨.bot, .bot _ _, hbot _⟩
        · exact ⟨.sort, .sort _ _, hc⟩
    | i + 3, hA, _ =>
        simp [lookupType, irrCtx] at hA
  · intro h
    have hl : ApproxI (badEnv c w) (.bvar 1) w ∧
        ∃ a, ApproxI (badEnv c w) (.bvar 2) a ∧ Ty w a :=
      ⟨approxI_bvar_iff.mpr (Or.inr (Or.inr rfl)), c,
        approxI_bvar_iff.mpr (Or.inr (Or.inr rfl)), hw⟩
    obtain ⟨hr, _⟩ := (h w).mp hl
    rcases approxI_bvar_iff.mp hr with h0 | h0
    · exact hw0 h0
    · exact hw0 h0

/-- The instance for `CTy` (`c = w = sort`, type-in-type): `irr` is unsound for the projected
    semantics at a semantically fitting environment. -/
theorem irr_unsound_collapsed (E : ResolvedEnv) :
    EnvFitsSem E (badEnv .sort .sort) irrCtx ∧
      ¬ PEqI E (badEnv .sort .sort) (.bvar 2) (.bvar 1) (.bvar 0) :=
  irr_unsound_of_universe_code (CTy E) (fun a => .bot a) (.univ .sort) (.univ .sort)
    (fun h => nomatch h)

/-- Hence the semantic typing lemma at `Sort 0` is FALSE over the collapsed universe. -/
theorem not_propDen_collapsed (E : ResolvedEnv) (n : Nat) : ¬ PropDen E n := by
  intro hD
  have hP := hD (irrCtx_prop E n) (badEnv .sort .sort) (irr_unsound_collapsed E).1
  exact (irr_unsound_collapsed E).2 (pEqI_irr hP _ _)


/-! ### what the logical relation needs from irr (`FundamentalLRI` is stated at `EnvI.bot`) -/

/-- At the degenerate environment every variable, in particular every proof variable, denotes
    `{⊥}`, a proposition ideal. -/
theorem isPropIdealI_bvar_bot (E : ResolvedEnv) (i : Nat) :
    IsPropIdealI E (denI EnvI.bot (.bvar i)) := by
  intro a ha
  rcases approxI_bvar_iff.mp ha with h0 | h0
  · subst h0; exact .bot
  · have h0' : a = .bot := h0
    subst h0'; exact .bot

/-- `irr` at the degenerate environment, at a proposition variable. -/
theorem pEqI_irr_bvar_bot (E : ResolvedEnv) (i : Nat) (p q : Expr Nat) :
    PEqI E EnvI.bot (.bvar i) p q :=
  pEqI_irr (isPropIdealI_bvar_bot E i) p q

/-- Under a binder the degenerate environment is extended by an ARBITRARY finite demand (fcd7's
    untyped Π steps), and the universe code is shared by `Sort 0` and `Sort 1`: so the
    impredicative proposition `Π Q : Sort 0, Q` is NOT a proposition ideal even at `⊥` — its
    step `[sort] ↦ sort` has a non-proposition output.  The irr case of `FundamentalLRI` can
    therefore not go through `PropDen` at `⊥` either; it needs the typed Π of Fig. 4 and a
    `Prop` code (O1 + O2 under binders). -/
theorem not_isPropIdealI_pi_propBinder_bot (E : ResolvedEnv) :
    ¬ IsPropIdealI E (denI EnvI.bot (.pi (.sort .zero) (.bvar 0))) := by
  intro h
  have hc : denI EnvI.bot (.pi (.sort .zero) (.bvar 0)) (.pi .bot [([.sort], .sort)]) :=
    .pi (.bot _ _) (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs
      exact .bvar (List.mem_singleton.mpr rfl))
  have := h _ hc
  cases this with
  | pi hf =>
      have := hf ([.sort], .sort) (List.mem_singleton.mpr rfl)
      cases this

#print axioms IsPropC
#print axioms TyCodeC
#print axioms CTy
#print axioms cty_prop_bot
#print axioms IsPropIdealI
#print axioms tprojI
#print axioms ProjI
#print axioms tyProjI
#print axioms denI_bot
#print axioms tprojI_bot
#print axioms tprojI_prop
#print axioms PEqI
#print axioms PEqI.refl
#print axioms PEqI.symm
#print axioms PEqI.trans
#print axioms pEqI_of_semEqI
#print axioms pEqI_irr
#print axioms EnvFitsSem
#print axioms PropDen
#print axioms pEqI_convT_irr
#print axioms isPropIdealI_pi_of_cod
#print axioms not_isPropIdealI_sort
#print axioms not_isPropIdealI_pi_sort
#print axioms denI_instantiate0
#print axioms pEqI_subst
#print axioms DomTyped
#print axioms NoSpine
#print axioms semEqI_app_stable
#print axioms pEqI_app_stable
#print axioms lam_id_not_domTyped
#print axioms approxI_app_const_inv
#print axioms approxI_app_const_spine
#print axioms pEqI_k_of_irr_iota
#print axioms pEqI_k_of_iota
#print axioms approxI_sort_collapse
#print axioms irrCtx
#print axioms irrCtx_conv
#print axioms irrCtx_prop
#print axioms badEnv
#print axioms approxI_bvar_iff
#print axioms irr_unsound_of_universe_code
#print axioms irr_unsound_collapsed
#print axioms not_propDen_collapsed
#print axioms isPropIdealI_bvar_bot
#print axioms pEqI_irr_bvar_bot
#print axioms not_isPropIdealI_pi_propBinder_bot

end Rcic.Declarative.NativeValleys.PiModelIrrAudit
