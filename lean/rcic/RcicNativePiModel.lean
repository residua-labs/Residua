import rcic.RcicNativeValleyDecoTransfer

/-!
# RcicNativePiModel — Π-injectivity by a domain model: the first compiled layer

ChatGPT #7608 (`admitted_no_raw_star_confluence`, `trueEnvU`) shows that even the full raw
relation with K and η-K is not star confluent: `True.rec M ≡ λm. λ_. m` is a conversion (the
nested η/λ peak) with no joining stars of any length, because the relation contracts η and
never expands it.  Confluence is therefore not the route to Π-injectivity of `TyConvT`.  The
alternative is semantic: Carneiro–Coquand–Frabetti Mathieu–Lennon-Bertrand–Melliès–Weirich,
*Definitional Inversion, Without Normalisation* (arXiv 2607.13662), prove injectivity and
no-confusion of type constructors by a Scott-domain model and a compact-indexed logical
relation, with η, type-in-type and general recursion, and no normalisation.

**The method, in their words and ours.**  A domain `D ≅ [D⇒D] + ↑(D × [D⇒D]) + ↑1`
(λ, Π, universe; coalesced sum so that `⊥ = λx.⊥`, which validates η) is approximated by
finite domains whose compact elements have an elementary inductive description.  Types are
interpreted as finitary projections of `D`, terms by elements; conversion is sound
(Theorem 2.31).  The model is deliberately coarse and NOT complete: semantic equality does
not reflect to conversion.  Injectivity is read back through a logical relation
`Γ ⊨ A ≡ A' type |_a`, indexed by a compact `a`, whose Π-clause says both sides
head-reduce, by object-theory conversions, to Π-types with convertible components; the
fundamental lemma gives `Γ ⊢ A ≡ A' : 𝒰 → Γ ⊨ A ≡ A' type |_a` for every compact
`a ≤ ⟦A⟧_⊥`, and `Π(⊥,⊥) ≤ ⟦Π A B⟧_⊥` closes (Corollary 2.37).  Neutrals are interpreted by
`⊥` (variables map to `⊥`), which is why open contexts need no Kripke quantification.

**Instantiation for RCIC — the layers.**
* L0 (this module, compiled): compact elements `Cpt` of the coarse domain with the
  constructors RCIC needs — `bot`, one collapsed `sort` (universe levels are irrelevant to
  Π-injectivity, and `sortEq`/`consts` become trivially sound), `pi`, `lam` (step
  functions), and constant-headed spines `spine r args` for inductive families,
  constructors, and opaque constants.  (The information order with `lam [] ≤ bot` and
  downward closure of `Approx` are L2's monotonicity lemma; this layer uses singleton
  ideals.)
* L1 (this module, compiled): the approximation relation `Approx ρ e c` ("`c` approximates
  `⟦e⟧_ρ`") for the untyped syntax — variables through the environment of ideals, `pi`/`lam`
  by step functions, `app` by application of step functions and by spine extension, `letE`
  as the β-redex, `lit` by `natExpand`; its inversion lemmas; semantic equality `SemEq`;
  and the two model-level inversion facts: `semEq_pi_inj` (Π is injective in the model, on
  domains and on codomains at every compact argument) and `semEq_pi_sort_disjoint`.
* L1′ (this module, compiled): soundness of the congruence/index fragment of `ConvT`
  (`refl`, `symm`, `trans`, `pi`, `lam`, `app`, `tyConv`, `sorts`, `consts`) for `SemEq`
  at every environment — `CongrFrag`, `semEq_of_congrFrag`.
* L2 (named): soundness of the computational constructors.  `beta`, `zeta`, `zetaLocal`,
  `lit` need the substitution lemma `ApproxSubst` (`Approx ρ (instantiate0 a b) c ↔
  Approx (Env.cons ⟦a⟧_ρ ρ) b c`, with the de Bruijn lifting lemmas); `eta` needs
  extensionality of step functions under the information order; `delta` and `iota` need
  the environment
  of definitions and the recursors' semantic functions (ι by cases on constructor-headed
  compacts; K on a `Prop` family is the recursor returning its minor on the one-point
  interpretation — the same reason the η-K certificate needed no uniqueness).
* L3 (named): typed semantics.  `irr` is NOT sound for the untyped `Approx` (two proofs of a
  `Prop` have different untyped denotations, and proofs occur inside types); the paper's
  §3.6 handles strict propositions by finitary projections, where every proposition's
  projection is one-point.  RCIC's impredicative `Prop` with K and η-K sits exactly there:
  `SemTyping` (finitary projectors for `pi`, `sort`, families; the one-point projector for
  propositions) and `TypedSoundness` (`ConvT Γ a b A → p_⟦A⟧ ⟦a⟧ = p_⟦A⟧ ⟦b⟧`).
* L4 (named): the compact-indexed logical relation over RCIC's typed head reduction
  (`ParRedT`'s weak-head fragment is a sub-relation of `ConvT`), its Π-clause, and the
  fundamental lemma `FundamentalPi`; then `piInj_of_fundamentalPi` reads off `PiInj`.

The exact remaining statements are L2–L4; nothing in this module depends on confluence.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelAudit

/-! ### L0: compact elements of the coarse domain -/

/-- Compact elements: `bot`, the collapsed universe, Π with a compact domain and a step
    function codomain, λ as a step function, and constant-headed spines. -/
inductive Cpt : Type
  | bot : Cpt
  | sort : Cpt
  | pi : Cpt → List (Cpt × Cpt) → Cpt
  | lam : List (Cpt × Cpt) → Cpt
  | spine : Nat → List Cpt → Cpt

/-- The principal "ideal" of a compact, in this first layer the singleton (downward closure
    under the information order is L2's monotonicity lemma). -/
def Cpt.down (u : Cpt) : Cpt → Prop := fun c => c = u

/-! ### L1: the approximation relation -/

/-- Environments: an ideal (set of compacts) per variable. -/
def Env : Type := Nat → Cpt → Prop

/-- Extend an environment. -/
def Env.cons (S : Cpt → Prop) (ρ : Env) : Env
  | 0 => S
  | i + 1 => ρ i

/-- The environment interpreting every variable by `⊥` (neutrals are degenerate). -/
def Env.bot : Env := fun _ c => c = .bot

/-- `Approx ρ e c`: the compact `c` approximates the denotation of `e` in `ρ`. -/
inductive Approx : Env → Expr Nat → Cpt → Prop
  | bot (ρ : Env) (e : Expr Nat) : Approx ρ e .bot
  | lamNil (ρ : Env) (e : Expr Nat) : Approx ρ e (.lam [])
  | bvar {ρ : Env} {i : Nat} {c : Cpt} (h : ρ i c) : Approx ρ (.bvar i) c
  | sort (ρ : Env) (l : Level) : Approx ρ (.sort l) .sort
  | pi {ρ : Env} {A B : Expr Nat} {a : Cpt} {f : List (Cpt × Cpt)} (hA : Approx ρ A a)
      (hB : ∀ p ∈ f, Approx (Env.cons (Cpt.down p.1) ρ) B p.2) : Approx ρ (.pi A B) (.pi a f)
  | lam {ρ : Env} {A b : Expr Nat} {f : List (Cpt × Cpt)}
      (hb : ∀ p ∈ f, Approx (Env.cons (Cpt.down p.1) ρ) b p.2) : Approx ρ (.lam A b) (.lam f)
  | app {ρ : Env} {f a : Expr Nat} {g : List (Cpt × Cpt)} {p : Cpt × Cpt}
      (hf : Approx ρ f (.lam g)) (hp : p ∈ g) (ha : Approx ρ a p.1) :
      Approx ρ (.app f a) p.2
  | const (ρ : Env) (r : Nat) (ls : List Level) : Approx ρ (.const r ls) (.spine r [])
  | appSpine {ρ : Env} {f a : Expr Nat} {r : Nat} {args : List Cpt} {u : Cpt}
      (hf : Approx ρ f (.spine r args)) (ha : Approx ρ a u) :
      Approx ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : Env} {A v b : Expr Nat} {c : Cpt} (h : Approx ρ (.app (.lam A b) v) c) :
      Approx ρ (.letE A v b) c
  | lit {ρ : Env} {t : Nat} {c : Cpt} (h : Approx ρ (natExpand t) c) : Approx ρ (.lit t) c

/-- Semantic equality at an environment. -/
def SemEq (ρ : Env) (a b : Expr Nat) : Prop := ∀ c, Approx ρ a c ↔ Approx ρ b c

theorem SemEq.refl (ρ : Env) (a : Expr Nat) : SemEq ρ a a := fun _ => Iff.rfl
theorem SemEq.symm {ρ : Env} {a b : Expr Nat} (h : SemEq ρ a b) : SemEq ρ b a :=
  fun c => (h c).symm
theorem SemEq.trans {ρ : Env} {a b c : Expr Nat} (h₁ : SemEq ρ a b) (h₂ : SemEq ρ b c) :
    SemEq ρ a c := fun d => (h₁ d).trans (h₂ d)

/-- Inversion at a Π. -/
theorem approx_pi_inv {ρ : Env} {A B : Expr Nat} {c : Cpt} (h : Approx ρ (.pi A B) c) :
    c = .bot ∨ c = .lam [] ∨
      ∃ a f, c = .pi a f ∧ Approx ρ A a ∧ ∀ p ∈ f, Approx (Env.cons (Cpt.down p.1) ρ) B p.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | lamNil => exact Or.inr (Or.inl rfl)
  | pi hA hB => exact Or.inr (Or.inr ⟨_, _, rfl, hA, hB⟩)

/-- Inversion at a sort. -/
theorem approx_sort_inv {ρ : Env} {l : Level} {c : Cpt} (h : Approx ρ (.sort l) c) :
    c = .bot ∨ c = .lam [] ∨ c = .sort := by
  cases h with
  | bot => exact Or.inl rfl
  | lamNil => exact Or.inr (Or.inl rfl)
  | sort => exact Or.inr (Or.inr rfl)

/-- Inversion at a λ. -/
theorem approx_lam_inv {ρ : Env} {A b : Expr Nat} {c : Cpt} (h : Approx ρ (.lam A b) c) :
    c = .bot ∨ ∃ f, c = .lam f ∧ ∀ p ∈ f, Approx (Env.cons (Cpt.down p.1) ρ) b p.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | lamNil => exact Or.inr ⟨[], rfl, fun _ h => nomatch h⟩
  | lam hb => exact Or.inr ⟨_, rfl, hb⟩

/-- Inversion at an application. -/
theorem approx_app_inv {ρ : Env} {f a : Expr Nat} {c : Cpt} (h : Approx ρ (.app f a) c) :
    c = .bot ∨ c = .lam [] ∨
      (∃ g p, c = p.2 ∧ Approx ρ f (.lam g) ∧ p ∈ g ∧ Approx ρ a p.1) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ Approx ρ f (.spine r args) ∧ Approx ρ a u) := by
  cases h with
  | bot => exact Or.inl rfl
  | lamNil => exact Or.inr (Or.inl rfl)
  | app hf hp ha => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, hf, hp, ha⟩))
  | appSpine hf ha => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, hf, ha⟩))

/-- Π is injective in the model: on domains, and on codomains at every compact argument. -/
theorem semEq_pi_inj {ρ : Env} {A B A' B' : Expr Nat} (h : SemEq ρ (.pi A B) (.pi A' B')) :
    SemEq ρ A A' ∧ ∀ u, SemEq (Env.cons (Cpt.down u) ρ) B B' := by
  refine ⟨fun a => ⟨fun hA => ?_, fun hA' => ?_⟩, fun u v => ⟨fun hB => ?_, fun hB' => ?_⟩⟩
  · have := (h (.pi a [])).mp (.pi hA (fun _ hp => nomatch hp))
    rcases approx_pi_inv this with h0 | h0 | ⟨a', f', heq, hA', _⟩
    · exact nomatch h0
    · exact nomatch h0
    · cases heq; exact hA'
  · have := (h (.pi a [])).mpr (.pi hA' (fun _ hp => nomatch hp))
    rcases approx_pi_inv this with h0 | h0 | ⟨a', f', heq, hA, _⟩
    · exact nomatch h0
    · exact nomatch h0
    · cases heq; exact hA
  · have := (h (.pi .bot [(u, v)])).mp
      (.pi (.bot ρ A) (fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp; exact hB))
    rcases approx_pi_inv this with h0 | h0 | ⟨a', f', heq, _, hB'⟩
    · exact nomatch h0
    · exact nomatch h0
    · cases heq; exact hB' (u, v) (List.mem_singleton.mpr rfl)
  · have := (h (.pi .bot [(u, v)])).mpr
      (.pi (.bot ρ A') (fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp; exact hB'))
    rcases approx_pi_inv this with h0 | h0 | ⟨a', f', heq, _, hB⟩
    · exact nomatch h0
    · exact nomatch h0
    · cases heq; exact hB (u, v) (List.mem_singleton.mpr rfl)

/-- Π and sorts are disjoint in the model. -/
theorem semEq_pi_sort_disjoint {ρ : Env} {A B : Expr Nat} {l : Level}
    (h : SemEq ρ (.pi A B) (.sort l)) : False := by
  have := (h (.pi .bot [])).mp (.pi (.bot ρ A) (fun _ hp => nomatch hp))
  rcases approx_sort_inv this with h0 | h0 | h0 <;> exact nomatch h0

/-- Π and constant-headed spines are disjoint in the model. -/
theorem semEq_pi_const_disjoint {ρ : Env} {A B : Expr Nat} {r : Nat} {ls : List Level}
    (h : SemEq ρ (.pi A B) (.const r ls)) : False := by
  have := (h (.pi .bot [])).mp (.pi (.bot ρ A) (fun _ hp => nomatch hp))
  cases this

/-! ### L1′: soundness of the congruence/index fragment -/

/-- The congruence/index fragment of native conversion: no computation, no irrelevance. -/
inductive CongrFrag (E : ResolvedEnv) (n : Nat) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Prop
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A} :
      CongrFrag E n (@ConvT.refl E n Γ a A h)
  | symm {Γ : LCtx} {a b A : Expr Nat} {h : ConvT E n Γ a b A} (hh : CongrFrag E n h) :
      CongrFrag E n (ConvT.symm Γ a b A h)
  | trans {Γ : LCtx} {a b c A : Expr Nat} {h₁ : ConvT E n Γ a b A} {h₂ : ConvT E n Γ b c A}
      (hh₁ : CongrFrag E n h₁) (hh₂ : CongrFrag E n h₂) : CongrFrag E n (ConvT.trans Γ a b c A h₁ h₂)
  | pi {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level} {h₁ : ConvT E n Γ A A' (.sort u)}
      {h₂ : ConvT E n (.assumption A :: Γ) B B' (.sort v)}
      (hh₁ : CongrFrag E n h₁) (hh₂ : CongrFrag E n h₂) : CongrFrag E n (ConvT.pi Γ A A' B B' u v h₁ h₂)
  | lam {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level} {h₁ : ConvT E n Γ A A' (.sort u)}
      {h₂ : ConvT E n (.assumption A :: Γ) b b' B}
      (hh₁ : CongrFrag E n h₁) (hh₂ : CongrFrag E n h₂) : CongrFrag E n (ConvT.lam Γ A A' b b' B u h₁ h₂)
  | app {Γ : LCtx} {f g a b A B : Expr Nat} {h₁ : ConvT E n Γ f g (.pi A B)}
      {h₂ : ConvT E n Γ a b A} (hh₁ : CongrFrag E n h₁) (hh₂ : CongrFrag E n h₂) :
      CongrFrag E n (ConvT.app Γ f g a b A B h₁ h₂)
  | tyConv {Γ : LCtx} {a b A A' : Expr Nat} {u : Level} {h : ConvT E n Γ a b A}
      {hA : ConvT E n Γ A A' (.sort u)} (hh : CongrFrag E n h) :
      CongrFrag E n (ConvT.tyConv Γ a b A A' u h hA)
  | sorts {Γ : LCtx} {u v : Level} {h : eqN u v} : CongrFrag E n (ConvT.sorts Γ u v h)
  | consts {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
      {hres : E.members r = some m} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true} {hwf' : levelsBounded n ls' = true}
      {h : eqNList ls ls'} :
      CongrFrag E n (ConvT.consts Γ r ls ls' m hres hlen hwf hwf' h)

/-- Semantic equality is a congruence for Π. -/
theorem semEq_pi {ρ : Env} {A A' B B' : Expr Nat} (hA : SemEq ρ A A')
    (hB : ∀ S, SemEq (Env.cons S ρ) B B') : SemEq ρ (.pi A B) (.pi A' B') := by
  intro c
  constructor
  · intro h
    rcases approx_pi_inv h with h0 | h0 | ⟨a, f, heq, ha, hf⟩
    · subst h0; exact .bot _ _
    · subst h0; exact .lamNil _ _
    · subst heq; exact .pi ((hA a).mp ha) (fun p hp => (hB _ p.2).mp (hf p hp))
  · intro h
    rcases approx_pi_inv h with h0 | h0 | ⟨a, f, heq, ha, hf⟩
    · subst h0; exact .bot _ _
    · subst h0; exact .lamNil _ _
    · subst heq; exact .pi ((hA a).mpr ha) (fun p hp => (hB _ p.2).mpr (hf p hp))

/-- Semantic equality is a congruence for λ (the annotation is semantically inert). -/
theorem semEq_lam {ρ : Env} {A A' b b' : Expr Nat}
    (hb : ∀ S, SemEq (Env.cons S ρ) b b') : SemEq ρ (.lam A b) (.lam A' b') := by
  intro c
  constructor
  · intro h
    rcases approx_lam_inv h with h0 | ⟨f, heq, hf⟩
    · subst h0; exact .bot _ _
    · subst heq; exact .lam (fun p hp => (hb _ p.2).mp (hf p hp))
  · intro h
    rcases approx_lam_inv h with h0 | ⟨f, heq, hf⟩
    · subst h0; exact .bot _ _
    · subst heq; exact .lam (fun p hp => (hb _ p.2).mpr (hf p hp))

/-- Semantic equality is a congruence for application. -/
theorem semEq_app {ρ : Env} {f g a b : Expr Nat} (hf : SemEq ρ f g) (ha : SemEq ρ a b) :
    SemEq ρ (.app f a) (.app g b) := by
  intro c
  constructor
  · intro h
    rcases approx_app_inv h with h0 | h0 | ⟨s, p, heq, hs, hp, hap⟩ | ⟨r, args, u, heq, hs, hau⟩
    · subst h0; exact .bot _ _
    · subst h0; exact .lamNil _ _
    · subst heq; exact .app ((hf _).mp hs) hp ((ha _).mp hap)
    · subst heq; exact .appSpine ((hf _).mp hs) ((ha _).mp hau)
  · intro h
    rcases approx_app_inv h with h0 | h0 | ⟨s, p, heq, hs, hp, hap⟩ | ⟨r, args, u, heq, hs, hau⟩
    · subst h0; exact .bot _ _
    · subst h0; exact .lamNil _ _
    · subst heq; exact .app ((hf _).mpr hs) hp ((ha _).mpr hap)
    · subst heq; exact .appSpine ((hf _).mpr hs) ((ha _).mpr hau)

/-- Sorts are semantically equal (the model collapses universes). -/
theorem semEq_sorts (ρ : Env) (u v : Level) : SemEq ρ (.sort u) (.sort v) := by
  intro c
  constructor <;> intro h <;> rcases approx_sort_inv h with h0 | h0 | h0 <;> subst h0
  · exact .bot _ _
  · exact .lamNil _ _
  · exact .sort _ _
  · exact .bot _ _
  · exact .lamNil _ _
  · exact .sort _ _

/-- Constants are semantically equal across level instantiations. -/
theorem semEq_consts (ρ : Env) (r : Nat) (ls ls' : List Level) :
    SemEq ρ (.const r ls) (.const r ls') := by
  intro c
  constructor <;> intro h <;> cases h
  · exact .bot _ _
  · exact .lamNil _ _
  · exact .const _ _ _
  · exact .bot _ _
  · exact .lamNil _ _
  · exact .const _ _ _

/-- Soundness of the congruence/index fragment at every environment. -/
theorem semEq_of_congrFrag {E : ResolvedEnv} {n : Nat} : {Γ : LCtx} → {a b T : Expr Nat} →
    {h : ConvT E n Γ a b T} → CongrFrag E n h → ∀ ρ : Env, SemEq ρ a b
  | _, _, _, _, _, .refl, ρ => SemEq.refl ρ _
  | _, _, _, _, _, .symm hh, ρ => (semEq_of_congrFrag hh ρ).symm
  | _, _, _, _, _, .trans hh₁ hh₂, ρ => (semEq_of_congrFrag hh₁ ρ).trans (semEq_of_congrFrag hh₂ ρ)
  | _, _, _, _, _, .pi hh₁ hh₂, ρ =>
      semEq_pi (semEq_of_congrFrag hh₁ ρ) (fun S => semEq_of_congrFrag hh₂ (Env.cons S ρ))
  | _, _, _, _, _, .lam _ hh₂, ρ => semEq_lam (fun S => semEq_of_congrFrag hh₂ (Env.cons S ρ))
  | _, _, _, _, _, .app hh₁ hh₂, ρ => semEq_app (semEq_of_congrFrag hh₁ ρ) (semEq_of_congrFrag hh₂ ρ)
  | _, _, _, _, _, .tyConv hh, ρ => semEq_of_congrFrag hh ρ
  | _, _, _, _, _, .sorts, ρ => semEq_sorts ρ _ _
  | _, _, _, _, _, .consts, ρ => semEq_consts ρ _ _ _

/-- Π-injectivity of the congruence fragment, read in the model: for a conversion in the
    fragment between two Π-types, the domains and codomains are semantically equal.  (The
    object-level conversions are read back only through the logical relation, L4.) -/
theorem congrFrag_pi_semInj {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A₁ B₁ A₂ B₂ T : Expr Nat}
    {h : ConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T} (hh : CongrFrag E n h) (ρ : Env) :
    SemEq ρ A₁ A₂ ∧ ∀ u, SemEq (Env.cons (Cpt.down u) ρ) B₁ B₂ :=
  semEq_pi_inj (semEq_of_congrFrag hh ρ)

/-! ### the named layers -/

/-- L2: the substitution lemma for the approximation relation. -/
def ApproxSubst : Prop :=
  ∀ (ρ : Env) (a b : Expr Nat) (c : Cpt),
    Approx ρ (instantiate0 a b) c ↔ Approx (Env.cons (fun u => Approx ρ a u) ρ) b c

/-- L3: typed soundness of the full native conversion at the degenerate environment, for
    TYPES — the statement the Π-injectivity argument consumes (Theorem 2.31 at `⊥`).  Not
    provable for the untyped `Approx` as it stands (`irr` inside types); it is the
    finitary-projection layer's theorem. -/
def TypedSoundnessAtBot (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {A B : Expr Nat} {u : Level}, CtxWfT E n Γ → ConvT E n Γ A B (.sort u) →
    SemEq Env.bot A B

/-- L4: the Π-clause of the compact-indexed logical relation at `Π(⊥,[])`, as the fundamental
    lemma delivers it for two convertible Π-types: both sides are syntactic Π-types already,
    so the clause is the pair of component conversions. -/
def FundamentalPi (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat},
    TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) →
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂

/-- The read-off: the fundamental lemma's Π-clause IS Π-injectivity. -/
def piInj_of_fundamentalPi {E : ResolvedEnv} {n : Nat} (F : FundamentalPi E n) : PiInj E n := F

#print axioms Cpt
#print axioms Cpt.down
#print axioms Env
#print axioms Env.cons
#print axioms Env.bot
#print axioms Approx
#print axioms SemEq
#print axioms SemEq.refl
#print axioms SemEq.symm
#print axioms SemEq.trans
#print axioms approx_pi_inv
#print axioms approx_sort_inv
#print axioms approx_lam_inv
#print axioms approx_app_inv
#print axioms semEq_pi_inj
#print axioms semEq_pi_sort_disjoint
#print axioms semEq_pi_const_disjoint
#print axioms CongrFrag
#print axioms semEq_pi
#print axioms semEq_lam
#print axioms semEq_app
#print axioms semEq_sorts
#print axioms semEq_consts
#print axioms semEq_of_congrFrag
#print axioms congrFrag_pi_semInj
#print axioms ApproxSubst
#print axioms TypedSoundnessAtBot
#print axioms FundamentalPi
#print axioms piInj_of_fundamentalPi

end Rcic.Declarative.NativeValleys.PiModelAudit
