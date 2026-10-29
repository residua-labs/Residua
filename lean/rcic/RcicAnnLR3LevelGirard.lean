import rcic.RcicAnnLR3CandidateReflection

/-!
# A hereditary level model (level-Girard codes)

A model for the typing half that tracks levels and type-ness, not content.
Codes are data in `Type 0` (`LCode : Nat → Type`):

- level zero: Prop-level type variables `var0`, opaque propositions `prop img`
  given by a well-formed raw image function (`PropImg`: jointly continuous
  in the environment, a defined level-zero sort member),
  and products into `Prop` (`pi0`);
- above level zero: type variables `var`, universes `univ`, named neutral
  types `neutral`, and products `pi c A B` at level `c + 1`.

The reading `ElA adm` is chaotic (bottom-carrying values) on every level-zero
code and every named neutral type. A universe relates the images of closed,
kinded *twin* codes (codes equal up to their level-zero parts, `Twin`). A
positive type variable reads its candidate, and a positive product is
hereditary over every admissible candidate for its bound variable.

Proved: images are monotone and finitely demanding (`image_mono`,
`image_finite`, `codomain_finite`); image-equal kinded codes are twins
(`imageEq_twin`); twins have the same reading (`el_twin`); the reading is a
PER in saturated environments (`el_laws`), bot-closed (`el_saturated`) and
independent of the raw environment (`el_raw`). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelGirard

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (withBot Head11Free)
open CandidateTowerProbe (REnv CEnv rcons ccons Sat Adm AdmLaws SatFor satFor_laws Ntr SatEnv
  satEnv_rcons)
open CandidateTowerCoherence (upd EnvLe envLe_rcons rcons_upd BotEnv botEnv_rcons constEnv
  applyValue_legalGraph_at pi_vs_tagged)

/-- Joint continuity: each output observation is determined by finitely many
(slot, observation) pairs of the environment. -/
def JointCont (F : REnv → Value) : Prop :=
  ∀ σ d, F σ d → ∃ S : List (Nat × CptI), (∀ p ∈ S, σ p.1 p.2) ∧
    ∀ σ' : REnv, (∀ p ∈ S, σ' p.1 p.2) → F σ' d

/-- Well-formedness of an opaque level-zero type, given by its raw image
function: jointly continuous in the environment, and a defined,
bottom-carrying level-zero sort member at every environment. -/
structure PropImg (img : REnv → Value) : Prop where
  cont : JointCont img
  level : ∀ σ, SortMember (some 0) (img σ)
  defined : ∀ σ, TypeDefined (img σ)
  bot : ∀ σ, img σ .bot

theorem JointCont.mono {F : REnv → Value} (h : JointCont F) (σ σ' : REnv) (hle : EnvLe σ σ')
    (d : CptI) (hd : F σ d) : F σ' d := by
  obtain ⟨S, hS, hF⟩ := h σ d hd
  exact hF σ' (fun p hp => hle _ _ (hS p hp))

/-- The observations a list demands at one slot. -/
def slotObs (S : List (Nat × CptI)) (j : Nat) : List CptI :=
  S.filterMap (fun p => if p.1 = j then some p.2 else none)

theorem mem_slotObs {S : List (Nat × CptI)} {j : Nat} {u : CptI} :
    u ∈ slotObs S j ↔ (j, u) ∈ S := by
  unfold slotObs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, he⟩
    by_cases h : p.1 = j
    · rw [if_pos h] at he
      injection he with he
      subst he
      have : p = (j, p.2) := by
        cases p
        simp only at h
        subst h
        rfl
      rw [← this]
      exact hp
    · rw [if_neg h] at he
      exact Option.noConfusion he
  · intro h
    exact ⟨(j, u), h, by simp⟩

theorem JointCont.finite {F : REnv → Value} (h : JointCont F) (σ : REnv) (j : Nat) (x : Value)
    (d : CptI) (hd : F (upd σ j x) d) :
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → F (upd σ j x') d := by
  obtain ⟨S, hS, hF⟩ := h _ d hd
  refine ⟨slotObs S j, fun u hu => ?_, fun x' hx' => hF _ (fun p hp => ?_)⟩
  · have := hS _ (mem_slotObs.mp hu)
    simpa [upd] using this
  · by_cases hpj : p.1 = j
    · have hp' : (j, p.2) ∈ S := by
        have : p = (j, p.2) := by
          cases p
          simp only at hpj
          subst hpj
          rfl
        rw [← this]
        exact hp
      show (if p.1 = j then x' else σ p.1) p.2
      rw [if_pos hpj]
      exact hx' _ (mem_slotObs.mpr hp')
    · have := hS p hp
      show (if p.1 = j then x' else σ p.1) p.2
      rw [if_neg hpj]
      simpa [upd, hpj] using this

/-- Codes of the level model. Level-zero codes are type variables of `Prop`,
opaque propositions given by their image, and products into `Prop`. Above
level zero: type variables, universes, named neutral types and products. -/
inductive LCode : Nat → Type
  | var0 (i : Nat) : LCode 0
  | prop (img : REnv → Value) : LCode 0
  | pi0 {a : Nat} (A : LCode a) (B : LCode 0) : LCode 0
  | var (k i : Nat) : LCode (k + 1)
  | univ (k : Nat) : LCode (k + 1)
  | neutral (k name : Nat) : LCode (k + 1)
  | pi (c : Nat) {a b : Nat} (A : LCode a) (B : LCode (b + 1)) : LCode (c + 1)

def image : {k : Nat} → REnv → LCode k → Value
  | _, σ, .var0 i => withBot (σ i)
  | _, σ, .prop img => img σ
  | _, σ, .pi0 A B => InductiveCodes.piValue (some 0) (image σ A)
      (UnifiedPi.legalGraph (fun _ _ => True) (fun x => image (rcons x σ) B))
  | _, σ, .var _ i => withBot (σ i)
  | _, _, .univ k => universeValue (some k)
  | _, _, .neutral k name => NativeMemberValues.value (some (k + 1)) name
  | _, σ, .pi c A B => InductiveCodes.piValue (some (c + 1)) (image σ A)
      (UnifiedPi.legalGraph (fun _ _ => True) (fun x => image (rcons x σ) B))

/-- The kind a product binder gives its variable: the level of a universe
domain, or none. -/
def kindOf : {k : Nat} → LCode k → Option Nat
  | _, .univ j => some j
  | _, _ => none

def Kinded : {k : Nat} → List (Option Nat) → LCode k → Prop
  | _, κ, .var0 i => κ[i]? = some (some 0)
  | _, _, .prop img => PropImg img
  | _, κ, .pi0 A B => Kinded κ A ∧ Kinded (kindOf A :: κ) B
  | _, κ, .var k i => κ[i]? = some (some (k + 1))
  | _, _, .univ _ => True
  | _, _, .neutral _ name => name ≠ 11
  | _, κ, .pi _ A B => Kinded κ A ∧ Kinded (kindOf A :: κ) B

/-- Scope: the image depends only on the first `n` environment entries. -/
def ClosedAt : {k : Nat} → Nat → LCode k → Prop
  | _, n, .var0 i => i < n
  | _, n, .prop img => ∀ σ σ', (∀ i, i < n → σ i = σ' i) → img σ = img σ'
  | _, n, .pi0 A B => ClosedAt n A ∧ ClosedAt (n + 1) B
  | _, n, .var _ i => i < n
  | _, _, .univ _ => True
  | _, _, .neutral _ _ => True
  | _, n, .pi _ A B => ClosedAt n A ∧ ClosedAt (n + 1) B

/-! ## Environment dependence of images -/

theorem image_mono : {k : Nat} → (c : LCode k) → ∀ {σ σ' : REnv}, ∀ (κ : List (Option Nat)),
    Kinded κ c → EnvLe σ σ' → ∀ d, image σ c d → image σ' c d
  | _, .var0 i, _, _, _, _, h, d, hd => hd.imp_right (h i d)
  | _, .prop _, σ, σ', _, hk, h, d, hd => hk.cont.mono σ σ' h d hd
  | _, .pi0 A B, σ, σ', κ, hk, h, d, hd => by
      rcases hd with hd | ⟨a, p, he, ha, hp | ⟨a', g, hpe, hA, hrows⟩⟩
      · exact Or.inl hd
      · exact Or.inr ⟨a, p, he, ha, Or.inl hp⟩
      · refine Or.inr ⟨a, p, he, ha, Or.inr ⟨a', g, hpe, image_mono A κ hk.1 h a' hA, ?_⟩⟩
        intro s hs
        rcases hrows s hs with hc | ⟨g', s', hc, hG, hs', hv⟩ | ⟨head, args, u, hc, hG, hv⟩
        · exact Or.inl hc
        · refine Or.inr (Or.inl ⟨g', s', hc, ?_, hs', hv⟩)
          rcases hG with hG | ⟨table, he', rows⟩
          · exact Or.inl hG
          · refine Or.inr ⟨table, he', fun t ht y hy hty => ?_⟩
            exact image_mono B _ hk.2 (envLe_rcons h (fun _ c => c)) t.2 (rows t ht y hy hty)
        · rcases hG with hG | ⟨table, he', _⟩
          · cases hG
          · cases he'
  | _, .var _ i, _, _, _, _, h, d, hd => hd.imp_right (h i d)
  | _, .univ _, _, _, _, _, _, _, hd => hd
  | _, .neutral _ _, _, _, _, _, _, _, hd => hd
  | _, .pi _ A B, σ, σ', κ, hk, h, d, hd => by
      rcases hd with hd | ⟨a, p, he, ha, hp | ⟨a', g, hpe, hA, hrows⟩⟩
      · exact Or.inl hd
      · exact Or.inr ⟨a, p, he, ha, Or.inl hp⟩
      · refine Or.inr ⟨a, p, he, ha, Or.inr ⟨a', g, hpe, image_mono A κ hk.1 h a' hA, ?_⟩⟩
        intro s hs
        rcases hrows s hs with hc | ⟨g', s', hc, hG, hs', hv⟩ | ⟨head, args, u, hc, hG, hv⟩
        · exact Or.inl hc
        · refine Or.inr (Or.inl ⟨g', s', hc, ?_, hs', hv⟩)
          rcases hG with hG | ⟨table, he', rows⟩
          · exact Or.inl hG
          · refine Or.inr ⟨table, he', fun t ht y hy hty => ?_⟩
            exact image_mono B _ hk.2 (envLe_rcons h (fun _ c => c)) t.2 (rows t ht y hy hty)
        · rcases hG with hG | ⟨table, he', _⟩
          · cases hG
          · cases he'

/-! ## Finite demand in every environment slot -/

/-- One application row of a product image is finitely determined in a slot,
for any monotone codomain image that is finitely determined in every slot. -/
theorem row_finite (F : REnv → Value)
    (hmono : ∀ σ σ', EnvLe σ σ' → ∀ d, F σ d → F σ' d)
    (ihF : ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), F (upd σ j x) d →
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → F (upd σ j x') d)
    (σ : REnv) (j : Nat) (x v : Value) (c : CptI)
    (h : NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
      (fun y => F (rcons y (upd σ j x)))) v c) :
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) →
      NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
        (fun y => F (rcons y (upd σ j x')))) v c := by
  rcases h with hc | ⟨g', s', hc, hG, hs', hv⟩ | ⟨head, args, u, hc, hG, hv⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hc⟩
  · rcases hG with hG | ⟨table, he, rows⟩
    · cases hG
    · cases he
      have hmin : F (rcons (demand s'.1) (upd σ j x)) s'.2 :=
        rows s' hs' (demand s'.1) True.intro (fun u hu => hu)
      rw [rcons_upd] at hmin
      obtain ⟨us, hus, hfin⟩ := ihF _ _ x _ hmin
      refine ⟨us, hus, fun x' hx' => Or.inr (Or.inl ⟨[s'], s', hc, ?_, by simp, hv⟩)⟩
      refine Or.inr ⟨[s'], rfl, fun t ht y _ hty => ?_⟩
      simp only [List.mem_singleton] at ht
      subst t
      have h0 := hfin x' hx'
      rw [← rcons_upd] at h0
      exact hmono _ _ (envLe_rcons (fun _ _ h => h) (fun c hc => hty c hc)) _ h0
  · rcases hG with hG | ⟨table, he, _⟩
    · cases hG
    · cases he

theorem rows_finite (F : REnv → Value)
    (hmono : ∀ σ σ', EnvLe σ σ' → ∀ d, F σ d → F σ' d)
    (ihF : ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), F (upd σ j x) d →
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → F (upd σ j x') d)
    (σ : REnv) (j : Nat) (x : Value) :
    (g : List (List CptI × CptI)) →
    (∀ s ∈ g, NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
      (fun y => F (rcons y (upd σ j x)))) (demand s.1) s.2) →
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) →
      ∀ s ∈ g, NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
        (fun y => F (rcons y (upd σ j x')))) (demand s.1) s.2
  | [], _ => ⟨[], by simp, fun _ _ s hs => by cases hs⟩
  | s :: g, h => by
      obtain ⟨us₁, hus₁, h₁⟩ := row_finite F hmono ihF σ j x _ _ (h s (by simp))
      obtain ⟨us₂, hus₂, h₂⟩ := rows_finite F hmono ihF σ j x g (fun t ht => h t (by simp [ht]))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun x' hx' t ht => ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hus₁ u hu
        · exact hus₂ u hu
      · rcases List.mem_cons.mp ht with ht | ht
        · subst ht
          exact h₁ x' (fun u hu => hx' u (List.mem_append_left _ hu))
        · exact h₂ x' (fun u hu => hx' u (List.mem_append_right _ hu)) t ht

theorem var_finite (σ : REnv) (i j : Nat) (x : Value) (d : CptI)
    (hd : withBot (upd σ j x i) d) :
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → withBot (upd σ j x' i) d := by
  rcases hd with hb | hd
  · exact ⟨[], by simp, fun _ _ => Or.inl hb⟩
  by_cases h : i = j
  · have hd' : (if i = j then x else σ i) d := hd
    rw [if_pos h] at hd'
    refine ⟨[d], fun u hu => by simp only [List.mem_singleton] at hu; subst hu; exact hd',
      fun x' hx' => Or.inr ?_⟩
    show (if i = j then x' else σ i) d
    rw [if_pos h]
    exact hx' d (by simp)
  · refine ⟨[], by simp, fun x' _ => Or.inr ?_⟩
    show (if i = j then x' else σ i) d
    rw [if_neg h]
    have hd' : (if i = j then x else σ i) d := hd
    rwa [if_neg h] at hd'

theorem pi_finite (A : REnv → Value) (F : REnv → Value) (lvl : Option Nat)
    (ihA : ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), A (upd σ j x) d →
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → A (upd σ j x') d)
    (hmono : ∀ σ σ', EnvLe σ σ' → ∀ d, F σ d → F σ' d)
    (ihF : ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), F (upd σ j x) d →
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → F (upd σ j x') d)
    (σ : REnv) (j : Nat) (x : Value) (d : CptI)
    (hd : InductiveCodes.piValue lvl (A (upd σ j x))
      (UnifiedPi.legalGraph (fun _ _ => True) (fun y => F (rcons y (upd σ j x)))) d) :
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) →
      InductiveCodes.piValue lvl (A (upd σ j x'))
        (UnifiedPi.legalGraph (fun _ _ => True) (fun y => F (rcons y (upd σ j x')))) d := by
  rcases hd with hd | ⟨a, p, he, ha, hp | ⟨a', g, hpe, hA, hrows⟩⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hd⟩
  · exact ⟨[], by simp, fun _ _ => Or.inr ⟨a, p, he, ha, Or.inl hp⟩⟩
  · obtain ⟨us₁, hus₁, h₁⟩ := ihA σ j x a' hA
    obtain ⟨us₂, hus₂, h₂⟩ := rows_finite F hmono ihF σ j x g hrows
    refine ⟨us₁ ++ us₂, fun u hu => ?_, fun x' hx' => ?_⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact hus₁ u hu
      · exact hus₂ u hu
    · exact Or.inr ⟨a, p, he, ha, Or.inr ⟨a', g, hpe,
        h₁ x' (fun u hu => hx' u (List.mem_append_left _ hu)),
        h₂ x' (fun u hu => hx' u (List.mem_append_right _ hu))⟩⟩

/-- Raw images are finitely determined in every environment slot. -/
theorem image_finite : {k : Nat} → (c : LCode k) → ∀ (κ : List (Option Nat)), Kinded κ c →
    ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), image (upd σ j x) c d →
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → image (upd σ j x') c d
  | _, .var0 i, _, _, σ, j, x, d, hd => var_finite σ i j x d hd
  | _, .prop _, _, hk, σ, j, x, d, hd => hk.cont.finite σ j x d hd
  | _, .pi0 A B, κ, hk, σ, j, x, d, hd =>
      pi_finite (fun σ => image σ A) (fun σ => image σ B) (some 0) (image_finite A κ hk.1)
        (fun σ σ' h => image_mono B _ hk.2 h) (image_finite B _ hk.2) σ j x d hd
  | _, .var _ i, _, _, σ, j, x, d, hd => var_finite σ i j x d hd
  | _, .univ _, _, _, _, _, _, _, hd => ⟨[], by simp, fun _ _ => hd⟩
  | _, .neutral _ _, _, _, _, _, _, _, hd => ⟨[], by simp, fun _ _ => hd⟩
  | _, .pi c A B, κ, hk, σ, j, x, d, hd =>
      pi_finite (fun σ => image σ A) (fun σ => image σ B) (some (c + 1))
        (image_finite A κ hk.1) (fun σ σ' h => image_mono B _ hk.2 h) (image_finite B _ hk.2)
        σ j x d hd

/-- The codomain's raw image function has finite demand. -/
theorem codomain_finite {k : Nat} (B : LCode k) (κ : List (Option Nat)) (hB : Kinded κ B)
    (σ : REnv) :
    UnifiedPi.LegalFiniteDemand (fun _ _ => True) (fun x => image (rcons x σ) B) := by
  intro x _ c hc
  have he : ∀ y, upd (rcons x σ) 0 y = rcons y σ := by
    intro y
    funext i
    cases i <;> rfl
  have hc' : image (upd (rcons x σ) 0 x) B c := by rw [he]; exact hc
  obtain ⟨us, hus, hfin⟩ := image_finite B κ hB (rcons x σ) 0 x c hc'
  refine ⟨us, hus, fun y _ hy => ?_⟩
  have h := hfin y hy
  rw [he] at h
  exact h

/-! ## Bottom, levels and observations of images -/

theorem image_bot {k : Nat} (σ : REnv) : (c : LCode k) → ∀ (κ : List (Option Nat)), Kinded κ c →
    image σ c .bot
  | .var0 _, _, _ => Or.inl rfl
  | .prop _, _, hk => hk.bot σ
  | .pi0 _ _, _, _ => Or.inl rfl
  | .var _ _, _, _ => Or.inl rfl
  | .univ _, _, _ => .bot _ _
  | .neutral _ _, _, _ => NativeMemberValues.value_bot _ _
  | .pi _ _ _, _, _ => Or.inl rfl

/-- The level of a non-variable code. -/
def lvlOf : {k : Nat} → LCode k → Option Nat
  | k, _ => some k

/-- Non-variable codes have defined images at their level. -/
def NonVar : {k : Nat} → LCode k → Prop
  | _, .var0 _ => False
  | _, .var _ _ => False
  | _, _ => True

theorem nonvar_level {k : Nat} (σ : REnv) : (c : LCode k) → ∀ (κ : List (Option Nat)),
    Kinded κ c → NonVar c → SortMember (some k) (image σ c) ∧ TypeDefined (image σ c)
  | .var0 _, _, _, h => h.elim
  | .prop _, _, hk, _ => ⟨hk.level σ, hk.defined σ⟩
  | .pi0 _ _, _, _, _ => ⟨InductiveCodes.piValue_level _ _ _, InductiveCodes.piValue_defined _ _ _⟩
  | .var _ _, _, _, h => h.elim
  | .univ k, _, _, _ => ⟨sort_member _ (some k), sort_defined _ (some k)⟩
  | .neutral k name, _, _, _ =>
      ⟨NativeMemberValues.value_level (some (k + 1)) name,
        NativeMemberValues.value_defined (some (k + 1)) name⟩
  | .pi _ _ _, _, _, _ => ⟨InductiveCodes.piValue_level _ _ _, InductiveCodes.piValue_defined _ _ _⟩

def ImageEq {k l : Nat} (c : LCode k) (d : LCode l) : Prop :=
  ∀ σ : REnv, BotEnv σ → ValueEq (image σ c) (image σ d)

theorem botEnv_const_bottom : BotEnv (constEnv bottom) := fun _ => rfl

theorem defined_nonbot {V : Value} (h : TypeDefined V) : ∃ c, V c ∧ c ≠ .bot := by
  obtain ⟨i, p, hp⟩ := h
  exact ⟨_, hp, fun h => CptI.noConfusion h⟩

/-- A variable's image is not a non-variable's image. -/
theorem var_vs_nonvar {l : Nat} {i : Nat} (d : LCode l) (κ : List (Option Nat)) (hk : Kinded κ d)
    (hd : NonVar d) (h : ∀ σ : REnv, BotEnv σ → ValueEq (withBot (σ i)) (image σ d)) : False := by
  obtain ⟨c, hc, hne⟩ := defined_nonbot (nonvar_level (constEnv bottom) d κ hk hd).2
  rcases (h (constEnv bottom) botEnv_const_bottom c).mpr hc with h0 | h0
  · exact hne h0
  · exact hne h0

theorem var_vs_var {i j : Nat} (h : ∀ σ : REnv, BotEnv σ → ValueEq (withBot (σ i)) (withBot (σ j))) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · exfalso
    let σ : REnv := fun n => if n = i then universeValue (some 0) else universeValue (some 1)
    have hσ : BotEnv σ := by
      intro n
      show (if n = i then universeValue (some 0) else universeValue (some 1)) .bot
      split <;> exact .bot _ _
    have h1 := h σ hσ
    have wb : ∀ v : Value, v .bot → ValueEq (withBot v) v := fun v hv c =>
      ⟨fun h => h.elim (fun h => h ▸ hv) id, Or.inr⟩
    have hi : σ i = universeValue (some 0) := by
      show (if i = i then _ else _) = _
      rw [if_pos rfl]
    have hj : σ j = universeValue (some 1) := by
      show (if j = i then _ else _) = _
      rw [if_neg (fun h => hij h.symm)]
    have h1 : ValueEq (σ i) (σ j) := (wb _ (hσ i)).symm.trans (h1.trans (wb _ (hσ j)))
    rw [hi, hj] at h1
    have := sort_code_injective h1
    cases this

theorem level_sep {V W : Value} {i j : Option Nat} (hV : SortMember i V) (hd : TypeDefined V)
    (hW : SortMember j W) (h : ValueEq V W) : i = j :=
  sortMember_unique hV (sortMember_congr h.symm hW) hd

theorem neutral_tagged (σ : REnv) (k name : Nat) :
    ValueEq (image σ (LCode.neutral k name))
      (InductiveCodes.taggedValue (some (k + 1)) (NeutralPER.neutralAtom name)) :=
  (InductiveCodes.taggedValue_denI EnvI.bot (some (k + 1)) (.const name [])).symm

theorem neutral_name_eq {k l n m : Nat}
    (h : ValueEq (NativeMemberValues.value (some k) n) (NativeMemberValues.value (some l) m))
    (hkl : k = l) : n = m := by
  subst hkl
  have hobs : InductiveCodes.taggedValue (some k) (NeutralPER.neutralAtom n)
      (NeutralCodes.fullTag (some k) (.spine n [])) :=
    (InductiveCodes.taggedValue_full _ _ _).mpr (NeutralPER.neutralAtom_observed n)
  have h2 := (InductiveCodes.taggedValue_denI EnvI.bot (some k) (.const n []) _).mp hobs
  have h3 := (h _).mp h2
  have h4 := (InductiveCodes.taggedValue_denI EnvI.bot (some k) (.const m []) _).mpr h3
  have h5 := (InductiveCodes.taggedValue_full _ _ _).mp h4
  rcases approxI_const_inv h5 with h6 | h6
  · cases h6
  · exact (CptI.spine.inj h6).1

theorem univ_payload_spine {k : Nat} (p : CptI)
    (h : TypeZeroTowerProbe.payload (TypeZeroTowerProbe.Code.univ k) p) :
    p = .bot ∨ ∃ r args, p = .spine r args := TypeZeroTowerProbe.univ_spine p h

theorem atom_spine (name : Nat) (p : CptI) (h : NeutralPER.neutralAtom name p) :
    p = .bot ∨ ∃ r args, p = .spine r args := by
  rcases approxI_const_inv h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨name, [], h⟩

/-! ## Twins: equal up to level-zero parts -/

inductive Twin : {k l : Nat} → LCode k → LCode l → Prop
  | zero {c d : LCode 0} : Twin c d
  | var (k i : Nat) : Twin (LCode.var k i) (LCode.var k i)
  | univ (k : Nat) : Twin (LCode.univ k) (LCode.univ k)
  | neutral (k name : Nat) : Twin (LCode.neutral k name) (LCode.neutral k name)
  | pi {c c' a b a' b' : Nat} {A : LCode a} {B : LCode (b + 1)} {A' : LCode a'}
      {B' : LCode (b' + 1)} (hA : Twin A A') (hB : Twin B B') :
      Twin (LCode.pi c A B) (LCode.pi c' A' B')

theorem twin_refl : {k : Nat} → (c : LCode k) → Twin c c
  | _, .var0 _ => .zero
  | _, .prop _ => .zero
  | _, .pi0 _ _ => .zero
  | _, .var k i => .var k i
  | _, .univ k => .univ k
  | _, .neutral k n => .neutral k n
  | _, .pi _ A B => .pi (twin_refl A) (twin_refl B)

theorem twin_symm {k l : Nat} {c : LCode k} {d : LCode l} (h : Twin c d) : Twin d c := by
  induction h with
  | zero => exact .zero
  | var k i => exact .var k i
  | univ k => exact .univ k
  | neutral k n => exact .neutral k n
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem twin_trans {k l : Nat} {c : LCode k} {d : LCode l} (h : Twin c d) :
    ∀ {m : Nat} {e : LCode m}, Twin d e → Twin c e := by
  induction h with
  | zero => intro m e h2; cases h2; exact .zero
  | var k i => intro m e h2; cases h2; exact .var k i
  | univ k => intro m e h2; cases h2; exact .univ k
  | neutral k n => intro m e h2; cases h2; exact .neutral k n
  | pi _ _ ihA ihB => intro m e h2; cases h2 with | pi hA hB => exact .pi (ihA hA) (ihB hB)

theorem twin_kindOf {k l : Nat} {c : LCode k} {d : LCode l} (h : Twin c d) :
    kindOf c = kindOf d := by
  cases h with
  | zero => rename_i c d; cases c <;> cases d <;> rfl
  | _ => rfl

/-! ## Image-equal kinded codes are twins -/

theorem kinded_var_level {κ : List (Option Nat)} {i k l : Nat}
    (h1 : κ[i]? = some (some k)) (h2 : κ[i]? = some (some l)) : k = l := by
  rw [h1] at h2
  injection h2 with h2
  injection h2

theorem univ_tagged' (k : Nat) :
    ValueEq (universeValue (some k))
      (InductiveCodes.taggedValue (some (k + 1))
        (TypeZeroTowerProbe.payload (TypeZeroTowerProbe.Code.univ k))) :=
  TypeZeroTowerProbe.image_tagged (TypeZeroTowerProbe.Code.univ k)

theorem pi_components {c c' a b a' b' : Nat} {A : LCode a} {B : LCode (b + 1)} {A' : LCode a'}
    {B' : LCode (b' + 1)} {κ : List (Option Nat)} (hc : Kinded κ (LCode.pi c A B))
    (hd : Kinded κ (LCode.pi c' A' B')) (h : ImageEq (LCode.pi c A B) (LCode.pi c' A' B')) :
    ImageEq A A' ∧ ImageEq B B' := by
  refine ⟨fun σ' hσ' => ?_, fun σ' hσ' => ?_⟩
  · exact (InductiveCodes.piValue_injective (image_bot σ' A κ hc.1) (image_bot σ' A' κ hd.1)
      (h σ' hσ')).2.1
  · have htail : BotEnv (fun i => σ' (i + 1)) := fun i => hσ' (i + 1)
    have he : rcons (σ' 0) (fun i => σ' (i + 1)) = σ' := by
      funext i
      cases i <;> rfl
    obtain ⟨_, _, hcod⟩ := InductiveCodes.piValue_injective
      (image_bot _ A κ hc.1) (image_bot _ A' κ hd.1) (h _ htail)
    have h1 := applyValue_legalGraph_at (codomain_finite B _ hc.2 (fun i => σ' (i + 1)))
      (x := σ' 0) (image_bot _ B _ hc.2)
    have h2 := applyValue_legalGraph_at (codomain_finite B' _ hd.2 (fun i => σ' (i + 1)))
      (x := σ' 0) (image_bot _ B' _ hd.2)
    rw [he] at h1 h2
    exact h1.symm.trans ((hcod (σ' 0)).trans h2)

theorem level0_vs_pos {k : Nat} (c : LCode 0) (d : LCode (k + 1)) (κ : List (Option Nat))
    (hc : Kinded κ c) (hd : Kinded κ d) (hnc : NonVar c) (hnd : NonVar d)
    (h : ImageEq c d) : False := by
  have l1 := nonvar_level (constEnv bottom) c κ hc hnc
  have l2 := nonvar_level (constEnv bottom) d κ hd hnd
  have := level_sep l1.1 l1.2 l2.1 (h _ botEnv_const_bottom)
  injection this with this
  exact Nat.succ_ne_zero k this.symm

theorem imageEq_twin : {k : Nat} → (c : LCode k) → {l : Nat} → (d : LCode l) →
    ∀ κ : List (Option Nat), Kinded κ c → Kinded κ d → ImageEq c d → Twin c d
  -- both level zero
  | _, .var0 _, _, .var0 _, _, _, _, _ => .zero
  | _, .var0 _, _, .prop _, _, _, _, _ => .zero
  | _, .var0 _, _, .pi0 _ _, _, _, _, _ => .zero
  | _, .prop _, _, .var0 _, _, _, _, _ => .zero
  | _, .prop _, _, .prop _, _, _, _, _ => .zero
  | _, .prop _, _, .pi0 _ _, _, _, _, _ => .zero
  | _, .pi0 _ _, _, .var0 _, _, _, _, _ => .zero
  | _, .pi0 _ _, _, .prop _, _, _, _, _ => .zero
  | _, .pi0 _ _, _, .pi0 _ _, _, _, _, _ => .zero
  -- a level-zero variable against a positive code
  | _, .var0 i, _, .var l j, _, hc, hd, h => by
      have hij := var_vs_var h
      subst hij
      exact absurd (kinded_var_level hc hd) (Nat.succ_ne_zero l).symm
  | _, .var0 _, _, .univ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .var0 _, _, .neutral _ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .var0 _, _, .pi _ _ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .var l i, _, .var0 j, _, hc, hd, h => by
      have hij := var_vs_var h
      subst hij
      exact absurd (kinded_var_level hc hd) (Nat.succ_ne_zero l)
  | _, .univ _, _, .var0 _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .neutral _ _, _, .var0 _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .pi _ _ _, _, .var0 _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  -- a positive variable against a level-zero non-variable
  | _, .var _ _, _, .prop _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .var _ _, _, .pi0 _ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .prop _, _, .var _ _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .pi0 _ _, _, .var _ _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  -- level-zero non-variables against positive non-variables
  | _, .prop _, _, .univ _, κ, hc, hd, h => (level0_vs_pos _ _ κ hc hd trivial trivial h).elim
  | _, .prop _, _, .neutral _ _, κ, hc, hd, h => (level0_vs_pos _ _ κ hc hd trivial trivial h).elim
  | _, .prop _, _, .pi _ _ _, κ, hc, hd, h => (level0_vs_pos _ _ κ hc hd trivial trivial h).elim
  | _, .pi0 _ _, _, .univ _, κ, hc, hd, h => (level0_vs_pos _ _ κ hc hd trivial trivial h).elim
  | _, .pi0 _ _, _, .neutral _ _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hc hd trivial trivial h).elim
  | _, .pi0 _ _, _, .pi _ _ _, κ, hc, hd, h => (level0_vs_pos _ _ κ hc hd trivial trivial h).elim
  | _, .univ _, _, .prop _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hd hc trivial trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .univ _, _, .pi0 _ _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hd hc trivial trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .neutral _ _, _, .prop _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hd hc trivial trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .neutral _ _, _, .pi0 _ _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hd hc trivial trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .pi _ _ _, _, .prop _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hd hc trivial trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .pi _ _ _, _, .pi0 _ _, κ, hc, hd, h =>
      (level0_vs_pos _ _ κ hd hc trivial trivial (fun σ hσ => (h σ hσ).symm)).elim
  -- positive codes
  | _, .var k i, _, .var l j, _, hc, hd, h => by
      have hij := var_vs_var h
      subst hij
      have hkl := Nat.succ.inj (kinded_var_level hc hd)
      subst hkl
      exact .var k i
  | _, .var _ _, _, .univ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .var _ _, _, .neutral _ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .var _ _, _, .pi _ _ _, κ, _, hd, h => (var_vs_nonvar _ κ hd trivial h).elim
  | _, .univ _, _, .var _ _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .neutral _ _, _, .var _ _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .pi _ _ _, _, .var _ _, κ, hc, _, h =>
      (var_vs_nonvar _ κ hc trivial (fun σ hσ => (h σ hσ).symm)).elim
  | _, .univ k, _, .univ j, _, _, _, h => by
      have hkj : some k = some j := sort_code_injective (h _ botEnv_const_bottom)
      cases hkj
      exact .univ k
  | _, .univ k, _, .neutral l name, _, _, _, h => by
      have h0 : ValueEq (TypeZeroTowerProbe.image (TypeZeroTowerProbe.Code.univ k))
          (TypeZeroTowerProbe.image (TypeZeroTowerProbe.Code.neutral (l + 1) name)) :=
        h _ botEnv_const_bottom
      exact (TypeZeroTowerProbe.not_univ_neutral h0).elim
  | _, .neutral l name, _, .univ k, _, _, _, h => by
      have h0 : ValueEq (TypeZeroTowerProbe.image (TypeZeroTowerProbe.Code.univ k))
          (TypeZeroTowerProbe.image (TypeZeroTowerProbe.Code.neutral (l + 1) name)) :=
        (h _ botEnv_const_bottom).symm
      exact (TypeZeroTowerProbe.not_univ_neutral h0).elim
  | _, .neutral k n, _, .neutral l m, κ, hc, hd, h => by
      have h0 := h _ botEnv_const_bottom
      have l1 := nonvar_level (constEnv bottom) (LCode.neutral k n) κ hc trivial
      have l2 := nonvar_level (constEnv bottom) (LCode.neutral l m) κ hd trivial
      have hkl := level_sep l1.1 l1.2 l2.1 h0
      injection hkl with hkl
      have hkl' := Nat.succ.inj hkl
      subst hkl'
      have hnm := neutral_name_eq h0 rfl
      subst hnm
      exact .neutral k n
  | _, .univ k, _, .pi _ A _, κ, _, hd, h =>
      (pi_vs_tagged (image_bot _ A κ hd.1)
        (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
        ((h _ botEnv_const_bottom).symm.trans (univ_tagged' k))).elim
  | _, .pi _ A _, _, .univ k, κ, hc, _, h =>
      (pi_vs_tagged (image_bot _ A κ hc.1)
        (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
        ((h _ botEnv_const_bottom).trans (univ_tagged' k))).elim
  | _, .neutral k name, _, .pi _ A _, κ, _, hd, h =>
      (pi_vs_tagged (image_bot _ A κ hd.1) (fun p hp => atom_spine name p hp)
        ((h _ botEnv_const_bottom).symm.trans (neutral_tagged _ k name))).elim
  | _, .pi _ A _, _, .neutral k name, κ, hc, _, h =>
      (pi_vs_tagged (image_bot _ A κ hc.1) (fun p hp => atom_spine name p hp)
        ((h _ botEnv_const_bottom).trans (neutral_tagged _ k name))).elim
  | _, .pi _ A B, _, .pi _ A' B', κ, hc, hd, h => by
      obtain ⟨hA, hB⟩ := pi_components hc hd h
      have tA := imageEq_twin A A' κ hc.1 hd.1 hA
      have hB' : Kinded (kindOf A :: κ) B' := by
        rw [twin_kindOf tA]
        exact hd.2
      exact .pi tA (imageEq_twin B B' _ hc.2 hB' hB)

/-! ## Closed images -/

theorem image_closed : {k : Nat} → (c : LCode k) → ∀ (n : Nat) (σ σ' : REnv),
    ClosedAt n c → (∀ i, i < n → σ i = σ' i) → image σ c = image σ' c
  | _, .var0 i, _, σ, σ', hc, h => by
      show withBot (σ i) = withBot (σ' i)
      rw [h i hc]
  | _, .prop _, _, σ, σ', hc, h => hc σ σ' h
  | _, .pi0 A B, n, σ, σ', hc, h => by
      have hA := image_closed A n σ σ' hc.1 h
      have hB : (fun x => image (rcons x σ) B) = (fun x => image (rcons x σ') B) := by
        funext x
        exact image_closed B (n + 1) _ _ hc.2 (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (Nat.lt_of_succ_lt_succ hi))
      show InductiveCodes.piValue _ (image σ A) _ = InductiveCodes.piValue _ (image σ' A) _
      rw [hA, hB]
  | _, .var _ i, _, σ, σ', hc, h => by
      show withBot (σ i) = withBot (σ' i)
      rw [h i hc]
  | _, .univ _, _, _, _, _, _ => rfl
  | _, .neutral _ _, _, _, _, _, _ => rfl
  | _, .pi _ A B, n, σ, σ', hc, h => by
      have hA := image_closed A n σ σ' hc.1 h
      have hB : (fun x => image (rcons x σ) B) = (fun x => image (rcons x σ') B) := by
        funext x
        exact image_closed B (n + 1) _ _ hc.2 (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact h i (Nat.lt_of_succ_lt_succ hi))
      show InductiveCodes.piValue _ (image σ A) _ = InductiveCodes.piValue _ (image σ' A) _
      rw [hA, hB]

/-- Closed, kinded codes. -/
def WFc {k : Nat} (c : LCode k) : Prop := Kinded [] c ∧ ClosedAt 0 c

theorem wfc_imageEq {k l : Nat} {c : LCode k} {d : LCode l} (hc : WFc c) (hd : WFc d)
    (σ : REnv) (h : ValueEq (image σ c) (image σ d)) : ImageEq c d := by
  intro σ' _
  rw [image_closed c 0 σ' σ hc.2 (fun _ hi => absurd hi (Nat.not_lt_zero _)),
    image_closed d 0 σ' σ hd.2 (fun _ hi => absurd hi (Nat.not_lt_zero _))]
  exact h

/-! ## The level reading -/

/-- Chaos: every pair of bottom-carrying values. -/
def chaos : Relation := fun x y => x .bot ∧ y .bot

theorem chaos_laws : Laws chaos := ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, _⟩ ⟨_, b⟩ => ⟨a, b⟩⟩

/-- The level reading. Every level-zero code and every named neutral type is
chaotic. A universe relates the images of twin closed codes of its level.
A positive type variable reads its candidate, and a positive product is
hereditary over every admissible candidate for its bound variable. -/
def ElA (adm : Adm) : {k : Nat} → REnv → CEnv → LCode k → Relation
  | _, _, _, .var0 _ => chaos
  | _, _, _, .prop _ => chaos
  | _, _, _, .pi0 _ _ => chaos
  | _, _, ρ, .var _ i => ρ i
  | _, σ, _, .univ k => fun V W => ∃ c d : LCode k, WFc c ∧ WFc d ∧ Twin c d ∧
      ValueEq V (image σ c) ∧ ValueEq W (image σ d)
  | _, _, _, .neutral _ _ => chaos
  | _, σ, ρ, .pi _ A B => fun f g => f .bot ∧ g .bot ∧ ∀ x y, ElA adm σ ρ A x y →
      ∀ R : Relation, adm x y R →
        ElA adm (rcons x σ) (ccons R ρ) B (NeutralPi.applyValue f x)
          (NeutralPi.applyValue g y) ∧
        ElA adm (rcons y σ) (ccons R ρ) B (NeutralPi.applyValue f x)
          (NeutralPi.applyValue g y)

theorem el_zero {adm : Adm} (σ : REnv) (ρ : CEnv) : (c : LCode 0) → ElA adm σ ρ c = chaos
  | .var0 _ => rfl
  | .prop _ => rfl
  | .pi0 _ _ => rfl

/-- Twins have the same reading. -/
theorem el_twin {adm : Adm} {k l : Nat} {c : LCode k} {d : LCode l} (h : Twin c d) :
    ∀ σ ρ, Same (ElA adm σ ρ c) (ElA adm σ ρ d) := by
  induction h with
  | zero =>
      rename_i c d
      intro σ ρ
      rw [el_zero σ ρ c, el_zero σ ρ d]
      exact fun _ _ => Iff.rfl
  | var => exact fun _ _ _ _ => Iff.rfl
  | univ => exact fun _ _ _ _ => Iff.rfl
  | neutral => exact fun _ _ _ _ => Iff.rfl
  | pi _ _ ihA ihB =>
      intro σ ρ f g
      constructor
      · rintro ⟨hf, hg, hfg⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := hfg x y ((ihA σ ρ x y).mpr hxy) R hR
        exact ⟨(ihB _ _ _ _).mp h1, (ihB _ _ _ _).mp h2⟩
      · rintro ⟨hf, hg, hfg⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := hfg x y ((ihA σ ρ x y).mp hxy) R hR
        exact ⟨(ihB _ _ _ _).mpr h1, (ihB _ _ _ _).mpr h2⟩

theorem el_saturated {adm : Adm} {k : Nat} (σ : REnv) (ρ : CEnv) (h : SatEnv σ ρ) :
    (c : LCode k) → ∀ x y, ElA adm σ ρ c x y → x .bot
  | .var0 _ => fun _ _ hxy => hxy.1
  | .prop _ => fun _ _ hxy => hxy.1
  | .pi0 _ _ => fun _ _ hxy => hxy.1
  | .var _ i => fun _ _ hxy => (h.1 i).2 _ _ hxy
  | .univ _ => fun _ _ ⟨c, _, hc, _, _, hx, _⟩ => (hx .bot).mpr (image_bot σ c [] hc.1)
  | .neutral _ _ => fun _ _ hxy => hxy.1
  | .pi _ _ _ => fun _ _ hxy => hxy.1

/-- Every reading is a PER in a saturated environment. -/
theorem el_laws {adm : Adm} (ha : AdmLaws adm) :
    {k : Nat} → (c : LCode k) → ∀ σ ρ, SatEnv σ ρ → Laws (ElA adm σ ρ c)
  | _, .var0 _, _, _, _ => chaos_laws
  | _, .prop _, _, _, _ => chaos_laws
  | _, .pi0 _ _, _, _, _ => chaos_laws
  | _, .var _ i, _, _, h => (h.1 i).1
  | _, .univ _, σ, _, _ => by
      refine ⟨?_, ?_⟩
      · rintro V W ⟨c, d, hc, hd, ht, hV, hW⟩
        exact ⟨d, c, hd, hc, twin_symm ht, hW, hV⟩
      · rintro V W Z ⟨c, d, hc, hd, ht, hV, hW⟩ ⟨d', e, hd', he, ht', hW', hZ⟩
        have hdd : Twin d d' := imageEq_twin d d' [] hd.1 hd'.1
          (wfc_imageEq hd hd' σ (hW.symm.trans hW'))
        exact ⟨c, e, hc, he, twin_trans ht (twin_trans hdd ht'), hV, hZ⟩
  | _, .neutral _ _, _, _, _ => chaos_laws
  | _, .pi _ A B, σ, ρ, h => by
      have lA := el_laws ha A σ ρ h
      have bot : ∀ x y, ElA adm σ ρ A x y → x .bot := el_saturated σ ρ h A
      refine ⟨?_, ?_⟩
      · rintro f g ⟨hf, hg, hfg⟩
        refine ⟨hg, hf, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := hfg y x (lA.symm hxy) R (ha.symm hR)
        exact ⟨(el_laws ha B _ _ (satEnv_rcons h (bot x y hxy) (ha.sat hR))).symm h2,
          (el_laws ha B _ _ (satEnv_rcons h (bot y x (lA.symm hxy)) (ha.sat hR))).symm h1⟩
      · rintro f g k ⟨hf, _, hfg⟩ ⟨_, hk, hgk⟩
        refine ⟨hf, hk, fun x y hxy R hR => ?_⟩
        have hxx := lA.trans hxy (lA.symm hxy)
        have hyy := lA.trans (lA.symm hxy) hxy
        exact ⟨(el_laws ha B _ _ (satEnv_rcons h (bot x y hxy) (ha.sat hR))).trans
            (hfg x x hxx R (ha.left hR)).1 (hgk x y hxy R hR).1,
          (el_laws ha B _ _ (satEnv_rcons h (bot y x (lA.symm hxy)) (ha.sat hR))).trans
            (hfg x y hxy R hR).2 (hgk y y hyy R (ha.left (ha.symm hR))).1⟩

/-- The reading does not depend on the raw environment. -/
theorem el_raw {adm : Adm} : {k : Nat} → (c : LCode k) → ∀ (σ σ' : REnv) (ρ : CEnv),
    Same (ElA adm σ ρ c) (ElA adm σ' ρ c)
  | _, .var0 _, _, _, _ => fun _ _ => Iff.rfl
  | _, .prop _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi0 _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .var _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .univ _, σ, σ', _ => fun _ _ => by
      constructor
      · rintro ⟨c, d, hc, hd, ht, hV, hW⟩
        rw [image_closed c 0 σ σ' hc.2 (fun _ hi => absurd hi (Nat.not_lt_zero _))] at hV
        rw [image_closed d 0 σ σ' hd.2 (fun _ hi => absurd hi (Nat.not_lt_zero _))] at hW
        exact ⟨c, d, hc, hd, ht, hV, hW⟩
      · rintro ⟨c, d, hc, hd, ht, hV, hW⟩
        rw [image_closed c 0 σ' σ hc.2 (fun _ hi => absurd hi (Nat.not_lt_zero _))] at hV
        rw [image_closed d 0 σ' σ hd.2 (fun _ hi => absurd hi (Nat.not_lt_zero _))] at hW
        exact ⟨c, d, hc, hd, ht, hV, hW⟩
  | _, .neutral _ _, _, _, _ => fun _ _ => Iff.rfl
  | _, .pi _ A B, σ, σ', ρ => fun f g => by
      constructor
      · rintro ⟨hf, hg, h⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := h x y ((el_raw A σ σ' ρ x y).mpr hxy) R hR
        exact ⟨(el_raw B _ _ _ _ _).mp h1, (el_raw B _ _ _ _ _).mp h2⟩
      · rintro ⟨hf, hg, h⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        obtain ⟨h1, h2⟩ := h x y ((el_raw A σ σ' ρ x y).mp hxy) R hR
        exact ⟨(el_raw B _ _ _ _ _).mp h1, (el_raw B _ _ _ _ _).mp h2⟩

/-! ## Joint continuity of images -/

/-- Finitely many requirements combine into one. -/
theorem combine_reqs {α : Type} (σ : REnv) (Q : REnv → α → Prop) :
    (g : List α) → (∀ s ∈ g, ∃ S : List (Nat × CptI), (∀ p ∈ S, σ p.1 p.2) ∧
      ∀ σ' : REnv, (∀ p ∈ S, σ' p.1 p.2) → Q σ' s) →
    ∃ S : List (Nat × CptI), (∀ p ∈ S, σ p.1 p.2) ∧
      ∀ σ' : REnv, (∀ p ∈ S, σ' p.1 p.2) → ∀ s ∈ g, Q σ' s
  | [], _ => ⟨[], by simp, fun _ _ s hs => by cases hs⟩
  | s :: g, h => by
      obtain ⟨S₁, h₁, k₁⟩ := h s (by simp)
      obtain ⟨S₂, h₂, k₂⟩ := combine_reqs σ Q g (fun t ht => h t (by simp [ht]))
      refine ⟨S₁ ++ S₂, fun p hp => ?_, fun σ' hσ' t ht => ?_⟩
      · rcases List.mem_append.mp hp with hp | hp
        · exact h₁ p hp
        · exact h₂ p hp
      · rcases List.mem_cons.mp ht with ht | ht
        · subst ht
          exact k₁ σ' (fun p hp => hσ' p (List.mem_append_left _ hp))
        · exact k₂ σ' (fun p hp => hσ' p (List.mem_append_right _ hp)) t ht

/-- Shift requirements on an extended environment down to the tail,
dropping slot zero. -/
def shiftReqs (S : List (Nat × CptI)) : List (Nat × CptI) :=
  S.filterMap (fun p => match p.1 with | 0 => none | i + 1 => some (i, p.2))

theorem shiftReqs_sound {S : List (Nat × CptI)} {σ : REnv} {y : Value}
    (h : ∀ p ∈ S, rcons y σ p.1 p.2) : ∀ p ∈ shiftReqs S, σ p.1 p.2 := by
  intro p hp
  obtain ⟨q, hq, he⟩ := List.mem_filterMap.mp hp
  obtain ⟨i, u⟩ := q
  cases i with
  | zero => exact Option.noConfusion he
  | succ i =>
      injection he with he
      subst he
      exact h _ hq

theorem shiftReqs_back {S : List (Nat × CptI)} {σ' : REnv} {y : Value}
    (h0 : ∀ u, (0, u) ∈ S → y u) (h : ∀ p ∈ shiftReqs S, σ' p.1 p.2) :
    ∀ p ∈ S, rcons y σ' p.1 p.2 := by
  intro p hp
  obtain ⟨i, u⟩ := p
  cases i with
  | zero => exact h0 u hp
  | succ i => exact h (i, u) (List.mem_filterMap.mpr ⟨_, hp, rfl⟩)

/-- A product image is jointly continuous when its domain and codomain are. -/
theorem pi_cont (A : REnv → Value) (F : REnv → Value) (lvl : Option Nat)
    (hA : JointCont A) (hF : JointCont F)
    (hmono : ∀ σ σ', EnvLe σ σ' → ∀ d, F σ d → F σ' d) :
    JointCont (fun σ => InductiveCodes.piValue lvl (A σ)
      (UnifiedPi.legalGraph (fun _ _ => True) (fun x => F (rcons x σ)))) := by
  intro σ d hd
  rcases hd with hd | ⟨a, p, he, ha, hp | ⟨a', g, hpe, hAobs, hrows⟩⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hd⟩
  · exact ⟨[], by simp, fun _ _ => Or.inr ⟨a, p, he, ha, Or.inl hp⟩⟩
  · obtain ⟨SA, hSA, kA⟩ := hA σ a' hAobs
    obtain ⟨SR, hSR, kR⟩ := combine_reqs σ (fun σ' s =>
        NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True) (fun x => F (rcons x σ')))
          (demand s.1) s.2) g (by
      intro s hs
      rcases hrows s hs with hc | ⟨g', t, hc, hG, ht, hdem⟩ | ⟨_, _, _, _, hG, _⟩
      · exact ⟨[], by simp, fun _ _ => Or.inl hc⟩
      · rcases hG with hG | ⟨table, hte, rows⟩
        · cases hG
        · cases hte
          have hmin : F (rcons (demand t.1) σ) t.2 := rows t ht (demand t.1) True.intro (fun u hu => hu)
          obtain ⟨S, hS, kS⟩ := hF _ _ hmin
          refine ⟨shiftReqs S, shiftReqs_sound hS, fun σ' hσ' => ?_⟩
          refine Or.inr (Or.inl ⟨[t], t, hc, Or.inr ⟨[t], rfl, fun r hr y _ hy => ?_⟩, by simp, hdem⟩)
          simp only [List.mem_singleton] at hr
          subst hr
          exact kS _ (shiftReqs_back (fun u hu => hy u (by
            have := hS _ hu
            exact this)) hσ')
      · rcases hG with hG | ⟨_, hte, _⟩
        · cases hG
        · cases hte)
    refine ⟨SA ++ SR, fun q hq => ?_, fun σ' hσ' => ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hSA q hq
      · exact hSR q hq
    · exact Or.inr ⟨a, p, he, ha, Or.inr ⟨a', g, hpe,
        kA σ' (fun q hq => hσ' q (List.mem_append_left _ hq)),
        kR σ' (fun q hq => hσ' q (List.mem_append_right _ hq))⟩⟩

theorem var_cont (i : Nat) : JointCont (fun σ => withBot (σ i)) := by
  intro σ d hd
  rcases hd with hb | hd
  · exact ⟨[], by simp, fun _ _ => Or.inl hb⟩
  · exact ⟨[(i, d)], by simpa using hd, fun σ' h => Or.inr (h (i, d) (by simp))⟩

theorem const_cont (V : Value) : JointCont (fun _ => V) :=
  fun _ _ hd => ⟨[], by simp, fun _ _ => hd⟩

/-- Every kinded code's image is jointly continuous. -/
theorem image_cont : {k : Nat} → (c : LCode k) → ∀ (κ : List (Option Nat)), Kinded κ c →
    JointCont (fun σ => image σ c)
  | _, .var0 i, _, _ => var_cont i
  | _, .prop _, _, hk => hk.cont
  | _, .pi0 A B, κ, hk => pi_cont (fun σ => image σ A) (fun σ => image σ B) (some 0)
      (image_cont A κ hk.1) (image_cont B _ hk.2) (fun σ σ' h => image_mono B _ hk.2 h)
  | _, .var _ i, _, _ => var_cont i
  | _, .univ _, _, _ => const_cont _
  | _, .neutral _ _, _, _ => const_cont _
  | _, .pi c A B, κ, hk => pi_cont (fun σ => image σ A) (fun σ => image σ B) (some (c + 1))
      (image_cont A κ hk.1) (image_cont B _ hk.2) (fun σ σ' h => image_mono B _ hk.2 h)

end Rcic.Declarative.Ann.LR3.LevelGirard
