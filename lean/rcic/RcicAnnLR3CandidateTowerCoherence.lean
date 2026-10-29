import rcic.RcicAnnLR3CandidateTowerProbe

/-!
# Coherence of open codes in candidate environments

Question (4) of the Girard-style probe: does image coherence survive with
variables? Yes, once it is quantified over raw environments. Suppose two open
codes have equal raw images in every bot-containing raw environment. Then
their interpretations agree in every saturated environment
(`open_coherent`). Variables are separated by varying the raw environment,
and products by the injectivity of the evaluator's product image.

The product case needs the codomain's raw image to be monotone and finitely
determined in each environment slot (`image_mono`, `image_finite`). It also
needs the pointwise application law of the legal graph
(`applyValue_legalGraph_at`), whose bottom premise is only needed at the
argument. Both are proved here by structural induction on codes.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateTowerCoherence

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (imaxN)
open CandidateTowerProbe

/-- The legal-graph application law at one argument with the bottom
observation. -/
theorem applyValue_legalGraph_at {F : Value → Value}
    (hfinite : UnifiedPi.LegalFiniteDemand (fun _ _ => True) F) {x : Value} (hb : F x .bot) :
    ValueEq (NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True) F) x) (F x) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ | ⟨head, args, u, hc, hf, ha⟩
    · subst c
      exact hb
    · rcases hf with hf | ⟨table, he, rows⟩
      · cases hf
      · cases he
        subst c
        exact rows s hs x True.intro ha
    · rcases hf with hf | ⟨table, he, rows⟩
      · cases hf
      · cases he
  · intro hc
    obtain ⟨us, hus, hrow⟩ := hfinite x True.intro c hc
    refine Or.inr (Or.inl ⟨[(us, c)], (us, c), rfl, ?_, by simp, hus⟩)
    refine Or.inr ⟨[(us, c)], rfl, ?_⟩
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hrow

/-! ## Environment dependence of images -/

def upd (σ : REnv) (j : Nat) (x : Value) : REnv := fun i => if i = j then x else σ i

theorem rcons_upd (y : Value) (σ : REnv) (j : Nat) (x : Value) :
    rcons y (upd σ j x) = upd (rcons y σ) (j + 1) x := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      show (if i = j then x else σ i) = (if i + 1 = j + 1 then x else σ i)
      by_cases h : i = j
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (Nat.succ.inj h'))]

def EnvLe (σ σ' : REnv) : Prop := ∀ i c, σ i c → σ' i c

theorem envLe_rcons {σ σ' : REnv} (h : EnvLe σ σ') {y y' : Value} (hy : ∀ c, y c → y' c) :
    EnvLe (rcons y σ) (rcons y' σ') := by
  intro i c
  cases i with
  | zero => exact hy c
  | succ i => exact h i c

/-- Raw images are monotone in the raw environment. -/
theorem image_mono : {k : Nat} → (c : GCode k) → {σ σ' : REnv} → EnvLe σ σ' →
    ∀ d, image σ c d → image σ' c d
  | _, .var _ i, _, _, h, d, hd => hd.imp_right (h i d)
  | _, .univ _, _, _, _, _, hd => hd
  | _, .neutral _ _, _, _, _, _, hd => hd
  | _, .pi A B, σ, σ', h, d, hd => by
      rcases hd with hd | ⟨a, p, he, ha, hp | ⟨a', g, hpe, hA, hrows⟩⟩
      · exact Or.inl hd
      · exact Or.inr ⟨a, p, he, ha, Or.inl hp⟩
      · refine Or.inr ⟨a, p, he, ha, Or.inr ⟨a', g, hpe, image_mono A h a' hA, ?_⟩⟩
        intro s hs
        rcases hrows s hs with hc | ⟨g', s', hc, hG, hs', hv⟩ | ⟨head, args, u, hc, hG, hv⟩
        · exact Or.inl hc
        · refine Or.inr (Or.inl ⟨g', s', hc, ?_, hs', hv⟩)
          rcases hG with hG | ⟨table, he', rows⟩
          · exact Or.inl hG
          · refine Or.inr ⟨table, he', fun t ht y hy hty => ?_⟩
            exact image_mono B (envLe_rcons h (fun _ c => c)) t.2 (rows t ht y hy hty)
        · rcases hG with hG | ⟨table, he', _⟩
          · cases hG
          · cases he'

/-- One application row of the product image is finitely determined in an
environment slot. -/
theorem row_finite {k : Nat} (B : GCode k)
    (ihB : ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), image (upd σ j x) B d →
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → image (upd σ j x') B d)
    (σ : REnv) (j : Nat) (x v : Value) (c : CptI)
    (h : NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
      (fun y => image (rcons y (upd σ j x)) B)) v c) :
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) →
      NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
        (fun y => image (rcons y (upd σ j x')) B)) v c := by
  rcases h with hc | ⟨g', s', hc, hG, hs', hv⟩ | ⟨head, args, u, hc, hG, hv⟩
  · exact ⟨[], by simp, fun _ _ => Or.inl hc⟩
  · rcases hG with hG | ⟨table, he, rows⟩
    · cases hG
    · cases he
      have hmin : image (rcons (demand s'.1) (upd σ j x)) B s'.2 :=
        rows s' hs' (demand s'.1) True.intro (fun u hu => hu)
      rw [rcons_upd] at hmin
      obtain ⟨us, hus, hfin⟩ := ihB _ _ x _ hmin
      refine ⟨us, hus, fun x' hx' => Or.inr (Or.inl ⟨[s'], s', hc, ?_, by simp, hv⟩)⟩
      refine Or.inr ⟨[s'], rfl, fun t ht y _ hty => ?_⟩
      simp only [List.mem_singleton] at ht
      subst t
      have h0 := hfin x' hx'
      rw [← rcons_upd] at h0
      exact image_mono B (envLe_rcons (fun _ _ h => h) (fun c hc => hty c hc)) _ h0
  · rcases hG with hG | ⟨table, he, _⟩
    · cases hG
    · cases he

theorem rows_finite {k : Nat} (B : GCode k)
    (ihB : ∀ (σ : REnv) (j : Nat) (x : Value) (d : CptI), image (upd σ j x) B d →
      ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → image (upd σ j x') B d)
    (σ : REnv) (j : Nat) (x : Value) :
    (g : List (List CptI × CptI)) →
    (∀ s ∈ g, NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
      (fun y => image (rcons y (upd σ j x)) B)) (demand s.1) s.2) →
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) →
      ∀ s ∈ g, NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True)
        (fun y => image (rcons y (upd σ j x')) B)) (demand s.1) s.2
  | [], _ => ⟨[], by simp, fun _ _ s hs => by cases hs⟩
  | s :: g, h => by
      obtain ⟨us₁, hus₁, h₁⟩ := row_finite B ihB σ j x _ _ (h s (by simp))
      obtain ⟨us₂, hus₂, h₂⟩ := rows_finite B ihB σ j x g (fun t ht => h t (by simp [ht]))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun x' hx' t ht => ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hus₁ u hu
        · exact hus₂ u hu
      · rcases List.mem_cons.mp ht with ht | ht
        · subst ht
          exact h₁ x' (fun u hu => hx' u (List.mem_append_left _ hu))
        · exact h₂ x' (fun u hu => hx' u (List.mem_append_right _ hu)) t ht

/-- Raw images are finitely determined in every environment slot. -/
theorem image_finite : {k : Nat} → (c : GCode k) → ∀ (σ : REnv) (j : Nat) (x : Value)
    (d : CptI), image (upd σ j x) c d →
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ ∀ x', (∀ u ∈ us, x' u) → image (upd σ j x') c d
  | _, .var _ i, σ, j, x, d, hd => by
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
  | _, .univ _, _, _, _, _, hd => ⟨[], by simp, fun _ _ => hd⟩
  | _, .neutral _ _, _, _, _, _, hd => ⟨[], by simp, fun _ _ => hd⟩
  | _, .pi A B, σ, j, x, d, hd => by
      rcases hd with hd | ⟨a, p, he, ha, hp | ⟨a', g, hpe, hA, hrows⟩⟩
      · exact ⟨[], by simp, fun _ _ => Or.inl hd⟩
      · exact ⟨[], by simp, fun _ _ => Or.inr ⟨a, p, he, ha, Or.inl hp⟩⟩
      · obtain ⟨us₁, hus₁, h₁⟩ := image_finite A σ j x a' hA
        obtain ⟨us₂, hus₂, h₂⟩ := rows_finite B (image_finite B) σ j x g hrows
        refine ⟨us₁ ++ us₂, fun u hu => ?_, fun x' hx' => ?_⟩
        · rcases List.mem_append.mp hu with hu | hu
          · exact hus₁ u hu
          · exact hus₂ u hu
        · exact Or.inr ⟨a, p, he, ha, Or.inr ⟨a', g, hpe,
            h₁ x' (fun u hu => hx' u (List.mem_append_left _ hu)),
            h₂ x' (fun u hu => hx' u (List.mem_append_right _ hu))⟩⟩

/-- The codomain's raw image function has finite demand. -/
theorem codomain_finite {k : Nat} (B : GCode k) (σ : REnv) :
    UnifiedPi.LegalFiniteDemand (fun _ _ => True) (fun x => image (rcons x σ) B) := by
  intro x _ c hc
  have hc' : image (upd (rcons x σ) 0 x) B c := by
    have he : upd (rcons x σ) 0 x = rcons x σ := by
      funext i
      cases i <;> rfl
    rw [he]
    exact hc
  obtain ⟨us, hus, hfin⟩ := image_finite B (rcons x σ) 0 x c hc'
  refine ⟨us, hus, fun y _ hy => ?_⟩
  have h := hfin y hy
  have he : upd (rcons x σ) 0 y = rcons y σ := by
    funext i
    cases i <;> rfl
  rw [he] at h
  exact h

/-! ## Coherence -/

def BotEnv (σ : REnv) : Prop := ∀ i, σ i .bot

theorem botEnv_rcons {σ : REnv} (h : BotEnv σ) {x : Value} (hx : x .bot) :
    BotEnv (rcons x σ) := by
  intro i
  cases i with
  | zero => exact hx
  | succ i => exact h i

def ImageEq {k l : Nat} (c : GCode k) (d : GCode l) : Prop :=
  ∀ σ : REnv, BotEnv σ → ValueEq (image σ c) (image σ d)

/-- Every non-variable image observes the tagged bottom pair. -/
def NonVar {k : Nat} : GCode k → Prop
  | .var _ _ => False
  | _ => True

theorem nonvar_obs {k : Nat} (σ : REnv) : (c : GCode k) → NonVar c →
    image σ c (.spine 10 [.bot, .bot])
  | .var _ _, h => h.elim
  | .univ _, _ => .appSpine (.appSpine (.const _ _ _) (.bot _ _)) (.bot _ _)
  | .neutral _ _, _ => .appSpine (.appSpine (.const _ _ _) (.bot _ _)) (.bot _ _)
  | .pi _ _, _ => Or.inr ⟨.bot, .bot, rfl, Or.inl rfl, Or.inl rfl⟩

def constEnv (v : Value) : REnv := fun _ => v

theorem var_vs_nonvar {k l : Nat} (i : Nat) (d : GCode l) (hd : NonVar d)
    (h : ImageEq (GCode.var k i) d) : False := by
  rcases (h (constEnv bottom) (fun _ => rfl) (.spine 10 [.bot, .bot])).mpr
    (nonvar_obs _ d hd) with h0 | h0 <;> cases h0

theorem var_vs_var {k l i j : Nat} (h : ImageEq (GCode.var k i) (GCode.var l j)) : i = j := by
  by_cases hij : i = j
  · exact hij
  · exfalso
    let σ : REnv := fun n => if n = i then universeValue (some 0) else universeValue (some 1)
    have hσ : BotEnv σ := by
      intro n
      show (if n = i then universeValue (some 0) else universeValue (some 1)) .bot
      split <;> exact .bot _ _
    have h1 := h σ hσ
    have wb : ∀ v : Value, v .bot → ValueEq (TypeZeroTowerProbe.withBot v) v := fun v hv c =>
      ⟨fun h => h.elim (fun h => h ▸ hv) id, Or.inr⟩
    have hi : σ i = universeValue (some 0) := by
      show (if i = i then _ else _) = _
      rw [if_pos rfl]
    have hj : σ j = universeValue (some 1) := by
      show (if j = i then _ else _) = _
      rw [if_neg (fun h => hij h.symm)]
    have h1 : ValueEq (σ i) (σ j) :=
      (wb _ (hσ i)).symm.trans (h1.trans (wb _ (hσ j)))
    rw [hi, hj] at h1
    have := sort_code_injective h1
    cases this

/-- Tagged payload observations of the non-variable images. -/
theorem pi_vs_tagged {k : Option Nat} {A C P : Value} {l : Option Nat}
    (hA : A .bot) (hP : ∀ p, P p → p = .bot ∨ ∃ r args, p = .spine r args)
    (h : ValueEq (InductiveCodes.piValue k A C) (InductiveCodes.taggedValue l P)) : False := by
  have hobs : InductiveCodes.piValue k A C (.spine 10 [.bot, .pi .bot []]) :=
    Or.inr ⟨.bot, .pi .bot [], rfl, Or.inl rfl, Or.inr ⟨.bot, [], rfl, hA, by simp⟩⟩
  rcases (h _).mp hobs with hb | ⟨a, p, he, _, hp⟩
  · cases hb
  · cases he
    rcases hP _ hp with hp | ⟨_, _, hp⟩ <;> cases hp

theorem univ_tagged (σ : REnv) (k : Nat) :
    ValueEq (image σ (GCode.univ k))
      (InductiveCodes.taggedValue (some (k+1)) (TypeZeroTowerProbe.payload (TypeZeroTowerProbe.Code.univ k))) :=
  TypeZeroTowerProbe.image_tagged (TypeZeroTowerProbe.Code.univ k)

theorem neutral_tagged (σ : REnv) (k name : Nat) :
    ValueEq (image σ (GCode.neutral k name))
      (InductiveCodes.taggedValue (some k)
        (TypeZeroTowerProbe.payload (TypeZeroTowerProbe.Code.neutral k name))) :=
  TypeZeroTowerProbe.image_tagged (TypeZeroTowerProbe.Code.neutral k name)

theorem el_univ_same {adm : Adm} {k j : Nat} (σ : REnv) (ρ : CEnv)
    (h : ValueEq (image σ (GCode.univ k)) (image σ (GCode.univ j))) :
    Same (ElA adm σ ρ (GCode.univ k)) (ElA adm σ ρ (GCode.univ j)) := by
  have hkj : some k = some j := sort_code_injective h
  cases hkj
  exact fun _ _ => Iff.rfl

theorem botEnv_const_bottom : BotEnv (constEnv bottom) := fun _ => rfl

/-- Image-equal kinded codes give their binders the same kind. -/
theorem kind_eq {k l : Nat} (c : GCode k) (d : GCode l) (κ : List (Option Nat))
    (hc : Kinded κ c) (hd : Kinded κ d) (h : ImageEq c d) :
    kindOfCode c = kindOfCode d := by
  have h0 := h (constEnv bottom) botEnv_const_bottom
  cases c with
  | var _ i =>
      cases d with
      | univ _ => exact (var_vs_nonvar i _ (by trivial) h).elim
      | _ => rfl
  | univ j =>
      cases d with
      | univ j' =>
          have hj : some j = some j' := sort_code_injective h0
          cases hj
          rfl
      | var _ i' => exact (var_vs_nonvar i' _ (by trivial) (fun σ hσ => (h σ hσ).symm)).elim
      | neutral l name =>
          exact (TypeZeroTowerProbe.not_univ_neutral (k := j) (l := l) (name := name) h0).elim
      | pi A B =>
          exact (pi_vs_tagged (image_bot _ botEnv_const_bottom A)
            (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
            (h0.symm.trans (univ_tagged _ j))).elim
  | neutral k name =>
      cases d with
      | univ j =>
          exact (TypeZeroTowerProbe.not_univ_neutral (k := j) (l := k) (name := name) h0.symm).elim
      | _ => rfl
  | pi A B =>
      cases d with
      | univ j =>
          exact (pi_vs_tagged (image_bot _ botEnv_const_bottom A)
            (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
            (h0.trans (univ_tagged _ j))).elim
      | _ => rfl

/-- Kinded open codes with equal raw images in every bot-containing raw
environment have equal interpretations in every saturated environment. -/
theorem open_coherent {adm : Adm} (ha : AdmLaws adm) :
    {k : Nat} → (c : GCode k) → {l : Nat} → (d : GCode l) →
    ∀ κ : List (Option Nat), Kinded κ c → Kinded κ d →
    ImageEq c d → ∀ σ ρ, SatEnv σ ρ → Same (ElA adm σ ρ c) (ElA adm σ ρ d)
  | _, .var k i, _, .var l j, κ, hc, hd, h, _, _, _ => by
      cases var_vs_var h
      have hkl : some (some k) = some (some l) := hc.symm.trans hd
      cases hkl
      exact fun _ _ => Iff.rfl
  | _, .var _ i, _, .univ _, _, _, _, h, _, _, _ => (var_vs_nonvar i _ (by trivial) h).elim
  | _, .var _ i, _, .neutral _ _, _, _, _, h, _, _, _ => (var_vs_nonvar i _ (by trivial) h).elim
  | _, .var _ i, _, .pi _ _, _, _, _, h, _, _, _ => (var_vs_nonvar i _ (by trivial) h).elim
  | _, .univ _, _, .var _ j, _, _, _, h, _, _, _ =>
      (var_vs_nonvar j _ (by trivial) (fun σ hσ => (h σ hσ).symm)).elim
  | _, .neutral _ _, _, .var _ j, _, _, _, h, _, _, _ =>
      (var_vs_nonvar j _ (by trivial) (fun σ hσ => (h σ hσ).symm)).elim
  | _, .pi _ _, _, .var _ j, _, _, _, h, _, _, _ =>
      (var_vs_nonvar j _ (by trivial) (fun σ hσ => (h σ hσ).symm)).elim
  | _, .univ _, _, .univ _, _, _, _, h, σ, ρ, hs => el_univ_same σ ρ (h σ hs.2)
  | _, .univ k, _, .neutral l name, _, _, _, h, σ, _, hs =>
      (TypeZeroTowerProbe.not_univ_neutral (k := k) (l := l) (name := name) (h σ hs.2)).elim
  | _, .neutral l name, _, .univ k, _, _, _, h, σ, _, hs =>
      (TypeZeroTowerProbe.not_univ_neutral (k := k) (l := l) (name := name) (h σ hs.2).symm).elim
  | _, .neutral _ _, _, .neutral _ _, _, _, _, _, _, _, _ => fun _ _ => Iff.rfl

  | _, .pi A B, _, .univ k, _, _, _, h, σ, _, hs =>
      (pi_vs_tagged (image_bot σ hs.2 A)
        (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
        ((h σ hs.2).trans (univ_tagged σ k))).elim
  | _, .pi A B, _, .neutral k name, _, _, _, h, σ, _, hs =>
      (pi_vs_tagged (image_bot σ hs.2 A)
        (fun p hp => TypeZeroTowerProbe.neutral_spine p hp)
        ((h σ hs.2).trans (neutral_tagged σ k name))).elim
  | _, .univ k, _, .pi A B, _, _, _, h, σ, _, hs =>
      (pi_vs_tagged (image_bot σ hs.2 A)
        (fun p hp => TypeZeroTowerProbe.univ_spine p hp)
        ((h σ hs.2).symm.trans (univ_tagged σ k))).elim
  | _, .neutral k name, _, .pi A B, _, _, _, h, σ, _, hs =>
      (pi_vs_tagged (image_bot σ hs.2 A)
        (fun p hp => TypeZeroTowerProbe.neutral_spine p hp)
        ((h σ hs.2).symm.trans (neutral_tagged σ k name))).elim
  | _, .pi A B, _, .pi A' B', κ, hc, hd, h, σ, ρ, hs => by
      have hdomB : ImageEq A A' ∧ ImageEq B B' := by
        refine ⟨fun σ' hσ' => ?_, fun σ' hσ' => ?_⟩
        · exact (InductiveCodes.piValue_injective (image_bot σ' hσ' A) (image_bot σ' hσ' A')
            (h σ' hσ')).2.1
        · have htail : BotEnv (fun i => σ' (i + 1)) := fun i => hσ' (i + 1)
          have he : rcons (σ' 0) (fun i => σ' (i + 1)) = σ' := by
            funext i
            cases i <;> rfl
          obtain ⟨_, _, hcod⟩ := InductiveCodes.piValue_injective
            (image_bot _ htail A) (image_bot _ htail A') (h _ htail)
          have hx := hσ' 0
          have h1 := applyValue_legalGraph_at (codomain_finite B (fun i => σ' (i + 1)))
            (x := σ' 0) (image_bot _ (botEnv_rcons htail hx) B)
          have h2 := applyValue_legalGraph_at (codomain_finite B' (fun i => σ' (i + 1)))
            (x := σ' 0) (image_bot _ (botEnv_rcons htail hx) B')
          rw [he] at h1 h2
          exact h1.symm.trans ((hcod (σ' 0)).trans h2)
      have hkind := kind_eq A A' κ hc.1 hd.1 hdomB.1
      have hB' : Kinded (kindOfCode A :: κ) B' := by
        rw [hkind]
        exact hd.2
      have sA := open_coherent ha A A' κ hc.1 hd.1 hdomB.1 σ ρ hs
      have sB : ∀ (z : Value), z .bot → ∀ R, Sat R →
          Same (ElA adm (rcons z σ) (ccons R ρ) B) (ElA adm (rcons z σ) (ccons R ρ) B') :=
        fun z hz R hR => open_coherent ha B B' _ hc.2 hB' hdomB.2 (rcons z σ) (ccons R ρ)
          ⟨fun i => by cases i; exact hR; exact hs.1 _, botEnv_rcons hs.2 hz⟩
      intro f g
      constructor
      · rintro ⟨hf, hg, hfg⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        have hxy' := (sA x y).mpr hxy
        have hx : x .bot := el_saturated σ ρ hs A x y hxy'
        have hy : y .bot := el_saturated σ ρ hs A y x ((el_laws_open ha A σ ρ hs).symm hxy')
        obtain ⟨h1, h2⟩ := hfg x y hxy' R hR
        exact ⟨(sB x hx R (ha.sat hR) _ _).mp h1, (sB y hy R (ha.sat hR) _ _).mp h2⟩
      · rintro ⟨hf, hg, hfg⟩
        refine ⟨hf, hg, fun x y hxy R hR => ?_⟩
        have hx : x .bot := el_saturated σ ρ hs A x y hxy
        have hy : y .bot := el_saturated σ ρ hs A y x ((el_laws_open ha A σ ρ hs).symm hxy)
        obtain ⟨h1, h2⟩ := hfg x y ((sA x y).mp hxy) R hR
        exact ⟨(sB x hx R (ha.sat hR) _ _).mpr h1, (sB y hy R (ha.sat hR) _ _).mpr h2⟩

/-! ## Proof irrelevance at level zero -/

theorem imaxN_zero' {a b : Nat} (h : imaxN a b = 0) : b = 0 := by
  by_cases hb : b = 0
  · exact hb
  · unfold imaxN at h
    rw [if_neg hb] at h
    have hle := Nat.le_max_right a b
    omega

/-- Every level-zero code is proof-irrelevant in a saturated environment. -/
theorem el_irrelevant {adm : Adm} (ha : AdmLaws adm) :
    {k : Nat} → (c : GCode k) → k = 0 → ∀ σ ρ, SatEnv σ ρ →
    ∀ x y, ElA adm σ ρ c x x → ElA adm σ ρ c y y → ElA adm σ ρ c x y
  | _, .var 0 _, _, _, _, _, _, _, hx, hy => ⟨hx.1, hy.1⟩
  | _, .var (_ + 1) _, hk, _, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hk).elim
  | _, .univ _, hk, _, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hk).elim
  | _, .neutral _ _, _, _, _, _, _, _, hx, hy => ⟨hx.1, hy.1⟩
  | _, @GCode.pi a b A B, hk, σ, ρ, h, x, y, hx, hy => by
      have hb : b = 0 := imaxN_zero' hk
      have lA := el_laws_open ha A σ ρ h
      refine ⟨hx.1, hy.2.1, fun u v huv R hR => ?_⟩
      have hRs := ha.sat hR
      have hvu := lA.symm huv
      have hu : u .bot := el_saturated σ ρ h A u v huv
      have hv : v .bot := el_saturated σ ρ h A v u hvu
      have su := satEnv_rcons h hu hRs
      have sv := satEnv_rcons h hv hRs
      have lu := el_laws_open ha B _ _ su
      have lv := el_laws_open ha B _ _ sv
      have hxu := (hx.2.2 u u (lA.trans huv hvu) R (ha.left hR)).1
      have hyu : ElA adm (rcons u σ) (ccons R ρ) B (NeutralPi.applyValue y v)
          (NeutralPi.applyValue y v) := by
        have h2 := (hy.2.2 v u hvu R (ha.symm hR)).2
        exact lu.trans h2 (lu.symm h2)
      have hxv : ElA adm (rcons v σ) (ccons R ρ) B (NeutralPi.applyValue x u)
          (NeutralPi.applyValue x u) := by
        have h2 := (hx.2.2 u v huv R hR).2
        exact lv.trans h2 (lv.symm h2)
      have hyv := (hy.2.2 v v (lA.trans hvu huv) R (ha.left (ha.symm hR))).1
      exact ⟨el_irrelevant ha B hb _ _ su _ _ hxu hyu, el_irrelevant ha B hb _ _ sv _ _ hxv hyv⟩

end Rcic.Declarative.Ann.LR3.CandidateTowerCoherence
