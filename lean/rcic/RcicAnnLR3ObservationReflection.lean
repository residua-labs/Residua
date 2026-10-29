import rcic.RcicAnnLR3TypeZeroTowerProbe

/-!
# Type-directed reflection on raw type images, by positive observations

`GenericReflectionBoundary` shows that reflected elements must depend on the
type they inhabit. Here reflection reads the raw type image only through
positive observations, so it needs no decision and stays continuous.
`Refl W v` is an inductive predicate on output observations:

- a sort payload `.spine 11 _` at level tag `j.map succ` gives the named
  neutral type `13` of level `j`, whatever `v` is (`j : Option Nat`, so the
  none level is included);
- a non-sort spine payload gives `v` itself;
- a product payload gives an η-expansion whose rows reflect the
  applications of `v` in the fibres (`fibreOf`), read from the product's own
  observations.

Laws (`reflV W v` is the value):
- `refl_mono` and `refl_cont`: reflection is monotone, and in continuous
  environments it is determined by a finite demand;
- `refl_universe`: at `universeValue j` reflection is the named neutral type
  `NativeMemberValues.value j 13`;
- `refl_ntype`: at a neutral type image (neutral, head-11-free payload),
  reflection of a neutral is the neutral;
- `refl_pi`: at a product image with a finitely demanding fibre function,
  applying the reflection to `x` is reflecting the application in the fibre
  at `x`.

No choice and no decision on raw values is used. This is the reflection the
open-realizer design needs. Its use for `NeutralSupport` (membership in every
code) is the next step. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ObservationReflection

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe (withBot Head11Free)

/-- The fibre of a type image at a finite argument demand, read from its
product observations. -/
def fibreOf (W : Value) (ds : List CptI) : Value := fun c =>
  c = .bot ∨ ∃ t a g, W (.spine 10 [t, .pi a g]) ∧ ∃ s ∈ g, (∀ u ∈ s.1, u ∈ ds) ∧ s.2 = c

/-- Type-directed reflection of a value `v` at a raw type image `W`, by
recursion on output observations. Each clause tests one positive
observation of `W`: a sort payload gives a level-tagged neutral type, a
non-sort spine payload gives `v` itself, and a product payload gives the
η-expansion whose rows reflect the applications in the fibres. -/
inductive Refl : Value → Value → CptI → Prop
  | bot (W v : Value) : Refl W v .bot
  | univ {W v : Value} (j : Option Nat) (q : List CptI) {c : CptI}
      (hw : W (.spine 10 [.spine (levelRef (j.map Nat.succ)) [], .spine 11 q]))
      (hc : NativeMemberValues.value j 13 c) : Refl W v c
  | neut {W v : Value} (t : CptI) (r : Nat) (args : List CptI) {c : CptI}
      (hw : W (.spine 10 [t, .spine r args])) (hr : r ≠ 11) (hc : v c) : Refl W v c
  | lam {W v : Value} (t a : CptI) (g' g : NeutralPi.Graph)
      (hw : W (.spine 10 [t, .pi a g']))
      (hrows : ∀ s ∈ g, Refl (fibreOf W s.1) (NeutralPi.applyValue v (demand s.1)) s.2) :
      Refl W v (.lam g)

def reflV (W v : Value) : Value := Refl W v

/-! ## Monotonicity -/

def Sub (x y : Value) : Prop := ∀ c, x c → y c

theorem fibreOf_mono {W W' : Value} (h : Sub W W') (ds : List CptI) :
    Sub (fibreOf W ds) (fibreOf W' ds) := by
  rintro c (hc | ⟨t, a, g, hw, s, hs, hd, he⟩)
  · exact Or.inl hc
  · exact Or.inr ⟨t, a, g, h _ hw, s, hs, hd, he⟩

theorem refl_mono {W v : Value} {c : CptI} (h : Refl W v c) :
    ∀ {W' v' : Value}, Sub W W' → Sub v v' → Refl W' v' c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | univ j q hw hc => intro _ _ hW _; exact .univ j q (hW _ hw) hc
  | neut t r args hw hr hc => intro _ _ hW hv; exact .neut t r args (hW _ hw) hr (hv _ hc)
  | lam t a g' g hw _ ih =>
      intro _ _ hW hv
      exact .lam t a g' g (hW _ hw) (fun s hs => ih s hs (fibreOf_mono hW s.1)
        (NeutralPi.applyValue_mono hv (fun _ hc => hc)))

/-! ## Continuity -/

/-- Monotone and determined by finite demands. -/
def Cont (Φ : Value → Value) : Prop :=
  (∀ y y', Sub y y' → Sub (Φ y) (Φ y')) ∧
  (∀ y c, Φ y c → ∃ ds : List CptI, (∀ u ∈ ds, y u) ∧ Φ (demand ds) c)

theorem demand_sub {x : Value} {ds : List CptI} (h : ∀ u ∈ ds, x u) : Sub (demand ds) x :=
  fun u hu => h u hu

theorem demand_append_left (ds es : List CptI) : Sub (demand ds) (demand (ds ++ es)) :=
  fun _ hu => List.mem_append_left _ hu

theorem demand_append_right (ds es : List CptI) : Sub (demand es) (demand (ds ++ es)) :=
  fun _ hu => List.mem_append_right _ hu

theorem append_in {x : Value} {ds es : List CptI} (h1 : ∀ u ∈ ds, x u) (h2 : ∀ u ∈ es, x u) :
    ∀ u ∈ ds ++ es, x u := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact h1 u hu
  · exact h2 u hu

theorem cont_fibre {Φ : Value → Value} (hΦ : Cont Φ) (ds : List CptI) :
    Cont (fun y => fibreOf (Φ y) ds) := by
  refine ⟨fun y y' h => fibreOf_mono (hΦ.1 y y' h) ds, ?_⟩
  rintro y c (hc | ⟨t, a, g, hw, s, hs, hd, he⟩)
  · exact ⟨[], by simp, Or.inl hc⟩
  · obtain ⟨es, hes, hw'⟩ := hΦ.2 y _ hw
    exact ⟨es, hes, Or.inr ⟨t, a, g, hw', s, hs, hd, he⟩⟩

theorem cont_app {Ψ : Value → Value} (hΨ : Cont Ψ) (z : Value) :
    Cont (fun y => NeutralPi.applyValue (Ψ y) z) := by
  refine ⟨fun y y' h => NeutralPi.applyValue_mono (hΨ.1 y y' h) (fun _ hc => hc), ?_⟩
  rintro y c (hc | ⟨g, s, hc, hf, hs, ha⟩ | ⟨r, args, u, hc, hf, ha⟩)
  · exact ⟨[], by simp, Or.inl hc⟩
  · obtain ⟨es, hes, hf'⟩ := hΨ.2 y _ hf
    exact ⟨es, hes, Or.inr (Or.inl ⟨g, s, hc, hf', hs, ha⟩)⟩
  · obtain ⟨es, hes, hf'⟩ := hΨ.2 y _ hf
    exact ⟨es, hes, Or.inr (Or.inr ⟨r, args, u, hc, hf', ha⟩)⟩

/-- Finitely many rows, each with its own finite demand, share one. -/
theorem rows_demand {x : Value} (P : List CptI → (List CptI × CptI) → Prop)
    (hP : ∀ ds es s, Sub (demand ds) (demand es) → P ds s → P es s) :
    (g : NeutralPi.Graph) → (∀ s ∈ g, ∃ ds, (∀ u ∈ ds, x u) ∧ P ds s) →
      ∃ ds, (∀ u ∈ ds, x u) ∧ ∀ s ∈ g, P ds s
  | [], _ => ⟨[], by simp, by simp⟩
  | s :: g, h => by
      obtain ⟨ds, hds, hs⟩ := h s (List.mem_cons_self _ _)
      obtain ⟨es, hes, hg⟩ := rows_demand P hP g (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
      refine ⟨ds ++ es, append_in hds hes, fun s' hs' => ?_⟩
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact hP _ _ _ (demand_append_left ds es) hs
      · exact hP _ _ _ (demand_append_right ds es) (hg s' hs')

/-- Reflection in continuous environments is determined by a finite demand. -/
theorem refl_cont {W v : Value} {c : CptI} (h : Refl W v c) :
    ∀ (Φ Ψ : Value → Value) (x : Value), Cont Φ → Cont Ψ → W = Φ x → v = Ψ x →
      ∃ ds, (∀ u ∈ ds, x u) ∧ Refl (Φ (demand ds)) (Ψ (demand ds)) c := by
  induction h with
  | bot => intro _ _ _ _ _ _ _; exact ⟨[], by simp, .bot _ _⟩
  | univ j q hw hc =>
      intro Φ Ψ x hΦ hΨ hW hv
      subst hW hv
      obtain ⟨ds, hds, hw'⟩ := hΦ.2 x _ hw
      exact ⟨ds, hds, .univ j q hw' hc⟩
  | neut t r args hw hr hc =>
      intro Φ Ψ x hΦ hΨ hW hv
      subst hW hv
      obtain ⟨ds, hds, hw'⟩ := hΦ.2 x _ hw
      obtain ⟨es, hes, hc'⟩ := hΨ.2 x _ hc
      exact ⟨ds ++ es, append_in hds hes, .neut t r args
        (hΦ.1 _ _ (demand_append_left ds es) _ hw') hr
        (hΨ.1 _ _ (demand_append_right ds es) _ hc')⟩
  | lam t a g' g hw _ ih =>
      intro Φ Ψ x hΦ hΨ hW hv
      subst hW hv
      obtain ⟨ds, hds, hw'⟩ := hΦ.2 x _ hw
      obtain ⟨es, hes, hrows⟩ := rows_demand (x := x)
        (fun ds s => Refl (fibreOf (Φ (demand ds)) s.1)
          (NeutralPi.applyValue (Ψ (demand ds)) (demand s.1)) s.2)
        (fun ds es s h r => refl_mono r (fibreOf_mono (hΦ.1 _ _ h) s.1)
          (NeutralPi.applyValue_mono (hΨ.1 _ _ h) (fun _ hc => hc)))
        g (fun s hs => ih s hs _ _ x (cont_fibre hΦ s.1) (cont_app hΨ (demand s.1)) rfl rfl)
      exact ⟨ds ++ es, append_in hds hes, .lam t a g' g
        (hΦ.1 _ _ (demand_append_left ds es) _ hw')
        (fun s hs => refl_mono (hrows s hs)
          (fibreOf_mono (hΦ.1 _ _ (demand_append_right ds es)) s.1)
          (NeutralPi.applyValue_mono (hΨ.1 _ _ (demand_append_right ds es)) (fun _ hc => hc)))⟩

/-! ## The universe law -/

def univPayload (j : Option Nat) : Value := denI EnvI.bot (.app (.const 11 []) (levelTerm j))

theorem universe_tagged (j : Option Nat) :
    universeValue j = InductiveCodes.taggedValue (j.map Nat.succ) (univPayload j) :=
  NeutralCodes.valueEq_eq (InductiveCodes.taggedValue_denI EnvI.bot (j.map Nat.succ) _).symm

theorem univPayload_inv {j : Option Nat} {p : CptI} (h : univPayload j p) :
    p = .bot ∨ ∃ u, p = .spine 11 [u] := by
  rcases approxI_app_inv h with hb | ⟨g, _, _, hf, _, _⟩ | ⟨r, args, u, he, hf, _⟩
  · exact Or.inl hb
  · rcases approxI_const_inv hf with h | h <;> cases h
  · rcases approxI_const_inv hf with h | h
    · cases h
    · cases h
      exact Or.inr ⟨u, he⟩

theorem tagged_obs {k : Option Nat} {P : Value} {a p : CptI}
    (h : InductiveCodes.taggedValue k P (.spine 10 [a, p])) :
    (a = .bot ∨ a = .spine (levelRef k) []) ∧ P p := by
  rcases h with h | ⟨a', p', he, ha, hp⟩
  · cases h
  · have h1 := (CptI.spine.inj he).2
    simp only [List.cons.injEq] at h1
    obtain ⟨rfl, rfl, -⟩ := h1
    exact ⟨ha, hp⟩

/-- At a universe image, reflection is the named neutral type `13` of that
level, for every reflected value. -/
theorem refl_universe (j : Option Nat) (v : Value) :
    ValueEq (reflV (universeValue j) v) (NativeMemberValues.value j 13) := by
  rw [universe_tagged]
  intro c
  constructor
  · intro h
    cases h with
    | bot => exact NativeMemberValues.value_bot _ _
    | univ j' q hw hc =>
        obtain ⟨ha, _⟩ := tagged_obs hw
        rcases ha with ha | ha
        · cases ha
        · have hj := levelRef_injective (CptI.spine.inj ha).1
          have hj' : j' = j := by
            cases j <;> cases j' <;> simp_all
          subst hj'
          exact hc
    | neut t r args hw hr _ =>
        rcases univPayload_inv (tagged_obs hw).2 with h | ⟨u, h⟩
        · cases h
        · simp only [CptI.spine.injEq] at h
          exact absurd h.1 hr
    | lam t a g' g hw _ =>
        rcases univPayload_inv (tagged_obs hw).2 with h | ⟨u, h⟩ <;> cases h
  · intro hc
    refine .univ j [.bot] ?_ hc
    exact Or.inr ⟨_, _, rfl, Or.inr rfl, .appSpine (args := []) (.const _ _ _) (.bot _ _)⟩

/-! ## The neutral-type law -/

/-- At a neutral type image, reflection of a neutral is the neutral. -/
theorem refl_ntype (k : Nat) {w : Value} (hw : CandidatePi.Neutral w) (hfree : Head11Free w)
    {v : Value} (hv : CandidatePi.Neutral v) :
    ValueEq (reflV (InductiveCodes.taggedValue (some k) (withBot w)) v) v := by
  intro c
  constructor
  · intro h
    cases h with
    | bot => exact RCodeSoundPiControl.neutral_bot hv
    | univ j q hw' _ =>
        rcases (tagged_obs hw').2 with h | h
        · cases h
        · exact (hfree q h).elim
    | neut _ _ _ _ _ hc => exact hc
    | lam t a g' g hw' _ =>
        rcases (tagged_obs hw').2 with h | h
        · cases h
        · rcases CandidatePi.neutral_spineOnly hw _ h with h | ⟨_, _, h⟩ <;> cases h
  · intro hc
    rcases CandidatePi.neutral_spineOnly hv c hc with rfl | ⟨name, args, rfl⟩
    · exact .bot _ _
    · obtain ⟨r, rargs, hr⟩ := CandidatePi.neutral_spine_observed hw
      have hr11 : r ≠ 11 := by
        rintro rfl
        exact hfree rargs hr
      exact .neut .bot r rargs (Or.inr ⟨_, _, rfl, Or.inl rfl, Or.inr hr⟩) hr11 hc

/-! ## The product law -/

section Pi

variable (k : Option Nat) (A : Value) (F : Value → Value)

def piImage : Value :=
  InductiveCodes.piValue k A (UnifiedPi.legalGraph (fun _ _ => True) F)

variable {k A F}

theorem cont_of_finite (hF : UnifiedPi.LegalFiniteDemand (fun _ _ => True) F) : Cont F := by
  refine ⟨fun y y' h c hc => ?_, fun y c hc => ?_⟩
  · obtain ⟨us, hus, hrow⟩ := hF y True.intro c hc
    exact hrow y' True.intro (fun u hu => h u (hus u hu))
  · obtain ⟨us, hus, hrow⟩ := hF y True.intro c hc
    exact ⟨us, hus, hrow _ True.intro (fun u hu => hu)⟩

theorem cont_apply (v : Value) : Cont (fun y => NeutralPi.applyValue v y) := by
  refine ⟨fun y y' h => NeutralPi.applyValue_mono (fun _ hc => hc) h, ?_⟩
  rintro y c (hc | ⟨g, s, hc, hf, hs, ha⟩ | ⟨r, args, u, hc, hf, ha⟩)
  · exact ⟨[], by simp, Or.inl hc⟩
  · exact ⟨s.1, ha, Or.inr (Or.inl ⟨g, s, hc, hf, hs, fun u hu => hu⟩)⟩
  · exact ⟨[u], by simpa using ha, Or.inr (Or.inr ⟨r, args, u, hc, hf, by simp [demand]⟩)⟩

theorem piImage_obs {t p : CptI} (h : piImage k A F (.spine 10 [t, p])) :
    p = .bot ∨ ∃ a g, p = .pi a g ∧ A a ∧
      ∀ s ∈ g, NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True) F) (demand s.1) s.2 :=
  (tagged_obs h).2

theorem fibreOf_piImage (hA : A .bot) (hF : UnifiedPi.LegalFiniteDemand (fun _ _ => True) F)
    (hb : ∀ x, F x .bot) (ds : List CptI) :
    fibreOf (piImage k A F) ds = F (demand ds) := by
  have happ : ValueEq (NeutralPi.applyValue (UnifiedPi.legalGraph (fun _ _ => True) F)
      (demand ds)) (F (demand ds)) :=
    UnifiedPi.applyValue_legalGraph (fun y _ => hb y) hF True.intro
  refine NeutralCodes.valueEq_eq (fun c => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with rfl | ⟨t, a, g, hw, s, hs, hd, rfl⟩
    · exact hb _
    · rcases piImage_obs hw with h | ⟨a', g'', h, _, hrows⟩
      · cases h
      · simp only [CptI.pi.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hr := hrows s hs
        have hr' := NeutralPi.applyValue_mono (fun _ hc => hc)
          (fun u hu => hd u hu : Sub (demand s.1) (demand ds)) _ hr
        exact (happ _).mp hr'
  · refine Or.inr ⟨.bot, .bot, [(ds, c)], ?_, (ds, c), List.mem_singleton_self _,
      fun u hu => hu, rfl⟩
    refine Or.inr ⟨.bot, .pi .bot [(ds, c)], rfl, Or.inl rfl, Or.inr ⟨.bot, [(ds, c)], rfl, hA, ?_⟩⟩
    intro s hs
    rw [List.mem_singleton.mp hs]
    exact (happ _).mpr h

/-- At a product image, applying the reflection is reflecting the
application in the fibre. -/
theorem refl_pi (hA : A .bot) (hF : UnifiedPi.LegalFiniteDemand (fun _ _ => True) F)
    (hb : ∀ x, F x .bot) (v x : Value) :
    ValueEq (NeutralPi.applyValue (reflV (piImage k A F) v) x)
      (reflV (F x) (NeutralPi.applyValue v x)) := by
  have hfib := fibreOf_piImage (k := k) hA hF hb
  have hFc := cont_of_finite hF
  intro c
  constructor
  · rintro (rfl | ⟨g, s, rfl, hR, hs, hd⟩ | ⟨r, args, u, rfl, hR, _⟩)
    · exact .bot _ _
    · cases hR with
      | univ j q hw _ =>
          rcases piImage_obs hw with h | ⟨_, _, h, _⟩ <;> cases h
      | neut t r' args' hw hr _ =>
          rcases piImage_obs hw with h | ⟨_, _, h, _⟩ <;> cases h
      | lam t a g' _ _ hrows =>
          have hrow := hrows s hs
          rw [hfib] at hrow
          exact refl_mono hrow (hFc.1 _ _ (fun u hu => hd u hu))
            (NeutralPi.applyValue_mono (fun _ hc => hc) (fun u hu => hd u hu))
    · cases hR with
      | univ j q hw _ =>
          rcases piImage_obs hw with h | ⟨_, _, h, _⟩ <;> cases h
      | neut t r' args' hw hr _ =>
          rcases piImage_obs hw with h | ⟨_, _, h, _⟩ <;> cases h
  · intro h
    obtain ⟨ds, hds, hR⟩ := refl_cont h F (fun y => NeutralPi.applyValue v y) x hFc
      (cont_apply v) rfl rfl
    refine Or.inr (Or.inl ⟨[(ds, c)], (ds, c), rfl, ?_, List.mem_singleton_self _, hds⟩)
    refine .lam .bot .bot [] [(ds, c)]
      (Or.inr ⟨.bot, .pi .bot [], rfl, Or.inl rfl, Or.inr ⟨.bot, [], rfl, hA, by simp⟩⟩) ?_
    intro s hs
    rw [List.mem_singleton.mp hs, hfib]
    exact hR

end Pi

end Rcic.Declarative.Ann.LR3.ObservationReflection
